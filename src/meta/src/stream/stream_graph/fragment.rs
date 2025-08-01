// Copyright 2025 RisingWave Labs
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::num::NonZeroUsize;
use std::ops::{Deref, DerefMut};
use std::sync::LazyLock;

use anyhow::{Context, anyhow};
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use risingwave_common::bail;
use risingwave_common::catalog::{
    CDC_SOURCE_COLUMN_NUM, ColumnCatalog, Field, FragmentTypeFlag, FragmentTypeMask, TableId,
    generate_internal_table_name_with_type,
};
use risingwave_common::hash::VnodeCount;
use risingwave_common::util::iter_util::ZipEqFast;
use risingwave_common::util::stream_graph_visitor::{
    self, visit_stream_node_cont, visit_stream_node_cont_mut,
};
use risingwave_connector::sink::catalog::SinkType;
use risingwave_meta_model::WorkerId;
use risingwave_pb::catalog::{PbSink, PbTable, Table};
use risingwave_pb::ddl_service::TableJobType;
use risingwave_pb::plan_common::{PbColumnCatalog, PbColumnDesc};
use risingwave_pb::stream_plan::dispatch_output_mapping::TypePair;
use risingwave_pb::stream_plan::stream_fragment_graph::{
    Parallelism, StreamFragment, StreamFragmentEdge as StreamFragmentEdgeProto,
};
use risingwave_pb::stream_plan::stream_node::{NodeBody, PbNodeBody};
use risingwave_pb::stream_plan::{
    BackfillOrder, DispatchOutputMapping, DispatchStrategy, DispatcherType, PbStreamNode,
    PbStreamScanType, StreamFragmentGraph as StreamFragmentGraphProto, StreamNode, StreamScanNode,
    StreamScanType,
};

use crate::barrier::SnapshotBackfillInfo;
use crate::controller::id::IdGeneratorManager;
use crate::manager::{MetaSrvEnv, StreamingJob, StreamingJobType};
use crate::model::{ActorId, Fragment, FragmentId, StreamActor};
use crate::stream::stream_graph::id::{
    GlobalActorIdGen, GlobalFragmentId, GlobalFragmentIdGen, GlobalTableIdGen,
};
use crate::stream::stream_graph::schedule::Distribution;
use crate::{MetaError, MetaResult};

/// The fragment in the building phase, including the [`StreamFragment`] from the frontend and
/// several additional helper fields.
#[derive(Debug, Clone)]
pub(super) struct BuildingFragment {
    /// The fragment structure from the frontend, with the global fragment ID.
    inner: StreamFragment,

    /// The ID of the job if it contains the streaming job node.
    job_id: Option<u32>,

    /// The required column IDs of each upstream table.
    /// Will be converted to indices when building the edge connected to the upstream.
    ///
    /// For shared CDC table on source, its `vec![]`, since the upstream source's output schema is fixed.
    upstream_table_columns: HashMap<TableId, Vec<PbColumnDesc>>,
}

impl BuildingFragment {
    /// Create a new [`BuildingFragment`] from a [`StreamFragment`]. The global fragment ID and
    /// global table IDs will be correctly filled with the given `id` and `table_id_gen`.
    fn new(
        id: GlobalFragmentId,
        fragment: StreamFragment,
        job: &StreamingJob,
        table_id_gen: GlobalTableIdGen,
    ) -> Self {
        let mut fragment = StreamFragment {
            fragment_id: id.as_global_id(),
            ..fragment
        };

        // Fill the information of the internal tables in the fragment.
        Self::fill_internal_tables(&mut fragment, job, table_id_gen);

        let job_id = Self::fill_job(&mut fragment, job).then(|| job.id());
        let upstream_table_columns =
            Self::extract_upstream_table_columns_except_cross_db_backfill(&fragment);

        Self {
            inner: fragment,
            job_id,
            upstream_table_columns,
        }
    }

    /// Extract the internal tables from the fragment.
    fn extract_internal_tables(&self) -> Vec<Table> {
        let mut fragment = self.inner.to_owned();
        let mut tables = Vec::new();
        stream_graph_visitor::visit_internal_tables(&mut fragment, |table, _| {
            tables.push(table.clone());
        });
        tables
    }

    /// Fill the information with the internal tables in the fragment.
    fn fill_internal_tables(
        fragment: &mut StreamFragment,
        job: &StreamingJob,
        table_id_gen: GlobalTableIdGen,
    ) {
        let fragment_id = fragment.fragment_id;
        stream_graph_visitor::visit_internal_tables(fragment, |table, table_type_name| {
            table.id = table_id_gen.to_global_id(table.id).as_global_id();
            table.schema_id = job.schema_id();
            table.database_id = job.database_id();
            table.name = generate_internal_table_name_with_type(
                &job.name(),
                fragment_id,
                table.id,
                table_type_name,
            );
            table.fragment_id = fragment_id;
            table.owner = job.owner();
            table.job_id = Some(job.id());
        });
    }

    /// Fill the information with the job in the fragment.
    fn fill_job(fragment: &mut StreamFragment, job: &StreamingJob) -> bool {
        let job_id = job.id();
        let fragment_id = fragment.fragment_id;
        let mut has_job = false;

        stream_graph_visitor::visit_fragment_mut(fragment, |node_body| match node_body {
            NodeBody::Materialize(materialize_node) => {
                materialize_node.table_id = job_id;

                // Fill the table field of `MaterializeNode` from the job.
                let table = materialize_node.table.insert(job.table().unwrap().clone());
                table.fragment_id = fragment_id; // this will later be synced back to `job.table` with `set_info_from_graph`
                // In production, do not include full definition in the table in plan node.
                if cfg!(not(debug_assertions)) {
                    table.definition = job.name();
                }

                has_job = true;
            }
            NodeBody::Sink(sink_node) => {
                sink_node.sink_desc.as_mut().unwrap().id = job_id;

                has_job = true;
            }
            NodeBody::Dml(dml_node) => {
                dml_node.table_id = job_id;
                dml_node.table_version_id = job.table_version_id().unwrap();
            }
            NodeBody::StreamFsFetch(fs_fetch_node) => {
                if let StreamingJob::Table(table_source, _, _) = job
                    && let Some(node_inner) = fs_fetch_node.node_inner.as_mut()
                    && let Some(source) = table_source
                {
                    node_inner.source_id = source.id;
                }
            }
            NodeBody::Source(source_node) => {
                match job {
                    // Note: For table without connector, it has a dummy Source node.
                    // Note: For table with connector, it's source node has a source id different with the table id (job id), assigned in create_job_catalog.
                    StreamingJob::Table(source, _table, _table_job_type) => {
                        if let Some(source_inner) = source_node.source_inner.as_mut()
                            && let Some(source) = source
                        {
                            debug_assert_ne!(source.id, job_id);
                            source_inner.source_id = source.id;
                        }
                    }
                    StreamingJob::Source(source) => {
                        has_job = true;
                        if let Some(source_inner) = source_node.source_inner.as_mut() {
                            debug_assert_eq!(source.id, job_id);
                            source_inner.source_id = source.id;
                        }
                    }
                    // For other job types, no need to fill the source id, since it refers to an existing source.
                    _ => {}
                }
            }
            NodeBody::StreamCdcScan(node) => {
                if let Some(table_desc) = node.cdc_table_desc.as_mut() {
                    table_desc.table_id = job_id;
                }
            }
            _ => {}
        });

        has_job
    }

    /// Extract the required columns of each upstream table except for cross-db backfill.
    fn extract_upstream_table_columns_except_cross_db_backfill(
        fragment: &StreamFragment,
    ) -> HashMap<TableId, Vec<PbColumnDesc>> {
        let mut table_columns = HashMap::new();

        stream_graph_visitor::visit_fragment(fragment, |node_body| {
            let (table_id, column_ids) = match node_body {
                NodeBody::StreamScan(stream_scan) => {
                    if stream_scan.get_stream_scan_type().unwrap()
                        == StreamScanType::CrossDbSnapshotBackfill
                    {
                        return;
                    }
                    (stream_scan.table_id.into(), stream_scan.upstream_columns())
                }
                NodeBody::CdcFilter(cdc_filter) => (cdc_filter.upstream_source_id.into(), vec![]),
                NodeBody::SourceBackfill(backfill) => (
                    backfill.upstream_source_id.into(),
                    // FIXME: only pass required columns instead of all columns here
                    backfill.column_descs(),
                ),
                _ => return,
            };
            table_columns
                .try_insert(table_id, column_ids)
                .expect("currently there should be no two same upstream tables in a fragment");
        });

        table_columns
    }

    pub fn has_shuffled_backfill(&self) -> bool {
        let stream_node = match self.inner.node.as_ref() {
            Some(node) => node,
            _ => return false,
        };
        let mut has_shuffled_backfill = false;
        let has_shuffled_backfill_mut_ref = &mut has_shuffled_backfill;
        visit_stream_node_cont(stream_node, |node| {
            let is_shuffled_backfill = if let Some(node) = &node.node_body
                && let Some(node) = node.as_stream_scan()
            {
                node.stream_scan_type == StreamScanType::ArrangementBackfill as i32
                    || node.stream_scan_type == StreamScanType::SnapshotBackfill as i32
            } else {
                false
            };
            if is_shuffled_backfill {
                *has_shuffled_backfill_mut_ref = true;
                false
            } else {
                true
            }
        });
        has_shuffled_backfill
    }
}

impl Deref for BuildingFragment {
    type Target = StreamFragment;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for BuildingFragment {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

/// The ID of an edge in the fragment graph. For different types of edges, the ID will be in
/// different variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumAsInner)]
pub(super) enum EdgeId {
    /// The edge between two building (internal) fragments.
    Internal {
        /// The ID generated by the frontend, generally the operator ID of `Exchange`.
        /// See [`StreamFragmentEdgeProto`].
        link_id: u64,
    },

    /// The edge between an upstream external fragment and downstream building fragment. Used for
    /// MV on MV.
    UpstreamExternal {
        /// The ID of the upstream table or materialized view.
        upstream_table_id: TableId,
        /// The ID of the downstream fragment.
        downstream_fragment_id: GlobalFragmentId,
    },

    /// The edge between an upstream building fragment and downstream external fragment. Used for
    /// schema change (replace table plan).
    DownstreamExternal(DownstreamExternalEdgeId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct DownstreamExternalEdgeId {
    /// The ID of the original upstream fragment (`Materialize`).
    pub(super) original_upstream_fragment_id: GlobalFragmentId,
    /// The ID of the downstream fragment.
    pub(super) downstream_fragment_id: GlobalFragmentId,
}

/// The edge in the fragment graph.
///
/// The edge can be either internal or external. This is distinguished by the [`EdgeId`].
#[derive(Debug, Clone)]
pub(super) struct StreamFragmentEdge {
    /// The ID of the edge.
    pub id: EdgeId,

    /// The strategy used for dispatching the data.
    pub dispatch_strategy: DispatchStrategy,
}

impl StreamFragmentEdge {
    fn from_protobuf(edge: &StreamFragmentEdgeProto) -> Self {
        Self {
            // By creating an edge from the protobuf, we know that the edge is from the frontend and
            // is internal.
            id: EdgeId::Internal {
                link_id: edge.link_id,
            },
            dispatch_strategy: edge.get_dispatch_strategy().unwrap().clone(),
        }
    }
}

fn clone_fragment(fragment: &Fragment, id_generator_manager: &IdGeneratorManager) -> Fragment {
    let fragment_id = GlobalFragmentIdGen::new(id_generator_manager, 1)
        .to_global_id(0)
        .as_global_id();
    let actor_id_gen = GlobalActorIdGen::new(id_generator_manager, fragment.actors.len() as _);
    Fragment {
        fragment_id,
        fragment_type_mask: fragment.fragment_type_mask,
        distribution_type: fragment.distribution_type,
        actors: fragment
            .actors
            .iter()
            .enumerate()
            .map(|(i, actor)| StreamActor {
                actor_id: actor_id_gen.to_global_id(i as _).as_global_id() as _,
                fragment_id,
                vnode_bitmap: actor.vnode_bitmap.clone(),
                mview_definition: actor.mview_definition.clone(),
                expr_context: actor.expr_context.clone(),
            })
            .collect(),
        state_table_ids: fragment.state_table_ids.clone(),
        maybe_vnode_count: fragment.maybe_vnode_count,
        nodes: fragment.nodes.clone(),
    }
}

pub fn check_sink_fragments_support_refresh_schema(
    fragments: &BTreeMap<FragmentId, Fragment>,
) -> MetaResult<()> {
    if fragments.len() != 1 {
        return Err(anyhow!(
            "sink with auto schema change should have only 1 fragment, but got {:?}",
            fragments.len()
        )
        .into());
    }
    let (_, fragment) = fragments.first_key_value().expect("non-empty");
    let sink_node = &fragment.nodes;
    let PbNodeBody::Sink(_) = sink_node.node_body.as_ref().unwrap() else {
        return Err(anyhow!("expect PbNodeBody::Sink but got: {:?}", sink_node.node_body).into());
    };
    let [stream_scan_node] = sink_node.input.as_slice() else {
        panic!("Sink has more than 1 input: {:?}", sink_node.input);
    };
    let PbNodeBody::StreamScan(scan) = stream_scan_node.node_body.as_ref().unwrap() else {
        return Err(anyhow!(
            "expect PbNodeBody::StreamScan but got: {:?}",
            stream_scan_node.node_body
        )
        .into());
    };
    let stream_scan_type = PbStreamScanType::try_from(scan.stream_scan_type).unwrap();
    if stream_scan_type != PbStreamScanType::ArrangementBackfill {
        return Err(anyhow!(
            "unsupported stream_scan_type for auto refresh schema: {:?}",
            stream_scan_type
        )
        .into());
    }
    let [merge_node, _batch_plan_node] = stream_scan_node.input.as_slice() else {
        panic!(
            "the number of StreamScan inputs is not 2: {:?}",
            stream_scan_node.input
        );
    };
    let NodeBody::Merge(_) = merge_node.node_body.as_ref().unwrap() else {
        return Err(anyhow!(
            "expect PbNodeBody::Merge but got: {:?}",
            merge_node.node_body
        )
        .into());
    };
    Ok(())
}

pub fn rewrite_refresh_schema_sink_fragment(
    original_sink_fragment: &Fragment,
    sink: &PbSink,
    newly_added_columns: &[ColumnCatalog],
    upstream_table: &PbTable,
    upstream_table_fragment_id: FragmentId,
    id_generator_manager: &IdGeneratorManager,
) -> MetaResult<(Fragment, Vec<PbColumnCatalog>, Option<PbTable>)> {
    let mut new_sink_columns = sink.columns.clone();
    fn extend_sink_columns(
        sink_columns: &mut Vec<PbColumnCatalog>,
        new_columns: &[ColumnCatalog],
        get_column_name: impl Fn(&String) -> String,
    ) {
        let next_column_id = sink_columns
            .iter()
            .map(|col| col.column_desc.as_ref().unwrap().column_id + 1)
            .max()
            .unwrap_or(1);
        sink_columns.extend(new_columns.iter().enumerate().map(|(i, col)| {
            let mut col = col.to_protobuf();
            let column_desc = col.column_desc.as_mut().unwrap();
            column_desc.column_id = next_column_id + (i as i32);
            column_desc.name = get_column_name(&column_desc.name);
            col
        }));
    }
    extend_sink_columns(&mut new_sink_columns, newly_added_columns, |name| {
        name.clone()
    });

    let mut new_sink_fragment = clone_fragment(original_sink_fragment, id_generator_manager);
    let sink_node = &mut new_sink_fragment.nodes;
    let PbNodeBody::Sink(sink_node_body) = sink_node.node_body.as_mut().unwrap() else {
        return Err(anyhow!("expect PbNodeBody::Sink but got: {:?}", sink_node.node_body).into());
    };
    let [stream_scan_node] = sink_node.input.as_mut_slice() else {
        panic!("Sink has more than 1 input: {:?}", sink_node.input);
    };
    let PbNodeBody::StreamScan(scan) = stream_scan_node.node_body.as_mut().unwrap() else {
        return Err(anyhow!(
            "expect PbNodeBody::StreamScan but got: {:?}",
            stream_scan_node.node_body
        )
        .into());
    };
    let [merge_node, _batch_plan_node] = stream_scan_node.input.as_mut_slice() else {
        panic!(
            "the number of StreamScan inputs is not 2: {:?}",
            stream_scan_node.input
        );
    };
    let NodeBody::Merge(merge) = merge_node.node_body.as_mut().unwrap() else {
        return Err(anyhow!(
            "expect PbNodeBody::Merge but got: {:?}",
            merge_node.node_body
        )
        .into());
    };
    // update sink_node
    // following logic in <StreamSink as Explain>::distill
    sink_node.identity = {
        let sink_type = SinkType::from_proto(sink.sink_type());
        let sink_type_str = if sink_type.is_append_only() {
            "append-only"
        } else {
            "upsert"
        };
        let column_names = new_sink_columns
            .iter()
            .map(|col| {
                ColumnCatalog::from(col.clone())
                    .name_with_hidden()
                    .to_string()
            })
            .join(", ");
        let downstream_pk = if sink_type.is_upsert() {
            let downstream_pk = sink
                .downstream_pk
                .iter()
                .map(|i| &sink.columns[*i as usize].column_desc.as_ref().unwrap().name)
                .collect_vec();
            format!(", downstream_pk: {downstream_pk:?}")
        } else {
            "".to_owned()
        };
        format!("StreamSink {{ type: {sink_type_str}, columns: [{column_names}]{downstream_pk} }}")
    };
    sink_node
        .fields
        .extend(newly_added_columns.iter().map(|col| {
            Field::new(
                format!("{}.{}", upstream_table.name, col.column_desc.name),
                col.data_type().clone(),
            )
            .to_prost()
        }));

    let new_log_store_table = if let Some(log_store_table) = &mut sink_node_body.table {
        extend_sink_columns(&mut log_store_table.columns, newly_added_columns, |name| {
            format!("{}_{}", upstream_table.name, name)
        });
        Some(log_store_table.clone())
    } else {
        None
    };
    sink_node_body.sink_desc.as_mut().unwrap().column_catalogs = new_sink_columns.clone();

    // update stream scan node
    stream_scan_node
        .fields
        .extend(newly_added_columns.iter().map(|col| {
            Field::new(
                format!("{}.{}", upstream_table.name, col.column_desc.name),
                col.data_type().clone(),
            )
            .to_prost()
        }));
    // following logic in <StreamTableScan as Explain>::distill
    stream_scan_node.identity = {
        let columns = stream_scan_node
            .fields
            .iter()
            .map(|col| &col.name)
            .join(", ");
        format!("StreamTableScan {{ table: t, columns: [{columns}] }}")
    };

    let stream_scan_type = PbStreamScanType::try_from(scan.stream_scan_type).unwrap();
    if stream_scan_type != PbStreamScanType::ArrangementBackfill {
        return Err(anyhow!(
            "unsupported stream_scan_type for auto refresh schema: {:?}",
            stream_scan_type
        )
        .into());
    }
    scan.arrangement_table = Some(upstream_table.clone());
    scan.output_indices.extend(
        (0..newly_added_columns.len()).map(|i| (i + scan.upstream_column_ids.len()) as u32),
    );
    scan.upstream_column_ids.extend(
        newly_added_columns
            .iter()
            .map(|col| col.column_id().get_id()),
    );
    let table_desc = scan.table_desc.as_mut().unwrap();
    table_desc
        .value_indices
        .extend((0..newly_added_columns.len()).map(|i| (i + table_desc.columns.len()) as u32));
    table_desc.columns.extend(
        newly_added_columns
            .iter()
            .map(|col| col.column_desc.to_protobuf()),
    );

    // update merge node
    merge_node.fields = scan
        .upstream_column_ids
        .iter()
        .map(|&column_id| {
            let col = upstream_table
                .columns
                .iter()
                .find(|c| c.column_desc.as_ref().unwrap().column_id == column_id)
                .unwrap();
            let col_desc = col.column_desc.as_ref().unwrap();
            Field::new(
                col_desc.name.clone(),
                col_desc.column_type.as_ref().unwrap().into(),
            )
            .to_prost()
        })
        .collect();
    merge.upstream_fragment_id = upstream_table_fragment_id;
    Ok((new_sink_fragment, new_sink_columns, new_log_store_table))
}

/// Adjacency list (G) of backfill orders.
/// `G[10] -> [1, 2, 11]`
/// means for the backfill node in `fragment 10`
/// should be backfilled before the backfill nodes in `fragment 1, 2 and 11`.
pub type FragmentBackfillOrder = HashMap<FragmentId, Vec<FragmentId>>;

/// In-memory representation of a **Fragment** Graph, built from the [`StreamFragmentGraphProto`]
/// from the frontend.
///
/// This only includes nodes and edges of the current job itself. It will be converted to [`CompleteStreamFragmentGraph`] later,
/// that contains the additional information of pre-existing
/// fragments, which are connected to the graph's top-most or bottom-most fragments.
#[derive(Default, Debug)]
pub struct StreamFragmentGraph {
    /// stores all the fragments in the graph.
    pub(super) fragments: HashMap<GlobalFragmentId, BuildingFragment>,

    /// stores edges between fragments: upstream => downstream.
    pub(super) downstreams:
        HashMap<GlobalFragmentId, HashMap<GlobalFragmentId, StreamFragmentEdge>>,

    /// stores edges between fragments: downstream -> upstream.
    pub(super) upstreams: HashMap<GlobalFragmentId, HashMap<GlobalFragmentId, StreamFragmentEdge>>,

    /// Dependent relations of this job.
    dependent_table_ids: HashSet<TableId>,

    /// The default parallelism of the job, specified by the `STREAMING_PARALLELISM` session
    /// variable. If not specified, all active worker slots will be used.
    specified_parallelism: Option<NonZeroUsize>,

    /// Specified max parallelism, i.e., expected vnode count for the graph.
    ///
    /// The scheduler on the meta service will use this as a hint to decide the vnode count
    /// for each fragment.
    ///
    /// Note that the actual vnode count may be different from this value.
    /// For example, a no-shuffle exchange between current fragment graph and an existing
    /// upstream fragment graph requires two fragments to be in the same distribution,
    /// thus the same vnode count.
    max_parallelism: usize,

    /// The backfill ordering strategy of the graph.
    backfill_order: BackfillOrder,
}

impl StreamFragmentGraph {
    /// Create a new [`StreamFragmentGraph`] from the given [`StreamFragmentGraphProto`], with all
    /// global IDs correctly filled.
    pub fn new(
        env: &MetaSrvEnv,
        proto: StreamFragmentGraphProto,
        job: &StreamingJob,
    ) -> MetaResult<Self> {
        let fragment_id_gen =
            GlobalFragmentIdGen::new(env.id_gen_manager(), proto.fragments.len() as u64);
        // Note: in SQL backend, the ids generated here are fake and will be overwritten again
        // with `refill_internal_table_ids` later.
        // TODO: refactor the code to remove this step.
        let table_id_gen = GlobalTableIdGen::new(env.id_gen_manager(), proto.table_ids_cnt as u64);

        // Create nodes.
        let fragments: HashMap<_, _> = proto
            .fragments
            .into_iter()
            .map(|(id, fragment)| {
                let id = fragment_id_gen.to_global_id(id);
                let fragment = BuildingFragment::new(id, fragment, job, table_id_gen);
                (id, fragment)
            })
            .collect();

        assert_eq!(
            fragments
                .values()
                .map(|f| f.extract_internal_tables().len() as u32)
                .sum::<u32>(),
            proto.table_ids_cnt
        );

        // Create edges.
        let mut downstreams = HashMap::new();
        let mut upstreams = HashMap::new();

        for edge in proto.edges {
            let upstream_id = fragment_id_gen.to_global_id(edge.upstream_id);
            let downstream_id = fragment_id_gen.to_global_id(edge.downstream_id);
            let edge = StreamFragmentEdge::from_protobuf(&edge);

            upstreams
                .entry(downstream_id)
                .or_insert_with(HashMap::new)
                .try_insert(upstream_id, edge.clone())
                .unwrap();
            downstreams
                .entry(upstream_id)
                .or_insert_with(HashMap::new)
                .try_insert(downstream_id, edge)
                .unwrap();
        }

        // Note: Here we directly use the field `dependent_table_ids` in the proto (resolved in
        // frontend), instead of visiting the graph ourselves.
        let dependent_table_ids = proto
            .dependent_table_ids
            .iter()
            .map(TableId::from)
            .collect();

        let specified_parallelism = if let Some(Parallelism { parallelism }) = proto.parallelism {
            Some(NonZeroUsize::new(parallelism as usize).context("parallelism should not be 0")?)
        } else {
            None
        };

        let max_parallelism = proto.max_parallelism as usize;
        let backfill_order = proto.backfill_order.unwrap_or(BackfillOrder {
            order: Default::default(),
        });

        Ok(Self {
            fragments,
            downstreams,
            upstreams,
            dependent_table_ids,
            specified_parallelism,
            max_parallelism,
            backfill_order,
        })
    }

    /// Retrieve the **incomplete** internal tables map of the whole graph.
    ///
    /// Note that some fields in the table catalogs are not filled during the current phase, e.g.,
    /// `fragment_id`, `vnode_count`. They will be all filled after a `TableFragments` is built.
    /// Be careful when using the returned values.
    pub fn incomplete_internal_tables(&self) -> BTreeMap<u32, Table> {
        let mut tables = BTreeMap::new();
        for fragment in self.fragments.values() {
            for table in fragment.extract_internal_tables() {
                let table_id = table.id;
                tables
                    .try_insert(table_id, table)
                    .unwrap_or_else(|_| panic!("duplicated table id `{}`", table_id));
            }
        }
        tables
    }

    /// Refill the internal tables' `table_id`s according to the given map, typically obtained from
    /// `create_internal_table_catalog`.
    pub fn refill_internal_table_ids(&mut self, table_id_map: HashMap<u32, u32>) {
        for fragment in self.fragments.values_mut() {
            stream_graph_visitor::visit_internal_tables(
                &mut fragment.inner,
                |table, _table_type_name| {
                    let target = table_id_map.get(&table.id).cloned().unwrap();
                    table.id = target;
                },
            );
        }
    }

    /// Use a trivial algorithm to match the internal tables of the new graph for
    /// `ALTER TABLE` or `ALTER SOURCE`.
    pub fn fit_internal_tables_trivial(
        &mut self,
        mut old_internal_tables: Vec<Table>,
    ) -> MetaResult<()> {
        let mut new_internal_table_ids = Vec::new();
        for fragment in self.fragments.values() {
            for table in &fragment.extract_internal_tables() {
                new_internal_table_ids.push(table.id);
            }
        }

        if new_internal_table_ids.len() != old_internal_tables.len() {
            bail!(
                "Different number of internal tables. New: {}, Old: {}",
                new_internal_table_ids.len(),
                old_internal_tables.len()
            );
        }
        old_internal_tables.sort_by(|a, b| a.id.cmp(&b.id));
        new_internal_table_ids.sort();

        let internal_table_id_map = new_internal_table_ids
            .into_iter()
            .zip_eq_fast(old_internal_tables.into_iter())
            .collect::<HashMap<_, _>>();

        // TODO(alter-mv): unify this with `fit_internal_table_ids_with_mapping` after we
        // confirm the behavior is the same.
        for fragment in self.fragments.values_mut() {
            stream_graph_visitor::visit_internal_tables(
                &mut fragment.inner,
                |table, _table_type_name| {
                    // XXX: this replaces the entire table, instead of just the id!
                    let target = internal_table_id_map.get(&table.id).cloned().unwrap();
                    *table = target;
                },
            );
        }

        Ok(())
    }

    /// Fit the internal tables' `table_id`s according to the given mapping.
    pub fn fit_internal_table_ids_with_mapping(&mut self, mut matches: HashMap<u32, Table>) {
        for fragment in self.fragments.values_mut() {
            stream_graph_visitor::visit_internal_tables(
                &mut fragment.inner,
                |table, _table_type_name| {
                    let target = matches.remove(&table.id).unwrap_or_else(|| {
                        panic!("no matching table for table {}({})", table.id, table.name)
                    });
                    table.id = target.id;
                    table.maybe_vnode_count = target.maybe_vnode_count;
                },
            );
        }
    }

    /// Returns the fragment id where the streaming job node located.
    pub fn table_fragment_id(&self) -> FragmentId {
        self.fragments
            .values()
            .filter(|b| b.job_id.is_some())
            .map(|b| b.fragment_id)
            .exactly_one()
            .expect("require exactly 1 materialize/sink/cdc source node when creating the streaming job")
    }

    /// Returns the fragment id where the table dml is received.
    pub fn dml_fragment_id(&self) -> Option<FragmentId> {
        self.fragments
            .values()
            .filter(|b| {
                FragmentTypeMask::from(b.fragment_type_mask).contains(FragmentTypeFlag::Dml)
            })
            .map(|b| b.fragment_id)
            .at_most_one()
            .expect("require at most 1 dml node when creating the streaming job")
    }

    /// Get the dependent streaming job ids of this job.
    pub fn dependent_table_ids(&self) -> &HashSet<TableId> {
        &self.dependent_table_ids
    }

    /// Get the parallelism of the job, if specified by the user.
    pub fn specified_parallelism(&self) -> Option<NonZeroUsize> {
        self.specified_parallelism
    }

    /// Get the expected vnode count of the graph. See documentation of the field for more details.
    pub fn max_parallelism(&self) -> usize {
        self.max_parallelism
    }

    /// Get downstreams of a fragment.
    fn get_downstreams(
        &self,
        fragment_id: GlobalFragmentId,
    ) -> &HashMap<GlobalFragmentId, StreamFragmentEdge> {
        self.downstreams.get(&fragment_id).unwrap_or(&EMPTY_HASHMAP)
    }

    /// Get upstreams of a fragment.
    fn get_upstreams(
        &self,
        fragment_id: GlobalFragmentId,
    ) -> &HashMap<GlobalFragmentId, StreamFragmentEdge> {
        self.upstreams.get(&fragment_id).unwrap_or(&EMPTY_HASHMAP)
    }

    pub fn collect_snapshot_backfill_info(
        &self,
    ) -> MetaResult<(Option<SnapshotBackfillInfo>, SnapshotBackfillInfo)> {
        Self::collect_snapshot_backfill_info_impl(self.fragments.values().map(|fragment| {
            (
                fragment.node.as_ref().unwrap(),
                fragment.fragment_type_mask.into(),
            )
        }))
    }

    /// Returns `Ok((Some(``snapshot_backfill_info``), ``cross_db_snapshot_backfill_info``))`
    pub fn collect_snapshot_backfill_info_impl(
        fragments: impl IntoIterator<Item = (&PbStreamNode, FragmentTypeMask)>,
    ) -> MetaResult<(Option<SnapshotBackfillInfo>, SnapshotBackfillInfo)> {
        let mut prev_stream_scan: Option<(Option<SnapshotBackfillInfo>, StreamScanNode)> = None;
        let mut cross_db_info = SnapshotBackfillInfo {
            upstream_mv_table_id_to_backfill_epoch: Default::default(),
        };
        let mut result = Ok(());
        for (node, fragment_type_mask) in fragments {
            visit_stream_node_cont(node, |node| {
                if let Some(NodeBody::StreamScan(stream_scan)) = node.node_body.as_ref() {
                    let stream_scan_type = StreamScanType::try_from(stream_scan.stream_scan_type)
                        .expect("invalid stream_scan_type");
                    let is_snapshot_backfill = match stream_scan_type {
                        StreamScanType::SnapshotBackfill => {
                            assert!(
                                fragment_type_mask
                                    .contains(FragmentTypeFlag::SnapshotBackfillStreamScan)
                            );
                            true
                        }
                        StreamScanType::CrossDbSnapshotBackfill => {
                            assert!(
                                fragment_type_mask
                                    .contains(FragmentTypeFlag::CrossDbSnapshotBackfillStreamScan)
                            );
                            cross_db_info.upstream_mv_table_id_to_backfill_epoch.insert(
                                TableId::new(stream_scan.table_id),
                                stream_scan.snapshot_backfill_epoch,
                            );

                            return true;
                        }
                        _ => false,
                    };

                    match &mut prev_stream_scan {
                        Some((prev_snapshot_backfill_info, prev_stream_scan)) => {
                            match (prev_snapshot_backfill_info, is_snapshot_backfill) {
                                (Some(prev_snapshot_backfill_info), true) => {
                                    prev_snapshot_backfill_info
                                        .upstream_mv_table_id_to_backfill_epoch
                                        .insert(
                                            TableId::new(stream_scan.table_id),
                                            stream_scan.snapshot_backfill_epoch,
                                        );
                                    true
                                }
                                (None, false) => true,
                                (_, _) => {
                                    result = Err(anyhow!("must be either all snapshot_backfill or no snapshot_backfill. Curr: {stream_scan:?} Prev: {prev_stream_scan:?}").into());
                                    false
                                }
                            }
                        }
                        None => {
                            prev_stream_scan = Some((
                                if is_snapshot_backfill {
                                    Some(SnapshotBackfillInfo {
                                        upstream_mv_table_id_to_backfill_epoch: HashMap::from_iter(
                                            [(
                                                TableId::new(stream_scan.table_id),
                                                stream_scan.snapshot_backfill_epoch,
                                            )],
                                        ),
                                    })
                                } else {
                                    None
                                },
                                *stream_scan.clone(),
                            ));
                            true
                        }
                    }
                } else {
                    true
                }
            })
        }
        result.map(|_| {
            (
                prev_stream_scan
                    .map(|(snapshot_backfill_info, _)| snapshot_backfill_info)
                    .unwrap_or(None),
                cross_db_info,
            )
        })
    }

    /// Collect the mapping from table / `source_id` -> `fragment_id`
    pub fn collect_backfill_mapping(&self) -> HashMap<u32, Vec<FragmentId>> {
        let mut mapping = HashMap::new();
        for (fragment_id, fragment) in &self.fragments {
            let fragment_id = fragment_id.as_global_id();
            let fragment_mask = fragment.fragment_type_mask;
            let candidates = [FragmentTypeFlag::StreamScan, FragmentTypeFlag::SourceScan];
            let has_some_scan = candidates
                .into_iter()
                .any(|flag| (fragment_mask & flag as u32) > 0);
            if has_some_scan {
                visit_stream_node_cont(fragment.node.as_ref().unwrap(), |node| {
                    match node.node_body.as_ref() {
                        Some(NodeBody::StreamScan(stream_scan)) => {
                            let table_id = stream_scan.table_id;
                            let fragments: &mut Vec<_> = mapping.entry(table_id).or_default();
                            fragments.push(fragment_id);
                            // each fragment should have only 1 scan node.
                            false
                        }
                        Some(NodeBody::SourceBackfill(source_backfill)) => {
                            let source_id = source_backfill.upstream_source_id;
                            let fragments: &mut Vec<_> = mapping.entry(source_id).or_default();
                            fragments.push(fragment_id);
                            // each fragment should have only 1 scan node.
                            false
                        }
                        _ => true,
                    }
                })
            }
        }
        mapping
    }

    /// Initially the mapping that comes from frontend is between `table_ids`.
    /// We should remap it to fragment level, since we track progress by actor, and we can get
    /// a fragment <-> actor mapping
    pub fn create_fragment_backfill_ordering(&self) -> FragmentBackfillOrder {
        let mapping = self.collect_backfill_mapping();
        let mut fragment_ordering: HashMap<u32, Vec<u32>> = HashMap::new();
        for (rel_id, downstream_rel_ids) in &self.backfill_order.order {
            let fragment_ids = mapping.get(rel_id).unwrap();
            for fragment_id in fragment_ids {
                let downstream_fragment_ids = downstream_rel_ids
                    .data
                    .iter()
                    .flat_map(|downstream_rel_id| mapping.get(downstream_rel_id).unwrap().iter())
                    .copied()
                    .collect();
                fragment_ordering.insert(*fragment_id, downstream_fragment_ids);
            }
        }
        fragment_ordering
    }
}

/// Fill snapshot epoch for `StreamScanNode` of `SnapshotBackfill`.
/// Return `true` when has change applied.
pub fn fill_snapshot_backfill_epoch(
    node: &mut StreamNode,
    snapshot_backfill_info: Option<&SnapshotBackfillInfo>,
    cross_db_snapshot_backfill_info: &SnapshotBackfillInfo,
) -> MetaResult<bool> {
    let mut result = Ok(());
    let mut applied = false;
    visit_stream_node_cont_mut(node, |node| {
        if let Some(NodeBody::StreamScan(stream_scan)) = node.node_body.as_mut()
            && (stream_scan.stream_scan_type == StreamScanType::SnapshotBackfill as i32
                || stream_scan.stream_scan_type == StreamScanType::CrossDbSnapshotBackfill as i32)
        {
            result = try {
                let table_id = TableId::new(stream_scan.table_id);
                let snapshot_epoch = cross_db_snapshot_backfill_info
                    .upstream_mv_table_id_to_backfill_epoch
                    .get(&table_id)
                    .or_else(|| {
                        snapshot_backfill_info.and_then(|snapshot_backfill_info| {
                            snapshot_backfill_info
                                .upstream_mv_table_id_to_backfill_epoch
                                .get(&table_id)
                        })
                    })
                    .ok_or_else(|| anyhow!("upstream table id not covered: {}", table_id))?
                    .ok_or_else(|| anyhow!("upstream table id not set: {}", table_id))?;
                if let Some(prev_snapshot_epoch) =
                    stream_scan.snapshot_backfill_epoch.replace(snapshot_epoch)
                {
                    Err(anyhow!(
                        "snapshot backfill epoch set again: {} {} {}",
                        table_id,
                        prev_snapshot_epoch,
                        snapshot_epoch
                    ))?;
                }
                applied = true;
            };
            result.is_ok()
        } else {
            true
        }
    });
    result.map(|_| applied)
}

static EMPTY_HASHMAP: LazyLock<HashMap<GlobalFragmentId, StreamFragmentEdge>> =
    LazyLock::new(HashMap::new);

/// A fragment that is either being built or already exists. Used for generalize the logic of
/// [`crate::stream::ActorGraphBuilder`].
#[derive(Debug, Clone, EnumAsInner)]
pub(super) enum EitherFragment {
    /// An internal fragment that is being built for the current streaming job.
    Building(BuildingFragment),

    /// An existing fragment that is external but connected to the fragments being built.
    Existing(Fragment),
}

/// A wrapper of [`StreamFragmentGraph`] that contains the additional information of pre-existing
/// fragments, which are connected to the graph's top-most or bottom-most fragments.
///
/// For example,
/// - if we're going to build a mview on an existing mview, the upstream fragment containing the
///   `Materialize` node will be included in this structure.
/// - if we're going to replace the plan of a table with downstream mviews, the downstream fragments
///   containing the `StreamScan` nodes will be included in this structure.
#[derive(Debug)]
pub struct CompleteStreamFragmentGraph {
    /// The fragment graph of the streaming job being built.
    building_graph: StreamFragmentGraph,

    /// The required information of existing fragments.
    existing_fragments: HashMap<GlobalFragmentId, Fragment>,

    /// The location of the actors in the existing fragments.
    existing_actor_location: HashMap<ActorId, WorkerId>,

    /// Extra edges between existing fragments and the building fragments.
    extra_downstreams: HashMap<GlobalFragmentId, HashMap<GlobalFragmentId, StreamFragmentEdge>>,

    /// Extra edges between existing fragments and the building fragments.
    extra_upstreams: HashMap<GlobalFragmentId, HashMap<GlobalFragmentId, StreamFragmentEdge>>,
}

pub struct FragmentGraphUpstreamContext {
    /// Root fragment is the root of upstream stream graph, which can be a
    /// mview fragment or source fragment for cdc source job
    upstream_root_fragments: HashMap<TableId, Fragment>,
    upstream_actor_location: HashMap<ActorId, WorkerId>,
}

pub struct FragmentGraphDownstreamContext {
    original_root_fragment_id: FragmentId,
    downstream_fragments: Vec<(DispatcherType, Fragment)>,
    downstream_actor_location: HashMap<ActorId, WorkerId>,
}

impl CompleteStreamFragmentGraph {
    /// Create a new [`CompleteStreamFragmentGraph`] with empty existing fragments, i.e., there's no
    /// upstream mviews.
    #[cfg(test)]
    pub fn for_test(graph: StreamFragmentGraph) -> Self {
        Self {
            building_graph: graph,
            existing_fragments: Default::default(),
            existing_actor_location: Default::default(),
            extra_downstreams: Default::default(),
            extra_upstreams: Default::default(),
        }
    }

    /// Create a new [`CompleteStreamFragmentGraph`] for newly created job (which has no downstreams).
    /// e.g., MV on MV and CDC/Source Table with the upstream existing
    /// `Materialize` or `Source` fragments.
    pub fn with_upstreams(
        graph: StreamFragmentGraph,
        upstream_root_fragments: HashMap<TableId, Fragment>,
        existing_actor_location: HashMap<ActorId, WorkerId>,
        job_type: StreamingJobType,
    ) -> MetaResult<Self> {
        Self::build_helper(
            graph,
            Some(FragmentGraphUpstreamContext {
                upstream_root_fragments,
                upstream_actor_location: existing_actor_location,
            }),
            None,
            job_type,
        )
    }

    /// Create a new [`CompleteStreamFragmentGraph`] for replacing an existing table/source,
    /// with the downstream existing `StreamScan`/`StreamSourceScan` fragments.
    pub fn with_downstreams(
        graph: StreamFragmentGraph,
        original_root_fragment_id: FragmentId,
        downstream_fragments: Vec<(DispatcherType, Fragment)>,
        existing_actor_location: HashMap<ActorId, WorkerId>,
        job_type: StreamingJobType,
    ) -> MetaResult<Self> {
        Self::build_helper(
            graph,
            None,
            Some(FragmentGraphDownstreamContext {
                original_root_fragment_id,
                downstream_fragments,
                downstream_actor_location: existing_actor_location,
            }),
            job_type,
        )
    }

    /// For replacing an existing table based on shared cdc source, which has both upstreams and downstreams.
    pub fn with_upstreams_and_downstreams(
        graph: StreamFragmentGraph,
        upstream_root_fragments: HashMap<TableId, Fragment>,
        upstream_actor_location: HashMap<ActorId, WorkerId>,
        original_root_fragment_id: FragmentId,
        downstream_fragments: Vec<(DispatcherType, Fragment)>,
        downstream_actor_location: HashMap<ActorId, WorkerId>,
        job_type: StreamingJobType,
    ) -> MetaResult<Self> {
        Self::build_helper(
            graph,
            Some(FragmentGraphUpstreamContext {
                upstream_root_fragments,
                upstream_actor_location,
            }),
            Some(FragmentGraphDownstreamContext {
                original_root_fragment_id,
                downstream_fragments,
                downstream_actor_location,
            }),
            job_type,
        )
    }

    /// The core logic of building a [`CompleteStreamFragmentGraph`], i.e., adding extra upstream/downstream fragments.
    fn build_helper(
        mut graph: StreamFragmentGraph,
        upstream_ctx: Option<FragmentGraphUpstreamContext>,
        downstream_ctx: Option<FragmentGraphDownstreamContext>,
        job_type: StreamingJobType,
    ) -> MetaResult<Self> {
        let mut extra_downstreams = HashMap::new();
        let mut extra_upstreams = HashMap::new();
        let mut existing_fragments = HashMap::new();

        let mut existing_actor_location = HashMap::new();

        if let Some(FragmentGraphUpstreamContext {
            upstream_root_fragments,
            upstream_actor_location,
        }) = upstream_ctx
        {
            for (&id, fragment) in &mut graph.fragments {
                let uses_shuffled_backfill = fragment.has_shuffled_backfill();

                for (&upstream_table_id, required_columns) in &fragment.upstream_table_columns {
                    let upstream_fragment = upstream_root_fragments
                        .get(&upstream_table_id)
                        .context("upstream fragment not found")?;
                    let upstream_root_fragment_id =
                        GlobalFragmentId::new(upstream_fragment.fragment_id);

                    let edge = match job_type {
                        StreamingJobType::Table(TableJobType::SharedCdcSource) => {
                            // we traverse all fragments in the graph, and we should find out the
                            // CdcFilter fragment and add an edge between upstream source fragment and it.
                            assert_ne!(
                                (fragment.fragment_type_mask & FragmentTypeFlag::CdcFilter as u32),
                                0
                            );

                            tracing::debug!(
                                ?upstream_root_fragment_id,
                                ?required_columns,
                                identity = ?fragment.inner.get_node().unwrap().get_identity(),
                                current_frag_id=?id,
                                "CdcFilter with upstream source fragment"
                            );

                            StreamFragmentEdge {
                                id: EdgeId::UpstreamExternal {
                                    upstream_table_id,
                                    downstream_fragment_id: id,
                                },
                                // We always use `NoShuffle` for the exchange between the upstream
                                // `Source` and the downstream `StreamScan` of the new cdc table.
                                dispatch_strategy: DispatchStrategy {
                                    r#type: DispatcherType::NoShuffle as _,
                                    dist_key_indices: vec![], // not used for `NoShuffle`
                                    output_mapping: DispatchOutputMapping::identical(
                                        CDC_SOURCE_COLUMN_NUM as _,
                                    )
                                    .into(),
                                },
                            }
                        }

                        // handle MV on MV/Source
                        StreamingJobType::MaterializedView
                        | StreamingJobType::Sink
                        | StreamingJobType::Index => {
                            // Build the extra edges between the upstream `Materialize` and
                            // the downstream `StreamScan` of the new job.
                            if upstream_fragment
                                .fragment_type_mask
                                .contains(FragmentTypeFlag::Mview)
                            {
                                // Resolve the required output columns from the upstream materialized view.
                                let (dist_key_indices, output_mapping) = {
                                    let nodes = &upstream_fragment.nodes;
                                    let mview_node =
                                        nodes.get_node_body().unwrap().as_materialize().unwrap();
                                    let all_columns = mview_node.column_descs();
                                    let dist_key_indices = mview_node.dist_key_indices();
                                    let output_mapping = gen_output_mapping(
                                        required_columns,
                                        &all_columns,
                                    )
                                    .context(
                                        "BUG: column not found in the upstream materialized view",
                                    )?;
                                    (dist_key_indices, output_mapping)
                                };
                                let dispatch_strategy = mv_on_mv_dispatch_strategy(
                                    uses_shuffled_backfill,
                                    dist_key_indices,
                                    output_mapping,
                                );

                                StreamFragmentEdge {
                                    id: EdgeId::UpstreamExternal {
                                        upstream_table_id,
                                        downstream_fragment_id: id,
                                    },
                                    dispatch_strategy,
                                }
                            }
                            // Build the extra edges between the upstream `Source` and
                            // the downstream `SourceBackfill` of the new job.
                            else if upstream_fragment
                                .fragment_type_mask
                                .contains(FragmentTypeFlag::Source)
                            {
                                let output_mapping = {
                                    let nodes = &upstream_fragment.nodes;
                                    let source_node =
                                        nodes.get_node_body().unwrap().as_source().unwrap();

                                    let all_columns = source_node.column_descs().unwrap();
                                    gen_output_mapping(required_columns, &all_columns).context(
                                        "BUG: column not found in the upstream source node",
                                    )?
                                };

                                StreamFragmentEdge {
                                    id: EdgeId::UpstreamExternal {
                                        upstream_table_id,
                                        downstream_fragment_id: id,
                                    },
                                    // We always use `NoShuffle` for the exchange between the upstream
                                    // `Source` and the downstream `StreamScan` of the new MV.
                                    dispatch_strategy: DispatchStrategy {
                                        r#type: DispatcherType::NoShuffle as _,
                                        dist_key_indices: vec![], // not used for `NoShuffle`
                                        output_mapping: Some(output_mapping),
                                    },
                                }
                            } else {
                                bail!(
                                    "the upstream fragment should be a MView or Source, got fragment type: {:b}",
                                    upstream_fragment.fragment_type_mask
                                )
                            }
                        }
                        StreamingJobType::Source | StreamingJobType::Table(_) => {
                            bail!(
                                "the streaming job shouldn't have an upstream fragment, job_type: {:?}",
                                job_type
                            )
                        }
                    };

                    // put the edge into the extra edges
                    extra_downstreams
                        .entry(upstream_root_fragment_id)
                        .or_insert_with(HashMap::new)
                        .try_insert(id, edge.clone())
                        .unwrap();
                    extra_upstreams
                        .entry(id)
                        .or_insert_with(HashMap::new)
                        .try_insert(upstream_root_fragment_id, edge)
                        .unwrap();
                }
            }

            existing_fragments.extend(
                upstream_root_fragments
                    .into_values()
                    .map(|f| (GlobalFragmentId::new(f.fragment_id), f)),
            );

            existing_actor_location.extend(upstream_actor_location);
        }

        if let Some(FragmentGraphDownstreamContext {
            original_root_fragment_id,
            downstream_fragments,
            downstream_actor_location,
        }) = downstream_ctx
        {
            let original_table_fragment_id = GlobalFragmentId::new(original_root_fragment_id);
            let table_fragment_id = GlobalFragmentId::new(graph.table_fragment_id());

            // Build the extra edges between the `Materialize` and the downstream `StreamScan` of the
            // existing materialized views.
            for (dispatcher_type, fragment) in &downstream_fragments {
                let id = GlobalFragmentId::new(fragment.fragment_id);

                // Similar to `extract_upstream_table_columns_except_cross_db_backfill`.
                let output_columns = {
                    let mut res = None;

                    stream_graph_visitor::visit_stream_node_body(&fragment.nodes, |node_body| {
                        let columns = match node_body {
                            NodeBody::StreamScan(stream_scan) => stream_scan.upstream_columns(),
                            NodeBody::SourceBackfill(source_backfill) => {
                                // FIXME: only pass required columns instead of all columns here
                                source_backfill.column_descs()
                            }
                            _ => return,
                        };
                        res = Some(columns);
                    });

                    res.context("failed to locate downstream scan")?
                };

                let table_fragment = graph.fragments.get(&table_fragment_id).unwrap();
                let nodes = table_fragment.node.as_ref().unwrap();

                let (dist_key_indices, output_mapping) = match job_type {
                    StreamingJobType::Table(_) | StreamingJobType::MaterializedView => {
                        let mview_node = nodes.get_node_body().unwrap().as_materialize().unwrap();
                        let all_columns = mview_node.column_descs();
                        let dist_key_indices = mview_node.dist_key_indices();
                        let output_mapping = gen_output_mapping(&output_columns, &all_columns)
                            .ok_or_else(|| {
                                MetaError::invalid_parameter(
                                    "unable to drop the column due to \
                                     being referenced by downstream materialized views or sinks",
                                )
                            })?;
                        (dist_key_indices, output_mapping)
                    }

                    StreamingJobType::Source => {
                        let source_node = nodes.get_node_body().unwrap().as_source().unwrap();
                        let all_columns = source_node.column_descs().unwrap();
                        let output_mapping = gen_output_mapping(&output_columns, &all_columns)
                            .ok_or_else(|| {
                                MetaError::invalid_parameter(
                                    "unable to drop the column due to \
                                     being referenced by downstream materialized views or sinks",
                                )
                            })?;
                        assert_eq!(*dispatcher_type, DispatcherType::NoShuffle);
                        (
                            vec![], // not used for `NoShuffle`
                            output_mapping,
                        )
                    }

                    _ => bail!("unsupported job type for replacement: {job_type:?}"),
                };

                let edge = StreamFragmentEdge {
                    id: EdgeId::DownstreamExternal(DownstreamExternalEdgeId {
                        original_upstream_fragment_id: original_table_fragment_id,
                        downstream_fragment_id: id,
                    }),
                    dispatch_strategy: DispatchStrategy {
                        r#type: *dispatcher_type as i32,
                        output_mapping: Some(output_mapping),
                        dist_key_indices,
                    },
                };

                extra_downstreams
                    .entry(table_fragment_id)
                    .or_insert_with(HashMap::new)
                    .try_insert(id, edge.clone())
                    .unwrap();
                extra_upstreams
                    .entry(id)
                    .or_insert_with(HashMap::new)
                    .try_insert(table_fragment_id, edge)
                    .unwrap();
            }

            existing_fragments.extend(
                downstream_fragments
                    .into_iter()
                    .map(|(_, f)| (GlobalFragmentId::new(f.fragment_id), f)),
            );

            existing_actor_location.extend(downstream_actor_location);
        }

        Ok(Self {
            building_graph: graph,
            existing_fragments,
            existing_actor_location,
            extra_downstreams,
            extra_upstreams,
        })
    }
}

/// Generate the `output_mapping` for [`DispatchStrategy`] from given columns.
fn gen_output_mapping(
    required_columns: &[PbColumnDesc],
    upstream_columns: &[PbColumnDesc],
) -> Option<DispatchOutputMapping> {
    let len = required_columns.len();
    let mut indices = vec![0; len];
    let mut types = None;

    for (i, r) in required_columns.iter().enumerate() {
        let (ui, u) = upstream_columns
            .iter()
            .find_position(|&u| u.column_id == r.column_id)?;
        indices[i] = ui as u32;

        // Only if we encounter type change (`ALTER TABLE ALTER COLUMN TYPE`) will we generate a
        // non-empty `types`.
        if u.column_type != r.column_type {
            types.get_or_insert_with(|| vec![TypePair::default(); len])[i] = TypePair {
                upstream: u.column_type.clone(),
                downstream: r.column_type.clone(),
            };
        }
    }

    // If there's no type change, indicate it by empty `types`.
    let types = types.unwrap_or(Vec::new());

    Some(DispatchOutputMapping { indices, types })
}

fn mv_on_mv_dispatch_strategy(
    uses_shuffled_backfill: bool,
    dist_key_indices: Vec<u32>,
    output_mapping: DispatchOutputMapping,
) -> DispatchStrategy {
    if uses_shuffled_backfill {
        if !dist_key_indices.is_empty() {
            DispatchStrategy {
                r#type: DispatcherType::Hash as _,
                dist_key_indices,
                output_mapping: Some(output_mapping),
            }
        } else {
            DispatchStrategy {
                r#type: DispatcherType::Simple as _,
                dist_key_indices: vec![], // empty for Simple
                output_mapping: Some(output_mapping),
            }
        }
    } else {
        DispatchStrategy {
            r#type: DispatcherType::NoShuffle as _,
            dist_key_indices: vec![], // not used for `NoShuffle`
            output_mapping: Some(output_mapping),
        }
    }
}

impl CompleteStreamFragmentGraph {
    /// Returns **all** fragment IDs in the complete graph, including the ones that are not in the
    /// building graph.
    pub(super) fn all_fragment_ids(&self) -> impl Iterator<Item = GlobalFragmentId> + '_ {
        self.building_graph
            .fragments
            .keys()
            .chain(self.existing_fragments.keys())
            .copied()
    }

    /// Returns an iterator of **all** edges in the complete graph, including the external edges.
    pub(super) fn all_edges(
        &self,
    ) -> impl Iterator<Item = (GlobalFragmentId, GlobalFragmentId, &StreamFragmentEdge)> + '_ {
        self.building_graph
            .downstreams
            .iter()
            .chain(self.extra_downstreams.iter())
            .flat_map(|(&from, tos)| tos.iter().map(move |(&to, edge)| (from, to, edge)))
    }

    /// Returns the distribution of the existing fragments.
    pub(super) fn existing_distribution(&self) -> HashMap<GlobalFragmentId, Distribution> {
        self.existing_fragments
            .iter()
            .map(|(&id, f)| {
                (
                    id,
                    Distribution::from_fragment(f, &self.existing_actor_location),
                )
            })
            .collect()
    }

    /// Generate topological order of **all** fragments in this graph, including the ones that are
    /// not in the building graph. Returns error if the graph is not a DAG and topological sort can
    /// not be done.
    ///
    /// For MV on MV, the first fragment popped out from the heap will be the top-most node, or the
    /// `Sink` / `Materialize` in stream graph.
    pub(super) fn topo_order(&self) -> MetaResult<Vec<GlobalFragmentId>> {
        let mut topo = Vec::new();
        let mut downstream_cnts = HashMap::new();

        // Iterate all fragments.
        for fragment_id in self.all_fragment_ids() {
            // Count how many downstreams we have for a given fragment.
            let downstream_cnt = self.get_downstreams(fragment_id).count();
            if downstream_cnt == 0 {
                topo.push(fragment_id);
            } else {
                downstream_cnts.insert(fragment_id, downstream_cnt);
            }
        }

        let mut i = 0;
        while let Some(&fragment_id) = topo.get(i) {
            i += 1;
            // Find if we can process more fragments.
            for (upstream_id, _) in self.get_upstreams(fragment_id) {
                let downstream_cnt = downstream_cnts.get_mut(&upstream_id).unwrap();
                *downstream_cnt -= 1;
                if *downstream_cnt == 0 {
                    downstream_cnts.remove(&upstream_id);
                    topo.push(upstream_id);
                }
            }
        }

        if !downstream_cnts.is_empty() {
            // There are fragments that are not processed yet.
            bail!("graph is not a DAG");
        }

        Ok(topo)
    }

    /// Seal a [`BuildingFragment`] from the graph into a [`Fragment`], which will be further used
    /// to build actors on the compute nodes and persist into meta store.
    pub(super) fn seal_fragment(
        &self,
        id: GlobalFragmentId,
        actors: Vec<StreamActor>,
        distribution: Distribution,
        stream_node: StreamNode,
    ) -> Fragment {
        let building_fragment = self.get_fragment(id).into_building().unwrap();
        let internal_tables = building_fragment.extract_internal_tables();
        let BuildingFragment {
            inner,
            job_id,
            upstream_table_columns: _,
        } = building_fragment;

        let distribution_type = distribution.to_distribution_type();
        let vnode_count = distribution.vnode_count();

        let materialized_fragment_id =
            if FragmentTypeMask::from(inner.fragment_type_mask).contains(FragmentTypeFlag::Mview) {
                job_id
            } else {
                None
            };

        let state_table_ids = internal_tables
            .iter()
            .map(|t| t.id)
            .chain(materialized_fragment_id)
            .collect();

        Fragment {
            fragment_id: inner.fragment_id,
            fragment_type_mask: inner.fragment_type_mask.into(),
            distribution_type,
            actors,
            state_table_ids,
            maybe_vnode_count: VnodeCount::set(vnode_count).to_protobuf(),
            nodes: stream_node,
        }
    }

    /// Get a fragment from the complete graph, which can be either a building fragment or an
    /// existing fragment.
    pub(super) fn get_fragment(&self, fragment_id: GlobalFragmentId) -> EitherFragment {
        if let Some(fragment) = self.existing_fragments.get(&fragment_id) {
            EitherFragment::Existing(fragment.clone())
        } else {
            EitherFragment::Building(
                self.building_graph
                    .fragments
                    .get(&fragment_id)
                    .unwrap()
                    .clone(),
            )
        }
    }

    /// Get **all** downstreams of a fragment, including the ones that are not in the building
    /// graph.
    pub(super) fn get_downstreams(
        &self,
        fragment_id: GlobalFragmentId,
    ) -> impl Iterator<Item = (GlobalFragmentId, &StreamFragmentEdge)> {
        self.building_graph
            .get_downstreams(fragment_id)
            .iter()
            .chain(
                self.extra_downstreams
                    .get(&fragment_id)
                    .into_iter()
                    .flatten(),
            )
            .map(|(&id, edge)| (id, edge))
    }

    /// Get **all** upstreams of a fragment, including the ones that are not in the building
    /// graph.
    pub(super) fn get_upstreams(
        &self,
        fragment_id: GlobalFragmentId,
    ) -> impl Iterator<Item = (GlobalFragmentId, &StreamFragmentEdge)> {
        self.building_graph
            .get_upstreams(fragment_id)
            .iter()
            .chain(self.extra_upstreams.get(&fragment_id).into_iter().flatten())
            .map(|(&id, edge)| (id, edge))
    }

    /// Returns all building fragments in the graph.
    pub(super) fn building_fragments(&self) -> &HashMap<GlobalFragmentId, BuildingFragment> {
        &self.building_graph.fragments
    }

    /// Returns all building fragments in the graph, mutable.
    pub(super) fn building_fragments_mut(
        &mut self,
    ) -> &mut HashMap<GlobalFragmentId, BuildingFragment> {
        &mut self.building_graph.fragments
    }

    /// Get the expected vnode count of the building graph. See documentation of the field for more details.
    pub(super) fn max_parallelism(&self) -> usize {
        self.building_graph.max_parallelism()
    }
}
