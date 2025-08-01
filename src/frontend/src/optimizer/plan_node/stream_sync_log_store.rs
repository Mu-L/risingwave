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

use pretty_xmlish::{Pretty, XmlNode};
use risingwave_pb::stream_plan::SyncLogStoreNode;
use risingwave_pb::stream_plan::stream_node::NodeBody;

use crate::optimizer::plan_node::expr_visitable::ExprVisitable;
use crate::optimizer::plan_node::generic::PhysicalPlanRef;
use crate::optimizer::plan_node::stream::StreamPlanNodeMetadata;
use crate::optimizer::plan_node::utils::{
    Distill, childless_record, infer_synced_kv_log_store_table_catalog_inner,
};
use crate::optimizer::plan_node::{
    ExprRewritable, PlanBase, PlanTreeNodeUnary, Stream, StreamNode, StreamPlanRef as PlanRef,
};
use crate::stream_fragmenter::BuildFragmentGraphState;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StreamSyncLogStore {
    pub base: PlanBase<Stream>,
    pub input: PlanRef,
    pub buffer_size: usize,
    pub pause_duration_ms: usize,
}

impl StreamSyncLogStore {
    pub fn new(input: PlanRef) -> Self {
        let base = PlanBase::new_stream(
            input.ctx().clone(),
            input.schema().clone(),
            input.stream_key().map(|keys| keys.to_vec()),
            input.functional_dependency().clone(),
            input.distribution().clone(),
            input.append_only(),
            input.emit_on_window_close(),
            input.watermark_columns().clone(),
            input.columns_monotonicity().clone(),
        );
        let pause_duration_ms = input
            .ctx()
            .session_ctx()
            .config()
            .streaming_sync_log_store_pause_duration_ms();
        let buffer_size = input
            .ctx()
            .session_ctx()
            .config()
            .streaming_sync_log_store_buffer_size();
        Self {
            base,
            input,
            buffer_size,
            pause_duration_ms,
        }
    }
}

impl Distill for StreamSyncLogStore {
    fn distill<'a>(&self) -> XmlNode<'a> {
        let fields = vec![
            ("buffer_size", Pretty::display(&self.buffer_size)),
            (
                "pause_duration_ms",
                Pretty::display(&self.pause_duration_ms),
            ),
        ];
        childless_record("StreamSyncLogStore", fields)
    }
}

impl PlanTreeNodeUnary<Stream> for StreamSyncLogStore {
    fn input(&self) -> PlanRef {
        self.input.clone()
    }

    fn clone_with_input(&self, input: PlanRef) -> Self {
        Self::new(input)
    }
}

impl_plan_tree_node_for_unary! { Stream, StreamSyncLogStore }

impl StreamNode for StreamSyncLogStore {
    fn to_stream_prost_body(&self, state: &mut BuildFragmentGraphState) -> NodeBody {
        let columns = self.input.schema().fields();
        let log_store_table = infer_synced_kv_log_store_table_catalog_inner(&self.input, columns)
            .with_id(state.gen_table_id_wrapped())
            .to_internal_table_prost()
            .into();
        NodeBody::SyncLogStore(Box::new(SyncLogStoreNode {
            log_store_table,
            pause_duration_ms: self.pause_duration_ms as _,
            buffer_size: self.buffer_size as _,
            aligned: false,
        }))
    }
}

impl ExprRewritable<Stream> for StreamSyncLogStore {}

impl ExprVisitable for StreamSyncLogStore {}
