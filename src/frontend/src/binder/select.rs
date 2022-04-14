// Copyright 2022 Singularity Data
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::fmt::Debug;
use std::iter;

use itertools::Itertools;
use regex::Regex;
use risingwave_common::error::{ErrorCode, Result};
use risingwave_common::types::DataType;
use risingwave_sqlparser::ast::{Expr, Ident, Select, SelectItem};

use super::bind_context::{Clause, ColumnBinding};
use super::UNNAMED_COLUMN;
use crate::binder::{Binder, Relation};
use crate::catalog::check_valid_column_name;
use crate::expr::{Expr as _, ExprImpl, InputRef};

#[derive(Debug)]
pub struct BoundSelect {
    pub distinct: bool,
    pub select_items: Vec<ExprImpl>,
    pub aliases: Vec<Option<String>>,
    pub from: Option<Relation>,
    pub where_clause: Option<ExprImpl>,
    pub group_by: Vec<ExprImpl>,
}

impl BoundSelect {
    /// The names returned by this [`BoundSelect`].
    pub fn names(&self) -> Vec<String> {
        self.aliases
            .iter()
            .cloned()
            .map(|alias| alias.unwrap_or_else(|| UNNAMED_COLUMN.to_string()))
            .collect()
    }

    /// The types returned by this [`BoundSelect`].
    pub fn data_types(&self) -> Vec<DataType> {
        self.select_items
            .iter()
            .map(|item| item.return_type())
            .collect()
    }

    pub fn is_correlated(&self) -> bool {
        self.select_items
            .iter()
            .chain(self.group_by.iter())
            .chain(self.where_clause.iter())
            .any(|expr| expr.has_correlated_input_ref())
    }
}

impl Binder {
    pub(super) fn bind_select(&mut self, select: Select) -> Result<BoundSelect> {
        // Bind FROM clause.
        let from = self.bind_vec_table_with_joins(select.from)?;

        // Bind WHERE clause.
        self.context.clause = Some(Clause::Where);
        let selection = select
            .selection
            .map(|expr| self.bind_expr(expr))
            .transpose()?;
        self.context.clause = None;

        if let Some(selection) = &selection {
            let return_type = selection.return_type();
            if return_type != DataType::Boolean {
                return Err(ErrorCode::InternalError(format!(
                    "argument of WHERE must be boolean, not type {:?}",
                    return_type
                ))
                .into());
            }
        }

        // Bind GROUP BY clause.
        let group_by = select
            .group_by
            .into_iter()
            .map(|expr| self.bind_expr(expr))
            .try_collect()?;

        // Bind SELECT clause.
        let (select_items, aliases) = self.bind_project(select.projection)?;

        Ok(BoundSelect {
            distinct: select.distinct,
            select_items,
            aliases,
            from,
            where_clause: selection,
            group_by,
        })
    }

    pub fn bind_project(
        &mut self,
        select_items: Vec<SelectItem>,
    ) -> Result<(Vec<ExprImpl>, Vec<Option<String>>)> {
        let mut select_list = vec![];
        let mut aliases = vec![];
        for item in select_items {
            match item {
                SelectItem::UnnamedExpr(expr) => {
                    let (select_expr, alias) = match &expr.clone() {
                        Expr::Identifier(ident) => {
                            (self.bind_expr(expr)?, Some(ident.value.clone()))
                        }
                        Expr::CompoundIdentifier(idents) => (
                            self.bind_expr(expr)?,
                            idents.last().map(|ident| ident.value.clone()),
                        ),
                        Expr::FieldIdentifier(field_expr, idents) => {
                            self.bind_single_field_column(*field_expr.clone(), idents)?
                        }
                        _ => (self.bind_expr(expr)?, None),
                    };
                    select_list.push(select_expr);
                    aliases.push(alias);
                }
                SelectItem::ExprWithAlias { expr, alias } => {
                    check_valid_column_name(&alias.value)?;

                    let expr = self.bind_expr(expr)?;
                    select_list.push(expr);
                    aliases.push(Some(alias.value));
                }
                SelectItem::QualifiedWildcard(obj_name) => {
                    let table_name = &obj_name.0.last().unwrap().value;
                    let (begin, end) = self.context.range_of.get(table_name).ok_or_else(|| {
                        ErrorCode::ItemNotFound(format!("relation \"{}\"", table_name))
                    })?;
                    let (exprs, names) = Self::bind_columns_iter(
                        self.context.columns[*begin..*end]
                            .iter()
                            .filter(|c| !c.column_name.contains('.')),
                    );
                    select_list.extend(exprs);
                    aliases.extend(names);
                }
                SelectItem::ExprQualifiedWildcard(expr, idents) => {
                    let (exprs, names) = self.bind_wildcard_field_column(expr, &idents.0)?;
                    select_list.extend(exprs);
                    aliases.extend(names);
                }
                SelectItem::Wildcard => {
                    let (exprs, names) = Self::bind_columns_iter(
                        self.context.columns[..]
                            .iter()
                            .filter(|c| !c.column_name.contains('.'))
                            .filter(|c| !c.is_hidden),
                    );
                    select_list.extend(exprs);
                    aliases.extend(names);
                }
            }
        }
        Ok((select_list, aliases))
    }

    /// Bind wildcard field column, e.g. `(table.v1).*`.
    pub fn bind_wildcard_field_column(
        &mut self,
        expr: Expr,
        ids: &[Ident],
    ) -> Result<(Vec<ExprImpl>, Vec<Option<String>>)> {
        let idents = self.extract_table_and_field_name(expr, ids)?;
        let (begin, end, column_name, bind) = match &idents[..] {
            [table, column] => {
                let bind = self
                    .context
                    .get_column_with_table_name(&column.value, &table.value)?;
                let (begin, end) = self.context.range_of.get(&table.value).ok_or_else(|| {
                    ErrorCode::ItemNotFound(format!("relation \"{}\"", table.value))
                })?;
                (*begin, *end, column.value.clone(), bind)
            }
            [column] => {
                let bind = self.context.get_column(&column.value)?;
                // If not given table name, use whole index in columns.
                (0, self.context.columns.len(), column.value.clone(), bind)
            }
            _ => {
                return Err(ErrorCode::InternalError(format!(
                    "The number of idents is not match: {:?}",
                    idents
                ))
                .into());
            }
        };

        // Only struct type column can use wildcard selection.
        if !matches!(bind.data_type, DataType::Struct { .. }) {
            return Err(ErrorCode::BindError(format!(
                "type {:?} is not composite",
                bind.data_type
            ))
            .into());
        }

        // Regular expression is `^name+\.{1}` which match column_name.
        // For example, if name is `table.v1`, then `table.v1.v2` can be matched,
        // but `table.v1` and `table.v1.v2.v3` cannot be matched.
        let column_re = Regex::new(&("^(".to_owned() + &column_name + ")+\\.{1}")).unwrap();
        Ok(Self::bind_columns_iter(
            self.context.columns[begin..end]
                .iter()
                .filter(|c| column_re.is_match(&c.column_name)),
        ))
    }

    /// Bind single field column, e.g. `(table.v1).v2`.
    pub fn bind_single_field_column(
        &mut self,
        expr: Expr,
        ids: &[Ident],
    ) -> Result<(ExprImpl, Option<String>)> {
        let idents = self.extract_table_and_field_name(expr, ids)?;
        Ok((
            self.bind_column(&idents[..])?,
            idents.last().map(|ident| ident.value.clone()),
        ))
    }

    /// This function will accept three expr type: `CompoundIdentifier`,`Identifier`,`Cast(Todo)`
    /// We will extract ident from expr and concat it with `ids` to get `field_column_name`.
    /// Will return `table_name` and `field_column_name` or `field_column_name`.
    pub fn extract_table_and_field_name(
        &mut self,
        expr: Expr,
        ids: &[Ident],
    ) -> Result<Vec<Ident>> {
        match expr {
            // For CompoundIdentifier, we will use first ident as `table_name` and second ident as
            // first part of `field_column_name` and then concat with ids.
            Expr::CompoundIdentifier(idents) => {
                let (table_name, column): (&String, &String) = match &idents[..] {
                    [table, column] => (&table.value, &column.value),
                    _ => {
                        return Err(ErrorCode::InternalError(format!(
                            "Too many idents: {:?}",
                            idents
                        ))
                        .into());
                    }
                };
                let fields = iter::once(column.clone())
                    .chain(ids.iter().map(|id| id.value.clone()))
                    .collect_vec();
                Ok(vec![
                    Ident::new(table_name),
                    Ident::new(Self::concat_ident_names(fields)),
                ])
            }
            // For Identifier, we will first use the ident as first part of `field_column_name`
            // and judge if this name is exist.
            // If not we will use the ident as table name.
            // The reason is that in pgsql, for table name v3 have a column name v3 which
            // have a field name v3. Select (v3).v3 from v3 will return the field value instead
            // of column value.
            Expr::Identifier(ident) => {
                let fields: Vec<String> = iter::once(ident.value.clone())
                    .chain(ids.iter().map(|id| id.value.clone()))
                    .collect_vec();
                let field_name = Self::concat_ident_names(fields.clone());
                if self.context.indexs_of.get(&field_name).is_some() {
                    Ok(vec![Ident::new(field_name)])
                } else {
                    Ok(vec![
                        ident,
                        Ident::new(Self::concat_ident_names(fields[1..].to_vec())),
                    ])
                }
            }
            Expr::Cast { .. } => {
                todo!()
            }
            _ => unreachable!(),
        }
    }

    /// Use . to concat ident name.
    pub fn concat_ident_names(idents: Vec<String>) -> String {
        if idents.is_empty() {
            return "".to_string();
        }
        let mut column_name = idents[0].clone();
        for name in &idents[1..] {
            column_name = column_name + "." + name;
        }
        column_name
    }

    pub fn bind_columns_iter<'a>(
        column_binding: impl Iterator<Item = &'a ColumnBinding>,
    ) -> (Vec<ExprImpl>, Vec<Option<String>>) {
        column_binding
            .map(|c| {
                (
                    InputRef::new(c.index, c.data_type.clone()).into(),
                    Some(c.column_name.clone()),
                )
            })
            .unzip()
    }
}
