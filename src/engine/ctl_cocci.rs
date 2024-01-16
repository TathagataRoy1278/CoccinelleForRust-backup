use std::rc::Rc;

use itertools::Itertools;

use crate::ctl::ctl_ast::GenericSubst;
use crate::ctl::ctl_engine::{Graph, Pred};
use crate::engine::cocci_vs_rs::match_nodes;
use crate::parsing_cocci::ast0::{MetavarName, Snode};
use crate::parsing_cocci::control_flow::NodeWrap;
use crate::{commons::ograph_extended::NodeData, parsing_rs::ast_rs::Rnode};

use super::cocci_vs_rs::{Looper, MetavarBinding};

type Substitution = crate::ctl::ctl_engine::Substitution<MetavarName, Rc<Rnode>>;
type SubstitutionList = Vec<Substitution>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Predicate<'a> {
    Match(&'a Snode),
}
pub enum MVar<'a> {
    NormalMatch(&'a Rnode),
}
impl<'a> Pred for Predicate<'a> {
    type ty = Predicate<'a>;
}

fn create_subs(s: MetavarBinding) -> Substitution {
    return GenericSubst::Subst(s.metavarinfo, s.rnode);
}
fn tokenf(a: &Snode, b: &Rnode) -> Vec<MetavarBinding> {
    vec![]
}

fn labels_for_ctl<'a>(
    nodes: &'a Vec<NodeData<NodeWrap>>,
    bindings: &'a Vec<MetavarBinding>,
) -> impl Fn(<Predicate as Pred>::ty) -> Vec<(usize, SubstitutionList)> + 'a {
    let f = |p: <Predicate as Pred>::ty| match p {
        Predicate::Match(snode) => nodes.iter().fold(vec![], |mut prev, node| {
            let env = match_nodes(snode, node.data().rnode(), bindings);
            let subs = env
                .into_iter()
                .map(|x| {
                    let t = x.bindings.into_iter().map(|s| create_subs(s)).collect_vec();
                    (node.id, t)
                })
                .collect_vec();
            prev.extend(subs);
            prev
        }),
    };
    f
}

// pub fn model_for_ctl(flow: Rflow, bindings: &Vec<MetavarBinding>) -> (Rflow, fn (&Vec<NodeData<NodeWrap>>, )->)
