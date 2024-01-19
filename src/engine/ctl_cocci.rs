use std::rc::Rc;

use itertools::Itertools;

use crate::commons::ograph_extended::{self, NodeIndex};
use crate::ctl::ctl_ast::{GenericSubst, GenericSubstList, Modif};
use crate::ctl::ctl_engine::{self, Graph, Pred, Subs, TripleList, WitnessTree, CTL_ENGINE};
use crate::ctl::wrapper_ctl::WrappedBinding;
use crate::engine::cocci_vs_rs::match_nodes;
use crate::parsing_cocci::ast0::{MetavarName, Snode};
use crate::parsing_cocci::parse_cocci::Rule;
use crate::parsing_rs::control_flow::{NodeWrap, Rflow};
use crate::{commons::ograph_extended::NodeData, parsing_rs::ast_rs::Rnode};

use super::cocci_vs_rs::{Looper, MetavarBinding};

type Substitution = crate::ctl::ctl_engine::Substitution<MetavarName, Rc<Rnode>>;

impl Subs for Substitution {
    type Value = Rc<Rnode>;
    type Mvar = MetavarName;

    fn eq_val(a: &Self::Value, b: &Self::Value) -> bool {
        a.equals(b)
    }

    fn merge_val(a: &Self::Value, b: &Self::Value) -> Self::Value {
        a.clone()
    }
}

type SubstitutionList = crate::ctl::ctl_engine::SubstitutionList<Substitution>;

impl<'a> Graph for Rflow<'a> {
    type Cfg = Rflow<'a>;

    //IMP ASK WHY NODE NEEDS TO HAVE ORD
    //DO WE NEED THE ORD with respect to only the
    //data or the other things too?
    type Node = NodeIndex;

    fn predecessors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node> {
        cfg.predecessors(*node)
    }

    fn successors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node> {
        cfg.successors(*node)
    }

    fn nodes(cfg: &Self::Cfg) -> Vec<Self::Node> {
        cfg.nodes()
    }

    fn direct_predecessors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node> {
        unimplemented!()
    }

    fn direct_successors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node> {
        unimplemented!()
    }

    fn extract_is_loop(cfg: &Self::Cfg, node: &Self::Node) -> bool {
        todo!()
    }

    fn size(cfg: &Self::Cfg) -> usize {
        cfg.nodes.len()
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Predicate {
    Match(Snode),
}
pub enum MVar<'a> {
    NormalMatch(&'a Rnode),
}
impl Pred for Predicate {
    type ty = (Predicate, Modif<Snode>);
}

fn create_subs(s: MetavarBinding) -> Substitution {
    return GenericSubst::Subst(s.metavarinfo, s.rnode);
}
fn tokenf(a: &Snode, b: &Rnode) -> Vec<MetavarBinding> {
    vec![]
}

fn labels_for_ctl<'a>(
    flow: &'a Rflow<'a>,
    nodes: Vec<NodeIndex>,
    bindings: &'a Vec<MetavarBinding>,
) -> fn(
    flow: &<Rflow<'a> as Graph>::Cfg,
    &<Predicate as Pred>::ty,
) -> Vec<(
    <Rflow<'a> as Graph>::Node,
    SubstitutionList,
    Vec<WitnessTree<Rflow<'a>, Substitution, Predicate>>,
)> {
    fn oldlabelfn<'a>(flow: &'a Rflow<'a>, p: &<Predicate as Pred>::ty) -> TripleList<Rflow<'a>, Substitution, Predicate> {
        match &p.0 {
            Predicate::Match(snode) => flow.nodes().iter().fold(vec![], |mut prev, node| {
                let env = match_nodes(&snode, flow.node(*node).data().rnode(), &vec![]);
                let subs = env
                    .into_iter()
                    .map(|x| {
                        let t = x.bindings.into_iter().map(|s| create_subs(s)).collect_vec();
                        (NodeIndex(node.to_usize()), t, vec![])
                    })
                    .collect_vec();
                prev.extend(subs);
                prev
            }),
        }
    }

    let nf = |p: <Predicate as Pred>::ty| {
        let (p, predvar) = p;
        let penv = |pp: <Predicate as Pred>::ty| match predvar {
            Modif::Modif(x) => {
                vec![GenericSubst::Subst(x, WB::<Rc<Rnode>>::PredVal(Modif::Modif(pp)))]
            }
            Modif::Unmodif(x) => {
                vec![GenericSubst::Subst(x, WB::<Rc<Rnode>>::PredVal(Modif::Unmodif(pp)))]
            }
            Modif::Control => vec![],
        };
        fn conv_sub<Mvar: Clone + Eq, Val: Clone>(
            sub: GenericSubst<Mvar, Val>,
        ) -> GenericSubst<Mvar, WB<Val>> {
            match sub {
                GenericSubst::Subst(x, v) => GenericSubst::Subst(x, WB::ClassicVal(v)),
                GenericSubst::NegSubst(x, v) => GenericSubst::NegSubst(x, WB::<Val>::ClassicVal(v)),
            }
        }
        fn conv_trip<Mvar: Clone + Eq>(
            s: (Predicate, Modif<MetavarName>),
            env: GenericSubstList<Mvar, (Predicate, Modif<MetavarName>)>,
            penv: impl FnOnce(
                (Predicate, Modif<MetavarName>),
            ) -> Vec<
                GenericSubst<
                    MetavarName,
                    WrappedBinding<(Predicate, Modif<MetavarName>), Rc<Rnode>>,
                >,
            >,
        ) -> (
            (Predicate, Modif<MetavarName>),
            Vec<
                GenericSubst<
                    Mvar,
                    WrappedBinding<
                        (Predicate, Modif<MetavarName>),
                        (Predicate, Modif<MetavarName>),
                    >,
                >,
            >,
            Vec<(Predicate, Modif<MetavarName>)>,
        ) {
            todo!()
            // (s, env.into_iter().map(|x| conv_sub(x)).collect_vec(), vec![])
        }
        // oldlabelfn(p).into_iter().map(|(a, env)| conv_trip(a, env, penv))
    };

    return oldlabelfn;

    // todo!()
}

// fn wrap_label(f: impl Fn(<Predicate as Pred>::ty) -> Vec<(usize, SubstitutionList)>) -> impl Fn(2) {
//
// }

type WB<Val> = WrappedBinding<<Predicate as Pred>::ty, Val>;

// fn wrap_label(oldlabelfn: impl Fn(<Predicate as Pred>::ty) -> Vec<(usize, SubstitutionList)>) {
//     fn newlabelfn(p: <Predicate as Pred>::ty) {
//         let (p, predvar) = p;
//         let penv = |pp: <Predicate as Pred>::ty| match predvar {
//             Modif::Modif(x) => {
//                 vec![GenericSubst::Subst(x, WB::<Rc<Rnode>>::PredVal(Modif::Modif(pp)))]
//             }
//             Modif::Unmodif(x) => {
//                 vec![GenericSubst::Subst(x, WB::<Rc<Rnode>>::PredVal(Modif::Unmodif(pp)))]
//             }
//             Modif::Control => vec![],
//         };
//         fn conv_sub<Mvar: Clone + Eq, Val: Clone>(
//             sub: GenericSubst<Mvar, Val>,
//         ) -> GenericSubst<Mvar, WB<Val>> {
//             match sub {
//                 GenericSubst::Subst(x, v) => GenericSubst::Subst(x, WB::ClassicVal(v)),
//                 GenericSubst::NegSubst(x, v) => GenericSubst::NegSubst(x, WB::<Val>::ClassicVal(v)),
//             }
//         }
//         fn conv_trip<Mvar: Clone + Eq>(
//             s: (Predicate, Modif<MetavarName>),
//             pp: (Predicate, Modif<MetavarName>),
//             env: GenericSubstList<Mvar, (Predicate, Modif<MetavarName>)>,
//             penv: impl FnOnce(
//                 (Predicate, Modif<MetavarName>),
//             ) -> Vec<
//                 GenericSubst<
//                     MetavarName,
//                     WrappedBinding<(Predicate, Modif<MetavarName>), Rc<Rnode>>,
//                 >,
//             >,
//         ) -> (
//             (Predicate, Modif<MetavarName>),
//             Vec<
//                 GenericSubst<
//                     MetavarName,
//                     WrappedBinding<(Predicate, Modif<MetavarName>), Rc<Rnode>>,
//                 >,
//             >,
//             Vec<
//                 GenericSubst<
//                     Mvar,
//                     WrappedBinding<
//                         (Predicate, Modif<MetavarName>),
//                         (Predicate, Modif<MetavarName>),
//                     >,
//                 >,
//             >,
//             Vec<(Predicate, Modif<MetavarName>)>,
//         ) {
//             (s, penv(pp), env.into_iter().map(|x| conv_sub(x)).collect_vec(), vec![])
//         }
//     }

//     todo!();
// }

pub fn model_for_ctl<'a>(
    flow: &'a Rflow<'a>,
    bindings: &'a Vec<MetavarBinding>,
) -> (
    &'a <Rflow<'a> as Graph>::Cfg,
    fn(&<Rflow<'a> as Graph>::Cfg, &<Predicate as Pred>::ty) -> TripleList<Rflow<'a>, Substitution, Predicate>,
    // impl Fn(<Predicate as Pred>::ty) -> Vec<(<Rflow<'a> as Graph>::Node, SubstitutionList, Vec<WitnessTree<Rflow<'a>, Substitution, Predicate>>)> + 'a,
    fn(&<Predicate as Pred>::ty) -> bool,
    Vec<<ograph_extended::Graph<NodeWrap<'a>> as ctl_engine::Graph>::Node>,
) {
    let nodes = flow.nodes();
    fn f(_: &<Predicate as Pred>::ty) -> bool {
        true
    }
    (flow, labels_for_ctl(flow, nodes.clone(), bindings), f, nodes)
}

pub fn processctl<'a>(rule: &Rule, flow: &'a Rflow<'a>, bindings: &'a Vec<MetavarBinding>) {
    let mut engine = CTL_ENGINE::<Rflow<'a>, Substitution, Predicate>::new(flow);
    let model = &model_for_ctl(flow, bindings);
    engine.sat(model, &rule.ctl, vec![]);
    todo!()
}
