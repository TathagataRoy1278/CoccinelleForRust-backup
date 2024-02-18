use std::fmt::Debug;
use std::fmt::Display;
use std::hash::Hash;
use std::rc::Rc;

use itertools::Itertools;
use ra_parser::SyntaxKind;

use crate::commons::ograph_extended::EdgeType;
use crate::commons::ograph_extended::{self, NodeIndex};
use crate::ctl::ctl_ast::{GenericCtl, GenericSubst, GenericSubstList, Modif};
use crate::ctl::ctl_engine::{self, Graph, Pred, Subs, TripleList, WitnessTree, CTL_ENGINE};
use crate::ctl::wrapper_ctl::WrappedBinding;
use crate::engine::cocci_vs_rs::match_nodes;
use crate::parsing_cocci::ast0::{MetavarName, Snode};
use crate::parsing_cocci::parse_cocci::Rule;
use crate::parsing_rs::control_flow::{NodeWrap, Rflow};
use crate::{commons::ograph_extended::NodeData, parsing_rs::ast_rs::Rnode};

use super::cocci_vs_rs::{Looper, MetavarBinding, Modifiers};

#[derive(Clone, PartialEq, Eq)]
pub enum SubOrMod {
    Sub(Rc<Rnode>),
    Mod(Snode, Modifiers),
}

type Substitution = crate::ctl::ctl_engine::Substitution<MetavarName, SubOrMod>;

impl Debug for SubOrMod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sub(arg0) => write!(f, "{}", arg0),
            Self::Mod(arg0, arg1) => write!(f, "{:?}", arg1),
        }
    }
}

impl Subs for Substitution {
    type Value = SubOrMod;
    type Mvar = MetavarName;

    fn eq_val(a: &Self::Value, b: &Self::Value) -> bool {
        //shouldnt be required
        todo!()
    }

    fn merge_val(a: &Self::Value, b: &Self::Value) -> Self::Value {
        a.clone()
    }
}

type SubstitutionList = crate::ctl::ctl_engine::SubstitutionList<Substitution>;

#[derive(PartialOrd, Ord, Clone, Debug)]
pub struct Node(NodeIndex, EdgeType);

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl Eq for Node {}

impl Hash for Node {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<'a> Graph for Rflow<'a> {
    type Cfg = Rflow<'a>;

    //The EdgeType makes sure only those children are returned
    //which are connected with that edgetype, which is used later
    //when matching metavariables
    //Note that the use of the edgetype from predecessors_and_edges
    //gives us the type of edge that was traversed to get that node.
    //While both have the same data type (NodeIndex, EdgeType) the use
    //is different
    type Node = Node;

    fn predecessors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node> {
        let (node, tet) = (node.0, node.1);
        let preds = cfg.predecessors_and_edges(node);

        preds
            .into_iter()
            .filter_map(
                |(x, et)| {
                    if et.is_default() && (tet.is_default() || tet == EdgeType::NextSibling) {
                        Some(Node(x, EdgeType::Default))
                    }
                    else {
                        assert_eq!(EdgeType::Sibling, et);
                        // Because succs and preds always return
                        // either default or sibling
                        
                        match tet {
                            EdgeType::Default => None, 
                            EdgeType::NextSibling => None, 
                            EdgeType::PrevSibling => Some(Node(x, EdgeType::NextSibling)),
                            EdgeType::Sibling => Some(Node(x, EdgeType::Sibling))
                        }

                    }
                }, //    if et == tet { Some(Node(x, EdgeType::Default)) } else { None }
            )
            .collect_vec()
    }

    fn successors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node> {
        let (node, tet) = (node.0, node.1);

        let succs = cfg.successors_and_edges(node);
        succs
            .into_iter()
            .filter_map(|(x, et)| {
                if et.is_default() && (tet.is_default() || tet == EdgeType::PrevSibling) {
                    Some(Node(x, EdgeType::Default))
                }
                else {
                    assert_eq!(EdgeType::Sibling, et);
                    // Because succs and preds always return
                    // either default or sibling
                    
                    match tet {
                        EdgeType::Default => None,
                        EdgeType::NextSibling => Some(Node(x, EdgeType::PrevSibling)), 
                        EdgeType::PrevSibling => None,
                        EdgeType::Sibling => Some(Node(x, EdgeType::Sibling))
                    }

                } 
            } )
            .collect_vec()
    }

    fn nodes(cfg: &Self::Cfg) -> Vec<Self::Node> {
        cfg.nodes().into_iter().map(|x| Node(x, EdgeType::Default)).collect_vec()
    }

    fn direct_predecessors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node> {
        <Rflow as Graph>::predecessors(cfg, node)
    }

    fn direct_successors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node> {
        <Rflow as Graph>::successors(cfg, node)
    }

    fn extract_is_loop(cfg: &Self::Cfg, node: &Self::Node) -> bool {
        return false;
        //TODO
    }

    fn size(cfg: &Self::Cfg) -> usize {
        cfg.nodes.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Predicate {
    Match(Snode, Modif, bool),
    //bool for if is after a metavariable
    //in which case successor is the next
    //sibling
    Kind(SyntaxKind, bool),
}

impl Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::Match(node, modif, pm) => {
                if *pm {
                    write!(f, "{}(M) {}", node.getstring(), modif)
                } else {
                    write!(f, "{} {}", node.getstring(), modif)
                }
            }
            Predicate::Kind(kind, pm) => {
                if *pm {
                    write!(f, "{:?}(M) ", kind)
                } else {
                    write!(f, "{:?} ", kind)
                }
            }
        }
    }
}

pub enum MVar<'a> {
    NormalMatch(&'a Rnode),
}

impl Pred for Predicate {
    type ty = Predicate;
}

//Functions
fn create_subs(s: MetavarBinding) -> Substitution {
    return GenericSubst::Subst(s.metavarinfo, SubOrMod::Sub(s.rnode));
}
fn tokenf(a: &Snode, b: &Rnode) -> Vec<MetavarBinding> {
    vec![]
}

pub type CWitnessTree<'a> = WitnessTree<Rflow<'a>, Substitution, Predicate>;

fn labels_for_ctl<'a>() -> fn(
    flow: &<Rflow<'a> as Graph>::Cfg,
    &<Predicate as Pred>::ty,
) -> Vec<(
    <Rflow<'a> as Graph>::Node,
    SubstitutionList,
    Vec<WitnessTree<Rflow<'a>, Substitution, Predicate>>,
)> {
    fn oldlabelfn<'a>(
        flow: &'a Rflow<'a>,
        p: &<Predicate as Pred>::ty,
    ) -> TripleList<Rflow<'a>, Substitution, Predicate> {
        match &p {
            Predicate::Match(snode, modif, pim) => {
                flow.nodes().iter().fold(vec![], |mut prev, node| {
                    if flow.node(*node).data().is_dummy() {
                        prev
                    } else {
                        let rnode = flow.node(*node).data().rnode();
                        eprintln!("Flight risk = {} {:?} {}", snode.getstring(), snode.kind(), snode.wrapper.metavar.ismeta());
                        let env = match_nodes(snode, rnode, &vec![]);
                        if !env.failed {
                            eprintln!("matches {}", rnode.getstring());
                            // if snode
                            let mut t = vec![];
                            if modif.ismodif() {
                                t.push(Substitution::Subst(
                                    MetavarName::create_v(),
                                    SubOrMod::Mod(snode.clone(), env.modifiers),
                                ));
                            }
                            t.extend(
                                env.bindings.into_iter().map(|s| create_subs(s)).collect_vec(),
                            );

                            // let tet = if *pim { EdgeType::Sibling } else { EdgeType::Sibling };

                            let et = match (!t.is_empty(), pim) {
                                // !t.isempty() is true if it is a metavar
                                (true, false) => EdgeType::NextSibling,
                                (false, false) => EdgeType::Default,
                                (true, true) => EdgeType::Sibling,
                                (false, true) => EdgeType::PrevSibling,
                            };

                            let sub = (Node(node.clone(), et), t, vec![]);

                            prev.push(sub);
                        }
                        prev
                    }
                })
            }
            Predicate::Kind(kind, pim) => {
                // eprintln!("krodher agun {:?}", kind);
                flow.nodes().iter().fold(vec![], |mut prev, node| {
                    if flow.node(*node).data().is_dummy() {
                        prev
                    } else {
                        if flow.node(*node).data().rnode().kind().eq(kind) {
                            let tet = if *pim { EdgeType::PrevSibling } else { EdgeType::Default };
                            prev.push((Node(node.clone(), tet), vec![], vec![]))
                        }
                        prev
                    }
                })
            }
        }
    }

    // let nf = |p: <Predicate as Pred>::ty| {
    //     let (p, predvar) = p;
    //     let penv = |pp: <Predicate as Pred>::ty| match predvar {
    //         Modif::Modif(x) => {
    //             vec![GenericSubst::Subst(x, WB::<Rc<Rnode>>::PredVal(Modif::Modif(pp)))]
    //         }
    //         Modif::Unmodif(x) => {
    //             vec![GenericSubst::Subst(x, WB::<Rc<Rnode>>::PredVal(Modif::Unmodif(pp)))]
    //         }
    //         Modif::Control => vec![],
    //     };
    //     fn conv_sub<Mvar: Clone + Eq, Val: Clone>(
    //         sub: GenericSubst<Mvar, Val>,
    //     ) -> GenericSubst<Mvar, WB<Val>> {
    //         match sub {
    //             GenericSubst::Subst(x, v) => GenericSubst::Subst(x, WB::ClassicVal(v)),
    //             GenericSubst::NegSubst(x, v) => GenericSubst::NegSubst(x, WB::<Val>::ClassicVal(v)),
    //         }
    //     }
    //     fn conv_trip<Mvar: Clone + Eq>(
    //         s: (Predicate, Modif<MetavarName>),
    //         env: GenericSubstList<Mvar, (Predicate, Modif<MetavarName>)>,
    //         penv: impl FnOnce(
    //             (Predicate, Modif<MetavarName>),
    //         ) -> Vec<
    //             GenericSubst<
    //                 MetavarName,
    //                 WrappedBinding<(Predicate, Modif<MetavarName>), Rc<Rnode>>,
    //             >,
    //         >,
    //     ) -> (
    //         (Predicate, Modif<MetavarName>),
    //         Vec<
    //             GenericSubst<
    //                 Mvar,
    //                 WrappedBinding<
    //                     (Predicate, Modif<MetavarName>),
    //                     (Predicate, Modif<MetavarName>),
    //                 >,
    //             >,
    //         >,
    //         Vec<(Predicate, Modif<MetavarName>)>,
    //     ) {
    //         todo!()
    //         // (s, env.into_iter().map(|x| conv_sub(x)).collect_vec(), vec![])
    //     }
    //     // oldlabelfn(p).into_iter().map(|(a, env)| conv_trip(a, env, penv))
    // };

    return oldlabelfn;

    // todo!()
}

// fn wrap_label(f: impl Fn(<Predicate as Pred>::ty) -> Vec<(usize, SubstitutionList)>) -> impl Fn(2) {
//
// }

type WB<Val> = WrappedBinding<Val>;

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
    fn(
        &<Rflow<'a> as Graph>::Cfg,
        &<Predicate as Pred>::ty,
    ) -> TripleList<Rflow<'a>, Substitution, Predicate>,
// impl Fn(<Predicate as Pred>::ty) -> Vec<(<Rflow<'a> as Graph>::Node, SubstitutionList, Vec<WitnessTree<Rflow<'a>, Substitution, Predicate>>)> + 'a,
    fn(&<Predicate as Pred>::ty) -> bool,
    Vec<<ograph_extended::Graph<crate::parsing_rs::control_flow::Node<'a>> as ctl_engine::Graph>::Node>,
){
    let nodes = flow.nodes().into_iter().map(|x| Node(x, EdgeType::Default)).collect_vec();
    fn f(_: &<Predicate as Pred>::ty) -> bool {
        true
    }
    (flow, labels_for_ctl(), f, nodes)
}

pub fn processctl<'a>(
    ctl: &GenericCtl<
        <Predicate as Pred>::ty,
        <GenericSubst<MetavarName, SubOrMod> as Subs>::Mvar,
        Vec<String>,
    >,
    flow: &'a Rflow<'a>,
    bindings: &'a Vec<MetavarBinding>,
) -> TripleList<Rflow<'a>, Substitution, Predicate> {
    let mut engine = CTL_ENGINE::<Rflow<'a>, Substitution, Predicate>::new(flow);
    let model = &model_for_ctl(flow, bindings);
    let tmp = engine.sat(model, ctl, vec![]);
    return tmp;
}
