use std::rc::Rc;

use ctl_ast::Direction;
use itertools::Itertools;

use super::ctl_ast::{GenericSubst, GenericWitnessTree};
use crate::{
    commons::info::Unknown, ctl::ctl_ast, parsing_cocci::ast0::MetavarName,
    parsing_rs::ast_rs::Rnode,
};

type Substitution = ctl_ast::GenericSubstList<MetavarName, Rc<Rnode>>;
type Witness<State, Anno, Value> = ctl_ast::GenericWitnessTree<State, Anno, Value>;

static timeout: usize = 800;
static pNew_INFO_OPT: bool = true;
struct CFG {}

#[derive(PartialEq, Eq)]
struct Node {}

type Triple<Mvar, Value: Clone> =
    (Node, Substitution, GenericWitnessTree<Unknown, Unknown, Unknown>);

pub trait GenericSubstitution {
    type Mvar;
    type Value;

    fn eq_mvar(a: Self::Mvar, b: Self::Mvar) -> bool;
    fn eq_val(a: Self::Value, b: Self::Value) -> bool;
    fn merge_val(a: Self::Value, b: Self::Value) -> bool;
    fn print_mvar(&self, b: Self) -> bool;
    fn print_value(&self, b: Self) -> bool;
}

// impl GenericSubstitution for Substitution {
//     type Mvar = MetavarName;
//     type Value = Rc<Rnode>;

//     fn eq_mvar(a: Self::Mvar, b: Self::Mvar) -> bool {
//         a==b
//     }

//     fn eq_val(a: Rc<Rnode>, b: Rc<Rnode>) -> bool {
//         a.equals(&b)
//     }

//     fn merge_val(a: Self::Value, b: Self::Value) -> bool {
//         false
//     }
//     fn print_mvar(&self, b: Self) -> bool {
//         false
//     }
//     fn print_value(&self, b: Self) -> bool {
//         false
//     }
// }

pub trait Graph {
    type CFG;
    type Node;

    fn predecessors(&self, node: &Self::Node) -> Vec<Self::Node>;
    fn successors(&self, node: &Self::Node) -> Vec<Self::Node>;

    fn direct_predecessors(&self, node: &Self::Node) -> Vec<Self::Node>;
    fn direct_successors(&self, node: &Self::Node) -> Vec<Self::Node>;

    fn extract_is_loop(&self, node: &Self::Node) -> bool;

    fn print_node(node: &Self::Node);
    fn size(&self) -> usize;
}

pub struct EgGrpah {
    cfg: CFG,
}

impl Graph for EgGrpah {
    type CFG = CFG;
    type Node = Node;

    fn predecessors(&self, node: &Self::Node) -> Vec<Self::Node> {
        todo!()
    }

    fn successors(&self, node: &Self::Node) -> Vec<Self::Node> {
        todo!()
    }

    fn direct_predecessors(&self, node: &Self::Node) -> Vec<Self::Node> {
        todo!()
    }

    fn direct_successors(&self, node: &Self::Node) -> Vec<Self::Node> {
        todo!()
    }

    fn extract_is_loop(&self, node: &Self::Node) -> bool {
        todo!()
    }

    fn print_node(node: &Self::Node) {
        todo!()
    }

    fn size(&self) -> usize {
        todo!()
    }
}

fn dom_sub<Mvar, Val>(sub: Substitution) -> MetavarName {
    match sub {
        GenericSubst::Subst(x, _) => x,
        GenericSubst::NegSubst(x, _) => x,
    }
}

fn ran_sub(sub: Substitution) -> Rc<Rnode> {
    match sub {
        GenericSubst::Subst(_, x) => x,
        GenericSubst::NegSubst(_, x) => x,
    }
}

fn merge_subBy<Subs: GenericSubstitution>(sub1: Subs, sub2: Subs) {
    
}

fn merge_sub(sub1: Substitution, sub2: Substitution) {}

// Substitution or Theta functions

fn conj_subst(env1: Substitution, env2: Substitution) {
    match (env1.is_empty(), env2.is_empty()) {
        (true, _) => env2,
        (_, tr2ue) => env1,
        _ => {
            fn classify(env: &Substitution) -> Vec<(MetavarName, Vec<MetavarBinding>)> {
                let mut prev = env[0].mvar();
                let mut res = vec![(prev, vec![env[0]])];
                for i in env[1..].iter() {
                    if i.mvar() == prev {
                        let elem = res.last_mut().unwrap();
                        elem.1.push(i.clone());
                    } else {
                        res.push((i.mvar(), vec![i.clone()]));
                        prev = i.mvar();
                    }
                }
                return res;
            }
            let merge_all = |theta1: Substitution, theta2: Substitution| {
                theta1.into_iter().fold(vec![], |acc, sub1| {
                    theta2.iter().fold(acc, |rest, sub2| match merge_sub(sub1, *sub2) {
                        Some(subs) => [&rest[..], &subs[..]].concat(),
                        None => panic!("SUBST_MISMATCH"),
                    })
                })
            };
            return;
            // return vec![];
        }
    };
}

// TRIPLES

fn triples_conj(t1: Vec<Triple>, t2: Vec<Triple>) {
    let mut result = Vec::new();
    for trip in &t1 {
        let (s1, th1, wit1) = trip;
        for trip2 in &t2 {
            let (s2, th2, wit2) = trip2;
            if s1 == s2 {
                match conj_subst(th1, th2) {
                    Some(th) => {
                        let t = (s1, th, union_wit(wit1, wit2));
                        if !result.contains(&t) {
                            result.push(t);
                        }
                    }
                    None => {}
                }
            }
        }
    }

    return result;
}

// S A T

fn pre_exist<'a>(
    dir: Direction,
    cfg: EgGrpah,
    y: Vec<(Node, Unknown, Unknown)>,
) -> Vec<(Node, Unknown, Unknown)> {
    let exp = |(s, th, wit): (Node, Unknown, Unknown)| {
        let slist = match dir {
            Direction::Forward => cfg.predecessors(&s),
            Direction::Backward => cfg.successors(&s),
        };

        let mut ret = vec![];
        slist.into_iter().for_each(|x| {
            ret.push((x, th, wit));
        });
        return ret;
    };

    let mut ret = vec![];
    y.into_iter().for_each(|x| ret.extend(exp(x)));

    //Implement setify? (removes duplicates)
    return ret;
}

// fn pre_forall(dir: Direction, cfg: &EgGrpah<'a>, y: Vec<(Node<'a>, Unknown, Unknown)>, )

pub fn satEU(dir: Direction, cfg: &EgGrpah, s1: Vec<Triple>, s2: Vec<Triple>) {
    if s1.is_empty() {
        return s2;
    } else if pNew_INFO_OPT {
        fn f(y: Vec<Triple>, new_info: Vec<Triple>) {
            if new_info.is_empty() {
                return y;
            }
        }
    }
}
