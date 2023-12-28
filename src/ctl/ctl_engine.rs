use itertools::Itertools;
use ra_hir::known::usize;
use std::marker::PhantomData;

use ctl_ast::Direction;

use crate::{commons::info::Unknown, ctl::ctl_ast};

use super::ctl_ast::{GenericSubst, GenericWitnessTree, GenericWitnessTreeList};

type Substitution<Mvar: Eq, Value: Clone + SubsVal<Value> + Eq> =
    ctl_ast::GenericSubst<Mvar, Value>;
type SubstitutionList<Mvar, Val> = Vec<Substitution<Mvar, Val>>;
type Witness<State, Anno, Value> = ctl_ast::GenericWitnessTree<State, Anno, Value>;

trait Graph {
    type Cfg;
    type Node: PartialEq;
}

trait Subs {
    type Value: Clone + Eq;
    type Mvar: Clone + Eq + Ord;

    fn eq_val(a: Self::Value, b: Self::Value) -> bool;
    fn merge_val(a: Self::Value, b: Self::Value) -> Self::Value;
}

trait Pred {}

struct CTL_ENGINE<G: Graph, S: Subs, P: Pred> {
    _a: PhantomData<G>,
    _b: PhantomData<S>,
    _c: PhantomData<P>,
}

impl<G: Graph, S: Subs, P: Pred> CTL_ENGINE<G, S, P> {
    fn mem_by<A: PartialEq>(a: &A, b: &[A]) -> bool {
        b.contains(a)
    }

    fn union_by<A: Ord + Clone>(xs: &Vec<A>, tmp: &Vec<A>) -> Vec<A> {
        match tmp.as_slice() {
            [] => xs.clone(),
            ys => {
                fn loop_fn<A: Clone + PartialEq, G, S, P>(tt: &[A], ys: &[A]) -> Vec<A>
                where
                    G: Graph,
                    P: Pred,
                    S: Subs,
                {
                    match tt.split_first() {
                        None => ys.to_vec(),
                        Some((x, xs)) => {
                            if CTL_ENGINE::<G, S, P>::mem_by(x, ys) {
                                loop_fn::<A, G, S, P>(xs, ys)
                            } else {
                                let mut tmp = loop_fn::<A, G, S, P>(xs, ys);
                                tmp.insert(0, x.clone());
                                tmp
                            }
                        }
                    }
                }
                let mut t = loop_fn::<A, G, S, P>(xs.as_slice(), ys);
                t.sort();
                t
            }
        }
    }

    fn dom_sub(sub: Substitution<S::Mvar, S::Value>) -> S::Mvar {
        match sub {
            GenericSubst::Subst(x, _) => x,
            GenericSubst::NegSubst(x, _) => x,
        }
    }

    fn ran_sub(sub: Substitution<S::Mvar, S::Value>) -> S::Value {
        match sub {
            GenericSubst::Subst(_, x) => x,
            GenericSubst::NegSubst(_, x) => x,
        }
    }

    fn merge_sub_by(
        sub1: Substitution<S::Mvar, S::Value>,
        sub2: Substitution<S::Mvar, S::Value>,
    ) -> Option<Vec<GenericSubst<S::Mvar, S::Value>>> {
        match (sub1, sub2) {
            (GenericSubst::Subst(x1, v1), GenericSubst::Subst(_x2, v2)) => {
                if v1 == v2 {
                    Some(vec![GenericSubst::Subst(x1, S::merge_val(v1, v2))])
                } else {
                    None
                }
            }
            (GenericSubst::NegSubst(x1, v1), GenericSubst::Subst(x2, v2)) => {
                if v1 != v2 {
                    Some(vec![GenericSubst::Subst(x2, v2)])
                } else {
                    None
                }
            }
            (GenericSubst::Subst(x1, v1), GenericSubst::NegSubst(x2, v2)) => {
                if v1 != v2 {
                    Some(vec![GenericSubst::Subst(x1, v1)])
                } else {
                    None
                }
            }
            (GenericSubst::NegSubst(x1, v1), GenericSubst::NegSubst(x2, v2)) => {
                if v1 == v2 {
                    let merged = S::merge_val(v1, v2);
                    if merged == v1 && merged == v2 {
                        return Some(vec![GenericSubst::NegSubst(x1, merged)]);
                    }
                }
                Some(vec![
                    GenericSubst::NegSubst(x1, v1.clone()),
                    GenericSubst::NegSubst(x2, v2.clone()),
                ])
            }
        }
    }

    fn merge_sub(
        sub1: Substitution<S::Mvar, S::Value>,
        sub2: Substitution<S::Mvar, S::Value>,
    ) -> Option<Vec<GenericSubst<S::Mvar, S::Value>>> {
        CTL_ENGINE::<G, S, P>::merge_sub_by(sub1, sub2)
    }

    // Substitution or Theta functions
    fn safe_append<A>(mut a: Vec<A>, b: Vec<A>) -> Vec<A> {
        a.extend(b);
        return a;
    }

    fn loop_fn<Mvar: Ord + Clone + Eq, Val: Clone + SubsVal<Val> + Eq>(
        mut ctheta: Vec<(Mvar, SubstitutionList<Mvar, Val>)>,
        mut ctheta_prime: Vec<(Mvar, SubstitutionList<Mvar, Val>)>,
        merge_all: impl Fn(
            SubstitutionList<Mvar, Val>,
            SubstitutionList<Mvar, Val>,
        ) -> SubstitutionList<Mvar, Val>,
    ) -> SubstitutionList<Mvar, Val> {
        match (ctheta.as_slice(), ctheta_prime.as_slice()) {
            ([], _) => ctheta_prime.iter().flat_map(|(_, ths)| ths.clone()).collect(),
            (_, []) => ctheta.iter().flat_map(|(_, ths)| ths.clone()).collect(),
            (&[(x, ths)], &[(y, ths_prime)]) => match x.cmp(&y) {
                std::cmp::Ordering::Equal => CTL_ENGINE::<G, S, P>::safe_append(
                    merge_all(ths, ths_prime),
                    CTL_ENGINE::<G, S, P>::loop_fn(
                        ctheta[1..].to_vec(),
                        ctheta_prime[1..].to_vec(),
                        merge_all,
                    ),
                ),
                std::cmp::Ordering::Less => CTL_ENGINE::<G, S, P>::safe_append(
                    ths,
                    CTL_ENGINE::<G, S, P>::loop_fn(ctheta[1..].to_vec(), ctheta_prime.clone(), merge_all),
                ),
                std::cmp::Ordering::Greater => CTL_ENGINE::<G, S, P>::safe_append(
                    ths_prime,
                    CTL_ENGINE::<G, S, P>::loop_fn(ctheta.clone(), ctheta_prime[1..].to_vec(), merge_all),
                ),
            },
            _ => panic!("ctl_engine: not possible 2"),
        }
    }

    fn conj_subst(
        env1: &SubstitutionList<S::Mvar, S::Value>,
        env2: &SubstitutionList<S::Mvar, S::Value>,
    ) {
        match (env1.is_empty(), env2.is_empty()) {
            (true, _) => env2,
            (_, true) => env1,
            _ => {
                fn classify<G: Graph, S: Subs, P: Pred>(
                    env: &SubstitutionList<S::Mvar, S::Value>,
                ) -> Vec<(S::Mvar, Vec<Substitution<S::Mvar, S::Value>>)> {
                    let mut prev = env[0].mvar().clone();
                    let mut res = vec![(prev, vec![env[0]])];
                    for i in env[1..].iter() {
                        if *i.mvar() == prev {
                            let elem = res.last_mut().unwrap();
                            elem.1.push(i.clone());
                        } else {
                            res.push((i.mvar().clone(), vec![i.clone()]));
                            prev = i.mvar().clone();
                        }
                    }
                    return res;
                }
                let merge_all = |theta1: SubstitutionList<S::Mvar, S::Value>,
                                 theta2: SubstitutionList<S::Mvar, S::Value>|
                 -> SubstitutionList<S::Mvar, S::Value> {
                    theta1.into_iter().fold(vec![], |acc, sub1| {
                        theta2.iter().fold(acc, |rest, sub2| {
                            match CTL_ENGINE::<G, S, P>::merge_sub(sub1, sub2.clone()) {
                                Some(subs) => [&rest[..], &subs[..]].concat(),
                                None => panic!("SUBST_MISMATCH"),
                            }
                        })
                    })
                };
                let mut c = classify::<G, S, P>(env1);
                c.extend(classify::<G, S, P>(env2));

                return;
                // return vec![];
            }
        };
    }

    // TRIPLES
    fn triples_conj<Mvar: Clone + Eq, Val: Clone + SubsVal<Val> + Eq>(
        t1: Vec<Triple<Mvar, Val, G>>,
        t2: Vec<Triple<Mvar, Val, G>>,
    ) {
    }

    fn tsriples_conj(
        t1: Vec<Triple<S::Mvar, S::Value, G>>,
        t2: Vec<Triple<S::Mvar, S::Value, G>>,
    ) {
        let mut result = Vec::new();
        for trip in &t1 {
            let (s1, th1, wit1) = trip;
            for trip2 in &t2 {
                let (s2, th2, wit2) = trip2;
                if s1 == s2 {
                    match CTL_ENGINE::conj_subst(th1, th2) {
                        Some(th) => {
                            let t = (s1, th, CTL_ENGINE::union_wit(wit1, wit2));
                            if !result.contains(&t) {
                                result.push(t);
                            }
                        }
                        None => {}
                    }
                }
            }
        }

        return;
    }

    fn union_wit<A, B, C>(
        p0: &GenericWitnessTreeList<A, B, C>,
        p1: &GenericWitnessTreeList<A, B, C>,
    ) -> GenericWitnessTreeList<A, B, C> {
        let res = CTL_ENGINE::union_by(p0, p1);
        let anynegwit = |x| match x {
            GenericWitnessTree::Wit(_, _, _, _) => false,
            GenericWitnessTree::NegWit(_) => true,
        };
        if res.iter().any(anynegwit) {
            res.iter().filter(anynegwit).collect()
        } else {
            res
        }
    }

    // S A T

    fn pre_exist<'a>(
        dir: Direction,
        cfg: G::Cfg,
        y: Vec<(G::Node, Unknown, Unknown)>,
    ) -> Vec<(G::Node, Unknown, Unknown)> {
        let exp = |(s, th, wit): (G::Node, Unknown, Unknown)| {
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

    fn pre_forall(dir: Direction, grp: G::Cfg) {}

    // fn pre_forall(dir: Direction, cfg: &EgGrpah<'a>, y: Vec<(Node<'a>, Unknown, Unknown)>, )

    // pub fn satEU(dir: Direction, cfg: &EgGrpah, s1: Vec<Triple>, s2: Vec<Triple>) {
    //     if s1.is_empty() {
    //         return s2;
    //     } else if pNew_INFO_OPT {
    //         fn f(y: Vec<Triple>, new_info: Vec<Triple>) {
    //             if new_info.is_empty() {
    //                 return y;
    //             }
    //         }
    //     }
    // }
}
type Triple<Mvar, Value: Clone, G: Graph> =
    (G::Node, SubstitutionList<Mvar, Value>, GenericWitnessTreeList<Unknown, Unknown, Unknown>);

pub trait SubsVal<Value> {
    // fn print_mvar(&self, b: Self) -> bool;
    // fn print_value(&self, b: Self) -> bool;
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

// pub trait Graph {
//     type CFG;
//     type Node;
//
//     fn predecessors(&self, node: &Self::Node) -> Vec<Self::Node>;
//     fn successors(&self, node: &Self::Node) -> Vec<Self::Node>;
//
//     fn direct_predecessors(&self, node: &Self::Node) -> Vec<Self::Node>;
//     fn direct_successors(&self, node: &Self::Node) -> Vec<Self::Node>;
//
//     fn extract_is_loop(&self, node: &Self::Node) -> bool;
//
//     fn print_node(node: &Self::Node);
//     fn size(&self) -> usize;
// }
//
