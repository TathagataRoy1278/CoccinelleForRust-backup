use ctl_ast::Direction;
use either::Either;
use itertools::Itertools;
use ra_hir::known::{std, usize};
use std::collections::HashMap;
use std::hash::Hash;
use std::iter;
use std::marker::PhantomData;
use std::{cmp::Ordering, os::linux::raw::stat};

use crate::{commons::info::Unknown, commons::util, ctl::ctl_ast, C};

use super::flag_ctl::LOOP_IN_SRC_MODE;
use super::{
    ctl_ast::{GenericCtl, GenericSubst, GenericWitnessTree, GenericWitnessTreeList, Strict},
    flag_ctl::PARTIAL_MATCH,
};

static pNEW_INFO_OPT: bool = true;
static pSATLEBEL_MEMO_OPT: bool = true;
static pREQUIRED_ENV_OPT: bool = true;
static pUNCHECKED_OPT: bool = true;
static pREQUIRED_STATES_OPT: bool = true;

type Substitution<Mvar: Eq, Value: Clone + Eq> = ctl_ast::GenericSubst<Mvar, Value>;
type SubstitutionList<S: Subs> = Vec<Substitution<S::Mvar, S::Value>>;
type Witness<State, Anno, Value> = ctl_ast::GenericWitnessTree<State, Anno, Value>;
type CTL<S: Subs, P: Pred> = Vec<GenericCtl<P::ty, S::Mvar, Vec<String>>>;
type WitnessTree<G: Graph, S: Subs, P: Pred> =
    GenericWitnessTree<G::Node, SubstitutionList<S>, Vec<CTL<S, P>>>;

type NodeList<G: Graph> = Vec<G::Node>;

type Triple<G: Graph, S: Subs, P: Pred> = (G::Node, SubstitutionList<S>, Vec<WitnessTree<G, S, P>>);
type TripleList<G: Graph, S: Subs, P: Pred> = Vec<Triple<G, S, P>>;

type Model<G: Graph, S: Subs, P: Pred> = (G::Cfg, fn(P::ty) -> TripleList<G, S, P>, fn(&P::ty) -> bool, NodeList<G>);
enum Auok<G: Graph, S: Subs, P: Pred> {
    Auok(TripleList<G, S, P>),
    AuFailed(TripleList<G, S, P>),
}

trait Graph {
    type Cfg;
    type Node: PartialEq + Ord + Clone + Hash + Copy;

    fn predecessors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node>;
    fn successors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node>;

    fn direct_predecessors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node>;
    fn direct_successors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node>;

    fn extract_is_loop(cfg: &Self::Cfg, node: &Self::Node) -> bool;

    fn size(cfg: &Self::Cfg) -> usize;
}

trait Subs {
    type Value: Clone + PartialEq + Eq + Ord;
    type Mvar: Clone + PartialEq + Eq + Ord;

    fn eq_val(a: &Self::Value, b: &Self::Value) -> bool;
    fn merge_val(a: &Self::Value, b: &Self::Value) -> Self::Value;
}

trait Pred {
    type ty: Clone + Eq + Ord;
}

enum WitAnnoTree<A> {
    WitAnno(A, Vec<WitAnnoTree<A>>),
}

fn annot<A, B, C>() {
    let simpleAnno = |l: A, phi: B, res: C| {
        print!(""); //unimplemented
    };
}

struct CTL_ENGINE<G: Graph, S: Subs, P: Pred> {
    reachable_state: HashMap<(G::Node, Direction), Vec<G::Node>>,
    reachable_table: HashMap<(G::Node, Direction), Vec<G::Node>>,
    memo_label: HashMap<P::ty, (G::Node, Substitution<S::Mvar, S::Value>)>,
    has_loop: bool,
    _b: PhantomData<S>,
    _c: PhantomData<P>,
}

//===========================================================================/
//Functions//

fn nub<A: Clone + Ord>(v: &Vec<A>) -> Vec<A> {
    let mut v = v.clone();
    v.sort();
    v.into_iter().dedup().collect_vec()
}

fn set_union<A: PartialEq + Clone>(a: &Vec<A>, b: &Vec<A>) -> Vec<A> {
    b.iter().fold(a.clone(), |mut acc, x| {
        if acc.contains(x) {
            return acc;
        } else {
            acc.push(x.clone());
            return acc;
        }
    })
}

fn mkstates<A: Clone>(states: &Vec<A>, required_states: &Option<Vec<A>>) -> Vec<A> {
    match required_states {
        None => states.clone(),
        Some(states) => states.clone(),
    }
}

fn hash_notest<A: Eq + Hash, B>(tbl: &mut HashMap<A, Vec<B>>, key: A, value: B) {
    match tbl.get_mut(&key) {
        Some(curr) => {
            let mut tmp = vec![value];
            tmp.append(curr);
            tbl.insert(key, tmp);
        }
        None => {
            tbl.insert(key, vec![value]);
        }
    }
}

fn split_subst<S: Subs>(
    theta: &SubstitutionList<S>,
    x: &S::Mvar,
) -> (SubstitutionList<S>, SubstitutionList<S>) {
    let mut t = vec![];
    let mut f = vec![];

    for i in theta {
        if i.mvar().eq(x) {
            t.push(i.clone());
        } else {
            f.push(i.clone());
        }
    }

    return (t, f);
}

//FixPOINT
fn fix<A>(eq: impl Fn(&A, &A) -> bool, f: impl Fn(&A) -> A, x: &A) -> A {
    let x1 = f(x);
    if eq(&x, &x1) {
        x1
    } else {
        fix(eq, f, &x1)
    }
}

fn subsetEq<A: Eq>(xs: &Vec<A>, ys: &Vec<A>) -> bool {
    xs.iter().all(|x| ys.contains(x))
}

fn setfix<A: Eq>(f: impl Fn(&Vec<A>) -> Vec<A>, x: &Vec<A>) -> Vec<A> {
    fix(subsetEq, f, x)
}

fn setgfix<A: Eq>(f: impl Fn(&Vec<A>) -> Vec<A>, x: &Vec<A>) -> Vec<A> {
    fix(subsetEq, f, x)
}

//---------

fn foldl1<A>(f: impl FnMut(A, &A) -> A, mut xs: Vec<A>) -> A {
    let item = xs.remove(0);
    xs.iter().fold(item, f)
}

fn setdiff<A: PartialEq>(xs: Vec<A>, ys: &Vec<A>) -> Vec<A> {
    xs.into_iter().filter(|x| !ys.contains(x)).collect_vec()
}

fn normalize<A, B: Ord, C: Ord>(trips: Vec<(A, Vec<B>, Vec<C>)>) -> Vec<(A, Vec<B>, Vec<C>)> {
    trips
        .into_iter()
        .map(|(a, mut b, mut c)| {
            b.sort();
            c.sort();
            (a, b, c)
        })
        .collect_vec()
}

fn negate_subst<S: Subs>(th: &SubstitutionList<S>) -> Vec<SubstitutionList<S>> {
    th.iter().map(|x| vec![x.neg()]).collect_vec()
}

fn negate_wit<G: Graph, S: Subs, P: Pred>(
    wit: &Vec<WitnessTree<G, S, P>>,
) -> Vec<Vec<WitnessTree<G, S, P>>> {
    let mut tmp = wit.iter().map(|x| vec![x.neg()]).collect_vec();
    tmp.sort();
    tmp
}

impl<G: Graph, S: Subs, P: Pred> CTL_ENGINE<G, S, P> {
    fn drop_wits(
        required_states: &Option<NodeList<G>>,
        s: &TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        match required_states {
            None => s.clone(),
            Some(states) => {
                s.clone().into_iter().filter(|(s, _, _)| states.contains(s)).collect_vec()
            }
        }
    }

    fn mem_by<A: PartialEq>(a: &A, b: &[A]) -> bool {
        b.contains(a)
    }

    fn get_children_required_states(
        dir: &Direction,
        m: &Model<G, S, P>,
        required_states: &Option<NodeList<G>>,
    ) -> Option<NodeList<G>> {
        None
    }

    fn strict_a1(
        strict: Strict,
        op: fn(
            &Direction,
            &Model<G, S, P>,
            &TripleList<G, S, P>,
            &Option<NodeList<G>>,
        ) -> TripleList<G, S, P>,
        failop: fn(
            &Direction,
            &Model<G, S, P>,
            &TripleList<G, S, P>,
            &Option<NodeList<G>>,
        ) -> TripleList<G, S, P>,
        dir: &Direction,
        m: &Model<G, S, P>,
        trips: &TripleList<G, S, P>,
        required_states: &Option<Vec<G::Node>>,
    ) -> TripleList<G, S, P> {
        let res = op(dir, &m, trips, required_states);
        if !PARTIAL_MATCH && strict == Strict::Strict {
            let states = mkstates(&m.3, &required_states);
            let fail = Self::filter_conj(&states, &res, &(failop(dir, m, trips, required_states)));
            return Self::triples_union(&res, &fail);
        } else {
            return res;
        }
    }

    fn strict_A2au(
        strict: Strict,
        op: fn(
            &Direction,
            &Model<G, S, P>,
            &TripleList<G, S, P>,
            &TripleList<G, S, P>,
            &Option<NodeList<G>>,
        ) -> Auok<G, S, P>,
        failop: fn(
            &Direction,
            &Model<G, S, P>,
            &TripleList<G, S, P>,
            &Option<NodeList<G>>,
        ) -> TripleList<G, S, P>,
        dir: &Direction,
        m: &Model<G, S, P>,
        trips1: &TripleList<G, S, P>,
        trips2: &TripleList<G, S, P>,
        required_states: &Option<NodeList<G>>,
    ) -> Auok<G, S, P> {
        match op(dir, m, trips1, trips2, required_states) {
            Auok::Auok(res) => {
                if !PARTIAL_MATCH && strict == Strict::Strict {
                    let states = mkstates(&m.3, required_states);
                    let fail =
                        Self::filter_conj(&states, &res, &failop(dir, m, trips1, required_states));
                    Auok::Auok(Self::triples_union(&res, &fail))
                } else {
                    Auok::Auok(res)
                }
            }
            Auok::AuFailed(res) => Auok::AuFailed(res),
        }
    }

    fn strict_A2(
        strict: Strict,
        op: fn(
            &Direction,
            &Model<G, S, P>,
            &TripleList<G, S, P>,
            &TripleList<G, S, P>,
            &Option<NodeList<G>>,
        ) -> TripleList<G, S, P>,
        failop: fn(
            &Direction,
            &Model<G, S, P>,
            &TripleList<G, S, P>,
            &Option<NodeList<G>>,
        ) -> TripleList<G, S, P>,
        dir: &Direction,
        m: &Model<G, S, P>,
        trips1: &TripleList<G, S, P>,
        trips2: &TripleList<G, S, P>,
        required_states: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        let res = op(dir, m, trips1, trips2, required_states);
        if !PARTIAL_MATCH && strict == Strict::Strict {
            let states = mkstates(&m.3, required_states);
            let fail = Self::filter_conj(&states, &res, &failop(dir, m, trips2, required_states));
            Self::triples_union(&res, &fail)
        } else {
            res
        }
    }

    fn reachsatEF(&self, dir: &Direction, grp: &Model<G, S, P>, s2: &NodeList<G>) -> NodeList<G> {
        let dirop = |node: &G::Node| match dir {
            Direction::Forward => G::successors(&grp.0, node),
            Direction::Backward => G::predecessors(&grp.0, node),
        };

        fn f<G: Graph, S: Subs, P: Pred>(
            y: &NodeList<G>,
            res: &NodeList<G>,
            ht: &HashMap<(G::Node, Direction), NodeList<G>>,
            dir: &Direction,
            dirop: impl Fn(&G::Node) -> Vec<G::Node>,
        ) -> NodeList<G> {
            match res.as_slice() {
                [] => y.clone(),
                ni => {
                    let mut pre_collected = vec![];
                    let mut new_info = vec![];

                    for n in ni {
                        let t = ht.get(&(n.clone(), *dir));
                        if t.is_some() {
                            pre_collected.push(t.unwrap());
                        } else {
                            new_info.push(n.clone());
                        }
                    }
                    let y = pre_collected
                        .iter()
                        .fold(y.clone(), |rest, x| CTL_ENGINE::<G, S, P>::union_by(x, &res));
                    let first = CTL_ENGINE::<G, S, P>::inner_setify(
                        &new_info.iter().flat_map(|node| dirop(node)).collect_vec(),
                    );
                    let new_info = setdiff(first, &y);
                    let mut res = new_info.clone();
                    res.extend(y);
                    f::<G, S, P>(&res, &new_info, ht, dir, dirop)
                }
            }
        }
        f::<G, S, P>(s2, s2, &self.reachable_table, dir, dirop).into_iter().rev().collect_vec()
    }

    fn triple_negate(
        s: G::Node,
        th: &SubstitutionList<S>,
        wit: &Vec<WitnessTree<G, S, P>>,
    ) -> (Vec<G::Node>, TripleList<G, S, P>) {
        let mut negths: TripleList<G, S, P> =
            negate_subst::<S>(th).into_iter().map(|x| (s.clone(), x, vec![])).collect_vec();
        let negwit: TripleList<G, S, P> = negate_wit::<G, S, P>(wit)
            .into_iter()
            .map(|x| (s.clone(), th.clone(), x))
            .collect_vec();
        negths.extend(negwit);
        return (vec![s], negths);
    }

    fn triples_top(
        states: &Vec<G::Node>,
    ) -> Vec<(G::Node, SubstitutionList<S>, Vec<WitnessTree<G, S, P>>)> {
        states.iter().map(|x| (x.clone(), vec![], vec![])).collect_vec()
    }

    fn setify<A: PartialEq + Clone + Ord>(mut v: &Vec<A>) -> Vec<A> {
        nub(v)
    }

    fn inner_setify<A: PartialEq + Clone + Ord>(mut v: &Vec<A>) -> Vec<A> {
        let mut a = Self::setify(v);
        a.sort();
        a
    }

    fn triples_witness(
        x: &S::Mvar,
        unchecked: bool,
        not_keep: bool,
        trips: &TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        let anyneg = |x: &SubstitutionList<S>| {
            x.iter().any(|x| match x {
                GenericSubst::NegSubst(_, _) => true,
                GenericSubst::Subst(_, _) => false,
            })
        };
        let allnegwit = |x: &Vec<WitnessTree<G, S, P>>| {
            x.iter().all(|a| match a {
                GenericWitnessTree::Wit(_, _, _, _) => false,
                GenericWitnessTree::NegWit(_) => true,
            })
        };
        let anynegwit = |x: &Vec<WitnessTree<G, S, P>>| {
            x.iter().any(|a| match a {
                GenericWitnessTree::Wit(_, _, _, _) => false,
                GenericWitnessTree::NegWit(_) => true,
            })
        };
        let negtopos = |x: &Vec<WitnessTree<G, S, P>>| {
            x.iter()
                .map(|a| match a {
                    GenericWitnessTree::Wit(_, _, _, _) => panic!("bad wit"),
                    GenericWitnessTree::NegWit(x) => (**x).clone(),
                })
                .collect_vec()
        };

        let res = trips.iter().fold(vec![], |mut prev, t @ (s, th, wit)| {
            let (th_x, newth) = split_subst::<S>(&th, x);
            match th_x.as_slice() {
                [] => {
                    prev.insert(0, t.clone());
                    prev
                }
                l if anyneg(&l.to_vec()) => prev,
                _ => {
                    let new_triple = if unchecked || not_keep {
                        (s.clone(), newth, wit.clone())
                    } else if anynegwit(wit) && allnegwit(wit) {
                        (
                            s.clone(),
                            newth,
                            vec![WitnessTree::<G, S, P>::NegWit(Box::new(
                                WitnessTree::<G, S, P>::Wit(
                                    s.clone(),
                                    th_x,
                                    vec![],
                                    negtopos(&wit),
                                ),
                            ))],
                        )
                    } else {
                        (
                            s.clone(),
                            newth,
                            vec![WitnessTree::<G, S, P>::Wit(s.clone(), th_x, vec![], wit.clone())],
                        )
                    };
                    prev.insert(0, new_triple.clone());
                    prev
                }
            }
        });
        if unchecked {
            Self::setify(&res)
        } else {
            res.into_iter().rev().collect_vec()
        }
    }

    fn nub_by<A: PartialEq + Clone>(l: &[A]) -> Vec<A> {
        match l {
            [] => vec![],
            xx => match xx.split_first() {
                Some((a, aa)) if aa.contains(a) => Self::nub_by(aa),
                Some((a, aa)) => {
                    let mut b = Self::nub_by(aa);
                    b.insert(0, a.clone());
                    b
                }
                _ => {
                    panic!("Should not ever come here as the empty case has been handled")
                }
            },
        }
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
            (GenericSubst::Subst(x1, ref v1), GenericSubst::Subst(_x2, ref v2)) => {
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
            (GenericSubst::NegSubst(x1, ref v1), GenericSubst::NegSubst(x2, ref v2)) => {
                if v1 == v2 {
                    let merged = S::merge_val(v1, v2);
                    if &merged == v1 && &merged == v2 {
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
        Self::merge_sub_by(sub1, sub2)
    }

    // Substitution or Theta functions
    fn safe_append<A>(mut a: Vec<A>, b: Vec<A>) -> Vec<A> {
        a.extend(b);
        return a;
    }

    fn clean_subst(mut theta: &mut SubstitutionList<S>) -> SubstitutionList<S> {
        theta.sort_by(|s1, s2| {
            let res = s1.mvar().cmp(s2.mvar());
            if res.is_eq() {
                match (s1, s2) {
                    (GenericSubst::Subst(_, _), GenericSubst::NegSubst(_, _)) => {
                        std::cmp::Ordering::Less
                    }
                    (GenericSubst::NegSubst(_, _), GenericSubst::Subst(_, _)) => {
                        std::cmp::Ordering::Greater
                    }
                    _ => s1.value().cmp(&s2.value()),
                }
            } else {
                res
            }
        });
        fn loop_fn<S: Subs>(theta: &[Substitution<S::Mvar, S::Value>]) -> SubstitutionList<S> {
            let mut res = vec![];
            match theta {
                [] => {
                    vec![]
                }
                [a @ GenericSubst::Subst(m1, v1), _b @ GenericSubst::NegSubst(m2, v2), rest @ ..]
                    if &m1 == &m2 =>
                {
                    res.push(a.clone());
                    res.extend(loop_fn::<S>(rest));
                    return res;
                }
                [a, rest @ ..] => {
                    res.push(a.clone());
                    res.extend(loop_fn::<S>(rest));
                    return res;
                }
            }
        }

        return loop_fn::<S>(theta);
    }

    fn loop_fn_conj(
        mut ctheta: Vec<(S::Mvar, SubstitutionList<S>)>,
        mut ctheta_prime: Vec<(S::Mvar, SubstitutionList<S>)>,
        merge_all: impl Fn(
            &SubstitutionList<S>,
            &SubstitutionList<S>,
        ) -> Result<SubstitutionList<S>, &'static str>,
    ) -> Result<SubstitutionList<S>, &'static str> {
        match (ctheta.as_slice(), ctheta_prime.as_slice()) {
            ([], _) => Ok(ctheta_prime.iter().flat_map(|(_, ths)| ths.clone()).collect()),
            (_, []) => Ok(ctheta.iter().flat_map(|(_, ths)| ths.clone()).collect()),
            (&[(ref x, ref ths)], &[(ref y, ref ths_prime)]) => match x.cmp(&y) {
                std::cmp::Ordering::Equal => Ok(Self::safe_append(
                    merge_all(ths, ths_prime)?,
                    Self::loop_fn_conj(
                        ctheta[1..].to_vec(),
                        ctheta_prime[1..].to_vec(),
                        merge_all,
                    )?,
                )),
                std::cmp::Ordering::Less => Ok(Self::safe_append(
                    ths.clone(),
                    Self::loop_fn_conj(ctheta[1..].to_vec(), ctheta_prime.clone(), merge_all)?,
                )),
                std::cmp::Ordering::Greater => Ok(Self::safe_append(
                    ths_prime.clone(),
                    Self::loop_fn_conj(ctheta.clone(), ctheta_prime[1..].to_vec(), merge_all)?,
                )),
            },
            _ => panic!("ctl_engine: not possible 2"),
        }
    }

    fn conj_subst(
        env1: &SubstitutionList<S>,
        env2: &SubstitutionList<S>,
    ) -> Result<SubstitutionList<S>, &'static str> {
        match (env1.is_empty(), env2.is_empty()) {
            (true, _) => Ok(env2.clone()),
            (_, true) => Ok(env1.clone()),
            _ => {
                fn classify<G: Graph, S: Subs, P: Pred>(
                    env: &[Substitution<S::Mvar, S::Value>],
                ) -> Vec<(S::Mvar, Vec<Substitution<S::Mvar, S::Value>>)> {
                    match env {
                        [] => vec![],
                        [x] => vec![(x.mvar().clone(), vec![x.clone()])],
                        [x, xs @ ..] => match classify::<G, S, P>(xs).as_slice() {
                            res @ [(nm, y), ys @ ..] => {
                                if x.mvar() == nm {
                                    let mut tmp = vec![x.clone()];
                                    tmp.append(&mut y.clone());
                                    let mut tmp = vec![(nm.clone(), tmp)];
                                    tmp.append(&mut ys.to_vec());
                                    tmp
                                } else {
                                    let mut tmp = vec![(x.mvar().clone(), vec![x.clone()])];
                                    tmp.append(&mut res.to_vec());
                                    tmp
                                }
                            }
                            _ => panic!("ctl_engine: not possible 1"),
                        },
                    }
                }
                let merge_all = |theta1: &SubstitutionList<S>,
                                 theta2: &SubstitutionList<S>|
                 -> Result<SubstitutionList<S>, &'static str> {
                    let mut is_error = false;
                    let res = theta1.into_iter().fold(vec![], |acc, sub1| {
                        if is_error {
                            return vec![];
                        }
                        theta2.iter().fold(acc, |rest, sub2| {
                            if is_error {
                                return vec![];
                            }
                            match Self::merge_sub(sub1.clone(), sub2.clone()) {
                                Some(subs) => [&rest[..], &subs[..]].concat(),
                                None => {
                                    is_error = true;
                                    vec![]
                                }
                            }
                        })
                    });
                    if is_error {
                        return Err("SUBST_MISMATCH");
                    } else {
                        return Ok(res);
                    }
                };
                Ok(Self::clean_subst(&mut Self::loop_fn_conj(
                    classify::<G, S, P>(env1),
                    classify::<G, S, P>(env2),
                    merge_all,
                )?))
                // return vec![];
            }
        }
    }

    // TRIPLES
    fn triples_conj(t1: &TripleList<G, S, P>, t2: &TripleList<G, S, P>) -> TripleList<G, S, P> {
        let mut shared: TripleList<G, S, P> = vec![];
        t1.iter().fold(shared, |rest, (s1, th1, wit1)| {
            t2.iter().fold(rest, |rest, (s2, th2, wit2)| {
                if s1 == s2 {
                    match Self::conj_subst(th1, th2) {
                        Ok(th) => {
                            let t = (s1.clone(), th, Self::union_wit(wit1, wit2));
                            if rest.contains(&t) {
                                rest
                            } else {
                                iter::once(t).chain(rest.into_iter()).collect_vec()
                            }
                        }
                        Err(_) => rest,
                    }
                } else {
                    rest
                }
            })
        })
    }

    fn triples_union(
        trips1: &TripleList<G, S, P>,
        trips2: &TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        Self::union_by(&trips1, &trips2)
    }

    fn triples_complement(
        states: &Vec<G::Node>,
        mut trips: &TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        if trips.is_empty() {
            states.iter().map(|x| (x.clone(), vec![], vec![])).collect_vec()
        } else {
            let cleanup = |(neg, pos): (Vec<G::Node>, TripleList<G, S, P>)| {
                let keep_pos = pos.into_iter().filter(|(x, _, _)| neg.contains(x)).collect_vec();
                let mut tmp = setdiff(states.clone(), &neg)
                    .into_iter()
                    .map(|x| (x, vec![], vec![]))
                    .collect_vec();
                tmp.extend(keep_pos);
                tmp
            };
            let mut trips = trips.clone();
            trips.sort();
            let all_negated = trips
                .into_iter()
                .map(|(s, th, wit)| Self::triple_negate(s.clone(), &th, &wit))
                .collect_vec();
            let merge_one =
                |(neg1, pos1): &(Vec<G::Node>, TripleList<G, S, P>),
                 (neg2, pos2): &(Vec<G::Node>, TripleList<G, S, P>)| {
                    let mut pos1conj = vec![];
                    let mut pos1keep = vec![];

                    for x in pos1 {
                        if neg2.contains(&x.0) {
                            pos1conj.push(x.clone());
                        } else {
                            pos1keep.push(x.clone());
                        }
                    }

                    let mut pos2conj = vec![];
                    let mut pos2keep = vec![];

                    for x in pos2 {
                        if neg1.contains(&x.0) {
                            pos2conj.push(x.clone());
                        } else {
                            pos2keep.push(x.clone());
                        }
                    }

                    let u = set_union(neg1, neg2);
                    let mut tmp = Self::triples_conj(&pos1conj, &pos2conj);
                    tmp.extend(pos1keep);
                    tmp.extend(pos2keep);
                    return (u, tmp);
                };
            // fn inner_loop<G: Graph, S: Subs, P: Pred>(
            //     merge_one: impl Fn(&(Vec<G::Node>, TripleList<G, S, P>), &(Vec<G::Node>, TripleList<G, S, P>)) -> (Vec<G::Node>, TripleList<G, S, P>),
            //     rest: &[(Vec<G::Node>, TripleList<G, S, P>)]) -> Vec<(Vec<G::Node>, TripleList<G, S, P>)>
            //         {
            //     match rest {
            //         [x1, x2, rest @ ..] => {
            //             let mut a: Vec<(Vec<G::Node>, TripleList<G, S, P>)> = vec![merge_one(x1, x2)];
            //             a.extend(inner_loop(merge_one, rest));
            //             return a;
            //         }
            //         l => l.to_vec()
            //     }
            // }
            fn inner_loop<A: Clone>(merge_one: impl Fn(&A, &A) -> A, rest: &[A]) -> Vec<A> {
                match rest {
                    [x1, x2, res @ ..] => {
                        let mut a = vec![merge_one(x1, x2)];
                        a.extend(inner_loop(merge_one, rest));
                        return a;
                    }
                    l => return l.to_vec(),
                }
            }
            fn outer_loop<A: Clone>(
                merge_one: fn(&A, &A) -> A,
                inner_loop: fn(fn(&A, &A) -> A, &[A]) -> Vec<A>,
                rest: &[A],
            ) -> A {
                match rest {
                    [x] => x.clone(),
                    l => outer_loop(merge_one, inner_loop, inner_loop(merge_one, l).as_slice()),
                }
            }

            cleanup(outer_loop(merge_one, inner_loop, &all_negated))
        }
    }

    // fn tsriples_conj(t1: Vec<Triple<S::Mvar, S::Value, G>>, t2: Vec<Triple<S::Mvar, S::Value, G>>) {
    //     let mut result = Vec::new();
    //     for trip in &t1 {
    //         let (s1, th1, wit1) = trip;
    //         for trip2 in &t2 {
    //             let (s2, th2, wit2) = trip2;
    //             if s1 == s2 {
    //                 match CTL_ENGINE::conj_subst(th1, th2) {
    //                     Ok(th) => {
    //                         let t = (s1, th, CTL_ENGINE::union_wit(wit1, wit2));
    //                         if !result.contains(&t) {
    //                             result.push(t);
    //                         }
    //                     }
    //                     Err(s) => {
    //                         eprintln!(s)
    //                     }
    //                 }
    //             }
    //         }
    //     }
    //
    //     return;
    // }

    fn union_wit<A: Clone + Ord, B: Clone + Ord, C: Clone + Ord>(
        p0: &GenericWitnessTreeList<A, B, C>,
        p1: &GenericWitnessTreeList<A, B, C>,
    ) -> GenericWitnessTreeList<A, B, C> {
        let res = Self::union_by(p0, p1);
        let anynegwit = |x: &GenericWitnessTree<A, B, C>| match x {
            &GenericWitnessTree::Wit(_, _, _, _) => false,
            &GenericWitnessTree::NegWit(_) => true,
        };
        if res.iter().any(anynegwit) {
            res.into_iter().filter(anynegwit).collect()
        } else {
            res
        }
    }

    fn extend_required(
        trips: &TripleList<G, S, P>,
        required: &Vec<Vec<SubstitutionList<S>>>,
    ) -> Vec<Vec<SubstitutionList<S>>> {
        if !PARTIAL_MATCH {
            required.clone()
        } else if !pREQUIRED_ENV_OPT {
            todo!()
        } else {
            required.clone()
        }
    }

    fn get_required_states<A, B, C>(l: &Vec<(A, B, C)>) -> Option<Vec<A>> {
        if !pREQUIRED_STATES_OPT && PARTIAL_MATCH {
            todo!()
        } else {
            None
        }
    }

    fn unwitify_unwanted(trips: &TripleList<G, S, P>) -> TripleList<G, S, P> {
        let anynegwit = |x: &Vec<WitnessTree<G, S, P>>| -> bool {
            x.iter().any(|x| match x {
                GenericWitnessTree::Wit(_, _, _, _) => false,
                GenericWitnessTree::NegWit(_) => true,
            })
        };

        Self::setify(&trips.iter().fold(vec![], |mut prev, (s, th, wit)| {
            if anynegwit(&wit) {
                prev
            } else {
                prev.insert(0, (s.clone(), th.clone(), vec![]));
                prev
            }
        }))
    }

    //CONJ

    fn filter_conj(
        states: &NodeList<G>,
        unwanted: &TripleList<G, S, P>,
        partial_matches: &TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        let x = Self::triples_conj(
            &Self::triples_complement(&states, &Self::unwitify_unwanted(&unwanted)),
            partial_matches,
        );
        Self::triples_conj(&Self::unwitify_unwanted(&x), &Self::triples_complement(&states, &x))
    }

    fn strict_triples_conj(
        strict: Strict,
        states: NodeList<G>,
        trips1: &TripleList<G, S, P>,
        trips2: &TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        let res = Self::triples_conj(trips1, trips2);
        if !PARTIAL_MATCH && strict == Strict::Strict {
            let fail_left = Self::filter_conj(&states, trips1, trips2);
            let fail_right = Self::filter_conj(&states, trips2, trips1);
            let ors = Self::triples_union(&fail_left, &fail_right);

            Self::triples_union(&res, &ors)
        } else {
            res
        }
    }

    // S A T

    fn pre_exist(
        dir: &Direction,
        m: &Model<G, S, P>,
        y: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        let check = |s: &G::Node| match reqst {
            None => true,
            Some(reqst) => reqst.contains(s),
        };
        let exp = |(s, th, wit): &Triple<G, S, P>| {
            let slist = match dir {
                Direction::Forward => G::predecessors(&m.0, &s),
                Direction::Backward => G::successors(&m.0, &s),
            };

            let mut ret = vec![];
            slist.into_iter().for_each(|x: G::Node| {
                if check(&x) {
                    ret.push((x.clone(), th.clone(), wit.clone()));
                }
            });
            return ret;
        };

        let mut ret = vec![];
        y.into_iter().for_each(|x| ret.extend(exp(x)));

        //Implement setify? (removes duplicates)
        return Self::setify(&ret);
    }

    fn pre_forall(
        dir: &Direction,
        grp: &Model<G, S, P>,
        y: &TripleList<G, S, P>,
        mut all: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        let check = |s: &G::Node| match reqst {
            None => true,
            Some(reqst) => reqst.contains(s),
        };

        let pred = match dir {
            Direction::Forward => G::direct_predecessors,
            Direction::Backward => G::direct_successors,
        };

        let succ = match dir {
            Direction::Backward => G::direct_predecessors,
            Direction::Forward => G::direct_successors,
        };

        let neighbours = Self::setify(
            &y.into_iter()
                .flat_map(|(x, _, _)| {
                    pred(&grp.0, &x).into_iter().filter(|x| check(&x)).into_iter().collect_vec()
                })
                .collect_vec(),
        )
        .into_iter()
        .map(|x| {
            let s = succ(&grp.0, &x);
            (x, s)
        })
        .collect_vec();
        let mut all = all.clone();
        all.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));

        fn up_nodes<A: Eq + Ord + Clone, B: Clone, C: Clone>(
            child: &A,
            s: &A,
            v: &[(A, B, C)],
        ) -> Vec<(A, B, C)> {
            match v {
                [] => vec![],
                [(s1, th, wit), xs @ ..] => match s1.cmp(&child) {
                    Ordering::Less => up_nodes(child, s, xs),
                    Ordering::Equal => {
                        let mut tmp = vec![(s.clone(), th.clone(), wit.clone())];
                        tmp.extend(up_nodes(child, s, xs));
                        tmp
                    }
                    Ordering::Greater => {
                        vec![]
                    }
                },
            }
        }

        let neighbour_triples = neighbours.iter().fold(
            vec![],
            |mut rest: Vec<Vec<TripleList<G, S, P>>>, (s, children): &(G::Node, Vec<G::Node>)| {
                let mut tmp = vec![];
                let mut is_error = false;
                for child in children.into_iter() {
                    match up_nodes(child, s, all.iter().as_slice()).as_slice() {
                        [] => {
                            is_error = true;
                            break;
                        }
                        l => tmp.push(l.to_vec()),
                    }
                }
                if !is_error {
                    rest.insert(0, tmp);
                }
                rest
            },
        );

        match neighbour_triples.as_slice() {
            [] => vec![],
            _ => neighbour_triples
                .into_iter()
                .map(|a| foldl1(|x, y| Self::triples_conj(&x, y), a))
                .flatten()
                .collect_vec(),
        }
    }

    pub fn satAX(
        dir: &Direction,
        m: &Model<G, S, P>,
        s: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        Self::pre_forall(dir, m, &s, &s, reqst)
    }

    fn satEX(
        dir: &Direction,
        m: &Model<G, S, P>,
        s: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        Self::pre_exist(dir, m, s, reqst)
    }
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
    pub fn satAU(
        dir: &Direction,
        m: &Model<G, S, P>,
        s1: &TripleList<G, S, P>,
        s2: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> Auok<G, S, P> {
        if s1.is_empty() {
            return Auok::Auok(s2.clone());
        } else if !pNEW_INFO_OPT {
            todo!();
        } else {
            let f = |y: &TripleList<G, S, P>| {
                let pre = Self::pre_forall(dir, &m, y, y, reqst);
                Self::triples_union(&s2, &Self::triples_conj(&s1, &pre))
                // Self::
            };
            return Auok::Auok(setfix(f, &s2));
            // Self::union_by()
        }
    }

    pub fn satEU(
        dir: &Direction,
        m: &Model<G, S, P>,
        s1: &TripleList<G, S, P>,
        s2: &TripleList<G, S, P>,
        required_states: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        if s1.is_empty() {
            return s2.clone();
        } else if (!pNEW_INFO_OPT) {
            todo!()
        } else {
            let f = |y: &TripleList<G, S, P>| {
                let pre = Self::pre_exist(dir, m, y, required_states);
                Self::triples_union(s2, &Self::triples_conj(s1, &pre))
            };
            setfix(f, s2)
        }
    }

    fn satEG(
        dir: &Direction,
        m: &Model<G, S, P>,
        s1: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        let f = |y: &TripleList<G, S, P>| {
            let pre = Self::pre_exist(dir, m, y, reqst);
            Self::triples_conj(y, &pre)
        };
        setgfix(f, s1)
    }

    fn sat_label(
        label: impl Fn(P::ty) -> TripleList<G, S, P>,
        required: &Vec<Vec<SubstitutionList<S>>>,
        p: P::ty,
    ) -> TripleList<G, S, P> {
        let triples = if !pSATLEBEL_MEMO_OPT { todo!() } else { Self::setify(&label(p)) };
        let ntriples = normalize(triples);
        if !pREQUIRED_ENV_OPT {
            todo!();
        }
        ntriples
    }

    fn get_reachable(
        &mut self,
        dir: &Direction,
        m: &Model<G, S, P>,
        required_states: &Option<Vec<G::Node>>,
    ) -> Option<NodeList<G>> {
        match required_states {
            None => None,
            Some(states) => Some(states.iter().fold(vec![], |rest: Vec<_>, curr| {
                if rest.contains(curr) {
                    rest
                } else {
                    set_union(
                        &match self.reachable_table.get(&(curr.clone(), *dir)) {
                            None => {
                                let states = Self::reachsatEF(&self, dir, m, &vec![curr.clone()]);
                                self.reachable_table.insert((*curr, *dir), states.clone());
                                states
                            }
                            Some(s) => s.clone(),
                        },
                        &rest,
                    )
                }
            })),
        }
    }

    fn satAF(
        dir: &Direction,
        m: &Model<G, S, P>,
        s: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        if !pNEW_INFO_OPT {
            todo!()
        } else {
            let f = |y: &TripleList<G, S, P>| {
                let pre = Self::pre_forall(dir, m, y, y, reqst);
                Self::triples_union(&s, &pre)
            };
            return setfix(f, s);
        }
    }

    fn satAW(
        dir: &Direction,
        m: &Model<G, S, P>,
        s1: &TripleList<G, S, P>,
        s2: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        if s1.is_empty() {
            s2.clone()
        } else {
            let f = |y: &TripleList<G, S, P>| {
                let pre = Self::pre_forall(dir, m, y, y, reqst);
                let conj = Self::triples_conj(s1, &pre);
                Self::triples_conj(s2, &conj)
            };
            let drop_wits = |y: &TripleList<G, S, P>| {
                y.iter().map(|(s, e, _)| (s.clone(), e.clone(), vec![])).collect_vec()
            };
            setgfix(f, &Self::triples_union(&nub(&drop_wits(s1)), s2))
        }
    }

    fn satAG(
        dir: &Direction,
        m: &Model<G, S, P>,
        s: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        let f = |y: &TripleList<G, S, P>| {
            let pre = Self::pre_forall(dir, m, y, y, reqst);
            Self::triples_conj(y, &pre)
        };
        setgfix(f, s)
    }

    fn satEF(
        dir: &Direction,
        m: &Model<G, S, P>,
        s2: &TripleList<G, S, P>,
        reqst: &Option<NodeList<G>>,
    ) -> TripleList<G, S, P> {
        if !pNEW_INFO_OPT {
            todo!()
        } else {
            let f = |y: &TripleList<G, S, P>| {
                let pre = Self::pre_exist(dir, m, y, reqst);
                Self::triples_union(s2, &pre)
            };
            return setfix(f, &s2);
        }
    }

    fn sat_verbose_loop<D>(
        &mut self,
        unchecked: bool,
        required: &Vec<Vec<SubstitutionList<S>>>,
        required_states: &Option<Vec<G::Node>>,
        annot: fn(
            isize,
            // &GenericCtl<P::ty, S::Mvar, Vec<String>>,
            &TripleList<G, S, P>,
            Vec<D>,
        ) -> D,
        maxlvl: isize,
        lvl: isize,
        m: &Model<G, S, P>,
        phi: GenericCtl<P::ty, S::Mvar, Vec<String>>,
        env: &Vec<(String, TripleList<G, S, P>)>,
    ) -> (D, TripleList<G, S, P>) {
        let states = &m.3;
        let label = m.1;

        macro_rules! satv {
            ($unchecked:expr, $required:expr, $required_states:expr, $phi:expr, $env:expr) => {
                self.sat_verbose_loop(
                    $unchecked,
                    $required,
                    $required_states,
                    annot,
                    maxlvl,
                    lvl + 1,
                    m,
                    $phi,
                    $env,
                )
            };
        }

        // let satv = &mut |unchecked,
        //                  required: &Vec<Vec<SubstitutionList<S>>>,
        //                  required_states: &Option<NodeList<G>>,
        //                  phi0: GenericCtl<P::ty, S::Mvar, Vec<String>>,
        //                  env: &Vec<(String, TripleList<G, S, P>)>| {
        //     self.sat_verbose_loop(
        //         unchecked,
        //         required,
        //         required_states,
        //         annot,
        //         maxlvl,
        //         lvl + 1,
        //         m,
        //         phi0,
        //         env
        //     )
        // };

        let anno = |res: Vec<(G::Node, SubstitutionList<S>, Vec<WitnessTree<G, S, P>>)>,
                    children| {
            // let r = res.iter().clone().collect_vec();
            (annot(lvl, &res, children), res)
        };

        if lvl > maxlvl && maxlvl > -1 {
            unimplemented!();
        } else {
            let (child, res) = match phi {
                GenericCtl::False => anno(vec![], vec![]),
                GenericCtl::True => anno(Self::triples_top(&states), vec![]),
                GenericCtl::Pred(p) => anno(Self::sat_label(label, required, p), vec![]),
                GenericCtl::Not(phi1) => {
                    let (child1, res1) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    anno(
                        Self::triples_complement(&mkstates(&states, &required_states), &res1),
                        vec![child1],
                    )
                }
                GenericCtl::Exists(keep, v, phi) => {
                    let new_required = required;
                    let (child, res) = self.sat_verbose_loop(
                        unchecked,
                        new_required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi,
                        env,
                    );
                    anno(Self::triples_witness(&v, unchecked, !keep, &res), vec![child])
                }
                GenericCtl::And(strict, (phi1, phi2)) => {
                    let pm = !false; //PARTIAL_MATC
                    match (
                        pm,
                        self.sat_verbose_loop(
                            unchecked,
                            required,
                            required_states,
                            annot,
                            maxlvl,
                            lvl + 1,
                            m,
                            *phi1,
                            env,
                        ),
                    ) {
                        (false, (child1, res)) if res.is_empty() => anno(vec![], vec![child1]),
                        (_, (child1, res1)) => {
                            let new_required = Self::extend_required(&res1, &required);
                            let new_required_states = Self::get_required_states(&res1);
                            match (
                                pm,
                                self.sat_verbose_loop(
                                    unchecked,
                                    &new_required,
                                    &new_required_states,
                                    annot,
                                    maxlvl,
                                    lvl + 1,
                                    m,
                                    *phi2,
                                    env,
                                ),
                            ) {
                                (false, (child2, res)) if res.is_empty() => {
                                    anno(vec![], vec![child1, child2])
                                }
                                (_, (child2, res2)) => {
                                    let res = Self::strict_triples_conj(
                                        strict,
                                        mkstates(&states, &required_states),
                                        &res1,
                                        &res2,
                                    );
                                    anno(res, vec![child1, child2])
                                }
                            }
                        }
                    }
                }
                GenericCtl::AndAny(dir, strict, phi1, phi2) => {
                    let pm = !PARTIAL_MATCH;
                    match (
                        pm,
                        self.sat_verbose_loop(
                            unchecked,
                            required,
                            required_states,
                            annot,
                            maxlvl,
                            lvl + 1,
                            m,
                            *phi1,
                            env,
                        ),
                    ) {
                        (false, (child1, res)) if res.is_empty() => anno(vec![], vec![child1]),
                        (_, (child1, res1)) => {
                            let new_required = Self::extend_required(&res1, &required);
                            let new_required_states = Self::get_required_states(&res1);
                            let new_required_states =
                                Self::get_reachable(self, &dir, m, &new_required_states);
                            match (
                                pm,
                                //self.sat_verbose_loop(unchecked, &new_required, &new_required_states, annot, maxlvl, lvl+1, m, *phi2, env)
                                self.sat_verbose_loop(
                                    unchecked,
                                    &new_required,
                                    &new_required_states,
                                    annot,
                                    maxlvl,
                                    lvl + 1,
                                    m,
                                    *phi2,
                                    env,
                                ),
                            ) {
                                (false, (child2, res)) if res.is_empty() => {
                                    anno(res1, vec![child1, child2])
                                }
                                (_, (child2, res2)) => match res1.as_slice() {
                                    [] => {
                                        if res2.is_empty() {
                                            anno(vec![], vec![child1, child2])
                                        } else {
                                            let res =
                                                res2[1..].iter().fold(vec![res2[0].clone()], |a, b| {
                                                    let s = mkstates(&states, &required_states);
                                                    Self::strict_triples_conj(
                                                        strict,
                                                        s,
                                                        &a,
                                                        &vec![b.clone()],
                                                    )
                                                });
                                            anno(res, vec![child1, child2])
                                        }
                                    }
                                    [(state, _, _)] => {
                                        let reachable_states = new_required_states.expect(
                                            "AndAny makes no sense with no reachable states",
                                        );
                                        let mut res2_tbl = HashMap::new();
                                        res2.iter().for_each(|(s1, e, w)| {
                                            hash_notest(
                                                &mut res2_tbl,
                                                *s1,
                                                (*state, e.clone(), w.clone()),
                                            );
                                        });
                                        let s = mkstates(&states, &required_states);
                                        let res = reachable_states.iter().fold(res1, |a, st| {
                                            let b = res2_tbl.get(st);
                                            match b {
                                                Some(b) => {
                                                    Self::strict_triples_conj(strict, s.clone(), &a, b)
                                                }
                                                None => a,
                                            }
                                        });
                                        anno(res, vec![child1, child2])
                                    }
                                    _ => {
                                        panic!("only one result allowed for the left arg of AndAny")
                                    }
                                },
                            }
                        }
                    }
                }
                GenericCtl::HackForStmt(_, _, _, _) => {
                    panic!("should not be called")
                }
                GenericCtl::Or(phi1, phi2) => {
                    let (child1, res1) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    let (child2, res2) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi2,
                        env,
                    );
                    anno(Self::triples_union(&res1, &res2), vec![child1, child2])
                }
                GenericCtl::Implies(phi1, phi2) => self.sat_verbose_loop(
                    unchecked,
                    required,
                    required_states,
                    annot,
                    maxlvl,
                    lvl + 1,
                    m,
                    C![Or, C![Not, *phi1], *phi2],
                    env,
                ),
                GenericCtl::AF(dir, strict, phi1) => {
                    if !LOOP_IN_SRC_MODE {
                        return satv!(
                            unchecked,
                            required,
                            required_states,
                            C![AU, dir, strict, C![True], *phi1],
                            env
                        );
                    } else {
                        let new_required_states = self.get_reachable(&dir, m, &required_states);
                        let (child, res) = self.sat_verbose_loop(
                            unchecked,
                            required,
                            &new_required_states,
                            annot,
                            maxlvl,
                            lvl + 1,
                            m,
                            *phi1,
                            env,
                        );
                        let res = Self::strict_a1(
                            strict,
                            Self::satAF,
                            Self::satEF,
                            &dir,
                            m,
                            &res,
                            &new_required_states,
                        );
                        anno(res, vec![child])
                    }
                }
                GenericCtl::AX(dir, strict, phi1) => {
                    let new_required_states =
                        Self::get_children_required_states(&dir, m, &required_states);
                    let (child, res) = self.sat_verbose_loop(
                        unchecked,
                        &required,
                        &new_required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    let res = Self::strict_a1(
                        strict,
                        Self::satAX,
                        Self::satEX,
                        &dir,
                        m,
                        &res,
                        &required_states,
                    );
                    anno(res, vec![child])
                }
                GenericCtl::AG(dir, strict, phi1) => {
                    let new_required_states = self.get_reachable(&dir, m, required_states);
                    let (child, res) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        &new_required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    let res = Self::strict_a1(
                        strict,
                        Self::satAG,
                        Self::satEF,
                        &dir,
                        m,
                        &res,
                        &new_required_states,
                    );
                    anno(res, vec![child])
                }
                GenericCtl::AW(_, _, _, _) => {
                    panic!("Should not be used")
                }
                GenericCtl::AU(dir, strict, phi1, phi2) => {
                    let new_required_states = self.get_reachable(&dir, m, required_states);
                    match self.sat_verbose_loop(
                        unchecked,
                        required,
                        &new_required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi2,
                        env,
                    ) {
                        (child2, v) if v.is_empty() => anno(vec![], vec![child2]),
                        (child2, s2) => {
                            let new_required = Self::extend_required(&s2, &required);
                            let (child1, s1) = self.sat_verbose_loop(
                                unchecked,
                                &new_required,
                                &new_required_states,
                                annot,
                                maxlvl,
                                lvl + 1,
                                m,
                                *phi1,
                                env,
                            );
                            let res = Self::strict_A2au(
                                strict,
                                Self::satAU,
                                Self::satEF,
                                &dir,
                                m,
                                &s1,
                                &s2,
                                &new_required_states,
                            );
                            match res {
                                Auok::Auok(res) => anno(res, vec![child1, child2]),
                                Auok::AuFailed(tmp_res) => {
                                    let s1 = Self::triples_conj(
                                        &Self::satEU(&dir, m, &s1, &tmp_res, &new_required_states),
                                        &s1,
                                    );
                                    let res = Self::strict_A2(
                                        strict,
                                        Self::satAW,
                                        Self::satEF,
                                        &dir,
                                        m,
                                        &s1,
                                        &s2,
                                        &new_required_states,
                                    );
                                    anno(res, vec![child1, child2])
                                }
                            }
                        }
                    }
                }
                GenericCtl::EF(dir, phi1) => {
                    let new_required_states = self.get_reachable(&dir, m, required_states);
                    let (child, res) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        &new_required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    anno(Self::satEF(&dir, m, &res, &new_required_states), vec![child])
                }
                GenericCtl::EX(dir, phi) => {
                    let new_required_states =
                        Self::get_children_required_states(&dir, m, required_states);
                    let (child, res) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        &new_required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi,
                        env,
                    );
                    anno(Self::satEX(&dir, m, &res, &required_states), vec![child])
                }
                GenericCtl::EG(dir, phi1) => {
                    let new_required_states = self.get_reachable(&dir, m, required_states);
                    let (child, res) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        &new_required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    anno(Self::satEG(&dir, m, &res, &new_required_states), vec![child])
                }
                GenericCtl::EU(dir, phi1, phi2) => {
                    let new_required_states = self.get_reachable(&dir, m, required_states);
                    match (self.sat_verbose_loop(
                        unchecked,
                        required,
                        &new_required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi2,
                        env,
                    )) {
                        (child2, v) if v.is_empty() => anno(vec![], vec![child2]),
                        (child2, res2) => {
                            let new_required = Self::extend_required(&res2, required);
                            let (child1, res1) = self.sat_verbose_loop(
                                unchecked,
                                &new_required,
                                &new_required_states,
                                annot,
                                maxlvl,
                                lvl + 1,
                                m,
                                *phi1,
                                env,
                            );
                            anno(
                                Self::satEU(&dir, m, &res1, &res2, &new_required_states),
                                vec![child1, child2],
                            )
                        }
                    }
                }
                GenericCtl::Let(v, phi1, phi2) => {
                    let (child1, res1) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    let mut q = vec![(v, res1)];
                    q.extend(env.clone());
                    let (child2, res2) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi2,
                        &q,
                    );
                    anno(res2, vec![child1, child2])
                }
                GenericCtl::LetR(dir, v, phi1, phi2) => {
                    let new_required_states = self.get_reachable(&dir, m, required_states);
                    let (child1, res1) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        &new_required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    let mut q = vec![(v, res1)];
                    q.extend(env.clone());
                    let (child2, res2) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi2,
                        &q,
                    );
                    anno(res2, vec![child1, child2])
                }
                GenericCtl::Ref(v) => {
                    let res = &env.iter().find(|(v1, res)| &v == v1).unwrap().1;
                    let res = if unchecked {
                        res.into_iter().map(|(s, th, _)| (s.clone(), th.clone(), vec![])).collect_vec()
                    } else {
                        res.clone()
                    };
                    anno(res, vec![])
                }
                GenericCtl::SeqOr(phi1, phi2) => {
                    let (child1, res1) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    let (child2, res2) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi2,
                        env,
                    );

                    let res1neg = res1.clone().into_iter().map(|(s, th, _)| (s, th, vec![])).collect_vec();
                    let pm = !PARTIAL_MATCH;
                    match (pm, &res1, &res2) {
                        (false, res1r, res2r) if res2.is_empty() => anno(res1, vec![child1, child2]),
                        (false, res1r, res2r) if res1.is_empty() => anno(res2, vec![child1, child2]),
                        _ => anno(
                            Self::triples_union(
                                &res1,
                                &Self::triples_conj(
                                    &Self::triples_complement(
                                        &mkstates(&states, required_states),
                                        &res1neg,
                                    ),
                                    &res2,
                                ),
                            ),
                            vec![child1, child2],
                        ),
                    }
                }
                GenericCtl::Uncheck(phi1) => {
                    let unchecked = !pREQUIRED_ENV_OPT;
                    let (child1, res1) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    anno(res1, vec![child1])
                }
                GenericCtl::InnerAnd(phi1) => {
                    let (child1, res1) = self.sat_verbose_loop(
                        unchecked,
                        required,
                        required_states,
                        annot,
                        maxlvl,
                        lvl + 1,
                        m,
                        *phi1,
                        env,
                    );
                    anno(res1, vec![child1])
                }
                GenericCtl::XX(_, _) => {
                    unimplemented!()
                }
            };
            let res1 = Self::drop_wits(required_states, &res);
            return (child, res1);
        }
    }

    fn filter_partial_matches() {}

    fn preprocess(cfg: &G::Cfg, preproc: fn(&P::ty) -> bool, res: Vec<Vec<P::ty>>) -> bool {
        return true;
        // if res.is_empty() {
        //     true
        // }
        // else {
        //     let l = res;
        //     let sz: usize = G::size(cfg);
        //     let get_any = |verbose, x| {
        //         let res = preproc(x);
        //         res
        //     };
        //     let get_all = |l: &Vec<P::ty>| if l.len()  > sz-2 {false} else {
        //         // l.iter().all(|x| get_any(false, x))
        //     };
        //     if l.iter().any(|x| get_all(x)) { true }
        //     else {
        //         false
        //     }
        // }
        
    }

    pub fn sat(
        &mut self,
        m: &Model<G, S, P>,
        // lab: impl Fn(P::ty) -> Vec<(P::ty, SubstitutionList<S>)>,
        // mut nodes: Vec<G::Node>,
        phi: GenericCtl<P::ty, S::Mvar, Vec<String>>,
        reqopt: Vec<Vec<P::ty>>
    ) {
        self.reachable_table.clear();
        self.memo_label.clear();

        let (x, label, preproc, states) = m;
        if Self::preprocess(x, *preproc, reqopt) {
            if states.iter().any(|node| G::extract_is_loop(x, node)) {

            }
        }
    }
}
