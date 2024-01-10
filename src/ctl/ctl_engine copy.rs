use ctl_ast::Direction;
use either::Either;
use itertools::Itertools;
use ra_hir::known::{std, usize};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::iter;
use std::marker::PhantomData;

use crate::{commons::info::Unknown, ctl::ctl_ast};

use super::ctl_ast::{GenericCtl, GenericSubst, GenericWitnessTree, GenericWitnessTreeList};

static pNEW_INFO_OPT: bool = true;
static pSATLEBEL_MEMO_OPT: bool = true;
static pREQUIRED_ENV_OPT: bool = true;
type Substitution<Mvar: Eq, Value: Clone + Eq> = ctl_ast::GenericSubst<Mvar, Value>;
type SubstitutionList<S: Subs> = Vec<Substitution<S::Mvar, S::Value>>;
type Witness<State, Anno, Value> = ctl_ast::GenericWitnessTree<State, Anno, Value>;

type NodeList<G: Graph> = Vec<G::Node>;

type Triple<G: Graph, S: Subs, P: Pred> = (G::Node, SubstitutionList<S>, Vec<WitnessTree<G, S, P>>);
type TripleList<G: Graph, S: Subs, P: Pred> = Vec<Triple<G, S, P>>;

enum Auok<G: Graph, S: Subs, P: Pred> {
    Auok(TripleList<G, S, P>),
    AuFailed(TripleList<G, S, P>),
}

trait Graph {
    type Cfg;
    type Node: PartialEq + Ord + Clone;

    fn predecessors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node>;
    fn successors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node>;

    fn direct_predecessors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node>;
    fn direct_successors(cfg: &Self::Cfg, node: &Self::Node) -> Vec<Self::Node>;

    fn extract_is_loop(cfg: &Self::Cfg, node: &Self::Node) -> bool;
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

type WitnessTree<G: Graph, S: Subs, P: Pred> = GenericWitnessTree<
    G::Node,
    SubstitutionList<S>,
    (G::Node, SubstitutionList<S>, Vec<GenericCtl<P::ty, S::Mvar, ()>>),
>;

fn annot<A, B, C>() {
    let simpleAnno = |l: A, phi: B, res: C| {
        print!(""); //unimplemented
    };
}

struct CTL_ENGINE<G: Graph, S: Subs, P: Pred> {
    reachable_state: HashMap<(G::Node, Direction), Vec<G::Node>>,
    has_loop: bool,
    _b: PhantomData<S>,
    _c: PhantomData<P>,
}



//===========================================================================/
//Functions//

fn union_vec<A: PartialEq + Clone>(a: &Vec<A>, b: &Vec<A>) -> Vec<A>{
    b.iter().fold(a.clone(), |mut acc, x| {
        if acc.contains(x) {
            return acc;
        }
        else {
            acc.push(x.clone());
            return acc;
        }
    })
}

//FixPOINT
fn fix<A>(eq: impl Fn(&A, &A) -> bool, f: impl Fn(&A) -> A, x: A) -> A {
    let x1 = f(&x);
    if eq(&x, &x1) {
        x1
    } else {
        fix(eq, f, x1)
    }
}

fn subsetEq<A: Eq>(xs: &Vec<A>, ys: &Vec<A>) -> bool {
    xs.iter().all(|x| ys.contains(x))
}

fn setfix<A: Eq>(f: impl Fn(&Vec<A>) -> Vec<A>, x: Vec<A>) -> Vec<A> {
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
    fn mem_by<A: PartialEq>(a: &A, b: &[A]) -> bool {
        b.contains(a)
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
    fn setify<A: PartialEq>(mut v: Vec<A>) -> Vec<A> {
        v.into_iter().dedup().collect_vec()
    }

    fn nub_by<A: PartialEq + Clone>(l: &[A]) -> Vec<A> {
        match l {
            [] => vec![],
            xx => match xx.split_first() {
                Some((a, aa)) if aa.contains(a) => CTL_ENGINE::<G, S, P>::nub_by(aa),
                Some((a, aa)) => {
                    let mut b = CTL_ENGINE::<G, S, P>::nub_by(aa);
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
        CTL_ENGINE::<G, S, P>::merge_sub_by(sub1, sub2)
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
                std::cmp::Ordering::Equal => Ok(CTL_ENGINE::<G, S, P>::safe_append(
                    merge_all(ths, ths_prime)?,
                    CTL_ENGINE::<G, S, P>::loop_fn_conj(
                        ctheta[1..].to_vec(),
                        ctheta_prime[1..].to_vec(),
                        merge_all,
                    )?,
                )),
                std::cmp::Ordering::Less => Ok(CTL_ENGINE::<G, S, P>::safe_append(
                    ths.clone(),
                    CTL_ENGINE::<G, S, P>::loop_fn_conj(
                        ctheta[1..].to_vec(),
                        ctheta_prime.clone(),
                        merge_all,
                    )?,
                )),
                std::cmp::Ordering::Greater => Ok(CTL_ENGINE::<G, S, P>::safe_append(
                    ths_prime.clone(),
                    CTL_ENGINE::<G, S, P>::loop_fn_conj(
                        ctheta.clone(),
                        ctheta_prime[1..].to_vec(),
                        merge_all,
                    )?,
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
                            match CTL_ENGINE::<G, S, P>::merge_sub(sub1.clone(), sub2.clone()) {
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
                Ok(CTL_ENGINE::<G, S, P>::clean_subst(&mut CTL_ENGINE::<G, S, P>::loop_fn_conj(
                    classify::<G, S, P>(env1),
                    classify::<G, S, P>(env2),
                    merge_all,
                )?))
                // return vec![];
            }
        }
    }

    // TRIPLES
    fn triples_conj(t1: TripleList<G, S, P>, t2: &TripleList<G, S, P>) -> TripleList<G, S, P> {
        let mut shared: TripleList<G, S, P> = vec![];
        t1.iter().fold(shared, |rest, (s1, th1, wit1)| {
            t2.iter().fold(rest, |rest, (s2, th2, wit2)| {
                if s1 == s2 {
                    match CTL_ENGINE::<G, S, P>::conj_subst(th1, th2) {
                        Ok(th) => {
                            let t = (s1.clone(), th, CTL_ENGINE::<G, S, P>::union_wit(wit1, wit2));
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
        trips1: TripleList<G, S, P>,
        trips2: TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        CTL_ENGINE::<G, S, P>::union_by(&trips1, &trips2)
    }

    fn triples_complement(
        states: &Vec<G::Node>,
        mut trips: TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        let a = if trips.is_empty() {
            states.iter().map(|x| (x.clone(), vec![], vec![])).collect_vec()
        } else {
            let cleanup = |neg: Vec<G::Node>, pos: TripleList<G, S, P>| {
                let keep_pos = pos.into_iter().filter(|(x, _, _)| neg.contains(x)).collect_vec();
                let mut tmp = setdiff(states.clone(), &neg)
                    .into_iter()
                    .map(|x| (x, vec![], vec![]))
                    .collect_vec();
                tmp.extend(keep_pos);
                tmp
            };
            trips.sort();
            let all_negated = trips.into_iter().map(|(s, th, wit)| CTL_ENGINE::<G, S, P>::triple_negate(s, &th, &wit));
            let merge_one = |(neg1, pos1): &(Vec<G::Node>, TripleList<G, S, P>), (neg2, pos2): &(Vec<G::Node>, TripleList<G, S, P>)| {
                let mut pos1conj = vec![];
                let mut pos1keep = vec![];

                for x in pos1 {
                    if neg2.contains(&x.0) {
                        pos1conj.push(x.clone());
                    }
                    else {
                        pos1keep.push(x.clone());
                    }
                }
                
                let mut pos2conj = vec![];
                let mut pos2keep = vec![];

                for x in pos2 {
                    if neg1.contains(&x.0) {
                        pos2conj.push(x.clone());
                    }
                    else {
                        pos2keep.push(x.clone());
                    }
                }

                let u = union_vec(neg1, neg2);
                let mut tmp = CTL_ENGINE::<G, S, P>::triples_conj(pos1conj, &pos2conj);
                tmp.extend(pos1keep);
                tmp.extend(pos2keep);
                return (u, tmp);
            };
            fn inner_loop<G: Graph, S: Subs, P: Pred>(
                merge_one: impl Fn(&(Vec<G::Node>, TripleList<G, S, P>), &(Vec<G::Node>, TripleList<G, S, P>)) -> (Vec<G::Node>, TripleList<G, S, P>), 
                rest: &[(Vec<G::Node>, TripleList<G, S, P>)]) -> Vec<(Vec<G::Node>, TripleList<G, S, P>)>
                    {
                match rest {
                    [x1, x2, rest @ ..] => {
                        let mut a: Vec<(Vec<G::Node>, TripleList<G, S, P>)> = vec![merge_one(x1, x2)];
                        a.extend(inner_loop(merge_one, rest));
                        return a;
                    }
                    l => l.to_vec()
                }
            }
            vec![]
        };
        vec![]
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
        let res = CTL_ENGINE::<G, S, P>::union_by(p0, p1);
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

    // S A T

    fn pre_exist<'a>(
        dir: &Direction,
        cfg: &G::Cfg,
        y: Vec<(G::Node, Unknown, Unknown)>,
    ) -> Vec<(G::Node, Unknown, Unknown)> {
        let exp = |(s, th, wit): (G::Node, Unknown, Unknown)| {
            let slist = match dir {
                Direction::Forward => G::predecessors(&cfg, &s),
                Direction::Backward => G::successors(&cfg, &s),
            };

            let mut ret = vec![];
            slist.into_iter().for_each(|x| {
                ret.push((x, th.clone(), wit.clone()));
            });
            return ret;
        };

        let mut ret = vec![];
        y.into_iter().for_each(|x| ret.extend(exp(x)));

        //Implement setify? (removes duplicates)
        return ret;
    }

    fn pre_forall(
        dir: &Direction,
        grp: &G::Cfg,
        y: Vec<G::Node>,
        mut all: TripleList<G, S, P>,
    ) -> TripleList<G, S, P> {
        let pred = match dir {
            Direction::Forward => G::direct_predecessors,
            Direction::Backward => G::direct_successors,
        };

        let succ = match dir {
            Direction::Backward => G::direct_predecessors,
            Direction::Forward => G::direct_successors,
        };

        let neighbours =
            CTL_ENGINE::<G, S, P>::setify(y.into_iter().flat_map(|x| pred(grp, &x)).collect_vec())
                .into_iter()
                .map(|x| {
                    let s = succ(grp, &x);
                    (x, s)
                })
                .collect_vec();
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
                .map(|a| foldl1(|x, y| CTL_ENGINE::<G, S, P>::triples_conj(x, y), a))
                .flatten()
                .collect_vec(),
        }
    }

    pub fn satAX(dir: &Direction, m: &G::Cfg, s: TripleList<G, S, P>) -> TripleList<G, S, P> {
        CTL_ENGINE::<G, S, P>::pre_forall(dir, m, s.iter().map(|x| x.0.clone()).collect_vec(), s)
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
    pub fn sat_AU<B, C>(
        dir: &Direction,
        m: (G::Cfg, B, C),
        s1: TripleList<G, S, P>,
        s2: TripleList<G, S, P>,
    ) -> Auok<G, S, P> {
        if s1.is_empty() {
            return Auok::Auok(s2);
        } else if !pNEW_INFO_OPT {
            todo!();
        } else {
            let f = |y: &TripleList<G, S, P>| {
                let pre = CTL_ENGINE::<G, S, P>::pre_forall(
                    dir,
                    &m.0,
                    y.iter().map(|x| x.0.clone()).collect_vec(),
                    y.clone(),
                );
                CTL_ENGINE::<G, S, P>::triples_union(
                    s2.clone(),
                    CTL_ENGINE::<G, S, P>::triples_conj(s1.clone(), &pre),
                )
                // CTL_ENGINE::<G, S, P>::
            };
            return Auok::Auok(setfix(f, s2.clone()));
            // CTL_ENGINE::<G, S, P>::union_by()
        }
    }

    fn satLabel(
        label: impl Fn(P::ty) -> TripleList<G, S, P>,
        required: Vec<Vec<SubstitutionList<S>>>,
        p: P::ty,
    ) -> TripleList<G, S, P> {
        let triples =
            if !pSATLEBEL_MEMO_OPT { todo!() } else { CTL_ENGINE::<G, S, P>::setify(label(p)) };
        let ntriples = normalize(triples);
        if !pREQUIRED_ENV_OPT {
            todo!();
        }
        ntriples
    }

    fn sat_verbose_loop<D>(
        unchecked: bool,
        required: Vec<Vec<SubstitutionList<S>>>,
        required_states: Option<Vec<G::Node>>,
        annot: impl Fn(isize, GenericCtl<P::ty, S::Mvar, ()>, TripleList<G, S, P>, Vec<D>) -> D,
        maxlvl: isize,
        lvl: isize,
        m: (&G::Cfg, impl Fn(P::ty) -> TripleList<G, S, P>, Vec<G::Node>),
        phi: GenericCtl<P::ty, S::Mvar, ()>,
        env: Vec<()>,
    ) -> (D, TripleList<G, S, P>) {
        let states = m.2.clone();
        let label = m.1;
        let satv = |unchecked, required, required_states, phi0, env| {
            CTL_ENGINE::<G, S, P>::sat_verbose_loop(
                unchecked,
                required,
                required_states,
                annot,
                maxlvl,
                lvl + 1,
                m,
                phi0,
                env,
            )
        };

        let anno = |res: Vec<(G::Node, SubstitutionList<S>, Vec<WitnessTree<G, S, P>>)>,
                    children| {
            let r = res.iter().clone().collect_vec();
            (annot(lvl, phi, res, children), r)
        };

        if lvl > maxlvl && maxlvl > -1 {
        } else {
            // let (d, res) =
            match phi {
                GenericCtl::False => anno(vec![], vec![]),
                GenericCtl::True => anno(CTL_ENGINE::<G, S, P>::triples_top(&states), vec![]),
                GenericCtl::Pred(p) => {
                    anno(CTL_ENGINE::<G, S, P>::satLabel(label, required, p), vec![])
                }
                GenericCtl::Not(phi1) => {
                    let (child1, res1) = satv(unchecked, required, required_states, phi1, env);
                    anno(triples)
                }
                GenericCtl::Exists(_, _, _) => {}
                GenericCtl::And(_, _) => {}
                GenericCtl::AndAny(_, _, _, _) => {}
                GenericCtl::HackForStmt(_, _, _, _) => {}
                GenericCtl::Or(_, _) => {}
                GenericCtl::Implies(_, _) => {}
                GenericCtl::AF(_, _, _) => {}
                GenericCtl::AX(_, _, _) => {}
                GenericCtl::AG(_, _, _) => {}
                GenericCtl::AW(_, _, _, _) => {}
                GenericCtl::AU(_, _, _, _) => {}
                GenericCtl::EF(_, _) => {}
                GenericCtl::EX(_, _) => {}
                GenericCtl::EG(_, _) => {}
                GenericCtl::EU(_, _, _) => {}
                GenericCtl::Let(_, _, _) => {}
                GenericCtl::LetR(_, _, _) => {}
                GenericCtl::Ref(_) => {}
                GenericCtl::SeqOr(_, _) => {}
                GenericCtl::Uncheck(_) => {}
                GenericCtl::InnerAnd(_) => {}
                GenericCtl::XX(_, _) => {}
            };
        }
        return vec![];
    }

    fn filter_partial_matches() {}

    pub fn sat(
        &mut self,
        cfg: &G::Cfg,
        lab: impl Fn(P::ty) -> Vec<(P::ty, SubstitutionList<S>)>,
        mut nodes: Vec<G::Node>,
        phi: GenericCtl<P::ty, S::Mvar, ()>,
    ) {
        if nodes.iter().any(|x| G::extract_is_loop(cfg, x)) {
            self.has_loop = true;
        }
        nodes.sort();
    }
}
