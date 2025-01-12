use std::{
    borrow::Borrow,
    fmt::{Debug, Display},
    marker::PhantomData,
};

// use super::ctl_engine::{Pred, CTL};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Strict {
    Strict,
    NonStrict,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Direction {
    Forward,
    Backward,
}

pub type Keepbinding = bool;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum GenericCtl<Pred: Display, Mvar, Anno> {
    False,
    True,
    Pred(Pred),
    Not(Box<GenericCtl<Pred, Mvar, Anno>>),
    Exists(Keepbinding, Mvar, Box<GenericCtl<Pred, Mvar, Anno>>),
    And(Strict, Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    AndAny(Direction, Strict, Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    HackForStmt(
        Direction,
        Strict,
        Box<GenericCtl<Pred, Mvar, Anno>>,
        Box<GenericCtl<Pred, Mvar, Anno>>,
    ),
    Or(Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    Implies(Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    AF(Direction, Strict, Box<GenericCtl<Pred, Mvar, Anno>>),
    AX(Direction, Strict, Box<GenericCtl<Pred, Mvar, Anno>>),
    AG(Direction, Strict, Box<GenericCtl<Pred, Mvar, Anno>>),
    AW(Direction, Strict, Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    AU(Direction, Strict, Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    EF(Direction, Box<GenericCtl<Pred, Mvar, Anno>>),
    EX(Direction, Box<GenericCtl<Pred, Mvar, Anno>>),
    EG(Direction, Box<GenericCtl<Pred, Mvar, Anno>>),
    EU(Direction, Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    Let(String, Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    LetR(Direction, String, Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    Ref(String),
    SeqOr(Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    Uncheck(Box<GenericCtl<Pred, Mvar, Anno>>),
    InnerAnd(Box<GenericCtl<Pred, Mvar, Anno>>),
    XX(Box<GenericCtl<Pred, Mvar, Anno>>, PhantomData<Anno>),
}

impl<Pred: Display + Clone, Mvar: Clone, Anno: Clone> GenericCtl<Pred, Mvar, Anno> {
    pub fn do_ctl(
        ctl0: &mut Box<GenericCtl<Pred, Mvar, Anno>>,
        f: &mut dyn FnMut(&mut GenericCtl<Pred, Mvar, Anno>),
    ) {
        match ctl0.as_mut() {
            GenericCtl::False => {}
            GenericCtl::True => {}
            GenericCtl::Pred(_) => f(ctl0),
            GenericCtl::Not(ctl) => Self::do_ctl(ctl, f),
            GenericCtl::Exists(_keep, _, ctl) => {
                Self::do_ctl(ctl, f);
            }
            GenericCtl::And(_, ctl, ctl1) => {
                Self::do_ctl(ctl, f);
                Self::do_ctl(ctl1, f);
            }
            GenericCtl::AndAny(_, _, ctl, ctl1) => {
                Self::do_ctl(ctl, f);
                Self::do_ctl(ctl1, f);
            }
            GenericCtl::HackForStmt(_, _, _, _) => todo!(),
            GenericCtl::Or(ctl, ctl1) => {
                Self::do_ctl(ctl, f);
                Self::do_ctl(ctl1, f);
            }
            GenericCtl::Implies(ctl, ctl1) => {
                Self::do_ctl(ctl, f);
                Self::do_ctl(ctl1, f);
            }
            GenericCtl::AF(_, _, ctl) => Self::do_ctl(ctl, f),
            GenericCtl::AX(_, _, ctl) => Self::do_ctl(ctl, f),
            GenericCtl::AG(_, _, ctl) => Self::do_ctl(ctl, f),
            GenericCtl::AW(_, _, ctl, ctl1) => {
                Self::do_ctl(ctl, f);
                Self::do_ctl(ctl1, f);
            }
            GenericCtl::AU(_, _, ctl, ctl1) => {
                Self::do_ctl(ctl, f);
                Self::do_ctl(ctl1, f);
            }
            GenericCtl::EF(_, ctl) => Self::do_ctl(ctl, f),
            GenericCtl::EX(_, ctl) => Self::do_ctl(ctl, f),
            GenericCtl::EG(_, ctl) => Self::do_ctl(ctl, f),
            GenericCtl::EU(_, ctl, ctl1) => {
                Self::do_ctl(ctl, f);
                Self::do_ctl(ctl1, f);
            }
            GenericCtl::Let(_, _, _) => todo!(),
            GenericCtl::LetR(_, _, _, _) => todo!(),
            GenericCtl::Ref(_) => todo!(),
            GenericCtl::SeqOr(_, _) => todo!(),
            GenericCtl::Uncheck(_) => todo!(),
            GenericCtl::InnerAnd(ctl) => Self::do_ctl(ctl, f),
            GenericCtl::XX(_, _) => todo!(),
        }
    }
}

impl<Pred: Display, Mvar: Display, Anno> Display for GenericCtl<Pred, Mvar, Anno> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn aux<Pred: Display, Mvar: Display, Anno>(
            f: &mut std::fmt::Formatter<'_>,
            ctl: &GenericCtl<Pred, Mvar, Anno>,
        ) -> std::fmt::Result {
            let verbose = true;
            return match ctl {
                GenericCtl::And(_, a, c) => match c.borrow() {
                    GenericCtl::AX(_, _, b) if !verbose => a.fmt(f).and(b.fmt(f)),
                    ctl => a.fmt(f).and(write!(f, " & (")).and(ctl.fmt(f)).and(write!(f, ")")),
                },
                GenericCtl::False => write!(f, "{}", "False"),
                GenericCtl::True => write!(f, "{}", "True"),
                GenericCtl::Pred(p) => write!(f, "{}", *p),
                GenericCtl::Not(ctl) => write!(f, "NOT (").and((*ctl).fmt(f)).and(write!(f, ")")),
                GenericCtl::Exists(keep, mvar, ctl) => {
                    if *keep { write!(f, "Ex ") } else { write!(f, "Exnk ") }
                        .and(write!(f, "{}", &format!("{} (", mvar)))
                        .and(ctl.fmt(f))
                        .and(write!(f, ")"))
                }
                GenericCtl::AndAny(_, _, _, _) => todo!(),
                GenericCtl::HackForStmt(_, _, _, _) => todo!(),
                GenericCtl::Or(c1, c2) => c1.fmt(f).and(write!(f, " OR ")).and(c2.fmt(f)),
                GenericCtl::Implies(_, _) => todo!(),
                GenericCtl::AF(_, _, ctl) => write!(f, "AF ").and(ctl.fmt(f)),
                GenericCtl::AX(_, _, ctl) => write!(f, "AX (").and(ctl.fmt(f)).and(write!(f, ")")),
                GenericCtl::AG(_, _, ctl) => write!(f, "AG ").and(ctl.fmt(f)),
                GenericCtl::AW(_, _, _, _) => todo!(),
                GenericCtl::AU(_, _, c1, c2) => write!(f, "\nA[")
                    .and(c1.fmt(f))
                    .and(write!(f, " U "))
                    .and(c2.fmt(f))
                    .and(write!(f, "]")),
                GenericCtl::EF(_, ctl) => write!(f, "AF ").and(ctl.fmt(f)),
                GenericCtl::EX(_, ctl) => write!(f, "EX ").and(ctl.fmt(f)),
                GenericCtl::EG(_, ctl) => write!(f, "EG ").and(ctl.fmt(f)),
                GenericCtl::EU(_, c1, c2) => write!(f, "E[ ")
                    .and(c1.fmt(f))
                    .and(write!(f, " U "))
                    .and(c2.fmt(f))
                    .and(write!(f, "]")),
                GenericCtl::Let(_, _, _) => todo!(),
                GenericCtl::LetR(_, _, _, _) => todo!(),
                GenericCtl::Ref(_) => todo!(),
                GenericCtl::SeqOr(_, _) => todo!(),
                GenericCtl::Uncheck(_) => todo!(),
                GenericCtl::InnerAnd(_) => todo!(),
                GenericCtl::XX(_, _) => todo!(),
            };
        }
        aux(f, self)
    }
}

// impl Debug for GenericCtl<>

#[derive(Clone, PartialEq, Eq)]
pub enum GenericSubst<Mvar: Clone + Eq, Value: Clone + Eq> {
    Subst(Mvar, Value),
    NegSubst(Mvar, Value),
}

impl<Mvar: Clone + Eq, Val: Clone + Eq> GenericSubst<Mvar, Val> {
    pub fn neg(&self) -> GenericSubst<Mvar, Val> {
        match self.clone() {
            GenericSubst::Subst(a, b) => GenericSubst::NegSubst(a, b),
            GenericSubst::NegSubst(a, b) => GenericSubst::Subst(a, b),
        }
    }

    pub fn into_neg(self) -> GenericSubst<Mvar, Val> {
        match self {
            GenericSubst::Subst(a, b) => GenericSubst::NegSubst(a, b),
            GenericSubst::NegSubst(a, b) => GenericSubst::Subst(a, b),
        }
    }
}

impl<Mvar: Clone + Ord, Val: Clone + Eq> PartialOrd for GenericSubst<Mvar, Val> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (GenericSubst::Subst(mvar1, _val1), GenericSubst::Subst(mvar2, _val2))
            | (GenericSubst::Subst(mvar1, _val1), GenericSubst::NegSubst(mvar2, _val2))
            | (GenericSubst::NegSubst(mvar1, _val1), GenericSubst::Subst(mvar2, _val2))
            | (GenericSubst::NegSubst(mvar1, _val1), GenericSubst::NegSubst(mvar2, _val2)) => {
                mvar1.partial_cmp(mvar2)
            }
        }
    }
}

impl<Mvar: Clone + Ord, Val: Clone + Eq> Ord for GenericSubst<Mvar, Val> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (GenericSubst::Subst(mvar1, _val1), GenericSubst::Subst(mvar2, _val2))
            | (GenericSubst::Subst(mvar1, _val1), GenericSubst::NegSubst(mvar2, _val2))
            | (GenericSubst::NegSubst(mvar1, _val1), GenericSubst::Subst(mvar2, _val2))
            | (GenericSubst::NegSubst(mvar1, _val1), GenericSubst::NegSubst(mvar2, _val2)) => {
                mvar1.cmp(mvar2)
            }
        }
    }
}

impl<Mvar: Clone + Ord + Display, Val: Clone + Eq + Debug> Debug for GenericSubst<Mvar, Val> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Subst(arg0, arg1) => write!(f, "{} -> {:?}", arg0, arg1),
            Self::NegSubst(arg0, arg1) => write!(f, "{} -/> {:?}", arg0, arg1),
        }
    }
}

#[derive(PartialEq, Eq, Clone)]
pub enum GenericWitnessTree<State: Eq + Clone, Subst: Eq + Clone + Ord, Anno: Eq + Clone> {
    Wit(State, Subst, Anno, Vec<GenericWitnessTree<State, Subst, Anno>>),
    NegWit(Box<GenericWitnessTree<State, Subst, Anno>>),
}

impl<A: Eq + Clone, B: Eq + Clone + Ord, C: Eq + Clone> GenericWitnessTree<A, B, C> {
    pub fn neg(&self) -> GenericWitnessTree<A, B, C> {
        GenericWitnessTree::NegWit(Box::new(self.clone()))
    }

    pub fn into_neg(self) -> GenericWitnessTree<A, B, C> {
        GenericWitnessTree::NegWit(Box::new(self))
    }

    pub fn subs(&self) -> B {
        match self {
            GenericWitnessTree::Wit(_, subs, _, _) => subs.clone(),
            GenericWitnessTree::NegWit(w) => w.subs(),
        }
    }
}

impl<State: Eq + Clone, Subst: Eq + Clone + Ord, Anno: Eq + Clone> PartialOrd
    for GenericWitnessTree<State, Subst, Anno>
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (GenericWitnessTree::Wit(_, sub1, _, _), GenericWitnessTree::Wit(_, sub2, _, _)) => {
                sub1.partial_cmp(sub2)
            }
            (wit1, GenericWitnessTree::NegWit(wit2)) => wit1.partial_cmp(&wit2),
            (GenericWitnessTree::NegWit(wit1), wit2) => (**wit1).partial_cmp(wit2),
            // (GenericWitnessTree::NegWit(wit1), GenericWitnessTree::NegWit(wit2)) => {
            //     wit1.partial_cmp(wit2)
            // }
        }
    }
}

impl<State: Eq + Clone, Subst: Eq + Clone + Ord, Anno: Eq + Clone> Ord
    for GenericWitnessTree<State, Subst, Anno>
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (GenericWitnessTree::Wit(_, sub1, _, _), GenericWitnessTree::Wit(_, sub2, _, _)) => {
                sub1.cmp(sub2)
            }
            (wit1, GenericWitnessTree::NegWit(wit2)) => wit1.cmp(&wit2),
            (GenericWitnessTree::NegWit(wit1), wit2) => (**wit1).cmp(wit2),
            // (GenericWitnessTree::NegWit(wit1), GenericWitnessTree::NegWit(wit2)) => wit1.cmp(wit2),
        }
    }
}

impl<G: Eq + Clone + Debug, S: Eq + Clone + Ord + Debug, P: Eq + Clone> Debug
    for GenericWitnessTree<G, S, P>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Wit(arg0, arg1, _arg2, arg3) => {
                write!(f, "{:?}, {:?}, {{{:?}}}", arg0, arg1, arg3)
            }
            Self::NegWit(arg0) => write!(f, "NOT({:?})", arg0),
        }
    }
}

pub type GenericWitnessTreeList<A, B, C> = Vec<GenericWitnessTree<A, B, C>>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Modif {
    Modif,
    Unmodif,
    Control,
}

impl Modif {
    pub fn ismodif(&self) -> bool {
        match self {
            Modif::Modif => true,
            Modif::Unmodif => false,
            Modif::Control => false,
        }
    }

    pub fn isunmodif(&self) -> bool {
        match self {
            Modif::Modif => false,
            Modif::Unmodif => true,
            Modif::Control => false,
        }
    }

    pub fn iscontrol(&self) -> bool {
        match self {
            Modif::Modif => false,
            Modif::Unmodif => false,
            Modif::Control => true,
        }
    }
}

impl Display for Modif {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Modif::Modif => write!(f, "modif"),
            Modif::Unmodif => Ok(()),
            Modif::Control => write!(f, "control"),
        }
    }
}

pub type GenericSubstList<Mvar, Value> = Vec<GenericSubst<Mvar, Value>>;

impl<Mvar: Clone + Eq, Value: Clone + Eq> GenericSubst<Mvar, Value> {
    pub fn mvar(&self) -> &Mvar {
        match self {
            GenericSubst::Subst(x, _) => x,
            GenericSubst::NegSubst(x, _) => x,
        }
    }
    pub fn value(&self) -> Value {
        match self {
            GenericSubst::Subst(_, x) => x.clone(),
            GenericSubst::NegSubst(_, x) => x.clone(),
        }
    }
}

// impl<Mvar: Display + Clone, Val: Display + Clone> Debug for GenericSubst<Mvar, Val> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             Self::Subst(arg0, arg1) => f.debug_tuple("Subst").field(arg0).field(arg1).finish(),
//             Self::NegSubst(arg0, arg1) => f.debug_tuple("NegSubst").field(arg0).field(arg1).finish(),
//         }
//     }
// }
