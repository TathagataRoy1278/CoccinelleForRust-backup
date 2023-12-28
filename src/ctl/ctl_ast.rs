use std::{marker::PhantomData, rc::Rc};

use crate::parsing_cocci::ast0::KeepBinding;

pub enum Strict {
    Strict,
    NonStrict,
}

pub enum Direction {
    Forward,
    Backward,
}

pub type Keepbinding = bool;

pub enum GenericCtl<Pred, Mvar, Anno> {
    False,
    Trye,
    Pred(Pred),
    Not(Box<GenericCtl<Pred, Mvar, Anno>>),
    Exists(KeepBinding, Mvar, Box<GenericCtl<Pred, Mvar, Anno>>),
    And(Strict, (Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>)),
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
    LetR(Direction, String, Box<GenericCtl<Pred, Mvar, Anno>>),
    Ref(String),
    SeqOr(Box<GenericCtl<Pred, Mvar, Anno>>, Box<GenericCtl<Pred, Mvar, Anno>>),
    Uncheck(Box<GenericCtl<Pred, Mvar, Anno>>),
    InnerAnd(Box<GenericCtl<Pred, Mvar, Anno>>),
    XX(Box<GenericCtl<Pred, Mvar, Anno>>, PhantomData<Anno>),
}

#[derive(Clone)]
pub enum GenericSubst<Mvar: Clone, Value: Clone> {
    Subst(Mvar, Value),
    NegSubst(Mvar, Value),
}

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum GenericWitnessTree<State, Subst, Anno> {
    Wit(State, Subst, Anno, Vec<GenericWitnessTree<State, Subst, Anno>>),
    NegWit(Box<GenericWitnessTree<State, Subst, Anno>>),
}

pub type GenericWitnessTreeList<A, B, C> = Vec<GenericWitnessTree<A, B, C>>;

enum Modif<T> {
    Modif(T),
    Unmodif(T),
    Control,
}
pub trait GenericSubstitution {
    type Mvar;
    type Value;

    fn eq_mvar(a: Self::Mvar, b: Self::Mvar) -> bool;
    fn eq_val(a: Self::Value, b: Self::Value) -> bool;
    fn merge_val(a: Self::Value, b: Self::Value) -> bool;
    fn print_mvar(&self, b: Self) -> bool;
    fn print_value(&self, b: Self) -> bool;
}

pub type GenericSubstList<Mvar, Value: Clone> = Vec<GenericSubst<Mvar, Value>>;

impl<Mvar: Clone, Value: Clone> GenericSubst<Mvar, Value> {
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