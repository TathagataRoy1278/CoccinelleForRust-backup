#![allow(unused)]

/*
(*
 * This file is part of Coccinelle, licensed under the terms of the GPL v2.
 * See copyright.txt in the Coccinelle source code for more information.
 * The Coccinelle source code can be obtained at http://coccinelle.lip6.fr
 *)

(* Issues:

1.  If a rule X depends on a rule Y (in a positive way), then we can ignore
    the constants in X.

2.  If a rule X contains a metavariable that is not under a disjunction and
    that is inherited from rule Y, then we can ignore the constants in X.

3.  If a rule contains a constant x in + code then subsequent rules that
    have it in - or context should not include it in their list of required
    constants.
*)

(* This doesn't do the . -> trick of get_constants for record fields, as
    that does not fit well with the recursive structure.  It was not clear
    that that was completely safe either, although eg putting a newline
    after the . or -> is probably unusual. *)
*/

use regex::Regex;
use std::collections::BTreeSet;
use std::collections::HashMap;
use super::parse_cocci::Rule;
use crate::parsing_cocci::ast0::Snode;
use crate::parsing_cocci::ast0::MetaVar;
use crate::commons::util::worktree_pure;
use crate::{syntaxerror,commons};
use parser::SyntaxKind;

type Tag = SyntaxKind;

// --------------------------------------------------------------------
// String management

struct SeparatedList<'a, Iterable, Item: std::fmt::Display>
where &'a Iterable: std::iter::IntoIterator<Item=Item>
{
    sep: &'a str,
    iterable: &'a Iterable,
}

impl<'a, Iterable, Item: std::fmt::Display> std::fmt::Display
    for SeparatedList<'a, Iterable, Item>
where &'a Iterable: std::iter::IntoIterator<Item=Item>
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
	let mut iter = self.iterable.into_iter();
	if let Some(first) = iter.next() {
	    first.fmt(f);
	    for item in iter {
		self.sep.fmt(f);
		item.fmt(f);
	    }
	}
	Ok(())
    }
}

fn separated_list<'a, Iterable, Item: std::fmt::Display>(
    sep: &'a str, iterable: &'a Iterable) -> SeparatedList<'a, Iterable, Item>
where &'a Iterable: std::iter::IntoIterator<Item=Item>
{
    SeparatedList { sep, iterable }
}

// --------------------------------------------------------------------
// Basic data type

// True means nothing was found
// False should never reach the top, it is the neutral element of or
// and an or is never empty

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Combine<'a> {
    True,
    False,
    Elem(&'a str),
    And(Box<BTreeSet<Combine<'a>>>),
    Or(Box<BTreeSet<Combine<'a>>>),
    Not(Box<Combine<'a>>),
}
use Combine::*;

// an iterator for Combine
pub struct CombineIterator<'c, 's> {
    stack: Vec<&'c Combine<'s>>
}

impl<'c, 's> Iterator for CombineIterator<'c, 's> {
    type Item = &'c Combine<'s>;

    fn next(&mut self) -> Option<Self::Item> {
	let result = self.stack.pop();
	if let Some(item) = result {
	    match item {
		And(l) | Or(l) => self.stack.extend(l.iter()),
		Not(e) => self.stack.push(e),
		_ => ()
	    }
	}
	result
    }
}

impl<'c, 's> IntoIterator for &'c Combine<'s> {
    type Item = &'c Combine<'s>;
    type IntoIter = CombineIterator<'c, 's>;

    fn into_iter(self) -> Self::IntoIter {
	CombineIterator { stack: Vec::from([self]) }
    }
}

impl<'a> std::fmt::Display for Combine<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
	match self {
            And(l) => write!(f, "({})", separated_list(" & ", &**l)),
            Or(l) => write!(f, "({})", separated_list(" | ", &**l)),
            Not(x) => write!(f, "!({})", x),
            Elem(x) => x.fmt(f),
            False => write!(f, "false"),
            True => write!(f, "true")
	}
    }
}

// --------------------------------------------------------------------
// various constants

static FALSE_ON_TOP_ERR: &str =
    "No rules apply.  Perhaps your semantic patch doesn't contain any +/-/* code, or you have a failed dependency.";

// --------------------------------------------------------------------
// Case for grep.  In this case, we don't care about the difference between
// and and or, and we don't support not, so we can just iterate over the
// tree, and collect the leaves.

type Clause<'a> = BTreeSet<&'a str>;
type CNF<'a> = BTreeSet<Clause<'a>>;

fn interpret_grep<'a>(strict: bool, x: &Combine<'a>) -> Option<Clause<'a>> {
    if let True = x {
        return None;
    };
    let mut collected = BTreeSet::new();
    for cmb in x {
        match cmb {
            Elem(x) => { collected.insert(*x); }
            Not(_) => syntaxerror!(0, "Not unexpected in grep arg"),
            And(_) | Or(_) => (),
            True =>
                if strict {
                    syntaxerror!(0, "True should not be in the final result")
                }
                else {
                    collected.insert("True");
                },
            False =>
                if strict {
                    syntaxerror!(0, FALSE_ON_TOP_ERR)
                }
                else {
                    collected.insert("False");
                }
        }
    }
    Some(collected)
}

// -------------------------------------------------------------------------
// interpretation for use with git grep

// convert to cnf, give up if the result is too complex
static MAX_CNF: usize = 5;

fn mk_false<'a>() -> CNF<'a> {
    BTreeSet::from([BTreeSet::new()])
}

fn big_and<'a, I: IntoIterator<Item=Clause<'a>>>(iter: I) -> CNF<'a> {
    let mut res = BTreeSet::new();
    for x in iter {
        if !(res.iter().any(|y| x.is_subset(y))) {
            res.insert(x);
        }
    }
    res
}

fn cnf<'a> (strict:bool, dep: &Combine<'a>) -> Result<CNF<'a>,()> {
    match dep {
        Elem(x) => Ok(BTreeSet::from([BTreeSet::from([*x])])),
        Not(_) => syntaxerror!(0, "not unexpected in coccigrep arg"),
        And(l) => {
            if l.is_empty() {
                syntaxerror!(0, "and should not be empty")
            }
            let l: Vec<CNF<'a>> =
                l.iter().map(|x| cnf(strict, x)).collect::<Result<_,_>>()?;
            Ok(big_and(l.into_iter().flatten()))
        }
        Or(l) => {
            if l.is_empty() {
                syntaxerror!(0, "or should not be empty")
            }
            let l: Vec<CNF<'a>> =
                l.iter().map(|x| cnf(strict, x)).collect::<Result<_,_>>()?;
            let icount =
                l.iter().filter(|x| x.len() > 1).take(MAX_CNF + 1).count();
            if icount > MAX_CNF {
                return Err(())
            }
            Ok(l.into_iter().reduce(|acc, cur| {
                big_and(cur.iter().flat_map(|x| {
                    acc.iter().map(|y| {
                        x.union(&y).cloned().collect()
                    })
                }))
            }).unwrap_or_else(mk_false))
        }
        True => Ok(BTreeSet::new()),
        False => {
            if strict {
                syntaxerror!(0, FALSE_ON_TOP_ERR)
            }
            else {
                Ok(mk_false())
            }
        }
    }
}

fn optimize<'a> (l : CNF<'a>) -> CNF<'a> {
    let mut l: Vec<_> = l.into_iter().map(|x| (x.len(), x)).collect();
    l.sort();
    l.reverse();
    big_and(l.into_iter().map(|(_,x)| x))
}

fn atoms<'a>(dep: &Combine<'a>) -> BTreeSet<&'a str> {
    let mut acc = BTreeSet::<&'a str>::new();
    for dep in dep {
        match dep {
            Elem(x) => { acc.insert(x); }
            And(_) | Or(_) | True | False => (),
            Not(x) => syntaxerror!(0, "Not unexpected in atoms")
        }
    }
    acc
}

// ------------------------------------------

fn count_atoms<'a>(l: &CNF<'a>) -> Vec<(&'a str,u32)> {
    let mut tbl = HashMap::new();
    // collect counts
    for &x in l.into_iter().flatten() {
        tbl.entry(x).and_modify(|counter| *counter += 1).or_insert(1);
    };
    // convert to a vector (element, count)
    let mut res : Vec<(&'a str,u32)> = tbl.into_iter().collect();
    // sort by counts
    res.sort_by_key(|(_,ct)| *ct); // why does * eliminate a lifetime error?
    res
}

fn extend<'a>(element : &'a str, res : &mut Clause<'a>, available : &mut CNF<'a>) {
    let mut added : Clause<'a> = BTreeSet::new();
    available
        .retain(|l| !(l.contains(element)) || { l.iter().for_each(|x| { added.insert(x); }); false });
    available.retain(|l| !(l.is_subset(&added)));
    res.extend(added);
}

fn leftres_rightres<'a>(tbl : &mut dyn DoubleEndedIterator<Item = &'a str>,
                        available : &mut CNF<'a>) -> (Clause<'a>,Clause<'a>) {
    let mut leftres : Clause<'a> = BTreeSet::new();
    let mut rightres : Clause<'a> = BTreeSet::new();
    while let (false,Some(f)) = (available.is_empty(),tbl.next()) {
        match tbl.next_back() {
            Some(b) => {
                extend(f, &mut leftres, available);
                extend(b, &mut rightres, available);
            }
            None => { // in the middle
                leftres.extend(available.iter().flatten());
            }
        }
    }
    (leftres,rightres)
}

fn split<'a>(l : &CNF<'a>) -> CNF<'a> {
    let mut tbl = count_atoms(l);
    let mut available = l.clone();
    // run extend
    let mut preres : CNF<'a> = CNF::new();
    tbl.retain(|&(f,ct)| ct > 1 || {
        let mut res = BTreeSet::new();
        extend(f, &mut res, &mut available);
        if !(res.is_empty()) {
            preres.insert(res);
        };
        false
    } );
    // make indices explicit in tbl
    let mut ltbl = tbl.into_iter().map(|(x,_)| x); // map to make it double ended
    let (leftres,rightres) = leftres_rightres(&mut ltbl,&mut available);
    if !leftres.is_empty() { preres.insert(leftres); }
    if !rightres.is_empty() { preres.insert(rightres); }
    preres
}

// ------------------------------------------

fn wordify<'a>(x: &'a &str) -> String {
    format!("\\b{}\\b", x.to_string())
}

fn orify<'a>(l: &BTreeSet<&'a str>) -> Regex {
    let list: Vec<String> = l.iter().map(wordify).collect();
    let str = format!("{}", separated_list(" \\| ", &list));
    Regex::new(str.as_str()).unwrap()
}

fn interpret_cocci_git_grep<'a> (strict: bool, x: &Combine<'a>) ->
    Option<(Regex, Vec<Regex>, Vec<String>)> {
    match x {
        True => None,
        False if strict => syntaxerror!(0, FALSE_ON_TOP_ERR),
        _ => { // allow use of ?
              (|| {
                let res1: Regex = orify(&atoms(x)); // all atoms
                let res = cnf(strict, x)?;
                let res = optimize(res);
                let res = split(&res);
                let res2: Vec<Regex> = res.iter().map(orify).collect(); // atoms in conjunction
                let res3: Vec<String> =
                    res.iter().map(|x| {
                                   let x : Vec<String> =
                                       x.iter().map(|x| x.to_string()).collect();
                                   format!("\\( -e {} \\)", separated_list(" -e ", &x)) }).collect();
                Ok::<(regex::Regex, Vec<regex::Regex>, Vec<std::string::String>), ()>((res1,res2,res3))
             })().ok()
        }
    }
}

// -------------------------------------------------------------------------

fn interpret_idutils<'a>(dep: Combine<'a>) -> Option<Combine<'a>> {
    match dep {
        True => None,
        x => Some(x)
    }
}

// -------------------------------------------------------------------------

fn build_and<'a>(x: &Combine<'a>, y: &Combine<'a>) -> Combine<'a> {
    if x == y {
        x.clone()
    }
    else {
        match (x,y) {
            (True,x) | (x,True) => x.clone(),
            (False,_x) | (_x,False) => False,
            (And(l1),And(l2)) => And(Box::new(l1.union(&*l2).cloned().collect())),
            (x,Or(l)) if l.contains(&x) => x.clone(),
            (Or(l),x) if l.contains(&x) => x.clone(),
            (Or(l1),Or(l2)) if l1.intersection(&*l2).count() > 0 => {
                let a1 = l1.difference(&l2).fold(False, |acc,a| build_or(&acc,a));
                let a2 = l2.difference(&*l1).fold(False, |acc,a| build_or(&acc,a));
                let inner = build_and(&a1,&a2);
                l1.intersection(&*l2).fold(inner, |acc,a| build_or(&acc,&a))
            }
            (x,And(l)) | (And(l),x) => {
                if l.contains(x) {
                    And(l.clone())
                }
                else {
                    let mut others: BTreeSet<Combine<'a>> =
                        l.iter().filter(|y| {if let Or(l1) = y { !l1.contains(x) } else { true }}).cloned().collect();
                    others.insert(x.clone());
                    And(Box::new(others))
                }
            }
            (x,y) => And(Box::new(BTreeSet::from([x.clone(),y.clone()])))
        }
    }
}

fn build_or<'a>(x: &Combine<'a>, y: &Combine<'a>) -> Combine<'a> {
    if x == y {
        x.clone()
    }
    else {
        match (x,y) {
            (True,_x) | (_x,True) => True,
            (False,x) | (x,False) => x.clone(),
            (Or(l1),Or(l2)) => Or(Box::new(l1.union(&*l2).cloned().collect())),
            (x,And(l)) if l.contains(&x) => x.clone(),
            (And(l),x) if l.contains(&x) => x.clone(),
            (And(l1),And(l2)) if !(l1.intersection(&*l2).count() == 0) => {
                let a1 = l1.difference(&l2).fold(True, |acc,a| build_and(&acc,a));
                let a2 = l2.difference(&*l1).fold(True, |acc,a| build_and(&acc,a));
                let inner = build_or(&a1,&a2);
                l1.intersection(&*l2).cloned().fold(inner, |acc,a| build_and(&acc,&a))
            }
            (x,Or(l)) | (Or(l),x) => {
                if l.contains(&x) {
                    Or(l.clone())
                }
                else {
                    let mut others: BTreeSet<Combine<'a>> =
                        l.iter().filter(|y| {if let And(l) = y { !l.contains(&x) } else { true }}).cloned().collect();
                    others.insert(x.clone());
                    Or(Box::new(others))
                }
            }
            (x,y) => Or(Box::new(BTreeSet::from([x.clone(),y.clone()])))
        }
    }
}

fn find_constants<'a>(rule: &'a Rule, env: HashMap<&str, &Combine<'a>>) -> Combine<'a> {
    let mut res = True;
    let mut work = |node: &'a Snode| {
        if node.astnode.kind() == Tag::PATH_EXPR {
            if node.wrapper.metavar == MetaVar::NoMeta {
                if let Some(comb) = env.get(&*(rule.name)) { // want str for name
                    res = build_and(comb,&res);
                }
                else {
                    res = False;
                }
            }
            else {
	        res = build_and(&res,&Elem(node.astnode.as_token().unwrap().text()));
            }
        }
    };
    worktree_pure(&rule.patch.minus, &mut work);
    res
}
