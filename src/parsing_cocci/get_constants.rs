// SPDX-License-Identifier: GPL-2.0

/*
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
use std::collections::HashSet;
use super::parse_cocci::Rule;
use super::parse_cocci::Dep;
use crate::parsing_cocci::ast0::Snode;
use crate::parsing_cocci::ast0::MetaVar;
use crate::parsing_cocci::ast0::Mcodekind;
use crate::parsing_cocci::cocci_grep;
use crate::commons::util::worktree_pure;
use crate::syntaxerror;
use ra_parser::SyntaxKind;
use std::process::{Command, Stdio};
use crate::interface::interface::CoccinelleForRust;

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
	    first.fmt(f)?;
	    for item in iter {
		self.sep.fmt(f)?;
		item.fmt(f)?;
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

fn interpret_grep<'a>(strict: bool, x: &Combine<'a>) -> Option<Vec<String>> {
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
    Some(collected.iter().map(|x| x.to_string()).collect())
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
    let mut l: Vec<_> = l.into_iter().collect();
    l.sort_by_key(|x| x.len());
    l.reverse();
    big_and(l)
}

fn atoms<'a>(dep: &Combine<'a>) -> BTreeSet<&'a str> {
    let mut acc = BTreeSet::new();
    for dep in dep {
        match dep {
            Elem(x) => { acc.insert(*x); }
            And(_) | Or(_) | True | False => (),
            Not(_) => syntaxerror!(0, "Not unexpected in atoms")
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

fn split<'a>(mut available : CNF<'a>) -> CNF<'a> {
    let mut tbl = count_atoms(&available);
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
                let res = split(res);
                let res2: Vec<Regex> = res.iter().map(orify).collect(); // atoms in conjunction
                let res3: Vec<String> =
                    res.iter().map(|x| {
                                   format!("\\( -e {} \\)", separated_list(" -e ", x)) }).collect();
                Ok::<(regex::Regex, Vec<regex::Regex>, Vec<std::string::String>), ()>((res1,res2,res3))
             })().ok()
        }
    }
}

// -------------------------------------------------------------------------
/*
fn interpret_idutils<'a>(dep: Combine<'a>) -> Option<Combine<'a>> {
    match dep {
        True => None,
        x => Some(x)
    }
}
*/
// -------------------------------------------------------------------------

fn build_and_nested<'a>(l: BTreeSet<Combine<'a>>, x: Combine<'a>) -> Combine<'a> {
    let mut others: BTreeSet<Combine<'a>> =
        l.into_iter().filter(|y| {
	    if let Or(l) = y {
		!l.contains(&x)
	    }
	    else {
		true
	    }
	}).collect();
    others.insert(x);
    And(Box::new(others))
}

fn build_and<'a>(x: Combine<'a>, y: &Combine<'a>) -> Combine<'a> {
    if x == *y {
        x
    }
    else {
        match (x,y) {
            (x,True) => x,
            (True,x) => x.clone(),
            (False,_) | (_,False) => False,
            (And(l1),And(l2)) => And(Box::new(l1.union(l2).cloned().collect())),
            (x,Or(l)) if l.contains(&x) => x,
            (Or(l),x) if l.contains(&x) => x.clone(),
            (Or(l1),Or(l2)) if l1.intersection(l2).count() > 0 => {
                let a1 = l1.difference(l2).fold(False, build_or);
                let a2 = l2.difference(&l1).fold(False, build_or);
                let inner = build_and(a1,&a2);
                l1.intersection(l2).fold(inner, build_or)
            }
            (x,And(l)) => {
                if l.contains(&x) {
                    And(l.clone())
                }
                else {
                    build_and_nested((**l).clone(), x)
                }
            }
            (And(l),x) => {
                if l.contains(x) {
                    And(l)
                }
                else {
                    build_and_nested(*l, x.clone())
                }
            }
            (x,y) => And(Box::new(BTreeSet::from([x,y.clone()])))
        }
    }
}

fn build_or_nested<'a>(l: BTreeSet<Combine<'a>>, x: Combine<'a>) -> Combine<'a> {
    let mut others: BTreeSet<Combine<'a>> =
        l.into_iter().filter(|y| {
	    if let And(l) = y {
		!l.contains(&x)
	    }
	    else {
		true
	    }
	}).collect();
    others.insert(x);
    Or(Box::new(others))
}

fn build_or<'a>(x: Combine<'a>, y: &Combine<'a>) -> Combine<'a> {
    if x == *y {
        x
    }
    else {
        match (x,y) {
            (True,_) | (_,True) => True,
            (x,False) => x,
            (False,x) => x.clone(),
            (Or(l1),Or(l2)) => Or(Box::new(l1.union(l2).cloned().collect())),
            (x,And(l)) if l.contains(&x) => x,
            (And(l),x) if l.contains(&x) => x.clone(),
            (And(l1),And(l2)) if !(l1.intersection(l2).count() == 0) => {
                let a1 = l1.difference(l2).fold(True, build_and);
                let a2 = l2.difference(&l1).fold(True, build_and);
                let inner = build_or(a1,&a2);
                l1.intersection(&*l2).fold(inner, build_and)
            }
            (x,Or(l)) => {
                if l.contains(&x) {
                    Or(l.clone())
                }
                else {
                    build_or_nested((**l).clone(), x)
                }
            }
            (Or(l),x) => {
                if l.contains(x) {
                    Or(l)
                }
                else {
                    build_or_nested(*l, x.clone())
                }
            }
            (x,y) => Or(Box::new(BTreeSet::from([x, y.clone()])))
        }
    }
}

fn do_get_constants<'a>(node: &'a Snode, kwds: bool, env: &HashMap<&str, Combine<'a>>) -> Combine<'a> {
    if kwds && node.is_keyword() {
        Elem(node.totokenrec())
    }
    else if node.kinds().contains(&Tag::PATH_EXPR) {
        if node.wrapper.metavar != MetaVar::NoMeta {
            if let Some(comb) = env.get(node.wrapper.metavar.getrulename()) {
                comb.clone()
            }
            else {
                False
            }
        }
        else if !kwds {
            Elem(node.totokenrec())
        }
        else {
            True
        }
    }
    else if node.wrapper.isdisj {
        node.children.iter()
            .fold(False,
                  |acc, child: &'a Snode|
                  build_or(acc, &do_get_constants(child, kwds, env)))
    }
    else {
        node.children.iter()
            .fold(False,
                  |acc, child: &'a Snode|
                  build_and(acc, &do_get_constants(child, kwds, env)))
    }
}

fn find_constants<'a>(rule: &'a Rule, kwds: bool, env: &HashMap<&str, Combine<'a>>) -> Combine<'a> {
    do_get_constants(&rule.patch.minus, kwds, env)
}

// it would be nice if one could just abort when False
// is reached
fn all_context<'a>(rule: &'a Rule) -> bool {
    let mut res = true;
    let mut work = |node: &'a Snode| {
        match &node.wrapper.mcodekind {
            Mcodekind::Context(bef,aft) => {
                if bef.len() > 0 || aft.len() > 0 {
                    res = false
                }
            }
            _ => { res = false }
        }
    };
    worktree_pure(&rule.patch.minus, &mut work);
    res
}

fn rule_fn<'a>(rule: &'a Rule, env: &HashMap<&str, Combine<'a>>) -> Combine<'a> {
    let minuses = find_constants(rule, false, env);
    match minuses {
        True => find_constants(rule, true, env),
        x => x
    }
}

fn dependencies<'a>(env: &HashMap<&str, Combine<'a>>, dep: &Dep) -> Combine<'a> {
    match dep {
        Dep::NoDep => True,
        Dep::FailDep => False,
        Dep::Dep(nm) => { // maybe nm could be a str up front?
            if let Some(comb) = env.get(&nm.as_str()) {
                comb.clone()
            }
            else {
                False
            }
        }
        Dep::AndDep(args) => build_and(dependencies(env, &args.0), &dependencies(env, &args.1)),
        Dep::OrDep(args)  => build_or(dependencies(env, &args.0), &dependencies(env, &args.1)),
        Dep::AntiDep(_)   => True
    }
}

fn run<'a>(rules: &'a Vec<Rule>) -> Combine<'a> {
    let mut env = HashMap::new();
    let mut res = False;
    for r in rules.iter() {
        match dependencies(&env, &r.dependson) {
            False => {}
            dependencies => {
                    env.insert(&r.name,True);
                    let cur_info = rule_fn(&r, &env);
                    let re_cur_info = build_and(dependencies, &cur_info);
                    if all_context(r) {
                        env.entry(&r.name).and_modify(|i| *i = re_cur_info);
                    }
                    else {
                        res = build_or(re_cur_info,&res);
                        env.entry(&r.name).and_modify(|i| *i = cur_info);
                }
            }
        }
    }
    res
}

// -------------------------------

#[derive(clap::ValueEnum, Clone, Debug, PartialEq)]
pub enum Scanner {
   NoScanner,
   Grep,
   GitGrep,
   CocciGrep,
}

fn get_files(dir: &String) -> Vec<String> {
    let msg = format!("{} unknown or not a directory", dir);
    let output = Command::new("find").arg(dir).args(["-type", "f", "-name", "\"*rs\""])
        .stdout(Stdio::piped())
        .output()
        .expect(&msg.as_str());
    String::from_utf8(output.stdout).expect(&msg).lines().map(|x| x.to_string()).collect()
}

fn call_grep(files: Vec<String>, query: Vec<String>) -> Vec<String> {
    let full = Regex::new(r"^[A-Za-z_][A-Za-z_0-9]*$").unwrap();
    let start = Regex::new(r"^[A-Za-z_]").unwrap();
    let finish = Regex::new(r".*[A-Za-z_]$").unwrap();
    let query : Vec<_> = query.iter().map(|x| {
                  if full.is_match_at(x, 0) {
                      format!("{}{}{}", r"\b", x, r"\b")
                  }
                  else if start.is_match_at(x, 0) {
                      format!("{}{}", r"\b", x)
                  }
                  else if finish.is_match_at(x, 0) {
                      format!("{}{}", x, r"\b")
                  }
                  else {
                      x.to_string()
                  }
              }).collect();
    let query = format!("'({})'", separated_list(" | ", &query));
    files.into_iter().filter(|fl| {
        if let Ok(_) = Command::new("egrep").args(["-q", &query, &fl]).output() {
            true
        }
        else {
            false
        }
    }).collect()
}

fn call_git_grep(dir: &String, query: String) -> HashSet<String> {
    let o = Command::new("/bin/bash")
                .arg(format!("cd {}; git grep -l -w {} -- \"*.rs\"", dir, query))
                .output().expect(format!("{} unknown or not a directory", dir).as_str());
    if let Ok(lines) = String::from_utf8(o.stdout) {
        lines.lines().map(|x| x.to_string()).collect()
    }
    else {
        HashSet::new()
    }
}

pub fn do_get_files<'a>(cfr: &CoccinelleForRust, dir: &String, rules: &'a Vec<Rule>) -> Vec<String> {
    if cfr.worth_trying == Scanner::NoScanner {
        get_files(dir)
    }
    else {
        let res = run(rules);
        match cfr.worth_trying {
            Scanner::Grep => {
                let query = interpret_grep(true, &res);
                let files = get_files(dir);
                if let Some(query) = query {
                    call_grep(files, query)
                }
                else {
                    files
                }
            }
            Scanner::GitGrep => {
                let query = interpret_cocci_git_grep(true, &res);
                if let Some((_, _, query)) = query {
                    let mut file_matches: Vec<HashSet<String>> =
                        query.into_iter().map(|q| call_git_grep(&dir, q)).collect();
                    if let Some(mut e) = file_matches.pop() {
                        for x in file_matches {
                            e.retain(|v| x.contains(v));
                        }
                        e.into_iter().collect()
                    }
                    else {
                        get_files(dir)
                    }
                }
                else {
                    get_files(dir)
                }
            }
            Scanner::CocciGrep => {
                let query = interpret_cocci_git_grep(true, &res);
                let files = get_files(dir);
                if let Some((big_regexp, regexps, _)) = query {
                    files.into_iter().filter(|fl| cocci_grep::interpret(&big_regexp, &regexps, fl))
                         .collect()
                }
                else {
                    files
                }
            }
            _ => Vec::<_>::new() // not possible
        }
    }
}
