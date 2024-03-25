// SPDX-License-Identifier: GPL-2.0

// For each rule return the list of variables that are used after it.
// Also augment various parts of each rule with unitary, inherited, and freshness
// information
#![allow(dead_code)]
use ra_parser::SyntaxKind;
use std::collections::HashSet;
use std::vec;

use super::ast0::{KeepBinding, MetaVar, Snode};
use super::parse_cocci::Rule;
use crate::commons::util::worktree_pure;

type Tag = SyntaxKind;
type Name = String;

// ----------------------------------------------------------------
// Basic collection functions for a single rule.
//

fn collect_unitary_nonunitary(free_usage: &Vec<MetaVar>) -> (HashSet<MetaVar>, HashSet<MetaVar>) {
    let mut unitary: HashSet<MetaVar> = HashSet::new();
    let mut nonunitary: HashSet<MetaVar> = HashSet::new();
    for id in free_usage {
        match unitary.take(id) {
            Some(removed) => {
                nonunitary.insert(removed);
            }
            None => {
                if !nonunitary.contains(id) {
                    unitary.insert(id.clone());
                }
            }
        }
    }
    (unitary, nonunitary)
}

fn collect_refs(root: &Snode, add: &mut dyn FnMut(MetaVar)) {
    let mut work = |node: &Snode| {
        if node.kinds().contains(&Tag::NAME_REF) {
            match &node.wrapper.metavar {
                MetaVar::NoMeta => {}
                mv => add(mv.clone()),
            }
        }
    };
    worktree_pure(&root, &mut work)
}

fn collect_minus_refs_unitary_nonunitary(root: &mut Snode) -> (HashSet<MetaVar>, HashSet<MetaVar>) {
    let mut refs: Vec<MetaVar> = vec![];
    let mut add = |x| refs.push(x);
    collect_refs(root, &mut add);
    collect_unitary_nonunitary(&refs)
}

fn collect_plus_refs(mut root: &mut Snode) -> HashSet<MetaVar> {
    let mut refs: HashSet<MetaVar> = HashSet::new();
    let mut add = |x| {
        refs.insert(x);
    };
    let mut work_exp_list_list = |expss: &Vec<Snode>| {
        for x in expss.iter() {
            collect_refs(x, &mut add)
        }
    };
    let mut work = |node: &Snode| {
        let (lplusses, rplusses) = node.wrapper.mcodekind.getpluses();
        work_exp_list_list(&lplusses);
        work_exp_list_list(&rplusses);
    };
    worktree_pure(&mut root, &mut work);
    refs
}

// ----------------------------------------------------------------
// classify as unitary (no binding) or nonunitary (env binding) or saved
// (witness binding)

fn classify_rule_variables(rule: &mut Rule, used_after: &mut Vec<MetaVar>) {
    let curname = &rule.name;

    let (unitarynames, nonunitarynames) =
        collect_minus_refs_unitary_nonunitary(&mut rule.patch.minus);
    let inplus = collect_plus_refs(&mut rule.patch.minus);

    let mut saved: HashSet<MetaVar> = inplus.clone(); // Either this has to be cloned or
                                                      // !inplus.contains(&r) needs to be replaced b with !saved.contains(&r)
    let mut unitary: HashSet<MetaVar> = HashSet::new();
    let mut nonunitary: HashSet<MetaVar> = HashSet::new();

    // classify metavariables as saved, unitary, and nonunitary
    let mut check_nonunitary = |mut r: MetaVar| {
        if used_after.contains(&r) {
            saved.insert(r.clone());
            r.setbinding(KeepBinding::SAVED);
        } else {
            nonunitary.insert(r.clone());
            r.setbinding(KeepBinding::NONUNITARY);
        }
    };

    for mut r in unitarynames {
        if r.getrulename() == curname && !inplus.contains(&r) && !used_after.contains(&r) {
            unitary.insert(r.clone());
            r.setbinding(KeepBinding::UNITARY)
        } else {
            check_nonunitary(r);
        }
    }

    for r in nonunitarynames {
        check_nonunitary(r);
    }

    // collect the nonlocal and inherited variables
    let mut free_vars = unitary.clone();
    let mut inherited = vec![];

    let mut collect = |r: MetaVar| {
        if r.getrulename() == curname {
            free_vars.insert(r);
        } else {
            inherited.push(r);
        }
    };

    for r in saved.clone() {
        //cloning here because
        collect(r);
    }

    for r in nonunitary.clone() {
        //these are again collected below
        collect(r.clone());
    }

    // drop the local variables from used_after
    if let Some(index) = used_after.iter().position(|value| value.getrulename() == curname) {
        used_after.remove(index);
    }

    // add the nonlocal variables to used_after
    let mut collect = |r: MetaVar| {
        if r.getrulename() != curname {
            used_after.push(r);
        }
    };

    for r in saved {
        collect(r)
    }

    for r in nonunitary {
        collect(r)
    }
}

// ----------------------------------------------------------------
// ----------------------------------------------------------------
// entry point

pub fn free_vars(rules: &mut Vec<Rule>) {
    let mut used_after: Vec<MetaVar> = vec![];

    for rule in rules.iter_mut().rev() {
        classify_rule_variables(rule, &mut used_after);
    }
}
