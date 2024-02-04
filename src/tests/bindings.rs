#![allow(dead_code)]
use itertools::Itertools;
use std::fs;

use crate::{
    commons::util::getstmtlist,
    engine::{
        cocci_vs_rs::{Looper, MetavarBinding, visitrnode_tmp},
        disjunctions::{getdisjunctions, Disjunction},
    },
    parsing_cocci::{ast0::Snode, parse_cocci::processcocci},
    parsing_rs::{ast_rs::Rnode, parse_rs::processrs_old},
};
fn tokenf<'a>(_node1: &'a Snode, _node2: &'a Rnode) -> Vec<MetavarBinding> {
    // this is
    // Tout will have the generic types in itself
    // ie ('a * 'b) tout //Ocaml syntax
    // Should I replace Snode and Rnode with generic types?
    // transformation.ml's tokenf
    // info_to_fixpos
    vec![]
}

static PREFIX: &str = "./src/tests";
fn checkbindings(bindings1: Vec<Vec<MetavarBinding>>, bindings2: Vec<(&str, &str)>) -> usize {
    let mut ctr: usize = 0;
    'outer: for bindingvec1 in bindings1.clone() {
        if bindingvec1.len() != bindings2.len() {
            continue;
        }
        for binding2 in bindings2.clone() {
            for binding1 in bindingvec1.clone() {
                if binding2.0 == binding1.metavarinfo.varname {
                    if binding2.1 != binding1.rnode.getstring().trim() {
                        continue 'outer;
                    }
                }
            }
        }
        ctr += 1;
    }
    return ctr;
}

fn testfile(cocci: &str, rs: &str, gbindings: Vec<Vec<(&str, &str)>>) {
    let patchstring =
        fs::read_to_string(format!("{}/{}", PREFIX, cocci)).expect("This shouldnt be empty");
    let rustcode =
        fs::read_to_string(format!("{}/{}", PREFIX, rs)).expect("This shouldnt be empty");

    //let mut rules = processcocci(contents.as_str());
    //set_logilines(&mut rules);

    let (mut rules, _, _) = processcocci(&patchstring);
    let rnode = processrs_old(&rustcode).ok().unwrap();

    let looper = Looper::new(tokenf);
    let a: Disjunction =
        getdisjunctions(Disjunction(vec![getstmtlist(&mut rules[0].patch.minus).clone().children]));
    let envs = visitrnode_tmp(&a.0, &rnode, &|a, b| looper.handledisjunctions(a, b, vec![]));
    let gbindings1 = envs.into_iter().map(|x| x.bindings).collect_vec();
    let mut totalbindings: usize = 0;
    for binding1 in gbindings {
        totalbindings += checkbindings(gbindings1.clone(), binding1);
    }
    println!("{}", totalbindings);
    assert!(gbindings1.len() == totalbindings)
}

#[test]
pub fn test1() {
    testfile("bindings/test1.cocci", "bindings/test1.rs", vec![vec![("e", "force")]]);
}

#[test]
pub fn test2() {
    testfile(
        "bindings/test2.cocci",
        "bindings/test2.rs",
        vec![vec![("e1", "a"), ("e2", "b")], vec![("e1", "1"), ("e2", "2")]],
    );
}

#[test]
pub fn test3() {
    testfile(
        "bindings/test3.cocci",
        "bindings/test3.rs",
        vec![vec![("e1", "f.func()"), ("e3", "23"), ("e2", "8")]],
    );
}

#[test]
pub fn test4() {
    testfile(
        "bindings/test4.cocci",
        "bindings/test4.rs",
        vec![vec![("e1", "f.func()"), ("e3", "23")]],
    );
}

#[test]
pub fn test5() {
    testfile(
        "bindings/test5.cocci",
        "bindings/test5.rs",
        vec![vec![("e1", "f.func()"), ("e3", "23"), ("i", "h"), ("e2", "8"), ("e4", "12")]],
    );
}

#[test]
pub fn test6() {
    testfile("bindings/test6.cocci", "bindings/test6.rs", vec![vec![("e2", "rigthhand")]]);
}

#[test]
pub fn test7() {
    testfile("bindings/test7.cocci", "bindings/test7.rs", vec![vec![("e2", "rigthhand")]]);
}

#[test]
pub fn test8() {
    testfile(
        "bindings/test8.cocci",
        "bindings/test8.rs",
        vec![vec![("e1", "f.func()"), ("e3", "23"), ("i", "h"), ("e2", "8")]],
    );
}

#[test]
pub fn test9() {
    testfile(
        "bindings/test9.cocci",
        "bindings/test9.rs",
        vec![vec![
            ("e1", "f.func()"),
            ("e3", "23"),
            ("i", "h"),
            ("e2", "8"),
            ("i1", "a"),
            ("i2", "b"),
            ("e4", "funccall()"),
        ]],
    );
}

#[test]
pub fn test10() {
    testfile(
        "bindings/test10.cocci",
        "bindings/test10.rs",
        vec![vec![
            ("e1", "f.func()"),
            ("e3", "23"),
            ("i", "h"),
            ("e2", "8"),
            ("i1", "(a, b)"),
            ("e4", "funccall()"),
        ]],
    );
}

#[test]
pub fn test11() {
    testfile("bindings/test11.cocci", "bindings/test11.rs", vec![vec![("x", "2"), ("y", "1")]]);
}
