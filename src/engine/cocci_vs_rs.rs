use std::rc::Rc;
use std::vec;

use itertools::Itertools;

use crate::{
    fail,
    parsing_cocci::ast0::Snode,
    parsing_cocci::ast0::{MetaVar, MetavarName, MODKIND},
    parsing_rs::ast_rs::Rnode,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MetavarBinding {
    pub metavarinfo: MetavarName,
    pub rnode: Rc<Rnode>,
}

impl<'a> MetavarBinding {
    fn new(rname: String, varname: String, rnode: Rnode) -> MetavarBinding {
        return MetavarBinding {
            metavarinfo: MetavarName { rulename: rname, varname: varname },
            rnode: Rc::new(rnode),
        };
    }
}

#[derive(Clone, Debug)]
pub struct Modifiers {
    pub minuses: Vec<(usize, usize)>,           //start, end
    pub pluses: Vec<(usize, bool, Vec<Snode>)>, //pos, isbefore?, actual plusses
}

#[derive(Clone, Debug)]
pub struct Environment {
    pub failed: bool,
    pub bindings: Vec<MetavarBinding>,
    pub modifiers: Modifiers,
}

impl<'a> Environment {
    pub fn add(&mut self, env: Self) {
        for binding in env.bindings {
            if !self.bindings.iter().any(|x| x.metavarinfo.varname == binding.metavarinfo.varname) {
                self.bindings.push(binding);
            }
        }
        //self.bindings.extend(env.bindings);
        self.modifiers.minuses.extend(env.modifiers.minuses);
        self.modifiers.pluses.extend(env.modifiers.pluses);
    }

    pub fn addbinding(&mut self, binding: MetavarBinding) {
        self.bindings.push(binding);
    }

    pub fn addbindings(&mut self, bindings: &Vec<&MetavarBinding>) {
        for &binding in bindings {
            self.bindings.push(binding.clone());
        }
    }

    pub fn new() -> Environment {
        Environment {
            failed: false,
            bindings: vec![],
            modifiers: Modifiers { minuses: vec![], pluses: vec![] },
        }
    }

    pub fn failed() -> Environment {
        Environment {
            failed: true,
            bindings: vec![],
            modifiers: Modifiers { minuses: vec![], pluses: vec![] },
        }
    }

    pub fn clonebindings(&self) -> Environment {
        Environment {
            failed: false,
            bindings: self.bindings.clone(),
            modifiers: Modifiers { minuses: vec![], pluses: vec![] },
        }
    }
}

enum MetavarMatch<'a, 'b> {
    Fail,
    Maybe(&'b Snode, &'a Rnode),
    Match,
    Exists,
}

fn addplustoenv(a: &Snode, b: &Rnode, env: &mut Environment) {
    if a.children.len() == 1 {
        addplustoenv(&a.children[0], b, env)
    } else {
        if a.wrapper.plusesbef.len() != 0 {
            env.modifiers.pluses.push((
                b.wrapper.info.charstart,
                true,
                a.wrapper.plusesbef.clone(),
            ));
        }
        if a.wrapper.plusesaft.len() != 0 {
            env.modifiers.pluses.push((b.wrapper.info.charend, false, a.wrapper.plusesaft.clone()));
        }
    }
}

pub struct Looper<'a> {
    _tokenf: fn(&'a Snode, &'a Rnode) -> Vec<MetavarBinding>,
}

impl<'a, 'b> Looper<'a> {
    pub fn new(_tokenf: fn(&'a Snode, &'a Rnode) -> Vec<MetavarBinding>) -> Looper<'a> {
        Looper { _tokenf }
    }

    //actual matching function. Takes two nodes and recursively matches them

    pub fn matchnodes(
        &self,
        nodevec1: &Vec<&Snode>,
        nodevec2: &Vec<&'a Rnode>,
        mut env: Environment,
    ) -> Environment {
        let mut nodevec1 = nodevec1.iter();
        let mut nodevec2 = nodevec2.iter();
        let mut a: &Snode;
        let mut b: &Rnode;

        loop {
            if let Some(ak) = nodevec1.next() {
                a = ak;
            } else {
                return env;
            }

            if let Some(bk) = nodevec2.next() {
                b = *bk;
            } else {
                //println!("fail");
                fail!();
            }

            let akind = a.kind();
            let bkind = b.kind();
            //println!("{:?} ===== {:?}", akind, bkind);//please dont remove this line
            //helps in debugging, and I always forget where to put it
            if akind != bkind && a.wrapper.metavar.isnotmeta() {
                //println!("fail");
                fail!()
            }
            match self.workon(a, b, &env.bindings) {
                MetavarMatch::Fail => {
                    fail!()
                }
                MetavarMatch::Maybe(a, b) => {
                    let renv = self.matchnodes(
                        &a.children.iter().collect_vec(),
                        &b.children.iter().collect_vec(),
                        env.clonebindings(),
                    );

                    if !renv.failed {
                        match a.wrapper.modkind {
                            Some(MODKIND::MINUS) | Some(MODKIND::STAR) => {
                                //env.modifiers.minuses.push(b.getpos());
                            }
                            _ => {}
                        }
                        addplustoenv(a, b, &mut env);

                        env.add(renv);
                    } else {
                        fail!()
                    }
                }
                MetavarMatch::Match => {
                    let minfo = a.wrapper.metavar.getminfo();
                    let binding = MetavarBinding::new(
                        minfo.0.rulename.to_string(),
                        minfo.0.varname.to_string(),
                        b.clone(),
                    );
                    match a.wrapper.modkind {
                        Some(MODKIND::MINUS) | Some(MODKIND::STAR) => {
                            env.modifiers.minuses.push(b.getpos());
                        }
                        Some(MODKIND::PLUS) => {}
                        None => {}
                    }
                    addplustoenv(a, b, &mut env);
                    env.addbinding(binding);
                }
                MetavarMatch::Exists => {
                    addplustoenv(a, b, &mut env);
                    match a.wrapper.modkind {
                        Some(MODKIND::MINUS) | Some(MODKIND::STAR) => {
                            //println!("exists -> {}", b.astnode.to_string());
                            env.modifiers.minuses.push(b.getpos());
                        }
                        Some(MODKIND::PLUS) => {}
                        None => {}
                    }
                }
            }
        }
    }
    //this function decides if two nodes match, fail or have a chance of matching, without
    //going deeper into the node.
    fn workon(
        &self,
        node1: &'b Snode,
        node2: &'a Rnode,
        bindings: &Vec<MetavarBinding>,
    ) -> MetavarMatch<'a, 'b> {
        // Metavar checking will be done inside the match
        // block below
        // to note: node1 and node2 are of the same SyntaxKind
        match &node1.wrapper.metavar {
            crate::parsing_cocci::ast0::MetaVar::NoMeta => {
                if node2.children.len() == 0
                //end of node
                {
                    //println!("{:?}========{}", node2.kind(), node2.astnode.to_string());

                    if node1.astnode.to_string() != node2.astnode.to_string() {
                        //basically checks for tokens
                        return MetavarMatch::Fail;
                    } else {
                        return MetavarMatch::Exists;
                    }
                }
                return MetavarMatch::Maybe(node1, node2); //not sure
            }
            metavar => {
                //NOTE THIS TAKES CARE OF EXP AND ID ONLY
                //println!("Found Expr {}, {:?}", node1.wrapper.metavar.getname(), node2.kind());
                if let Some(binding) = bindings
                    .iter()
                    .find(|binding| binding.metavarinfo.varname == node1.wrapper.metavar.getname())
                {
                    if binding.rnode.equals(node2) {
                        MetavarMatch::Exists
                    } else {
                        MetavarMatch::Fail
                    }
                } else {
                    match metavar {
                        MetaVar::Exp(_info) => {
                            if node2.isexpr() {
                                return MetavarMatch::Match;
                            }
                            return MetavarMatch::Maybe(node1, node2);
                        }
                        MetaVar::Id(_info) => {
                            if node2.isid() {
                                return MetavarMatch::Match;
                            }
                            return MetavarMatch::Maybe(node1, node2);
                        }
                        MetaVar::Type(_info) => {
                            if node2.istype() {
                                return MetavarMatch::Match;
                            }
                            return MetavarMatch::Maybe(node1, node2);
                        }

                        MetaVar::NoMeta => {
                            panic!("Should never occur");
                            //since no meta has been taken care of in the previous match
                        }
                    }
                }
            }
        }
    }

    pub fn handledisjunctions(
        &self,
        disjs: &Vec<Vec<Snode>>,
        node2: &Vec<&'a Rnode>,
        inheritedbindings: Vec<&MetavarBinding>,
    ) -> (Vec<Environment>, bool) {
        let mut environments: Vec<Environment> = vec![];
        let mut matched = false;
        for disj in disjs {
            let mut inheritedenv = Environment::new();
            inheritedenv.addbindings(&inheritedbindings);
            let env = self.matchnodes(&disj.iter().collect_vec(), node2, inheritedenv);
            matched = matched || !env.failed;
            if !env.failed {
                environments.push(env);
            }
        }
        (environments, matched)
    }
}
