// SPDX-License-Identifier: GPL-2.0

use std::rc::Rc;
use std::vec;

use itertools::Itertools;
use ra_parser::SyntaxKind;
use regex::Regex;

use crate::{
    commons::util::{getnrfrompt, getnrfrompt_r},
    debugcocci, fail,
    parsing_cocci::ast0::{Mcodekind, Snode},
    parsing_cocci::ast0::{MetaVar, MetavarName},
    parsing_rs::ast_rs::Rnode,
};

type Tag = SyntaxKind;

//This array is used for special matching cases where we want to continue matching
//even if the node types do not match
const EXCEPTIONAL_MATCHES: [(Tag, Tag); 1] = [(Tag::PATH_TYPE, Tag::PATH_SEGMENT)];

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

/// This checks for any pluses attached to the SEMANTIC PATCH CODE
/// If so it marks the corresponding position in the RUST CODE
/// and stores it along with the plus code in env
fn addplustoenv(a: &Snode, b: &Rnode, env: &mut Environment) {
    match &a.wrapper.mcodekind {
        Mcodekind::Context(avec, bvec) => {
            if avec.len() != 0 {
                env.modifiers.pluses.push((b.wrapper.info.charstart, true, avec.clone()));
            }
            if bvec.len() != 0 {
                env.modifiers.pluses.push((b.wrapper.info.charend, false, bvec.clone()));
            }
        }
        Mcodekind::Minus(pluses) => {
            //This is a replacement
            if pluses.len() != 0 {
                env.modifiers.pluses.push((b.wrapper.info.charstart, true, pluses.clone()));
            }
        }
        _ => {}
    }
}

pub fn types_equal(ty1: &str, ty2: &str) -> bool {
    let pattern = Regex::new(ty1).unwrap();
    pattern.is_match(ty2)
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

            //println!("{:?} ===== {:?} --> {}", akind, bkind, b.getunformatted());
            //please dont remove this line
            //helps in debugging, and I always forget where to put it

            //This takes care of when node types dont match but we still
            //want to work on them
            if EXCEPTIONAL_MATCHES.contains(&(akind, bkind)) {
                (a, b) = self.exceptional_workon(a, b);
                //println!("{:?} ===== {:?} --> {} ::: Exceptional", akind, bkind, b.getunformatted());
            } else {
                if akind != bkind && a.wrapper.metavar.isnotmeta()
                //There are certain metavariables which need to be processed even if the types dont match
                {
                    fail!()
                }
            }

            //At this point in execution, there are two possiblities
            //Either akind == bkind or a is a metavar or
            //(akind, bkind) is present in EXCEPRIONAL_MATCHES
            //The rule is, akind is allowed to be diff from bkind only if
            //there is a guaranteed match or fail in the next few iters
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
                        addplustoenv(a, b, &mut env);
                        env.add(renv);
                    } else {
                        fail!()
                    }
                }
                MetavarMatch::Match => {
                    let minfo = a.wrapper.metavar.getminfo();

                    debugcocci!(
                        "Binding {} to {}.{}",
                        b.getstring(),
                        minfo.0.rulename.to_string(),
                        minfo.0.varname.to_string()
                    );

                    let binding = MetavarBinding::new(
                        minfo.0.rulename.to_string(),
                        minfo.0.varname.to_string(),
                        b.clone(),
                    );

                    match a.wrapper.mcodekind {
                        Mcodekind::Minus(_) | Mcodekind::Star => {
                            env.modifiers.minuses.push(b.getpos());
                        }
                        Mcodekind::Plus => {}
                        Mcodekind::Context(_, _) => {}
                    }
                    addplustoenv(a, b, &mut env);
                    env.addbinding(binding);
                }
                MetavarMatch::Exists => {
                    //No bindings are created
                    addplustoenv(a, b, &mut env);
                    match a.wrapper.mcodekind {
                        Mcodekind::Minus(_) | Mcodekind::Star => {
                            env.modifiers.minuses.push(b.getpos());
                        }
                        Mcodekind::Plus => {}
                        Mcodekind::Context(_, _) => {}
                    }
                }
            }
        }
    }

    fn exceptional_workon(&self, node1: &'b Snode, node2: &'a Rnode) -> (&'b Snode, &'a Rnode) {
        match (node1.kind(), node2.kind()) {
            (Tag::PATH_TYPE, Tag::PATH_SEGMENT) => {
                //If a type is being compared then
                //Type maybe something like Foo<A, B> but it needs
                //to match types like Foo

                let name_ref1 = getnrfrompt(node1);
                let name_ref2 = match &node2.children.iter().map(|x| x.kind()).collect_vec()[..] {
                    [Tag::COLON2, Tag::NAME_REF] => &node2.children[1],
                    [Tag::NAME_REF]
                    | [Tag::NAME_REF, _]//GenericArgList
                    | [Tag::NAME_REF, _, _] => &node2.children[0],//Paramlist, RetType
                    | [Tag::L_ANGLE, Tag::PATH_TYPE, Tag::R_ANGLE] => {
                        getnrfrompt_r(&node2.children[1])
                    }
                    | [Tag::L_ANGLE, _, Tag::AS_KW, _, Tag::R_ANGLE] => {
                        //This should fail as it is something like
                        //<TypeA as TypeB>
                        //These types are matched seperately from
                        //visitrnode
                        node2
                    }
                    _ => {
                        panic!("PathSegment not fully implented in exceptional_workon");
                    } //There is one missing branch here: '<' PathType ('as' PathType)? '>'
                      //I am not sure how to handle that branch
                };

                (name_ref1, name_ref2)
            }
            _ => {
                panic!("The match arms should be exhaustive.");
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

                    if node1.totoken() != node2.totoken() {
                        //basically checks for tokens
                        return MetavarMatch::Fail;
                    } else {
                        return MetavarMatch::Exists;
                    }
                }
                return MetavarMatch::Maybe(node1, node2); //not sure
            }
            metavar => {
                //println!("Found Expr {}, {:?}", node1.wrapper.metavar.getname(), node2.kind());
                if let Some(binding) = bindings
                    .iter()
                    .find(|binding| binding.metavarinfo.varname == node1.wrapper.metavar.getname())
                {
                    //this is entered if a metavar has already been bound or is present
                    //in the inherited environment
                    if binding.rnode.equals(node2) {
                        MetavarMatch::Exists
                    } else {
                        MetavarMatch::Fail
                    }
                } else {
                    if metavar.isinherited() {
                        //If the metavar is inhertited
                        //but no bindings exist from previous rules
                        //then fail matching
                        return MetavarMatch::Fail;
                    }

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
                        MetaVar::Lifetime(_info) => {
                            if node2.islifetime() {
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
                        MetaVar::Parameter(_info) => {
                            if node2.isparam() {
                                return MetavarMatch::Match;
                            }
                            return MetavarMatch::Maybe(node1, node2);
                        }
                        MetaVar::Adt(tyname1, _info) => {
                            if let Some(tyname2) = &node2.wrapper.get_type() {
                                if types_equal(tyname1, tyname2) {
                                    return MetavarMatch::Match;
                                }
                            }

                            //Will go deeper for both other types and
                            //Non types like blocks
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
        let dnum = disjs.len();

        'outer: for din in 0..dnum {
            let disj = &disjs[din];
            let mut inheritedenv = Environment::new();
            inheritedenv.addbindings(&inheritedbindings);

            //this part makes sure that if any previous disjunctions
            //match for the current piece of code, we shall abort the matching
            //(a | b) is converted into (a | (not a) and b)

            for prevdisj in &disjs[0..din] {
                let penv =
                    self.matchnodes(&prevdisj.iter().collect_vec(), node2, inheritedenv.clone());
                if !penv.failed {
                    continue 'outer;
                }
            }

            let env = self.matchnodes(&disj.iter().collect_vec(), node2, inheritedenv);
            matched = matched || !env.failed;
            if !env.failed {
                environments.push(env);
            }
        }
        (environments, matched)
    }
}

pub fn visitrnode<'a>(
    nodea: &Vec<Vec<Snode>>,
    nodeb: &'a Rnode,
    f: &dyn Fn(&Vec<Vec<Snode>>, &Vec<&'a Rnode>) -> (Vec<Environment>, bool),
) -> Vec<Environment> {
    let mut environments = vec![];
    let nodebchildren = &mut nodeb.children.iter();

    loop {
        let tmp = f(nodea, &nodebchildren.clone().collect_vec()); //CLoning an Iter only clones the references inside

        if tmp.1 {
            environments.extend(tmp.0);
        }

        if let Some(child) = nodebchildren.next() {
            environments.extend(visitrnode(nodea, child, f));
        } else {
            break;
        }
    }
    return environments;
}
