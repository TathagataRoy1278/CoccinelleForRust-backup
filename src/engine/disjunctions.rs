// SPDX-License-Identifier: GPL-2.0

use itertools::{enumerate, Itertools};

use crate::{
    commons::util::{attach_pluses_back, attach_pluses_front},
    parsing_cocci::ast0::{Pluses, Snode},
};

#[derive(Debug)]
pub struct Disjunction(pub Vec<Vec<Snode>>);

impl Disjunction {
    pub fn new() -> Disjunction {
        Disjunction(vec![])
    }

    pub fn setchildren(&mut self, i: usize, j: usize, mut nodes: Disjunction) {
        if nodes.0.len() <= 1 {
            //this means no disjunctions exi=ist withing self.0[i]
            return;
        }
        let tmpdisj = self.0[i].clone();
        self.0[i][j].set_children(nodes.0.remove(0));
        for (ctr, disj) in enumerate(nodes.0) {
            let mut newdisj = tmpdisj.clone();
            newdisj[j].set_children(disj);
            self.0.insert(i + ctr + 1, newdisj);
        }
    }

    pub fn attachpluses(&mut self, pluses: Pluses) {
        for disj in &mut self.0 {
            attach_pluses_front(&mut disj[0], pluses.0.clone());
            let len = disj.len();
            attach_pluses_back(&mut disj[len - 1], pluses.1.clone());
        }
    }
}

pub fn getdisjunctions<'a>(nodes: Disjunction) -> Disjunction {
    let mut tmpdisjs: Vec<Vec<Snode>> = vec![]; //for each disjunction branch
    for disj in nodes.0.clone() {
        let mut newvec: Vec<Vec<Snode>> = vec![vec![]];
        //it may split into more branches if it has disjunctions inside
        for node in disj {
            if node.wrapper.isdisj {
                let (disjs, pluses) = node.getdisjs();
                //let tmpdisj = nodes.0[gi + i].remove(gj + j);
                let mut disjchildren =
                    Disjunction(disjs.iter().map(|x| x.children.clone()).collect_vec());
                disjchildren.attachpluses(pluses);
                let expandeddisj = getdisjunctions(disjchildren);
                //the above expands any inner disjunctions
                let tmpvec = newvec.clone();
                newvec = vec![]; //this discards the current disjunction to be
                                 //rebuilt
                for vec in tmpvec {
                    for disjvec in expandeddisj.0.clone() {
                        let mut tmpvec = vec.clone();
                        tmpvec.extend(disjvec);
                        newvec.push(tmpvec);
                    }
                }
                //nodes.add(gi + i, gj + j, getdisjunctions(disjtmp));
            } else {
                let tmpvec = newvec;
                newvec = vec![];
                //let tmp = getdisjunctions(Disjunction(vec![node.children]));
                //nodes.setchildren(gi + i, gj + j, tmp);
                if (&node.children).len() == 0 {
                    for mut vec in tmpvec {
                        vec.push(node.clone());
                        newvec.push(vec);
                    }
                } else {
                    for vec in tmpvec {
                        let tmpnode = node.clone();
                        for i in getdisjunctions(Disjunction(vec![node.children.clone()])).0 {
                            let mut newdisj = tmpnode.clone();
                            newdisj.set_children(i);
                            let mut tmpvec = vec.clone();
                            tmpvec.push(newdisj);
                            newvec.push(tmpvec);
                        }
                    }
                }
            }
        }
        tmpdisjs.extend(newvec);
    }
    return Disjunction(tmpdisjs);
}
