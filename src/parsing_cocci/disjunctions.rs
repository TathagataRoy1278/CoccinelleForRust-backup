use std::{cmp::Ordering, f64::consts::E};

use itertools::Itertools;
use ra_parser::SyntaxKind;

use crate::{
    commons::info::{COCCI_DISJ_DELIM, COCCI_DISJ_ID},
    parsing_cocci::ast0::{wrap_root, PositionInfo, Snode},
};

use super::parse_cocci::Patch;

type Tag = SyntaxKind;
type DisjId = (usize, usize); //disj number, branch number
type Dinfo = (DisjId, (usize, usize)); //disj_id, start_char, end_char

fn range_in(r1: (usize, usize), r2: (usize, usize)) -> bool {
    (r1.0 >= r2.0) && (r1.1 <= r2.1)
}

fn is_overlap(r1: (usize, usize), r2: (usize, usize)) -> bool {
    (r1.0 <= r2.1) && (r2.0 <= r1.1)
}

pub fn process_disjs(mut p: Patch, _has_type: bool) -> Patch {
    fn extract_braches(node: &Snode, info: (usize, usize)) -> Vec<Snode> {
        //this node is one of the possible branches
        let mut ret = vec![];
        for child in &node.children {
            let pos = child.wrapper.info.get_pos_tuple();
            if !is_overlap(info, pos) {
                continue;
            }
            // There is overlap
            // disj maybe fully inside this node
            // or exactly or the node may be fully
            // inside disj. This is because it is assumed
            // that partial overlap cannot happen in case
            // of a disjunction and any node.
            //
            // For example, let (a = 23; let) s= 20;
            //             |-----------|
            //                  |-----------|
            // is not allowed
            // but
            // let (a = 23;) let s = 10;
            // |-----------|
            //     |-------|
            // is valid
            if info == pos {
                //exact
                ret = vec![child.clone()];
                break;
            } else if range_in(info, pos) {
                // inside
                ret = extract_braches(child, info);
                break;
            } else {
                // other inside
                ret.push(child.clone());
            }
        }
        return ret;
    }

    fn extract_disj_mut(node: &mut Snode, id: usize) -> Option<&mut Snode> {
        for child in &mut node.children {
            if child.is_disj && child.wrapper.disj_id.unwrap() == id {
                return Some(child);
            } else {
                match extract_disj_mut(child, id) {
                    Some(child) => return Some(child),
                    None => continue,
                }
            }
        }
        None
    }

    fn merge_into_snode(mut main: Snode, expanded: Vec<(Snode, Vec<Dinfo>)>) {
        // This function is suppossed to put in the necessary syntaxkinds from
        //the expanded nodes into main

        fn aux(snode: &mut Snode, ps @ (parsed_node, dinfo): &(Snode, Vec<Dinfo>)) {
            // This takes snode and one possible parsed branch
            // aux is called only on the top disjunctions
            if snode.is_disj {
                let info = dinfo[dinfo
                    .iter()
                    .position(|x| {
                        x.0 .0
                            == snode
                                .wrapper
                                .disj_id
                                .expect("Disjunction should always havbe a disj_id")
                    })
                    .unwrap()];
                let parsed_branch = extract_braches(parsed_node, info.1);
                let parsed_tokens = parsed_branch
                    .iter()
                    .flat_map(|x| x.into_preorder())
                    .collect_vec();

                // we finally have the list of nodes we want to put in.
                // It is given that exactly one branch should match
                fn match_disj(
                    snode: &Snode,
                    parsed_tokens: &Vec<&Snode>,
                    lin: usize,
                ) -> Result<(usize, Vec<usize>), ()> {
                    // the list of integers returned denote which branches the current
                    // expanded branches match
                    let mut ret = vec![];
                    let mut lastin: usize;
                    if !snode.is_disj {
                        lastin = lin;
                        if snode.children.len() == 0 {
                            if snode.getstring() == parsed_tokens[lastin].getstring() {
                                lastin += 1;
                                return Ok((lastin, ret));
                            } else {
                                return Err(());
                            }
                        }
                        for node in &snode.children {
                            if node.children.len() == 0 {
                                if node.getstring() == parsed_tokens[lastin].getstring() {
                                    lastin += 1;
                                    continue;
                                } else {
                                    return Err(());
                                }
                            } else {
                                let (ln, mret) = match_disj(node, parsed_tokens, lastin)?;
                                ret.extend(mret);
                                lastin = ln;
                            }
                        }
                        return Ok((lastin, ret));
                    } else {
                        lastin = lin;
                        'branch: for (ind, branch) in snode.children.iter().enumerate() {
                            // eprintln!("LIN - {}", lastin);
                            //branch is made up of tokentree elements
                            lastin = lin;
                            ret = vec![];
                            for node in &branch.children {
                                // eprintln!(
                                //     "scannig node : {}, lastin - {}, legs - {:?}",
                                //     node.getstring(),
                                //     lastin,
                                //     parsed_tokens
                                // );
                                if node.children.len() == 0 {
                                    if node.getstring() == parsed_tokens[lastin].getstring() {
                                        lastin += 1;
                                    } else {
                                        continue 'branch;
                                    }
                                } else {
                                    if node.is_disj {
                                        let (lin, od) =
                                            match match_disj(node, parsed_tokens, lastin) {
                                                Ok(res) => res,
                                                Err(_) => continue 'branch,
                                            };
                                        lastin = lin;
                                        ret.extend(od);
                                    } else {
                                        for child in &node.children {
                                            eprintln!("child - {}", child.getstring());
                                            let (ln, mret) =
                                                match match_disj(child, parsed_tokens, lastin) {
                                                    Ok(res) => res,
                                                    Err(_) => continue 'branch,
                                                };
                                            ret.extend(mret);
                                            lastin = ln;
                                        }
                                    }
                                }
                            }
                            ret.insert(0, ind);
                            break;
                        }
                    }
                    return Ok((lastin, ret));
                }

                // eprintln!("pts - {:?}", parsed_tokens);
                let (_, inds) = match_disj(snode, &parsed_tokens, 0)
                    .expect("Some error in parsing disjunctions. Specifically matching the expanded brances to the their respective disjunctions");
                // eprintln!("matched {:?} with INDS = {:?}", parsed_tokens, inds);

                // At this point, for a disjunction we have which branch(or branches for nested disjunction)
                // is/are applicaple for this expansion.

                // We now substitute in the SyntaxKinds.
                // This is gonna be painful
            } else {
                snode.children.iter_mut().for_each(|x| aux(x, ps));
            }
        }

        for eb in expanded {
            aux(&mut main, &eb)
        }
        // for (dnode, dinfo) in expanded {
        //     if !range_in(dinfo[0], main.wrapper.info.get_pos_tuple()) {
        //         return main;
        //     } else {
        //         //no disjunction in main or dnode
        //         if dnode.kinds() == main.kinds() {
        //             let mut children1 = main.children;
        //             let mut children2 = dnode.children;
        //             let chlidren = vec![];

        //             for child in children1 {
        //                 let child2 = children2.remove(0);
        //                 let pos = child2.wrapper.info.get_pos_tuple();

        //                 if pos.1 >= dinfo[0].0 {}
        //             }
        //         }
        //     }
        // }
    }

    fn resolve_snodes(mut expanded: Vec<(Snode, Vec<Dinfo>)>) -> Snode {
        eprintln!("{:?}", expanded);
        let sort_f = |(_, range1): &Dinfo, (_, range2): &Dinfo| match is_overlap(*range1, *range2) {
            true => match range_in(*range1, *range2) {
                true => std::cmp::Ordering::Less,
                false => std::cmp::Ordering::Greater,
            },
            false => {
                if range1.1 < range2.0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
        };
        expanded.get_mut(0).unwrap().1.sort_by(sort_f);

        let (mut main_node, maininfo) = expanded.remove(0);

        for (did, inds) in &maininfo {
            fn to_disj(node: &mut Snode, (did, info): (DisjId, (usize, usize))) {
                //converts the node snode into
                let mut start: Option<usize> = None;
                let mut end: Option<usize> = None;

                for (ind, child) in node.children.iter_mut().enumerate() {
                    let pos = child.wrapper.info.get_pos_tuple();
                    eprintln!("{} - {:?}    {:?}", child.getstring(), pos, info);
                    if !is_overlap(info, pos) {
                        continue;
                    }
                    // There is overlap
                    // disj maybe fully inside this node
                    // or node may be fully inside the disj
                    if info == pos {
                        //exact
                        (start, end) = (Some(ind), Some(ind));
                        break;
                    } else if range_in(info, pos) {
                        // inside
                        to_disj(child, (did, info));
                        return;
                    } else {
                        //
                        if start.is_none() {
                            start = Some(ind)
                        } else {
                            end = Some(ind)
                        }
                    }
                }
                eprintln!("{:?}, {:?}", start, end);
                let new_pos = (
                    node.children[start.unwrap()].wrapper.info.pos_info.cstart,
                    node.children[end.unwrap()].wrapper.info.pos_info.cend,
                );
                let disj_children = node
                    .children
                    .drain(start.unwrap()..end.unwrap() + 1)
                    .collect_vec();
                let mut disj_branch = Snode::make_fake();
                disj_branch.wrapper.info.pos_info =
                    PositionInfo::new(0, 0, 0, 0, 0, new_pos.0, new_pos.1, 0);
                disj_branch.children = disj_children;

                let mut disj = Snode::make_disj(vec![disj_branch]);
                disj.wrapper.disj_id = Some(did.0);

                node.children.insert(start.unwrap(), disj);
            }
            to_disj(&mut main_node, (*did, *inds));
        }

        let maininfo = maininfo
            .into_iter()
            .map(|((x, y), z)| ((x, vec![y]), z))
            .collect_vec();
        let mut m = (main_node, maininfo);
        // main node is now well formed.

        for (ex_branch, ex_info) in expanded {
            eprintln!(
                "MUT - {}:{:?}\nMMM - {}:{:?}",
                m.0.getstring(),
                m.1,
                ex_branch.getstring(),
                ex_info
            );
            m = merge_snodes(m, (ex_branch, ex_info));
        }

        m.0.print_tree_kinds();
        m.0
    }

    fn merge_snodes(
        (mut main_node, mut maininfo): (Snode, Vec<((usize, Vec<usize>), (usize, usize))>),
        (tmd, tmi): (Snode, Vec<Dinfo>),
    ) -> (Snode, Vec<((usize, Vec<usize>), (usize, usize))>) {
        // Vec<Dinfo> of mainnode must be sorted
        for (did, _inds) in maininfo.iter_mut() {
            let ((_tid, bno), tminfo) = match tmi.iter().position(|(x, _)| x.0 == did.0) {
                Some(ii) => tmi[ii],
                None => continue,
            };
            if did.1.contains(&bno) {
                eprintln!("skipped");
                continue;
            }

            let mdisj = extract_disj_mut(&mut main_node, did.0)
                .expect("Disjunction cannot be found while merging");
            let parsed_nodes2 = extract_braches(&tmd, tminfo);
            let mut branch2 = Snode::make_fake();
            branch2.children = parsed_nodes2;
            mdisj.children.push(branch2);
            did.1.push(bno);
        }
        return (main_node, maininfo);
    }

    fn expand_disj(node: &mut Snode, dno: &mut usize) -> Vec<(String, Vec<Dinfo>)> {
        if node.children.len() == 0 {
            return vec![(node.asttoken.as_ref().unwrap().to_string(), vec![])];
        } else if node.is_disj {
            let adno = *dno;
            *dno = *dno + 1;

            node.wrapper.disj_id = Some(adno);
            node.children
                .iter_mut()
                .enumerate()
                .flat_map(|(bno, branch)| {
                    let mut bs = expand_disj(branch, dno);
                    bs.iter_mut().for_each(|(st, infos)| {
                        *st = String::from(st.trim());
                        eprintln!("corrected to {:?}", st);
                        infos.insert(0, ((adno, bno), (0, 0 + st.len())))
                    });
                    return bs;
                })
                .collect_vec()
        } else {
            return node.children.iter_mut().fold(
                vec![(String::new(), vec![])],
                |acc: Vec<(String, Vec<Dinfo>)>, node| {
                    let mut new = vec![];
                    let new_bs = expand_disj(node, dno);
                    //for no disjunctions new_bs will be one element

                    for (st, ins) in acc {
                        let st = String::from(st.trim());
                        for (new_b, new_ins) in new_bs.iter() {
                            // let new_b = new_b.trim();
                            let mut new_ins = new_ins.clone();
                            let jj = new_ins.clone();
                            let offset = if st.is_empty() { 0 } else { 1 };
                            new_ins.iter_mut().for_each(|(_, (ins1, ins2))| {
                                *ins1 = *ins1 + st.len() + offset; //
                                *ins2 = *ins2 + st.len() + offset; // Plus offset for the space character added in
                                                                   // in the next lines
                            });

                            let (mut sti, mut ins) = (st.clone(), ins.clone());
                            if !sti.is_empty() {
                                sti.push(' ');
                            }
                            sti.push_str(new_b);
                            eprintln!("SSS - {:?}, {:?}, {:?}", sti, jj, new_ins);
                            ins.extend(new_ins);

                            new.push((sti, ins));
                        }
                    }
                    new
                },
            );
        }
    }

    fn visitor(mut node: Snode) -> Snode {
        // Takes a tree and checks if it has macros which are
        // wrapped disjunctions. If yes, it converts them into
        // appropriate Snodes. To note the TokenTrees inside
        // Are not parsed into SyntaxNodes yet. Just the disjunctions
        // are represented as Snodes

        let kinds = node.kinds();
        if kinds.ends_with(&[Tag::MACRO_CALL]) {
            // Unwraps used below because children can never be 0
            let mut children = node.children;
            let mut attrs = vec![];
            while children.first().unwrap().has_kind(&Tag::ATTR) {
                attrs.push(children.remove(0));
            } //removes all attributes

            if children.first().unwrap().getstring() != COCCI_DISJ_ID {
                //This is a regular macro call and not what we are looking for
                attrs.extend(children);
                node.children = attrs;
                return node;
            }

            // Removing the [] from the tokentree
            let mut token_tree = children.remove(2);
            token_tree.children.remove(token_tree.children.len() - 1);
            token_tree.children.remove(0);
            let token_tree = token_tree.children;

            // Handling Disjucntions
            let mut branches = vec![];
            let mut branch = vec![];
            for token in token_tree {
                if token.getstring() == COCCI_DISJ_DELIM {
                    let mut node = Snode::make_fake();
                    node.children = branch;
                    branches.push(node);
                    branch = vec![];
                } else {
                    branch.push(visitor(token));
                }
            }
            if !branch.is_empty() {
                let mut node = Snode::make_fake();
                node.children = branch;
                branches.push(node);
            }

            let disj = Snode::make_disj(branches);
            return disj;
        } else {
            node.children = node
                .children
                .into_iter()
                .map(|node: Snode| visitor(node))
                .collect_vec();
            return node;
        }
    }

    fn resolve_inner_disjs(mut node: Snode) -> Snode {
        // In this step all the macros inside the TokenTrees of
        // other macros which are actually disjunctions are converted
        // into macros so that visitor can convert them into Disjunctions.
        // Can they be combined?
        // TokenTrees
        if node.has_kind(&SyntaxKind::TOKEN_TREE) {
            let mut new_tt = vec![];
            let mut children = node.children.into_iter();
            loop {
                if let Some(child) = children.next() {
                    if child.getstring() == COCCI_DISJ_ID {
                        //is a disj

                        let mut mstr = String::new();

                        mstr.push_str(&child.getstring());
                        let _ = children.next().unwrap(); //BANG

                        mstr.push('!');

                        let tt = children.next().unwrap();
                        assert!(tt.has_kind(&SyntaxKind::TOKEN_TREE));

                        mstr.push_str(&tt.getstring());

                        let mut wrapped = wrap_root(&format!("fn _disj_wrap_ () {{ {} }}", mstr))
                            .expect("Error while parsing inner disjunction");
                        let mac = wrapped
                            .children
                            .remove(3) //BlockExpr
                            .children
                            .remove(1); //gets the macro inside
                        let wr_mac = mac;

                        new_tt.push(resolve_inner_disjs(wr_mac));
                    } else {
                        new_tt.push(child);
                    }
                } else {
                    break;
                }
            }
            node.children = new_tt;
            return node;
        } else {
            if node.children.len() == 0 {
                return node;
            } else {
                node.children = node
                    .children
                    .into_iter()
                    .map(|node| resolve_inner_disjs(node))
                    .collect_vec();
                return node;
            }
        }
    }

    // The next two functions can definitely be combined
    // into one, but I am too tired right now.
    p.minus = resolve_inner_disjs(p.minus);
    // eprintln!("after resolution");
    // eprintln!("AA - {}", self.minus.getstring());
    // self.minus.print_tree();
    p.minus = visitor(p.minus);
    //At this point all the disjunctions are converted into macros
    //to be parsed
    // eprintln!("After visiting");
    // self.minus.print_tree();
    let bs = expand_disj(&mut p.minus, &mut 0);
    // eprintln!("{:?}", bs);
    let expanded = bs
        .into_iter()
        .map(|(b, inf)| {
            (
                wrap_root(&b).expect("Malformed Patch due to disjunction."),
                inf,
            )
        })
        .collect_vec();

    p.minus = resolve_snodes(expanded);
    // eprintln!("PASS - {}", snode.getstring());

    p.plus = resolve_inner_disjs(p.plus);
    p.plus = visitor(p.plus);
    let bs = expand_disj(&mut p.plus, &mut 0);
    // eprintln!("{:?}", bs);
    let expanded = bs
        .into_iter()
        .map(|(b, inf)| {
            (
                wrap_root(&b).expect("Malformed Patch due to disjunction."),
                inf,
            )
        })
        .collect_vec();
    p.plus = resolve_snodes(expanded);

    return p;
}

fn print_disj(snode: &Snode, disj_info: Vec<Dinfo>) {
    for ins in disj_info.iter().map(|(_, x)| x).collect_vec() {
        let pinfo = &snode.wrapper.info.pos_info;
        if range_in(*ins, (pinfo.cstart, pinfo.cend)) {
            eprintln!("DD - {:?}", snode);
        } else {
            eprintln!(
                "nnmatch - {}:{:?}",
                snode.getstring(),
                (pinfo.cstart, pinfo.cend)
            );
        }
    }
    snode
        .children
        .iter()
        .for_each(|x| print_disj(x, disj_info.clone()));
}
