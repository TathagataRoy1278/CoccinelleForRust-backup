use itertools::Itertools;
use ra_parser::SyntaxKind;

use crate::commons::info::{L_BROS, R_BROS};
use crate::commons::ograph_extended::{EdgeType, Graph, NodeIndex};
use crate::parsing_rs::ast_rs::Rnode;
use std::fmt::Debug;

// enum Node1<'a> {
//     TopNode,
//     EndNode,
//     Item(&'a Rnode), //For nodes under SourceFile
//     //Each item should be disjoint
//     SeqStart(&'a Rnode), // {
//     SeqEnd(&'a Rnode),   // }

//     ExprStmt(&'a Rnode),

//     IfHeader(&'a Rnode),
//     Else(&'a Rnode),
//     WhileHeader(&'a Rnode),
//     ForHeader(&'a Rnode),
//     LoopHeader(&'a Rnode),
//     MatchHeader(&'a Rnode),
// }

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Node<'a> {
    StartNode,
    AfterNode,
    RnodeW(NodeWrap<'a>),
    EndNode,
}

impl<'a> Node<'a> {
    pub fn rnode(&self) -> Option<&'a Rnode> {
        match self {
            Node::StartNode => None,
            Node::AfterNode => None,
            Node::RnodeW(nodew) => return Some(nodew.rnode),
            Node::EndNode => None,
        }
    }

    pub fn label(&self) -> Option<usize> {
        match self {
            Node::StartNode => None,
            Node::AfterNode => None,
            Node::RnodeW(nodew) => return Some(nodew.info.labels),
            Node::EndNode => None,
        }
    }

    pub fn is_dummy(&self) -> bool {
        match self {
            Node::StartNode => true,
            Node::AfterNode => true,
            Node::RnodeW(_) => false,
            Node::EndNode => true,
        }
    }

    pub fn paren_val(&self) -> Option<Option<usize>> {
        match self {
            Node::StartNode | Node::EndNode | Node::AfterNode => {
                return None;
            }
            Node::RnodeW(nodew) => Some(nodew.info.paren),
        }
    }

    pub fn getstring(&self) -> String {
        match self {
            Node::StartNode => String::from("Start"),
            Node::AfterNode => String::from("After"),
            Node::RnodeW(nodew) => {
                if nodew.rnode.children.is_empty() {
                    format!("{}", nodew.rnode.getstring())
                } else {
                    format!("{:?}", nodew.rnode.kinds())
                }
            }
            Node::EndNode => String::from("End"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct NodeWrap<'a> {
    rnode: &'a Rnode,
    info: NodeInfo,
}

impl<'a> Debug for NodeWrap<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.rnode.getstring()[..10])
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct NodeInfo {
    paren: Option<usize>,
    labels: usize,
    bclabels: Vec<usize>,
    is_loop: bool,
    is_fake: bool,
}

pub type Rflow<'a> = Graph<Node<'a>>;

fn make_node<'a>(paren: Option<usize>, label: usize, rnode: &'a Rnode) -> Node<'a> {
    return Node::RnodeW(NodeWrap { rnode: rnode, info: NodeInfo::new(paren, label) });
}

impl NodeInfo {
    pub fn new(paren: Option<usize>, labels: usize) -> NodeInfo {
        return NodeInfo { paren: paren, labels, bclabels: vec![], is_loop: false, is_fake: false };
    }
}

pub fn ast_to_flow<'a>(rnodes: &'a Vec<Rnode>) -> Graph<Node<'a>> {
    fn rem_attr(children: &[Rnode]) -> (&[Rnode], bool) {
        if children.is_empty() {
            (children, false)
        } else {
            //always first element has to be the attribute
            if children[0].has_kind(&SyntaxKind::ATTR) {
                return (&children[1..], true);
            } else {
                return (children, false);
            }
        }
    }

    fn make_graph<'b, 'a: 'b>(
        prev_inds: &[NodeIndex],
        graph: &'b mut Graph<Node<'a>>,
        rnodes: &'a Vec<Rnode>,
        label: usize,
        splits: &[usize], //the branch is split into two at each
        //index in splits
        paren: usize,
    ) -> (Vec<NodeIndex>, Vec<NodeIndex>) {
        //One for Default, one for Siblings
        let mut prev_sib: Option<NodeIndex> = None;
        //First one is the index of the last node if children exist
        //Second one is the list of all the nodes with no next node
        //at their own level
        let mut psibs = vec![];
        let mut prev_inds = prev_inds.to_vec();
        let label = label << 1;
        if rnodes.is_empty() {
            return (vec![], psibs);
        }

        let mut rnodes = rnodes.iter().peekable();
        let mut ends = vec![]; //has the last nodes which need to be linked to the next ones
        let mut ctr: usize = 0;
        let mut nparen: usize;

        while rnodes.peek().is_some() {
            let rnode = match rnodes.next() {
                Some(rnode) => rnode,
                None => break,
            };
            nparen = paren + ctr + 1;

            //Setting ParenVals
            let lkind = rnode.kinds().last().unwrap();
            let node = if L_BROS.contains(lkind) {
                make_node(Some(paren), label, rnode)
            } else if R_BROS.contains(lkind) {
                make_node(Some(paren), label, rnode)
            } else {
                //Node created and added to graph
                make_node(None, label, rnode)
            };

            let ind = graph.add_node(node);

            // EDGES BEING CREATES
            //creates defalut edge between the previous nodes and the current
            prev_inds.iter().for_each(|pind| {
                graph.add_edge(*pind, ind, EdgeType::Default);
            });

            //creates sibling edge between the current node and the previous sibling node
            if let Some(prev_sib) = prev_sib {
                graph.add_edge(prev_sib, ind, EdgeType::Sibling);
            }

            //creates edges between the current node and all the nodes prior that have no next siblings
            psibs.into_iter().for_each(|pind| {
                graph.add_edge(pind, ind, EdgeType::Sibling);
            });

            use ra_parser::SyntaxKind as Tag;

            //StmtList

            //Branching
            //inds = last processed node from inside make_graph
            //pindst = last processed nodes with no siblings
            let (inds, pindst) = match rnode.kinds().last().unwrap() {
                Tag::IF_EXPR => {
                    let (children, hasattr) = rem_attr(rnode.children.as_slice());
                    let hasattr: usize = if hasattr { 1 } else { 0 };
                    match children {
                        [ifkw, _cond, _thenn] if ifkw.has_kind(&Tag::IF_KW) => {
                            make_graph(&[ind], graph, &rnode.children, label, &[], nparen)
                        }
                        [ifkw, _cond, _thenn, _elsekw, _elsebr] if ifkw.has_kind(&Tag::IF_KW) => {
                            make_graph(
                                &[ind],
                                graph,
                                &rnode.children,
                                label,
                                &[hasattr + 2],
                                nparen,
                            )
                        }
                        _ => {
                            panic!("Pattern does not exist")
                        }
                    }
                }
                Tag::STMT_LIST => {
                    let children = &rnode.children;
                    let (is, ps) = make_graph(&[ind], graph, children, label, &[], nparen);

                    assert_eq!(is.len(), 1); //the last node is the }
                    let rc = is.last().unwrap();
                    let lc = graph.successors(ind)[0]; //only one because stmt list always has { as starting

                    let after = Node::AfterNode;
                    let afi = graph.add_node(after);
                    graph.add_edge(lc, afi, EdgeType::Default);
                    graph.add_edge(afi, *rc, EdgeType::Default);

                    (is, ps)
                }
                _ => make_graph(&[ind], graph, &rnode.children, label, &[], nparen),
            };
            psibs = pindst;

            if splits.contains(&ctr) {
                //inds is empty when ind has no children
                if inds.is_empty() {
                    ends.push(ind);
                } else {
                    ends.extend(inds);
                }

                //prev inds remains the same to connect
                //to the next branch
            } else {
                if inds.is_empty() {
                    prev_inds = vec![ind];
                } else {
                    prev_inds = inds;
                }
            }

            prev_sib = Some(ind);

            if rnodes.peek().is_none() {
                psibs.push(ind);
            }

            ctr += 1;
        }

        ends.extend(prev_inds);
        return (ends, psibs);
    }

    let mut graph: Graph<Node<'a>> = Graph::new();
    let f = graph.add_node(Node::StartNode);

    let (e, _) = make_graph(&[f], &mut graph, rnodes, 0, &[], 0);

    //Make end dummy node loop
    let ind = graph.add_node(Node::EndNode);
    e.into_iter().for_each(|e| {
        graph.add_edge(e, ind, EdgeType::Default);
    });
    graph.add_edge(ind, ind, EdgeType::Default);

    return graph;
}

pub fn asts_to_flow<'a>(rnode: &'a Vec<Vec<Rnode>>) -> Vec<Graph<Node<'a>>> {
    rnode.iter().map(|rnodes| ast_to_flow(rnodes)).collect_vec()
}

// pub fn ast_to_flow_tmp<'a>(rnodes: &'a Vec<Rnode>) -> Graph<Node<'a>> {
//     fn make_graph<'b, 'a: 'b>(
//         graph: &'b mut Graph<Node<'a>>,
//         rnodes: &'a Vec<Rnode>,
//         label: usize,
//     ) -> Option<NodeIndex> {
//         let mut node_indices = vec![];
//         for rnode in rnodes {
//             let label = label;
//             let info = NodeInfo::new(label);
//             let node = NodeWrap { rnode, info };

//             node_indices.push(graph.add_node(Node::RnodeW(node)));
//         }
//         node_indices.push(graph.add_node(Node::EndNode));

//         let fni = node_indices[0];
//         let mut iter = node_indices.into_iter().peekable();
//         while let Some(ni) = iter.next() {
//             let node = graph.get_node(ni);
//             let nodew = node.data();

//             match nodew {
//                 Node::RnodeW(nodew) => {
//                     let rnode: &'a Rnode = nodew.rnode;
//                     match rnode.kind() {
//                         _ => {
//                             let cni = make_graph(graph, &rnode.children, label << 1);
//                             cni.map(|cni| graph.add_edge(ni, cni, EdgeType::Children));
//                         }
//                     }
//                     if let Some(nni) = iter.peek() {
//                         graph.add_edge(ni, *nni, EdgeType::Default);
//                     }
//                 }
//                 Node::EndNode => {
//                     graph.add_edge(ni, ni, EdgeType::Default);
//                 }
//             }
//         }

//         return Some(fni);
//     }

//     let mut graph: Graph<Node<'a>> = Graph::new();
//     make_graph(&mut graph, rnodes, 0);
//     return graph;
// }
