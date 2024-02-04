use itertools::Itertools;

use crate::commons::ograph_extended::{EdgeType, Graph, NodeData, NodeIndex};
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
    RnodeW(NodeWrap<'a>),
    EndNode,
}

impl<'a> Node<'a> {
    pub fn rnode(&self) -> &'a Rnode {
        match self {
            Node::StartNode => panic!("Shouldnt be called"),
            Node::RnodeW(nodew) => return nodew.rnode,
            Node::EndNode => panic!("Shouldnt be called"),
        }
    }

    pub fn is_dummy(&self) -> bool {
        match self {
            Node::StartNode => true,
            Node::RnodeW(_) => false,
            Node::EndNode => true,
        }
    }

    pub fn getstring(&self) -> String {
        if self.is_dummy() {
            return String::from("Dummy;");
        } else {
            if self.rnode().children.is_empty() {
                format!("{}", self.rnode().getstring())
            } else {
                format!("{:?}", self.rnode().kind())
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct NodeWrap<'a> {
    rnode: &'a Rnode,
    info: NodeInfo,
}

impl<'a> NodeWrap<'a> {
    pub fn rnode(&self) -> &'a Rnode {
        return self.rnode;
    }

    pub fn info(&self) -> NodeInfo {
        return self.info.clone();
    }
}

impl<'a> Debug for NodeWrap<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.rnode.getstring()[..10])
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct NodeInfo {
    labels: usize,
    bclabels: Vec<usize>,
    is_loop: bool,
    is_fake: bool,
}

pub type Rflow<'a> = Graph<Node<'a>>;

fn make_node<'a>(label: usize, rnode: &'a Rnode) -> Node<'a> {
    return Node::RnodeW(NodeWrap { rnode: rnode, info: NodeInfo::new(label) });
}

impl NodeInfo {
    pub fn new(labels: usize) -> NodeInfo {
        return NodeInfo { labels, bclabels: vec![], is_loop: false, is_fake: false };
    }
}

pub fn ast_to_flow<'a>(rnodes: &'a Vec<Rnode>) -> Graph<Node<'a>> {
    fn make_graph<'b, 'a: 'b>(
        mut prev: NodeIndex,
        graph: &'b mut Graph<Node<'a>>,
        rnodes: &'a Vec<Rnode>,
        label: usize,
    ) -> Option<NodeIndex> {
        let mut prev_sib = None;

        let label = label << 1;
        if rnodes.is_empty() {
            return None;
        }

        let mut rnodes = rnodes.iter().peekable();

        while rnodes.peek().is_some() {
            let rnode = match rnodes.next() {
                Some(rnode) => rnode,
                None => break,
            };

            let node = make_node(label, rnode);
            let ind = graph.add_node(node);
            graph.add_edge(prev, ind, EdgeType::Default);
            //creates edge between the current node and the previous node

            if let Some(prev_sib) = prev_sib {
                graph.add_edge(prev_sib, ind, EdgeType::NextSibling);
            }

            let inds = make_graph(ind, graph, &rnode.children, label);
            match inds {
                Some(e) => {
                    prev = e;
                }
                None => {
                    prev = ind;
                }
            }
            prev_sib = Some(ind);
        }

        return Some(prev);
    }

    let mut graph: Graph<Node<'a>> = Graph::new();
    let f = graph.add_node(Node::StartNode);

    let e = make_graph(f, &mut graph, rnodes, 0).unwrap();

    //Make end dummy node loop
    let ind = graph.add_node(Node::EndNode);
    graph.add_edge(e, ind, EdgeType::Default);
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
