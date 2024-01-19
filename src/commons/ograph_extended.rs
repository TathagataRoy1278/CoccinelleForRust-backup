use std::hash::Hash;

use itertools::Itertools;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EdgeIndex(usize);
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeIndex(pub usize);

impl NodeIndex {
    pub fn to_usize(&self) -> usize {
        self.0
    }
}

impl EdgeIndex {
    pub fn to_usize(&self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy)]
pub enum EdgeType {
    Default,
    Children,
}

// impl Into<usize> for EdgeIndex {
//     fn into(self) -> usize {
//         self.0
//     }
// }

// impl Into<usize> for NodeIndex {
//     fn into(self) -> usize {
//         self.0
//     }
// }

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct NodeData<K: Hash> {
    pub id: usize,
    data: K,
    first_out_edge: Option<EdgeIndex>,
    first_in_edge: Option<EdgeIndex>,
}

impl<K: Hash> NodeData<K> {
    pub fn data(&self) -> &K {
        return &self.data;
    }
}

impl<K: PartialEq + Eq + Hash> PartialOrd for NodeData<K> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.id.partial_cmp(&other.id)
    }
}

impl<K: Eq + PartialEq + Hash> Ord for NodeData<K> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering{
        self.id.cmp(&other.id)
    }
}

pub struct EdgeData {
    origin: NodeIndex,
    target: NodeIndex,
    edgetype: EdgeType,
    next_edge: Option<EdgeIndex>,
}

impl EdgeData {
    pub fn origin(&self) -> NodeIndex {
        return self.origin;
    }

    pub fn target(&self) -> NodeIndex {
        return self.target;
    }

    pub fn ty(&self) -> EdgeType {
        return self.edgetype;
    }
}

#[derive(Default)]
pub struct Graph<K: Hash> {
    pub nodes: Vec<NodeData<K>>,
    pub edges: Vec<EdgeData>,
}

impl<'a, K: Clone + Hash> Graph<K> {
    pub fn new() -> Graph<K> {
        return Graph { nodes: vec![], edges: vec![] };
    }

    pub fn node(&self, i: NodeIndex) -> NodeData<K> {
        self.nodes[i.to_usize()].clone()
    }

    pub fn nodes(&'a self) -> Vec<NodeIndex> {
        // self.nodes.clone().into_iter().collect_vec()
        (0..self.nodes.len()-1).map(|x| NodeIndex(x)).collect_vec()
    }

    pub fn last_edge_index(&self, x: EdgeIndex) -> EdgeIndex {
        let edge = &self.edges[x.to_usize()];
        match edge.next_edge {
            None => x,
            Some(ei) => self.last_edge_index(ei),
        }
    }

    pub fn add_node(&mut self, data: K) -> NodeIndex {
        let n = self.nodes.len();
        let nd = NodeData { id: n, data: data, first_out_edge: None, first_in_edge: None };
        self.nodes.push(nd);
        NodeIndex(n)
    }

    pub fn get_node(&self, ind: NodeIndex) -> &NodeData<K> {
        return &self.nodes[ind.to_usize()];
    }

    pub fn get_node_mut(&mut self, ind: NodeIndex) -> &mut NodeData<K> {
        return &mut self.nodes[ind.to_usize()];
    }

    pub fn add_edge(&mut self, nodei: NodeIndex, succ: NodeIndex, edgetype: EdgeType) -> EdgeIndex {
        let edge = EdgeData { origin: nodei, target: succ, edgetype: edgetype, next_edge: None };
        let nei = self.edges.len();
        self.edges.push(edge);
        let nodei = nodei.to_usize();

        match self.nodes[nodei].first_out_edge {
            None => {
                self.nodes[nodei].first_out_edge = Some(EdgeIndex(nei));
            }
            Some(ei) => {
                let lastindex = self.last_edge_index(ei).to_usize();
                self.edges[lastindex].next_edge = Some(EdgeIndex(nei));
            }
        }

        match self.nodes[nodei].first_in_edge {
            None => {
                self.nodes[nodei].first_in_edge = Some(EdgeIndex(nei));
            }
            Some(ei) => {
                let lastindex = self.last_edge_index(ei).to_usize();
                self.edges[lastindex].next_edge = Some(EdgeIndex(nei));
            }
        }

        EdgeIndex(nei)
    }

    pub fn add_edges(&mut self, nodei: NodeIndex, succs: Vec<(NodeIndex, EdgeType)>) {
        if succs.is_empty() {
            return;
        }

        let mut liei = None;
        let mut loei = None;
        let mut nei = self.edges.len();
        let nodei = nodei.to_usize();

        for (succ, edgetype) in succs {
            let edge = EdgeData {
                origin: NodeIndex(nodei),
                target: succ,
                edgetype: edgetype,
                next_edge: None,
            };
            self.edges.push(edge);

            match self.nodes[nodei].first_out_edge {
                None => {
                    self.nodes[nodei].first_out_edge = Some(EdgeIndex(nei));
                }
                Some(ei) => {
                    let lastindex = loei.unwrap_or(self.last_edge_index(ei)).to_usize();
                    self.edges[lastindex].next_edge = Some(EdgeIndex(nei));
                }
            }

            loei = Some(EdgeIndex(nei));
            match self.nodes[nodei].first_in_edge {
                None => {
                    self.nodes[nodei].first_in_edge = Some(EdgeIndex(nei));
                }
                Some(ei) => {
                    let lastindex = liei.unwrap_or(self.last_edge_index(ei)).to_usize();
                    self.edges[lastindex].next_edge = Some(EdgeIndex(nei));
                }
            }
            liei = Some(EdgeIndex(nei));

            nei += 1;
        }
    }

    pub fn successors(&'a self, source: NodeIndex) -> Vec<NodeIndex> {
        let first_o_edge = self.nodes[source.to_usize()].first_out_edge;
        let iter = EdgesIter {
            graph: self,
            current_edge_index: first_o_edge
        };

        let mut ret = vec![];
        for i in iter {
            ret.push(i);
        }

        return ret;
    }

    pub fn predecessors(&self, source: NodeIndex) -> Vec<NodeIndex> {
        let first_i_edge = self.nodes[source.to_usize()].first_in_edge;
        let iter = EdgesIter {
            graph: self,
            current_edge_index: first_i_edge
        };

        let mut ret = vec![];
        for i in iter {
            ret.push(i);
        }

        return ret;
    }
}

pub struct EdgesIter<'graph, K: Hash> {
    graph: &'graph Graph<K>,
    current_edge_index: Option<EdgeIndex>
}

impl<'graph, K: Hash> Iterator for EdgesIter<'graph, K> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        match self.current_edge_index {
            None => None,
            Some(edge_num) => {
                let edge = &self.graph.edges[edge_num.to_usize()];
                self.current_edge_index = edge.next_edge;
                Some(edge.target)
            }
        }
    }
}