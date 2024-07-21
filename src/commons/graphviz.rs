use std::{collections::HashSet, fs};

use crate::{commons::ograph_extended::EdgeType, parsing_rs::control_flow::Rflow};

use super::ograph_extended::NodeIndex;

pub fn make_graphviz(graph: &Rflow, filename: &str) {
    fn aux(node: NodeIndex, graph: &Rflow, table: &mut HashSet<(NodeIndex, NodeIndex, EdgeType)>) -> String {
        let mut res = String::new();
        let sae = graph.successors_and_edges(node);

        for (child, etype) in sae {
            if table.get(&(node, child, etype)).is_some() {
                //for dealing with loops
                continue;
            }

            table.insert((node, child, etype));
            if graph.get_node(node).data().paren_val().is_some() {
                let parenval = graph.get_node(node).data().paren_val().unwrap();

                res.push_str(&format!(
                    "{} [label = \"{}:{} Pval - {}\"]\n",
                    node.0,
                    node.0,
                    graph.node(node).data().getstring(),
                    parenval
                ));
            } else {
                res.push_str(&format!(
                    "{} [label = \"{}:{}\"]\n",
                    node.0,
                    node.0,
                    graph.node(node).data().getstring()
                ));
            }

            if etype == EdgeType::Default {
                res.push_str(&format!("{} -> {}\n", node.0, child.0,));
            } else {
                res.push_str(&format!("{} -> {} [color = blue]\n", node.0, child.0,));
            }
            res.push_str(&aux(child, graph, table));
        }

        return res;
    }

    let res = aux(NodeIndex(0), &graph, &mut HashSet::new());
    let res = format!("digraph {{ \n{} \n}}", res);

    if let Err(_) = fs::write(filename, res) {
        eprintln!("Could not write file");
    }
}
