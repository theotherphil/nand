
use petgraph::prelude::*;
use std::collections::HashSet;

pub fn topological_sort<N, E>(graph: &Graph<N, E>) -> Vec<NodeIndex> {
    let mut stack = Vec::new();
    let mut black = Vec::new();
    let mut white: HashSet<NodeIndex> = graph.node_indices().collect();
    let mut grey = HashSet::<NodeIndex>::new();
    let mut active: Option<NodeIndex>;

    while !white.is_empty() {
        let u = *white.iter().nth(0).unwrap();
        white.remove(&u);
        grey.insert(u);
        active = Some(u);

        loop {
            if let Some(v) = graph.neighbors_directed(active.unwrap(), Direction::Outgoing)
                                  .filter(|w| white.contains(w))
                                  .nth(0) {
                white.remove(&v);
                grey.insert(v);
                stack.push(active.unwrap());
                active = Some(v);
            } else {
                let a = active.unwrap();
                grey.remove(&a);
                black.push(a);
                let mut incomplete_children = graph
                    .neighbors_directed(a, Direction::Outgoing)
                    .filter(|w| white.contains(w) || grey.contains(w));
                if let Some(c) = incomplete_children.next() {
                    panic!("Cycle detected involving {:?}", c);
                }
                active = stack.pop();
            }
            if active == None {
                break;
            }
        }
    }

    black.into_iter().rev().collect()
}

#[cfg(test)]
mod tests {
    use petgraph::prelude::*;
    use super::*;

    #[test]
    fn test_topological_sort_empty_graph() {
        let g = Graph::<&str, ()>::new();
        let ordered = topological_sort(&g);
        assert_eq!(Vec::<NodeIndex>::new(), ordered)
    }

    #[test]
    fn test_topological_sort_singleton_graph() {
        let mut g = Graph::<&str, ()>::new();
        let a = g.add_node("a");
        let ordered = topological_sort(&g);
        assert_eq!(vec![a], ordered)
    }

    #[test]
    fn test_topological_sort_two_node_chain() {
        let mut g = Graph::<&str, ()>::new();
        let a = g.add_node("a");
        let b = g.add_node("b");
        g.extend_with_edges(&[
            (a, b)
        ]);
        let ordered = topological_sort(&g);
        assert_eq!(vec![a, b], ordered);
    }

    #[test]
    fn test_topological_sort_two_node_antichain() {
        let mut g = Graph::<&str, ()>::new();
        let _ = g.add_node("a");
        let _ = g.add_node("b");
        let ordered = topological_sort(&g);
        assert_eq!(2, ordered.len());
    }

    #[test]
    fn test_topological_sort_triangle() {
        let mut g = Graph::<&str, ()>::new();
        let a = g.add_node("a");
        let b = g.add_node("b");
        let c = g.add_node("c");
        g.extend_with_edges(&[
            (a, b), (c, b), (a, c)
        ]);
        let ordered = topological_sort(&g);
        assert_eq!(vec![a, c, b], ordered);
    }

    #[test]
    fn test_topological_sort_diamond() {
        let mut g = Graph::<&str, ()>::new();
        let a = g.add_node("a");
        let b = g.add_node("b");
        let c = g.add_node("c");
        let d = g.add_node("d");
        g.extend_with_edges(&[
            (a, b), (a, c), (b, d), (c, d)
        ]);
        let ordered = topological_sort(&g);
        assert_eq!(4, ordered.len());
        assert_eq!(a, ordered[0]);
        assert_eq!(d, ordered[3]);
    }

    #[test]
    #[should_panic]
    fn test_topological_sort_rejects_two_element_cycle() {
        let mut g = Graph::<&str, ()>::new();
        let a = g.add_node("a");
        let b = g.add_node("b");
        g.extend_with_edges(&[
            (a, b), (b, a)
        ]);
        let _ = topological_sort(&g);
    }
}
