// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

use crate::bst;

const PARENT_MASK: usize = usize::MAX >> 1;
const COLOR_MASK: usize = 1 << ((std::mem::size_of::<usize>() * 8) - 1);

pub trait Node<E>: bst::TreeNode<E>
where
    Self: Sized,
{
    fn is_black(&self) -> bool;
    fn is_red(&self) -> bool;
    fn set_black(&mut self);
    fn set_red(&mut self);
}

/// This is a private function used exclusively by `rbtree::insert()`.
fn insert_loop<K, T>(nodes: &mut Vec<T>, n: usize) -> Option<(usize, usize, usize)>
where
    K: Ord,
    T: Node<K>,
{
    let len: usize = nodes.len();
    if n < len {
        let p: usize = nodes[n].parent();
        if p < len {
            let pp: usize = nodes[p].parent();
            if pp < len && nodes[p].is_red() {
                return Some((n, p, pp));
            }
        }
    }
    None
}

/// fix up any red-black rule violations
fn insert_fixup<K, T>(nodes: &mut Vec<T>, root: &mut usize, mut index: usize)
where
    K: Ord + Copy,
    T: Node<K>,
{
    while let Some((n, p, pp)) = insert_loop(nodes, index) {
        if p == nodes[pp].left() {
            let u: usize = nodes[pp].right();
            if u < nodes.len() && nodes[u].is_red() {
                nodes[p].set_black();
                nodes[u].set_black();
                nodes[pp].set_red();
                index = pp;
            } else {
                if n == nodes[p].right() {
                    bst::rotate_left(nodes, root, p);
                    nodes[n].set_black();
                } else {
                    nodes[p].set_black();
                };
                bst::rotate_right(nodes, root, pp);
                nodes[pp].set_red();
                break;
            }
        } else {
            let u: usize = nodes[pp].left();
            if u < nodes.len() && nodes[u].is_red() {
                nodes[p].set_black();
                nodes[u].set_black();
                nodes[pp].set_red();
                index = pp;
            } else {
                if n == nodes[p].left() {
                    bst::rotate_right(nodes, root, p);
                    nodes[n].set_black();
                } else {
                    nodes[p].set_black();
                };
                bst::rotate_left(nodes, root, pp);
                nodes[pp].set_red();
                break;
            }
        }
    }
    nodes[*root].set_black();
}

fn transplant<K, T>(nodes: &mut [T], root: &mut usize, node: T, child: T)
where
    K: Ord + Copy,
    T: Node<K>,
{
    // need to implement
}

fn delete_fixup<K, T>(nodes: &mut [T], index: usize)
where
    K: Ord,
    T: Node<K>,
{
    // need to implement
}

/*
pub mod map {

    use crate::bst;

    pub trait Entry<K, V> {
        fn key(&self) -> &K;
        fn value(&self) -> &V;
        fn value_mut(&mut self) -> &mut V;
    }

    #[derive(Debug, Clone, Copy)]
    pub struct Node<K, V> {
        parent: usize,
        left: usize,
        right: usize,
        entry: (K, V),
    }

    impl<T> From<T> for Node<K, V>
    where
        T: bst::TreeNode<(K, V)>,
    {
        fn from(entry: T) -> Self {
            Self {
                parent: bst::NIL,
                left: bst::NIL,
                right: bst::NIL,
                entry,
            }
        }
    }

    impl<K, V> Node<K, V> {
        pub fn new(key: K, value: V) -> Self {
            Self {
                parent: super::PARENT_MASK, // starts as red
                left: bst::NIL,
                right: bst::NIL,
                entry: (key, value),
            }
        }

        #[inline]
        pub fn value(&self) -> &V {
            &self.entry.1
        }

        #[inline]
        pub fn entry(&self) -> &(K, V) {
            &self.entry
        }
    }

    impl<K, V, T> super::Node<T> for Node<K, V> {
        #[inline]
        fn is_black(&self) -> bool {
            self.parent & super::COLOR_MASK == 1
        }

        #[inline]
        fn is_red(&self) -> bool {
            self.parent & super::COLOR_MASK == 0
        }

        #[inline]
        fn set_black(&mut self) {
            self.parent |= super::COLOR_MASK;
        }

        #[inline]
        fn set_red(&mut self) {
            self.parent &= super::PARENT_MASK;
        }
    }

    impl<K, V, T> bst::TreeNode<T> for Node<K, V> {
        #[inline]
        fn key(&self) -> &K {
            &self.entry.0
        }

        #[inline]
        fn left(&self) -> usize {
            self.left
        }

        #[inline]
        fn parent(&self) -> usize {
            self.parent & super::PARENT_MASK
        }

        #[inline]
        fn right(&self) -> usize {
            self.right
        }

        #[inline]
        fn set_left(&mut self, l: usize) {
            self.left = l;
        }

        #[inline]
        fn set_parent(&mut self, p: usize) {
            self.parent = (self.parent & super::COLOR_MASK) | (p & super::PARENT_MASK);
        }

        #[inline]
        fn set_right(&mut self, r: usize) {
            self.right = r;
        }
    }

    #[derive(Debug, Clone)]
    pub struct Map<K, V>
    where
        K: Ord,
    {
        inner: Vec<Node<K, V>>,
        root: usize,
    }

    impl<K, V> Map<K, V>
    where
        K: Ord,
    {
        pub fn new() -> Self {
            Self {
                inner: Vec::new(),
                root: bst::NIL,
            }
        }

        /*pub fn insert(&mut self, node: Node<K, V>)
        where
            K: Ord + Copy,
        {
            // perform a bst insertion
            match bst::insert(&mut self.inner, &mut self.root, node) {
                Ok(index) => {
                    super::insert_fixup(&mut self.inner, &mut self.root, index);
                }
                Err(index) => {
                    self.inner[index].entry.1 = node.entry.1.clone();
                }
            }
        }*/
    }
}
*/
