// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * Put crate documentation here...
 */

use crate::bst;
use crate::error::{Error, ErrorKind, Result};
use std::cmp::Ordering;

pub trait Node<K, P>: bst::Node<K>
where
    Self: Sized,
    K: Ord + Copy,
    P: Ord + Copy,
{
    fn priority(&self) -> &P;
    fn entry(&self) -> &(K, P);
    fn is_leaf(&self) -> bool;
}

#[allow(unused_variables)]
pub trait Treap<K, P, const MAX_HEAP: bool> {
    fn insert(&mut self, key: K, priority: P) -> Result<()>;
    fn remove(&mut self, key: &K) -> Option<(K, P)>;
    fn update(&mut self, key: &K, new_priority: P) -> Option<P> {
        None // update does not apply to all types of treaps
    }
    fn top(&mut self) -> Option<(K, P)>;
    fn peek(&self) -> Option<&(K, P)>;
    fn search(&self, key: &K) -> Option<&(K, P)>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub fn bubble_up<K, P, T>(nodes: &mut Vec<T>, root: &mut usize, sort_order: Ordering, index: usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    T: Node<K, P>,
{
    while nodes[index].parent() < nodes.len()
        && nodes[index]
            .priority()
            .cmp(nodes[nodes[index].parent()].priority())
            == sort_order
    {
        let p: usize = nodes[index].parent();
        if index == nodes[p].right() {
            bst::rotate_left(nodes, root, p);
        } else {
            bst::rotate_right(nodes, root, p);
        }
    }
}

pub fn insert<K, P, T>(
    nodes: &mut Vec<T>,
    root: &mut usize,
    sort_order: Ordering,
    entry: T,
) -> Result<()>
where
    K: Ord + Copy,
    P: Ord + Copy,
    T: Node<K, P>,
{
    let index: usize = bst::insert(nodes, root, entry)
        .map_err(|_| Error::new(ErrorKind::InsertionFailed, "Key already exists."))?;
    bubble_up(nodes, root, sort_order, index);
    Ok(())
}

pub fn push_down<K, P, T>(nodes: &mut [T], root: &mut usize, sort_order: Ordering, index: usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    T: Node<K, P>,
{
    while !nodes[index].is_leaf() {
        if nodes[index].left() != bst::NIL
            && (nodes[index].right() == bst::NIL
                || nodes[nodes[index].left()]
                    .priority()
                    .cmp(nodes[nodes[index].right()].priority())
                    == sort_order)
        {
            bst::rotate_right(nodes, root, index);
        } else {
            bst::rotate_left(nodes, root, index);
        }
    }
}

pub fn remove<K, P, T>(
    nodes: &mut Vec<T>,
    root: &mut usize,
    sort_order: Ordering,
    index: usize,
) -> Result<T>
where
    K: Ord + Copy,
    P: Ord + Copy,
    T: Node<K, P>,
{
    if index >= nodes.len() {
        Err(Error::new(
            ErrorKind::IndexOutOfBounds,
            "Index does not exist.",
        ))
    } else if nodes.len() == 1 {
        *root = bst::NIL;
        Ok(nodes.pop().expect("treap.pop() should never panic"))
    } else {
        push_down(nodes, root, sort_order, index);
        let p: usize = nodes[index].parent();
        if nodes[p].left() == index {
            nodes[p].set_left(bst::NIL);
        } else {
            nodes[p].set_right(bst::NIL);
        }
        bst::swap_remove(nodes, root, index)
    }
}

pub mod basic {

    use super::Node as NodeTrait;
    use crate::{bst, error};
    use std::cmp::Ordering;

    #[derive(Debug, Clone, Copy)]
    struct Node<K, P>
    where
        K: Ord + Copy,
        P: Ord + Copy,
    {
        parent: usize,
        left: usize,
        right: usize,
        entry: (K, P),
    }

    impl<K, P> From<(K, P)> for Node<K, P>
    where
        K: Ord + Copy,
        P: Ord + Copy,
    {
        fn from(entry: (K, P)) -> Self {
            Self {
                parent: bst::NIL,
                left: bst::NIL,
                right: bst::NIL,
                entry,
            }
        }
    }

    impl<K, P> super::Node<K, P> for Node<K, P>
    where
        K: Ord + Copy,
        P: Ord + Copy,
    {
        #[inline]
        fn priority(&self) -> &P {
            &self.entry.1
        }

        #[inline]
        fn entry(&self) -> &(K, P) {
            &self.entry
        }

        #[inline]
        fn is_leaf(&self) -> bool {
            self.left == bst::NIL && self.right == bst::NIL
        }
    }

    impl<K, P> bst::Node<K> for Node<K, P>
    where
        K: Ord + Copy,
        P: Ord + Copy,
    {
        #[inline]
        fn key(&self) -> &K {
            &self.entry.0
        }

        #[inline]
        fn left(&self) -> usize {
            self.left
        }

        #[inline]
        fn right(&self) -> usize {
            self.right
        }

        #[inline]
        fn parent(&self) -> usize {
            self.parent
        }

        #[inline]
        fn set_left(&mut self, l: usize) {
            self.left = l;
        }

        #[inline]
        fn set_parent(&mut self, p: usize) {
            self.parent = p;
        }

        #[inline]
        fn set_right(&mut self, r: usize) {
            self.right = r;
        }
    }

    #[derive(Debug, Clone)]
    pub struct Treap<K, P, const MAX_HEAP: bool>
    where
        K: Ord + Copy,
        P: Ord + Copy,
    {
        treap: Vec<Node<K, P>>,
        root: usize,
        sort_order: Ordering,
    }

    impl<K, P, const MAX_HEAP: bool> Default for Treap<K, P, MAX_HEAP>
    where
        K: Ord + Copy,
        P: Ord + Copy,
    {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<K, P, const MAX_HEAP: bool> Treap<K, P, MAX_HEAP>
    where
        K: Ord + Copy,
        P: Ord + Copy,
    {
        pub fn new() -> Self {
            Self {
                treap: Vec::new(),
                root: bst::NIL,
                sort_order: if MAX_HEAP {
                    Ordering::Greater
                } else {
                    Ordering::Less
                },
            }
        }

        pub fn with_capacity(capacity: usize) -> Self {
            Self {
                treap: Vec::with_capacity(capacity),
                root: bst::NIL,
                sort_order: if MAX_HEAP {
                    Ordering::Greater
                } else {
                    Ordering::Less
                },
            }
        }

        /// Returns true if the correct priority is on top of the treap.
        /// Please note that this function is intended for use during testing.
        ///
        /// ## Example:
        ///
        /// ```
        /// use rtreap::treap::Treap as TreapTrait;
        /// use rtreap::treap::basic::Treap;
        /// use std::cmp::Ordering;
        ///
        /// let mut v: Vec<usize> = Vec::new();
        /// let mut treap: Treap<usize, usize, false> = Treap::new();
        /// treap.insert(1, 234);
        /// treap.insert(333, 21);
        /// treap.insert(74, 12);
        /// treap.insert(559, 32);
        /// assert!(treap.heap_is_valid());
        /// ```
        #[doc(hidden)]
        pub fn heap_is_valid(&self) -> bool {
            if !self.treap.is_empty() {
                assert!(
                    self.root < self.treap.len(),
                    "the root {} is not found",
                    self.root
                );
                for i in 0..self.treap.len() {
                    if self.treap[i]
                        .priority()
                        .cmp(self.treap[self.root].priority())
                        == self.sort_order
                    {
                        return false;
                    }
                }
            }
            true
        }

        pub fn inorder<F>(&self, n: usize, callback: F)
        where
            F: Fn(&K),
        {
            bst::in_order(&self.treap, n, callback);
        }
    }

    impl<K, P, const MAX_HEAP: bool> super::Treap<K, P, MAX_HEAP> for Treap<K, P, MAX_HEAP>
    where
        K: Ord + Copy,
        P: Ord + Copy,
    {
        fn len(&self) -> usize {
            self.treap.len()
        }

        fn is_empty(&self) -> bool {
            self.treap.is_empty()
        }

        fn peek(&self) -> Option<&(K, P)> {
            if self.treap.is_empty() {
                None
            } else {
                Some(self.treap[self.root].entry())
            }
        }

        fn search(&self, key: &K) -> Option<&(K, P)> {
            if let Some(i) = bst::search(&self.treap, self.root, key) {
                Some(self.treap[i].entry())
            } else {
                None
            }
        }

        /// Inserts a new node containing `key` and `priority` into the treap.
        ///
        /// ## Examples:
        ///
        /// ```
        /// use rtreap::treap::Treap as TreapTrait;
        /// use rtreap::treap::basic::Treap;
        ///
        /// let mut treap: Treap<usize, usize, false> = Treap::new();
        /// assert!(treap.insert(123, 456).is_ok(), "Treap insertion failed.");
        /// ```
        fn insert(&mut self, key: K, priority: P) -> error::Result<()> {
            super::insert(
                &mut self.treap,
                &mut self.root,
                self.sort_order,
                Node::from((key, priority)),
            )
        }

        /*pub fn iter(&self) -> std::slice::Iter<'_, BasicNode<K, P>> {
            self.treap.iter()
        }*/

        fn remove(&mut self, key: &K) -> Option<(K, P)> {
            if let Some(i) = bst::search(&self.treap, self.root, key) {
                match super::remove(&mut self.treap, &mut self.root, self.sort_order, i) {
                    Ok(node) => Some(node.entry),
                    Err(_) => None,
                }
            } else {
                None
            }
        }

        fn update(&mut self, key: &K, new_priority: P) -> Option<P> {
            if let Some(index) = bst::search(&self.treap, self.root, key) {
                let old_priority: P = *self.treap[index].priority();
                self.treap[index].entry.1 = new_priority;
                if new_priority.cmp(&old_priority) == self.sort_order {
                    super::bubble_up(&mut self.treap, &mut self.root, self.sort_order, index);
                } else {
                    super::push_down(&mut self.treap, &mut self.root, self.sort_order, index);
                }
                Some(old_priority)
            } else {
                None
            }
        }

        fn top(&mut self) -> Option<(K, P)> {
            if self.treap.is_empty() {
                None
            } else {
                let i: usize = self.root;
                match super::remove(&mut self.treap, &mut self.root, self.sort_order, i) {
                    Ok(node) => Some(node.entry),
                    Err(_) => None,
                }
            }
        }
    }
}
