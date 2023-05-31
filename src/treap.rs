// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * Put crate documentation here...
 */

use crate::bst; //::{inorder, rotate_left, rotate_right, search, swap_remove, Node, NIL};
use crate::error::{Error, ErrorKind, Result};
use std::cmp::Ordering;

#[derive(Debug, Clone, Copy)]
pub struct Node<K, P>
where
    K: Ord + Copy,
    P: Ord + Copy,
{
    parent: usize,
    left: usize,
    right: usize,
    key: K,
    priority: P,
}

impl<K, P> Node<K, P>
where
    K: Ord + Copy,
    P: Ord + Copy,
{
    pub fn new(key: K, priority: P) -> Self {
        Self {
            parent: bst::NIL,
            left: bst::NIL,
            right: bst::NIL,
            key,
            priority,
        }
    }

    #[inline]
    pub fn priority(&self) -> &P {
        &self.priority
    }

    #[inline]
    pub fn is_leaf(&self) -> bool {
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
        &self.key
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

    pub fn len(&self) -> usize {
        self.treap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.treap.is_empty()
    }

    pub fn peek(&self) -> Option<&P> {
        if self.treap.is_empty() {
            None
        } else {
            Some(self.treap[self.root].priority())
        }
    }

    pub fn root(&self) -> usize {
        self.root
    }

    pub fn search(&self, key: &K) -> Option<usize> {
        bst::search(&self.treap, self.root, key)
    }

    /// Inserts a new node containing `key` and `priority` into the treap.
    ///
    /// ## Examples:
    ///
    /// ```
    /// use rtreap::treap::{Treap, Node};
    ///
    /// let mut treap: Treap<usize, usize, false> = Treap::new();
    /// assert!(treap.insert(123, 456).is_ok(), "Treap insertion failed.");
    /// ```
    pub fn insert(&mut self, key: K, priority: P) -> Result<()> {
        let new_node: usize =
            bst::insert(&mut self.treap, &mut self.root, Node::new(key, priority)).or(Err(
                Error::new(ErrorKind::IndexOutOfBounds, "Key already exists."),
            ))?;
        // fix up the heap priorities
        while self.treap[new_node].parent != bst::NIL
            && self.treap[new_node]
                .priority
                .cmp(&self.treap[self.treap[new_node].parent].priority)
                == self.sort_order
        {
            let p: usize = self.treap[new_node].parent;
            if new_node == self.treap[p].right {
                bst::rotate_left(&mut self.treap, &mut self.root, p);
            } else {
                bst::rotate_right(&mut self.treap, &mut self.root, p);
            }
        }
        Ok(())
    }

    fn private_remove(&mut self, n: usize) -> Result<Node<K, P>> {
        if n >= self.treap.len() {
            Err(Error::new(
                ErrorKind::IndexOutOfBounds,
                "Index does not exist.",
            ))
        } else if self.treap.len() == 1 {
            self.root = bst::NIL;
            Ok(self.treap.pop().expect("treap.pop() should never panic"))
        } else {
            while !self.treap[n].is_leaf() {
                if self.treap[n].left != bst::NIL
                    && (self.treap[n].right == bst::NIL
                        || self.treap[self.treap[n].left]
                            .priority
                            .cmp(&self.treap[self.treap[n].right].priority)
                            == self.sort_order)
                {
                    bst::rotate_right(&mut self.treap, &mut self.root, n);
                } else {
                    bst::rotate_left(&mut self.treap, &mut self.root, n);
                }
            }
            let p: usize = self.treap[n].parent;
            if self.treap[p].left == n {
                self.treap[p].left = bst::NIL;
            } else {
                self.treap[p].right = bst::NIL;
            }
            bst::swap_remove(&mut self.treap, &mut self.root, n)
        }
    }

    pub fn update(&mut self) -> Result<()> {
        Ok(())
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Node<K, P>> {
        self.treap.iter()
    }

    pub fn remove(&mut self, key: &K) -> Option<Node<K, P>> {
        if let Some(index) = self.search(key) {
            self.private_remove(index).ok()
        } else {
            None
        }
    }

    pub fn top(&mut self) -> Option<Node<K, P>> {
        if self.treap.is_empty() {
            None
        } else {
            self.private_remove(self.root).ok()
        }
    }

    /// Returns true if the correct priority is on top of the treap.
    /// Please note that this function is intended for use during testing.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::Treap;
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
                if self.treap[i].priority.cmp(&self.treap[self.root].priority) == self.sort_order {
                    return false;
                }
            }
        }
        true
    }

    pub fn inorder<F>(&self, n: usize, callback: F)
    where
        F: Fn(&Node<K, P>),
    {
        bst::inorder(&self.treap, n, callback);
    }
}
