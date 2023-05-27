// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * Put crate documentation here...
 */

use std::cmp::Ordering;

#[derive(Debug, Copy, Clone)]
pub enum ErrorKind {
    RotationError,
    IndexOutOfBounds,
}

impl std::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ErrorKind::IndexOutOfBounds => f.write_str("Index out of bounds"),
            ErrorKind::RotationError => f.write_str("Rotation error"),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Error {
    kind: ErrorKind,
    message: &'static str,
}

impl Error {
    pub fn new(kind: ErrorKind, message: &'static str) -> Self {
        Self { kind, message }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{} {}", self.kind.to_string(), self.message))
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// Value used as a sentinel.
pub const NIL: usize = usize::MAX;

#[derive(Debug, Copy, Clone)]
pub struct Node<K, P>
where
    K: Copy + Eq + PartialEq + Ord,
    P: Copy + Eq + PartialEq + Ord,
{
    parent: usize,
    left: usize,
    right: usize,
    key: K,
    priority: P,
}

impl<K, P> Node<K, P>
where
    K: Copy + Eq + PartialEq + Ord,
    P: Copy + Eq + PartialEq + Ord,
{
    pub fn new(key: K, priority: P) -> Self {
        Self {
            parent: NIL,
            left: NIL,
            right: NIL,
            key,
            priority,
        }
    }

    pub fn is_leaf(&self) -> bool {
        if self.left == NIL && self.right == NIL {
            true
        } else {
            false
        }
    }

    pub fn is_root(&self) -> bool {
        self.parent == NIL
    }
}

#[derive(Debug, Clone)]
pub struct Treap<K, P, const MAX_HEAP: bool>
where
    K: Copy + Eq + PartialEq + Ord + std::fmt::Debug,
    P: Copy + Eq + PartialEq + Ord + std::fmt::Debug,
{
    treap: Vec<Node<K, P>>,
    root: usize,
    sort_order: Ordering,
}

impl<K, P, const MAX_HEAP: bool> Treap<K, P, MAX_HEAP>
where
    K: Copy + Eq + PartialEq + Ord + std::fmt::Debug,
    P: Copy + Eq + PartialEq + Ord + std::fmt::Debug,
{
    pub fn new() -> Self {
        Self {
            treap: Vec::new(),
            root: NIL,
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
            root: NIL,
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
            Some(&self.treap[self.root].priority)
        }
    }

    pub fn root(&self) -> usize {
        self.root
    }

    pub fn search(&self, key: &K) -> Option<usize> {
        let mut n: usize = self.root;
        while n < self.treap.len() {
            match key.cmp(&self.treap[n].key) {// self.treap[n].key.cmp(key) {
                Ordering::Equal => return Some(n),
                Ordering::Less => n = self.treap[n].left,
                Ordering::Greater => n = self.treap[n].right,
            };
        }
        None
    }

    fn rotate_right(&mut self, n: usize) {
        let treap_size: usize = self.treap.len();
        if n < treap_size {
            let l: usize = self.treap[n].left;
            if l < treap_size {
                let p: usize = self.treap[n].parent;
                self.treap[l].parent = p;
                if p < treap_size {
                    if n == self.treap[p].left {
                        self.treap[p].left = l;
                    } else {
                        self.treap[p].right = l;
                    }
                } else {
                    self.root = l;
                }
                self.treap[n].parent = l;
                let r: usize = self.treap[l].right;
                self.treap[n].left = r;
                if r < treap_size {
                    self.treap[r].parent = n;
                }
                self.treap[l].right = n;
            }
        }
    }

    fn rotate_left(&mut self, n: usize) {
        let treap_size: usize = self.treap.len();
        if n < treap_size {
            let r: usize = self.treap[n].right;
            if r < treap_size {
                let p: usize = self.treap[n].parent;
                self.treap[r].parent = p;
                if p < treap_size {
                    if n == self.treap[p].left {
                        self.treap[p].left = r;
                    } else {
                        self.treap[p].right = r;
                    }
                } else {
                    self.root = r;
                }
                self.treap[n].parent = r;
                let l: usize = self.treap[r].left;
                self.treap[n].right = l;
                if l < treap_size {
                    self.treap[l].parent = n;
                }
                self.treap[r].left = n;
            }
        }
    }

    /// Inserts a new node containing `key` and `priority` into the treap.
    ///
    /// ## Examples:
    ///
    /// ```
    /// use rtreap::{Treap, Node};
    ///
    /// let mut treap: Treap<usize, usize, false> = Treap::new();
    /// assert!(treap.insert(123, 456).is_ok(), "Treap insertion failed.");
    /// ```
    pub fn insert(&mut self, key: K, priority: P) -> Result<()> {
        let new_node: usize = self.treap.len();
        self.treap.push(Node::new(key, priority));
        if new_node == 0 {
            // new_node is the only node and the new root
            self.root = new_node;
        } else {
            // perform a BST insertion
            let mut node: usize = self.root;
            loop {
                if key <= self.treap[node].key {
                    if self.treap[node].left == NIL {
                        self.treap[node].left = new_node;
                        self.treap[new_node].parent = node;
                        break;
                    } else {
                        node = self.treap[node].left;
                    }
                } else {
                    if self.treap[node].right == NIL {
                        self.treap[node].right = new_node;
                        self.treap[new_node].parent = node;
                        break;
                    } else {
                        node = self.treap[node].right;
                    }
                }
            }
            // fix up the heap priorities
            while self.treap[new_node].parent != NIL
                && self.treap[new_node]
                    .priority
                    .cmp(&self.treap[self.treap[new_node].parent].priority)
                    == self.sort_order
            {
                let p: usize = self.treap[new_node].parent;
                if new_node == self.treap[p].right {
                    self.rotate_left(p);
                } else {
                    self.rotate_right(p);
                }
            }
        }
        Ok(())
    }

    fn swap_remove(&mut self, index: usize) -> Result<Node<K, P>> {
        let treap_size: usize = self.treap.len();
        if index < treap_size {
            let n: usize = self.treap.len() - 1; // get the index of the last node
            if n != index {
                let p: usize = self.treap[n].parent;
                let l: usize = self.treap[n].left;
                let r: usize = self.treap[n].right;
                if p < treap_size {
                    if self.treap[p].left == n {
                        self.treap[p].left = index;
                    } else {
                        self.treap[p].right = index;
                    }
                }
                if l < treap_size {
                    self.treap[l].parent = index;
                }
                if r < treap_size {
                    self.treap[r].parent = index;
                }
                if n == self.root {
                    self.root = index;
                }
            }
            Ok(self.treap.swap_remove(index))
        } else {
            Err(Error::new(ErrorKind::IndexOutOfBounds, ""))
        }
    }

    fn private_remove(&mut self, n: usize) -> Result<Node<K, P>> {
        if n >= self.treap.len() {
            Err(Error::new(
                ErrorKind::IndexOutOfBounds,
                "Index does not exist.",
            ))
        } else if self.treap.len() == 1 {
            self.root = NIL;
            Ok(self.treap.pop().expect("treap.pop() should never panic"))
        } else {
            while !self.treap[n].is_leaf() {
                if self.treap[n].left != NIL
                    && (self.treap[n].right == NIL
                        || self.treap[self.treap[n].left]
                            .priority
                            .cmp(&self.treap[self.treap[n].right].priority)
                            == self.sort_order)
                {
                    self.rotate_right(n);
                } else {
                    self.rotate_left(n);
                }
            }
            let p: usize = self.treap[n].parent;
            if self.treap[p].left == n {
                self.treap[p].left = NIL;
            } else {
                self.treap[p].right = NIL;
            }
            self.swap_remove(n)
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
    /// use rtreap::Treap;
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
            assert!(self.root < self.treap.len(), "the root {} is not found", self.root);
            for i in 0..self.treap.len() {
                if self.treap[i].priority.cmp(&self.treap[self.root].priority) == self.sort_order {
                    return false;
                }
            }
        }
        true
    }
}
