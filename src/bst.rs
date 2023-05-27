// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

use crate::error::{Error, ErrorKind, Result};
use std::cmp::Ordering;

/// Value used as a sentinel.
pub const NIL: usize = usize::MAX;

pub trait Node<K>
where
    Self: Sized,
{
    fn parent(&self) -> usize;
    fn left(&self) -> usize;
    fn right(&self) -> usize;
    fn set_parent(&mut self, p: usize);
    fn set_left(&mut self, l: usize);
    fn set_right(&mut self, r: usize);
    fn key(&self) -> &K;
}

pub fn insert<K, T>(tree: &mut Vec<T>, root: &mut usize, node: T) -> usize
where
    T: Node<K>,
    K: Ord + Copy,
{
    let new_node: usize = tree.len();
    tree.push(node);
    if new_node == 0 {
        // new_node is the only node and the new root
        *root = new_node;
    } else {
        // perform a BST insertion
        let mut n: usize = *root;
        loop {
            if tree[new_node].key().cmp(tree[n].key()) == Ordering::Greater {
                if tree[n].right() == NIL {
                    tree[n].set_right(new_node);
                    tree[new_node].set_parent(n);
                    break;
                } else {
                    n = tree[n].right();
                }
            } else if tree[n].left() == NIL {
                tree[n].set_left(new_node);
                tree[new_node].set_parent(n);
                break;
            } else {
                n = tree[n].left();
            }
        }
    }
    new_node
}

pub fn search<K, T>(tree: &[T], mut node: usize, key: &K) -> Option<usize>
where
    K: Ord,
    T: Node<K>,
{
    while node < tree.len() {
        match key.cmp(tree[node].key()) {
            Ordering::Equal => return Some(node),
            Ordering::Less => node = tree[node].left(),
            Ordering::Greater => node = tree[node].right(),
        };
    }
    None
}

pub fn rotate_right<K, T>(tree: &mut [T], root: &mut usize, node: usize)
where
    T: Node<K>,
{
    let treap_size: usize = tree.len();
    if node < treap_size {
        let l: usize = tree[node].left();
        if l < treap_size {
            let p: usize = tree[node].parent();
            tree[l].set_parent(p);
            if p < treap_size {
                if node == tree[p].left() {
                    tree[p].set_left(l);
                } else {
                    tree[p].set_right(l);
                }
            } else {
                *root = l;
            }
            tree[node].set_parent(l);
            let r: usize = tree[l].right();
            tree[node].set_left(r);
            if r < treap_size {
                tree[r].set_parent(node);
            }
            tree[l].set_right(node);
        }
    }
}

pub fn rotate_left<K, T>(tree: &mut [T], root: &mut usize, node: usize)
where
    T: Node<K>,
{
    let treap_size: usize = tree.len();
    if node < treap_size {
        let r: usize = tree[node].right();
        if r < treap_size {
            let p: usize = tree[node].parent();
            tree[r].set_parent(p);
            if p < treap_size {
                if node == tree[p].left() {
                    tree[p].set_left(r);
                } else {
                    tree[p].set_right(r);
                }
            } else {
                *root = r;
            }
            tree[node].set_parent(r);
            let l: usize = tree[r].left();
            tree[node].set_right(l);
            if l < treap_size {
                tree[l].set_parent(node);
            }
            tree[r].set_left(node);
        }
    }
}

pub fn swap_remove<K, T>(tree: &mut Vec<T>, root: &mut usize, index: usize) -> Result<T>
where
    T: Node<K>,
{
    let treap_size: usize = tree.len();
    if index < treap_size {
        let n: usize = treap_size - 1; // get the index of the last node
        if n != index {
            let p: usize = tree[n].parent();
            let l: usize = tree[n].left();
            let r: usize = tree[n].right();
            if p < treap_size {
                if tree[p].left() == n {
                    tree[p].set_left(index);
                } else {
                    tree[p].set_right(index);
                }
            }
            if l < treap_size {
                tree[l].set_parent(index);
            }
            if r < treap_size {
                tree[r].set_parent(index);
            }
            if n == *root {
                *root = index;
            }
        }
        Ok(tree.swap_remove(index))
    } else {
        Err(Error::new(
            ErrorKind::IndexOutOfBounds,
            "swap_remove() failed because ",
        ))
    }
}

pub fn inorder<K, F, T>(tree: &[T], mut node: usize, callback: F)
where
    F: Fn(&T),
    T: Node<K>,
{
    let mut prev: usize = node;
    while node < tree.len() {
        if tree[node].right() != prev {
            if tree[node].left() != prev {
                while tree[node].left() != NIL {
                    node = tree[node].left();
                }
            }
            callback(&tree[node]);
            if tree[node].right() != NIL {
                node = tree[node].right();
                loop {
                    while tree[node].left() != NIL {
                        node = tree[node].left();
                    }
                    callback(&tree[node]);
                    if tree[node].right() != NIL {
                        node = tree[node].right();
                    } else {
                        break;
                    }
                }
            }
        }
        prev = node;
        node = tree[node].parent();
    }
}

pub fn preorder<K, F, T>(tree: &[T], mut node: usize, callback: F)
where
    F: Fn(&T),
    T: Node<K>,
{
    let mut prev = node;
    while node != NIL {
        //go down the tree
        if tree[node].right() != prev {
            if tree[node].left() != prev {
                callback(&tree[node]);
                while tree[node].left() != NIL {
                    node = tree[node].left();
                    callback(&tree[node]);
                }
            }
            if tree[node].right() != NIL {
                node = tree[node].right();
                callback(&tree[node]);
                loop {
                    while tree[node].left() != NIL {
                        node = tree[node].left();
                        callback(&tree[node]);
                    }
                    if tree[node].right() != NIL {
                        node = tree[node].right();
                        callback(&tree[node]);
                    } else {
                        break;
                    }
                }
            }
        }
        //go up the tree
        prev = node;
        node = tree[node].parent();
    }
}

pub fn postorder<K, F, T>(tree: &[T], mut node: usize, callback: F)
where
    F: Fn(&T),
    T: Node<K>,
{
    let mut prev = node;
    while node != NIL {
        if tree[node].right() != prev {
            if tree[node].left() != prev {
                while tree[node].left() != NIL {
                    node = tree[node].left()
                }
            }
            if tree[node].right() != NIL {
                node = tree[node].right();
                loop {
                    while tree[node].left() != NIL {
                        node = tree[node].left()
                    }
                    if tree[node].right() != NIL {
                        node = tree[node].right();
                    } else {
                        break;
                    }
                }
            }
        }
        callback(&tree[node]);
        prev = node;
        node = tree[node].parent();
    }
}

/*

struct Trunk {
    prev: usize,
    text: &'static str,
}

fn showTrunks(trunk: &Trunk) {
    showTrunks(&trunk.prev);
    print!("{}", trunk.s);
}

fn print_tree<K>(tree: &[dyn Node<K>], root: usize, prev: Option<Trunk>, isLeft: bool) {
    if root < tree.len() {
        let prev_str: &'static str = "    ";
        let trunk = Trunk {
            prev,
            text: prev_str,
        };

        print_tree(tree, tree[root].left, Some(trunk), true);

        if prev.is_none() {
            trunk.text = "----";
        } else if isLeft {
            trunk.text = ",---";
            prev_str = "   |";
        } else {
            trunk.text = "`---";
            prev.text = prev_str;
        }

        showTrunks(&trunk);
        print!("{}", root);

        if (prev) {
            prev.text = prev_str;
        }
        trunk.text = "   |";

        print_tree(tree, tree[root].right, Some(trunk), false);
    }
}

pub fn print_bst<K>(tree: &[Node<K>], root: usize) {
    if root < tree.len() {
        print_tree(tree, root, None, false);
        println!();
    }
}
*/
