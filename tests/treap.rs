#[cfg(test)]
mod tests {
    use rand::prelude::*;
    use rtreap::treap::{BasicTreap, Treap as TreapTrait};
    use std::vec;

    const COUNT: usize = 1000;

    #[test]
    pub fn test_treap() {
        let mut treap: BasicTreap<usize, usize, false> = BasicTreap::new();
        let mut keys: Vec<usize> = vec![0; COUNT];
        rand::thread_rng().fill(&mut keys[..]);

        println!("{:?}", &treap);

        for key in keys.iter() {
            //let key = rand::thread_rng().gen_range(0..10000);
            let priority = rand::thread_rng().gen_range(0..10000);
            treap
                .insert(*key, priority)
                .expect("treap.insert() failed.");
            assert!(treap.is_valid(), "heap priorities violated after insertion");
        }

        //treap.inorder(0, print_key);

        for key in keys.iter() {
            treap.remove(key);
            if !treap.is_empty() {
                assert!(treap.is_valid(), "treap priorities violated");
            }
        }

        assert!(treap.len() == 0, "treap length is {} not zero", treap.len());

        //assert!(1==2);
    }
}
