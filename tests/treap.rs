#[cfg(test)]
mod tests {
    use std::vec;

    use rand::prelude::*;
    use rtreap::Treap;

    const COUNT: usize = 3000;

    #[test]
    pub fn test_treap() {
        let mut treap: Treap<usize, usize, false> = Treap::new();
        let mut keys: Vec<usize> = vec![0; COUNT];
        rand::thread_rng().fill(&mut keys[..]);

        println!("{:?}", &treap);

        for key in keys.iter() {
            //let key = rand::thread_rng().gen_range(0..10000);
            let priority = rand::thread_rng().gen_range(0..10000);
            treap
                .insert(*key, priority)
                .expect("treap.insert() failed.");
            assert!(treap.heap_is_valid(), "heap priorities violated after insertion");
        }

        println!("root = {}", treap.root());
        for (i, node) in treap.iter().enumerate() {
            println!("{} {:?}", i, node);
        }
        println!();

        for key in keys.iter() {
            treap.remove(key);
            println!("root = {}", treap.root());
            for (i, node) in treap.iter().enumerate() {
                println!("{} {:?}", i, node);
            }
            println!();
            assert!(treap.heap_is_valid(), "heap priorities violated");
        }

        assert!(treap.len() == 0, "treap length is {} not zero", treap.len());
    }
}
