
use std::hash::BuildHasherDefault;

use fnv::FnvHasher;
use std::collections::HashMap;
pub type HashMapFnv<K, V> = HashMap<K, V, BuildHasherDefault<FnvHasher>>;

macro_rules! hashmap {
    ($( $key: expr => $val: expr ),*) => {{
        let mut map = HashMapFnv::default();
        $( map.insert($key, $val); )*
        map
    }}
}

// This must exist somewhere already...
pub fn join<S: AsRef<str>, I: Iterator<Item=S>>(iter: I, sep: &str) -> String {
    let mut r = String::new();
    let mut first = true;
    for s in iter {
        if !first {
            r.push_str(sep);
        }
        first = false;
        r.push_str(s.as_ref());
    }
    r
}

pub fn enumerate_bool_vecs(n: usize, max_count: usize) -> Vec<Vec<bool>> {
    assert!(n > 0 && n < 32);
    let mut ret = vec![];

    for i in 0..(1 << n) {
        let mut set = vec![false; n];
        for bit in 0..n {
            if ((i >> bit) & 1) == 1 {
                set[bit] = true;
            }
        }
        ret.push(set.clone());
        if ret.len() >= max_count {
            break;
        }
    }

    ret
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::usize;

    #[test]
    fn test_enumerate_bool_vecs() {
        assert_eq!(enumerate_bool_vecs(1, usize::MAX), vec![
            vec![false], vec![true]
        ]);
        assert_eq!(enumerate_bool_vecs(2, usize::MAX), vec![
            vec![false, false], vec![true, false], vec![false, true], vec![true, true]
        ]);
        assert_eq!(enumerate_bool_vecs(3, usize::MAX), vec![
            vec![false, false, false], vec![true, false, false],
            vec![false, true, false], vec![true, true, false],
            vec![false, false, true], vec![true, false, true],
            vec![false, true, true], vec![true, true, true]
        ]);
    }
}
