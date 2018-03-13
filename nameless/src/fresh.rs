use std::fmt;

use AlphaEq;

/// A source of generated ids
pub struct FreshState {
    next_gen: u32,
}

impl FreshState {
    pub fn new() -> FreshState {
        FreshState { next_gen: 0 }
    }

    pub fn next_gen(&mut self) -> GenId {
        let next_gen = self.next_gen;
        self.next_gen += 1;
        GenId(next_gen)
    }
}

/// A generated id
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct GenId(u32);

impl AlphaEq for GenId {
    fn alpha_eq(&self, other: &GenId) -> bool {
        self == other
    }
}

impl fmt::Display for GenId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}
