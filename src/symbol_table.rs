use std::collections::HashMap;
use std::hash::Hash;

/// A symbol table, tracking visible things as scopes are pushed and popped.
///
/// A symbol table is essentially a stack of individual frames, each of which contains many bindings
/// from `K` to `V`. Each frame must have unique keys, but frames may bind the same key as a frame
/// below it; when looking up that key, the value from the top most frame will be chosen.
///
/// Frames come in two flavors, `Opaque` and `Transparent`. `Opaque` frames prevent lookups from proceeding
/// further down the stack, and are useful for things like entering a new method, where any variables
/// in the stack above it are no longer visible. `Transparent` frames are useful for things like blocks,
/// where a new set of bindings can be introduced that may shadow existing bindings, but their scope
/// is limited and they will be popped off and the previous bindings restored.
#[derive(Clone)]
pub struct SymbolTable<K: Eq + Hash, V> {
    // TODO parallel key/value arrays with frame trackers for efficiency
    frames: Vec<Frame<K, V>>,
}

impl<K: Eq + Hash, V> Default for SymbolTable<K, V> {
    fn default() -> Self {
        SymbolTable::new()
    }
}

/// perform `$action` inside of a freshly pushed frame with opacity `$opacity`.
macro_rules! with_frame {
    ($symbol_table:expr, $opacity:expr, $action:expr) => {{
        // TODO want to use scope_guard to ensure pop_frame() gets called, but it doesn't work when $symbol_table and $action both mutably borrow `self`.
        ($symbol_table).push_frame($opacity);
        let result = $action;
        ($symbol_table).pop_frame();
        result
    }};
}

impl<K: Eq + Hash, V> SymbolTable<K, V> {
    pub fn new() -> SymbolTable<K, V> {
        SymbolTable { frames: Vec::new() }
    }

    pub fn lookup(&self, key: &K) -> Option<&V> {
        let mut iter = self.frames.iter().rev();

        loop {
            match iter.next() {
                Some(curr_frame) => {
                    if let Some(v) = curr_frame.lookup(key) {
                        return Some(v);
                    }

                    if curr_frame.opacity == Opacity::Opaque {
                        return None;
                    }
                }
                None => return None,
            }
        }
    }

    pub fn bind(&mut self, key: K, value: V) -> Option<V> {
        self.frames.last_mut().and_then(|f| f.bind(key, value))
    }

    pub fn push_frame(&mut self, opacity: Opacity) {
        self.frames.push(Frame::new(opacity))
    }

    pub fn pop_frame(&mut self) {
        self.frames.pop();
    }

    /// Current depth of frames. Useful for distingiushing between incarnations of a shadowed variable.
    pub fn depth(&self) -> usize {
        self.frames.len()
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone)]
pub enum Opacity {
    Opaque,
    Transparent,
}

impl Default for Opacity {
    fn default() -> Self {
        Opacity::Opaque
    }
}

#[derive(Clone)]
struct Frame<K: Eq + Hash, V> {
    bindings: HashMap<K, V>,
    opacity: Opacity,
}

impl<K: Eq + Hash, V> Frame<K, V> {
    fn new(opacity: Opacity) -> Frame<K, V> {
        Frame {
            bindings: HashMap::new(),
            opacity,
        }
    }

    fn bind(&mut self, key: K, value: V) -> Option<V> {
        self.bindings.insert(key, value)
    }

    fn lookup(&self, key: &K) -> Option<&V> {
        self.bindings.get(key)
    }
}

impl<K: Eq + Hash, V> Default for Frame<K, V> {
    fn default() -> Self {
        Frame::new(Opacity::default())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test() {}
}
