use std::fmt;
use std::fmt::{Display, Formatter};

use crate::ast::{AstNode, AstNodeKind, AstRef, FunctionImplementation, Ident, LVal, TypeExpr};
use crate::capabilities::{CapabilityDeclaration, CapabilityExpr};
use crate::symbol_table::{Opacity, SymbolTable};
use crate::ty::Ty;
use crate::type_check::AssignabilityJudgment::NotAssignable;
use crate::type_constructors::TypeConstructor;
use bumpalo::Bump;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Mutex;

// TODO definitely gonna need to change this at some point...
pub type Name = &'static str;

pub struct TypeContext<'tc> {
    arenas: &'tc Arenas,
    interners: Interners<'tc>,
}

impl<'tc> TypeContext<'tc> {
    pub fn new(arenas: &'tc Arenas) -> TypeContext<'tc> {
        TypeContext {
            arenas,
            interners: Interners::new(arenas),
        }
    }

    pub(crate) fn intern_type_constructor(
        &'tc self,
        type_constructor: TypeConstructor,
    ) -> &'tc TypeConstructor {
        self.interners.type_constructors.intern(type_constructor)
    }

    pub(crate) fn intern_cap_decl(
        &'tc self,
        cap_decl: CapabilityDeclaration,
    ) -> &'tc CapabilityDeclaration {
        self.interners.capability_declarations.intern(cap_decl)
    }

    pub(crate) fn intern_cap_expr(
        &'tc self,
        cap_expr: CapabilityExpr<'tc>,
    ) -> &'tc CapabilityExpr<'tc> {
        self.interners.capability_expressions.intern(cap_expr)
    }

    pub(crate) fn intern_ty(&'tc self, ty: Ty<'tc>) -> &'tc Ty<'tc> {
        self.interners.tys.intern(ty)
    }

    pub(crate) fn lookup_type_constructor(&self, _name: Name) -> Option<&TypeConstructor> {
        unimplemented!("type constructor lookup in type context")
    }
}

#[derive(Default)]
pub struct Arenas {
    type_constructors: Bump,
    capability_declarations: Bump,
    capability_expressions: Bump,
    tys: Bump,
}

struct Interners<'tc> {
    type_constructors: InternedById<'tc, Name, TypeConstructor>,
    capability_declarations: InternedById<'tc, Name, CapabilityDeclaration>,
    capability_expressions: InternedBySet<'tc, CapabilityExpr<'tc>>,
    tys: InternedBySet<'tc, Ty<'tc>>,
}

impl<'tc> Interners<'tc> {
    fn new(arenas: &'tc Arenas) -> Interners<'tc> {
        Interners {
            type_constructors: InternedById::new(&arenas.type_constructors),
            capability_declarations: InternedById::new(&arenas.capability_declarations),
            capability_expressions: InternedBySet::new(&arenas.capability_expressions),
            tys: InternedBySet::new(&arenas.tys),
        }
    }
}

pub trait Identifiable<Id: Eq + PartialEq + Ord + PartialOrd + Hash> {
    fn get_id(&self) -> Id;
}

/// Intern values with some distinguishing ID, and deduplicate subsequent interns by comparing ID.
struct InternedById<'a, Id: Eq + PartialEq + Ord + PartialOrd + Hash, T: Identifiable<Id>> {
    arena: &'a Bump,
    map: Mutex<HashMap<Id, &'a T>>,
}

impl<'a, Id: Eq + PartialEq + Ord + PartialOrd + Hash, T: Identifiable<Id>>
    InternedById<'a, Id, T>
{
    fn new(arena: &'a Bump) -> InternedById<'a, Id, T> {
        InternedById {
            arena,
            map: Mutex::new(HashMap::default()),
        }
    }

    fn intern(&self, target: T) -> &T {
        let it = self.arena.alloc(target);
        let id = it.get_id();
        let mut map = self.map.lock().unwrap();
        map.insert(id, it);
        it
    }
}

/// Intern values, and deduplicate subsequent interns by comparing reference equality.
struct InternedBySet<'a, T: Eq + Hash> {
    arena: &'a Bump,
    set: Mutex<HashSet<&'a T>>,
}

impl<'a, T: Eq + Hash> InternedBySet<'a, T> {
    fn new(arena: &'a Bump) -> InternedBySet<'a, T> {
        InternedBySet {
            arena,
            set: Mutex::new(HashSet::default()),
        }
    }

    fn intern(&self, target: T) -> &T {
        let mut set = self.set.lock().unwrap();
        match set.get(&target) {
            Some(existing) => *existing,
            None => {
                let it = self.arena.alloc(target);
                set.insert(it);
                it
            }
        }
    }
}

pub(crate) trait Assignable
where
    Self: Display,
{
    // TODO some type context parameter probably needs to be threaded through here
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment;

    fn assignable_to(&self, to: &Self) -> AssignabilityJudgment {
        Assignable::assignable(self, to)
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub(crate) enum AssignabilityJudgment {
    Assignable,
    NotAssignable { reason: String },
}

impl AssignabilityJudgment {
    pub(crate) fn and<F>(&self, next: F) -> AssignabilityJudgment
    where
        F: Fn() -> AssignabilityJudgment,
    {
        use AssignabilityJudgment::*;
        match self {
            Assignable => next(),
            not_assignable => not_assignable.to_owned(),
        }
    }

    pub(crate) fn or<F>(&self, next: F) -> AssignabilityJudgment
    where
        F: Fn() -> AssignabilityJudgment,
    {
        use AssignabilityJudgment::*;
        match self {
            Assignable => Assignable,
            _ => next(),
        }
    }
}

impl Display for AssignabilityJudgment {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                AssignabilityJudgment::Assignable => "assignable",
                NotAssignable { reason } => reason.as_str(),
            }
        )
    }
}

impl AssignabilityJudgment {
    pub(crate) fn not_assignable(reason: String) -> AssignabilityJudgment {
        NotAssignable { reason }
    }

    pub(crate) fn is_assignable(&self) -> bool {
        match self {
            AssignabilityJudgment::Assignable => true,
            _ => false,
        }
    }
}

pub(crate) fn check_assign_or<A, F>(
    from1: &A,
    to1: &A,
    from2: &A,
    to2: &A,
    on_fail: F,
) -> AssignabilityJudgment
where
    A: Assignable,
    F: Fn(&AssignabilityJudgment, &AssignabilityJudgment) -> AssignabilityJudgment,
{
    use AssignabilityJudgment::*;
    match from1.assignable_to(to1) {
        Assignable => Assignable,
        lhs_not_assn => match from2.assignable_to(to2) {
            Assignable => Assignable,
            rhs_not_assn => on_fail(&lhs_not_assn, &rhs_not_assn),
        },
    }
}

pub(crate) fn check_assign_and<A, F>(
    from1: &A,
    to1: &A,
    from2: &A,
    to2: &A,
    on_fail: F,
) -> AssignabilityJudgment
where
    A: Assignable,
    F: Fn(&AssignabilityJudgment) -> AssignabilityJudgment,
{
    use AssignabilityJudgment::*;
    match from1.assignable_to(to1) {
        Assignable => match from2.assignable_to(to2) {
            Assignable => Assignable,
            not_assignable => on_fail(&not_assignable),
        },
        not_assignable => on_fail(&not_assignable),
    }
}

// TODO real error reporting
pub type TypeError = String;

/// A typing judgment is the result of type checking an AST node. If the node is well-typed, it will
/// return the WellTyped variant which carries the node's type, and if it's not, it'll return the TypeError
/// variant which carries a description of the error.
///
/// Both variants carry an Env pointer, which encapsulates the type of all variables in scope *after*
/// checking the node. This is important to thread through because visiting a node may refine the type
/// of a variable; that is, alter it somehow that all code after it in the flow control must take into
/// account.
///
/// For example, invoking a function may refine the capabilities of the arguments of the function.
/// Given a function:
/// ```nocap
/// fn doSomething(self: Foo<>[A]) -> () => self[+B] { /* ... */ }
/// ```
/// and a block:
/// ```nocap
/// {
///     let foo: Foo<>[A] = ...;
///     foo.doSomething();
/// }
/// ```
///
/// we know after invoking `doSomething()` that the type of `foo` has been refined to `Foo<>[A, B]`
/// because of the type of `doSomething()`. Thus, checking `doSomething()` would return a TypingJudgment
/// like `WellTyped((), { foo: Foo<>[A, B] })` which contains the result type of the expression `()`,
/// and a new environment reflecting the refined type of `foo`.
pub enum TypingJudgment<'tc> {
    WellTyped(&'tc Ty<'tc>, Env<'tc>),
    TypeError(TypeError, Env<'tc>),
}

/// Convert a TypingJudgment into a Result, discarding the environment.
impl<'tc> Into<Result<&'tc Ty<'tc>, TypeError>> for TypingJudgment<'tc> {
    fn into(self) -> Result<&'tc Ty<'tc>, TypeError> {
        match self {
            TypingJudgment::WellTyped(ty, _env) => Ok(ty),
            TypingJudgment::TypeError(reason, _env) => Err(reason),
        }
    }
}

impl<'tc> TypingJudgment<'tc> {
    /// Perform `action` iff `TypingJudgment` is `WellTyped`.
    /// `and_then` is essentially `>>=`, making `TypingJudgment` behave almost like a State monad over the environment.
    pub fn and_then<F>(self, mut action: F) -> TypingJudgment<'tc>
    where
        F: FnMut(&'tc Ty<'tc>, Env<'tc>) -> TypingJudgment<'tc>,
    {
        match self {
            TypingJudgment::WellTyped(ty, env) => action(ty, env),
            TypingJudgment::TypeError(_, _) => self,
        }
    }
}

/// Do something returning Result<&Ty, TypeError>, returning &Ty on success and returning early with
/// TypingJudgment::TypeError(err, env) on error
macro_rules! ty_try {
    ($env:ident, $body:expr) => {{
        match $body {
            Ok(ty) => ty,
            Err(err) => return TypingJudgment::TypeError(err, $env),
        }
    }};
}

macro_rules! tj_try {
    ($exp:expr, $t:ident, $env:ident, $body:expr) => {{
        match $exp {
            TypingJudgment::WellTyped($t, $env) => $body,
            err => return err,
        }
    }};
}

struct TypeChecker<'tc> {
    type_context: &'tc TypeContext<'tc>,
    local_context: LocalContext,
}

type Env<'tc> = Rc<Environment<'tc>>;

impl<'tc> TypeChecker<'tc> {
    pub fn check(&mut self, ast_ref: AstRef) -> TypingJudgment<'tc> {
        let initial_env = Rc::new(Environment::new());
        self.check_node(&*ast_ref, initial_env)
    }

    fn check_func_impl(
        &mut self,
        func_impl: &FunctionImplementation,
        env: Env<'tc>,
    ) -> TypingJudgment<'tc> {
        self.check_node(&func_impl.body, env)
    }

    fn check_node(&mut self, node: &AstNode, env: Env<'tc>) -> TypingJudgment<'tc> {
        match &node.kind {
            AstNodeKind::VarRef(ident) => self.check_var_ref(ident, env),
            AstNodeKind::VarDecl(lhs, ty, rhs) => self.check_assign(lhs, ty, rhs, env),
            AstNodeKind::Block(exprs) => self.check_block(exprs, env),
            _ => unimplemented!("haven't implemented type checking for {}", node),
        }
    }

    fn check_var_ref(&mut self, ident: &Ident, env: Env<'tc>) -> TypingJudgment<'tc> {
        self.local_context
            .symbols
            .lookup(&ident.name)
            .and_then(|var| env.lookup(var))
            .map_or_else(
                || {
                    TypingJudgment::TypeError(
                        format!("variable not in scope: {}", ident.name),
                        env.clone(),
                    )
                },
                |ty| TypingJudgment::WellTyped(ty, env.clone()),
            )
    }

    fn check_assign(
        &mut self,
        lhs: &AstNode,
        ty: &TypeExpr,
        rhs: &AstNode,
        env: Env<'tc>,
    ) -> TypingJudgment<'tc> {
        self.check_node(rhs, env)
            .and_then(|rhs_ty, env| match &lhs.kind {
                AstNodeKind::LVal(lval) => match lval {
                    LVal::Variable(name) => {
                        let ty = ty_try!(env, Ty::from_type_expr(ty, self.type_context));
                        if let NotAssignable { reason } = rhs_ty.assignable_to(ty) {
                            return TypingJudgment::TypeError(reason, env);
                        }
                        self.local_context.symbols.bind(
                            name.name,
                            ScopedVar {
                                name: name.name,
                                depth: self.local_context.symbols.depth(),
                            },
                        );
                        let new_env =
                            env.refine(self.local_context.symbols.lookup(&name.name).unwrap(), ty);
                        TypingJudgment::WellTyped(ty, new_env)
                    }
                },
                _ => TypingJudgment::TypeError(format!("not an lval: {}", lhs), env),
            })
    }

    fn check_block(&mut self, exprs: &Vec<AstRef>, env: Env<'tc>) -> TypingJudgment<'tc> {
        match exprs.split_last() {
            Some((last, others)) => {
                let outer_env = env.clone();
                let mut curr_env = env.clone();
                let block_tj =
                    with_frame!(&mut self.local_context.symbols, Opacity::Transparent, {
                        for expr in others.iter() {
                            tj_try!(self.check_node(expr, curr_env.clone()), _ty, next_env, {
                                curr_env = next_env.clone();
                            });
                        }
                        self.check_node(last, curr_env.clone())
                    });
                tj_try!(block_tj, last_expr_ty, last_expr_env, {
                    let outgoing_env = last_expr_env.preserving_refinements_of_outer_vars(
                        outer_env.clone(),
                        self.local_context.symbols.depth(),
                    );
                    TypingJudgment::WellTyped(last_expr_ty, outgoing_env)
                })
            }
            None => TypingJudgment::TypeError("block has nothing in it".to_owned(), env.clone()),
        }
    }
}

/// which variables are visible, and what the frame depth was when they were encountered. the depth
/// allows us to distinguish between shadowed variables. eg, if `x` is shadowed, there'll be a binding
/// to `n`, and then once the shadowing frame it popped, it'll be bound to `n - 1`
type VariableScope = SymbolTable<Name, ScopedVar>;

#[derive(Default)]
struct LocalContext {
    symbols: VariableScope,
}

impl LocalContext {
    fn new() -> Self {
        Self::default()
    }
}

/// A variable's name, along with the depth of the scope that defined it. That lets us distinguish between
/// various incarnations of a shadowed variable.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone)]
struct ScopedVar {
    name: Name,
    depth: usize,
}

type Refinements<'tc> = HashMap<ScopedVar, &'tc Ty<'tc>>;

/// A linked list of frames which refine the type of variables.
/// TODO this could certainly be made a lot more efficient, going for ease of use to start
#[derive(Clone)]
pub struct Environment<'tc> {
    previous: Option<Env<'tc>>,
    refinements: Refinements<'tc>,
}

impl<'tc> Environment<'tc> {
    fn new() -> Environment<'tc> {
        Environment {
            previous: None,
            refinements: HashMap::default(),
        }
    }

    fn refine(self: Rc<Environment<'tc>>, var: &ScopedVar, ty: &'tc Ty<'tc>) -> Env<'tc> {
        let mut map = Refinements::with_capacity(1);
        map.insert(*var, ty);
        self.refine_map(map)
    }

    fn refine_map(self: Env<'tc>, refinements: Refinements<'tc>) -> Env<'tc> {
        Rc::new(Environment {
            previous: Some(self.clone()),
            refinements,
        })
    }

    fn lookup(self: &Env<'tc>, var: &ScopedVar) -> Option<&'tc Ty<'tc>> {
        if let Some(ty) = self.refinements.get(var) {
            Some(ty)
        } else if let Some(prev) = &self.previous {
            prev.lookup(var)
        } else {
            None
        }
    }

    /// returns an environment which builds on `outer_env` and preserves all refinements from `self`
    /// for ScopedVars with depth <= max_depth. This is useful for when an inner scope (self) may have refined
    /// the type of a var from an outer scope, and we want to preserve that refinement even after
    /// the inner scope is closed.
    fn preserving_refinements_of_outer_vars(
        self: &Env<'tc>,
        outer_env: Env<'tc>,
        max_depth: usize,
    ) -> Env<'tc> {
        let mut curr_env = &Some(self.clone());
        let mut new_refinements = Refinements::new();
        while let Some(e) = curr_env {
            for (var, ty) in e.refinements.iter() {
                if var.depth <= max_depth {
                    new_refinements.insert(*var, ty);
                }
            }
            curr_env = &e.previous;
        }

        Rc::new(Environment {
            previous: Some(outer_env.clone()),
            refinements: new_refinements,
        })
    }
}

#[cfg(test)]
pub(crate) mod test_utils {
    use crate::type_check::{AssignabilityJudgment, Assignable};

    pub(crate) fn assert_assignable_to<T: Assignable>(lhs: &T, rhs: &T) {
        match lhs.assignable_to(rhs) {
            AssignabilityJudgment::Assignable => return,
            AssignabilityJudgment::NotAssignable { reason } => {
                panic!(
                    "Expected {} to be assignable to {}, but wasn't because {}",
                    lhs, rhs, reason
                )
            }
        }
    }

    pub(crate) fn assert_not_assignable_to<T: Assignable>(lhs: &T, rhs: &T) {
        match lhs.assignable_to(rhs) {
            AssignabilityJudgment::NotAssignable { .. } => return,
            AssignabilityJudgment::Assignable => {
                panic!(
                    "Expected {} not to be assignable to {}, but it was.",
                    lhs, rhs
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test() {}
}
