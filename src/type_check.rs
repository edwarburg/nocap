use std::fmt;
use std::fmt::{Display, Formatter};

use crate::ast;
use crate::ast::{
    AstNode, CompilationUnit, CompilationUnitKind, Expr, ExprKind, FunctionImplementation, Ident,
    ItemKind, Stmt, StmtKind, R,
};
use crate::capabilities::{CapabilityDeclaration, CapabilityExpr};
use crate::symbol_table::{Opacity, SymbolTable};

use crate::func_decls::FunctionDeclaration;
use crate::ty::Ty;
use crate::type_check::AssignabilityJudgment::NotAssignable;
use crate::type_constructors::TypeConstructor;
use bumpalo::Bump;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Mutex;

// TODO definitely gonna need to change this at some point...
pub type Name = &'static str;

pub struct TypeContext<'tc> {
    pub arenas: &'tc Arenas,
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

    pub(crate) fn lookup_type_constructor(&self, name: Name) -> Option<&TypeConstructor> {
        self.interners.type_constructors.lookup(name)
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

    pub(crate) fn intern_func_ty(
        &'tc self,
        func_decl: FunctionDeclaration<'tc>,
    ) -> &'tc FunctionDeclaration<'tc> {
        self.interners.func_decls.intern(func_decl)
    }

    pub(crate) fn lookup_func_decl(&'tc self, name: Name) -> Option<&'tc FunctionDeclaration<'tc>> {
        self.interners.func_decls.lookup(name)
    }
}

#[derive(Default)]
pub struct Arenas {
    type_constructors: Bump,
    capability_declarations: Bump,
    capability_expressions: Bump,
    tys: Bump,
    func_decls: Bump,
}

struct Interners<'tc> {
    type_constructors: InternedById<'tc, Name, TypeConstructor>,
    capability_declarations: InternedById<'tc, Name, CapabilityDeclaration>,
    capability_expressions: InternedBySet<'tc, CapabilityExpr<'tc>>,
    tys: InternedBySet<'tc, Ty<'tc>>,
    func_decls: InternedById<'tc, Name, FunctionDeclaration<'tc>>,
}

impl<'tc> Interners<'tc> {
    fn new(arenas: &'tc Arenas) -> Interners<'tc> {
        Interners {
            type_constructors: InternedById::new(&arenas.type_constructors),
            capability_declarations: InternedById::new(&arenas.capability_declarations),
            capability_expressions: InternedBySet::new(&arenas.capability_expressions),
            tys: InternedBySet::new(&arenas.tys),
            func_decls: InternedById::new(&arenas.func_decls),
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

    fn lookup(&self, id: Id) -> Option<&T> {
        let map = self.map.lock().unwrap();
        map.get(&id).map(|t| *t)
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
    // TODO ty to use for error recovery?
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

impl<'tc> Display for TypingJudgment<'tc> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypingJudgment::WellTyped(ty, _) => {
                write!(f, "WellTyped({})", ty)
            }
            TypingJudgment::TypeError(err, _) => {
                write!(f, "TypeErr({})", err)
            }
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

    fn is_well_typed(&self) -> bool {
        match self {
            TypingJudgment::WellTyped(_, _) => true,
            _ => false,
        }
    }

    fn is_type_error(&self) -> bool {
        match self {
            TypingJudgment::TypeError(_, _) => true,
            _ => false,
        }
    }

    fn env(&self) -> Env<'tc> {
        match self {
            TypingJudgment::WellTyped(_, env) => env.clone(),
            TypingJudgment::TypeError(_, env) => env.clone(),
        }
    }

    fn replacing_env(self, new_env: Env<'tc>) -> TypingJudgment<'tc> {
        match self {
            TypingJudgment::WellTyped(ty, _old_env) => {
                TypingJudgment::WellTyped(ty, new_env.clone())
            }
            TypingJudgment::TypeError(err, _old_env) => {
                TypingJudgment::TypeError(err.clone(), new_env.clone())
            }
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

pub enum TypeCheckerResult<'tc> {
    Ok {
        final_env: Env<'tc>,
    },
    Err {
        final_env: Env<'tc>,
        item_results: Vec<TypingJudgment<'tc>>,
    },
}

impl<'tc> TypeCheckerResult<'tc> {
    fn is_ok(&self) -> bool {
        match self {
            TypeCheckerResult::Ok { .. } => true,
            _ => false,
        }
    }

    fn is_err(&self) -> bool {
        match self {
            TypeCheckerResult::Err { .. } => true,
            _ => false,
        }
    }

    fn final_env(&'tc self) -> Env<'tc> {
        match self {
            TypeCheckerResult::Ok { final_env, .. } => final_env.clone(),
            TypeCheckerResult::Err { final_env, .. } => final_env.clone(),
        }
    }
}

impl<'tc> Into<Result<(), Vec<TypingJudgment<'tc>>>> for TypeCheckerResult<'tc> {
    fn into(self) -> Result<(), Vec<TypingJudgment<'tc>>> {
        match self {
            TypeCheckerResult::Ok { .. } => Result::Ok(()),
            TypeCheckerResult::Err { item_results, .. } => Result::Err(item_results),
        }
    }
}

impl<'tc> TypeChecker<'tc> {
    fn check_compilation_unit(&mut self, unit: &CompilationUnit) -> TypeCheckerResult<'tc> {
        match &unit.kind {
            CompilationUnitKind::File(items) => {
                let mut item_results: Vec<TypingJudgment<'tc>> = Vec::with_capacity(items.len());
                for item in items {
                    match &item.kind {
                        ItemKind::FuncDecl(_) => {
                            unimplemented!("TODO add func signature to type context");
                        }
                        ItemKind::FuncDeclWithImpl(_, func_impl) => {
                            // TODO add func signature to type context
                            let result =
                                self.check_func_impl(func_impl, Rc::new(Environment::new()));
                            item_results.push(result);
                        }
                    }
                }

                let final_env = item_results.iter().last().unwrap().env().clone();

                if item_results.iter().all(|result| result.is_well_typed()) {
                    TypeCheckerResult::Ok { final_env }
                } else {
                    TypeCheckerResult::Err {
                        item_results,
                        final_env,
                    }
                }
            }
        }
    }

    fn check_func_impl(
        &mut self,
        func_impl: &FunctionImplementation,
        env: Env<'tc>,
    ) -> TypingJudgment<'tc> {
        self.check_expr(&func_impl.body, env)
    }

    fn check_stmt(&mut self, stmt: &Stmt, env: Env<'tc>) -> TypingJudgment<'tc> {
        match &stmt.kind() {
            StmtKind::VarDecl(lhs, ty, rhs) => self.check_var_decl(lhs, ty, rhs, env),
            StmtKind::Expr(expr) => self.check_expr(expr, env),
            _ => unimplemented!("haven't implemented type checking for {:#?}", stmt),
        }
    }

    fn check_expr(&mut self, expr: &Expr, env: Env<'tc>) -> TypingJudgment<'tc> {
        match &expr.kind {
            ExprKind::VarRef(ident) => self.check_var_ref(ident, env),
            ExprKind::Block(stmts, expr) => self.check_block(stmts, expr, env),
            ExprKind::Invoke(func_ident, actual_args, type_args) => {
                self.check_invoke(func_ident, actual_args, type_args, env)
            }
        }
    }

    fn check_invoke(
        &mut self,
        func_ident: &Ident,
        actual_args: &Vec<R<Expr>>,
        _type_args: &Vec<R<ast::Ty>>,
        env: Env<'tc>,
    ) -> TypingJudgment<'tc> {
        // TODO handle type args
        if let Some(func_decl) = self.type_context.lookup_func_decl(func_ident.name) {
            let expected_num_args = func_decl.ty.formal_args.len();
            let actual_num_args = actual_args.len();
            if actual_num_args != expected_num_args {
                return TypingJudgment::TypeError(format!("Wrong number of args for invocation of function {}: expected {}, actual {}", func_ident.name, expected_num_args, actual_num_args), env.clone());
            }
            let mut last_tj = TypingJudgment::WellTyped(&Ty::Bottom, env.clone());
            for (formal, actual) in func_decl.ty.formal_args.iter().zip(actual_args.iter()) {
                let env = last_tj.env();
                let tj = self.check_expr(actual, env);
                if let TypingJudgment::WellTyped(actual_ty, new_env) = &tj {
                    if !actual_ty.assignable_to(formal.ty).is_assignable() {
                        last_tj = TypingJudgment::TypeError(
                            format!(
                                "wrong type for parameter. expected {}, actual {}",
                                formal.ty, actual_ty
                            ),
                            new_env.clone(),
                        );
                    } else {
                        last_tj = tj;
                    }
                } else {
                    last_tj = tj;
                }
            }

            let last_env = last_tj.env();
            let mut refinements =
                Refinements::with_capacity(func_decl.ty.output_capability_constraints.len());
            for cap_const in func_decl.ty.output_capability_constraints.iter() {
                let (idx, _arg) = func_decl
                    .ty
                    .formal_args
                    .iter()
                    .find_position(|arg| arg.name == cap_const.name)
                    .unwrap();
                let expr = &actual_args[idx];
                if let ast::ExprKind::VarRef(_name) = &expr.kind {
                    // TODO var_ref needs to tell us the depth here somehow...
                    let var_from_actual = ScopedVar {
                        name: cap_const.name,
                        depth: 1,
                    };
                    let existing_ty = last_env.lookup(&var_from_actual).unwrap();
                    let new_ty_s =
                        existing_ty.apply_constraint(&cap_const.constraint, self.type_context);
                    let new_type = self.type_context.intern_ty(new_ty_s);
                    refinements.insert(var_from_actual, new_type);
                } else {
                    // no binding for us to modify, so just skip
                    continue;
                }
            }

            if refinements.is_empty() {
                last_tj
            } else {
                last_tj.replacing_env(last_env.refine_map(refinements))
            }
        } else {
            TypingJudgment::TypeError(
                format!("no such function: {}", func_ident.name),
                env.clone(),
            )
        }
    }

    fn check_var_ref(&mut self, ident: &Ident, env: Env<'tc>) -> TypingJudgment<'tc> {
        self.local_context
            .symbols
            .lookup(&ident.name)
            .and_then(|var| env.lookup(var))
            .map_or_else(
                || {
                    // TODO just for tests, return bottom type for unknown variable references
                    TypingJudgment::WellTyped(&Ty::Bottom, env.clone())
                    // TypingJudgment::TypeError(
                    //     format!("variable not in scope: {}", ident.name),
                    //     env.clone(),
                    // )
                },
                |ty| TypingJudgment::WellTyped(ty, env.clone()),
            )
    }

    fn check_var_decl(
        &mut self,
        lhs: &Ident,
        ty: &ast::Ty,
        rhs: &Expr,
        env: Env<'tc>,
    ) -> TypingJudgment<'tc> {
        self.check_expr(rhs, env).and_then(|rhs_ty, env| {
            let ty = ty_try!(env, Ty::from_ast(ty, self.type_context));
            if let NotAssignable { reason } = rhs_ty.assignable_to(ty) {
                return TypingJudgment::TypeError(reason, env);
            }
            self.local_context.symbols.bind(
                lhs.name,
                ScopedVar {
                    name: lhs.name,
                    depth: self.local_context.symbols.depth(),
                },
            );
            let new_env = env.refine(self.local_context.symbols.lookup(&lhs.name).unwrap(), ty);
            TypingJudgment::WellTyped(ty, new_env)
        })
    }

    fn check_block(
        &mut self,
        stmts: &Vec<R<Stmt>>,
        expr: &R<Expr>,
        env: Env<'tc>,
    ) -> TypingJudgment<'tc> {
        let outer_env = env.clone();
        let mut curr_env = env.clone();
        let block_tj = with_frame!(&mut self.local_context.symbols, Opacity::Transparent, {
            for stmt in stmts.iter() {
                tj_try!(self.check_stmt(stmt, curr_env.clone()), _ty, next_env, {
                    curr_env = next_env.clone();
                });
            }
            self.check_expr(expr, curr_env.clone())
        });
        tj_try!(block_tj, last_expr_ty, last_expr_env, {
            let outgoing_env = last_expr_env.preserving_refinements_of_outer_vars(
                outer_env.clone(),
                self.local_context.symbols.depth(),
            );
            TypingJudgment::WellTyped(last_expr_ty, outgoing_env)
        })
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
    use crate::ast;
    use crate::func_decls::{ArgCapConstraint, CapConstraint, FunctionFormalArg, FunctionType};
    use crate::ty;
    use crate::type_check::*;
    use crate::type_constructors::{TypeConstructor, TypeConstructorInvocation};
    use itertools::Itertools;

    #[test]
    fn test_invoke_adds_cap() {
        let comp_unit: ast::R<ast::CompilationUnit> = ast! {
            (file
                // TODO read func decls and intern their types
                // fn foo(a: Foo) -> Foo => a[+Blah];
                // (defn foo [(arg a (ty Foo))] [(ty Foo)] [(arg_cap_const a (cap_add (cap Blah)))])
                // fn bar(a: Foo[Blah]) -> Foo
                // (defn bar [(arg a (ty Foo (cap Blah))] [(ty Foo)] [])
                // fn main() -> Foo { let a: Foo = b; foo(a) }
                (defn main [] [(ty Foo)] []
                    // let a: Foo = ...;
                    // let b: Foo = ...;
                    // foo(a);
                    // bar(a);
                    // bar(b) // in my bar(b) world
                    (block
                        [(let a [(ty Foo)] _a)
                         (let b [(ty Foo)] _b)
                         (stmt (invoke foo a))
                         // should succeed since `a` gained `Blah` after invoking `foo`
                         (stmt (invoke bar a))]
                         // should fail because `b` is just `Foo` not `Foo[Blah]`
                        (invoke bar b))))
        };

        // set up environment: there's a type named `Foo` with no type vars, and `b` is whatever type we need it to be (ie, bottom).
        let areans = Arenas::default();
        let tc = TypeContext::new(&areans);
        let blah_cap_expr = tc.intern_cap_expr(CapabilityExpr::Cap(
            tc.intern_cap_decl(CapabilityDeclaration::new("Blah")),
        ));
        let foo_tc = tc.intern_type_constructor(TypeConstructor {
            name: "Foo",
            type_parameters: vec![],
        });
        let foo_tci = tc.intern_ty(ty::Ty::TyConInv(TypeConstructorInvocation {
            constructor: foo_tc,
            type_parameter_bindings: vec![],
            capabilities: None,
        }));
        let foo_blah_tci = tc.intern_ty(ty::Ty::TyConInv(TypeConstructorInvocation {
            constructor: foo_tc,
            type_parameter_bindings: vec![],
            capabilities: Some(blah_cap_expr),
        }));

        fn get_func_type<'tc>(ty: &'tc Ty<'tc>) -> &'tc FunctionType {
            match ty {
                Ty::Func(ft) => ft,
                _ => panic!(),
            }
        }

        let _foo_func = tc.intern_func_ty(FunctionDeclaration {
            name: "foo",
            ty: get_func_type(tc.intern_ty(Ty::Func(FunctionType {
                formal_args: vec![FunctionFormalArg {
                    name: "a",
                    ty: foo_tci,
                }],
                return_type: foo_tci,
                output_capability_constraints: vec![ArgCapConstraint {
                    name: "a",
                    constraint: CapConstraint::Add(blah_cap_expr),
                }],
            }))),
        });

        let _bar_func = tc.intern_func_ty(FunctionDeclaration {
            name: "bar",
            ty: get_func_type(tc.intern_ty(Ty::Func(FunctionType {
                formal_args: vec![FunctionFormalArg {
                    name: "a",
                    ty: foo_blah_tci,
                }],
                return_type: foo_tci,
                output_capability_constraints: vec![],
            }))),
        });

        // type check the file with the given env
        let local_context = LocalContext::default();
        let mut checker = TypeChecker {
            type_context: &tc,
            local_context,
        };

        // println!("{:#?}", comp_unit);
        let result = checker.check_compilation_unit(&*comp_unit);
        match result {
            TypeCheckerResult::Ok { .. } => {
                assert!(
                    false,
                    format!("expected type checker to fail, but it succeeded")
                );
            }
            TypeCheckerResult::Err { item_results, .. } => {
                let err = item_results.iter().find(|tj| {
                    if let TypingJudgment::TypeError(err, _) = tj {
                        err.contains("wrong type for parameter. expected Foo[Blah], actual Foo")
                    } else {
                        false
                    }
                });
                if err.is_none() {
                    assert!(false, "Expected error like 'wrong type for parameter. expected Foo[Blah], actual Foo', but got:\n{}", item_results.iter().join("\n"));
                }
            }
        }
    }
}
