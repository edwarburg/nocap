use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Display;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Mutex;

use bumpalo::Bump;
use itertools::Itertools;

use crate::ast;
use crate::ast::R;
use crate::ast_to_ty::FromAst;
use crate::data_structures::symbol_table::Opacity;
use crate::data_structures::symbol_table::SymbolTable;
use crate::ty;

pub mod assignable;
use assignable::AssignabilityJudgment;
use assignable::CheckAssignable;
// TODO definitely gonna need to change this at some point...
pub type Name = &'static str;

pub struct TypeContext<'tc> {
    pub arenas: &'tc Arenas,
    interners: Interners<'tc>,
}

impl<'tc> TypeContext<'tc> {}

impl<'tc> TypeContext<'tc> {
    pub fn new(arenas: &'tc Arenas) -> TypeContext<'tc> {
        TypeContext {
            arenas,
            interners: Interners::new(arenas),
        }
    }

    pub(crate) fn intern_type_constructor(
        &'tc self,
        type_constructor: ty::TypeConstructor,
    ) -> &'tc ty::TypeConstructor {
        self.interners.type_constructors.intern(type_constructor)
    }

    pub(crate) fn lookup_type_constructor(&self, name: Name) -> Option<&ty::TypeConstructor> {
        self.interners.type_constructors.lookup(name)
    }

    pub(crate) fn intern_cap_decl(
        &'tc self,
        cap_decl: ty::CapabilityDeclaration,
    ) -> &'tc ty::CapabilityDeclaration {
        self.interners.capability_declarations.intern(cap_decl)
    }

    pub(crate) fn lookup_cap_decl(&self, name: Name) -> Option<&ty::CapabilityDeclaration> {
        self.interners.capability_declarations.lookup(name)
    }

    pub(crate) fn intern_cap_expr(
        &'tc self,
        cap_expr: ty::CapabilityExpr<'tc>,
    ) -> &'tc ty::CapabilityExpr<'tc> {
        self.interners.capability_expressions.intern(cap_expr)
    }

    pub(crate) fn intern_ty(&'tc self, ty: ty::Ty<'tc>) -> &'tc ty::Ty<'tc> {
        self.interners.tys.intern(ty)
    }

    pub(crate) fn intern_func_decl(
        &'tc self,
        func_decl: ty::FunctionDeclaration<'tc>,
    ) -> &'tc ty::FunctionDeclaration<'tc> {
        self.interners.func_decls.intern(func_decl)
    }

    pub(crate) fn lookup_func_decl(
        &'tc self,
        name: Name,
    ) -> Option<&'tc ty::FunctionDeclaration<'tc>> {
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
    type_constructors: InternedById<'tc, Name, ty::TypeConstructor>,
    capability_declarations: InternedById<'tc, Name, ty::CapabilityDeclaration>,
    capability_expressions: InternedBySet<'tc, ty::CapabilityExpr<'tc>>,
    tys: InternedBySet<'tc, ty::Ty<'tc>>,
    func_decls: InternedById<'tc, Name, ty::FunctionDeclaration<'tc>>,
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
    WellTyped(&'tc ty::Ty<'tc>, Env<'tc>),
    // TODO ty to use for error recovery?
    TypeError(TypeError, Env<'tc>),
}

/// Convert a TypingJudgment into a Result, discarding the environment.
impl<'tc> Into<Result<&'tc ty::Ty<'tc>, TypeError>> for TypingJudgment<'tc> {
    fn into(self) -> Result<&'tc ty::Ty<'tc>, TypeError> {
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
        F: FnMut(&'tc ty::Ty<'tc>, Env<'tc>) -> TypingJudgment<'tc>,
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
    ($env:expr, $body:expr) => {{
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
    fn check_compilation_unit(&mut self, unit: &ast::CompilationUnit) -> TypeCheckerResult<'tc> {
        use crate::ast::*;
        match &unit.kind {
            CompilationUnitKind::File(items) => {
                // go through funcs, structs, etc and extract header info from them, to allow
                // out-of-order declaration

                let mut item_results: Vec<TypingJudgment<'tc>> = Vec::with_capacity(items.len());
                for item in items {
                    let result = self.check_header_and_intern(item);
                    item_results.push(result);
                }

                // if there's something to check, go through and check them
                if !item_results.is_empty() && item_results.iter().all(|res| res.is_well_typed()) {
                    item_results.clear();
                    for item in items {
                        match &item.kind {
                            ItemKind::FuncDecl(_) => {
                                // nothing to do
                            }
                            ItemKind::FuncDeclWithImpl(_, func_impl) => {
                                let result =
                                    self.check_func_impl(func_impl, Rc::new(Environment::new()));
                                item_results.push(result);
                            }
                            ItemKind::CapDecl(_cap_decl) => {}
                            ItemKind::StructDecl(_struct_decl) => {}
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

    fn check_header_and_intern(&mut self, item: &ast::Item) -> TypingJudgment<'tc> {
        use crate::ast::*;
        match &item.kind {
            ItemKind::FuncDecl(func_sig) => self.check_func_sig_and_intern(func_sig),
            ItemKind::FuncDeclWithImpl(func_sig, _) => self.check_func_sig_and_intern(func_sig),
            ItemKind::CapDecl(cap_decl) => self.check_cap_decl_and_intern(cap_decl),
            ItemKind::StructDecl(struct_decl) => self.check_struct_decl_and_intern(struct_decl),
        }
    }

    fn check_func_sig_and_intern(
        &mut self,
        func_sig: &ast::FunctionSignature,
    ) -> TypingJudgment<'tc> {
        let decl = ty_try!(
            Rc::new(Environment::new()),
            ty::FunctionDeclaration::from_ast(func_sig, self.type_context)
        );
        self.type_context.intern_ty(ty::Ty::Func(decl.ty.clone()));
        TypingJudgment::WellTyped(&ty::Ty::Unit, Rc::new(Environment::new()))
    }

    fn check_cap_decl_and_intern(
        &mut self,
        cap_decl: &ast::CapabilityDeclaration,
    ) -> TypingJudgment<'tc> {
        self.type_context
            .intern_cap_decl(ty::CapabilityDeclaration {
                name: cap_decl.name,
            });

        TypingJudgment::WellTyped(&ty::Ty::Unit, Rc::new(Environment::new()))
    }

    fn check_struct_decl_and_intern(
        &mut self,
        struct_decl: &ast::StructDeclaration,
    ) -> TypingJudgment<'tc> {
        self.type_context
            .intern_type_constructor(ty::TypeConstructor {
                name: struct_decl.name,
                type_parameters: vec![],
            });

        TypingJudgment::WellTyped(&ty::Ty::Unit, Rc::new(Environment::new()))
    }

    fn check_func_impl(
        &mut self,
        func_impl: &ast::FunctionImplementation,
        env: Env<'tc>,
    ) -> TypingJudgment<'tc> {
        self.check_expr(&func_impl.body, env)
    }

    fn check_stmt(&mut self, stmt: &ast::Stmt, env: Env<'tc>) -> TypingJudgment<'tc> {
        use crate::ast::*;
        match &stmt.kind() {
            StmtKind::VarDecl(lhs, ty, rhs) => self.check_var_decl(lhs, ty, rhs, env),
            StmtKind::Expr(expr) => self.check_expr(expr, env),
            _ => unimplemented!("haven't implemented type checking for {:#?}", stmt),
        }
    }

    fn check_var_decl(
        &mut self,
        lhs: &ast::Ident,
        ty: &ast::Ty,
        rhs: &ast::Expr,
        env: Env<'tc>,
    ) -> TypingJudgment<'tc> {
        self.check_expr(rhs, env).and_then(|rhs_ty, env| {
            let ty = ty_try!(env, ty::Ty::from_ast(ty, self.type_context));
            if let AssignabilityJudgment::NotAssignable { reason } = rhs_ty.assignable_to(ty) {
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

    fn check_expr(&mut self, expr: &ast::Expr, env: Env<'tc>) -> TypingJudgment<'tc> {
        use crate::ast::*;
        match &expr.kind {
            ExprKind::VarRef(ident) => self.check_var_ref(ident, env),
            ExprKind::Block(stmts, expr) => self.check_block(stmts, expr, env),
            ExprKind::Invoke(func_ident, actual_args, type_args) => {
                self.check_invoke(func_ident, actual_args, type_args, env)
            }
        }
    }

    fn check_block(
        &mut self,
        stmts: &Vec<R<ast::Stmt>>,
        expr: &R<ast::Expr>,
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

    fn check_invoke(
        &mut self,
        func_ident: &ast::Ident,
        actual_args: &Vec<R<ast::Expr>>,
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
            let mut last_tj = TypingJudgment::WellTyped(&ty::Ty::Bottom, env.clone());
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
                    let new_type =
                        cap_const
                            .constraints
                            .iter()
                            .fold(existing_ty, |_acc, constraint| {
                                self.type_context.intern_ty(
                                    existing_ty.apply_constraint(constraint, self.type_context),
                                )
                            });
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

    fn check_var_ref(&mut self, ident: &ast::Ident, env: Env<'tc>) -> TypingJudgment<'tc> {
        self.local_context
            .symbols
            .lookup(&ident.name)
            .and_then(|var| env.lookup(var))
            .map_or_else(
                || {
                    // TODO just for tests, return bottom type for unknown variable references
                    TypingJudgment::WellTyped(&ty::Ty::Bottom, env.clone())
                    // TypingJudgment::TypeError(
                    //     format!("variable not in scope: {}", ident.name),
                    //     env.clone(),
                    // )
                },
                |ty| TypingJudgment::WellTyped(ty, env.clone()),
            )
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

type Refinements<'tc> = HashMap<ScopedVar, &'tc ty::Ty<'tc>>;

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

    fn refine(self: Rc<Environment<'tc>>, var: &ScopedVar, ty: &'tc ty::Ty<'tc>) -> Env<'tc> {
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

    fn lookup(self: &Env<'tc>, var: &ScopedVar) -> Option<&'tc ty::Ty<'tc>> {
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
    use crate::typecheck::assignable::{AssignabilityJudgment, CheckAssignable};

    pub(crate) fn assert_assignable_to<T: CheckAssignable>(lhs: &T, rhs: &T) {
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

    pub(crate) fn assert_not_assignable_to<T: CheckAssignable>(lhs: &T, rhs: &T) {
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
    use itertools::Itertools;

    use crate::ast;
    use crate::typecheck::*;

    #[test]
    fn test_invoke_adds_cap() {
        let comp_unit: ast::R<ast::CompilationUnit> = ast! {
            (file
                // cap Blah;
                (defcap Blah)
                // struct Foo<> {};
                (defstruct Foo [] [])
                // fn foo(a: Foo) -> Foo => a[+Blah];
                (defn foo [(arg a (ty Foo))] [(ty Foo)] [(arg_cap_const a (cap_add (cap Blah)))])
                // fn bar(a: Foo[Blah]) -> Foo
                (defn bar [(arg a (ty Foo [] [(cap Blah)]))] [(ty Foo)] [])
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
