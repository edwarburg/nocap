use std::fmt;
use std::fmt::Debug;
use std::ops::Deref;

use bumpalo::core_alloc::fmt::Formatter;

use crate::type_check::Name;

////////////////////////////////////////////////
//                  Shared                    //
////////////////////////////////////////////////

/// An owned pointer to an AstNode
pub struct R<N: AstNode> {
    ptr: Box<N>,
}

impl<N: AstNode> R<N> {
    fn new(node: N) -> Self {
        R {
            ptr: Box::new(node),
        }
    }
}

impl<N: AstNode> Deref for R<N> {
    type Target = N;

    fn deref(&self) -> &Self::Target {
        &self.ptr
    }
}

impl<N: AstNode> Debug for R<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "R(")?;
        Debug::fmt(&self.ptr, f)?;
        write!(f, ")")
    }
}

/// Provides common implementations for node sub-types (Item, Expr, Ty, Cap, etc).
macro_rules! node_impls {
    ($n:ident, $k:ident) => {
        impl AstNode for $n {
            type Kind = $k;

            fn from_header_and_kind(header: AstHeader, kind: Self::Kind) -> Self {
                // TODO one day this may not be sufficient, if various sub-nodes get more fields...
                $n { header, kind }
            }

            fn header(&self) -> &AstHeader {
                &self.header
            }
            fn kind(&self) -> &Self::Kind {
                &self.kind
            }
        }

        // node into kind
        impl Into<$n> for $k {
            fn into(self) -> $n {
                $n::from_kind(self)
            }
        }

        // node into R
        impl Into<R<$n>> for $n {
            fn into(self) -> R<$n> {
                R::new(self)
            }
        }

        // kind into R
        impl Into<R<$n>> for $k {
            fn into(self) -> R<$n> {
                R::new($n::from_kind(self))
            }
        }

        impl Debug for $n {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                write!(f, stringify!($n))?;
                write!(f, "(")?;
                Debug::fmt(&self.kind, f)?;
                write!(f, ")")
            }
        }
    };
}

/// Contains shared stuff every AstNode tracks. Span, type, resolved fqn, etc.
#[derive(Debug, Default)]
pub struct AstHeader {
    // TODO span, nodeid, type, etc
}

/// Generally, the interesting parts of a node are stored in the `kind` field. That's where we distinguish
/// between the different types of nodes and store the various references to children etc.
///
/// This wrapper allows us to generalize over any node of a particular type (expr, stmt, etc), as well
/// as track metadata on the node in a header. This header contains things like the span the node
/// represents, as well as any data that's been populated about the node through the various passes
/// - for example, the type checker tags the node with its resolved type (if it's an expression), etc.
pub trait AstNode: Debug + Sized {
    type Kind;

    fn from_header_and_kind(header: AstHeader, kind: Self::Kind) -> Self;
    fn from_kind(kind: Self::Kind) -> Self {
        Self::from_header_and_kind(AstHeader::default(), kind)
    }

    fn header(&self) -> &AstHeader;
    fn kind(&self) -> &Self::Kind;
}

////////////////////////////////////////////////
//                  Units                     //
////////////////////////////////////////////////

/// A compilation unit, eg, a file.
pub struct CompilationUnit {
    pub header: AstHeader,
    pub kind: CompilationUnitKind,
}

#[derive(Debug)]
pub enum CompilationUnitKind {
    File(Vec<R<Item>>),
}

node_impls!(CompilationUnit, CompilationUnitKind);

////////////////////////////////////////////////
//                  Items                     //
////////////////////////////////////////////////

pub struct Item {
    pub header: AstHeader,
    pub kind: ItemKind,
}

#[derive(Debug)]
pub enum ItemKind {
    FuncDecl(FunctionSignature),
    FuncDeclWithImpl(FunctionSignature, FunctionImplementation),
}

#[derive(Debug)]
pub struct FunctionSignature {
    pub name: Ident,
    // TODO type parameter declarations
    pub args: Vec<FunctionFormalArg>,
    pub return_ty: R<Ty>,
    pub output_cap_constraints: Vec<ArgCapConstraint>,
}

#[derive(Debug)]
pub struct FunctionFormalArg {
    pub name: Ident,
    pub ty: R<Ty>,
}

#[derive(Debug)]
pub struct ArgCapConstraint {
    pub for_arg: Ident,
    pub constraints: Vec<CapConstraint>,
}

node_impls!(Item, ItemKind);

#[derive(Debug)]
pub struct FunctionImplementation {
    pub body: R<Expr>,
}

pub struct Stmt {
    pub header: AstHeader,
    pub kind: StmtKind,
}

#[derive(Debug)]
pub enum StmtKind {
    /// Variable definitions. `let lval: type = rval`
    VarDecl(Ident, Ty, R<Expr>),
    /// assign to an lval. `a = foo`, `foo.a = b`, `foo[i] = c`, etc
    Assign(LVal, R<Expr>),
    /// An expression that appears on a line by itself; typically this is a function invoked for its
    /// side effect.
    Expr(R<Expr>),
}

node_impls!(Stmt, StmtKind);

////////////////////////////////////////////////
//               Expressions                  //
////////////////////////////////////////////////

/// An expression node in the AST.
pub struct Expr {
    pub header: AstHeader,
    pub kind: ExprKind,
}

impl Expr {
    fn new(kind: ExprKind) -> Self {
        Expr {
            header: AstHeader {},
            kind,
        }
    }
}

node_impls!(Expr, ExprKind);

#[derive(Debug)]
pub enum ExprKind {
    /// Variable reference. `foo`, `bar`, etc
    VarRef(Ident),
    /// Blocks of statements, followed by a resulting expression
    /// {
    ///     let a = b;
    ///     a = c;
    ///     a
    /// }
    Block(Vec<R<Stmt>>, R<Expr>),
    /// function invocation. `foo()`, `foo<A>(a, b)`, etc
    Invoke(Ident, Vec<R<Expr>>, Vec<R<Ty>>),
}

#[derive(Debug)]
pub struct Ident {
    pub name: Name,
}

impl Ident {
    fn new(name: Name) -> Ident {
        Ident { name }
    }
}

impl Into<Ident> for Name {
    fn into(self) -> Ident {
        Ident::new(self)
    }
}

#[derive(Debug)]
pub enum LVal {
    Variable(Ident),
}

////////////////////////////////////////////////
//                  Types                     //
////////////////////////////////////////////////

/// The AST's view of a type. Can't perform type analysis using it, but can be converted to type_constructors::Ty with a TypeContext
pub struct Ty {
    pub header: AstHeader,
    pub kind: TyKind,
}

#[derive(Debug)]
pub enum TyKind {
    TyVar(Ident),
    TyConstInv(TypeConstructorInvocation),
}

node_impls!(Ty, TyKind);

#[derive(Debug)]
pub struct TypeConstructorInvocation {
    pub constructor: Ident,
    pub actual_type_parameters: Vec<R<Ty>>,
    pub capabilities: Option<R<Cap>>,
}

impl TypeConstructorInvocation {
    pub fn noarg_nocap(constructor: Ident) -> Self {
        TypeConstructorInvocation {
            constructor,
            actual_type_parameters: Vec::new(),
            capabilities: None,
        }
    }
}

////////////////////////////////////////////////
//              Capabilities                  //
////////////////////////////////////////////////

/// The ast's view of capability expressions
pub struct Cap {
    pub header: AstHeader,
    pub kind: CapKind,
}

#[derive(Debug)]
pub enum CapKind {
    CapRef(Ident),
    And(R<Cap>, R<Cap>),
    Or(R<Cap>, R<Cap>),
}

node_impls!(Cap, CapKind);

#[derive(Debug)]
pub enum CapConstraint {
    Add(R<Cap>),
    Sub(R<Cap>),
}

#[macro_use]
#[cfg(test)]
pub(crate) mod test_utils {
    /// Macro that turns an s-exp DSL into AstNodes or references (R<>) to the same. The caller must
    /// provide the type somehow, as this macro leaves it up to `Into` to wrap up an `AstNode::Kind`
    /// into either a node or a reference to a node.
    ///
    /// Why? https://en.wikipedia.org/wiki/Greenspun%27s_tenth_rule, and also because it makes it easy
    /// to write tests for phases of the compiler after parsing without invoking the parser itself.
    #[macro_export]
    macro_rules! ast {

    // Unit
    ((file $($items:tt)*)) => {{
        use crate::ast;
        ast::CompilationUnitKind::File(vec![$(ast!($items)),*]).into()
    }};

    // Item
    ((defn $name:ident [$($args:tt)*] [$ty:tt] [$($var_cap_consts:tt)*])) => {{
        use crate::ast;
        ast::ItemKind::FuncDecl(ast::FunctionSignature {
            name: stringify!($name).into(),
            args: vec![$(ast!($args)),*],
            return_ty: ast!($ty),
            output_cap_constraints: vec![$(ast!($var_cap_consts)),*]
        }).into()
    }};
    ((defn $name:ident [$($args:tt)*] [$ty:tt] [$($var_cap_consts:tt)*] $body:tt)) => {{
        use crate::ast;
        ast::ItemKind::FuncDeclWithImpl(
            ast::FunctionSignature {
                name: stringify!($name).into(),
                args: vec![$(ast!($args)),*],
                return_ty: ast!($ty),
                output_cap_constraints: vec![$(ast!($var_cap_consts)),*]
            },
            ast::FunctionImplementation { body: ast!($body) }
        ).into()
    }};
    ((arg $name:ident $ty:tt)) => {{
        use crate::ast;
        ast::FunctionFormalArg {
            name: stringify!($name).into(),
            ty: ast!($ty)
        }
    }};
    ((arg_cap_const $name:ident $($const:tt)*)) => {{
        use crate::ast;
        ast::ArgCapConstraint {
            for_arg: stringify!($name).into(),
            constraints: vec![$(ast!($const)),*]
        }
    }};

    // Stmt
    ((stmt $expr:tt)) => {{
        use crate::ast;
        ast::StmtKind::Expr(ast!($expr)).into()
    }};

    // Expr
    ((let $lhs:ident [$ty:tt] $rhs:tt)) => {{
        use crate::ast;
        ast::StmtKind::VarDecl(
            stringify!($lhs).into(),
            ast!($ty),
            ast!($rhs),
        ).into()
    }};
    ($var:ident) => {{
        use crate::ast;
        ast::ExprKind::VarRef(stringify!($var).into()).into()
    }};
    ((block [$($body:tt)*] $expr:tt)) => {{
        use crate::ast;
        ast::ExprKind::Block(vec![$(ast!($body)),*], ast!($expr)).into()
    }};
    ((invoke $fun:ident $($args:tt)*)) => {{
        use crate::ast;
        ast::ExprKind::Invoke(stringify!($fun).into(), vec![$(ast!($args)),*], vec![]).into()
    }};

    // Ty
    // TODO type parameters, capabilities
    ((ty $ty:ident)) => {{
        use crate::ast;
        ast::TyKind::TyConstInv(ast::TypeConstructorInvocation::noarg_nocap(
            stringify!($ty).into(),
        )).into()
    }};
    // TODO can we collapse these next two rules? not sure how to alternate Some/None with optional cap constraints
    ((ty $ty:ident [$($ty_parms:tt)*] [])) => {{
        use crate::ast;
        ast::TyKind::TyConstInv(ast::TypeConstructorInvocation {
            constructor: stringify!($ty).into(),
            actual_type_parameters: vec![$(ast!($ty_parms)),*],
            capabilities: None,
        }).into()
    }};
    ((ty $ty:ident [$($ty_parms:tt)*] [$cap_consts:tt])) => {{
        use crate::ast;
        ast::TyKind::TyConstInv(ast::TypeConstructorInvocation {
            constructor: stringify!($ty).into(),
            actual_type_parameters: vec![$(ast!($ty_parms)),*],
            capabilities: Some(ast!($cap_consts)),
        }).into()
    }};

    // Cap
    ((cap_add $cap:tt)) => {{
        use crate::ast;
        ast::CapConstraint::Add(ast!($cap))
    }};
    ((cap_sub $cap:tt)) => {{
        use crate::ast;
        ast::CapConstraint::Sub(ast!($cap))
    }};
    ((cap $name:ident)) => {{
        use crate::ast;
        ast::CapKind::CapRef(stringify!($name).into()).into()
    }};
    ((cap_and [$cap1:tt] [$cap2:tt])) => {{
        use crate::ast;
        ast::CapKind::And(ast!($cap1), ast!($cap2)).into()
    }};
    ((cap_or [$cap1:tt] [$cap2:tt])) => {{
        use crate::ast;
        ast::CapKind::Or(ast!($cap1), ast!($cap2)).into()
    }};
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::*;

    #[test]
    fn test_macro() {
        let node: R<Expr> = ast! {
            (block
                [(let a [(ty Foo)] b)
                 (let c [(ty Bar)] d)]
                (invoke foo a c))
        };
        println!("{:#?}", node);
    }
}
