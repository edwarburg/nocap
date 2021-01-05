use crate::type_check::Name;
use bumpalo::core_alloc::fmt::Formatter;
use std::fmt;
use std::fmt::Display;
use std::ops::Deref;

/// An owned pointer to an AstNode
pub struct AstRef {
    ptr: Box<AstNode>,
}

impl Deref for AstRef {
    type Target = AstNode;

    fn deref(&self) -> &Self::Target {
        &self.ptr
    }
}

/// A node in the AST.
///
/// Generally, the interesting parts of an AstNode are stored in the AstNodeKind. That's where we distinguish
/// between the different types of nodes and store the various referenced to children etc.
///
/// This wrapper allows us to generalize over any AstNode, as well as track metadata on the node in a
/// header. This header contains things like the span the node represents, as well as any data that's
/// been populated about the node through the various passes - for example, the type checker tags the
/// node with its resolved type (if it's an expression), etc. That allows accumulating
pub struct AstNode {
    pub header: AstNodeHeader,
    pub kind: AstNodeKind,
}

impl Display for AstNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

/// Contains shared stuff every AstNode tracks. Span, type, resolved fqn, etc.
pub struct AstNodeHeader {
    // TODO span, nodeid, type, etc
}

pub struct Ident {
    pub name: Name,
}

pub enum AstNodeKind {
    /// Identifiers. `Foo`, `bar`, etc
    Ident(Ident),
    /// Variable reference. `foo`, `bar`, etc
    VarRef(Ident),
    /// Variable definitions. `let lval: type = rval`
    VarDecl(AstRef, TypeExpr, AstRef),
    /// Expressions valid on the left hand side of an assignment. `a`, `foo.a`, `foo[i]`, etc.
    LVal(LVal),
    /// Blocks of statements
    /// {
    ///     // ...
    /// }
    Block(Vec<AstRef>),
    /// function invocation. `foo()`, `foo<A>()`, etc
    Invoke(Name),
    /// Type expressions. `Int`, `Foo<A>[C]`, etc
    TypeExpr(TypeExpr),
}

impl Display for AstNodeKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO display AST nodes
        write!(f, "node")
    }
}

pub enum LVal {
    Variable(Ident),
}

/// The AST's view of a type. Can't perform type analysis using it, but can be converted to type_constructors::Ty with a TypeContext
pub enum TypeExpr {
    Variable(Ident),
    TyConstInv(TypeConstructorInvocation),
}

pub struct TypeConstructorInvocation {
    pub constructor: Ident,
    pub actual_type_parameters: Vec<AstRef>,
    pub capabilities: Vec<AstRef>,
}

pub struct FunctionImplementation {
    pub body: AstRef,
}
