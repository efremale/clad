//--------------------------------------------------------------------*- C++ -*-
// clad - the C++ Clang-based Automatic Differentiator
// version: $Id: ClangPlugin.cpp 7 2013-06-01 22:48:03Z v.g.vassilev@gmail.com $
// author:  Vassil Vassilev <vvasilev-at-cern.ch>
//------------------------------------------------------------------------------

#ifndef CLAD_DERIVATIVE_BUILDER_H
#define CLAD_DERIVATIVE_BUILDER_H

#include "clang/Sema/Sema.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtVisitor.h"

#include <array>
#include <stack>
#include <unordered_map>

namespace clang {
  class ASTContext;
  class CXXOperatorCallExpr;
  class DeclRefExpr;
  class FunctionDecl;
  class MemberExpr;
  class NamespaceDecl;
  class Scope;
  class Sema;
  class Stmt;
}

namespace clad {
  namespace utils {
    class StmtClone;
  }
  class FunctionDeclInfo;
}

namespace clad {
  static clang::SourceLocation noLoc{};
  class DiffPlan;
  /// The main builder class which then uses either ForwardModeVisitor or 
  /// ReverseModeVisitor based on the required mode.
  class DerivativeBuilder {
  private:
    friend class VisitorBase;
    friend class ForwardModeVisitor;
    friend class ReverseModeVisitor;

    clang::Sema& m_Sema;
    clang::ASTContext& m_Context;
    std::unique_ptr<utils::StmtClone> m_NodeCloner;
    clang::NamespaceDecl* m_BuiltinDerivativesNSD;

    clang::Expr* findOverloadedDefinition(clang::DeclarationNameInfo DNI,
                            llvm::SmallVectorImpl<clang::Expr*>& CallArgs);
    bool overloadExists(clang::Expr* UnresolvedLookup,
                            llvm::MutableArrayRef<clang::Expr*> ARargs);

  public:
    DerivativeBuilder(clang::Sema& S);
    ~DerivativeBuilder();

    ///\brief Produces the derivative of a given function
    /// according to a given plan.
    ///
    ///\param[in] FD - the function that will be differentiated.
    ///
    ///\returns The differentiated function.
    ///
    clang::FunctionDecl* Derive(FunctionDeclInfo& FDI, const DiffPlan & plan);
  };

  /// A base class for all common functionality for visitors
  class VisitorBase {
  protected:
    VisitorBase(DerivativeBuilder& builder) :
      m_Builder(builder),
      m_Sema(builder.m_Sema),
      m_Context(builder.m_Context),
      m_CurScope(m_Sema.TUScope),
      m_DerivativeInFlight(false) {}

    using Stmts = llvm::SmallVector<clang::Stmt*, 16>;

    DerivativeBuilder& m_Builder;
    clang::Sema& m_Sema;
    clang::ASTContext& m_Context;
    clang::Scope* m_CurScope;
    bool m_DerivativeInFlight;
    /// The Derivative function that is being generated.
    clang::FunctionDecl* m_Derivative;
    /// The function that is currently differentiated.
    clang::FunctionDecl* m_Function;
    /// A stack of all the blocks where the statements of the gradient function
    /// are stored (e.g., function body, if statement blocks).
    std::stack<Stmts> m_Blocks;

    template <typename Range>
    clang::CompoundStmt* MakeCompoundStmt(const Range & Stmts) {
      auto Stmts_ref = llvm::makeArrayRef(Stmts.data(), Stmts.size());
      return new (m_Context) clang::CompoundStmt(m_Context,
                                                 Stmts_ref,
                                                 noLoc,
                                                 noLoc);
    }

    /// Get the latest block of code (i.e. place for statements output).
    Stmts & currentBlock() {
      return m_Blocks.top();
    }
    /// Create new block.
    Stmts & startBlock() {
      m_Blocks.push({});
      return m_Blocks.top();
    }
    /// Remove the block from the stack, wrap it in CompoundStmt and return it.
    clang::CompoundStmt* finishBlock() {
      auto CS = MakeCompoundStmt(currentBlock());
      m_Blocks.pop();
      return CS;
    }
    /// Output a statement to the current block.
    void emitToCurrentBlock(clang::Stmt* S) {
      currentBlock().push_back(S);
    }

    /// Get a current scope.
    clang::Scope* currentScope() {
      return m_CurScope;
    }
    /// Enters a new scope.
    void enterScope(unsigned ScopeFlags) {
      // FIXME: since Sema::CurScope is private, we cannot access it and have
      // to use separate member variable m_CurScope. The only options to set
      // CurScope of Sema seemt to be through Parser or ContextAndScopeRAII.
      m_CurScope = new clang::Scope(currentScope(), ScopeFlags, m_Sema.Diags);
    }
    void exitScope() {
      // This will remove all the decls in the scope from the IdResolver. 
      m_Sema.ActOnPopScope(noLoc, m_CurScope);
      auto oldScope = m_CurScope;
      m_CurScope = oldScope->getParent();
      delete oldScope;
    }

    /// A shorthand to simplify syntax for creation of new expressions.
    /// Uses m_Sema.BuildUnOp internally.
    clang::Expr* BuildOp(clang::UnaryOperatorKind OpCode, clang::Expr* E);
    /// Uses m_Sema.BuildBin internally.
    clang::Expr* BuildOp(clang::BinaryOperatorKind OpCode,
                         clang::Expr* L,
                         clang::Expr* R);
    
    clang::Expr* BuildParens(clang::Expr* E);

    /// Builds variable declaration to be used inside the derivative body
    clang::VarDecl* BuildVarDecl(clang::QualType Type,
                                 clang::IdentifierInfo* Identifier,
                                 clang::Expr* Init = nullptr);
    
    clang::VarDecl* BuildVarDecl(clang::QualType Type,
                                 llvm::StringRef prefix = "_t",
                                 clang::Expr* Init = nullptr);
    /// Wraps a declaration in DeclStmt.
    clang::Stmt* BuildDeclStmt(clang::Decl* D);
    clang::Stmt* BuildDeclStmt(llvm::MutableArrayRef<clang::Decl*> DS);
    
    /// Builds a DeclRefExpr to a given Decl.
    clang::Expr* BuildDeclRef(clang::ValueDecl* D);

    /// Stores the result of an expression in a temporary variable (of the same
    /// type as is the result of the expression) and
    /// returns a reference to it. 
    clang::Expr* StoreAndRef(clang::Expr* E,
                             llvm::StringRef prefix = "_t");
    /// An overload allowing to specify the type for the variable.
    clang::Expr* StoreAndRef(clang::Expr* E,
                             clang::QualType Type,
                             llvm::StringRef prefix = "_t");

    /// Shorthand to issues a warning or error.
    template <std::size_t N>
    void diag(clang::DiagnosticsEngine::Level level, // Warning or Error
              const char (&format)[N],
              llvm::ArrayRef<llvm::StringRef> args = {},
              clang::SourceLocation loc = {});

    /// Conuter used to create unique identifiers for temporaries
    std::size_t m_tmpId = 0;
    
    /// Creates unique identifier of the form "_t<number>" that is guaranteed
    /// not to collide with anything in the current scope
    clang::IdentifierInfo* CreateUniqueIdentifier(llvm::StringRef name_base,
                                                  std::size_t id);

    /// Updates references in newly cloned statements.
    void updateReferencesOf(clang::Stmt* InSubtree);
    /// Clones a statement
    clang::Stmt* Clone(const clang::Stmt* S);
    /// A shorthand to simplify cloning of expressions.
    clang::Expr* Clone(const clang::Expr* E);
  };

  /// A class that represents the result of Visit of ForwardModeVisitor.
  /// Stmt() allows to access the original (cloned) Stmt and Stmt_dx() allows
  /// to access its derivative (if exists, otherwise null). If Visit produces
  /// other (intermediate) statements, they are output to the current block.
  class StmtDiff {
  private:
    std::array<clang::Stmt*, 2> data;
  public:
    StmtDiff(clang::Stmt* orig = nullptr,
             clang::Stmt* diff = nullptr) {
      data[0] = orig;
      data[1] = diff;
    }

    clang::Stmt* Stmt() { return data[0]; }
    clang::Stmt* Stmt_dx() { return data[1]; }
    clang::Expr* Expr() { return llvm::cast_or_null<clang::Expr>(Stmt()); }
    clang::Expr* Expr_dx() { return llvm::cast_or_null<clang::Expr>(Stmt_dx()); }
    std::array<clang::Stmt*, 2> & Stmts() {
      return data;
    }
  };
    
  /// A visitor for processing the function code in forward mode.
  /// Used to compute derivatives by clad::differentiate.
  class ForwardModeVisitor
    : public clang::ConstStmtVisitor<ForwardModeVisitor, StmtDiff>,
      public VisitorBase {
  private:
    clang::VarDecl* m_IndependentVar;
    /// Map used to keep track of variable declarations and match them
    /// with their derivatives.
    std::unordered_map<clang::VarDecl*, clang::Expr*> m_Variables;
    unsigned m_DerivativeOrder;
    unsigned m_ArgIndex;

  public:
    ForwardModeVisitor(DerivativeBuilder& builder);
    ~ForwardModeVisitor();

    ///\brief Produces the first derivative of a given function.
    ///
    ///\param[in] FD - the function that will be differentiated.
    ///
    ///\returns The differentiated function.
    ///
    clang::FunctionDecl* Derive(FunctionDeclInfo& FDI, const DiffPlan& plan);

    StmtDiff VisitStmt(const clang::Stmt* S);
    StmtDiff VisitCompoundStmt(const clang::CompoundStmt* CS);
    StmtDiff VisitIfStmt(const clang::IfStmt* If);
    StmtDiff VisitReturnStmt(const clang::ReturnStmt* RS);
    StmtDiff VisitUnaryOperator(const clang::UnaryOperator* UnOp);
    StmtDiff VisitBinaryOperator(const clang::BinaryOperator* BinOp);
    StmtDiff VisitCXXOperatorCallExpr(const clang::CXXOperatorCallExpr* OpCall);
    StmtDiff VisitDeclRefExpr(const clang::DeclRefExpr* DRE);
    StmtDiff VisitParenExpr(const clang::ParenExpr* PE);
    StmtDiff VisitMemberExpr(const clang::MemberExpr* ME);
    StmtDiff VisitIntegerLiteral(const clang::IntegerLiteral* IL);
    StmtDiff VisitFloatingLiteral(const clang::FloatingLiteral* FL);
    StmtDiff VisitCallExpr(const clang::CallExpr* CE);
    StmtDiff VisitDeclStmt(const clang::DeclStmt* DS);
    StmtDiff VisitImplicitCastExpr(const clang::ImplicitCastExpr* ICE);
    StmtDiff VisitConditionalOperator(const clang::ConditionalOperator* CO);
    StmtDiff VisitForStmt(const clang::ForStmt* FS);
    // Decl is not Stmt, so it cannot be visited directly.
    // Instead, wrap it in DeclStmt and Visit.
    // Orginal cloned VarDecl is output to Cloned arg, for easier access.
    StmtDiff VisitVarDecl(const clang::VarDecl* VD, clang::VarDecl*& Cloned) {
      auto Result = Visit(BuildDeclStmt(const_cast<clang::VarDecl*>(VD)));
      auto DS = llvm::cast<clang::DeclStmt>(Result.Stmt());
      auto Decl = DS->getSingleDecl();
      Cloned = llvm::cast<clang::VarDecl>(Decl);
      return Result;
    } 
  };

  /// A visitor for processing the function code in reverse mode.
  /// Used to compute derivatives by clad::gradient.
  class ReverseModeVisitor
    : public clang::ConstStmtVisitor<ReverseModeVisitor, void>,
      public VisitorBase {
  private:
    /// Stack is used to pass the arguments (dfdx) to further nodes
    /// in the Visit method.
    std::stack<clang::Expr*> m_Stack;
    clang::Expr* dfdx () {
        return m_Stack.top ();
    }
    void Visit(const clang::Stmt* stmt, clang::Expr* expr) {
        m_Stack.push(expr);
        clang::ConstStmtVisitor<ReverseModeVisitor, void>::Visit(stmt);
        m_Stack.pop();
    }
 
    //// A reference to the output parameter of the gradient function.
    clang::Expr* m_Result;

  public:
    ReverseModeVisitor(DerivativeBuilder& builder);
    ~ReverseModeVisitor();

    ///\brief Produces the gradient of a given function.
    ///
    ///\param[in] FD - the function that will be differentiated.
    ///
    ///\returns The gradient of the function
    ///
    clang::FunctionDecl* Derive(FunctionDeclInfo & FDI, const DiffPlan& plan);
    void VisitCompoundStmt(const clang::CompoundStmt* CS);
    void VisitIfStmt(const clang::IfStmt* If);
    void VisitReturnStmt(const clang::ReturnStmt* RS);
    void VisitUnaryOperator(const clang::UnaryOperator* UnOp);
    void VisitBinaryOperator(const clang::BinaryOperator* BinOp);
    void VisitDeclStmt(const clang::DeclStmt* DS);
    void VisitMemberExpr(const clang::MemberExpr* ME);
    void VisitDeclRefExpr(const clang::DeclRefExpr* DRE);
    void VisitParenExpr(const clang::ParenExpr* PE);
    void VisitIntegerLiteral(const clang::IntegerLiteral* IL);
    void VisitFloatingLiteral(const clang::FloatingLiteral* FL);
    void VisitCallExpr(const clang::CallExpr* CE);
    void VisitImplicitCastExpr(const clang::ImplicitCastExpr* ICE);
    void VisitConditionalOperator(const clang::ConditionalOperator* CO);
  };
} // end namespace clad

#endif // CLAD_DERIVATIVE_BUILDER_H
