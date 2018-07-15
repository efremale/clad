//--------------------------------------------------------------------*- C++ -*-
// clad - the C++ Clang-based Automatic Differentiator
// version: $Id: ClangPlugin.cpp 7 2013-06-01 22:48:03Z v.g.vassilev@gmail.com $
// author:  Vassil Vassilev <vvasilev-at-cern.ch>
//------------------------------------------------------------------------------

#include "clad/Differentiator/DerivativeBuilder.h"

#include "ConstantFolder.h"

#include "clad/Differentiator/DiffPlanner.h"
#include "clad/Differentiator/StmtClone.h"

#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Overload.h"
#include "clang/Sema/SemaInternal.h"

using namespace clang;


namespace clad {
  static SourceLocation noLoc{};

  CompoundStmt* NodeContext::wrapInCompoundStmt(clang::ASTContext& C) const {
    assert(!isSingleStmt() && "Must be more than 1");
    llvm::ArrayRef<Stmt*> stmts
    = llvm::makeArrayRef(m_Stmts.data(), m_Stmts.size());
    clang::SourceLocation noLoc;
    return new (C) clang::CompoundStmt(C, stmts, noLoc, noLoc);
  }

  DerivativeBuilder::DerivativeBuilder(clang::Sema& S)
    : m_Sema(S), m_Context(S.getASTContext()),
      m_NodeCloner(new utils::StmtClone(m_Context)),
      m_BuiltinDerivativesNSD(nullptr) {}

  DerivativeBuilder::~DerivativeBuilder() {}

  static void registerDerivative(FunctionDecl* derivedFD, Sema& semaRef) {
    LookupResult R(semaRef, derivedFD->getNameInfo(), Sema::LookupOrdinaryName);
    semaRef.LookupQualifiedName(R, derivedFD->getDeclContext(),
                                /*allowBuiltinCreation*/ false);
    // Inform the decl's decl context for its existance after the lookup,
    // otherwise it would end up in the LookupResult.
    derivedFD->getDeclContext()->addDecl(derivedFD);

    if (R.empty())
      return;
    // Register the function on the redecl chain.
    derivedFD->setPreviousDecl(cast<FunctionDecl>(R.getFoundDecl()));

  }

  FunctionDecl* DerivativeBuilder::Derive(FunctionDeclInfo& FDI,
                                          const DiffPlan& plan) {
    FunctionDecl* result = nullptr;
    if (plan.getMode() == DiffMode::forward) {
      ForwardModeVisitor V(*this);
      result = V.Derive(FDI, plan);
    }
    else if (plan.getMode() == DiffMode::reverse) {
      ReverseModeVisitor V(*this);
      result = V.Derive(FDI, plan);
    }

    if (result)
      registerDerivative(result, m_Sema);
    return result;
  }

  VarDecl* VisitorBase::BuildVarDecl(QualType Type,
                                     IdentifierInfo* Identifier,
                                     Expr* Init) {

    auto VD = VarDecl::Create(m_Context,
                              m_Derivative,
                              noLoc,
                              noLoc,
                              Identifier,
                              Type,
                              nullptr, // FIXME: Should there be any TypeInfo?
                              SC_None);
    VD->setInit(Init);
    return VD;
  }

  Stmt* VisitorBase::BuildDeclStmt(Decl* D) {
    return m_Sema.ActOnDeclStmt(m_Sema.ConvertDeclToDeclGroup(D),
                                noLoc,
                                noLoc).get();
  }
  
  Stmt* VisitorBase::BuildDeclStmt(llvm::MutableArrayRef<Decl*> DS) {
    auto DGR = DeclGroupRef::Create(m_Context, DS.data(), DS.size());
    return new (m_Context) DeclStmt(DGR,
                                    noLoc,
                                    noLoc);
  }

  IdentifierInfo*
  VisitorBase::CreateUniqueIdentifier(llvm::StringRef name_base,
                                      std::size_t id) {
  
    for (;;) {
      auto name = &m_Context.Idents.get(name_base.data() + std::to_string(id));
      LookupResult R(m_Sema,
                     DeclarationName(name),
                     noLoc,
                     Sema::LookupOrdinaryName);
      m_Sema.LookupName(R, m_CurScope.get(), false);
      if (R.empty()) {
        m_tmpId = id + 1;
        return name;
      }
      else
        id += 1;
    }
  }

  CompoundStmt* VisitorBase::MakeCompoundStmt(
    const llvm::SmallVector<clang::Stmt*, 16> & Stmts) {
    auto Stmts_ref = llvm::makeArrayRef(Stmts.data(), Stmts.size());
    return new (m_Context) clang::CompoundStmt(m_Context,
                                               Stmts_ref,
                                               noLoc,
                                               noLoc);
  }

  Expr* VisitorBase::BuildParens(Expr* E) {
    return m_Sema.ActOnParenExpr(noLoc, noLoc, E).get();
  }

  template <std::size_t N>
  void VisitorBase::diag(clang::DiagnosticsEngine::Level level,
                         const char (&format)[N],
                         llvm::ArrayRef<llvm::StringRef> args,
                         clang::SourceLocation loc) {
    unsigned diagID
      = m_Sema.Diags.getCustomDiagID(level, format);
    auto stream = m_Sema.Diag(loc, diagID);
    for (auto arg : args)
      stream << arg;
  }

  Expr* VisitorBase::StoreAndRef(Expr* E, llvm::StringRef prefix) {
    return StoreAndRef(E, E->getType(), prefix);
  }

  Expr* VisitorBase::StoreAndRef(Expr* E,
                                 QualType Type,
                                 llvm::StringRef prefix) {
    // Create variable declaration.
    auto Var = BuildVarDecl(Type,
                            CreateUniqueIdentifier(prefix, m_tmpId),
                            E);
    
    // Add the identifier to the scope
    m_CurScope->AddDecl(Var);
    m_Sema.IdResolver.AddDecl(Var);
    // Add the declaration to the body of the gradient function.
    currentBlock().push_back(BuildDeclStmt(Var));

    // Return reference to the declaration instead of original expression.
    return m_Sema.BuildDeclRefExpr(Var,
                                   Type,
                                   VK_LValue,
                                   noLoc).get();
  }

  ForwardModeVisitor::ForwardModeVisitor(DerivativeBuilder& builder):
    VisitorBase(builder) {}

  ForwardModeVisitor::~ForwardModeVisitor() {}

  FunctionDecl* ForwardModeVisitor::Derive(
    FunctionDeclInfo& FDI,
    const DiffPlan& plan) {
    FunctionDecl* FD = FDI.getFD();
    m_Function = FD;
    assert(FD && "Must not be null.");
    assert(!m_DerivativeInFlight
           && "Doesn't support recursive diff. Use DiffPlan.");
    m_DerivativeInFlight = true;
#ifndef NDEBUG
    bool notInArgs = true;
    for (unsigned i = 0; i < FD->getNumParams(); ++i)
      if (FDI.getPVD() == FD->getParamDecl(i)) {
        notInArgs = false;
        break;
      }
    assert(!notInArgs && "Must pass in a param of the FD.");
#endif


    m_IndependentVar = FDI.getPVD(); // FIXME: Use only one var.
    m_DerivativeOrder = plan.getCurrentDerivativeOrder();
    std::string s = std::to_string(m_DerivativeOrder);
    std::string derivativeBaseName;
    if (m_DerivativeOrder == 1)
      s = "";
    switch (FD->getOverloadedOperator()) {
    default:
      derivativeBaseName = plan.begin()->getFD()->getNameAsString();
      break;
    case OO_Call:
      derivativeBaseName = "operator_call";
      break;
    }

    m_ArgIndex = plan.getArgIndex();
    IdentifierInfo* II = &m_Context.Idents.get(
      derivativeBaseName + "_d" + s + "arg" + std::to_string(m_ArgIndex));
    DeclarationNameInfo name(II, noLoc);
    FunctionDecl* derivedFD = 0;
    if (isa<CXXMethodDecl>(FD)) {
      CXXRecordDecl* CXXRD = cast<CXXRecordDecl>(FD->getDeclContext());
      derivedFD = CXXMethodDecl::Create(m_Context, CXXRD, noLoc, name,
                                        FD->getType(), FD->getTypeSourceInfo(),
                                        FD->getStorageClass(),
                                        FD->isInlineSpecified(),
                                        FD->isConstexpr(), noLoc);
      derivedFD->setAccess(FD->getAccess());
    }
    else {
      assert(isa<FunctionDecl>(FD) && "Must derive from FunctionDecl.");
      derivedFD = FunctionDecl::Create(m_Context,
                                       FD->getDeclContext(), noLoc,
                                       name, FD->getType(),
                                       FD->getTypeSourceInfo(),
                                       FD->getStorageClass(),
                                       /*default*/
                                       FD->isInlineSpecified(),
                                       FD->hasWrittenPrototype(),
                                       FD->isConstexpr()
                                       );
    }
    m_Derivative = derivedFD;

    llvm::SmallVector<ParmVarDecl*, 4> params;
    ParmVarDecl* newPVD = 0;
    ParmVarDecl* PVD = 0;

    // We will use the m_CurScope to do the needed lookups.
    m_CurScope.reset(new Scope(m_Sema.TUScope, Scope::FnScope,
                               m_Sema.getDiagnostics()));

    // FIXME: We should implement FunctionDecl and ParamVarDecl cloning.
    for(size_t i = 0, e = FD->getNumParams(); i < e; ++i) {
      PVD = FD->getParamDecl(i);
      Expr* clonedPVDDefaultArg = 0;
      if (PVD->hasDefaultArg())
        clonedPVDDefaultArg = Clone(PVD->getDefaultArg());

      newPVD = ParmVarDecl::Create(m_Context, derivedFD, noLoc, noLoc,
                                   PVD->getIdentifier(), PVD->getType(),
                                   PVD->getTypeSourceInfo(),
                                   PVD->getStorageClass(),
                                   clonedPVDDefaultArg);

      // Make m_IndependentVar to point to the argument of the newly created
      // derivedFD.
      if (PVD == m_IndependentVar)
        m_IndependentVar = newPVD;

      params.push_back(newPVD);
      // Add the args in the scope and id chain so that they could be found.
      if (newPVD->getIdentifier()) {
        m_CurScope->AddDecl(newPVD);
        m_Sema.IdResolver.AddDecl(newPVD);
      }
    }

    llvm::ArrayRef<ParmVarDecl*> paramsRef
      = llvm::makeArrayRef(params.data(), params.size());
    derivedFD->setParams(paramsRef);
    derivedFD->setBody(0);

    // This is creating a 'fake' function scope. See SemaDeclCXX.cpp
    Sema::SynthesizedFunctionScope Scope(m_Sema, derivedFD);
    auto block = startBlock();
    for (auto param : params) {
      auto dValue = 
        (param == m_IndependentVar) ?
          1 :
          0 ;
      auto dParam =
        ConstantFolder::synthesizeLiteral(param->getType(),
                                          m_Context,
                                          dValue);
      dParam = StoreAndRef(dParam, "_d_" + param->getNameAsString());
      m_Variables[param] = dParam;
    }

    Visit(FD->getMostRecentDecl()->getBody());
    auto derivativeBody = finishBlock();

    derivedFD->setBody(derivativeBody);
    // Cleanup the IdResolver chain.
    for(FunctionDecl::param_iterator I = derivedFD->param_begin(),
        E = derivedFD->param_end(); I != E; ++I) {
      if ((*I)->getIdentifier()) {
        m_CurScope->RemoveDecl(*I);
        //m_Sema.IdResolver.RemoveDecl(*I); // FIXME: Understand why that's bad
      }
    }

    m_DerivativeInFlight = false;
    return derivedFD;
  }

  Stmt* DerivativeBuilder::Clone(const Stmt* S) {
    Stmt* clonedStmt = m_NodeCloner->Clone(S);
    updateReferencesOf(clonedStmt);
    return clonedStmt;
  }
  Expr* DerivativeBuilder::Clone(const Expr* E) {
    const Stmt* S = E;
    return llvm::cast<Expr>(Clone(S));
  }

  Expr* DerivativeBuilder::BuildOp(UnaryOperatorKind OpCode, Expr* E) {
    return m_Sema.BuildUnaryOp(m_CurScope.get(),
                               noLoc,
                               OpCode,
                               E).get();
  }

  Expr* DerivativeBuilder::BuildOp(clang::BinaryOperatorKind OpCode,
                                   Expr* L, Expr* R) {
    return m_Sema.BuildBinOp(nullptr, noLoc, OpCode, L, R).get();
  }

  ExprDiff ForwardModeVisitor::VisitStmt(const Stmt* S) {
    // Unknown stmt, just clone it.
    currentBlock().push_back(Clone(S));
    return {};
  }

  ExprDiff ForwardModeVisitor::VisitCompoundStmt(const CompoundStmt* CS) {
    for (auto S : CS->body())
      Visit(S);
    return {};
  }

  ExprDiff ForwardModeVisitor::VisitIfStmt(const IfStmt* If) {
    auto init = If->getInit();
    // FIXME: starting from C++17, init can be any statement and potentially
    // needs to be differentiated.
    auto clonedInit =
      init ?
        Clone(init) :
        nullptr;

    auto condVarDecl = If->getConditionVariable();
    VarDecl* condVar = nullptr;
    if (condVarDecl) {
       // A block for declarations inside If.
       // This will output cond variable declaration and its derivative to
       // the current block.
       // FIXME: this puts cond var decl in the current scope instead of if
       // scope, so it can potentially collide with something.
       auto diff = Visit(BuildDeclStmt(condVarDecl));
       auto condVarDeclStmt = dyn_cast<DeclStmt>(currentBlock().back());
       condVar = dyn_cast<VarDecl>(condVarDeclStmt->getSingleDecl());
       // Remove cond var declaration from the current block as it will be 
       // placed in the if statement.
       currentBlock().pop_back();
       m_Variables[condVar] = diff.dx();
    }
       
    auto cond = Clone(If->getCond());
    auto thenStmt = If->getThen();
    Stmt* thenStmtDiff = nullptr;
    if (thenStmt) {
      startBlock();
      Visit(thenStmt);
      thenStmtDiff = finishBlock();
    }
    auto elseStmt = If->getElse();
    Stmt* elseStmtDiff = nullptr;
    if (elseStmt) {
      startBlock();
      Visit(elseStmt);
      elseStmtDiff = finishBlock();
    }
    
   auto ifStmt =
     new (m_Context) IfStmt(m_Context,
                            noLoc,
                            If->isConstexpr(),
                            clonedInit,
                            condVar,
                            cond,
                            thenStmtDiff,
                            noLoc,
                            elseStmtDiff);
    currentBlock().push_back(ifStmt);  
    
    if (condVar)
      m_Variables.erase(condVar);
    return {}; // No expressions are produced.
  }

  ExprDiff 
  ForwardModeVisitor::VisitConditionalOperator(const ConditionalOperator* CO) {
    auto cond = Clone(CO->getCond());
    auto ifTrue = Visit(CO->getTrueExpr());
    auto ifFalse = Visit(CO->getFalseExpr());

    cond = StoreAndRef(cond);
    cond =
      m_Sema.ActOnCondition(m_CurScope.get(),
                            noLoc,
                            cond,
                            Sema::ConditionKind::Boolean).get().second;
    auto condExpr = 
      new (m_Context) ConditionalOperator(cond,
                                          noLoc,
                                          ifTrue.x(),
                                          noLoc,
                                          ifFalse.x(),
                                          ifTrue.x()->getType(),
                                          CO->getValueKind(),
                                          OK_Ordinary);
   
    auto dcondExpr = 
      new (m_Context) ConditionalOperator(cond,
                                          noLoc,
                                          ifTrue.dx(),
                                          noLoc,
                                          ifFalse.dx(),
                                          ifTrue.dx()->getType(),
                                          // FIXME: check if we can get lvalue
                                          // in some case
                                          VK_RValue, 
                                          OK_Ordinary);
    
    auto dcondExprParens = BuildParens(dcondExpr);

    return {
      StoreAndRef(condExpr),
      StoreAndRef(dcondExprParens)
    };
  }

  ExprDiff ForwardModeVisitor::VisitForStmt(const ForStmt* FS) {
    auto init = FS->getInit();
    // init can be any statement and potentially needs to be differentiated.
    auto clonedInit =
      init ?
        Clone(init) :
        nullptr;

    auto condVarDecl = FS->getConditionVariable();
    auto clonedCondVarDecl =
      condVarDecl ?
        dyn_cast<VarDecl>(
          dyn_cast<DeclStmt>(
           Clone(BuildDeclStmt(condVarDecl)))->getSingleDecl()) :
      nullptr;
       
    auto cond = 
      (FS->getCond()) ?
        Clone(FS->getCond()) :
        nullptr;
    auto incDiff = Clone(FS->getInc());
    auto body = FS->getBody();
    startBlock();
    Visit(body);
    auto bodyDiff = finishBlock();
 
    auto forStmt =
      new (m_Context) ForStmt(m_Context,
                              clonedInit,
                              cond,
                              clonedCondVarDecl,
                              incDiff,
                              bodyDiff,
                              noLoc,
                              noLoc,
                              noLoc);
    currentBlock().push_back(forStmt);  
  
    return {}; // No expressions are produced.
  }

  ExprDiff ForwardModeVisitor::VisitReturnStmt(const ReturnStmt* RS) {
    auto retValDiff = Visit(RS->getRetValue());
    auto returnStmt =
      m_Sema.ActOnReturnStmt(noLoc,
                             retValDiff.dx(), // return the derivative
                             m_Sema.getCurScope()).get();
    currentBlock().push_back(returnStmt);
    return retValDiff;
  }
  
  ExprDiff ForwardModeVisitor::VisitParenExpr(const ParenExpr* PE) {
    auto subExprDiff = Visit(PE->getSubExpr());
    return {
      BuildParens(subExprDiff.x()),
      BuildParens(subExprDiff.dx())
    };      
  }

  ExprDiff ForwardModeVisitor::VisitMemberExpr(const MemberExpr* ME) {
    MemberExpr* clonedME = dyn_cast<MemberExpr>(Clone(ME));
    // Copy paste from VisitDeclRefExpr.
    QualType Ty = ME->getType();
    if (clonedME->getMemberDecl() == m_IndependentVar)
      return {
        clonedME,
        ConstantFolder::synthesizeLiteral(Ty, m_Context, 1)
      };
    return {
      clonedME,
      ConstantFolder::synthesizeLiteral(Ty, m_Context, 0)
    };
  }

  ExprDiff ForwardModeVisitor::VisitDeclRefExpr(const DeclRefExpr* DRE) {
    auto clonedDRE = dyn_cast<DeclRefExpr>(Clone(DRE));
    auto type = clonedDRE->getType();
    if (auto VD = dyn_cast<VarDecl>(clonedDRE->getDecl())) {
      // If DRE references a variable, try to find if we know something about
      // how it is related to the independent variable.
      auto it = m_Variables.find(VD);
      if (it != std::end(m_Variables)) {
        // If a record was found, use the recorded derivative.
        auto dVar = it->second;
        return { clonedDRE, dVar };
      }
    }
    // Is not a variable or is a reference to something unrelated to independent
    // variable. Derivative is 0.
    return {
      clonedDRE,
      ConstantFolder::synthesizeLiteral(type, m_Context, 0)
    };
  }

  ExprDiff ForwardModeVisitor::VisitIntegerLiteral(
    const IntegerLiteral* IL) {
    llvm::APInt zero(m_Context.getIntWidth(m_Context.IntTy), /*value*/0);
    IntegerLiteral* constant0 = IntegerLiteral::Create(m_Context, zero,
                                                       m_Context.IntTy,
                                                       noLoc);
    return { Clone(IL), constant0 };
  }

  ExprDiff ForwardModeVisitor::VisitFloatingLiteral(
    const FloatingLiteral* FL) {
    llvm::APFloat zero = llvm::APFloat::getZero(FL->getSemantics());
    FloatingLiteral* constant0 =
      FloatingLiteral::Create(m_Context,
                              zero,
                              true,
                              FL->getType(),
                              noLoc);
    return { Clone(FL), constant0 };
  }

  // This method is derived from the source code of both 
  // buildOverloadedCallSet() in SemaOverload.cpp
  // and ActOnCallExpr() in SemaExpr.cpp.
  bool DerivativeBuilder::overloadExists(Expr* UnresolvedLookup,
                                         llvm::MutableArrayRef<Expr*> ARargs) {
    if (UnresolvedLookup->getType() == m_Context.OverloadTy) {
      OverloadExpr::FindResult find = OverloadExpr::find(UnresolvedLookup);
      
      if (!find.HasFormOfMemberPointer) {
        OverloadExpr *ovl = find.Expression;
        
        if (isa<UnresolvedLookupExpr>(ovl)) {
          ExprResult result;
          SourceLocation Loc;
          OverloadCandidateSet CandidateSet(Loc,
                                            OverloadCandidateSet::CSK_Normal);
          Scope* S = m_Sema.getScopeForContext(m_Sema.CurContext);
          UnresolvedLookupExpr *ULE = cast<UnresolvedLookupExpr>(ovl);
          // Populate CandidateSet.
          m_Sema.buildOverloadedCallSet(S, UnresolvedLookup, ULE, ARargs, Loc,
                                        &CandidateSet, &result);
          
          OverloadCandidateSet::iterator Best;
          OverloadingResult OverloadResult =
            CandidateSet.BestViableFunction(m_Sema,
                                            UnresolvedLookup->getLocStart(),
                                            Best);
          if (OverloadResult) // No overloads were found.
            return true;
        }
      }
    }
    return false;
  }

  static NamespaceDecl* LookupBuiltinDerivativesNSD(ASTContext &C, Sema& S) {
    // Find the builtin derivatives namespace
    DeclarationName Name = &C.Idents.get("custom_derivatives");
    LookupResult R(S, Name, SourceLocation(), Sema::LookupNamespaceName,
                   Sema::ForRedeclaration);
    S.LookupQualifiedName(R, C.getTranslationUnitDecl(),
                          /*allowBuiltinCreation*/ false);
    assert(!R.empty() && "Cannot find builtin derivatives!");
    return cast<NamespaceDecl>(R.getFoundDecl());
  }

  Expr* DerivativeBuilder::findOverloadedDefinition(DeclarationNameInfo DNI,
                                       llvm::SmallVectorImpl<Expr*>& CallArgs) {
    if (!m_BuiltinDerivativesNSD)
      m_BuiltinDerivativesNSD = LookupBuiltinDerivativesNSD(m_Context, m_Sema);

    LookupResult R(m_Sema, DNI, Sema::LookupOrdinaryName);
    m_Sema.LookupQualifiedName(R, m_BuiltinDerivativesNSD,
                               /*allowBuiltinCreation*/ false);
    Expr* OverloadedFn = 0;
    if (!R.empty()) {
      CXXScopeSpec CSS;
      Expr* UnresolvedLookup
        = m_Sema.BuildDeclarationNameExpr(CSS, R, /*ADL*/ false).get();

      llvm::MutableArrayRef<Expr*> MARargs
        = llvm::MutableArrayRef<Expr*>(CallArgs);
            
      SourceLocation Loc;
      Scope* S = m_Sema.getScopeForContext(m_Sema.CurContext);
      
      if (overloadExists(UnresolvedLookup, MARargs)) {
        return 0;
      }
      
      OverloadedFn = m_Sema.ActOnCallExpr(S, UnresolvedLookup, Loc,
                                          MARargs, Loc).get();
    }
    return OverloadedFn;
  }
  
  ExprDiff ForwardModeVisitor::VisitCallExpr(const CallExpr* CE) {
    // Find the built-in derivatives namespace.
    std::string s = std::to_string(m_DerivativeOrder);
    if (m_DerivativeOrder == 1)
      s = "";
    IdentifierInfo* II = 0;
    if (m_ArgIndex == 1)
      II = &m_Context.Idents.get(CE->getDirectCallee()->getNameAsString() +
                                 "_d" + s + "arg0");
    else
      II = &m_Context.Idents.get(CE->getDirectCallee()->getNameAsString() +
                                 "_d" + s + "arg" + std::to_string(m_ArgIndex));
    DeclarationName name(II);
    SourceLocation DeclLoc;
    DeclarationNameInfo DNInfo(name, DeclLoc);

    SourceLocation noLoc;
    llvm::SmallVector<Expr*, 4> CallArgs;
    // For f(g(x)) = f'(x) * g'(x)
    Expr* Multiplier = 0;
    for (size_t i = 0, e = CE->getNumArgs(); i < e; ++i) {
      auto argDiff = Visit(CE->getArg(i));
      if (!Multiplier)
        Multiplier = argDiff.dx();
      else {
        Multiplier =
          BuildOp(BO_Add, Multiplier, argDiff.dx());
      }
      CallArgs.push_back(argDiff.x());
    }

    auto call =
      m_Sema.ActOnCallExpr(m_Sema.getScopeForContext(m_Sema.CurContext),
                           Clone(CE->getCallee()),
                           noLoc,
                           llvm::MutableArrayRef<Expr*>(CallArgs),
                           noLoc).get();
    // Store the result of the call in a variable so that the function is 
    // not called multiple times;
    call = StoreAndRef(call);

    Expr* callDiff =
      m_Builder.findOverloadedDefinition(DNInfo, CallArgs);
    if (callDiff) {
      // f_darg0 function was found.
      if (Multiplier)
        callDiff = BuildOp(BO_Mul,
                           callDiff,
                           BuildParens(Multiplier));
      return {
        call,
        callDiff
      };
    }

    // Check if it is a recursive call.
    if (CE->getDirectCallee() == m_Function) {
      // The differentiated function is called recursively.
      auto derivativeRef =
        m_Sema.BuildDeclarationNameExpr(CXXScopeSpec(),
                                        m_Derivative->getNameInfo(),
                                        m_Derivative).get();
      auto selfCallDiff =
        m_Sema.ActOnCallExpr(m_Sema.getScopeForContext(m_Sema.CurContext),
                             derivativeRef,
                             noLoc,
                             llvm::MutableArrayRef<Expr*>(CallArgs),
                             noLoc).get();
      if (Multiplier)
        selfCallDiff = BuildOp(BO_Mul, selfCallDiff, Multiplier);
      return {
        call,
        selfCallDiff
      };
    }  

    Expr* OverloadedFnInFile
      = m_Builder.findOverloadedDefinition(CE->getDirectCallee()->getNameInfo(),
                                           CallArgs);

    if (OverloadedFnInFile) {
      // Take the function to derive from the source.
      const FunctionDecl* FD = CE->getDirectCallee();
      // Get the definition, if any.
      const FunctionDecl* mostRecentFD = FD->getMostRecentDecl();
      while (mostRecentFD && !mostRecentFD->isThisDeclarationADefinition()) {
        mostRecentFD = mostRecentFD->getPreviousDecl();
      }
      if (!mostRecentFD || !mostRecentFD->isThisDeclarationADefinition()) {
        diag(DiagnosticsEngine::Error,
             "attempted differention of function '%0', which does not have a \
              definition",
             { FD->getNameAsString() },
             FD->getLocEnd());
        auto zero = 
          ConstantFolder::synthesizeLiteral(call->getType(),
                                            m_Context,
                                            0);
        return {
          call,
          zero
        };
      }

      // Look for a declaration of a function to differentiate
      // in the derivatives namespace.
      LookupResult R(m_Sema, CE->getDirectCallee()->getNameInfo(),
                     Sema::LookupOrdinaryName);
      m_Sema.LookupQualifiedName(R, m_Builder.m_BuiltinDerivativesNSD,
                                 /*allowBuiltinCreation*/ false);
      {
        DeclContext::lookup_result res
          = m_Context.getTranslationUnitDecl()->lookup(name);
        bool shouldAdd = true;
        for (DeclContext::lookup_iterator I = res.begin(), E = res.end();
             I != E; ++I) {
          for (LookupResult::iterator J = R.begin(), E = R.end(); J != E; ++J)
            if (cast<ValueDecl>(*I)->getType().getTypePtr()
                == cast<ValueDecl>(J.getDecl())->getType().getTypePtr()) {
              shouldAdd = false;
              break;
            }
          if (shouldAdd)
            R.addDecl(*I);
          shouldAdd = true;
        }
        assert(!R.empty() && "Must be reachable");
      }      // Update function name in the source.
      CXXScopeSpec CSS;
      Expr* ResolvedLookup
        = m_Sema.BuildDeclarationNameExpr(CSS, R, /*ADL*/ false).get();
      CallExpr* clonedCE = dyn_cast<CallExpr>(Clone(CE));
      clonedCE->setCallee(ResolvedLookup);
      // FIXME: What is this part doing? Is it reachable at all?
      // Shouldn't it be multiplied by arg derivatives?
      return {
        call,
        clonedCE
      };
    }

    // Function was not derived => issue a warning.
    diag(DiagnosticsEngine::Warning,
         "function '%0' was not differentiated because it is not declared in \
          namespace 'custom_derivatives' attempted differention of function \
          '%0', which does not have a definition",
         { CE->getDirectCallee()->getNameAsString() },
         CE->getDirectCallee()->getLocEnd());
    
    return {
      call,
      ConstantFolder::synthesizeLiteral(
        call->getType(),
        m_Context,
        0)
    };
  }
  
  void DerivativeBuilder::updateReferencesOf(Stmt* InSubtree) {
    utils::ReferencesUpdater up(m_Sema, m_NodeCloner.get(), m_CurScope.get());
    up.TraverseStmt(InSubtree);
  }

  ExprDiff ForwardModeVisitor::VisitUnaryOperator(
    const UnaryOperator* UnOp) {
    auto diff = Visit(UnOp->getSubExpr());
    auto opKind = UnOp->getOpcode();
    auto op = BuildOp(opKind, diff.x());
    // If opKind is unary plus or minus, apply that op to derivative.
    // Otherwise, the derivative is 0.
    // FIXME: add support for other unary operators 
    if (opKind == UO_Plus || opKind == UO_Minus) {
      return {
        op,
        BuildOp(opKind, diff.dx())
      };
    }
    else {
      diag(DiagnosticsEngine::Warning,
           "attempt to differentiate unsupported unary operator, derivative \
            set to 0",
           {},
           UnOp->getLocEnd());
      auto zero = 
        ConstantFolder::synthesizeLiteral(op->getType(),
                                          m_Context,
                                          0);
      return {
        op,
        zero
      };
    }
  }

  ExprDiff ForwardModeVisitor::VisitBinaryOperator(
    const BinaryOperator* BinOp) {

    auto Ldiff = Visit(BinOp->getLHS());
    auto Rdiff = Visit(BinOp->getRHS());

    ConstantFolder folder(m_Context);
    auto opCode = BinOp->getOpcode();
    Expr* opDiff = nullptr;
    
    if (opCode == BO_Mul) {
      opDiff =
        BuildOp(BO_Add,
                BuildOp(BO_Mul, Ldiff.dx(), Rdiff.x()),
                BuildOp(BO_Mul, Ldiff.x(), Rdiff.dx()));
      opDiff = folder.fold(opDiff);
      opDiff = StoreAndRef(opDiff);
    }
    else if (opCode == BO_Div) {
      auto nom =
        BuildOp(BO_Sub, 
                BuildOp(BO_Mul, Ldiff.dx(), Rdiff.x()),
                BuildOp(BO_Mul, Ldiff.x(), Rdiff.dx()));
      nom = BuildParens(nom);
      auto denom = 
        BuildOp(BO_Mul, Rdiff.x(), Rdiff.x());
      denom = BuildParens(denom);
      opDiff = BuildOp(BO_Div, nom, denom);
      opDiff = folder.fold(opDiff);
      opDiff = StoreAndRef(opDiff);
    }
    else if (opCode == BO_Add) {
      opDiff = BuildOp(BO_Add,
                       Ldiff.dx(),
                       Rdiff.dx());
      opDiff = folder.fold(opDiff);
      opDiff = StoreAndRef(opDiff);
    }
    else if (opCode == BO_Sub) {
      opDiff = BuildOp(BO_Sub,
                       Ldiff.dx(),
                       BuildParens(Rdiff.dx()->IgnoreParens()));
      opDiff = folder.fold(opDiff);
      opDiff = StoreAndRef(opDiff);
    }
    else if (opCode == BO_Assign) {
      if (isa<DeclRefExpr>(Ldiff.dx())) {
        opDiff = BuildOp(BO_Assign,
                         Ldiff.dx(),
                         Rdiff.dx());
        currentBlock().push_back(opDiff);
      }
    }     
    else {
      //FIXME: add support for other binary operators
      diag(DiagnosticsEngine::Warning,
           "attempt to differentiate unsupported binary operator, derivative \
            set to 0",
           {},
           BinOp->getLocEnd());
      opDiff =
        ConstantFolder::synthesizeLiteral(BinOp->getType(),
                                          m_Context,
                                          0);
    }   

    auto op = BuildOp(opCode, Ldiff.x(), Rdiff.x());
    if (opCode != BO_Assign)
      op = StoreAndRef(op);
    else
      currentBlock().push_back(op);

    return {
      op,
      opDiff
    };
  }

  ExprDiff ForwardModeVisitor::VisitDeclStmt(const DeclStmt* DS) {
    llvm::SmallVector<Decl*, 4> decls;
    for (auto D : DS->decls()) {
      if (auto VD = dyn_cast<VarDecl>(D)) {
        // If variable is initialized with some expression, derive the
        // expression and store it in the table.
        if (VD->hasInit()) {
          auto initDiff = Visit(VD->getInit());
          auto declDiff =
            StoreAndRef(initDiff.dx(),
                        VD->getType(),
                        "_d_" + VD->getNameAsString()); 
          VD =
            BuildVarDecl(VD->getType(),
                         VD->getIdentifier(),
                         initDiff.x()); 
          m_Variables.emplace(VD, declDiff);
        }
        else {
          VD = BuildVarDecl(VD->getType(),
                            VD->getIdentifier(),
                            nullptr);
        }
        m_CurScope->AddDecl(VD);
        //TODO: clean the idResolver chain!!!!!
        if (VD->getIdentifier())
          m_Sema.IdResolver.AddDecl(VD);
        decls.push_back(VD);
      }
      else {
        diag(DiagnosticsEngine::Warning,
             "Unsupported declaration",
             {},
             D->getLocEnd());
      }
    }
    auto newDS = BuildDeclStmt(decls);
    currentBlock().push_back(newDS);
    return {};
  }

  ExprDiff
  ForwardModeVisitor::VisitImplicitCastExpr(const ImplicitCastExpr* ICE) {
    auto subExprDiff = Visit(ICE->getSubExpr());
    
    // FIXME: is it allways correct to cast to the same type and via the same
    // cast kind?
    return {
      ImplicitCastExpr::Create(m_Context,
                               ICE->getType(),
                               ICE->getCastKind(),
                               subExprDiff.x(),
                               // FIXME: add cast path in case of derived to
                               // base cast.
                               nullptr, 
                               ICE->getValueKind()),
      ImplicitCastExpr::Create(m_Context,
                               ICE->getType(),
                               ICE->getCastKind(),
                               subExprDiff.dx(),
                               // FIXME: add cast path in case of derived to
                               // base cast.
                               nullptr, 
                               ICE->getValueKind())
    };  
  }

  ExprDiff
  ForwardModeVisitor::
  VisitCXXOperatorCallExpr(const CXXOperatorCallExpr* OpCall) {
    // This operator gets emitted when there is a binary operation containing
    // overloaded operators. Eg. x+y, where operator+ is overloaded.
    diag(DiagnosticsEngine::Error,
         "We don't support overloaded operators yet!",
         {},
         OpCall->getLocEnd());
    return {};
  }

  Stmt* VisitorBase::Clone(const Stmt* s) {
    return m_Builder.Clone(s);
  }
  Expr* VisitorBase::Clone(const Expr* e) {
    return m_Builder.Clone(e);
  }

  ReverseModeVisitor::ReverseModeVisitor(DerivativeBuilder& builder):
    VisitorBase(builder) {}

  ReverseModeVisitor::~ReverseModeVisitor() {}

  FunctionDecl* ReverseModeVisitor::Derive(
    FunctionDeclInfo& FDI, const DiffPlan& plan) {
    m_Function = FDI.getFD();
    assert(m_Function && "Must not be null.");
   
    // We name the gradient of f as f_grad.
    auto derivativeBaseName = m_Function->getNameAsString();
    IdentifierInfo* II = &m_Context.Idents.get(derivativeBaseName + "_grad");
    DeclarationNameInfo name(II, noLoc);

    // A vector of types of the gradient function parameters.
    llvm::SmallVector<QualType, 16> paramTypes(m_Function->getNumParams() + 1);
    std::transform(m_Function->param_begin(),
                   m_Function->param_end(),
                   std::begin(paramTypes),
                   [] (const ParmVarDecl* PVD) {
                     return PVD->getType();
                   });
    // The last parameter is the output parameter of the R* type.
    paramTypes.back() = m_Context.getPointerType(m_Function->getReturnType());
    // For a function f of type R(A1, A2, ..., An),
    // the type of the gradient function is void(A1, A2, ..., An, R*).
    auto gradientFunctionType = 
      m_Context.getFunctionType(m_Context.VoidTy,
                                llvm::ArrayRef<QualType>(paramTypes.data(),
                                                         paramTypes.size()),
                                // Cast to function pointer.
                                FunctionProtoType::ExtProtoInfo());

    // Create the gradient function declaration.
    FunctionDecl* gradientFD = nullptr;
    if (isa<CXXMethodDecl>(m_Function)) {
      auto CXXRD = cast<CXXRecordDecl>(m_Function->getDeclContext());
      gradientFD = CXXMethodDecl::Create(m_Context,
                                         CXXRD,
                                         noLoc,
                                         name,
                                         gradientFunctionType,
                                         m_Function->getTypeSourceInfo(),
                                         m_Function->getStorageClass(),
                                         m_Function->isInlineSpecified(),
                                         m_Function->isConstexpr(),
                                         noLoc);
      gradientFD->setAccess(m_Function->getAccess());
    }
    else if (isa<FunctionDecl>(m_Function)) {
      gradientFD = FunctionDecl::Create(m_Context,
                                        m_Function->getDeclContext(),
                                        noLoc,
                                        name,
                                        gradientFunctionType,
                                        m_Function->getTypeSourceInfo(),
                                        m_Function->getStorageClass(),
                                        m_Function->isInlineSpecified(),
                                        m_Function->hasWrittenPrototype(),
                                        m_Function->isConstexpr());
    }
    else {
      diag(DiagnosticsEngine::Error,
           "attempted differention of '%0' which is of unsupported type",
           { m_Function->getNameAsString() },
           m_Function->getLocEnd());
      return nullptr;
    }
    m_Derivative = gradientFD;
         
    m_CurScope.reset(new Scope(m_Sema.TUScope, Scope::FnScope,
                               m_Sema.getDiagnostics()));

    // Create parameter declarations.
    llvm::SmallVector<ParmVarDecl*, 4> params(paramTypes.size());
    std::transform(m_Function->param_begin(),
                   m_Function->param_end(),
                   std::begin(params),
                   [&] (const ParmVarDecl* PVD) {
                     auto VD = 
                       ParmVarDecl::Create(m_Context,
                                           gradientFD,
                                           noLoc,
                                           noLoc,
                                           PVD->getIdentifier(),
                                           PVD->getType(),
                                           PVD->getTypeSourceInfo(),
                                           PVD->getStorageClass(),
                                           // Clone default arg if present.
                                           (PVD->hasDefaultArg() ?  
                                             Clone(PVD->getDefaultArg()) :
                                             nullptr));
                     if (VD->getIdentifier()) {
                       m_CurScope->AddDecl(VD);
                       m_Sema.IdResolver.AddDecl(VD);
                     }
                     return VD;
                   });
    // The output paremeter "_result".
    params.back() =
      ParmVarDecl::Create(m_Context,
                          gradientFD,
                          noLoc,
                          noLoc,
                          &m_Context.Idents.get("_result"),
                          paramTypes.back(),
                          m_Context.getTrivialTypeSourceInfo(paramTypes.back(),
                                                             noLoc),
                          params.front()->getStorageClass(),
                          // No default value.
                          nullptr);
    if (params.back()->getIdentifier()) {
      m_CurScope->AddDecl(params.back());
      m_Sema.IdResolver.AddDecl(params.back());
    }

    llvm::ArrayRef<ParmVarDecl*> paramsRef =
      llvm::makeArrayRef(params.data(), params.size());
    gradientFD->setParams(paramsRef);
    gradientFD->setBody(nullptr);

    Sema::SynthesizedFunctionScope Scope(m_Sema, gradientFD);
    // Reference to the output parameter.
    m_Result = m_Sema.BuildDeclRefExpr(params.back(),
                                       paramTypes.back(),
                                       VK_LValue,
                                       noLoc).get();
    // Initially, df/df = 1.
    auto dfdf = ConstantFolder::synthesizeLiteral(m_Function->getReturnType(),
                                                  m_Context,
                                                  1.0);

    auto bodyStmts = startBlock();
    // Start the visitation process which outputs the statements in the current
    // block.
    auto functionBody = m_Function->getMostRecentDecl()->getBody();
    Visit(functionBody, dfdf);
    // Create the body of the function.
    auto gradientBody = finishBlock();

    gradientFD->setBody(gradientBody);
    // Cleanup the IdResolver chain.
    for(FunctionDecl::param_iterator I = gradientFD->param_begin(),
        E = gradientFD->param_end(); I != E; ++I) {
      if ((*I)->getIdentifier()) {
        m_CurScope->RemoveDecl(*I);
        //m_Sema.IdResolver.RemoveDecl(*I); // FIXME: Understand why that's bad
      }
    }

    return gradientFD;
  }

  void ReverseModeVisitor::VisitCompoundStmt(const CompoundStmt* CS) {
    for (CompoundStmt::const_body_iterator I = CS->body_begin(),
           E = CS->body_end(); I != E; ++I)
        Visit(*I, dfdx());
  }

  void ReverseModeVisitor::VisitIfStmt(const clang::IfStmt* If) {
    if (If->getConditionVariable())
        // FIXME:Visit(If->getConditionVariableDeclStmt(), dfdx());
        llvm_unreachable("variable declarations are not currently supported");
    auto cond = Clone(If->getCond());
    auto thenStmt = If->getThen();
    auto elseStmt = If->getElse();
   
    Stmt* thenBody = nullptr;
    Stmt* elseBody = nullptr;
    if (thenStmt) {
      auto thenBlock = startBlock();
      Visit(thenStmt, dfdx());
      thenBody = finishBlock();
    }
    if (elseStmt) {
      auto elseBlock = startBlock();
      Visit(elseStmt, dfdx());
      elseBody = finishBlock();
    }

    auto ifStmt =
      new (m_Context) IfStmt(m_Context,
                             noLoc,
                             If->isConstexpr(),
                             // FIXME: add init for condition variable
                             nullptr,
                             // FIXME: add condition variable decl
                             nullptr,
                             cond,
                             thenBody,
                             noLoc,
                             elseBody);
    currentBlock().push_back(ifStmt);  
  }

  void ReverseModeVisitor::VisitConditionalOperator(
    const clang::ConditionalOperator* CO) {
    auto condVar = StoreAndRef(Clone(CO->getCond()));
    auto cond =
      m_Sema.ActOnCondition(m_CurScope.get(),
                            noLoc,
                            condVar,
                            Sema::ConditionKind::Boolean).get().second;
    auto ifTrue = CO->getTrueExpr();
    auto ifFalse = CO->getFalseExpr();

    auto VisitBranch =
      [&] (Stmt* branch, Expr* ifTrue, Expr* ifFalse) {
        if (!branch)
          return;
        auto condExpr =
          new (m_Context) ConditionalOperator(cond,
                                              noLoc,
                                              ifTrue,
                                              noLoc,
                                              ifFalse,
                                              ifTrue->getType(),
                                              VK_RValue,
                                              OK_Ordinary);
        
        auto dStmt = new (m_Context) ParenExpr(noLoc,
                                               noLoc,
                                               condExpr);
        Visit(branch, dStmt);
    };
   
    // FIXME: not optimal, creates two (condExpr ? ... : ...) expressions,
    // so cond is unnesarily checked twice. 
    // Can be improved by storing the result of condExpr in a temporary.

    auto zero = ConstantFolder::synthesizeLiteral(dfdx()->getType(),
                                                  m_Context,
                                                  0);
    //xi = (cond ? ifTrue : ifFalse)
    //dxi/d ifTrue = (cond ? 1 : 0)
    //df/d ifTrue += df/dxi * dxi/d ifTrue = (cond ? df/dxi : 0)
    VisitBranch(ifTrue, dfdx(), zero);
    //dxi/d ifFalse = (cond ? 0 : 1)
    //df/d ifFalse += df/dxi * dxi/d ifFalse = (cond ? 0 : df/dxi)
    VisitBranch(ifFalse, zero, dfdx());
  }

  void ReverseModeVisitor::VisitReturnStmt(const ReturnStmt* RS) {
    Visit(RS->getRetValue(), dfdx());
  }
  
  void ReverseModeVisitor::VisitParenExpr(const ParenExpr* PE) {
    Visit(PE->getSubExpr(), dfdx());
  }

  void ReverseModeVisitor::VisitDeclRefExpr(const DeclRefExpr* DRE) {
    auto decl = DRE->getDecl();
    // Check DeclRefExpr is a reference to an independent variable.
    auto it = std::find(m_Function->param_begin(),
                        m_Function->param_end(),
                        decl);
    if (it == m_Function->param_end()) {
      // Is not an independent variable, ignored.
      return;
    }
    auto idx = std::distance(m_Function->param_begin(), it);
    auto size_type = m_Context.getSizeType();
    auto size_type_bits = m_Context.getIntWidth(size_type);
    // Create the idx literal.
    auto i = IntegerLiteral::Create(m_Context,
                                    llvm::APInt(size_type_bits, idx),
                                    size_type,
                                    noLoc);
    // Create the _result[idx] expression.
    auto result_at_i =
      m_Sema.CreateBuiltinArraySubscriptExpr(m_Result,
                                             noLoc,
                                             i,
                                             noLoc).get();
    // Create the (_result[idx] += dfdx) statement.
    auto add_assign = BuildOp(BO_AddAssign, result_at_i, dfdx());
    // Add it to the body statements.
    currentBlock().push_back(add_assign);
  }

  void ReverseModeVisitor::VisitIntegerLiteral(const IntegerLiteral* IL) {
    // Nothing to do with it.
  }

  void ReverseModeVisitor::VisitFloatingLiteral(const FloatingLiteral* FL) {
    // Nothing to do with it.
  }
  
  void ReverseModeVisitor::VisitCallExpr(const CallExpr* CE) {
    auto FD = CE->getDirectCallee();
    if (!FD) {
      diag(DiagnosticsEngine::Warning,
           "attempted differentiation of something that is not a direct call \
            to a function and is not supported yet. Ignored.");
      return;
    }
    IdentifierInfo* II = nullptr;
    auto NArgs = FD->getNumParams();
    // If the function has no args then we assume that it is not related
    // to independent variables and does not contribute to gradient.
    if (!NArgs)
      return;

    llvm::SmallVector<Expr*, 16> CallArgs(CE->getNumArgs());
    std::transform(CE->arg_begin(), CE->arg_end(), std::begin(CallArgs),
      [this](const Expr* Arg) { return Clone(Arg); });

    VarDecl* ResultDecl = nullptr;
    Expr* Result = nullptr;
    // If the function has a single arg, we look for a derivative w.r.t. to 
    // this arg (it is unlikely that we need gradient of a one-dimensional'
    // function).
    if (NArgs == 1)
      II = &m_Context.Idents.get(FD->getNameAsString() + "_darg0");
    // If it has more args, we look for its gradient.
    else {
      II = &m_Context.Idents.get(FD->getNameAsString() + "_grad");
      // We also need to create an array to store the result of gradient call.
      auto size_type_bits = m_Context.getIntWidth(m_Context.getSizeType());
      auto ArrayType =
        m_Context.getConstantArrayType(CE->getType(),
                                       llvm::APInt(size_type_bits, NArgs),
                                       ArrayType::ArraySizeModifier::Normal,
                                       0); // No IndexTypeQualifiers

      // Create {} array initializer to fill it with zeroes.
      auto ZeroInitBraces = m_Sema.ActOnInitList(noLoc,
                                                 {},
                                                 noLoc).get();
      // Declare: Type _gradX[Nargs];
      ResultDecl = BuildVarDecl(ArrayType,
                                CreateUniqueIdentifier("_grad", m_tmpId));
      // Add zero-initializer : Type _gradX[Nargs] = {};
      m_Sema.AddInitializerToDecl(ResultDecl,
                                  ZeroInitBraces,
                                  /* DirectInit */ false);
      Result = m_Sema.BuildDeclRefExpr(ResultDecl,
                                       ArrayType,
                                       VK_LValue,
                                       noLoc).get();
      // Pass the array as the last parameter for gradient.
      CallArgs.push_back(Result);
    }
      
    // Try to find it in builtin derivatives
    DeclarationName name(II);
    DeclarationNameInfo DNInfo(name, noLoc);
    auto OverloadedDerivedFn =
      m_Builder.findOverloadedDefinition(DNInfo, CallArgs);

    // Derivative was not found, check if it is a recursive call
    if (!OverloadedDerivedFn) {
      if (FD != m_Function) {
        // Not a recursive call, derivative was not found, ignore.
        // Issue a warning.
        diag(DiagnosticsEngine::Warning,
             "function '%0' was not differentiated because it is not declared \
              in namespace 'custom_derivatives'",
             { FD->getNameAsString() },
             CE->getDirectCallee()->getLocEnd());
        return;
      }
      // Recursive call.
      auto selfRef = m_Sema.BuildDeclarationNameExpr(CXXScopeSpec(),
                                                     m_Derivative->getNameInfo(),
                                                     m_Derivative).get();

      OverloadedDerivedFn =
        m_Sema.ActOnCallExpr(m_Sema.getScopeForContext(m_Sema.CurContext),
                             selfRef,
                             noLoc,
                             llvm::MutableArrayRef<Expr*>(CallArgs),
                             noLoc).get(); 
    }

    if (OverloadedDerivedFn) {
      // Derivative was found.
      if (NArgs == 1) {
        // If function has a single arg, call it and store a result.
        Result = StoreAndRef(OverloadedDerivedFn);
        auto d = BuildOp(BO_Mul, dfdx(), Result);
        auto dTmp = StoreAndRef(d);
        Visit(CE->getArg(0), dTmp);
      }
      else {
        // Put Result array declaration in the function body.
        currentBlock().push_back(BuildDeclStmt(ResultDecl));
        // Call the gradient, passing Result as the last Arg.
        currentBlock().push_back(OverloadedDerivedFn);
        // Visit each arg with df/dargi = df/dxi * Result[i].
        for (unsigned i = 0; i < CE->getNumArgs(); i++) {
          auto size_type = m_Context.getSizeType();
          auto size_type_bits = m_Context.getIntWidth(size_type);
          // Create the idx literal.
          auto I =
            IntegerLiteral::Create(m_Context,
                                   llvm::APInt(size_type_bits, i),
                                   size_type,
                                   noLoc);
          // Create the Result[I] expression.
          auto ithResult =
            m_Sema.CreateBuiltinArraySubscriptExpr(Result,
                                                   noLoc,
                                                   I,
                                                   noLoc).get();
          auto di = BuildOp(BO_Mul, dfdx(), ithResult);
          auto diTmp = StoreAndRef(di);
          Visit(CE->getArg(i), diTmp);
        }
      }
    }
  }

  void ReverseModeVisitor::VisitUnaryOperator(const UnaryOperator* UnOp) {
    auto opCode = UnOp->getOpcode();
    if (opCode == UO_Plus)
      //xi = +xj
      //dxi/dxj = +1.0
      //df/dxj += df/dxi * dxi/dxj = df/dxi
      Visit(UnOp->getSubExpr(), dfdx());
    else if (opCode == UO_Minus) {
      //xi = -xj
      //dxi/dxj = -1.0
      //df/dxj += df/dxi * dxi/dxj = -df/dxi
      auto d = BuildOp(UO_Minus, dfdx());
      Visit(UnOp->getSubExpr(), d);
    }
    else
      llvm_unreachable("unsupported unary operator");
  }

  void ReverseModeVisitor::VisitBinaryOperator(const BinaryOperator* BinOp) {
    auto opCode = BinOp->getOpcode();

    auto L = BinOp->getLHS();
    auto R = BinOp->getRHS();

    if (opCode == BO_Add) {
      //xi = xl + xr
      //dxi/xl = 1.0
      //df/dxl += df/dxi * dxi/xl = df/dxi
      Visit(L, dfdx());
      //dxi/xr = 1.0
      //df/dxr += df/dxi * dxi/xr = df/dxi
      Visit(R, dfdx());
    }
    else if (opCode == BO_Sub) {
      //xi = xl - xr
      //dxi/xl = 1.0
      //df/dxl += df/dxi * dxi/xl = df/dxi
      Visit(L, dfdx());
      //dxi/xr = -1.0
      //df/dxl += df/dxi * dxi/xr = -df/dxi
      auto dr = BuildOp(UO_Minus, dfdx());
      Visit(R, dr);
    }
    else if (opCode == BO_Mul) {
      //xi = xl * xr
      //dxi/xl = xr
      //df/dxl += df/dxi * dxi/xl = df/dxi * xr
      auto dl = BuildOp(BO_Mul, dfdx(), Clone(R));
      auto dlTmp = StoreAndRef(dl);
      Visit(L, dlTmp);
      //dxi/xr = xl
      //df/dxr += df/dxi * dxi/xr = df/dxi * xl
      auto dr = BuildOp(BO_Mul, Clone(L), dfdx());
      auto drTmp = StoreAndRef(dr);
      Visit(R, drTmp);
    }
    else if (opCode == BO_Div) {
      //xi = xl / xr
      //dxi/xl = 1 / xr
      //df/dxl += df/dxi * dxi/xl = df/dxi * (1/xr)
      auto clonedR = Clone(R);
      auto dl = BuildOp(BO_Div, dfdx(), clonedR);
      auto dlTmp = StoreAndRef(dl);
      Visit(L, dlTmp);
      //dxi/xr = -xl / (xr * xr)
      //df/dxl += df/dxi * dxi/xr = df/dxi * (-xl /(xr * xr))
      // Wrap R * R in parentheses: (R * R). otherwise code like 1 / R * R is
      // produced instead of 1 / (R * R).
      auto RxR =
        m_Sema.ActOnParenExpr(noLoc,
                              noLoc,
                              BuildOp(BO_Mul, clonedR, clonedR)).get();
      auto dr =
        BuildOp(BO_Mul,
                dfdx(),
                BuildOp(UO_Minus,
                        BuildOp(BO_Div, Clone(L), RxR)));
      auto drTmp = StoreAndRef(dr);
      Visit(R, drTmp);
    }
    else
      llvm_unreachable("unsupported binary operator");
  }

  void ReverseModeVisitor::VisitDeclStmt(const DeclStmt* DS) {
    llvm_unreachable("declarations are not supported yet");
  }

  void ReverseModeVisitor::VisitImplicitCastExpr(const ImplicitCastExpr* ICE) {
    Visit(ICE->getSubExpr(), dfdx());
  }

  void ReverseModeVisitor::VisitMemberExpr(const MemberExpr* ME) {
    // We do not treat struct members as independent variables, so they are not
    // differentiated.
  }

  
} // end namespace clad
