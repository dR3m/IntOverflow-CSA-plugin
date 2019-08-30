#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Frontend/CheckerRegistry.h"
#include "clang/AST/Attr.h"
#include "clang/Basic/Builtins.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include <climits>
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/AnalysisManager.h"
#include <sstream>

using namespace clang;
using namespace ento;
using namespace std;

//-------------------------------------------------ASTWALKER--------------------------------------------
namespace {
	class ASTWalker : public RecursiveASTVisitor<ASTWalker> {
		private:
			const CheckerBase *Checker = nullptr;
			ASTContext *ASTCntxt;
			AnalysisDeclContext *ADCntxt = nullptr;
			//BugReporter &BReporter;
			map<string, unsigned> IntSizes = {
				{"char", 8},
				{"short", 16},
				{"int", 32},
				{"long", 64},
				{"long long", 128},
				{"unsigned char", 8},
				{"unsigned short", 16},
				{"unsigned int", 32},
				{"unsigned long", 64},
				{"unsigned long long", 128},
			};
			map<string, map<string, unsigned>> BitFieldSizes = {};
			llvm::raw_ostream &logger = llvm::outs();
			string endl = "\n";

		public:
			ASTWalker(const CheckerBase *C, ASTContext *ASTCntxt, AnalysisDeclContext *ADCntxt) : Checker(C), ASTCntxt(ASTCntxt), ADCntxt(ADCntxt) {};
			ASTWalker(ASTContext *ASTCntxt) : ASTCntxt(ASTCntxt) {};

			bool VisitCastExpr(CastExpr *Cast);
			bool VisitBinAssign(BinaryOperator *Node);

			void Traverse() {TraverseAST(*ASTCntxt);};
			bool IOCastCheck(CastExpr *E);
			bool findSubIntegerLiteral(Expr *E);
			void getLocString(SourceLocation Loc);
	};
}

void ASTWalker::getLocString(SourceLocation Loc){
	FullSourceLoc FullLoc = ASTCntxt->getFullLoc(Loc);
	logger << "source location: " << FullLoc.getSpellingLineNumber() << ":";
	logger << FullLoc.getSpellingColumnNumber() << endl;
}

//FIX: Now BitFields checks seperately. May warn about same piece of code several times. (And one will be correct and another - not)
bool ASTWalker::IOCastCheck(CastExpr *E){
	bool isIO = false;
	if (E->getCastKind() == CK_IntegralCast){ //getCastKindName to print
		QualType CastType = E->getType(); // Final cast type

		Expr *SubE = E->getSubExpr();
		QualType SubType = SubE->getType();
		//logger << CastType.getAsString() << " and " << SubType.getAsString() << endl;

		if (CastType->isSignedIntegerType() != SubType->isSignedIntegerType()){
			isIO = true;	
			logger << "Potential IO: CWE-194 - Unexpected Sign Extension" << endl;
			getLocString(E->getExprLoc());
		}

		if (CastType->isBuiltinType() and SubType->isBuiltinType()){
				// Check for canonical type for cases then type is like __uint8_t. Then translate it to canonical unsigned char.
				string s1 = CastType.isCanonical() ? CastType.getAsString() : CastType.getCanonicalType().getAsString();
				string s2 = SubType.isCanonical() ? SubType.getAsString() : SubType.getCanonicalType().getAsString();
				
				// Get type size.
				unsigned t1 = IntSizes[s1]; 
				unsigned t2 = IntSizes[s2];
					
				if ((t1 < t2)){
					isIO = true;
					logger << "Potential IO: CWE-197 - Numeric Truncation Error, "; 
					logger << s1 << " (" << t1 << " bit) and " ; 
					logger << s2 << " (" << t2 << " bit)" << endl ; 
					getLocString(E->getExprLoc());
				}
				
				/*if (isIO && (t1 > t2)){ //That IF statement is useless, just for additional warning
					logger << "Potential IO: Different sing + bit increase, "; 
					logger << s1 << " (" << t1 << " bit) and " ; 
					logger << s2 << " (" << t2 << " bit)" << endl ; 
				}*/
		}
	}
	if (isIO) 
		logger << endl;
	return isIO;
}

// TODO: Replace it with functions from ASTMatcher class
bool ASTWalker::findSubIntegerLiteral(Expr *E){
	for (Expr::child_iterator C = E->child_begin(); C != E->child_end(); C++) {
		logger << C->getStmtClassName() << endl;
	}
	return true;
}

//?watch node with any bin operation
bool ASTWalker::VisitBinAssign(BinaryOperator *Node){
	Expr *LH = Node->getLHS();
	Expr *RH = Node->getRHS();
	
	FieldDecl *BF1 = LH->getSourceBitField();
	FieldDecl *BF2 = RH->getSourceBitField();
	
	QualType LType =  LH->getType();
	QualType RType =  RH->getType();
	
	string s1 = LType.isCanonical() ? LType.getAsString() : LType.getCanonicalType().getAsString();
	string s2 = RType.isCanonical() ? RType.getAsString() : RType.getCanonicalType().getAsString();
				
	unsigned t1 = BF1 != nullptr ?  BF1->getBitWidthValue(*ASTCntxt) : IntSizes[s1]; 
	unsigned t2 = BF2 != nullptr ?  BF2->getBitWidthValue(*ASTCntxt) : IntSizes[s2];

	if ((t1 < t2)){
		logger << "Potential IO: Bit truncation, "; 
		logger << s1 << " (" << t1 << " bit) and " ; 
		logger << s2 << " (" << t2 << " bit)" << endl ; 
	}

	return true;
}

//For all cast types
//CastKind in ASTBitCodes.h
//Finding Integer Implicit Cast and check it
bool ASTWalker::VisitCastExpr(CastExpr *E){
	IOCastCheck(E);
		//getLocString(E->getBeginLoc());
		//Report(E->getSourceRange(), 1);
	return true;
}

//-------------------------------------------Taint----------------------------------------------------------------------------
namespace {
class TestChecker : public Checker<check::PostStmt<CallExpr>, check::PreStmt<CallExpr>, check::ASTCodeBody> {
	public:
	static void *getTag() {
		static int Tag;
		return &Tag;
	}

	struct CheckerOpts {
		string RawInp;
		vector<string> UserInpFuncName;
		void splitRaw() {
			istringstream iss(RawInp);
			string tmp;
			while (!iss.eof()){
				iss >> tmp;
				UserInpFuncName.push_back(tmp);
			}
		};
	};
	CheckerOpts Opts;
	void checkASTCodeBody(const Decl *D, AnalysisManager &AM, BugReporter &BR) const;

	void checkPostStmt(const CallExpr *CE, CheckerContext &C) const;
	void checkPreStmt(const CallExpr *CE, CheckerContext &C) const;

	private:
	static const unsigned InvalidArgIndex = UINT_MAX;
	/// Denotes the return vale.
	static const unsigned ReturnValueIndex = UINT_MAX - 1;

	/// Catch taint related bugs. Check if tainted data is passed to a
	/// system call etc.
	bool checkPre(const CallExpr *CE, CheckerContext &C) const;

	/// Add taint sources on a pre-visit.
	void addSourcesPre(const CallExpr *CE, CheckerContext &C) const;

	/// Propagate taint generated at pre-visit.
	bool propagateFromPre(const CallExpr *CE, CheckerContext &C) const;

	/// Add taint sources on a post visit.
	void addSourcesPost(const CallExpr *CE, CheckerContext &C) const;

	/// Given a pointer argument, return the value it points to.
	static Optional<SVal> getPointedToSVal(CheckerContext &C, const Expr *Arg);

	/// Functions defining the attack surface.
	typedef ProgramStateRef (TestChecker::*FnCheck)(const CallExpr *, CheckerContext &C) const;
	ProgramStateRef postScanf(const CallExpr *CE, CheckerContext &C) const;
	ProgramStateRef postRetTaint(const CallExpr *CE, CheckerContext &C) const;

	/// Taint the scanned input if the file is tainted.
	ProgramStateRef preFscanf(const CallExpr *CE, CheckerContext &C) const;

	bool isTaited(const CallExpr *CE, StringRef Name, CheckerContext &C) const;

	bool isInsecFunc(const CallExpr *CE, CheckerContext &C){
		StringRef Name = C.getCalleeName(C.getCalleeDecl(CE));
		auto iter = find(Opts.UserInpFuncName.begin(), Opts.UserInpFuncName.end(), Name);
		if (iter != Opts.UserInpFuncName.end())
			return true;
		return false;
	};
	bool isInsecFunc(StringRef Name){
		auto iter = find(Opts.UserInpFuncName.begin(), Opts.UserInpFuncName.end(), Name);
		if (iter != Opts.UserInpFuncName.end())
			return true;
		return false;
	};

	bool TaintCustomFunc(const CallExpr *CE, CheckerContext &C){
	  	ProgramStateRef State = C.getState();
		for (unsigned int i = 1; i < CE->getNumArgs(); ++i) {
			const Expr *Arg = CE->getArg(i);
			Optional<SVal> V = getPointedToSVal(C, Arg);
			if (V)
				State = State->addTaint(*V);
		}
		return true;
	}

	typedef SmallVector<unsigned, 2> ArgVector;

	/// A struct used to specify taint propagation rules for a function.
	///
	/// If any of the possible taint source arguments is tainted, all of the
	/// destination arguments should also be tainted. Use InvalidArgIndex in the
	/// src list to specify that all of the arguments can introduce taint. Use
	/// InvalidArgIndex in the dst arguments to signify that all the non-const
	/// pointer and reference arguments might be tainted on return. If
	/// ReturnValueIndex is added to the dst list, the return value will be
	/// tainted.
	struct TaintPropagationRule {
		/// List of arguments which can be taint sources and should be checked.
		ArgVector SrcArgs;
		/// List of arguments which should be tainted on function return.
		ArgVector DstArgs;
		// TODO: Check if using other data structures would be more optimal.

		TaintPropagationRule() {}

		TaintPropagationRule(unsigned SArg, unsigned DArg, bool TaintRet = false) {
			SrcArgs.push_back(SArg);
			DstArgs.push_back(DArg);
			if (TaintRet)
				DstArgs.push_back(ReturnValueIndex);
		}

		TaintPropagationRule(unsigned SArg1, unsigned SArg2, unsigned DArg, bool TaintRet = false) {
			SrcArgs.push_back(SArg1);
			SrcArgs.push_back(SArg2);
			DstArgs.push_back(DArg);
			if (TaintRet)
				DstArgs.push_back(ReturnValueIndex);
		}

		/// Get the propagation rule for a given function.
		static TaintPropagationRule getTaintPropagationRule(const FunctionDecl *FDecl, StringRef Name, CheckerContext &C);

		inline void addSrcArg(unsigned A) { SrcArgs.push_back(A); }
		inline void addDstArg(unsigned A) { DstArgs.push_back(A); }

		inline bool isNull() const { return SrcArgs.empty(); }

		inline bool isDestinationArgument(unsigned ArgNum) const {
			return (find(DstArgs.begin(), DstArgs.end(), ArgNum) != DstArgs.end());
		}

		static inline bool isTaintedOrPointsToTainted(const Expr *E, ProgramStateRef State, CheckerContext &C) {
			if (State->isTainted(E, C.getLocationContext()))
				return true;
				
			if (!E->getType().getTypePtr()->isPointerType())
				return false;

			Optional<SVal> V = getPointedToSVal(C, E);
				return (V && State->isTainted(*V));
		}

		/// Pre-process a function which propagates taint according to the
		/// taint rule.
		ProgramStateRef process(const CallExpr *CE, CheckerContext &C) const;
	};
};

const unsigned TestChecker::ReturnValueIndex;
const unsigned TestChecker::InvalidArgIndex;
} // end of anonymous namespace

void TestChecker::checkASTCodeBody(const Decl *D, AnalysisManager &AM, BugReporter &BR) const {
	//llvm::outs() << "checkASTBody\n\n";
}

/// A set which is used to pass information from call pre-visit instruction
/// to the call post-visit. The values are unsigned integers, which are either
/// ReturnValueIndex, or indexes of the pointer/reference argument, which
/// points to data, which should be tainted on return.
REGISTER_SET_WITH_PROGRAMSTATE(TaintArgsOnPostVisit, unsigned)

TestChecker::TaintPropagationRule TestChecker::TaintPropagationRule::getTaintPropagationRule(const FunctionDecl *FDecl, StringRef Name, CheckerContext &C) {
	// Check for exact name match for functions without builtin substitutes.
	TaintPropagationRule Rule = llvm::StringSwitch<TaintPropagationRule>(Name)
			.Case("atoi", TaintPropagationRule(0, ReturnValueIndex))
			.Case("atol", TaintPropagationRule(0, ReturnValueIndex))
			.Case("atoll", TaintPropagationRule(0, ReturnValueIndex))
			.Case("getc", TaintPropagationRule(0, ReturnValueIndex))
			.Case("fgetc", TaintPropagationRule(0, ReturnValueIndex))
			.Case("getc_unlocked", TaintPropagationRule(0, ReturnValueIndex))
			.Case("getw", TaintPropagationRule(0, ReturnValueIndex))
			.Case("toupper", TaintPropagationRule(0, ReturnValueIndex))
			.Case("tolower", TaintPropagationRule(0, ReturnValueIndex))
			.Case("strchr", TaintPropagationRule(0, ReturnValueIndex))
			.Case("strrchr", TaintPropagationRule(0, ReturnValueIndex))
			.Case("read", TaintPropagationRule(0, 2, 1, true))
			.Case("pread", TaintPropagationRule(InvalidArgIndex, 1, true))
			.Case("gets", TaintPropagationRule(InvalidArgIndex, 0, true))
			.Case("fgets", TaintPropagationRule(2, 0, true))
			.Case("getline", TaintPropagationRule(2, 0))
			.Case("getdelim", TaintPropagationRule(3, 0))
			.Case("fgetln", TaintPropagationRule(0, ReturnValueIndex))
			.Default(TaintPropagationRule());

	if (!Rule.isNull())
		return Rule;

	// Check if it's one of the memory setting/copying functions.
	// This check is specialized but faster then calling isCLibraryFunction.
	unsigned BId = 0;
	if ((BId = FDecl->getMemoryFunctionKind()))
		switch (BId) {
		case Builtin::BImemcpy:
		case Builtin::BImemmove:
		case Builtin::BIstrncpy:
		case Builtin::BIstrncat:
		return TaintPropagationRule(1, 2, 0, true);
		case Builtin::BIstrlcpy:
		case Builtin::BIstrlcat:
		return TaintPropagationRule(1, 2, 0, false);
		case Builtin::BIstrndup:
		return TaintPropagationRule(0, 1, ReturnValueIndex);

		default:
		break;
		};

	// Process all other functions which could be defined as builtins.
	if (Rule.isNull()) {
		if (C.isCLibraryFunction(FDecl, "snprintf") ||
			C.isCLibraryFunction(FDecl, "sprintf"))
		return TaintPropagationRule(InvalidArgIndex, 0, true);
		else if (C.isCLibraryFunction(FDecl, "strcpy") ||
				C.isCLibraryFunction(FDecl, "stpcpy") ||
				C.isCLibraryFunction(FDecl, "strcat"))
		return TaintPropagationRule(1, 0, true);
		else if (C.isCLibraryFunction(FDecl, "bcopy"))
		return TaintPropagationRule(0, 2, 1, false);
		else if (C.isCLibraryFunction(FDecl, "strdup") ||
				C.isCLibraryFunction(FDecl, "strdupa"))
		return TaintPropagationRule(0, ReturnValueIndex);
		else if (C.isCLibraryFunction(FDecl, "wcsdup"))
		return TaintPropagationRule(0, ReturnValueIndex);
	}
		
	return TaintPropagationRule();
} 
//end of getTaintPropagationRule

void TestChecker::checkPreStmt(const CallExpr *CE, CheckerContext &C) const {
	TaintVisitor tv = TaintVisitor(C, C.getState());
	
	// Check for errors first.
	if (checkPre(CE, C))
		return;

	// Add taint second.
	addSourcesPre(CE, C);
}

void TestChecker::checkPostStmt(const CallExpr *CE, CheckerContext &C) const {
  if (propagateFromPre(CE, C))
    return;
  addSourcesPost(CE, C);
}

void TestChecker::addSourcesPre(const CallExpr *CE, CheckerContext &C) const {
	ProgramStateRef State = nullptr;
	const FunctionDecl *FDecl = C.getCalleeDecl(CE);
	if (!FDecl || FDecl->getKind() != Decl::Function)
		return;

	StringRef Name = C.getCalleeName(FDecl);
	if (Name.empty())
		return;

	// First, try generating a propagation rule for this function.
	TaintPropagationRule Rule = TaintPropagationRule::getTaintPropagationRule(FDecl, Name, C);
	if (!Rule.isNull()) {
		State = Rule.process(CE, C);
		if (!State)
			return;
		C.addTransition(State);
		return;
	}

	// Otherwise, check if we have custom pre-processing implemented.
	FnCheck evalFunction = llvm::StringSwitch<FnCheck>(Name)
								.Case("fscanf", &TestChecker::preFscanf)
								.Default(nullptr);
	// Check and evaluate the call.
	if (evalFunction)
		State = (this->*evalFunction)(CE, C);
	if (!State)
		return;
	C.addTransition(State);
}

bool TestChecker::propagateFromPre(const CallExpr *CE, CheckerContext &C) const {
  	ProgramStateRef State = C.getState();

	// Depending on what was tainted at pre-visit, we determined a set of
	// arguments which should be tainted after the function returns. These are
	// stored in the state as TaintArgsOnPostVisit set.
	TaintArgsOnPostVisitTy TaintArgs = State->get<TaintArgsOnPostVisit>();
	if (TaintArgs.isEmpty())
		return false;

	for (llvm::ImmutableSet<unsigned>::iterator I = TaintArgs.begin(), E = TaintArgs.end(); I != E; ++I) {
		unsigned ArgNum = *I;

		// Special handling for the tainted return value.
		if (ArgNum == ReturnValueIndex) {
			State = State->addTaint(CE, C.getLocationContext());
			continue;
		}

		// The arguments are pointer arguments. The data they are pointing at is
		// tainted after the call.
		if (CE->getNumArgs() < (ArgNum + 1))
		return false;
		const Expr *Arg = CE->getArg(ArgNum);
		Optional<SVal> V = getPointedToSVal(C, Arg);
		if (V)
			State = State->addTaint(*V);
  	}

	// Clear up the taint info from the state.
	State = State->remove<TaintArgsOnPostVisit>();

	if (State != C.getState()) {
		C.addTransition(State);
		return true;
	}
	return false;
}

// Define the attack surface.
void TestChecker::addSourcesPost(const CallExpr *CE, CheckerContext &C) const {
	// Set the evaluation function by switching on the callee name.
	const FunctionDecl *FDecl = C.getCalleeDecl(CE);
	if (!FDecl || FDecl->getKind() != Decl::Function)
		return;

	StringRef Name = C.getCalleeName(FDecl);
	if (Name.empty())
		return;
	FnCheck evalFunction = llvm::StringSwitch<FnCheck>(Name)
			.Case("scanf", &TestChecker::postScanf)
			.Case("getchar", &TestChecker::postRetTaint)
			.Case("getchar_unlocked", &TestChecker::postRetTaint)
			.Case("getenv", &TestChecker::postRetTaint)
			.Case("fopen", &TestChecker::postRetTaint)
			.Case("fdopen", &TestChecker::postRetTaint)
			.Case("freopen", &TestChecker::postRetTaint)
			.Case("getch", &TestChecker::postRetTaint) 
			.Case("wgetch", &TestChecker::postRetTaint)
			.Default(nullptr);	
	
	ProgramStateRef State = nullptr;
	if (evalFunction)
		State = (this->*evalFunction)(CE, C);

	if (!State)
		return;

	C.addTransition(State);
}

bool TestChecker::checkPre(const CallExpr *CE, CheckerContext &C) const {
  	const FunctionDecl *FDecl = C.getCalleeDecl(CE);
	if (!FDecl || FDecl->getKind() != Decl::Function)
		return false;

	StringRef Name = C.getCalleeName(FDecl);
	if (Name.empty())
		return false;

	if (isTaited(CE, Name, C)){
		// so what next?
		C.getState()->dumpTaint();
		ASTContext &AC =  C.getASTContext();
		ASTWalker AW = ASTWalker(&AC);
		//AW.Traverse();
		return true; 
  }

  return false;
}

Optional<SVal> TestChecker::getPointedToSVal(CheckerContext &C, const Expr *Arg) {
  ProgramStateRef State = C.getState();
  SVal AddrVal = C.getSVal(Arg->IgnoreParens());
  if (AddrVal.isUnknownOrUndef())
    return None;

  Optional<Loc> AddrLoc = AddrVal.getAs<Loc>();
  if (!AddrLoc)
    return None;

  QualType ArgTy = Arg->getType().getCanonicalType();
  if (!ArgTy->isPointerType())
    return None;

  QualType ValTy = ArgTy->getPointeeType();

  if (ValTy->isVoidType())
    ValTy = C.getASTContext().CharTy;

  return State->getSVal(*AddrLoc, ValTy);
}

ProgramStateRef TestChecker::TaintPropagationRule::process(const CallExpr *CE, CheckerContext &C) const {
	ProgramStateRef State = C.getState();
	// Check for taint in arguments.
	bool IsTainted = false;
	for (ArgVector::const_iterator I = SrcArgs.begin(), E = SrcArgs.end(); I != E;
		++I) {
		unsigned ArgNum = *I;

		if (ArgNum == InvalidArgIndex) {
			// Check if any of the arguments is tainted, but skip the
			// destination arguments.
			for (unsigned int i = 0; i < CE->getNumArgs(); ++i) {
				if (isDestinationArgument(i))
					continue;
				if ((IsTainted = isTaintedOrPointsToTainted(CE->getArg(i), State, C)))
					break;
			}
			break;
		}

		if (CE->getNumArgs() < (ArgNum + 1))
		return State;
		if ((IsTainted = isTaintedOrPointsToTainted(CE->getArg(ArgNum), State, C)))
		break;
	}
	if (!IsTainted)
		return State;

	// Mark the arguments which should be tainted after the function returns.
	for (ArgVector::const_iterator I = DstArgs.begin(), E = DstArgs.end(); I != E; ++I) {
		unsigned ArgNum = *I;

		// Should we mark all arguments as tainted?
		if (ArgNum == InvalidArgIndex) {
			// For all pointer and references that were passed in:
			//   If they are not pointing to const data, mark data as tainted.
			for (unsigned int i = 0; i < CE->getNumArgs(); ++i) {
				const Expr *Arg = CE->getArg(i);
				// Process pointer argument.
				const Type *ArgTy = Arg->getType().getTypePtr();
				QualType PType = ArgTy->getPointeeType();
				if ((!PType.isNull() && !PType.isConstQualified()) ||
					(ArgTy->isReferenceType() && !Arg->getType().isConstQualified()))
				State = State->add<TaintArgsOnPostVisit>(i);
			}
			continue;
		}

		// Should mark the return value?
		if (ArgNum == ReturnValueIndex) {
			State = State->add<TaintArgsOnPostVisit>(ReturnValueIndex);
			continue;
		}

		// Mark the given argument.
		assert(ArgNum < CE->getNumArgs());
		State = State->add<TaintArgsOnPostVisit>(ArgNum);
	}

	return State;
}

ProgramStateRef TestChecker::preFscanf(const CallExpr *CE, CheckerContext &C) const {
	assert(CE->getNumArgs() >= 2);
	ProgramStateRef State = C.getState();

	// Check is the file descriptor is tainted.
	if (State->isTainted(CE->getArg(0), C.getLocationContext())) {
		// All arguments except for the first two should get taint.
		for (unsigned int i = 2; i < CE->getNumArgs(); ++i)
		State = State->add<TaintArgsOnPostVisit>(i);
		return State;
	}

	return nullptr;
}

ProgramStateRef TestChecker::postScanf(const CallExpr *CE, CheckerContext &C) const {
	ProgramStateRef State = C.getState();
	if (CE->getNumArgs() < 2)
		return State;

	// All arguments except for the very first one should get taint.
	for (unsigned int i = 1; i < CE->getNumArgs(); ++i) {
		// The arguments are pointer arguments. The data they are pointing at is
		// tainted after the call.
		const Expr *Arg = CE->getArg(i);
		Optional<SVal> V = getPointedToSVal(C, Arg);
		if (V)
			State = State->addTaint(*V);
	}
	return State;
}

ProgramStateRef TestChecker::postRetTaint(const CallExpr *CE,CheckerContext &C) const {
	return C.getState()->addTaint(CE, C.getLocationContext());
}

bool TestChecker::isTaited(const CallExpr *CE, StringRef Name, CheckerContext &C) const {
	ProgramStateRef State = C.getState();
	const Expr *E;
	bool Tainted = false;

	for (unsigned i = 0; i < CE->getNumArgs(); i++){
		E = CE->getArg(i);
		Optional<SVal> PointedToSVal = getPointedToSVal(C, E);
		SVal TaintedSVal;

  		if (PointedToSVal && State->isTainted(*PointedToSVal)){
			TaintedSVal = *PointedToSVal;
			Tainted = true;
			llvm::outs() << "in func " << Name << " \n";
			TaintedSVal.dump();
			llvm::outs() << "\n";
		  }
		else if (State->isTainted(E, C.getLocationContext())){
			TaintedSVal = C.getSVal(E);
			Tainted = true;
			llvm::outs() << "in func " << Name << " \n";
			TaintedSVal.dump();
			llvm::outs() << "\n";
		}
	}

	return Tainted;
}

void initializationFunction(CheckerManager &mgr){
  	TestChecker *checker =  mgr.registerChecker<TestChecker>();
	AnalyzerOptions &AnOpts = mgr.getAnalyzerOptions();
	TestChecker::CheckerOpts &ChOpts = checker->Opts;
	ChOpts.RawInp = AnOpts.getCheckerStringOption("UsrInpFrom", "", checker); //space seperated
	ChOpts.splitRaw();
}

extern "C" void clang_registerCheckers (CheckerRegistry &registry) {
	registry.addChecker(&initializationFunction, "test.Me", "Bla Bla", "doc_link");
}

extern "C" const  char  clang_analyzerAPIVersionString [] = "8.0.1";