import ProofLibrary.FiniteTree

structure Predicate where
  id : Nat

structure Variable where
  id : Nat

instance : BEq Variable where
  beq a b := a.id = b.id

structure Constant where
  id : Nat

/- I think we only need skolem function symbols
structure FunctionSymbol where
  id : Nat
-/

structure SkolemFS where
  ruleId : Nat
  var : Variable

inductive GroundTerm where
  | const (c : Constant) : GroundTerm
  | func (ft : FiniteTree SkolemFS Constant) : GroundTerm

def GroundTerm.depth : GroundTerm -> Nat
  | GroundTerm.const _ => 0
  | GroundTerm.func ft => FiniteTree.depth ft

inductive VarOrConst where
  | var (v : Variable) : VarOrConst
  | const (c : Constant) : VarOrConst

def VarOrConst.isVar : VarOrConst -> Bool
  | VarOrConst.var _ => true
  | VarOrConst.const _ => false

def VarOrConst.filterVars : List VarOrConst -> List Variable
  | List.nil => List.nil
  | List.cons voc vocs => match voc with
    | VarOrConst.var v => List.cons v (VarOrConst.filterVars vocs)
    | VarOrConst.const _ => (VarOrConst.filterVars vocs)

inductive Term where
  | var (v : Variable) : Term
  | const (c : Constant) : Term
  | func (ft : FiniteTree SkolemFS VarOrConst) : Term

def GroundTerm.toTerm : GroundTerm -> Term
  | GroundTerm.const c => Term.const c
  | GroundTerm.func ft => Term.func (FiniteTree.mapLeaves (fun c => FiniteTree.leaf (VarOrConst.const c)) ft)

instance : Coe GroundTerm Term where
  coe := GroundTerm.toTerm

def Term.variables : Term -> List Variable
  | Term.var v => List.cons v List.nil
  | Term.const _ => List.nil
  | Term.func ft => VarOrConst.filterVars ft.leaves

def Term.skolemize (ruleId : Nat) (frontier : List Variable) (t : Term) : Term :=
  match t with
    | Term.var v => ite (List.elem v frontier)
      (Term.var v)
      (Term.func (FiniteTree.inner { ruleId := ruleId, var := v} (FiniteTreeList.fromList (List.map (fun fv => FiniteTree.leaf (VarOrConst.var fv)) frontier))))
    | t => t
