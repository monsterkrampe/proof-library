import ProofLibrary.List
import ProofLibrary.FiniteTree

structure Predicate where
  id : Nat
  deriving DecidableEq

structure Variable where
  id : Nat
  deriving DecidableEq

structure Constant where
  id : Nat
  deriving DecidableEq

/- I think we only need skolem function symbols
structure FunctionSymbol where
  id : Nat
-/

structure SkolemFS where
  ruleId : Nat
  var : Variable
  deriving DecidableEq

-- inductive GroundTerm where
--   | const (c : Constant) : GroundTerm
--   | func (ft : FiniteTree SkolemFS Constant) : GroundTerm
--   deriving DecidableEq

def GroundTerm := FiniteTree SkolemFS Constant 
deriving DecidableEq

@[match_pattern]
def GroundTerm.const (c : Constant) := @FiniteTree.leaf SkolemFS Constant c

inductive SkolemTerm where
  | var (v : Variable) : SkolemTerm
  | const (c : Constant) : SkolemTerm
  | func (fs : SkolemFS) (frontier : List Variable) : SkolemTerm
  deriving DecidableEq

def SkolemTerm.variables : SkolemTerm -> List Variable
  | .var v => List.cons v List.nil
  | .const _ => List.nil
  | .func _ vs => vs

-- def GroundTerm.depth : GroundTerm -> Nat
--   | GroundTerm.const _ => 0
--   | GroundTerm.func ft => FiniteTree.depth ft

inductive VarOrConst where
  | var (v : Variable) : VarOrConst
  | const (c : Constant) : VarOrConst
  deriving DecidableEq

def VarOrConst.isVar : VarOrConst -> Bool
  | VarOrConst.var _ => true
  | VarOrConst.const _ => false

def VarOrConst.filterVars : List VarOrConst -> List Variable
  | List.nil => List.nil
  | List.cons voc vocs => match voc with
    | VarOrConst.var v => List.cons v (VarOrConst.filterVars vocs)
    | VarOrConst.const _ => (VarOrConst.filterVars vocs)

theorem VarOrConst.filterVars_occur_in_original_list (l : List VarOrConst) (v : Variable) : v ∈ (filterVars l).toSet -> VarOrConst.var v ∈ l.toSet := by
  induction l with 
  | nil => intros; contradiction
  | cons head tail ih => 
    intro h 
    unfold filterVars at h
    split at h
    . simp [Set.element, List.toSet] at h
      simp [Set.element, List.toSet] 
      cases h with 
      | inl hl => apply Or.inl; simp [Set.element] at hl; rw [hl]; simp [Set.element]
      | inr hr => apply Or.inr; apply ih; apply hr
    . simp [Set.element] 
      apply Or.inr 
      apply ih
      apply h

-- inductive Term where
--   | var (v : Variable) : Term
--   | const (c : Constant) : Term
--   | func (ft : FiniteTree SkolemFS VarOrConst) : Term
--   deriving DecidableEq
--
-- def GroundTerm.toTerm : GroundTerm -> Term
--   | .const c => Term.const c
--   | .func ft => Term.func (FiniteTree.mapLeaves (fun c => FiniteTree.leaf (VarOrConst.const c)) ft)
--
-- instance : Coe GroundTerm Term where
--   coe := GroundTerm.toTerm
--
-- def SkolemTerm.toTerm : SkolemTerm -> Term
--   | .var v => Term.var v
--   | .const c => Term.const c
--   | .func fs frontier => Term.func (FiniteTree.inner fs (FiniteTreeList.fromList (frontier.map (fun fv => FiniteTree.leaf (VarOrConst.var fv)))))
--
-- instance : Coe SkolemTerm Term where
--   coe := SkolemTerm.toTerm
--
-- def Term.variables : Term -> List Variable
--   | Term.var v => List.cons v List.nil
--   | Term.const _ => List.nil
--   | Term.func ft => VarOrConst.filterVars ft.leaves

def VarOrConst.skolemize (ruleId : Nat) (frontier : List Variable) (voc : VarOrConst) : SkolemTerm :=
  match voc with
    | VarOrConst.var v => ite (List.elem v frontier)
      (SkolemTerm.var v)
      (SkolemTerm.func { ruleId := ruleId, var := v} frontier)
    | VarOrConst.const c => SkolemTerm.const c

theorem VarOrConst.skolemize_injective (ruleId : Nat) (frontier : List Variable) (s t : VarOrConst) : s.skolemize ruleId frontier = t.skolemize ruleId frontier -> s = t := by 
  cases s with 
  | var vs => cases t with 
    | var vt => 
      simp [skolemize]
      split
      . split 
        . simp 
        . intros; contradiction
      . split 
        . intros; contradiction
        . simp
    | const _ => 
      simp [skolemize]
      split <;> intros <;> assumption
  | const cs => cases t with 
    | var vt => 
      simp [skolemize]
      split <;> intros <;> assumption
    | const _ => simp [skolemize]

-- def VarOrConst.skolemize_into_functional_term (ruleId : Nat) (frontier : List Variable) (v : Variable) (v_not_frontier : ¬ frontier.elem v) : FiniteTree SkolemFS Variable := 
--   match eq : skolemize ruleId frontier (VarOrConst.var v) with 
--   | .var _ => by simp [skolemize, v_not_frontier] at eq
--   | .const _ => by simp [skolemize, v_not_frontier] at eq
--   | .func ft => 
--     let mapper : VarOrConst
--     ft
--
-- theorem VarOrConst.skolemize_leaves_is_frontier (ruleId : Nat) (frontier : List Variable) (v : Variable) (v_not_frontier : ¬ frontier.elem v) : (skolemize_into_functional_term ruleId frontier v v_not_frontier).leaves = frontier := by sorry

-- def Term.skolemize (ruleId : Nat) (frontier : List Variable) (t : Term) : Term :=
--   match t with
--     | Term.var v => ite (List.elem v frontier)
--       (Term.var v)
--       (Term.func (FiniteTree.inner { ruleId := ruleId, var := v} (FiniteTreeList.fromList (List.map (fun fv => FiniteTree.leaf (VarOrConst.var fv)) frontier))))
--     | t => t

