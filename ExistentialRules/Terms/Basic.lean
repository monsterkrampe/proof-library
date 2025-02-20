import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.FiniteTree
import BasicLeanDatastructures.Set.Basic
import BasicLeanDatastructures.Set.Finite

structure Signature where
  P : Type u
  V : Type v
  C : Type w
  arity : P -> Nat

structure SkolemFS (sig : Signature) [DecidableEq sig.V] where
  ruleId : Nat
  disjunctIndex : Nat
  var : sig.V
  arity : Nat -- NOTE: this is not enforced anywhere; we set this when skolemizing to remember the frontier size
  deriving DecidableEq

abbrev PreGroundTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := FiniteTree (SkolemFS sig) sig.C

namespace PreGroundTerm

  mutual

    def arity_ok {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] : FiniteTree (SkolemFS sig) sig.C -> Bool
    | .leaf _ => true
    | .inner func ts =>
      ts.toList.length == func.arity && arity_ok_list ts

    def arity_ok_list {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] : FiniteTreeList (SkolemFS sig) sig.C -> Bool
    | .nil => true
    | .cons hd tl => arity_ok hd && arity_ok_list tl

  end

  theorem arity_ok_list_iff_arity_ok_each_mem {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] (ts : FiniteTreeList (SkolemFS sig) sig.C) : (∀ t, t ∈ ts.toList -> PreGroundTerm.arity_ok t) ↔ PreGroundTerm.arity_ok_list ts := by
    cases ts with
    | nil => simp [arity_ok_list, FiniteTreeList.toList]
    | cons hd tl =>
      unfold arity_ok_list
      simp [FiniteTreeList.toList]
      intro _
      apply arity_ok_list_iff_arity_ok_each_mem

end PreGroundTerm

abbrev GroundTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := { t : PreGroundTerm sig // PreGroundTerm.arity_ok t }

inductive SkolemTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : SkolemTerm sig
| const (c : sig.C) : SkolemTerm sig
| func (fs : SkolemFS sig) (frontier : List sig.V) (arity_ok : frontier.length = fs.arity) : SkolemTerm sig
deriving DecidableEq

inductive VarOrConst (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : VarOrConst sig
| const (c : sig.C) : VarOrConst sig
deriving DecidableEq

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundTerm

  def const (c : sig.C) : GroundTerm sig := ⟨FiniteTree.leaf c, by simp [PreGroundTerm.arity_ok]⟩
  def func (func : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = func.arity) : GroundTerm sig := ⟨FiniteTree.inner func (FiniteTreeList.fromList ts.unattach), by
    unfold PreGroundTerm.arity_ok
    rw [Bool.and_eq_true, beq_iff_eq]
    rw [FiniteTreeList.fromListToListIsId]
    constructor
    . rw [List.length_unattach]; exact arity_ok
    . rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]
      rw [FiniteTreeList.fromListToListIsId]
      intro t t_mem
      unfold List.unattach at t_mem
      rw [List.mem_map] at t_mem
      rcases t_mem with ⟨t, t_mem, t_eq⟩
      rw [← t_eq]
      exact t.property
  ⟩

  -- TODO: we are barely using cases and rec for GroundTerm; use it more or remove it if it turns out to not be useful
  @[elab_as_elim, cases_eliminator]
  def cases
      {motive : GroundTerm sig -> Sort u}
      (t : GroundTerm sig)
      (const : (c : sig.C) -> motive (GroundTerm.const c))
      (func : (func : SkolemFS sig) -> (ts : List (GroundTerm sig)) -> (arity_ok : ts.length = func.arity) -> motive (GroundTerm.func func ts arity_ok)) :
      motive t :=
    match eq : t.val with
    | .leaf c =>
      have eq : t = GroundTerm.const c := Subtype.eq eq
      eq ▸ const c
    | .inner f ts => by
      let ts : List (GroundTerm sig) := ts.toList.attach.map (fun ⟨t', mem⟩ => ⟨t', by
        have prop := t.property
        unfold PreGroundTerm.arity_ok at prop
        simp only [eq, Bool.and_eq_true, beq_iff_eq] at prop
        have prop := prop.right
        rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem] at prop
        apply prop
        exact mem
      ⟩)
      have arity_ok : ts.length = f.arity := by
        have prop := t.property
        unfold PreGroundTerm.arity_ok at prop
        simp only [eq, Bool.and_eq_true, beq_iff_eq] at prop
        unfold ts
        rw [List.length_map, List.length_attach]
        exact prop.left
      have eq : t = GroundTerm.func f ts arity_ok := by
        apply Subtype.eq
        unfold GroundTerm.func
        simp [eq, ts]
        unfold List.unattach
        rw [List.map_map, List.map_attach]
        simp [FiniteTreeList.toListFromListIsId]
      exact eq ▸ (func f ts arity_ok)

  @[elab_as_elim, induction_eliminator]
  def rec
      {motive : GroundTerm sig -> Sort u}
      (const : (c : sig.C) -> motive (GroundTerm.const c))
      (func : (func : SkolemFS sig) -> (ts : List (GroundTerm sig)) -> (arity_ok : ts.length = func.arity) -> (∀ t, t ∈ ts -> motive t) -> motive (GroundTerm.func func ts arity_ok))
      (t : GroundTerm sig) :
      motive t :=
    match eq_val : t.val with
    | .leaf c =>
      have eq : t = GroundTerm.const c := Subtype.eq eq_val
      eq ▸ const c
    | .inner f ts => by
      let ts : List (GroundTerm sig) := ts.toList.attach.map (fun ⟨t', mem⟩ => ⟨t', by
        have prop := t.property
        unfold PreGroundTerm.arity_ok at prop
        simp only [eq_val, Bool.and_eq_true, beq_iff_eq] at prop
        have prop := prop.right
        rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem] at prop
        apply prop
        exact mem
      ⟩)
      have arity_ok : ts.length = f.arity := by
        have prop := t.property
        unfold PreGroundTerm.arity_ok at prop
        simp only [eq_val, Bool.and_eq_true, beq_iff_eq] at prop
        unfold ts
        rw [List.length_map, List.length_attach]
        exact prop.left
      have eq : t = GroundTerm.func f ts arity_ok := by
        apply Subtype.eq
        unfold GroundTerm.func
        simp [eq_val, ts]
        unfold List.unattach
        rw [List.map_map, List.map_attach]
        simp [FiniteTreeList.toListFromListIsId]
      exact eq ▸ (func f ts arity_ok (by
        intro t' mem
        have : t'.val.depth < t.val.depth := by
          conv => right; unfold FiniteTree.depth
          simp only [eq_val]
          rw [Nat.add_comm]
          apply Nat.lt_add_one_of_le
          apply FiniteTree.depth_le_depthList_of_mem
          unfold ts at mem
          rw [List.mem_map] at mem
          rcases mem with ⟨s, s_mem, t_eq⟩
          simp at t_eq
          rw [← t_eq]
          unfold List.attach at s_mem
          unfold List.attachWith at s_mem
          rw [List.mem_pmap] at s_mem
          rcases s_mem with ⟨_, s_mem, s_eq⟩
          rw [← s_eq]
          exact s_mem
        apply GroundTerm.rec const func
      ))
  termination_by t.val.depth

  def toConst (t : GroundTerm sig) (isConst : ∃ c, t = GroundTerm.const c) : sig.C :=
    match eq : t.val with
    | .leaf c => c
    | .inner _ _ => by
      apply False.elim
      rcases isConst with ⟨c, isConst⟩
      rw [isConst] at eq
      simp [GroundTerm.const] at eq

  def depth (t : GroundTerm sig) : Nat := t.val.depth
  def constants (t : GroundTerm sig) : (List sig.C) := t.val.leaves
  def functions (t : GroundTerm sig) : (List (SkolemFS sig)) := t.val.innerLabels

  theorem depth_const (c : sig.C) : (GroundTerm.const c).depth = 1 := by
    simp [GroundTerm.const, depth, FiniteTree.depth]

  theorem depth_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
      (GroundTerm.func f ts arity_ok).depth = 1 + (((ts.map (GroundTerm.depth)).max?).getD 1) := by
    simp only [GroundTerm.func, depth, FiniteTree.depth]

    have : ∀ (ts : List (GroundTerm sig)), (FiniteTree.depthList (FiniteTreeList.fromList ts.unattach)) = (((ts.map (GroundTerm.depth)).max?).getD 1) := by
      intro ts
      induction ts with
      | nil => simp [FiniteTreeList.fromList, FiniteTree.depthList]
      | cons hd tl ih =>
        rw [List.map_cons, List.max?_cons, List.unattach_cons]
        unfold FiniteTree.depthList
        unfold FiniteTreeList.fromList
        simp only [Option.getD_some]
        cases eq : (tl.map depth).max? with
        | some m => simp only [Option.elim]; rw [ih, eq, Option.getD_some]; rfl
        | none =>
          simp only [Option.elim]
          rw [List.max?_eq_none_iff, List.map_eq_nil_iff] at eq
          rw [eq]
          simp only [FiniteTreeList.fromList, FiniteTree.depthList, List.unattach_nil]
          rw [Nat.max_eq_left]
          . rfl
          . unfold FiniteTree.depth; cases hd.val <;> simp

    rw [this]

  theorem constants_const (c : sig.C) : (GroundTerm.const c).constants = [c] := by
    simp [GroundTerm.const, constants, FiniteTree.leaves]

  theorem constants_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
      (GroundTerm.func f ts arity_ok).constants = ts.flatMap GroundTerm.constants := by
    simp only [GroundTerm.func, constants, FiniteTree.leaves]

    have : ∀ (ts : List (GroundTerm sig)), (FiniteTree.leavesList (FiniteTreeList.fromList ts.unattach)) = (ts.flatMap GroundTerm.constants) := by
      intro ts
      induction ts with
      | nil => simp [FiniteTreeList.fromList, FiniteTree.leavesList]
      | cons hd tl ih =>
        rw [List.flatMap_cons, List.unattach_cons]
        unfold FiniteTree.leavesList
        unfold FiniteTreeList.fromList
        simp only
        rw [ih]
        rfl

    rw [this]

  theorem functions_const (c : sig.C) : (GroundTerm.const c).functions = [] := by
    simp [GroundTerm.const, functions, FiniteTree.innerLabels]

  theorem functions_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
      (GroundTerm.func f ts arity_ok).functions = f :: (ts.flatMap GroundTerm.functions) := by
    simp only [GroundTerm.func, functions, FiniteTree.innerLabels]

    have : ∀ (ts : List (GroundTerm sig)), (FiniteTree.innerLabelsList (FiniteTreeList.fromList ts.unattach)) = (ts.flatMap GroundTerm.functions) := by
      intro ts
      induction ts with
      | nil => simp [FiniteTreeList.fromList, FiniteTree.innerLabelsList]
      | cons hd tl ih =>
        rw [List.flatMap_cons, List.unattach_cons]
        unfold FiniteTree.innerLabelsList
        unfold FiniteTreeList.fromList
        simp only
        rw [ih]
        rfl

    rw [this]

end GroundTerm

namespace SkolemTerm

  def variables : SkolemTerm sig -> List sig.V
  | .var v => List.cons v List.nil
  | .const _ => List.nil
  | .func _ vs _ => vs

end SkolemTerm

namespace VarOrConst

  def isVar : VarOrConst sig -> Bool
  | .var _ => true
  | .const _ => false

  def filterVars : List (VarOrConst sig) -> List sig.V
  | .nil => List.nil
  | .cons voc vocs => match voc with
    | .var v => List.cons v (filterVars vocs)
    | .const _ => filterVars vocs

  theorem filterVars_occur_in_original_list (l : List (VarOrConst sig)) (v : sig.V) : v ∈ filterVars l -> VarOrConst.var v ∈ l := by
    induction l with
    | nil => intros; contradiction
    | cons head tail ih =>
      intro h
      unfold filterVars at h
      split at h
      . simp at h
        simp
        cases h with
        | inl h => apply Or.inl; exact h
        | inr h => apply Or.inr; apply ih; exact h
      . simp
        apply ih
        exact h

  theorem mem_filterVars_of_var (l : List (VarOrConst sig)) (v : sig.V) : VarOrConst.var v ∈ l -> v ∈ filterVars l := by
    induction l with
    | nil => intros; contradiction
    | cons head tail ih =>
      intro h
      simp at h
      unfold filterVars
      cases h with
      | inl h => rw [← h]; simp
      | inr h => split; rw [List.mem_cons]; apply Or.inr; apply ih; exact h; apply ih; exact h

  def filterConsts : List (VarOrConst sig) -> List sig.C
  | .nil => List.nil
  | .cons voc vocs => match voc with
    | .var _ => filterConsts vocs
    | .const c => List.cons c (filterConsts vocs)

  theorem filterConsts_occur_in_original_list (l : List (VarOrConst sig)) (c : sig.C) : c ∈ filterConsts l -> VarOrConst.const c ∈ l := by
    induction l with
    | nil => intros; contradiction
    | cons head tail ih =>
      intro h
      unfold filterConsts at h
      split at h
      . simp
        apply ih
        exact h
      . simp at h
        simp
        cases h with
        | inl h => apply Or.inl; exact h
        | inr h => apply Or.inr; apply ih; exact h

  theorem mem_filterConsts_of_const (l : List (VarOrConst sig)) (c : sig.C) : VarOrConst.const c ∈ l -> c ∈ filterConsts l := by
    induction l with
    | nil => intros; contradiction
    | cons head tail ih =>
      intro h
      simp at h
      unfold filterConsts
      cases h with
      | inl h => rw [← h]; simp
      | inr h => split; apply ih; exact h; rw [List.mem_cons]; apply Or.inr; apply ih; exact h

  def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (voc : VarOrConst sig) : SkolemTerm sig :=
    match voc with
      | .var v => ite (v ∈ frontier)
        (SkolemTerm.var v)
        (SkolemTerm.func { ruleId, disjunctIndex, var := v, arity := frontier.length } frontier rfl)
      | .const c => SkolemTerm.const c

  theorem skolemize_injective (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (s t : VarOrConst sig) : s.skolemize ruleId disjunctIndex frontier = t.skolemize ruleId disjunctIndex frontier -> s = t := by
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
        simp only [skolemize]
        split <;> intros <;> contradiction
    | const cs => cases t with
      | var vt =>
        simp only [skolemize]
        split <;> intros <;> contradiction
      | const _ => simp [skolemize]

end VarOrConst

