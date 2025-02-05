import ProofLibrary.List
import ProofLibrary.FiniteTree
import ProofLibrary.Set.Basic
import ProofLibrary.Set.Finite

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

abbrev GroundTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := FiniteTree (SkolemFS sig) sig.C

inductive SkolemTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
  | var (v : sig.V) : SkolemTerm sig
  | const (c : sig.C) : SkolemTerm sig
  | func (fs : SkolemFS sig) (frontier : List sig.V) : SkolemTerm sig
  deriving DecidableEq

inductive VarOrConst (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
  | var (v : sig.V) : VarOrConst sig
  | const (c : sig.C) : VarOrConst sig
  deriving DecidableEq

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

@[match_pattern]
def GroundTerm.const (c : sig.C) := @FiniteTree.leaf (SkolemFS sig) sig.C c

def GroundTerm.toConst (t : GroundTerm sig) (isConst : ∃ c, t = GroundTerm.const c) : sig.C :=
  match eq : t with
  | .leaf c => c
  | .inner _ _ => by
    apply False.elim
    rcases isConst with ⟨c, isConst⟩
    simp [GroundTerm.const] at isConst

def GroundTerm.contains_func (func : SkolemFS sig) : GroundTerm sig -> Bool
| .leaf _ => false
| .inner func' ts => func == func' || ts.toList.attach.any (fun ⟨t, mem⟩ =>
  have : t.depth < (FiniteTree.inner func' ts).depth := by
    conv => right; unfold FiniteTree.depth
    rw [Nat.add_comm]
    apply Nat.lt_add_one_of_le
    apply FiniteTree.depth_le_depthList_of_mem
    exact mem
  contains_func func t
)
termination_by t => FiniteTree.depth t

def GroundTerm.cyclic : GroundTerm sig -> Bool
| .leaf _ => false
| .inner func ts => (ts.toList.any (contains_func func)) || ts.toList.attach.any (fun ⟨t, mem⟩ =>
  have : t.depth < (FiniteTree.inner func ts).depth := by
    conv => right; unfold FiniteTree.depth
    rw [Nat.add_comm]
    apply Nat.lt_add_one_of_le
    apply FiniteTree.depth_le_depthList_of_mem
    exact mem
  cyclic t
)
termination_by t => FiniteTree.depth t

def SkolemTerm.variables : SkolemTerm sig -> List sig.V
  | .var v => List.cons v List.nil
  | .const _ => List.nil
  | .func _ vs => vs

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
        (SkolemTerm.func { ruleId, disjunctIndex, var := v, arity := frontier.length } frontier)
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


section ListsOfTerms

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def all_term_lists_of_length (candidate_terms : List (GroundTerm sig)) : Nat -> List (List (GroundTerm sig))
  | .zero => [[]]
  | .succ n =>
    let prev_terms := all_term_lists_of_length candidate_terms n
    candidate_terms.flatMap (fun t =>
      prev_terms.map (fun ts =>
        t :: ts
      )
    )

  theorem mem_all_term_lists_of_length (candidate_terms : List (GroundTerm sig)) (length : Nat) : ∀ ts, ts ∈ (all_term_lists_of_length candidate_terms length) ↔ (ts.length = length ∧ (∀ t, t ∈ ts -> t ∈ candidate_terms)) := by
    induction length with
    | zero => intro ts; unfold all_term_lists_of_length; simp; intro eq t mem; rw [eq] at mem; simp at mem
    | succ length ih =>
      intro ts
      unfold all_term_lists_of_length
      simp only [List.mem_flatMap, List.mem_map]

      constructor
      . intro h
        rcases h with ⟨t, t_mem, prev, prev_mem, ts_eq⟩
        rw [← ts_eq]
        specialize ih prev
        have ih := ih.mp prev_mem
        constructor
        . rw [List.length_cons, ih.left]
        . intro t' t'_mem
          rw [List.mem_cons] at t'_mem
          cases t'_mem with
          | inl t'_mem => rw [t'_mem]; apply t_mem
          | inr t'_mem => apply ih.right; exact t'_mem
      . intro h
        cases ts with
        | nil => simp at h
        | cons hd tl =>
          exists hd
          constructor
          . apply h.right
            simp
          . exists tl
            constructor
            . rw [ih]
              constructor
              . have l := h.left
                rw [List.length_cons, Nat.add_right_cancel_iff] at l
                exact l
              . intro t t_mem
                apply h.right
                simp [t_mem]
            . rfl

  def all_terms_limited_by_depth (constants : List sig.C) (funcs : List (SkolemFS sig)) : Nat -> List (GroundTerm sig)
  | 0 => []
  | 1 => constants.map GroundTerm.const
  | .succ (.succ depth) =>
    let prev := all_terms_limited_by_depth constants funcs (.succ depth)
    funcs.flatMap (fun func =>
      (all_term_lists_of_length prev func.arity).map (fun ts =>
        FiniteTree.inner func (FiniteTreeList.fromList ts)
      )
    )

  theorem mem_all_terms_limited_by_depth (constants : List sig.C) (funcs : List (SkolemFS sig)) (depth : Nat) :
      ∀ t, t ∈ (all_terms_limited_by_depth constants funcs depth) ↔ (t.depth ≤ depth ∧ (∀ c, c ∈ t.leaves -> c ∈ constants) ∧ (∀ func, func ∈ t.innerLabels -> func ∈ funcs)) := by
    induction depth with
    | zero =>
      simp [all_terms_limited_by_depth]
      intro t t_depth
      cases t <;> simp [FiniteTree.depth] at t_depth
    | succ depth ih =>
      intro t
      unfold all_terms_limited_by_depth

      cases t with
      | leaf c => sorry
      | inner t_func ts =>

        cases depth with
        | zero =>
          simp only [Nat.zero_add]
          sorry
        | succ depth =>
          simp only [List.mem_flatMap, List.mem_map]

          let rec aux : ∀ (ts : FiniteTreeList (SkolemFS sig) sig.C), (∀ t, t ∈ ts.toList -> t ∈ (all_terms_limited_by_depth constants funcs depth.succ)) ↔
              ((FiniteTree.depthList ts ≤ depth.succ) ∧ (∀ c, c ∈ FiniteTree.leavesList ts -> c ∈ constants) ∧ (∀ func, func ∈ FiniteTree.innerLabelsList ts -> func ∈ funcs)) := by
            intro ts
            cases ts with
            | nil =>
              simp [FiniteTree.depthList, FiniteTree.leavesList, FiniteTree.innerLabelsList, FiniteTreeList.toList]
            | cons hd tl =>
              unfold FiniteTree.depthList
              unfold FiniteTree.leavesList
              unfold FiniteTree.innerLabelsList

              specialize ih hd
              have ih_inner := aux tl

              constructor
              . intro h

                have ih := ih.mp (by
                  apply h
                  unfold FiniteTreeList.toList
                  simp
                )
                have ih_inner := ih_inner.mp (by
                  intro t t_mem
                  apply h
                  unfold FiniteTreeList.toList
                  simp [t_mem]
                )

                constructor
                . rw [Nat.max_le]
                  constructor
                  . apply ih.left
                  . apply ih_inner.left
                constructor
                . intro c c_mem
                  rw [List.mem_append] at c_mem
                  cases c_mem with
                  | inl c_mem => apply ih.right.left; exact c_mem
                  | inr c_mem => apply ih_inner.right.left; exact c_mem
                . intro func func_mem
                  rw [List.mem_append] at func_mem
                  cases func_mem with
                  | inl func_mem => apply ih.right.right; exact func_mem
                  | inr func_mem => apply ih_inner.right.right; exact func_mem
              . intro h

                have ih := ih.mpr (by
                  sorry
                  /- apply h -/
                  /- unfold FiniteTreeList.toList -/
                  /- simp -/
                )
                have ih_inner := ih_inner.mpr (by
                  sorry
                  /- intro t t_mem -/
                  /- apply h -/
                  /- unfold FiniteTreeList.toList -/
                  /- simp [t_mem] -/
                )
                intro t t_mem
                unfold FiniteTreeList.toList at t_mem
                rw [List.mem_cons] at t_mem
                cases t_mem with
                | inl t_mem => rw [t_mem]; apply ih
                | inr t_mem => apply ih_inner; exact t_mem

          constructor
          . intro h
            rcases h with ⟨func, func_mem, ts, ts_mem, t_eq⟩
            rw [← t_eq]
            rw [mem_all_term_lists_of_length] at ts_mem

            /- let rec aux : ∀ (ts : FiniteTreeList (SkolemFS sig) sig.C), (∀ t, t ∈ ts.toList -> t ∈ (all_terms_limited_by_depth constants funcs depth.succ)) -> -/
            /-     ((FiniteTree.depthList ts ≤ depth.succ) ∧ (∀ c, c ∈ FiniteTree.leavesList ts -> c ∈ constants) ∧ (∀ func, func ∈ FiniteTree.innerLabelsList ts -> func ∈ funcs)) := by -/
            /-   intro ts -/
            /-   cases ts with -/
            /-   | nil => -/
            /-     intro h -/
            /-     constructor -/
            /-     . simp [FiniteTree.depthList] -/
            /-     constructor -/
            /-     . simp [FiniteTree.leavesList] -/
            /-     . simp [FiniteTree.innerLabelsList] -/
            /-   | cons hd tl => -/
            /-     intro h -/
            /-     unfold FiniteTree.depthList -/
            /-     unfold FiniteTree.leavesList -/
            /-     unfold FiniteTree.innerLabelsList -/
            /-     specialize ih hd -/
            /-     have ih := ih.mp (by -/
            /-       apply h -/
            /-       unfold FiniteTreeList.toList -/
            /-       simp -/
            /-     ) -/
            /-     have ih_inner := aux tl (by -/
            /-       intro t t_mem -/
            /-       apply h -/
            /-       unfold FiniteTreeList.toList -/
            /-       simp [t_mem] -/
            /-     ) -/
            /-     constructor -/
            /-     . rw [Nat.max_le] -/
            /-       constructor -/
            /-       . apply ih.left -/
            /-       . apply ih_inner.left -/
            /-     constructor -/
            /-     . intro c c_mem -/
            /-       rw [List.mem_append] at c_mem -/
            /-       cases c_mem with -/
            /-       | inl c_mem => apply ih.right.left; exact c_mem -/
            /-       | inr c_mem => apply ih_inner.right.left; exact c_mem -/
            /-     . intro func func_mem -/
            /-       rw [List.mem_append] at func_mem -/
            /-       cases func_mem with -/
            /-       | inl func_mem => apply ih.right.right; exact func_mem -/
            /-       | inr func_mem => apply ih_inner.right.right; exact func_mem -/

            unfold FiniteTree.depth
            unfold FiniteTree.leaves
            unfold FiniteTree.innerLabels

            have this := (aux (FiniteTreeList.fromList ts)).mp (by intro t t_mem; rw [FiniteTreeList.fromListToListIsId] at t_mem; apply ts_mem.right; exact t_mem)
            constructor
            . rw [Nat.add_comm]
              apply Nat.succ_le_succ
              exact this.left
            constructor
            . exact this.right.left
            . intro func' func'_mem
              rw [List.mem_cons] at func'_mem
              cases func'_mem with
              | inl func'_mem => rw [func'_mem]; exact func_mem
              | inr func'_mem => apply this.right.right; exact func'_mem

          . intro h
            exists t_func
            constructor
            . apply h.right.right
              unfold FiniteTree.innerLabels
              simp
            exists ts

            unfold FiniteTree.depth at h
            unfold FiniteTree.leaves at h
            unfold FiniteTree.innerLabels at h

            have this := (aux ts).mpr (by
              constructor
              . rw [Nat.add_comm] at h
                rw [Nat.succ_le_succ_iff] at h
                exact h.left
              constructor
              . exact h.right.left
              . intro func func_mem
                apply h.right.right
                simp [func_mem]
            )

            constructor
            . rw [mem_all_term_lists_of_length]
              constructor
              . sorry
              . intro t t_mem
                apply this
                exact t_mem
            . rw [FiniteTreeList.toListFromListIsId]

end ListsOfTerms
