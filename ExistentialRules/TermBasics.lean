import ExistentialRules.List
import ExistentialRules.FiniteTree
import ExistentialRules.Set.Basic
import ExistentialRules.Set.Finite

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

mutual

  def PreGroundTerm.arity_ok {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] : FiniteTree (SkolemFS sig) sig.C -> Bool
  | .leaf _ => true
  | .inner func ts =>
    ts.toList.length == func.arity && arity_ok_list ts

  def PreGroundTerm.arity_ok_list {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] : FiniteTreeList (SkolemFS sig) sig.C -> Bool
  | .nil => true
  | .cons hd tl => arity_ok hd && arity_ok_list tl

end

theorem PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] (ts : FiniteTreeList (SkolemFS sig) sig.C) : (∀ t, t ∈ ts.toList -> PreGroundTerm.arity_ok t) ↔ PreGroundTerm.arity_ok_list ts := by
  cases ts with
  | nil => simp [arity_ok_list, FiniteTreeList.toList]
  | cons hd tl =>
    unfold arity_ok_list
    simp [FiniteTreeList.toList]
    intro _
    apply arity_ok_list_iff_arity_ok_each_mem

section FunctionPathsAndCyclicity

  variable {sig : Signature} [DecidableEq sig.V]

  mutual

    def PreGroundTerm.function_paths : FiniteTree (SkolemFS sig) sig.C -> List (List (SkolemFS sig))
    | .leaf _ => [[]]
    | .inner f ts =>
      match ts with
      | .nil => [[f]]
      | _ => (function_paths_list ts).map (fun path => f :: path)

    def PreGroundTerm.function_paths_list : FiniteTreeList (SkolemFS sig) sig.C -> List (List (SkolemFS sig))
    | .nil => []
    | .cons hd tl => (function_paths hd) ++ (function_paths_list tl)

  end

  mutual

    theorem PreGroundTerm.function_path_elements_are_inner_labels (t : FiniteTree (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t -> ∀f, f ∈ path -> f ∈ t.innerLabels := by
      intro path path_mem f f_mem
      cases t with
      | leaf c =>
        simp only [function_paths, List.mem_singleton] at path_mem
        rw [path_mem] at f_mem
        simp at f_mem
      | inner func ts =>
        unfold function_paths at path_mem
        cases ts with
        | nil =>
          rw [List.mem_singleton] at path_mem
          rw [path_mem] at f_mem
          rw [List.mem_singleton] at f_mem
          unfold FiniteTree.innerLabels
          rw [List.mem_cons]
          apply Or.inl
          exact f_mem
        | cons hd tl =>
          rw [List.mem_map] at path_mem
          rcases path_mem with ⟨path', mem, eq⟩
          rw [← eq] at f_mem
          rw [List.mem_cons] at f_mem
          unfold FiniteTree.innerLabels
          rw [List.mem_cons]
          cases f_mem with
          | inl f_mem => apply Or.inl; exact f_mem
          | inr f_mem =>
            apply Or.inr
            exact function_path_elements_are_inner_labels_list (FiniteTreeList.cons hd tl) path' mem f f_mem

    theorem PreGroundTerm.function_path_elements_are_inner_labels_list (ts : FiniteTreeList (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths_list ts -> ∀f, f ∈ path -> f ∈ FiniteTree.innerLabelsList ts := by
      intro path path_mem f f_mem
      cases ts with
      | nil =>
        unfold function_paths_list at path_mem
        simp at path_mem
      | cons hd tl =>
        unfold function_paths_list at path_mem
        rw [List.mem_append] at path_mem
        unfold FiniteTree.innerLabelsList
        rw [List.mem_append]
        cases path_mem with
        | inl path_mem =>
          apply Or.inl
          exact function_path_elements_are_inner_labels hd path path_mem f f_mem
        | inr path_mem =>
          apply Or.inr
          exact function_path_elements_are_inner_labels_list tl path path_mem f f_mem

  end

  mutual

    theorem PreGroundTerm.function_path_of_depth_exists (t : FiniteTree (SkolemFS sig) sig.C) : ∃ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t ∧ path.length = t.depth - 1 := by
      cases t with
      | leaf c => exists []; simp [FiniteTree.depth, function_paths]
      | inner f ts =>
        cases ts with
        | nil =>
          exists [f]
          constructor
          . unfold function_paths
            simp
          . unfold FiniteTree.depth
            unfold FiniteTree.depthList
            simp
        | cons hd tl =>
          rcases PreGroundTerm.function_path_of_depth_exists_list (FiniteTreeList.cons hd tl) (by simp) with ⟨path, mem, len⟩
          exists (f :: path)
          constructor
          . unfold function_paths
            rw [List.mem_map]
            exists path
          . unfold List.length
            unfold FiniteTree.depth
            rw [len]
            rw [Nat.sub_one_add_one]
            . rw [Nat.add_comm]
              simp
            . unfold FiniteTree.depthList
              intro contra
              have : hd.depth = 0 ∧ FiniteTree.depthList tl = 0 := by omega
              have contra := this.left
              unfold FiniteTree.depth at contra
              cases hd <;> simp at contra

    theorem PreGroundTerm.function_path_of_depth_exists_list (ts : FiniteTreeList (SkolemFS sig) sig.C) : ts ≠ FiniteTreeList.nil -> ∃ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths_list ts ∧ path.length = (FiniteTree.depthList ts) - 1 := by
      intro neq
      cases ts with
      | nil => simp at neq
      | cons hd tl =>
        cases tl with
        | nil =>
          have := function_path_of_depth_exists hd
          rcases this with ⟨path, mem, len⟩
          exists path
          constructor
          . unfold function_paths_list
            rw [List.mem_append]
            apply Or.inl
            exact mem
          . unfold FiniteTree.depthList
            unfold FiniteTree.depthList
            rw [Nat.max_eq_left]
            . exact len
            . unfold FiniteTree.depth
              cases hd <;> simp
        | cons mid tl =>
          cases Decidable.em (hd.depth ≤ FiniteTree.depthList (FiniteTreeList.cons mid tl)) with
          | inl depth_le =>
            have := PreGroundTerm.function_path_of_depth_exists_list (FiniteTreeList.cons mid tl) (by simp)
            rcases this with ⟨path, mem, len⟩
            exists path
            constructor
            . unfold function_paths_list
              rw [List.mem_append]
              apply Or.inr
              exact mem
            . unfold FiniteTree.depthList
              rw [Nat.max_eq_right]
              . exact len
              . exact depth_le
          | inr depth_le =>
            have := function_path_of_depth_exists hd
            rcases this with ⟨path, mem, len⟩
            exists path
            constructor
            . unfold function_paths_list
              rw [List.mem_append]
              apply Or.inl
              exact mem
            . unfold FiniteTree.depthList
              rw [Nat.max_eq_left]
              . exact len
              . apply Nat.le_of_lt
                simp at depth_le
                exact depth_le

  end

  mutual

    def PreGroundTerm.contains_func (func : SkolemFS sig) : FiniteTree (SkolemFS sig) sig.C -> Bool
    | .leaf _ => false
    | .inner func' ts => func == func' || PreGroundTerm.contains_func_list func ts

    def PreGroundTerm.contains_func_list (func : SkolemFS sig) : FiniteTreeList (SkolemFS sig) sig.C -> Bool
    | .nil => false
    | .cons hd tl => contains_func func hd || contains_func_list func tl

  end

  mutual

    theorem PreGroundTerm.function_path_elements_are_in_contains_func (t : FiniteTree (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t -> ∀f, f ∈ path -> PreGroundTerm.contains_func f t := by
      intro path path_mem f f_mem
      cases t with
      | leaf c =>
        simp only [function_paths, List.mem_singleton] at path_mem
        rw [path_mem] at f_mem
        simp at f_mem
      | inner func ts =>
        unfold contains_func
        rw [Bool.or_eq_true]
        unfold function_paths at path_mem
        cases ts with
        | nil =>
          rw [List.mem_singleton] at path_mem
          rw [path_mem] at f_mem
          rw [List.mem_singleton] at f_mem
          apply Or.inl
          rw [f_mem]
          simp
        | cons hd tl =>
          rw [List.mem_map] at path_mem
          rcases path_mem with ⟨path', mem, eq⟩
          rw [← eq] at f_mem
          rw [List.mem_cons] at f_mem
          cases f_mem with
          | inl f_mem => apply Or.inl; rw [f_mem]; simp
          | inr f_mem =>
            apply Or.inr
            exact PreGroundTerm.function_path_elements_are_in_contains_func_list (FiniteTreeList.cons hd tl) path' mem f f_mem

    theorem PreGroundTerm.function_path_elements_are_in_contains_func_list (ts : FiniteTreeList (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths_list ts -> ∀f, f ∈ path -> PreGroundTerm.contains_func_list f ts := by
      intro path path_mem f f_mem
      cases ts with
      | nil =>
        unfold function_paths_list at path_mem
        simp at path_mem
      | cons hd tl =>
        unfold contains_func_list
        rw [Bool.or_eq_true]
        unfold function_paths_list at path_mem
        rw [List.mem_append] at path_mem
        cases path_mem with
        | inl path_mem => apply Or.inl; exact function_path_elements_are_in_contains_func hd path path_mem f f_mem
        | inr path_mem => apply Or.inr; exact function_path_elements_are_in_contains_func_list tl path path_mem f f_mem

  end

  mutual

    def PreGroundTerm.cyclic : FiniteTree (SkolemFS sig) sig.C -> Bool
    | .leaf _ => false
    | .inner func ts => (contains_func_list func ts) || PreGroundTerm.cyclic_list ts

    def PreGroundTerm.cyclic_list : FiniteTreeList (SkolemFS sig) sig.C -> Bool
    | .nil => false
    | .cons hd tl => PreGroundTerm.cyclic hd || PreGroundTerm.cyclic_list tl

  end

  mutual

    theorem PreGroundTerm.cyclic_of_path_with_dup (t : FiniteTree (SkolemFS sig) sig.C) (path : List (SkolemFS sig)) (path_mem : path ∈ PreGroundTerm.function_paths t) (dup : ¬ path.Nodup) : PreGroundTerm.cyclic t := by
      cases t with
      | leaf c =>
        unfold PreGroundTerm.function_paths at path_mem
        rw [List.mem_singleton] at path_mem
        rw [path_mem] at dup
        simp at dup
      | inner f ts =>
        unfold PreGroundTerm.function_paths at path_mem
        cases ts with
        | nil =>
          rw [List.mem_singleton] at path_mem
          rw [path_mem] at dup
          simp at dup
        | cons hd tl =>
          rw [List.mem_map] at path_mem
          rcases path_mem with ⟨path', mem, eq⟩
          unfold PreGroundTerm.cyclic
          rw [Bool.or_eq_true]
          cases Decidable.em (f ∈ path') with
          | inl f_mem =>
            apply Or.inl
            exact PreGroundTerm.function_path_elements_are_in_contains_func_list (FiniteTreeList.cons hd tl) path' mem f f_mem
          | inr f_mem =>
            apply Or.inr
            rw [← eq] at dup
            rw [List.nodup_cons] at dup
            simp only [not_and] at dup
            apply PreGroundTerm.cyclic_of_path_with_dup_list (FiniteTreeList.cons hd tl) path' mem
            apply dup
            apply f_mem

    theorem PreGroundTerm.cyclic_of_path_with_dup_list (ts : FiniteTreeList (SkolemFS sig) sig.C) (path : List (SkolemFS sig)) (path_mem : path ∈ PreGroundTerm.function_paths_list ts) (dup : ¬ path.Nodup) : PreGroundTerm.cyclic_list ts := by
      unfold cyclic_list
      cases ts with
      | nil =>
        unfold PreGroundTerm.function_paths_list at path_mem
        simp at path_mem
      | cons hd tl =>
        unfold PreGroundTerm.function_paths_list at path_mem
        rw [List.mem_append] at path_mem
        rw [Bool.or_eq_true]
        cases path_mem with
        | inl path_mem =>
          apply Or.inl
          exact cyclic_of_path_with_dup hd path path_mem dup
        | inr path_mem =>
          apply Or.inr
          exact cyclic_of_path_with_dup_list tl path path_mem dup

  end

  variable [DecidableEq sig.C]

  theorem PreGroundTerm.cyclic_of_depth_too_big (t : PreGroundTerm sig) (funcs : List (SkolemFS sig)) (nodup : funcs.Nodup) (funcs_in_t_from_funcs : ∀ func, func ∈ t.innerLabels -> func ∈ funcs) : funcs.length + 2 ≤ t.depth -> PreGroundTerm.cyclic t := by
    intro le_depth
    have := PreGroundTerm.function_path_of_depth_exists t
    rcases this with ⟨path, path_mem, path_len⟩

    have path_length_gt : funcs.length < path.length := by
      rw [path_len]
      apply Nat.lt_of_succ_le
      apply Nat.le_of_succ_le_succ
      rw [Nat.succ_eq_add_one]
      rw [Nat.succ_eq_add_one]
      rw [Nat.sub_one_add_one]
      . exact le_depth
      . unfold FiniteTree.depth
        cases t <;> simp

    have dup_in_path : ¬ path.Nodup := by
      apply List.contains_dup_of_exceeding_nodup_list_with_same_elements funcs path nodup path_length_gt
      intro f f_mem
      apply funcs_in_t_from_funcs
      exact PreGroundTerm.function_path_elements_are_inner_labels t path path_mem f f_mem

    exact PreGroundTerm.cyclic_of_path_with_dup t path path_mem dup_in_path

end FunctionPathsAndCyclicity

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

def GroundTerm.const (c : sig.C) : GroundTerm sig := ⟨FiniteTree.leaf c, by simp [PreGroundTerm.arity_ok]⟩
def GroundTerm.func (func : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = func.arity) : GroundTerm sig := ⟨FiniteTree.inner func (FiniteTreeList.fromList ts.unattach), by
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
def GroundTerm.cases
    {motive : GroundTerm sig -> Sort u}
    (t : GroundTerm sig)
    (const : (c : sig.C) -> (eq : t = GroundTerm.const c) -> motive (GroundTerm.const c))
    (func : (func : SkolemFS sig) -> (ts : List (GroundTerm sig)) -> (arity_ok : ts.length = func.arity) -> (eq : t = GroundTerm.func func ts arity_ok) -> motive (GroundTerm.func func ts arity_ok)) :
    motive t :=
  match eq : t.val with
  | .leaf c =>
    have eq : t = GroundTerm.const c := Subtype.eq eq
    eq ▸ const c eq
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
    exact eq ▸ (func f ts arity_ok eq)

@[elab_as_elim, induction_eliminator]
def GroundTerm.rec
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

def GroundTerm.toConst (t : GroundTerm sig) (isConst : ∃ c, t = GroundTerm.const c) : sig.C :=
  match eq : t.val with
  | .leaf c => c
  | .inner _ _ => by
    apply False.elim
    rcases isConst with ⟨c, isConst⟩
    rw [isConst] at eq
    simp [GroundTerm.const] at eq

def SkolemTerm.variables : SkolemTerm sig -> List sig.V
  | .var v => List.cons v List.nil
  | .const _ => List.nil
  | .func _ vs _ => vs

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
    | zero => intro ts; unfold all_term_lists_of_length; simp; intro eq t _ mem; rw [eq] at mem; simp at mem
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
      (all_term_lists_of_length prev func.arity).attach.map (fun ⟨ts, mem⟩ =>
        ⟨
          FiniteTree.inner func (FiniteTreeList.fromList ts.unattach),
          by
            unfold PreGroundTerm.arity_ok
            simp
            constructor
            . rw [FiniteTreeList.fromListToListIsId]
              rw [List.length_unattach]
              rw [mem_all_term_lists_of_length] at mem
              exact mem.left
            . apply (PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem _).mp
              rw [FiniteTreeList.fromListToListIsId]
              intro t t_mem
              unfold List.unattach at t_mem
              rw [List.mem_map] at t_mem
              rcases t_mem with ⟨t, h⟩
              rw [← h.right]
              exact t.property
        ⟩
      )
    ) ++ prev

  theorem mem_all_terms_limited_by_depth (constants : List sig.C) (funcs : List (SkolemFS sig)) (depth : Nat) :
      ∀ t, t ∈ (all_terms_limited_by_depth constants funcs depth) ↔ (t.val.depth ≤ depth ∧ (∀ c, c ∈ t.val.leaves -> c ∈ constants) ∧ (∀ func, func ∈ t.val.innerLabels -> func ∈ funcs)) := by
    induction depth with
    | zero =>
      simp [all_terms_limited_by_depth]
      intro t _ t_depth
      cases t <;> simp [FiniteTree.depth] at t_depth
    | succ depth ih =>
      intro t
      unfold all_terms_limited_by_depth

      cases depth with
      | zero =>
        simp only [Nat.zero_add]
        constructor
        . intro h
          rw [List.mem_map] at h
          rcases h with ⟨c, c_mem, h⟩
          rw [← h]
          simp [GroundTerm.const, FiniteTree.depth, FiniteTree.leaves, FiniteTree.innerLabels]
          exact c_mem
        . intro h
          cases eq : t with
          | const c =>
            rw [List.mem_map]
            exists c
            constructor
            . apply h.right.left
              simp [eq, GroundTerm.const, FiniteTree.leaves]
            . rfl
          | func _ ts _ =>
            have contra := h.left
            unfold FiniteTree.depth at contra
            simp only [eq, GroundTerm.func] at contra
            cases ts with
            | nil => simp [FiniteTreeList.fromList, FiniteTree.depthList] at contra
            | cons t _ =>
              simp only [List.unattach, List.map_cons, FiniteTreeList.fromList, FiniteTree.depthList] at contra
              rw [Nat.add_comm, Nat.succ_le_succ_iff, Nat.max_le] at contra
              have contra := contra.left
              unfold FiniteTree.depth at contra
              cases eq : t.val <;> simp [eq] at contra
      | succ depth =>
        let rec aux : ∀ (ts : FiniteTreeList (SkolemFS sig) sig.C), (PreGroundTerm.arity_ok_list ts) -> ((∀ (t : GroundTerm sig), t.val ∈ ts.toList -> t ∈ (all_terms_limited_by_depth constants funcs depth.succ)) ↔
            ((FiniteTree.depthList ts ≤ depth.succ) ∧ (∀ c, c ∈ FiniteTree.leavesList ts -> c ∈ constants) ∧ (∀ func, func ∈ FiniteTree.innerLabelsList ts -> func ∈ funcs))) := by
          intro ts arities_ok
          cases ts with
          | nil =>
            simp [FiniteTree.depthList, FiniteTree.leavesList, FiniteTree.innerLabelsList, FiniteTreeList.toList]
          | cons hd tl =>
            unfold PreGroundTerm.arity_ok_list at arities_ok
            rw [Bool.and_eq_true] at arities_ok
            unfold FiniteTree.depthList
            unfold FiniteTree.leavesList
            unfold FiniteTree.innerLabelsList

            specialize ih ⟨hd, arities_ok.left⟩
            have ih_inner := aux tl

            constructor
            . intro h

              have ih := ih.mp (by
                apply h
                unfold FiniteTreeList.toList
                simp
              )
              have ih_inner := (ih_inner arities_ok.right).mp (by
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
              rw [Nat.max_le] at h

              have ih := ih.mpr (by
                constructor
                . exact h.left.left
                constructor
                . intro c c_mem
                  apply h.right.left
                  rw [List.mem_append]
                  apply Or.inl
                  exact c_mem
                . intro func func_mem
                  apply h.right.right
                  rw [List.mem_append]
                  apply Or.inl
                  exact func_mem
              )
              have ih_inner := (ih_inner arities_ok.right).mpr (by
                constructor
                . exact h.left.right
                constructor
                . intro c c_mem
                  apply h.right.left
                  rw [List.mem_append]
                  apply Or.inr
                  exact c_mem
                . intro func func_mem
                  apply h.right.right
                  rw [List.mem_append]
                  apply Or.inr
                  exact func_mem
              )
              intro t t_mem
              unfold FiniteTreeList.toList at t_mem
              rw [List.mem_cons] at t_mem
              cases t_mem with
              | inl t_mem =>
                have : t = ⟨hd, arities_ok.left⟩ := by apply Subtype.eq; exact t_mem
                rw [this]
                apply ih
              | inr t_mem => apply ih_inner; exact t_mem

        constructor
        . intro h
          rw [List.mem_append] at h
          cases h with
          | inr h =>
            rw [ih] at h
            constructor
            . apply Nat.le_succ_of_le
              exact h.left
            constructor
            . exact h.right.left
            . exact h.right.right
          | inl h =>
            simp only [List.mem_flatMap, List.mem_map] at h
            rcases h with ⟨func, func_mem, ts, ts_mem, t_eq⟩
            rw [← t_eq]
            unfold List.attach at ts_mem
            unfold List.attachWith at ts_mem
            rw [List.mem_pmap] at ts_mem
            rcases ts_mem with ⟨ts_val, ts_mem, ts_eq⟩
            rw [mem_all_term_lists_of_length] at ts_mem

            unfold FiniteTree.depth
            unfold FiniteTree.leaves
            unfold FiniteTree.innerLabels

            have this := (aux (FiniteTreeList.fromList ts_val.unattach) (by
              apply (PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem _).mp
              rw [FiniteTreeList.fromListToListIsId]
              intro t t_mem
              unfold List.unattach at t_mem
              rw [List.mem_map] at t_mem
              rcases t_mem with ⟨t, h⟩
              rw [← h.right]
              exact t.property
            )).mp (by
              intro t t_mem
              rw [FiniteTreeList.fromListToListIsId] at t_mem
              apply ts_mem.right
              unfold List.unattach at t_mem
              rw [List.mem_map] at t_mem
              rcases t_mem with ⟨t', mem, eq⟩
              have : t' = t := by apply Subtype.eq; exact eq
              rw [← this]
              exact mem
            )

            rw [← ts_eq]
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
          rw [List.mem_append]
          simp only [List.mem_flatMap, List.mem_map]
          rcases h with ⟨depth_le, consts_mem, funcs_mem⟩
          rw [Nat.le_iff_lt_or_eq] at depth_le
          cases depth_le with
          | inl depth_le =>
            apply Or.inr
            rw [ih]
            constructor
            . apply Nat.le_of_lt_succ
              exact depth_le
            constructor
            . exact consts_mem
            . exact funcs_mem
          | inr depth_le =>
            cases eq : t.val with
            | leaf _ => rw [eq] at depth_le; simp [FiniteTree.depth] at depth_le
            | inner t_func ts =>
              rw [eq] at depth_le
              rw [eq] at consts_mem
              rw [eq] at funcs_mem
              unfold FiniteTree.depth at depth_le
              unfold FiniteTree.leaves at consts_mem
              unfold FiniteTree.innerLabels at funcs_mem

              have this := (aux ts (by have prop := t.property; unfold PreGroundTerm.arity_ok at prop; simp only [eq, Bool.and_eq_true] at prop; exact prop.right)).mpr (by
                constructor
                . apply Nat.le_of_eq
                  rw [Nat.add_comm] at depth_le
                  injection depth_le with depth_le
                constructor
                . exact consts_mem
                . intro func func_mem
                  apply funcs_mem
                  simp [func_mem]
              )

              apply Or.inl
              exists t_func
              constructor
              . apply funcs_mem
                simp
              let ts_ground_terms : List (GroundTerm sig) := ts.toList.attach.map (fun ⟨t', mem⟩ =>
                ⟨t', by
                  have prop := t.property
                  unfold PreGroundTerm.arity_ok at prop
                  rw [eq] at prop
                  simp only [Bool.and_eq_true] at prop
                  apply (PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem ts).mpr
                  . exact prop.right
                  . exact mem
                ⟩
              )
              have : ts_ground_terms ∈ all_term_lists_of_length (all_terms_limited_by_depth constants funcs depth.succ) t_func.arity := by
                rw [mem_all_term_lists_of_length]
                constructor
                . have prop := t.property
                  unfold PreGroundTerm.arity_ok at prop
                  rw [eq, Bool.and_eq_true, beq_iff_eq] at prop
                  unfold ts_ground_terms
                  rw [List.length_map, List.length_attach]
                  exact prop.left
                . intro t t_mem
                  apply this
                  unfold ts_ground_terms at t_mem
                  rw [List.mem_map] at t_mem
                  rcases t_mem with ⟨val, val_mem, t_eq⟩
                  unfold List.attach at val_mem
                  unfold List.attachWith at val_mem
                  rw [List.mem_pmap] at val_mem
                  rcases val_mem with ⟨_, val_mem, eq⟩
                  simp only at t_eq
                  rw [← t_eq, ← eq]
                  exact val_mem

              exists ⟨ts_ground_terms, this⟩

              constructor
              . apply List.mem_attach
              . have : ts_ground_terms.unattach = ts.toList := by
                  unfold List.unattach
                  unfold ts_ground_terms
                  rw [List.map_map, List.map_attach]
                  simp
                apply Subtype.eq
                simp only
                rw [this]
                rw [FiniteTreeList.toListFromListIsId]
                rw [eq]

end ListsOfTerms

