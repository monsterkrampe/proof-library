import ExistentialRules.Terms.Basic

variable {sig : Signature} [DecidableEq sig.V]

namespace PreGroundTerm

  mutual

    def function_paths : FiniteTree (SkolemFS sig) sig.C -> List (List (SkolemFS sig))
    | .leaf _ => [[]]
    | .inner f ts =>
      match ts with
      | .nil => [[f]]
      | _ => (function_paths_list ts).map (fun path => f :: path)

    def function_paths_list : FiniteTreeList (SkolemFS sig) sig.C -> List (List (SkolemFS sig))
    | .nil => []
    | .cons hd tl => (function_paths hd) ++ (function_paths_list tl)

  end

  mutual

    theorem function_path_elements_are_inner_labels (t : FiniteTree (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t -> ∀f, f ∈ path -> f ∈ t.innerLabels := by
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

    theorem function_path_elements_are_inner_labels_list (ts : FiniteTreeList (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths_list ts -> ∀f, f ∈ path -> f ∈ FiniteTree.innerLabelsList ts := by
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

    theorem function_path_of_depth_exists (t : FiniteTree (SkolemFS sig) sig.C) : ∃ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t ∧ path.length = t.depth - 1 := by
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

    theorem function_path_of_depth_exists_list (ts : FiniteTreeList (SkolemFS sig) sig.C) : ts ≠ FiniteTreeList.nil -> ∃ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths_list ts ∧ path.length = (FiniteTree.depthList ts) - 1 := by
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

    def contains_func (func : SkolemFS sig) : FiniteTree (SkolemFS sig) sig.C -> Bool
    | .leaf _ => false
    | .inner func' ts => func == func' || PreGroundTerm.contains_func_list func ts

    def contains_func_list (func : SkolemFS sig) : FiniteTreeList (SkolemFS sig) sig.C -> Bool
    | .nil => false
    | .cons hd tl => contains_func func hd || contains_func_list func tl

  end

  mutual

    theorem function_path_elements_are_in_contains_func (t : FiniteTree (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t -> ∀f, f ∈ path -> PreGroundTerm.contains_func f t := by
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

    theorem function_path_elements_are_in_contains_func_list (ts : FiniteTreeList (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths_list ts -> ∀f, f ∈ path -> PreGroundTerm.contains_func_list f ts := by
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

    def cyclic : FiniteTree (SkolemFS sig) sig.C -> Bool
    | .leaf _ => false
    | .inner func ts => (contains_func_list func ts) || PreGroundTerm.cyclic_list ts

    def cyclic_list : FiniteTreeList (SkolemFS sig) sig.C -> Bool
    | .nil => false
    | .cons hd tl => PreGroundTerm.cyclic hd || PreGroundTerm.cyclic_list tl

  end

  mutual

    theorem cyclic_of_path_with_dup (t : FiniteTree (SkolemFS sig) sig.C) (path : List (SkolemFS sig)) (path_mem : path ∈ PreGroundTerm.function_paths t) (dup : ¬ path.Nodup) : PreGroundTerm.cyclic t := by
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

    theorem cyclic_of_path_with_dup_list (ts : FiniteTreeList (SkolemFS sig) sig.C) (path : List (SkolemFS sig)) (path_mem : path ∈ PreGroundTerm.function_paths_list ts) (dup : ¬ path.Nodup) : PreGroundTerm.cyclic_list ts := by
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

  theorem cyclic_of_depth_too_big (t : PreGroundTerm sig) (funcs : List (SkolemFS sig)) (nodup : funcs.Nodup) (funcs_in_t_from_funcs : ∀ func, func ∈ t.innerLabels -> func ∈ funcs) : funcs.length + 2 ≤ t.depth -> PreGroundTerm.cyclic t := by
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

end PreGroundTerm

