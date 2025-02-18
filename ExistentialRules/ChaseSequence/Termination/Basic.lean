import ExistentialRules.ChaseSequence.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

section Definitions

  namespace ChaseBranch
    def terminates (branch : ChaseBranch obs kb) : Prop :=
      ∃ n : Nat, branch.branch.infinite_list n = none
  end ChaseBranch

  namespace ChaseTree
    def terminates (ct : ChaseTree obs kb) : Prop := ∀ branch, branch ∈ ct.branches -> branch.terminates
  end ChaseTree

  namespace KnowledgeBase
    def terminates (kb : KnowledgeBase sig) (obs : ObsoletenessCondition sig) : Prop := ∀ (ct : ChaseTree obs kb), ct.terminates
  end KnowledgeBase

  namespace RuleSet
    def terminates (rs : RuleSet sig) (obs : ObsoletenessCondition sig) : Prop := ∀ (db : Database sig), { rules := rs, db := db : KnowledgeBase sig }.terminates obs
  end RuleSet

end Definitions

section GeneralResults

  namespace ChaseBranch

    theorem terminating_has_last_index (branch : ChaseBranch obs kb) : branch.terminates ↔ ∃ n, (branch.branch.infinite_list n).isSome ∧ ∀ m, m > n -> branch.branch.infinite_list m = none := by
      unfold ChaseBranch.terminates
      constructor
      . intro h
        rcases h with ⟨n, h⟩
        induction n with
        | zero => rw [branch.database_first] at h; simp at h
        | succ n ih =>
          cases eq : branch.branch.infinite_list n with
          | none => apply ih; exact eq
          | some _ =>
            exists n
            rw [eq]
            simp
            intro m n_lt_m
            have : n+1 ≤ m := by apply Nat.succ_le_of_lt; exact n_lt_m
            rw [Nat.le_iff_lt_or_eq] at this
            cases this with
            | inr n_eq_m => rw [← n_eq_m]; exact h
            | inl n_lt_m =>
              have no_holes := branch.branch.no_holes
              apply Option.decidable_eq_none.byContradiction
              intro contra
              specialize no_holes m contra
              let n_succ_fin : Fin m := ⟨n+1, n_lt_m⟩
              specialize no_holes n_succ_fin
              apply no_holes
              exact h
      . intro h
        rcases h with ⟨n, _, h⟩
        exists n+1
        apply h
        simp

    theorem terminates_iff_result_finite (branch : ChaseBranch obs kb) : branch.terminates ↔ branch.result.finite := by
      constructor
      . intro h
        cases (terminating_has_last_index branch).mp h with | intro n h =>
          cases eq : branch.branch.infinite_list n with
          | none => rw [eq] at h; simp at h
          | some node =>
            cases node.fact.property with | intro l hl =>
              exists l
              unfold ChaseBranch.result
              constructor
              . exact hl.left
              . intro e
                rw [hl.right e]
                simp [Set.element]
                constructor
                . intro e_in_node
                  exists n
                  rw [eq]
                  simp [Option.is_some_and]
                  exact e_in_node
                . intro ex_n'
                  cases ex_n' with | intro n' hn' =>
                    have : n' ≤ n := by
                      apply Decidable.byContradiction
                      intro contra
                      simp at contra
                      have contra := h.right n' contra
                      rw [contra] at hn'
                      simp [Option.is_some_and] at hn'
                    have subset := chaseBranchSetIsSubsetOfAllFollowing branch n' (n-n')
                    cases eq' : branch.branch.infinite_list n' with
                    | none => rw [eq'] at hn'; simp [Option.is_some_and] at hn'
                    | some node' =>
                      rw [eq'] at hn'
                      simp [Option.is_some_and] at hn'
                      rw [eq'] at subset
                      simp at subset
                      have : n' + (n - n') = n := by apply Nat.add_sub_of_le; exact this
                      rw [this] at subset
                      rw [eq] at subset
                      simp [Option.is_none_or] at subset
                      apply subset
                      exact hn'
      . intro h
        rcases h with ⟨l, h⟩
        unfold ChaseBranch.result at h
        simp only [Set.element] at h
        unfold ChaseBranch.terminates

        have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> ∃ n, (branch.branch.infinite_list n).is_some_and (fun fs => e ∈ fs.fact.val)) ->
            (∃ n, (branch.branch.infinite_list n).is_some_and (fun fs => ∀ e, e ∈ l -> e ∈ fs.fact.val)) := by
          intro l
          induction l with
          | nil => simp; exists 0; rw [branch.database_first]; simp [Option.is_some_and]
          | cons hd tl ih =>
            intro h
            specialize ih (by intro _ e_mem; apply h; simp [e_mem])
            rcases ih with ⟨n_ih, ih⟩
            specialize h hd (by simp)
            rcases h with ⟨n_hd, h⟩
            exists max n_ih n_hd

            cases eq_n_ih : branch.branch.infinite_list n_ih with
            | none => rw [eq_n_ih] at ih; simp [Option.is_some_and] at ih
            | some _=>
            cases eq_n_hd : branch.branch.infinite_list n_hd with
            | none => rw [eq_n_hd] at h; simp [Option.is_some_and] at h
            | some _=>

            cases Decidable.em (n_ih ≤ n_hd) with
            | inl n_ih_le_n_hd =>
              rw [Nat.max_eq_right n_ih_le_n_hd]
              rw [eq_n_hd]; simp [Option.is_some_and]
              constructor
              . rw [eq_n_hd] at h; simp [Option.is_some_and] at h
                exact h
              . have subs_following := chaseBranchSetIsSubsetOfAllFollowing branch n_ih (n_hd - n_ih)
                rw [eq_n_ih] at subs_following
                simp at subs_following
                rw [Nat.add_sub_of_le n_ih_le_n_hd] at subs_following
                rw [eq_n_hd] at subs_following
                simp [Option.is_none_or] at subs_following
                intro e e_mem_tl
                apply subs_following
                rw [eq_n_ih] at ih; simp [Option.is_some_and] at ih
                apply ih
                exact e_mem_tl
            | inr n_ih_not_le_n_hd =>
              have n_hd_le_n_ih : n_hd ≤ n_ih := by apply Nat.le_of_lt; apply Nat.lt_of_not_le; exact n_ih_not_le_n_hd
              rw [Nat.max_eq_left n_hd_le_n_ih]
              rw [eq_n_ih]; simp [Option.is_some_and]
              constructor
              . have subs_following := chaseBranchSetIsSubsetOfAllFollowing branch n_hd (n_ih - n_hd)
                rw [eq_n_hd] at subs_following
                simp at subs_following
                rw [Nat.add_sub_of_le n_hd_le_n_ih] at subs_following
                rw [eq_n_ih] at subs_following
                simp [Option.is_none_or] at subs_following
                apply subs_following
                rw [eq_n_hd] at h; simp [Option.is_some_and] at h
                apply h
              . rw [eq_n_ih] at ih; simp [Option.is_some_and] at ih
                exact ih

        specialize this l (by intro e; exact (h.right e).mp)
        rcases this with ⟨n, this⟩

        have trg_ex := branch.triggers_exist
        specialize trg_ex n

        cases eq : branch.branch.infinite_list n with
        | none => exists n
        | some chase_node =>
          rw [eq] at trg_ex
          simp [Option.is_none_or] at trg_ex
          cases trg_ex with
          | inr trg_ex =>
            unfold not_exists_trigger_opt_fs at trg_ex
            exists n+1
            exact trg_ex.right
          | inl trg_ex =>
            unfold exists_trigger_opt_fs at trg_ex
            rcases trg_ex with ⟨trg, active, i, eq_fs⟩
            unfold Trigger.active at active

            apply False.elim
            apply active.right
            apply obs.contains_trg_result_implies_cond i

            intro e e_mem_res
            rw [eq] at this
            simp [Option.is_some_and] at this
            apply this
            apply (h.right e).mpr
            exists n+1
            rw [← eq_fs]
            simp [Option.is_some_and]
            apply Or.inr
            exact e_mem_res

  end ChaseBranch

  namespace ChaseTree

    theorem finitely_many_branch_of_terminates (ct : ChaseTree obs kb) : ct.terminates -> ct.branches.finite := by
      unfold terminates
      unfold ChaseBranch.terminates
      intro each_b_term

      have : ∀ b, b ∈ ct.tree.branches -> ∃ i, b.infinite_list i = none := by
        intro b b_mem
        rcases b_mem with ⟨nodes, b_mem, _⟩

        -- It might seem like byContradiction is not needed but we need the contra hypothesis to show that cb is a proper chase branch
        apply Classical.byContradiction
        intro contra

        let cb : ChaseBranch obs kb := {
          branch := b
          database_first := by rw [← ct.database_first]; rw [b_mem]; simp [InfiniteList.take]; rfl
          triggers_exist := by
            intro n
            cases eq : b.infinite_list n with
            | none => simp [Option.is_none_or]
            | some node =>
              simp [Option.is_none_or]
              have trgs_ex := ct.triggers_exist (nodes.take n).reverse
              unfold FiniteDegreeTree.get at trgs_ex
              unfold PossiblyInfiniteTree.get at trgs_ex
              rw [← b_mem, eq] at trgs_ex
              simp [Option.is_none_or] at trgs_ex
              cases trgs_ex with
              | inr trgs_ex =>
                unfold not_exists_trigger_list at trgs_ex
                have all_none := ct.tree.children_empty_means_all_following_none _ trgs_ex.right
                specialize all_none (nodes n)
                apply False.elim
                apply contra
                exists (n+1)
                rw [b_mem]
                unfold InfiniteList.take
                simp
                exact all_none
              | inl trgs_ex =>
                apply Or.inl
                unfold exists_trigger_list at trgs_ex
                unfold exists_trigger_list_condition at trgs_ex
                unfold exists_trigger_opt_fs
                rcases trgs_ex with ⟨trg, trg_active, trg_eq⟩
                exists trg
                constructor
                . exact trg_active
                . have length_eq : trg.val.result.length = (ct.tree.children (nodes.take n).reverse).length := by
                    rw [← trg_eq]
                    simp [List.enum_with_lt_length_eq]

                  have get_node_eq : (ct.tree.children (nodes.take n).reverse)[nodes n]? = b.infinite_list (n+1) := by
                    rw [FiniteDegreeTree.getElem_children_eq_getElem_tree_children]
                    rw [PossiblyInfiniteTree.getElem_children_eq_get_tree]
                    rw [b_mem]
                    conv => right; unfold InfiniteList.take
                    simp
                    rfl

                  have nodes_n_le : nodes n < trg.val.result.length := by
                    rw [length_eq]
                    apply Decidable.byContradiction
                    intro contra'
                    simp at contra'
                    rw [List.getElem?_eq_none contra'] at get_node_eq
                    apply contra
                    exists (n+1)
                    rw [get_node_eq]

                  exists ⟨nodes n, nodes_n_le⟩


                  rw [List.map_eq_iff] at trg_eq
                  specialize trg_eq (nodes n)

                  simp only [← get_node_eq, trg_eq]
                  rw [List.getElem?_eq_getElem]
                  rw [List.getElem_attach]
                  . simp
                    constructor
                    . rw [List.enum_with_lt_getElem_snd_eq_getElem]
                    . rw [List.enum_with_lt_getElem_fst_eq_index]
                  . simp [List.enum_with_lt_length_eq]
                    exact nodes_n_le
          fairness := by
            intro trg
            have fair := ct.fairness_infinite_branches trg
            rcases fair with ⟨i, fair⟩
            exists i
            cases eq : b.infinite_list i with
            | none => apply False.elim; apply contra; exists i
            | some node =>
              simp [Option.is_some_and]
              constructor
              . specialize fair (nodes.take i).reverse (by simp [InfiniteList.length_take])
                unfold FiniteDegreeTree.get at fair
                unfold PossiblyInfiniteTree.get at fair
                rw [← b_mem, eq, Option.is_none_or] at fair
                exact fair
              . intro j lt
                cases eq2 : b.infinite_list j with
                | none => apply False.elim; apply contra; exists j
                | some node2 =>
                  rw [Option.is_none_or]
                  specialize fair (nodes.take j).reverse (by simp [InfiniteList.length_take]; exact Nat.le_of_lt lt)
                  unfold FiniteDegreeTree.get at fair
                  unfold PossiblyInfiniteTree.get at fair
                  rw [← b_mem, eq2, Option.is_none_or] at fair
                  exact fair
        }

        apply contra
        specialize each_b_term cb (by exists nodes)
        exact each_b_term

      -- Koenig's Lemma
      have : ct.tree.branches.finite := by
        apply ct.tree.branches_finite_of_each_finite
        apply this

      rcases this with ⟨l, l_nodup, l_eq⟩

      let cb_for_b (b : PossiblyInfiniteList (ChaseNode obs kb.rules)) : Option (ChaseBranch obs kb) :=
        match (Classical.propDecidable (∃ (cb : ChaseBranch obs kb), cb.branch = b)) with
        | .isTrue p => some (Classical.choose p)
        | .isFalse _ => none

      have := Classical.typeDecidableEq (ChaseBranch obs kb)
      let filtered := (l.filterMap (fun b => cb_for_b b)).eraseDupsKeepRight

      exists filtered
      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro e
        unfold filtered
        rw [List.mem_eraseDupsKeepRight_iff]
        unfold branches
        simp
        constructor
        . intro h
          rcases h with ⟨b, b_mem, b_eq⟩
          unfold cb_for_b at b_eq
          split at b_eq
          case h_1 _ p _ =>
            have spec := Classical.choose_spec p
            injection b_eq with b_eq
            rw [← b_eq]
            simp [Set.element]
            rw [spec]
            apply (l_eq b).mp
            exact b_mem
          case h_2 _ p _ =>
            simp at b_eq
        . intro h
          exists e.branch
          rw [l_eq]
          constructor
          . exact h
          . unfold cb_for_b
            split
            case h_1 _ p _ =>
              have spec := Classical.choose_spec p
              simp
              apply ChaseBranch.ext
              exact spec
            case h_2 _ p _ =>
              apply False.elim
              apply p
              exists e

    theorem result_finite_of_branches_finite (ct : ChaseTree obs kb) : ct.branches.finite -> ct.result.finite := by
      intro bs_finite
      unfold Set.finite at bs_finite
      rcases bs_finite with ⟨l, _, iff⟩
      have : DecidableEq (FactSet sig) := Classical.typeDecidableEq (FactSet sig)
      exists (l.map ChaseBranch.result).eraseDupsKeepRight
      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro fs
        rw [List.mem_eraseDupsKeepRight_iff]
        simp
        constructor
        . intro h
          rcases h with ⟨b, mem, eq⟩
          exists b
          constructor
          . rw [← iff]; exact mem
          . exact eq
        . intro h
          rcases h with ⟨b, mem, eq⟩
          exists b
          constructor
          . rw [iff]; exact mem
          . exact eq

    theorem terminates_iff_result_finite (ct : ChaseTree obs kb) : ct.terminates ↔ ∀ fs, fs ∈ ct.result -> fs.finite := by
      unfold terminates
      unfold result
      constructor
      . intro each_b_term
        intro res res_mem
        rcases res_mem with ⟨b, mem, eq⟩
        rw [← eq]
        rw [← ChaseBranch.terminates_iff_result_finite]
        apply each_b_term
        exact mem
      . intro each_b_term
        intro b mem
        rw [ChaseBranch.terminates_iff_result_finite]
        apply each_b_term
        exists b

  end ChaseTree

end GeneralResults

