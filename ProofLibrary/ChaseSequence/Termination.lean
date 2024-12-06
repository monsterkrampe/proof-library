import ProofLibrary.ChaseSequence.Basic

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

end GeneralResults

