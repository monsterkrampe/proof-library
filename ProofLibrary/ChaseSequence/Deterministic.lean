import ProofLibrary.ChaseSequence.Basic
import ProofLibrary.ChaseSequence.Universality

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

-- TODO: split up the proofs to get rid of this
set_option maxHeartbeats 1000000

def ChaseTree.firstResult (ct : ChaseTree obs kb) : FactSet sig := fun f => ∃ n, (ct.tree.get (List.repeat 0 n)).is_some_and (fun node => f ∈ node.fact)

theorem ChaseTree.firstResult_is_in_result (ct : ChaseTree obs kb) : ct.firstResult ∈ ct.result := by
  unfold firstResult
  unfold result
  simp [Set.element]
  let firstBranch : ChaseBranch obs kb := {
    branch := {
      infinite_list := fun n => ct.tree.get (List.repeat 0 n)
      no_holes := by
        simp
        intro n h m
        have no_orphans := ct.tree.tree.no_orphans (List.repeat 0 n) h ⟨List.repeat 0 m, by exists List.repeat 0 (n-m); rw [List.repeat_split n (n-m) m]; simp⟩
        exact no_orphans
    }
    database_first := by simp [List.repeat]; rw [ct.database_first]
    triggers_exist := by
      intro n
      simp
      cases eq : ct.tree.get (List.repeat 0 n) with
      | none => simp [Option.is_none_or]
      | some node =>
        simp [Option.is_none_or]
        have trg_ex := ct.triggers_exist (List.repeat 0 n)
        rw [eq] at trg_ex; simp [Option.is_none_or] at trg_ex
        cases trg_ex with
        | inl trg_ex =>
          apply Or.inl
          unfold exists_trigger_list at trg_ex
          cases trg_ex with | intro trg trg_ex =>
            unfold exists_trigger_list_condition at trg_ex
            unfold exists_trigger_opt_fs
            exists trg
            constructor
            . exact trg_ex.left
            . cases eq2 : trg.val.rule.head.length with
              | zero =>
                have : ct.tree.children (List.repeat 0 n) = [] := by
                  rw [← trg_ex.right]
                  simp
                  unfold PreTrigger.result
                  rw [← List.isEmpty_eq_true, List.isEmpty_iff_length_eq_zero]
                  rw [List.enum_with_lt_length_eq]
                  simp
                  rw [← List.isEmpty_eq_true, List.isEmpty_iff_length_eq_zero]
                  rw [← trg.val.head_length_eq_mapped_head_length]
                  exact eq2
                have : node ∈ ct.tree.leaves := by
                  unfold FiniteDegreeTree.leaves
                  unfold PossiblyInfiniteTree.leaves
                  simp [Set.element]
                  exists (List.repeat 0 n)
                  constructor
                  . exact eq
                  . rw [← ct.tree.children_eq_lifted_children, this]; rfl
                have not_active : ¬ trg.val.active node.fact := by apply ct.fairness_leaves; exact this
                have active : trg.val.active node.fact := trg_ex.left
                contradiction
              | succ _ =>
                have length_aux_1 : 0 < trg.val.result.length := by
                  unfold PreTrigger.result
                  simp
                  rw [← trg.val.head_length_eq_mapped_head_length]
                  rw [eq2]
                  simp
                have length_aux_2 : 0 < (ct.tree.children (List.repeat 0 n)).length := by
                  rw [← trg_ex.right]
                  simp [List.enum_with_lt_length_eq]
                  exact length_aux_1
                exists ⟨0, length_aux_1⟩
                unfold List.repeat
                rw [← ct.tree.getElem_children_eq_get_tree (List.repeat 0 n) ⟨0, length_aux_2⟩]
                simp
                simp only [← trg_ex.right]
                simp
                rw [List.enum_with_lt_getElem_snd_eq_getElem]
                rw [List.enum_with_lt_getElem_fst_eq_index]
                constructor
                . rfl
                . rfl
        | inr trg_ex =>
          apply Or.inr
          unfold not_exists_trigger_opt_fs
          unfold not_exists_trigger_list at trg_ex
          constructor
          . exact trg_ex.left
          unfold List.repeat
          apply ct.tree.children_empty_means_all_following_none
          exact trg_ex.right
    fairness := by
      intro trg
      cases Classical.em (∃ n : Nat, ct.tree.get (List.repeat 0 n) ≠ none ∧ ∀ m : Nat, m > n -> ct.tree.get (List.repeat 0 m) = none) with
      | inl h =>
        cases h with | intro n hn =>
          exists n
          cases eq : ct.tree.get (List.repeat 0 n) with
          | none => rw [eq] at hn; simp at hn
          | some node =>
            simp
            rw [eq]
            simp [Option.is_some_and]
            constructor
            . apply ct.fairness_leaves
              unfold FiniteDegreeTree.leaves
              unfold PossiblyInfiniteTree.leaves
              simp only [Set.element]
              exists (List.repeat 0 n)
              constructor
              . simp only [FiniteDegreeTree.get] at eq; exact eq
              . unfold PossiblyInfiniteList.empty
                unfold PossiblyInfiniteTree.children
                unfold InfiniteTreeSkeleton.children
                simp
                apply funext
                have next_none := hn.right (n+1) (by simp)
                unfold List.repeat at next_none
                have children_empty := ct.tree.first_child_none_means_children_empty (List.repeat 0 n) next_none
                have all_none := ct.tree.children_empty_means_all_following_none _ children_empty
                unfold FiniteDegreeTree.get at all_none
                unfold PossiblyInfiniteTree.get at all_none
                exact all_none
            . intro m hm
              have m_eq := hn.right m hm
              rw [m_eq]
              simp [Option.is_none_or]
      | inr h =>
        have h : ¬ ∃ n : Nat, ct.tree.get (List.repeat 0 n) = none := by
          simp at h
          simp
          intro n
          induction n with
          | zero => simp [List.repeat]; rw [ct.database_first]; simp
          | succ n ih =>
            specialize h n ih
            cases h with | intro m hm =>
              intro contra
              have : n + 1 ≤ m := by apply Nat.succ_le_of_lt; exact hm.left
              have no_orphans := ct.tree.tree.no_orphans (List.repeat 0 m) hm.right ⟨(List.repeat 0 (n+1)), by
                exists (List.repeat 0 (m - (n + 1)))
                rw [← List.repeat_split]
                rw [← (Nat.sub_add_comm this)]
                simp
              ⟩
              unfold FiniteDegreeTree.get at contra
              unfold PossiblyInfiniteTree.get at contra
              contradiction
        cases ct.fairness_infinite_branches trg with | intro i hi =>
          exists i
          cases eq : ct.tree.get (List.repeat 0 i) with
          | none => apply False.elim; apply h; exists i
          | some node =>
            constructor
            . simp; rw[eq]; simp [Option.is_some_and]
              specialize hi (List.repeat 0 i) (by rw [List.length_repeat]; simp)
              rw [eq] at hi
              simp [Option.is_none_or] at hi
              exact hi
            . intro j hj
              specialize hi (List.repeat 0 j) (by rw [List.length_repeat]; apply Nat.le_of_lt; exact hj)
              simp
              exact hi
  }
  exists firstBranch
  constructor
  . unfold ChaseTree.branches
    unfold FiniteDegreeTree.branches
    unfold PossiblyInfiniteTree.branches
    unfold InfiniteTreeSkeleton.branches
    unfold InfiniteTreeSkeleton.branches_through
    simp [firstBranch, Set.element]
    let nodes : InfiniteList Nat := fun _ => 0
    exists nodes
    constructor
    . intro n
      unfold FiniteDegreeTree.get
      unfold PossiblyInfiniteTree.get
      have : List.repeat 0 n = (nodes.take n).reverse := by
        simp only [nodes]
        induction n with
        | zero => simp [List.repeat, InfiniteList.take]
        | succ n ih =>
          unfold List.repeat
          unfold InfiniteList.take
          simp
          exact ih
      rw [this]
    . rfl
  . unfold ChaseBranch.result
    rfl

theorem ChaseTree.firstResult_is_result_when_deterministic (ct : ChaseTree obs kb) : kb.isDeterministic -> ct.result = fun fs => fs = ct.firstResult := by
  intro h_deterministic
  unfold ChaseTree.result
  apply funext
  intro fs
  simp
  constructor
  . intro h
    cases h with | intro branch h =>
      rw [← h.right]
      have branch_in_ct := h.left
      unfold ChaseTree.branches at branch_in_ct
      unfold FiniteDegreeTree.branches at branch_in_ct
      unfold PossiblyInfiniteTree.branches at branch_in_ct
      unfold InfiniteTreeSkeleton.branches at branch_in_ct
      simp only [Set.element] at branch_in_ct
      cases branch_in_ct with | intro nodes branch_in_ct =>
        have : ∀ n, (branch.branch.infinite_list (n+1)).is_none_or (fun _ => nodes n = 0) := by
          intro n
          cases eq : branch.branch.infinite_list (n+1) with
          | none => simp [Option.is_none_or]
          | some node =>
            have trg_ex := ct.triggers_exist (nodes.take n).reverse
            simp [Option.is_none_or]
            have n_succ_in_ct := branch_in_ct.left (n+1)
            rw [eq] at n_succ_in_ct
            unfold FiniteDegreeTree.get at trg_ex
            unfold PossiblyInfiniteTree.get at trg_ex
            rw [← branch_in_ct.left] at trg_ex
            cases eq_prev : branch.branch.infinite_list n with
            | none =>
              have no_holes := branch.branch.no_holes (n+1) (by rw [eq]; simp) ⟨n, by simp⟩
              rw [eq_prev] at no_holes
              contradiction
            | some prev_node =>
              rw [eq_prev] at trg_ex
              simp [Option.is_none_or] at trg_ex
              cases trg_ex with
              | inl trg_ex =>
                unfold exists_trigger_list at trg_ex
                unfold exists_trigger_list_condition at trg_ex
                cases trg_ex with | intro trg h_trg =>
                  unfold InfiniteList.take at n_succ_in_ct
                  simp at n_succ_in_ct
                  have children_get_eq := ct.tree.tree.getElem_children_eq_get_tree (nodes.take n).reverse (nodes n)
                  unfold PossiblyInfiniteTree.get at children_get_eq
                  rw [← children_get_eq] at n_succ_in_ct
                  rw [← FiniteDegreeTree.children_eq_lifted_children] at n_succ_in_ct
                  rw [← h_trg.right] at n_succ_in_ct
                  rw [PossiblyInfiniteList.get_fromList_eq_list_getElem] at n_succ_in_ct
                  have n_succ_in_ct := Eq.symm n_succ_in_ct
                  rw [List.getElem?_eq_some_iff] at n_succ_in_ct
                  cases n_succ_in_ct with | intro isLt n_succ_in_ct =>
                    simp [List.enum_with_lt_length_eq] at isLt
                    unfold PreTrigger.result at isLt
                    simp at isLt
                    rw [← PreTrigger.head_length_eq_mapped_head_length] at isLt
                    unfold KnowledgeBase.isDeterministic at h_deterministic
                    unfold RuleSet.isDeterministic at h_deterministic
                    rw [h_deterministic _ trg.property] at isLt
                    rw [Nat.lt_succ] at isLt
                    simp at isLt
                    exact isLt
              | inr trg_ex =>
                unfold not_exists_trigger_list at trg_ex
                have contra := ct.tree.children_empty_means_all_following_none (nodes.take n).reverse trg_ex.right (nodes n)
                have branch_in_ct := branch_in_ct.left (n+1)
                unfold InfiniteList.take at branch_in_ct
                simp at branch_in_ct
                unfold FiniteDegreeTree.get at contra
                unfold PossiblyInfiniteTree.get at contra
                rw [contra] at branch_in_ct
                rw [eq] at branch_in_ct
                contradiction
        have : ∀ n, (branch.branch.infinite_list n).is_none_or (fun _ => (nodes.take n).reverse = List.repeat 0 n) := by
          intro n
          cases eq : branch.branch.infinite_list n with
          | none => simp [Option.is_none_or]
          | some val =>
            simp [Option.is_none_or]
            induction n generalizing val with
            | zero => unfold List.repeat; unfold InfiniteList.take; simp
            | succ n ih =>
              unfold List.repeat
              unfold InfiniteList.take
              simp
              constructor
              . specialize this n
                rw [eq] at this
                simp [Option.is_none_or] at this
                exact this
              . have no_holes := branch.branch.no_holes (n+1)
                rw [eq] at no_holes
                simp at no_holes
                specialize no_holes ⟨n, by simp⟩
                simp only [Option.ne_none_iff_exists] at no_holes
                cases no_holes with | intro prev_node no_holes =>
                  apply ih prev_node
                  rw [no_holes]
        have nodes_none_means_first_branch_none : ∀ n, ct.tree.get (nodes.take n).reverse = none -> ct.tree.get (List.repeat 0 n) = none := by
          intro n
          induction n with
          | zero => unfold InfiniteList.take; unfold List.repeat; simp
          | succ n ih =>
            intro h
            cases eq : ct.tree.get (nodes.take n).reverse with
            | none =>
              specialize ih eq
              apply Option.decidable_eq_none.byContradiction
              intro contra
              have no_orphans := ct.tree.tree.no_orphans (List.repeat 0 (n+1)) contra ⟨(List.repeat 0 n), by exists [0]⟩
              contradiction
            | some node =>
              have eq' := eq
              unfold FiniteDegreeTree.get at eq
              unfold PossiblyInfiniteTree.get at eq
              rw [← branch_in_ct.left] at eq
              specialize this n
              rw [eq] at this; simp [Option.is_none_or] at this
              rw [this] at eq'
              have trg_ex := branch.triggers_exist n
              rw [eq] at trg_ex; simp [Option.is_none_or] at trg_ex
              cases trg_ex with
              | inl trg_ex =>
                unfold exists_trigger_opt_fs at trg_ex
                cases trg_ex with | intro _ trg_ex => cases trg_ex.right with | intro _ trg_ex =>
                  unfold FiniteDegreeTree.get at h
                  unfold PossiblyInfiniteTree.get at h
                  rw [← branch_in_ct.left] at h
                  rw [h] at trg_ex
                  contradiction
              | inr trg_ex =>
                unfold not_exists_trigger_opt_fs at trg_ex
                have trg_ex' := ct.triggers_exist (List.repeat 0 n)
                rw [eq'] at trg_ex'; simp [Option.is_none_or] at trg_ex'
                cases trg_ex' with
                | inl trg_ex' =>
                  unfold exists_trigger_list at trg_ex'
                  unfold exists_trigger_list_condition at trg_ex'
                  cases trg_ex' with | intro trg' trg_ex' =>
                    apply False.elim
                    apply trg_ex.left
                    exists trg'
                    exact trg_ex'.left
                | inr trg_ex' =>
                  unfold not_exists_trigger_list at trg_ex'
                  apply FiniteDegreeTree.children_empty_means_all_following_none
                  exact trg_ex'.right
        apply funext
        intro f
        unfold ChaseBranch.result
        unfold ChaseTree.firstResult
        simp
        constructor
        . intro h; cases h with | intro n h =>
          exists n
          cases eq : branch.branch.infinite_list n with
          | none => rw [eq] at h; simp [Option.is_some_and] at h
          | some node =>
            specialize this n
            rw [eq] at this
            simp [Option.is_none_or] at this
            rw [← this]
            unfold FiniteDegreeTree.get; unfold PossiblyInfiniteTree.get; rw [← branch_in_ct.left]; exact h
        . intro h; cases h with | intro n h =>
          exists n
          rw [branch_in_ct.left]
          cases eq : branch.branch.infinite_list n with
          | none =>
            rw [nodes_none_means_first_branch_none n (by
              unfold FiniteDegreeTree.get
              unfold PossiblyInfiniteTree.get
              rw [← branch_in_ct.left]
              exact eq
            )] at h
            simp [Option.is_some_and] at h
          | some node =>
            specialize this n
            rw [eq] at this
            simp [Option.is_none_or] at this
            rw [this]
            exact h
  . intro h
    have firstResult_is_in_result := ct.firstResult_is_in_result
    unfold ChaseTree.result at firstResult_is_in_result
    simp [Set.element] at firstResult_is_in_result
    rw [h]
    exact firstResult_is_in_result

theorem deterministicChaseTreeResultUniversallyModelsKb (ct : ChaseTree obs kb) : kb.isDeterministic -> ct.firstResult.universallyModelsKb kb := by
  intro h
  unfold FactSet.universallyModelsKb
  constructor
  . apply chaseTreeResultModelsKb; apply ct.firstResult_is_in_result
  . intro m m_is_model
    cases chaseTreeResultIsUniversal ct m m_is_model with | intro fs h' =>
      cases h' with | intro hom h' =>
        rw [ct.firstResult_is_result_when_deterministic h] at h'
        simp [Set.element] at h'
        exists hom
        rw [← h'.left]
        exact h'.right

def ChaseBranch.intoTree (cb : ChaseBranch obs kb) (deterministic : kb.isDeterministic) : ChaseTree obs kb :=
  {
    tree := {
      tree := {
        infinite_tree := fun l => if l.all (fun e => e = 0) then cb.branch.infinite_list l.length else none
        no_orphans := by
          intro l
          cases eq : l.all (fun e => e = 0) with
          | false => simp [eq]
          | true =>
            simp only [eq]
            intro not_none
            intro parent
            rcases parent.property with ⟨diff, l_eq⟩
            have : parent.val.all (fun e => e = 0) := by
              rw [← l_eq] at eq
              rw [List.all_append] at eq
              rw [Bool.and_eq_true] at eq
              exact eq.right
            simp [this]
            cases diff with
            | nil => simp at l_eq; rw [l_eq]; apply not_none
            | cons _ _ =>
              let parent_len_fin : Fin l.length := ⟨parent.val.length, by simp [← l_eq]; apply Nat.lt_add_one_of_le; simp⟩
              have := cb.branch.no_holes l.length not_none parent_len_fin
              exact this
        no_holes_in_children := by
          intro l n
          unfold InfiniteTreeSkeleton.children
          cases n with
          | succ n =>
            have all_eq_false : ((n+1)::l).all (fun e => e = 0) = false := by rw [List.all_eq_false]; exists n+1; simp
            simp [all_eq_false]
          | zero =>
            intro _ m
            have isLt := m.isLt
            simp at isLt
      }
      finitely_many_children := by
        intro l
        cases eq : cb.branch.infinite_list (l.length + 1) with
        | none =>
          exists 0
          rw [PossiblyInfiniteTree.getElem_children_eq_get_tree]
          unfold PossiblyInfiniteTree.get
          cases eq2 : l.all (fun e => e = 0) with
          | false => simp [eq2, eq]; intro k; have isLt := k.isLt; simp at isLt
          | true => simp [eq2, eq]; intro k; have isLt := k.isLt; simp at isLt
        | some _ =>
          cases eq2 : l.all (fun e => e = 0) with
          | false =>
            exists 0
            rw [PossiblyInfiniteTree.getElem_children_eq_get_tree]
            unfold PossiblyInfiniteTree.get
            simp [eq2]
            intro k; have isLt := k.isLt; simp at isLt
          | true =>
            exists 1
            rw [PossiblyInfiniteTree.getElem_children_eq_get_tree]
            unfold PossiblyInfiniteTree.get
            simp
            rw [PossiblyInfiniteTree.getElem_children_eq_get_tree]
            unfold PossiblyInfiniteTree.get
            simp
            constructor
            . simp at eq2; apply eq2
            . rw [eq]; simp
    }
    database_first := by
      simp only [FiniteDegreeTree.get, PossiblyInfiniteTree.get]
      exact cb.database_first
    triggers_exist := by
      simp only [FiniteDegreeTree.get, PossiblyInfiniteTree.get]
      intro l
      cases eq : l.all (fun e => e = 0) with
      | false => simp [Option.is_none_or]
      | true =>
        simp only [reduceIte]
        have cb_trgs := cb.triggers_exist l.length
        cases eq2 : cb.branch.infinite_list l.length with
        | none => simp [Option.is_none_or]
        | some node =>
          simp only [Option.is_none_or]
          rw [eq2] at cb_trgs
          simp only [Option.is_none_or] at cb_trgs
          cases cb_trgs with
          | inl cb_trgs =>
            apply Or.inl
            unfold exists_trigger_opt_fs at cb_trgs
            unfold exists_trigger_list
            unfold exists_trigger_list_condition
            rcases cb_trgs with ⟨trg, trg_active, trg_result⟩
            exists trg
            constructor
            . exact trg_active
            . rcases trg_result with ⟨i, trg_result⟩
              have res_length : trg.val.result.length = 1 := by
                unfold PreTrigger.result; simp; rw [← PreTrigger.head_length_eq_mapped_head_length]; apply deterministic; exact trg.property
              have i_eq : i = (⟨0, by simp [res_length]⟩ : Fin trg.val.result.length) := by
                cases eq : i.val with
                | zero => ext; rw [eq]
                | succ _ =>
                  have isLt := i.isLt
                  rw [eq, res_length] at isLt
                  simp at isLt
              rw [List.map_eq_iff]
              intro j
              cases j with
              | zero =>
                rw [FiniteDegreeTree.getElem_children_eq_getElem_tree_children]
                rw [PossiblyInfiniteTree.getElem_children_eq_get_tree]
                unfold PossiblyInfiniteTree.get
                rw [List.getElem?_eq_getElem (by simp [List.enum_with_lt_length_eq]; rw [res_length]; simp)]
                have : (0::l).all (fun e => e = 0) = true := by
                  rw [List.all_cons]
                  rw [eq]
                  simp
                conv => left; simp [this]
                rw [← trg_result]
                simp
                rw [List.enum_with_lt_getElem_fst_eq_index, List.enum_with_lt_getElem_snd_eq_getElem]
                rw [i_eq]
                simp
                . rw [res_length]; simp
                . rw [res_length]; simp
              | succ j =>
                rw [FiniteDegreeTree.getElem_children_eq_getElem_tree_children]
                rw [PossiblyInfiniteTree.getElem_children_eq_get_tree]
                unfold PossiblyInfiniteTree.get
                rw [List.getElem?_eq_none]
                . simp
                . simp [List.enum_with_lt_length_eq, res_length]
          | inr cb_trgs =>
            apply Or.inr
            unfold not_exists_trigger_opt_fs at cb_trgs
            unfold not_exists_trigger_list
            constructor
            . exact cb_trgs.left
            . apply FiniteDegreeTree.first_child_none_means_children_empty
              unfold FiniteDegreeTree.get
              unfold PossiblyInfiniteTree.get
              have : (0::l).all (fun e => e = 0) = true := by
                rw [List.all_cons]
                rw [eq]
                simp
              simp [this]
              exact cb_trgs.right
    fairness_leaves := by
      intro leaf leaf_mem
      unfold FiniteDegreeTree.leaves at leaf_mem
      unfold PossiblyInfiniteTree.leaves at leaf_mem
      unfold PossiblyInfiniteTree.get at leaf_mem
      rcases leaf_mem with ⟨node, node_eq, node_children⟩
      have all_none := PossiblyInfiniteTree.children_empty_means_all_following_none _ _ node_children
      cases eq : node.all (fun e => e = 0) with
      | false => simp [eq] at node_eq
      | true =>
        simp [eq] at node_eq
        have : (0::node).all (fun e => e = 0) = true := by
          rw [List.all_cons]
          rw [eq]
          simp
        specialize all_none 0
        unfold PossiblyInfiniteTree.get at all_none
        simp [this] at all_none

        intro trg
        have fair := cb.fairness trg
        rcases fair with ⟨i, fair⟩
        have : i ≤ node.length := by
          cases Decidable.em (i ≤ node.length) with
          | inl le => exact le
          | inr n_le =>
            simp at n_le
            -- all cases should result in contradictions
            cases eq2 : i - node.length with
            | zero =>
              rw [Nat.sub_eq_iff_eq_add (by apply Nat.le_of_lt; exact n_le)] at eq2
              rw [eq2] at n_le
              simp at n_le
            | succ j =>
              rw [Nat.sub_eq_iff_eq_add (by apply Nat.le_of_lt; exact n_le)] at eq2
              cases j with
              | zero =>
                cases eq3 : cb.branch.infinite_list i with
                | none => rw [eq3] at fair; simp [Option.is_some_and] at fair
                | some _ =>
                  rw [eq2] at eq3
                  simp at eq3
                  rw [Nat.add_comm] at eq3
                  rw [all_none] at eq3
                  simp at eq3
              | succ _ =>
                cases eq3 : cb.branch.infinite_list i with
                | none => rw [eq3] at fair; simp [Option.is_some_and] at fair
                | some _ =>
                  have no_holes := cb.branch.no_holes i (by simp [eq3]) ⟨
                    node.length + 1,
                    by
                      rw [eq2]
                      conv => right; rw [Nat.add_assoc, Nat.add_assoc]
                      apply Nat.lt_add_left
                      rw [← Nat.add_assoc, Nat.add_comm]
                      simp
                  ⟩
                  rw [all_none] at no_holes
                  simp at no_holes
        cases Nat.lt_or_eq_of_le this with
        | inr eq =>
          have fair_left := fair.left
          rw [eq, node_eq] at fair_left
          simp [Option.is_some_and] at fair_left
          exact fair_left
        | inl lt =>
          have fair_right := fair.right node.length lt
          rw [node_eq] at fair_right
          simp [Option.is_none_or] at fair_right
          exact fair_right
    fairness_infinite_branches := by
      intro trg
      have fair := cb.fairness trg
      rcases fair with ⟨i, fair⟩
      exists i + 1
      intro node node_length_ge
      unfold FiniteDegreeTree.get
      unfold PossiblyInfiniteTree.get
      cases eq : node.all (fun e => e = 0) with
      | false => simp [eq, Option.is_none_or]
      | true =>
        simp [eq]
        apply fair.right
        apply Nat.lt_of_succ_le
        exact node_length_ge
  }

theorem ChaseBranch.intoTree_same_result (cb : ChaseBranch obs kb) (deterministic : kb.isDeterministic) : (cb.intoTree deterministic).firstResult = cb.result := by
  unfold ChaseBranch.intoTree
  unfold ChaseBranch.result
  unfold ChaseTree.firstResult
  apply funext
  intro f
  rw [eq_iff_iff]
  simp only [FiniteDegreeTree.get, PossiblyInfiniteTree.get]
  constructor
  . intro h
    rcases h with ⟨n, h⟩
    rw [List.all_eq_val_repeat 0, List.length_repeat] at h
    simp at h
    exists n
  . intro h
    rcases h with ⟨n, h⟩
    exists n
    rw [List.all_eq_val_repeat 0, List.length_repeat]
    simp
    exact h

theorem deterministicChaseBranchResultUniversallyModelsKb (cb : ChaseBranch obs kb) : kb.isDeterministic -> cb.result.universallyModelsKb kb := by
  intro deterministic
  rw [← cb.intoTree_same_result deterministic]
  apply deterministicChaseTreeResultUniversallyModelsKb
  exact deterministic

