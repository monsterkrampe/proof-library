import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.Trigger
import ProofLibrary.Logic
import ProofLibrary.PossiblyInfiniteTree

structure ChaseNode (obs : ObsoletenessCondition) (rules : RuleSet) where
  fact : FactSet
  -- the origin if none only for the database
  origin : Option ((trg : RTrigger obs rules) × Fin trg.val.result.length)

def exists_trigger_opt_fs (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger obs rules), trg.val.active before.fact ∧ ∃ i, some { fact := before.fact ∪ trg.val.result.get i, origin := some ⟨trg, i⟩ } = after

def exists_trigger_list (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger obs rules), trg.val.active before.fact ∧ trg.val.result.enum_with_lt.map (fun ⟨i, fs⟩ => { fact := before.fact ∪ fs, origin := some ⟨trg, i⟩ }) = after

def not_exists_trigger_opt_fs (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.fact) ∧ after = none

def not_exists_trigger_list (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.fact) ∧ after = []

structure ChaseBranch (obs : ObsoletenessCondition) (kb : KnowledgeBase) where
  branch : PossiblyInfiniteList (ChaseNode obs kb.rules)
  database_first : branch.infinite_list 0 = some { fact := kb.db.toFactSet, origin := none }
  triggers_exist : ∀ n : Nat, (branch.infinite_list n).is_none_or (fun before =>
    let after := branch.infinite_list (n+1)
    (exists_trigger_opt_fs obs kb.rules before after) ∨
    (not_exists_trigger_opt_fs obs kb.rules before after))
  fairness : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ((branch.infinite_list i).is_some_and (fun fs => ¬ trg.val.active fs.fact))
    ∧ (∀ j : Nat, j > i -> (branch.infinite_list j).is_none_or (fun fs => ¬ trg.val.active fs.fact))

namespace ChaseBranch
  def result (branch : ChaseBranch obs kb) : FactSet :=
    fun f => ∃ n : Nat, (branch.branch.infinite_list n).is_some_and (fun fs => f ∈ fs.fact)

  def terminates (branch : ChaseBranch obs kb) : Prop :=
    ∃ n : Nat, branch.branch.infinite_list n = none
end ChaseBranch

structure ChaseTree (obs : ObsoletenessCondition) (kb : KnowledgeBase) where
  tree : FiniteDegreeTree (ChaseNode obs kb.rules)
  database_first : tree.get [] = some { fact := kb.db.toFactSet, origin := none }
  triggers_exist : ∀ node : List Nat, (tree.get node).is_none_or (fun before =>
    let after := tree.children node
    (exists_trigger_list obs kb.rules before after) ∨
    (not_exists_trigger_list obs kb.rules before after))

  fairness_leaves : ∀ leaf, leaf ∈ tree.leaves -> ∀ trg : (RTrigger obs kb.rules), ¬ trg.val.active leaf.fact
  fairness_infinite_branches : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ∀ node : List Nat, node.length ≥ i ->
    (tree.get node).is_none_or (fun fs => ¬ trg.val.active fs.fact)

namespace ChaseTree
  -- NOTE: this does not work; the address might not be valid in the sense that a number might be bigger than the number of disjuncts in a rule head, which leads to malformed branches that are no valid ChaseBranches
  -- def branch_for (ct : ChaseTree obs kb) (address : InfiniteList Nat) : ChaseBranch obs kb := {
  --   branch := ct.tree.branch_for address
  --   database_first := by
  --     rw [← ct.database_first]
  --     unfold FiniteDegreeTree.branch_for
  --     unfold PossiblyInfiniteTree.branch_for
  --     unfold InfiniteTreeSkeleton.branch_for
  --     simp
  --     unfold FiniteDegreeTree.get
  --     unfold PossiblyInfiniteTree.get
  --     unfold InfiniteList.take
  --     rfl
  --   triggers_exist := by sorry
  --   fairness := by sorry
  -- }

  def branches (ct : ChaseTree obs kb) : Set (ChaseBranch obs kb) := fun branch => branch.branch ∈ ct.tree.branches

  def result (ct : ChaseTree obs kb) : Set FactSet := fun fs => ∃ branch, branch ∈ ct.branches ∧ branch.result = fs

  def terminates (ct : ChaseTree obs kb) : Prop := ∀ branch, branch ∈ ct.branches -> branch.terminates
end ChaseTree


theorem chaseBranchSetIsSubsetOfNext (cb : ChaseBranch obs kb) : ∀ n : Nat,
  match cb.branch.infinite_list n with
  | .none => cb.branch.infinite_list (n+1) = none
  | .some fs => (cb.branch.infinite_list (n+1)).is_none_or (fun fs2 => fs.fact ⊆ fs2.fact) :=
by
  intro n
  cases eq : cb.branch.infinite_list n with
  | none =>
    simp
    have dec : Decidable (cb.branch.infinite_list (n+1) = none) := Option.decidable_eq_none
    apply dec.byContradiction
    intro contra
    let n' : Fin (n+1) := ⟨n, by simp⟩
    have : ¬ cb.branch.infinite_list n' = none := by apply cb.branch.no_holes; apply contra
    contradiction
  | some fs =>
    simp
    cases eq2 : cb.branch.infinite_list (n+1) with
    | none => simp [Option.is_none_or]
    | some fs2 =>
      simp [Option.is_none_or]
      intro f h
      have trg_ex_n := cb.triggers_exist n
      simp [eq, Option.is_none_or] at trg_ex_n
      cases trg_ex_n with
      | inl g =>
        cases g with | intro trg h_trg =>
          cases h_trg.right with | intro i h_i =>
            rw [eq2] at h_i
            injection h_i with h_i
            rw [← h_i]
            simp [Set.element, Set.union]
            apply Or.inl
            exact h
      | inr g =>
        have g_right := g.right
        rw [eq2] at g_right
        contradiction

theorem chaseTreeSetIsSubsetOfEachNext (ct : ChaseTree obs kb) : ∀ address : List Nat,
  match ct.tree.get address with
  | .none => ct.tree.children address = []
  | .some fs => ∀ fs2, fs2 ∈ ct.tree.children address -> fs.fact ⊆ fs2.fact :=
by
  intro address
  cases eq : ct.tree.get address with
  | none => simp; apply FiniteDegreeTree.children_empty_when_not_existing; exact eq
  | some fs =>
    simp
    intro fs2 h
    have trg_ex_addr := ct.triggers_exist address
    simp [eq, Option.is_none_or] at trg_ex_addr
    cases trg_ex_addr with
    | inl g =>
      cases g with | intro trg h_trg =>
        rw [← h_trg.right] at h
        rw [List.mem_map] at h
        cases h with | intro head h_head =>
          rw [← h_head.right]
          intro f h
          apply Or.inl
          exact h
    | inr g =>
      rw [g.right] at h
      contradiction

theorem chaseBranchSetIsSubsetOfAllFollowing (cb : ChaseBranch obs kb) : ∀ (n m : Nat),
  match cb.branch.infinite_list n with
  | .none => cb.branch.infinite_list (n+m) = none
  | .some fs => (cb.branch.infinite_list (n+m)).is_none_or (fun fs2 => fs.fact ⊆ fs2.fact) :=
by
  intro n m
  induction m with
  | zero =>
    cases eq : cb.branch.infinite_list n with
    | none => simp; exact eq
    | some fs => simp [Option.is_none_or, eq, Set.subset]
  | succ m ih =>
    cases eq : cb.branch.infinite_list n with
    | none =>
      simp
      simp [eq] at ih
      have step := chaseBranchSetIsSubsetOfNext cb (n+m)
      simp [ih] at step
      exact step
    | some fs =>
      simp
      simp [eq, Option.is_none_or] at ih
      have step := chaseBranchSetIsSubsetOfNext cb (n+m)
      cases eq2 : cb.branch.infinite_list (n+m) with
      | none => simp [eq2] at step; rw [← Nat.add_assoc, step, Option.is_none_or]; simp
      | some fs2 =>
        simp [eq2] at step; simp [eq2] at ih; rw [← Nat.add_assoc]
        cases eq3 : cb.branch.infinite_list (n+m+1) with
        | none => simp [Option.is_none_or]
        | some fs3 =>
          simp [Option.is_none_or]; simp [eq3, Option.is_none_or] at step;
          apply Set.subsetTransitive; constructor; apply ih; apply step

theorem chaseTreeSetIsSubsetOfAllFollowing (ct : ChaseTree obs kb) : ∀ (n m : List Nat),
  match ct.tree.get n with
  | .none => ct.tree.get (m ++ n) = none
  | .some fs => (ct.tree.get (m ++ n)).is_none_or (fun fs2 => fs.fact ⊆ fs2.fact) :=
by
  intro n m
  induction m with
  | nil =>
    cases eq : ct.tree.get n with
    | none => simp; exact eq
    | some fs => simp [Option.is_none_or, eq, Set.subset]
  | cons i m ih =>
    cases eq : ct.tree.get n with
    | none =>
      simp
      simp [eq] at ih
      have step := chaseTreeSetIsSubsetOfEachNext ct (m ++ n)
      simp [ih] at step
      apply FiniteDegreeTree.children_empty_means_all_following_none
      apply step
    | some fs =>
      simp
      simp [eq, Option.is_none_or] at ih
      have step := chaseTreeSetIsSubsetOfEachNext ct (m ++ n)
      cases eq2 : ct.tree.get (m ++ n) with
      | none =>
        simp [eq2] at step
        unfold Option.is_none_or
        have helper := ct.tree.children_empty_means_all_following_none (m ++ n) step
        rw [helper]
        simp
      | some fs2 =>
        simp [eq2] at step; simp [eq2] at ih
        cases eq3 : ct.tree.get (i :: (m ++ n)) with
        | none => simp [Option.is_none_or]
        | some fs3 =>
          simp [Option.is_none_or]
          apply Set.subsetTransitive
          constructor
          apply ih
          apply step

          rw [ct.tree.in_children_iff_index_exists]
          exists i

theorem chaseBranchSetIsSubsetOfResult (cb : ChaseBranch obs kb) : ∀ n : Nat, (cb.branch.infinite_list n).is_none_or (fun fs => fs.fact ⊆ cb.result) := by
  intro n
  unfold Option.is_none_or

  cases eq : cb.branch.infinite_list n with
  | none => simp
  | some fs =>
    simp
    unfold ChaseBranch.result
    intro f h
    simp [Set.element]
    exists n
    unfold Option.is_some_and
    simp [eq]
    exact h

theorem chaseTreeSetIsSubsetOfResult (ct : ChaseTree obs kb) : ∀ node : List Nat, (ct.tree.get node).is_none_or (fun fs => sorry) := by
  sorry

/-
theorem trgLoadedForChaseResultMeansLoadedAtSomeIndex (cs : ChaseSequence obs kb) : ∀ trg : Trigger obs, trg.loaded cs.result -> ∃ n : Nat, trg.loaded (cs.fact_sets n) := by
  intro trg
  simp [ChaseSequence.result, PreTrigger.loaded]

  induction trg.mapped_body
  case nil =>
    intro _
    exists 0
    intro _ contra
    contradiction
  case cons head tail ih =>
    intro loaded
    have ex_head_n := loaded head
    simp [Set.element, List.toSet, Set.union] at ex_head_n

    have ex_tail_n := by
      apply ih
      simp [List.toSet] at loaded
      have ⟨ _, tailSubs ⟩ := (Set.unionSubsetEachSubset _ _ _).mp loaded
      exact tailSubs
    cases ex_head_n with | intro i hi =>
      cases ex_tail_n with | intro j hj =>
        exists Nat.max i j
        simp [List.toSet]
        rw [Set.unionSubsetEachSubset]

        have max_help_left : ∀ a b : Nat, a ≤ Nat.max a b := by
          intro a b
          simp [Nat.max_def]
          cases Decidable.em (a ≤ b)
          case inl h => simp [h]
          case inr h => simp [h]
        have max_help_right : ∀ a b : Nat, b ≤ Nat.max a b := by
          intro a b
          simp [Nat.max_def]
          split -- seems to be the same as the following above: cases Decidable.em (a ≤ b)
          case isTrue h => simp [h]
          case isFalse h => apply Nat.le_of_lt; apply Nat.lt_of_succ_le; rw [← Nat.not_le_eq]; exact h
        have help_i : i ≤ Nat.max i j := by apply max_help_left
        have help_j : j ≤ Nat.max i j := by apply max_help_right

        constructor
        apply Set.subsetTransitive _ (cs.fact_sets i) _
        constructor
        intro e he
        simp [Set.element] at he
        rw [he]
        assumption
        cases Nat.le.dest help_i with | intro m hm => rw [← hm]; apply chaseSequenceSetIsSubsetOfAllFollowing cs i m
        cases Nat.le.dest help_j with | intro m hm =>
          rw [← hm]
          apply Set.subsetTransitive
          constructor
          apply hj
          apply chaseSequenceSetIsSubsetOfAllFollowing cs j m

theorem trgActiveForChaseResultMeansActiveAtSomeIndex (cs : ChaseSequence obs kb) : ∀ trg : Trigger obs, trg.active cs.result -> ∃ n : Nat, trg.active (cs.fact_sets n) := by
  intro trg
  simp [ChaseSequence.result, Trigger.active]
  intro loaded active
  have trgLoadedForN := trgLoadedForChaseResultMeansLoadedAtSomeIndex cs trg loaded
  cases trgLoadedForN with | intro n loadedN =>
    exists n
    constructor
    exact loadedN
    intro contra
    apply active
    apply obs.monotone
    apply chaseSequenceSetIsSubsetOfResult cs n
    apply contra

theorem funcTermForExisVarInChaseMeansTriggerIsUsed (cs : ChaseSequence obs kb) (trg : RTrigger obs kb.rules) (var : Variable) (i : Nat) : (¬ var ∈ trg.val.rule.frontier) ∧ (∃ f: Fact, f ∈ cs.fact_sets i ∧ ((trg.val.apply_to_var_or_const (VarOrConst.var var)) ∈ f.terms.toSet)) -> ∃ j, j ≤ i ∧ trg.val.result ∪ cs.fact_sets (j-1) = cs.fact_sets j := by
  intro ⟨var_not_in_frontier, exis_f⟩
  induction i with
  | zero =>
    cases exis_f with | intro f hf =>
      let ⟨f_in_db, functional_term_in_f⟩ := hf
      rw [cs.database_first] at f_in_db
      have : ∀ t, t ≠ GroundSubstitution.apply_skolem_term trg.val.subs (VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule) (VarOrConst.var var)) := by
        intro t
        unfold Database.toFactSet at f_in_db
        unfold Fact.toFunctionFreeFact at f_in_db
        simp only [Set.element] at f_in_db
        split at f_in_db
        case h_1 => contradiction
        case h_2 _ _ to_fff_is_some =>
          split at to_fff_is_some
          case isFalse h => contradiction
          case isTrue _ _ all_terms_ff =>
            have : ¬ (List.all f.terms fun t => match t with
              | GroundTerm.const _ => true
              | _ => false) = true := by
                apply List.neg_all_of_any_neg
                apply List.any_of_exists
                exists GroundSubstitution.apply_skolem_term trg.val.subs (VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule) (VarOrConst.var var))
                constructor
                exact functional_term_in_f
                simp [GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var_not_in_frontier]
            contradiction
      apply False.elim
      apply this
      rfl
  | succ j ih =>
    -- TODO: this should actually be decidable but we need to change the implementation for this
    cases Classical.em (∃ f: Fact, f ∈ cs.fact_sets j ∧ (trg.val.subs.apply_skolem_term (VarOrConst.skolemize trg.val.rule.id trg.val.rule.frontier (VarOrConst.var var))) ∈ f.terms.toSet) with
    | inl f_in_j =>
      cases ih f_in_j with | intro k hk =>
        exists k
        constructor
        apply Nat.le_succ_of_le
        exact hk.left
        exact hk.right
    | inr f_not_in_j =>
      exists j+1
      constructor
      . simp
      . cases cs.triggers_exist j with
        | inr no_trg_ex =>
          have : cs.fact_sets j = cs.fact_sets (j+1) := no_trg_ex.right
          have : ¬ (cs.fact_sets j = cs.fact_sets (j+1)) := by
            cases exis_f with | intro f hf =>
            have : ¬ f ∈ cs.fact_sets j := by
              intro f_in_j
              apply f_not_in_j
              exists f
              constructor
              exact f_in_j
              exact hf.right
            have : f ∈ cs.fact_sets (j + 1) := hf.left
            intro steps_eq
            rw [← steps_eq] at this
            contradiction
          contradiction
        | inl trg_ex => cases trg_ex with | intro trg' h_trg' =>
          have : ∃ f, f ∈ PreTrigger.result trg'.val ∧ (trg.val.apply_to_var_or_const (VarOrConst.var var)) ∈ List.toSet f.terms := by
            cases exis_f with | intro f hf =>
              exists f
              constructor
              . have f_in_next_step := hf.left
                rw [← h_trg'.right] at f_in_next_step
                cases f_in_next_step with
                | inl _ => assumption
                | inr f_in_j =>
                  apply False.elim
                  apply f_not_in_j
                  exists f
                  constructor
                  exact f_in_j
                  exact hf.right
              . exact hf.right

          have : ∃ var2, ¬ var2 ∈ trg'.val.rule.frontier ∧ (trg.val.apply_to_var_or_const (VarOrConst.var var)) = (trg'.val.apply_to_var_or_const (VarOrConst.var var2)) := by
            cases this with | intro f hf =>
              have ⟨f_in_res, apply_var_in_f_terms⟩ := hf
              let i := trg'.val.idx_of_fact_in_result f f_in_res
              let atom_for_f := trg'.val.rule.head.get i

              cases List.inToSetMeansExistsIndex _ _ apply_var_in_f_terms with | intro k hk =>
                have f_is_at_its_idx : f = trg'.val.mapped_head.get ⟨i.val, by simp [PreTrigger.mapped_head]⟩ := by simp [i, PreTrigger.idx_of_fact_in_result]; apply List.idx_of_get

                have atom_arity_same_as_fact : f.terms.length = List.length (FunctionFreeAtom.terms atom_for_f) := by
                  rw [f_is_at_its_idx]
                  unfold PreTrigger.mapped_head
                  unfold PreTrigger.apply_to_function_free_atom
                  simp [atom_for_f]

                let term_for_f := atom_for_f.terms.get ⟨k.val, (by
                  rw [← atom_arity_same_as_fact]
                  exact k.isLt
                )⟩

                -- TODO: this is similar to stuff going on around line 590; check if we can unify
                have : (trg'.val.apply_to_var_or_const term_for_f) = f.terms.get k := by
                  have : f.terms = (trg'.val.apply_to_function_free_atom atom_for_f).terms := by
                    conv => lhs; rw [f_is_at_its_idx]
                    rw [← PreTrigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]
                  rw [List.get_eq_of_eq this]
                  simp [PreTrigger.apply_to_function_free_atom, term_for_f]

                have : (trg.val.apply_to_var_or_const (VarOrConst.var var)) = (trg'.val.apply_to_var_or_const term_for_f) := by
                  rw [← this] at hk
                  exact hk

                cases eq_term_for_f : term_for_f with
                | const c =>
                  rw [eq_term_for_f] at this
                  simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var_not_in_frontier] at this
                  contradiction
                | var var_for_f =>
                  exists var_for_f
                  have var_for_f_not_in_frontier : ¬ var_for_f ∈ trg'.val.rule.frontier := by
                    apply Decidable.byContradiction
                    intro h
                    simp at h
                    rw [eq_term_for_f] at this

                    apply f_not_in_j
                    have var_for_f_occurs_in_body_atom := trg'.val.rule.frontier_var_occurs_in_fact_in_body var_for_f h
                    cases var_for_f_occurs_in_body_atom with | intro body_atom_for_f h_body_atom_for_f =>
                      exists (SubsTarget.apply trg'.val.subs body_atom_for_f)
                      constructor
                      . have trg'_loaded := h_trg'.left.left
                        apply trg'_loaded
                        unfold PreTrigger.mapped_body
                        simp [SubsTarget.apply]
                        unfold GroundSubstitution.apply_function_free_conj
                        apply List.mappedElemInMappedList
                        apply h_body_atom_for_f.left
                      . simp [SubsTarget.apply, GroundSubstitution.apply_function_free_atom]
                        simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const] at this
                        rw [this]
                        simp [GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, h]
                        apply List.existsIndexMeansInToSet
                        cases (List.inToSetMeansExistsIndex _ _ h_body_atom_for_f.right) with | intro l h_l =>
                          exists ⟨l, (by rw [List.length_map]; exact l.isLt)⟩
                          simp
                          simp at h_l
                          rw [← h_l]
                          simp [GroundSubstitution.apply_var_or_const]

                  constructor
                  . exact var_for_f_not_in_frontier
                  . rw [eq_term_for_f] at this
                    exact this

          have : trg.val.rule = trg'.val.rule ∧ ∀ v, v ∈ trg.val.rule.frontier.toSet -> trg.val.subs v = trg'.val.subs v := by
            cases this with | intro var2 hvar2 =>
              apply RTrigger.funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame
              apply var_not_in_frontier
              apply hvar2.left
              apply hvar2.right
          have : trg.val.mapped_head = trg'.val.mapped_head := by
            unfold PreTrigger.mapped_head
            rw [← this.left]
            apply List.map_eq_map_if_functions_eq
            intro a _
            unfold PreTrigger.apply_to_function_free_atom
            simp
            intro voc hvoc
            cases voc with
            | const c => simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize]
            | var v =>
              cases Decidable.em (v ∈ trg.val.rule.frontier) with
              | inl v_in_frontier =>
                simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term]
                rw [← this.left]
                simp [VarOrConst.skolemize, v_in_frontier]
                apply this.right
                apply List.listElementAlsoToSetElement
                apply v_in_frontier
              | inr v_not_in_frontier =>
                simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term]
                rw [← this.left]
                simp [VarOrConst.skolemize, v_not_in_frontier]
                apply congrArg
                rw [← FiniteTreeList.eqIffFromListEq]
                apply List.map_eq_map_if_functions_eq
                intro w hw
                rw [← this.right w]
                exact hw

          have : trg.val.result = trg'.val.result := by
            unfold PreTrigger.result
            rw [this]
          rw [this]
          exact h_trg'.right

theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (cs : ChaseSequence obs kb) (trg : RTrigger obs kb.rules) (var : Variable) (i : Nat) : (¬ var ∈ trg.val.rule.frontier) ∧ (∃ f: Fact, f ∈ cs.fact_sets i ∧ (trg.val.apply_to_var_or_const (VarOrConst.var var)) ∈ f.terms.toSet) -> trg.val.result ⊆ cs.fact_sets i := by
  intro h
  cases funcTermForExisVarInChaseMeansTriggerIsUsed cs trg var i h with | intro j hj =>
    have : trg.val.result ⊆ cs.fact_sets j := by
      rw [← hj.right]
      apply Set.subsetUnionSomethingStillSubset
      apply Set.subsetOfSelf

    apply Set.subsetTransitive
    constructor
    apply this
    cases Nat.le.dest hj.left with | intro k hk =>
      rw [← hk]
      apply chaseSequenceSetIsSubsetOfAllFollowing

namespace KnowledgeBase
  def terminates (obs : ObsoletenessCondition) (kb : KnowledgeBase) : Prop :=
    ∃ cs : ChaseSequence obs kb, cs.terminates

  def universally_terminates (obs : ObsoletenessCondition) (kb : KnowledgeBase) : Prop :=
    ∀ cs : ChaseSequence obs kb, cs.terminates
end KnowledgeBase

noncomputable def inductive_homomorphism (cs : ChaseSequence obs kb) (m : FactSet) (mIsModel : m.modelsKb obs kb) : (i : Nat) -> { hom : GroundTermMapping // isHomomorphism hom (cs.fact_sets i) m }
| .zero => ⟨id, (by
  constructor
  . unfold isIdOnConstants ; intro gt ; cases gt <;> simp
  . rw [cs.database_first]
    intro el
    simp [Set.element]
    intro elInSet
    cases elInSet with | intro f hf =>
      apply mIsModel.left
      simp [Set.element]
      have : f = el := by have hfr := hf.right; simp [applyFact, List.map_id'] at hfr; exact hfr
      rw [this] at hf
      exact hf.left
)⟩
| .succ j =>
  let prev_hom := inductive_homomorphism cs m mIsModel j

  let trg_ex_dec := Classical.propDecidable (∃ trg : (RTrigger obs kb.rules), trg.val.active (cs.fact_sets j) ∧ trg.val.result ∪ cs.fact_sets j = cs.fact_sets (j + 1))
  match trg_ex_dec with
  | .isFalse n_trg_ex => ⟨prev_hom.val, (by
    have sequence_finished := by cases cs.triggers_exist j with
    | inl _ => contradiction
    | inr hr => exact hr
    rw [← sequence_finished.right]
    exact prev_hom.property
  )⟩
  | .isTrue trg_ex =>
    let trg := Classical.choose trg_ex
    let ⟨trg_active_for_current_step, trg_result_used_for_next_chase_step⟩ := Classical.choose_spec trg_ex

    let trg_variant_for_m : RTrigger obs kb.rules := {
      val := {
        rule := trg.val.rule
        subs := fun t => prev_hom.val (trg.val.subs t)
      }
      property := trg.property
    }
    have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
      have : trg_variant_for_m.val.loaded (applyFactSet prev_hom (cs.fact_sets j)) := by
        apply PreTrigger.term_mapping_preserves_loadedness
        exact prev_hom.property.left
        exact trg_active_for_current_step.left
      apply Set.subsetTransitive
      exact ⟨this, prev_hom.property.right⟩
    have trg_variant_obsolete_on_m : obs.cond trg_variant_for_m.val m := by
      have m_models_trg : m.modelsRule obs trg_variant_for_m.val.rule := by exact mIsModel.right trg.val.rule trg.property
      unfold FactSet.modelsRule at m_models_trg
      apply m_models_trg
      constructor
      rfl
      apply trg_variant_loaded_for_m

    let obs_for_m_subs := Classical.choose (obs.cond_implies_trg_is_satisfied trg_variant_obsolete_on_m)
    let h_obs_for_m_subs := Classical.choose_spec (obs.cond_implies_trg_is_satisfied trg_variant_obsolete_on_m)

    let next_hom : GroundTermMapping := fun t =>
      match t with
      | FiniteTree.leaf _ => t
      | FiniteTree.inner _ _ =>
        let t_in_step_j_dec := Classical.propDecidable (∃ f, f ∈ (cs.fact_sets j) ∧ t ∈ f.terms.toSet)
        match t_in_step_j_dec with
        | Decidable.isTrue _ => prev_hom.val t
        | Decidable.isFalse _ =>
          let t_in_trg_result_dec := Classical.propDecidable (∃ f, f ∈ trg.val.result ∧ t ∈ f.terms.toSet)
          match t_in_trg_result_dec with
          | Decidable.isFalse _ => t
          | Decidable.isTrue t_in_trg_result =>
            let f := Classical.choose t_in_trg_result
            let ⟨f_in_trg_result, t_in_f⟩ := Classical.choose_spec t_in_trg_result

            let idx_f := trg.val.idx_of_fact_in_result f f_in_trg_result
            let atom_in_head := trg.val.rule.head.get idx_f
            let idx_t_in_f := f.terms.idx_of t (List.listToSetElementAlsoListElement _ _ t_in_f)
            have idx_t_in_f_isLt := idx_t_in_f.isLt
            have f_is_at_its_idx : f = trg.val.mapped_head.get ⟨idx_f.val, by simp [PreTrigger.mapped_head]⟩ := by simp [idx_f, PreTrigger.idx_of_fact_in_result]; apply List.idx_of_get

            have atom_arity_same_as_fact : f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by
                rw [f_is_at_its_idx]
                unfold PreTrigger.mapped_head
                unfold PreTrigger.apply_to_function_free_atom
                simp [atom_in_head]

            let term_corresponding_to_t := atom_in_head.terms.get ⟨idx_t_in_f.val, (by
              rw [← atom_arity_same_as_fact]
              exact idx_t_in_f_isLt
            )⟩

            obs_for_m_subs.apply_var_or_const term_corresponding_to_t

    ⟨next_hom, (by
      constructor
      . intro term
        split
        . simp
        . trivial
      . rw [← trg_result_used_for_next_chase_step]
        intro mapped_fact fact_in_chase

        cases fact_in_chase with | intro fact fact_in_chase =>
          rw [← fact_in_chase.right]
          let fact_in_chase := fact_in_chase.left

          cases fact_in_chase with
          | inr fact_in_prev_step =>
            apply prev_hom.property.right
            exists fact
            constructor
            exact fact_in_prev_step
            unfold applyFact
            simp
            intro ground_term _
            have : ∃ f, f ∈ (cs.fact_sets j) ∧ ground_term ∈ f.terms.toSet := by
              exists fact
              rw [← List.listElementIffToSetElement]
              constructor
              assumption
              assumption
            cases ground_term with
            | leaf c => simp [next_hom]; apply prev_hom.property.left (GroundTerm.const c)
            | inner _ _ =>
              simp [next_hom]
              split
              . rfl
              . contradiction
          | inl fact_in_trg_result =>
            let idx_of_fact_in_result := trg.val.idx_of_fact_in_result fact fact_in_trg_result
            have fact_is_at_its_idx : fact = trg.val.mapped_head.get ⟨idx_of_fact_in_result.val, by simp [PreTrigger.mapped_head]⟩ := by simp [idx_of_fact_in_result, PreTrigger.idx_of_fact_in_result]; apply List.idx_of_get

            rw [fact_is_at_its_idx]
            unfold applyFact

            apply h_obs_for_m_subs.right
            apply List.existsIndexMeansInToSet
            exists ⟨idx_of_fact_in_result.val, (by simp [GroundSubstitution.apply_function_free_conj])⟩
            simp [GroundSubstitution.apply_function_free_conj, GroundSubstitution.apply_function_free_atom, PreTrigger.mapped_head, PreTrigger.apply_to_function_free_atom]

            -- we show that applying next_hom after trg is the same is applying trg_variant_for_m for each relevant VarOrConst

            intro voc voc_is_in_head_atom_for_fact
            cases voc with
            | const _ => simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const]
            | var v_from_head_atom =>
              simp [next_hom, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const]
              split
              case h_1 c h_c_eq =>
                have v_is_in_frontier : v_from_head_atom ∈ trg.val.rule.frontier := by
                  apply Decidable.byContradiction
                  intro opp
                  simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, opp] at h_c_eq
                rw [h_obs_for_m_subs.left _ v_is_in_frontier]
                simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, v_is_in_frontier]
                simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, v_is_in_frontier] at h_c_eq
                rw [h_c_eq]
                have prev_hom_id_on_constants := prev_hom.property.left (FiniteTree.leaf c)
                simp at prev_hom_id_on_constants
                rw [prev_hom_id_on_constants]
              case h_2 =>
                split
                case h_1 _ exis_f _ =>
                  have v_is_in_frontier : v_from_head_atom ∈ trg.val.rule.frontier := by
                    apply Decidable.byContradiction
                    intro v_not_in_frontier
                    simp at v_not_in_frontier

                    have : trg.val.result ⊆ cs.fact_sets j := by
                      apply funcTermForExisVarInChaseMeansTriggerResultOccurs
                      constructor
                      apply v_not_in_frontier
                      apply exis_f

                    have : obs.cond trg.val (cs.fact_sets j) := obs.contains_trg_result_implies_cond this

                    have : ¬ obs.cond trg.val (cs.fact_sets j) := trg_active_for_current_step.right
                    contradiction

                  rw [h_obs_for_m_subs.left]
                  simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, v_is_in_frontier]
                  have : trg.val.rule = trg_variant_for_m.val.rule := by rfl
                  rw [← this]
                  apply v_is_in_frontier
                case h_2 _ n_exis_f_for_step_j _ =>
                  have v_not_in_frontier : ¬ v_from_head_atom ∈ trg.val.rule.frontier := by
                    intro v_is_in_frontier
                    have v_in_body := Rule.frontier_var_occurs_in_fact_in_body _ _ v_is_in_frontier
                    cases v_in_body with | intro f hf =>
                      apply n_exis_f_for_step_j
                      exists (trg.val.subs.apply_function_free_atom f)
                      constructor
                      . apply trg_active_for_current_step.left
                        unfold PreTrigger.mapped_body
                        apply List.mappedElemInMappedList
                        apply hf.left
                      . simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, v_is_in_frontier, GroundSubstitution.apply_function_free_atom]
                        have : trg.val.subs v_from_head_atom = trg.val.subs.apply_var_or_const (VarOrConst.var v_from_head_atom) := by simp [GroundSubstitution.apply_var_or_const]
                        rw [this]
                        apply List.mappedElemInMappedList
                        apply hf.right
                  split
                  case h_1 _ n_exis_f_for_trg_result _ =>
                    apply False.elim
                    apply n_exis_f_for_trg_result
                    exists fact
                    constructor
                    exact fact_in_trg_result
                    rw [fact_is_at_its_idx]

                    rw [← PreTrigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]

                    apply List.existsIndexMeansInToSet
                    rw [List.listElementIffToSetElement] at voc_is_in_head_atom_for_fact
                    cases (List.inToSetMeansExistsIndex _ _ voc_is_in_head_atom_for_fact) with | intro voc_idx h_voc_idx =>
                      exists ⟨voc_idx.val, (by
                        rw [← PreTrigger.apply_to_function_free_atom_terms_same_length]
                        apply voc_idx.isLt
                      )⟩
                      simp [GroundSubstitution.apply_atom, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, FunctionFreeAtom.skolemize, PreTrigger.apply_to_function_free_atom, PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const]
                      simp at h_voc_idx
                      rw [← h_voc_idx]
                  case h_2 _ exis_f _ =>
                    split
                    case _ _ chosen_f_in_result applied_v_is_in_chosen_f _ =>

                      let v_from_head_atom := VarOrConst.var v_from_head_atom
                      let skolem_v := trg.val.skolemize_var_or_const v_from_head_atom
                      let chosen_f := Classical.choose exis_f

                      let idx_f := trg.val.idx_of_fact_in_result chosen_f chosen_f_in_result
                      let atom_in_head := trg.val.rule.head.get idx_f
                      let idx_v_in_f := chosen_f.terms.idx_of (trg.val.apply_to_var_or_const v_from_head_atom) (List.listToSetElementAlsoListElement _ _ applied_v_is_in_chosen_f)
                      have idx_v_in_f_isLt := idx_v_in_f.isLt
                      have f_is_at_its_idx : chosen_f = trg.val.mapped_head.get ⟨idx_f.val, by simp [PreTrigger.mapped_head]⟩ := by simp [idx_f, PreTrigger.idx_of_fact_in_result]; apply List.idx_of_get
                      have v_is_at_its_idx : (trg.val.apply_to_var_or_const v_from_head_atom) = chosen_f.terms.get idx_v_in_f := by simp [idx_v_in_f]; apply List.idx_of_get

                      have atom_arity_same_as_fact : chosen_f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by
                        rw [f_is_at_its_idx]
                        unfold PreTrigger.mapped_head
                        simp
                        rw [← PreTrigger.apply_to_function_free_atom_terms_same_length]
                        simp [atom_in_head]

                      let var_corresponding_to_applied_v := atom_in_head.terms.get ⟨idx_v_in_f.val, (by
                        rw [← atom_arity_same_as_fact]
                        exact idx_v_in_f_isLt
                      )⟩

                      let skolem_term_corresponding_to_applied_v := trg.val.skolemize_var_or_const var_corresponding_to_applied_v

                      have subs_application_is_injective_for_freshly_introduced_terms : ∀ s, trg.val.apply_to_skolemized_term skolem_v = trg.val.apply_to_var_or_const s -> skolem_v = trg.val.skolemize_var_or_const s := by
                        intro s hs
                        cases s with
                        | const const_s =>
                          simp [skolem_v, PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, v_not_in_frontier, GroundSubstitution.apply_skolem_term] at hs
                          contradiction
                        | var var_s =>
                          apply PreTrigger.subs_application_is_injective_for_freshly_introduced_terms
                          apply v_not_in_frontier
                          apply hs

                      have skolemized_ts_are_equal : skolem_term_corresponding_to_applied_v = skolem_v := by
                        apply Eq.symm
                        apply subs_application_is_injective_for_freshly_introduced_terms
                        unfold PreTrigger.apply_to_var_or_const at v_is_at_its_idx
                        simp at v_is_at_its_idx
                        rw [v_is_at_its_idx]

                        have : chosen_f.terms = (trg.val.apply_to_function_free_atom atom_in_head).terms := by
                          rw [f_is_at_its_idx]
                          rw [← PreTrigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]

                        simp [this, PreTrigger.apply_to_function_free_atom, var_corresponding_to_applied_v]

                      have : var_corresponding_to_applied_v = v_from_head_atom := by
                        apply VarOrConst.skolemize_injective trg.val.rule.id (Rule.frontier trg.val.rule)
                        apply skolemized_ts_are_equal

                      simp [var_corresponding_to_applied_v, atom_in_head] at this
                      rw [this]

    )⟩

theorem inductive_homomorphism_same_on_terms_in_next_step (cs : ChaseSequence obs kb) (m : FactSet) (mIsModel : m.modelsKb obs kb) : ∀ i f t, f ∈ cs.fact_sets i ∧ t ∈ f.terms.toSet -> (inductive_homomorphism cs m mIsModel i).val t = (inductive_homomorphism cs m mIsModel (Nat.succ i)).val t := by
  intro i f t ⟨f_in_step_i, t_is_term_in_f⟩
  conv =>
    rhs
    unfold inductive_homomorphism
    simp
  split
  case h_1 _ n_ex_trg _ => simp [n_ex_trg]
  case h_2 _ _ _ =>
    split
    simp
    split
    case h_1 c => exact (inductive_homomorphism cs m mIsModel i).property.left (GroundTerm.const c)
    case h_2 ft =>
      split
      case h_1 _ ex_f _ => rfl
      case h_2 _ n_ex_f _ => apply False.elim; apply n_ex_f; exists f

theorem inductive_homomorphism_same_on_all_following_terms (cs : ChaseSequence obs kb) (m : FactSet) (mIsModel : m.modelsKb obs kb) : ∀ i j f t, f ∈ cs.fact_sets i ∧ t ∈ f.terms.toSet -> (inductive_homomorphism cs m mIsModel i).val t = (inductive_homomorphism cs m mIsModel (i + j)).val t := by
  intro i j f t
  induction j with
  | zero => intros; rfl
  | succ k ih =>
    intro h_precondition
    rw [ih h_precondition]
    apply inductive_homomorphism_same_on_terms_in_next_step
    constructor
    apply chaseSequenceSetIsSubsetOfAllFollowing
    apply h_precondition.left
    apply h_precondition.right

theorem chaseResultUnivModelsKb (cs : ChaseSequence obs kb) : cs.result.universallyModelsKb obs kb := by
  constructor
  constructor

  -- DB in CS
  unfold FactSet.modelsDb
  unfold ChaseSequence.result
  intro f
  intro h
  exists 0
  rw [cs.database_first]
  exact h

  -- Rules modelled
  unfold FactSet.modelsRules
  intro r
  intro h
  unfold FactSet.modelsRule
  simp
  intro trg trg_rule trg_loaded
  apply Classical.byContradiction
  intro trg_not_obsolete
  cases (trgActiveForChaseResultMeansActiveAtSomeIndex cs trg ⟨trg_loaded, trg_not_obsolete⟩) with | intro i active_i =>
    have not_active_eventually := cs.fairness ⟨trg, by rw [← trg_rule] at h; apply h⟩ i active_i
    cases not_active_eventually with | intro j not_active_j =>
      have ⟨j_ge_i, not_active_j⟩ := not_active_j
      simp [Trigger.active] at not_active_j
      have obsolete_j := not_active_j (by
        simp [PreTrigger.loaded]
        apply Set.subsetTransitive
        constructor
        apply active_i.left
        cases Nat.le.dest j_ge_i with | intro m hm => rw [← hm]; apply chaseSequenceSetIsSubsetOfAllFollowing cs i m
      )
      apply trg_not_obsolete
      apply obs.monotone
      apply chaseSequenceSetIsSubsetOfResult cs j
      apply obsolete_j

  -- universality
  intro m mIsModel

  let inductive_homomorphism_shortcut := inductive_homomorphism cs m mIsModel

  let global_h : GroundTermMapping := fun t =>
    let dec := Classical.propDecidable (∃ f, f ∈ cs.result ∧ t ∈ f.terms.toSet)
    match dec with
      | Decidable.isTrue p =>
        let ⟨hfl, _⟩ := Classical.choose_spec p
        let i := Classical.choose hfl
        let target_h := inductive_homomorphism_shortcut i
        target_h.val t
      | Decidable.isFalse _ => t

  have : ∀ i f, f ∈ cs.fact_sets i -> applyFact global_h f = applyFact (inductive_homomorphism_shortcut i).val f := by
    intro i f f_in_step_i
    unfold applyFact
    simp [global_h]
    -- apply List.map_eq_map_if_functions_eq
    intro t t_is_term_in_f
    split
    case h_2 _ n_ex_f' _ =>
      apply False.elim
      apply n_ex_f'
      exists f
      constructor
      . apply chaseSequenceSetIsSubsetOfResult; apply f_in_step_i
      . rw [← List.listElementIffToSetElement]; apply t_is_term_in_f
    case h_1 _ ex_f' _ =>
      split
      case _ f' t_is_term_in_f' _ =>
        let j := Classical.choose f'
        let f'_in_step_j := Classical.choose_spec f'
        cases Nat.le_total i j with
        | inl i_le_j =>
          have j_is_i_plus_k := Nat.le.dest i_le_j
          cases j_is_i_plus_k with | intro k hk =>
            simp [j] at hk
            rw [← hk]
            apply Eq.symm
            apply inductive_homomorphism_same_on_all_following_terms
            constructor
            apply f_in_step_i
            rw [← List.listElementIffToSetElement]; apply t_is_term_in_f
        | inr j_le_i =>
          have i_is_j_plus_k := Nat.le.dest j_le_i
          cases i_is_j_plus_k with | intro k hk =>
            rw [← hk]
            apply inductive_homomorphism_same_on_all_following_terms
            constructor
            apply f'_in_step_j
            apply t_is_term_in_f'

  exists global_h
  constructor
  . intro gt
    split
    case h_1 _ c =>
      simp [global_h]
      split
      . split
        case h_1 hfl _ _ =>
          let i := Classical.choose hfl
          exact (inductive_homomorphism_shortcut i).property.left (GroundTerm.const c)
      . trivial
    . trivial

  . intro f hf
    unfold ChaseSequence.result at hf
    unfold Set.element at hf
    unfold applyFactSet at hf
    cases hf with | intro e he =>
      let ⟨hel, her⟩ := he
      simp [Set.element] at hel
      cases hel with | intro n hn =>
        rw [← her]
        rw [this n e hn]
        have : applyFactSet (inductive_homomorphism_shortcut n).val (cs.fact_sets n) ⊆ m := (inductive_homomorphism_shortcut n).property.right
        unfold Set.subset at this
        apply this
        simp [Set.element, applyFactSet]
        exists e
-/

