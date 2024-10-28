import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.Trigger
import ProofLibrary.Logic
import ProofLibrary.PossiblyInfiniteTree

structure ChaseNode (obs : ObsoletenessCondition) (rules : RuleSet) where
  fact : FactSet
  -- the origin is none only for the database
  origin : Option ((trg : RTrigger obs rules) × Fin trg.val.result.length)
  fact_contains_origin_result : origin.is_none_or (fun origin => origin.fst.val.result.get origin.snd ⊆ fact)

def exists_trigger_opt_fs (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger obs rules), trg.val.active before.fact ∧ ∃ i, some { fact := before.fact ∪ trg.val.result.get i, origin := some ⟨trg, i⟩, fact_contains_origin_result := by simp [Option.is_none_or]; apply Set.subsetUnionSomethingStillSubset'; apply Set.subsetOfSelf } = after

def exists_trigger_list_condition (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) (trg : RTrigger obs rules) : Prop :=
  trg.val.active before.fact ∧ trg.val.result.enum_with_lt.attach.map (fun ⟨⟨i, fs⟩, h⟩ => {
    fact := before.fact ∪ fs,
    origin := some ⟨trg, i⟩,
    fact_contains_origin_result := by
      have : fs = trg.val.result[i.val] := by rw [List.mk_mem_enum_with_lt_iff_getElem] at h; rw [h]
      simp [Option.is_none_or]
      apply Set.subsetUnionSomethingStillSubset'
      rw [this]
      apply Set.subsetOfSelf
    }) = after

def exists_trigger_list (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger obs rules), exists_trigger_list_condition obs rules before after trg

def not_exists_trigger_opt_fs (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.fact) ∧ after = none

def not_exists_trigger_list (obs : ObsoletenessCondition) (rules : RuleSet) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.fact) ∧ after = []

structure ChaseBranch (obs : ObsoletenessCondition) (kb : KnowledgeBase) where
  branch : PossiblyInfiniteList (ChaseNode obs kb.rules)
  database_first : branch.infinite_list 0 = some { fact := kb.db.toFactSet, origin := none, fact_contains_origin_result := by simp [Option.is_none_or] }
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
  database_first : tree.get [] = some { fact := kb.db.toFactSet, origin := none, fact_contains_origin_result := by simp [Option.is_none_or] }
  triggers_exist : ∀ node : List Nat, (tree.get node).is_none_or (fun before =>
    let after := tree.children node
    (exists_trigger_list obs kb.rules before after) ∨
    (not_exists_trigger_list obs kb.rules before after))

  fairness_leaves : ∀ leaf, leaf ∈ tree.leaves -> ∀ trg : (RTrigger obs kb.rules), ¬ trg.val.active leaf.fact
  fairness_infinite_branches : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ∀ node : List Nat, node.length ≥ i ->
    (tree.get node).is_none_or (fun fs => ¬ trg.val.active fs.fact)

namespace ChaseTree
  def branches (ct : ChaseTree obs kb) : Set (ChaseBranch obs kb) := fun branch =>
    branch.branch ∈ ct.tree.branches

  def branches_through (ct : ChaseTree obs kb) (node : List Nat) : Set (ChaseBranch obs kb) := fun branch =>
    branch.branch ∈ ct.tree.branches_through node

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

theorem chaseTreeSetIsSubsetOfResult (ct : ChaseTree obs kb) : ∀ node : List Nat, (ct.tree.get node).is_none_or (fun fs => ∀ branch, branch ∈ ct.branches_through node -> fs.fact ⊆ branch.result) := by
  intro node
  unfold Option.is_none_or

  cases eq : ct.tree.get node with
  | none => simp
  | some fs =>
    simp
    intro branch branch_through_node
    have : branch.branch.infinite_list node.length = ct.tree.get node := by
      unfold ChaseTree.branches_through at branch_through_node
      unfold FiniteDegreeTree.branches_through at branch_through_node
      unfold PossiblyInfiniteTree.branches_through at branch_through_node
      unfold InfiniteTreeSkeleton.branches_through at branch_through_node
      simp [Set.element] at branch_through_node
      rw [branch_through_node.right ⟨node.length, by simp⟩]
      simp
      rfl

    have branch_subs_result := chaseBranchSetIsSubsetOfResult branch node.length
    rw [this] at branch_subs_result
    simp [eq, Option.is_none_or] at branch_subs_result
    apply branch_subs_result

theorem trgLoadedForChaseResultMeansLoadedAtSomeIndex (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.loaded cb.result -> ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => trg.loaded fs.fact) := by
  intro trg
  unfold ChaseBranch.result
  unfold PreTrigger.loaded

  induction trg.mapped_body
  case nil =>
    intro _
    exists 0
    rw [cb.database_first]
    simp [Option.is_some_and]
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

        unfold Option.is_some_and
        split
        case h_1 heq =>
          simp [Nat.max_def] at heq
          split at heq
          . rw [heq] at hj
            simp [Option.is_some_and] at hj
          . rw [heq] at hi
            simp [Option.is_some_and] at hi

        case h_2 heq =>
          simp
          rw [Set.unionSubsetEachSubset]
          constructor
          . unfold Option.is_some_and at hi
            split at hi
            . contradiction
            case h_2 a heq2 =>
              apply Set.subsetTransitive _ a.fact _
              constructor
              . intro e he
                simp [Set.element] at he
                rw [he]
                assumption
              . cases Nat.le.dest help_i with | intro m hm =>
                have subsOfAllFollowing := chaseBranchSetIsSubsetOfAllFollowing cb i m
                rw [heq2] at subsOfAllFollowing
                simp at subsOfAllFollowing
                rw [← hm] at heq
                rw [heq] at subsOfAllFollowing
                simp [Option.is_none_or] at subsOfAllFollowing
                exact subsOfAllFollowing
          . cases Nat.le.dest help_j with | intro m hm =>
              have subsOfAllFollowing := chaseBranchSetIsSubsetOfAllFollowing cb j m
              split at subsOfAllFollowing
              . rw [hm, heq] at subsOfAllFollowing; contradiction
              case h_2 heq2 =>
                rw [heq2] at hj
                simp [Option.is_some_and] at hj
                rw [← hm] at heq
                rw [heq] at subsOfAllFollowing
                simp [Option.is_none_or] at subsOfAllFollowing
                apply Set.subsetTransitive
                constructor
                apply hj
                apply subsOfAllFollowing

theorem trgActiveForChaseResultMeansActiveAtSomeIndex (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.active cb.result -> ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => trg.active fs.fact) := by
  intro trg
  unfold Trigger.active
  simp
  intro loaded active
  have trgLoadedForN := trgLoadedForChaseResultMeansLoadedAtSomeIndex cb trg loaded
  cases trgLoadedForN with | intro n loadedN =>
    exists n
    unfold Option.is_some_and
    split
    case h_1 heq => rw [heq] at loadedN; simp [Option.is_some_and] at loadedN
    case h_2 heq =>
      simp
      constructor
      . rw [heq] at loadedN; simp [Option.is_some_and] at loadedN; exact loadedN
      . intro contra
        apply active
        apply obs.monotone
        . have subsetOfResult := chaseBranchSetIsSubsetOfResult cb n
          rw [heq] at subsetOfResult
          simp [Option.is_none_or] at subsetOfResult
          apply subsetOfResult
        . apply contra

theorem funcTermForExisVarInChaseMeansTriggerIsUsed (ct : ChaseTree obs kb) (trg : RTrigger obs kb.rules) (result_index : Fin trg.val.result.length) (var : Variable) (node : ChaseNode obs kb.rules) (node_path : List Nat) : some node = ct.tree.get node_path ∧ (¬ var ∈ trg.val.rule.frontier) ∧ (∃ f: Fact, f ∈ node.fact ∧ (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) ∈ f.terms.toSet) -> ∃ drop_number : Fin node_path.length, (ct.tree.get (node_path.drop drop_number.val)).is_some_and (fun prev_node => prev_node.origin.is_some_and (fun origin => trg.equiv origin.fst ∧ result_index.val = origin.snd.val)) := by
  intro ⟨node_is_at_path, var_not_in_frontier, exis_f⟩
  induction node_path generalizing node with
  | nil =>
    cases exis_f with | intro f hf =>
      let ⟨f_in_db, functional_term_in_f⟩ := hf
      rw [ct.database_first] at node_is_at_path
      injection node_is_at_path with node_is_at_path
      rw [node_is_at_path] at f_in_db
      simp at f_in_db
      have : ∀ t, t ≠ GroundSubstitution.apply_skolem_term trg.val.subs (VarOrConst.skolemize trg.val.rule.id result_index.val (Rule.frontier trg.val.rule) (VarOrConst.var var)) := by
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
                exists GroundSubstitution.apply_skolem_term trg.val.subs (VarOrConst.skolemize trg.val.rule.id result_index.val (Rule.frontier trg.val.rule) (VarOrConst.var var))
                constructor
                exact functional_term_in_f
                simp [GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var_not_in_frontier]
            contradiction
      apply False.elim
      apply this
      rfl
  | cons head tail ih =>
    cases eq : ct.tree.get tail with
    | none =>
      apply False.elim
      apply ct.tree.tree.no_orphans (head::tail) _ ⟨tail, by exists [head]⟩
      unfold FiniteDegreeTree.get at eq
      unfold PossiblyInfiniteTree.get at eq
      exact eq
      unfold FiniteDegreeTree.get at node_is_at_path
      unfold PossiblyInfiniteTree.get at node_is_at_path
      rw [← node_is_at_path]
      simp
    | some tail_node =>
      -- TODO: this should actually be decidable but we need to change the implementation for this
      cases Classical.em (∃ f: Fact, f ∈ tail_node.fact ∧ (trg.val.subs.apply_skolem_term (VarOrConst.skolemize trg.val.rule.id result_index.val trg.val.rule.frontier (VarOrConst.var var))) ∈ f.terms.toSet) with
      | inl f_in_j =>
        cases ih tail_node (Eq.symm eq) f_in_j with | intro k _ =>
          exists ⟨k+1, by simp⟩
      | inr f_not_in_j =>
        exists ⟨0, by simp⟩
        simp [Option.is_some_and]
        rw [← node_is_at_path]
        simp
        have triggers_exist := ct.triggers_exist tail
        rw [eq] at triggers_exist
        simp [Option.is_none_or] at triggers_exist
        cases triggers_exist with
        | inr no_trg_ex =>
          unfold not_exists_trigger_list at no_trg_ex
          have : ct.tree.get (head::tail) = none := by
            apply ct.tree.children_empty_means_all_following_none
            exact no_trg_ex.right
          rw [this] at node_is_at_path
          simp at node_is_at_path
        | inl trg_ex =>
          unfold exists_trigger_list at trg_ex
          cases trg_ex with | intro trg' htrg' =>
            have head_lt_tail_children_length : head < (ct.tree.children tail).length := by
              apply Decidable.byContradiction
              intro contra
              have : none = (ct.tree.children tail)[head]? := by
                simp at contra
                apply Eq.symm
                apply List.getElem?_eq_none
                exact contra
              rw [FiniteDegreeTree.getElem_children_eq_getElem_tree_children] at this
              rw [PossiblyInfiniteTree.getElem_children_eq_get_tree] at this
              unfold FiniteDegreeTree.get at node_is_at_path
              rw [← node_is_at_path] at this
              contradiction
            have head_lt_aux_1 : head < trg'.val.result.length := by rw [← htrg'.right] at head_lt_tail_children_length; simp [List.enum_with_lt_length_eq] at head_lt_tail_children_length; exact head_lt_tail_children_length
            have head_lt_aux_2 : head < trg'.val.rule.head.length := by rw [← htrg'.right] at head_lt_tail_children_length; simp [List.enum_with_lt_length_eq] at head_lt_tail_children_length; rw [PreTrigger.head_length_eq_mapped_head_length]; unfold PreTrigger.result at head_lt_tail_children_length; simp at head_lt_tail_children_length; exact head_lt_tail_children_length
            have head_lt_aux_3 : head < trg'.val.mapped_head.length := by rw [← htrg'.right] at head_lt_tail_children_length; simp [List.enum_with_lt_length_eq] at head_lt_tail_children_length; unfold PreTrigger.result at head_lt_tail_children_length; simp at head_lt_tail_children_length; exact head_lt_tail_children_length
            have head_lt_aux_4 : head < trg'.val.result.enum_with_lt.length := by rw [List.enum_with_lt_length_eq]; exact head_lt_aux_1

            rw [← ct.tree.getElem_children_eq_get_tree tail ⟨head, head_lt_tail_children_length⟩] at node_is_at_path
            injection node_is_at_path with node_is_at_path

            have : ∃ f, f ∈ trg'.val.result[head] ∧ (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) ∈ List.toSet f.terms := by
              cases exis_f with | intro f hf =>
                exists f
                constructor
                . have f_in_next_step := hf.left
                  rw [node_is_at_path] at f_in_next_step
                  simp [← htrg'.right] at f_in_next_step
                  cases f_in_next_step with
                  | inr f_in_result =>
                    simp only [List.getElem_attach _ _ head_lt_aux_4] at f_in_result
                    rw [List.enum_with_lt_getElem_snd_eq_getElem] at f_in_result
                    assumption
                  | inl f_in_j =>
                    apply False.elim
                    apply f_not_in_j
                    exists f
                    constructor
                    exact f_in_j
                    exact hf.right
                . exact hf.right

            have : ∃ var2, ¬ var2 ∈ trg'.val.rule.frontier ∧ (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) = (trg'.val.apply_to_var_or_const head (VarOrConst.var var2)) := by
              cases this with | intro f hf =>
                have ⟨f_in_res, apply_var_in_f_terms⟩ := hf
                let i := trg'.val.idx_of_fact_in_result f ⟨head, head_lt_aux_1⟩ f_in_res
                let atom_for_f := trg'.val.rule.head[head].get i

                cases List.inToSetMeansExistsIndex _ _ apply_var_in_f_terms with | intro k hk =>
                  have f_is_at_its_idx : f = (trg'.val.mapped_head.get ⟨head, head_lt_aux_3⟩).get ⟨i.val, by unfold PreTrigger.mapped_head; simp⟩ := by simp [i, PreTrigger.idx_of_fact_in_result]; apply List.idx_of_get

                  have atom_arity_same_as_fact : f.terms.length = List.length (FunctionFreeAtom.terms atom_for_f) := by
                    rw [f_is_at_its_idx]
                    unfold PreTrigger.mapped_head
                    unfold PreTrigger.apply_to_function_free_atom
                    simp [atom_for_f]

                  let term_for_f := atom_for_f.terms.get ⟨k.val, (by
                    rw [← atom_arity_same_as_fact]
                    exact k.isLt
                  )⟩

                  have : (trg'.val.apply_to_var_or_const head term_for_f) = f.terms.get k := by
                    have : f.terms = (trg'.val.apply_to_function_free_atom head atom_for_f).terms := by
                      conv => lhs; rw [f_is_at_its_idx]
                      rw [← trg'.val.apply_subs_to_atom_at_idx_same_as_fact_at_idx ⟨head, head_lt_aux_2⟩]
                      simp [atom_for_f]
                    rw [List.get_eq_of_eq this]
                    simp [PreTrigger.apply_to_function_free_atom, term_for_f]

                  have : (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) = (trg'.val.apply_to_var_or_const head term_for_f) := by
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
                        . have trg'_loaded := htrg'.left.left
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

            have : trg.equiv trg' ∧ result_index.val = head := by
              cases this with | intro var2 hvar2 =>
                apply RTrigger.funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame trg trg' ⟨result_index.val, by have isLt := result_index.isLt; unfold PreTrigger.result at isLt; rw [PreTrigger.head_length_eq_mapped_head_length]; simp at isLt; apply isLt⟩ ⟨head, head_lt_aux_2⟩
                apply var_not_in_frontier
                apply hvar2.left
                apply hvar2.right

            simp [← htrg'.right] at node_is_at_path
            rw [node_is_at_path]
            simp
            simp only [List.getElem_attach _ _ head_lt_aux_4]
            rw [List.enum_with_lt_getElem_fst_eq_index _ _ head_lt_aux_1]
            exact this

theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (ct : ChaseTree obs kb) (trg : RTrigger obs kb.rules) (result_index : Fin trg.val.result.length) (var : Variable) (node : ChaseNode obs kb.rules) (node_path : List Nat) : (some node = ct.tree.get node_path) ∧ (¬ var ∈ trg.val.rule.frontier) ∧ (∃ f: Fact, f ∈ node.fact ∧ (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) ∈ f.terms.toSet) -> trg.val.result.get result_index ⊆ node.fact := by
  intro h
  have node_is_at_path := h.left
  cases funcTermForExisVarInChaseMeansTriggerIsUsed ct trg result_index var node node_path h with | intro drop_number h =>
    cases eq : ct.tree.get (node_path.drop drop_number) with
    | none => rw [eq] at h; simp [Option.is_some_and] at h
    | some prev_node =>
      rw [eq] at h; simp [Option.is_some_and] at h
      have : trg.val.result.get result_index ⊆ prev_node.fact := by
        cases eq : prev_node.origin with
        | none => simp [eq] at h
        | some origin =>
          have fact_contains_origin_result := prev_node.fact_contains_origin_result
          simp [eq] at h
          rw [eq] at fact_contains_origin_result
          simp [Option.is_none_or] at fact_contains_origin_result
          simp [h.right]
          unfold RTrigger.equiv at h
          simp [PreTrigger.result_eq_of_equiv _ _ h.left]
          exact fact_contains_origin_result

      apply Set.subsetTransitive
      constructor
      apply this

      have subsetAllFollowing := chaseTreeSetIsSubsetOfAllFollowing ct (node_path.drop drop_number) (node_path.take drop_number)
      rw [eq] at subsetAllFollowing
      rw [List.take_append_drop] at subsetAllFollowing
      rw [← node_is_at_path] at subsetAllFollowing
      simp [Option.is_none_or] at subsetAllFollowing
      exact subsetAllFollowing

abbrev InductiveHomomorphismResult (ct : ChaseTree obs kb) (m : FactSet) (depth : Nat) := {pair : (List Nat) × GroundTermMapping // pair.1.length = depth ∧ (ct.tree.get pair.1).is_none_or (fun fs => isHomomorphism pair.2 fs.fact m) }

noncomputable def inductive_homomorphism_with_prev_node_and_trg (ct : ChaseTree obs kb) (m : FactSet) (m_is_model : m.modelsKb obs kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : InductiveHomomorphismResult ct m (prev_depth + 1) :=
  let prev_path := prev_result.val.fst
  let prev_hom := prev_result.val.snd
  let prev_cond := prev_result.property
  have prev_hom_is_homomorphism : isHomomorphism prev_hom prev_node_unwrapped.fact m := by
    have prev_cond_r := prev_cond.right
    rw [prev_node_eq] at prev_cond_r
    simp [Option.is_none_or] at prev_cond_r
    exact prev_cond_r

  let trg := Classical.choose trg_ex
  let trg_spec := Classical.choose_spec trg_ex
  let trg_active_for_current_step := trg_spec.left
  let trg_result_used_for_next_chase_step := trg_spec.right

  let trg_variant_for_m : RTrigger obs kb.rules := {
    val := {
      rule := trg.val.rule
      subs := fun t => prev_hom (trg.val.subs t)
    }
    property := trg.property
  }
  have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
    have : trg_variant_for_m.val.loaded (applyFactSet prev_hom prev_node_unwrapped.fact) := by
      apply PreTrigger.term_mapping_preserves_loadedness
      . exact prev_hom_is_homomorphism.left
      . exact trg_active_for_current_step.left
    apply Set.subsetTransitive
    exact ⟨this, prev_hom_is_homomorphism.right⟩
  have trg_variant_obsolete_on_m : obs.cond trg_variant_for_m.val m := by
    have m_models_trg : m.modelsRule obs trg_variant_for_m.val.rule := by exact m_is_model.right trg.val.rule trg.property
    unfold FactSet.modelsRule at m_models_trg
    apply m_models_trg
    constructor
    rfl
    apply trg_variant_loaded_for_m

  let obs_for_m_subs := Classical.choose (obs.cond_implies_trg_is_satisfied trg_variant_obsolete_on_m)
  let h_obs_for_m_subs := Classical.choose_spec (obs.cond_implies_trg_is_satisfied trg_variant_obsolete_on_m)
  let head_index_for_m_subs := Classical.choose h_obs_for_m_subs
  let h_obs_at_head_index_for_m_subs := Classical.choose_spec h_obs_for_m_subs

  let result_index_for_trg : Fin trg.val.result.length := ⟨head_index_for_m_subs.val, by unfold PreTrigger.result; unfold PreTrigger.mapped_head; simp [List.enum_with_lt_length_eq]⟩

  let next_hom : GroundTermMapping := fun t =>
    match t with
    | FiniteTree.leaf _ => t
    | FiniteTree.inner _ _ =>
      let t_in_step_j_dec := Classical.propDecidable (∃ f, f ∈ prev_node_unwrapped.fact ∧ t ∈ f.terms.toSet)
      match t_in_step_j_dec with
      | Decidable.isTrue _ => prev_hom t
      | Decidable.isFalse _ =>
        let t_in_trg_result_dec := Classical.propDecidable (∃ f, f ∈ (trg.val.result.get result_index_for_trg) ∧ t ∈ f.terms.toSet)
        match t_in_trg_result_dec with
        | Decidable.isFalse _ => t
        | Decidable.isTrue t_in_trg_result =>
          let f := Classical.choose t_in_trg_result
          let ⟨f_in_trg_result, t_in_f⟩ := Classical.choose_spec t_in_trg_result

          let idx_f := trg.val.idx_of_fact_in_result f result_index_for_trg f_in_trg_result
          let atom_in_head := (trg.val.rule.head.get head_index_for_m_subs).get idx_f
          let idx_t_in_f := f.terms.idx_of t (List.listToSetElementAlsoListElement _ _ t_in_f)
          have idx_t_in_f_isLt := idx_t_in_f.isLt
          have f_is_at_its_idx :
            f = (trg.val.mapped_head.get ⟨head_index_for_m_subs.val, by simp [PreTrigger.mapped_head, List.enum_with_lt_length_eq]⟩).get ⟨idx_f.val, by simp [PreTrigger.mapped_head, List.enum_with_lt_getElem_snd_eq_getElem]⟩ := by simp [idx_f, PreTrigger.idx_of_fact_in_result]; apply List.idx_of_get

          have atom_arity_same_as_fact : f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by
              rw [f_is_at_its_idx]
              unfold PreTrigger.mapped_head
              unfold PreTrigger.apply_to_function_free_atom
              simp [atom_in_head, List.enum_with_lt_getElem_snd_eq_getElem]

          let term_corresponding_to_t := atom_in_head.terms.get ⟨idx_t_in_f.val, (by
            rw [← atom_arity_same_as_fact]
            exact idx_t_in_f_isLt
          )⟩

          obs_for_m_subs.apply_var_or_const term_corresponding_to_t

  ⟨(head_index_for_m_subs.val::prev_path, next_hom), by
    have prev_cond_r := prev_cond.right
    rw [prev_node_eq] at prev_cond_r
    simp [Option.is_none_or] at prev_cond_r

    constructor
    . simp; exact prev_cond.left
    cases next_node_eq : ct.tree.get (head_index_for_m_subs.val::prev_path) with
    | none => simp [Option.is_none_or]
    | some next_node =>
    simp only [Option.is_none_or]
    constructor
    . intro term
      split
      . simp
      . trivial
    have next_node_results_from_trg : next_node.fact = prev_node_unwrapped.fact ∪ trg.val.result.get result_index_for_trg := by
      have length_eq_helper_1 : trg.val.rule.head.length = trg.val.result.enum_with_lt.attach.length := by
        simp
        rw [List.enum_with_lt_length_eq]
        unfold PreTrigger.result
        unfold PreTrigger.mapped_head
        simp [List.enum_with_lt_length_eq]
      have length_eq_helper_2 : trg_variant_for_m.val.rule.head.length = (ct.tree.children prev_path).length := by
        rw [← trg_result_used_for_next_chase_step]
        simp
        simp at length_eq_helper_1
        exact length_eq_helper_1
      have length_lt_helper : head_index_for_m_subs.val < trg.val.result.enum_with_lt.length := by
        simp at length_eq_helper_1
        rw [← length_eq_helper_1]
        exact head_index_for_m_subs.isLt
      rw [List.map_eq_iff] at trg_result_used_for_next_chase_step
      specialize trg_result_used_for_next_chase_step head_index_for_m_subs.val
      have index_valid : head_index_for_m_subs < (ct.tree.children prev_path).length := by rw [← length_eq_helper_2]; exact head_index_for_m_subs.isLt
      rw [List.getElem?_eq_getElem (l:=ct.tree.children prev_path) (n:=head_index_for_m_subs) index_valid] at trg_result_used_for_next_chase_step
      rw [List.getElem?_eq_getElem (l:=trg.val.result.enum_with_lt.attach) (n:=head_index_for_m_subs) (by rw [← length_eq_helper_1]; simp)] at trg_result_used_for_next_chase_step
      simp at trg_result_used_for_next_chase_step
      have : some (ct.tree.children prev_path)[head_index_for_m_subs.val] = some next_node := by
        rw [ct.tree.getElem_children_eq_get_tree prev_path ⟨head_index_for_m_subs.val, index_valid⟩]
        exact next_node_eq
      injection this with this
      rw [this] at trg_result_used_for_next_chase_step
      rw [trg_result_used_for_next_chase_step]
      simp
      simp only [List.getElem_attach _ _ length_lt_helper]
      rw [List.enum_with_lt_getElem_snd_eq_getElem]
    rw [next_node_results_from_trg]

    intro mapped_fact fact_in_chase

    cases fact_in_chase with | intro fact fact_in_chase =>
      rw [← fact_in_chase.right]
      let fact_in_chase := fact_in_chase.left

      cases fact_in_chase with
      | inl fact_in_prev_step =>
        apply prev_cond_r.right
        exists fact
        constructor
        exact fact_in_prev_step
        unfold applyFact
        simp
        intro ground_term _
        have : ∃ f, f ∈ prev_node_unwrapped.fact ∧ ground_term ∈ f.terms.toSet := by
          exists fact
          rw [← List.listElementIffToSetElement]
          constructor
          assumption
          assumption
        cases ground_term with
        | leaf c => simp [next_hom]; apply prev_cond_r.left (GroundTerm.const c)
        | inner _ _ =>
          simp [next_hom]
          split
          . rfl
          . contradiction
      | inr fact_in_trg_result =>
        let idx_of_fact_in_result := trg.val.idx_of_fact_in_result fact result_index_for_trg fact_in_trg_result
        have fact_is_at_its_idx :
          fact = (trg.val.mapped_head.get ⟨head_index_for_m_subs.val, by simp [PreTrigger.mapped_head, List.enum_with_lt_length_eq]⟩).get ⟨idx_of_fact_in_result.val, by simp [PreTrigger.mapped_head, List.enum_with_lt_getElem_snd_eq_getElem]⟩ := by simp [idx_of_fact_in_result, PreTrigger.idx_of_fact_in_result]; apply List.idx_of_get

        rw [fact_is_at_its_idx]
        unfold applyFact

        apply h_obs_at_head_index_for_m_subs.right
        apply List.existsIndexMeansInToSet
        exists ⟨idx_of_fact_in_result.val, (by
          simp only [GroundSubstitution.apply_function_free_conj, List.length_map]
          have isLt := idx_of_fact_in_result.isLt
          simp only [List.get_eq_getElem, head_index_for_m_subs] at isLt
          apply isLt
        )⟩
        simp only [GroundSubstitution.apply_function_free_conj, GroundSubstitution.apply_function_free_atom, PreTrigger.mapped_head, PreTrigger.apply_to_function_free_atom, List.get_eq_getElem, List.getElem_map]

        -- we show that applying next_hom after trg is the same is applying trg_variant_for_m for each relevant VarOrConst

        simp only [head_index_for_m_subs, Fact.mk.injEq]
        constructor
        . simp [List.enum_with_lt_getElem_snd_eq_getElem]
        let head_disjunct : List FunctionFreeAtom := trg.val.rule.head[head_index_for_m_subs.val]
        have : (trg.val.rule.head.enum[head_index_for_m_subs.val]'(by simp [List.enum_with_lt_length_eq])).snd = head_disjunct := by rw [List.getElem_enum]
        have terms_eq : head_disjunct[idx_of_fact_in_result.val].terms = head_disjunct[idx_of_fact_in_result.val].terms := rfl
        conv at terms_eq => left; simp only [← this]
        conv at terms_eq => right; simp only [head_disjunct]
        simp only [head_index_for_m_subs] at terms_eq
        rw [List.map_map, terms_eq, List.map_eq_map_iff]
        intro voc voc_is_in_head_atom_for_fact
        cases voc with
        | const _ => simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const]
        | var v_from_head_atom =>
          have : trg.val.rule.head.enum[head_index_for_m_subs.val].fst = head_index_for_m_subs.val := by simp
          rw [this]
          simp [next_hom, GroundSubstitution.apply_var_or_const]
          split
          case h_1 c h_c_eq =>
            have v_is_in_frontier : v_from_head_atom ∈ trg.val.rule.frontier := by
              apply Decidable.byContradiction
              intro opp
              simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, opp] at h_c_eq
            rw [h_obs_at_head_index_for_m_subs.left _ v_is_in_frontier]
            simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, v_is_in_frontier]
            simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, v_is_in_frontier] at h_c_eq
            rw [h_c_eq]
            have prev_hom_id_on_constants := prev_cond_r.left (FiniteTree.leaf c)
            simp at prev_hom_id_on_constants
            simp only [prev_hom]
            rw [prev_hom_id_on_constants]
          case h_2 =>
            split
            case h_1 _ exis_f _ =>
              have v_is_in_frontier : v_from_head_atom ∈ trg.val.rule.frontier := by
                apply Decidable.byContradiction
                intro v_not_in_frontier
                simp at v_not_in_frontier

                have : (trg.val.result.get result_index_for_trg) ⊆ prev_node_unwrapped.fact := by
                  apply funcTermForExisVarInChaseMeansTriggerResultOccurs ct trg result_index_for_trg v_from_head_atom prev_node_unwrapped prev_path
                  constructor
                  . rw [prev_node_eq]
                  constructor
                  . apply v_not_in_frontier
                  . simp [result_index_for_trg]
                    apply exis_f

                have : obs.cond trg.val prev_node_unwrapped.fact := obs.contains_trg_result_implies_cond result_index_for_trg this
                have : ¬ obs.cond trg.val prev_node_unwrapped.fact := trg_active_for_current_step.right
                contradiction

              rw [h_obs_at_head_index_for_m_subs.left]
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
                . exact fact_in_trg_result
                rw [fact_is_at_its_idx]

                rw [← PreTrigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]

                apply List.existsIndexMeansInToSet
                rw [List.listElementIffToSetElement] at voc_is_in_head_atom_for_fact
                cases (List.inToSetMeansExistsIndex _ _ voc_is_in_head_atom_for_fact) with | intro voc_idx h_voc_idx =>
                  exists ⟨voc_idx.val, (by
                    rw [← PreTrigger.apply_to_function_free_atom_terms_same_length]
                    apply voc_idx.isLt
                  )⟩
                  simp only [GroundSubstitution.apply_atom, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, FunctionFreeAtom.skolemize, PreTrigger.apply_to_function_free_atom, PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const]
                  simp only [List.get_eq_getElem, List.getElem_map, head_index_for_m_subs]
                  simp only [List.get_eq_getElem] at h_voc_idx
                  rw [← h_voc_idx]
              case h_2 _ exis_f _ =>
                split
                case _ _ chosen_f_in_result applied_v_is_in_chosen_f _ =>
                  let v_from_head_atom := VarOrConst.var v_from_head_atom
                  let skolem_v := trg.val.skolemize_var_or_const head_index_for_m_subs v_from_head_atom
                  let chosen_f := Classical.choose exis_f

                  let idx_f := trg.val.idx_of_fact_in_result chosen_f result_index_for_trg chosen_f_in_result
                  let atom_in_head := (trg.val.rule.head.get head_index_for_m_subs).get idx_f
                  let idx_v_in_f := chosen_f.terms.idx_of (trg.val.apply_to_var_or_const head_index_for_m_subs v_from_head_atom) (List.listToSetElementAlsoListElement _ _ applied_v_is_in_chosen_f)
                  have idx_v_in_f_isLt := idx_v_in_f.isLt
                  have f_is_at_its_idx : chosen_f = (trg.val.mapped_head.get ⟨head_index_for_m_subs.val, by simp [PreTrigger.mapped_head, List.enum_with_lt_length_eq]⟩).get ⟨idx_f.val, by simp [PreTrigger.mapped_head, List.enum_with_lt_getElem_snd_eq_getElem]⟩ := by simp [idx_f, PreTrigger.idx_of_fact_in_result]; apply List.idx_of_get
                  have v_is_at_its_idx : (trg.val.apply_to_var_or_const head_index_for_m_subs v_from_head_atom) = chosen_f.terms.get idx_v_in_f := by simp [idx_v_in_f]; apply List.idx_of_get

                  have atom_arity_same_as_fact : chosen_f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by
                    rw [f_is_at_its_idx]
                    unfold PreTrigger.mapped_head
                    simp
                    rw [← PreTrigger.apply_to_function_free_atom_terms_same_length]
                    simp [atom_in_head, List.enum_with_lt_getElem_snd_eq_getElem]

                  let var_corresponding_to_applied_v := atom_in_head.terms.get ⟨idx_v_in_f.val, (by
                    rw [← atom_arity_same_as_fact]
                    exact idx_v_in_f_isLt
                  )⟩

                  let skolem_term_corresponding_to_applied_v := trg.val.skolemize_var_or_const head_index_for_m_subs var_corresponding_to_applied_v

                  have subs_application_is_injective_for_freshly_introduced_terms : ∀ s, trg.val.apply_to_skolemized_term skolem_v = trg.val.apply_to_var_or_const head_index_for_m_subs s -> skolem_v = trg.val.skolemize_var_or_const head_index_for_m_subs s := by
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

                    have : chosen_f.terms = (trg.val.apply_to_function_free_atom head_index_for_m_subs atom_in_head).terms := by
                      rw [f_is_at_its_idx]
                      rw [← PreTrigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]

                    simp [this, PreTrigger.apply_to_function_free_atom, var_corresponding_to_applied_v]

                  have : var_corresponding_to_applied_v = v_from_head_atom := by
                    apply VarOrConst.skolemize_injective trg.val.rule.id head_index_for_m_subs (Rule.frontier trg.val.rule)
                    apply skolemized_ts_are_equal

                  simp [var_corresponding_to_applied_v, atom_in_head] at this
                  rw [this]
  ⟩

noncomputable def inductive_homomorphism_with_prev_node (ct : ChaseTree obs kb) (m : FactSet) (m_is_model : m.modelsKb obs kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) : InductiveHomomorphismResult ct m (prev_depth + 1) :=
  let trg_ex_dec := Classical.propDecidable (exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst))
  match trg_ex_dec with
  | .isFalse _ =>
    let ⟨(prev_path, prev_hom), prev_cond⟩ := prev_result
    -- just prepending zero here as it does not really matter which index we append but the length must match
    ⟨(0::prev_path, prev_hom), by
      constructor
      . simp; exact prev_cond.left
      . have : ct.tree.get (0::prev_path) = none := by
          apply FiniteDegreeTree.children_empty_means_all_following_none
          let triggers_exist := ct.triggers_exist prev_path
          rw [prev_node_eq] at triggers_exist
          simp [Option.is_none_or] at triggers_exist
          cases triggers_exist with
          | inl _ => contradiction
          | inr hr => unfold not_exists_trigger_list at hr; exact hr.right
        rw [this]
        simp [Option.is_none_or]
    ⟩
  | .isTrue trg_ex =>
    inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex

noncomputable def inductive_homomorphism (ct : ChaseTree obs kb) (m : FactSet) (m_is_model : m.modelsKb obs kb) : (depth : Nat) ->
  InductiveHomomorphismResult ct m depth
| .zero => ⟨([], id), by
  simp [Option.is_none_or]; rw [ct.database_first]; simp
  constructor
  . unfold isIdOnConstants; intro gt ; cases gt <;> simp
  . intro el
    simp [Set.element]
    intro el_in_set
    cases el_in_set with | intro f hf =>
      apply m_is_model.left
      simp [Set.element]
      have : f = el := by have hfr := hf.right; simp [applyFact, List.map_id'] at hfr; exact hfr
      rw [this] at hf
      exact hf.left
⟩
| .succ j =>
  let ⟨(prev_path, prev_hom), prev_cond⟩ := inductive_homomorphism ct m m_is_model j
  let prev_node := ct.tree.get prev_path

  match prev_node_eq : prev_node with
  | .none =>
    -- just prepending zero here as it does not really matter which index we append but the length must match
    ⟨(0::prev_path, prev_hom), by
      constructor
      . simp; exact prev_cond.left
      . have : ct.tree.get (0::prev_path) = none := by
          apply Option.decidable_eq_none.byContradiction
          intro contra
          apply ct.tree.tree.no_orphans _ contra ⟨prev_path, by exists [0]⟩
          simp [prev_node] at prev_node_eq
          unfold FiniteDegreeTree.get at prev_node_eq
          unfold PossiblyInfiniteTree.get at prev_node_eq
          simp
          exact prev_node_eq
        rw [this]
        simp [Option.is_none_or]
    ⟩
  | .some prev_node_unwrapped =>
    inductive_homomorphism_with_prev_node ct m m_is_model j ⟨⟨prev_path, prev_hom⟩, prev_cond⟩ prev_node_unwrapped prev_node_eq
termination_by depth => depth

theorem inductive_homomorphism_with_prev_node_and_trg_path_not_empty (ct : ChaseTree obs kb) (m : FactSet) (m_is_model : m.modelsKb obs kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1 ≠ [] := by
  unfold inductive_homomorphism_with_prev_node_and_trg
  simp

theorem inductive_homomorphism_path_not_empty : ∀ n, (inductive_homomorphism ct m m_is_model (n+1)).val.1 ≠ [] := by
  intro n
  unfold inductive_homomorphism
  split
  simp
  split
  . simp
  unfold inductive_homomorphism_with_prev_node
  simp
  split
  . simp
  apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty

theorem inductive_homomorphism_with_prev_node_and_trg_path_extends_prev (ct : ChaseTree obs kb) (m : FactSet) (m_is_model : m.modelsKb obs kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1 = ((inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1.head (by apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty)) :: prev_result.val.fst := by
  conv => left; rw [List.head_cons_tail _ (inductive_homomorphism_with_prev_node_and_trg_path_not_empty ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex)]
  simp
  unfold inductive_homomorphism_with_prev_node_and_trg
  simp

theorem inductive_homomorphism_path_extends_prev {ct : ChaseTree obs kb} : ∀ n, (inductive_homomorphism ct m m_is_model (n+1)).val.1 = ((inductive_homomorphism ct m m_is_model (n+1)).val.1.head (by apply inductive_homomorphism_path_not_empty)) :: (inductive_homomorphism ct m m_is_model n).val.1 := by
  intro n
  conv => left; rw [List.head_cons_tail _ (inductive_homomorphism_path_not_empty n)]
  simp
  conv => left; unfold inductive_homomorphism
  split
  case _ prev_path _ _ heq =>
    have : prev_path = (inductive_homomorphism ct m m_is_model n).val.1 := by rw [heq]
    simp
    split
    . simp; exact this
    unfold inductive_homomorphism_with_prev_node
    simp
    split
    . simp; exact this
    unfold inductive_homomorphism_with_prev_node_and_trg
    simp; exact this

theorem inductive_homomorphism_path_extends_all_prev {ct : ChaseTree obs kb} : ∀ n d, (inductive_homomorphism ct m m_is_model (n+d)).val.1 = ((inductive_homomorphism ct m m_is_model (n+d)).val.1.take d) ++ (inductive_homomorphism ct m m_is_model n).val.1 := by
  intro n d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc]
    rw [inductive_homomorphism_path_extends_prev (n+d)]
    simp
    exact ih

theorem inductive_homomorphism_with_prev_node_and_trg_latest_index_lt_trg_result_length
  {ct : ChaseTree obs kb}
  (prev_step : Nat)
  (prev_node : ChaseNode obs kb.rules)
  (prev_ex : some prev_node = ct.tree.get (inductive_homomorphism ct m m_is_model prev_step).val.1)
  (trg_ex : exists_trigger_list obs kb.rules prev_node (ct.tree.children (inductive_homomorphism ct m m_is_model prev_step).val.1))
  : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_step _ _ (Eq.symm prev_ex) trg_ex).val.1.head (by apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty) < (Classical.choose trg_ex).val.result.length := by
    let prev_result := inductive_homomorphism ct m m_is_model prev_step
    let prev_hom := prev_result.val.snd
    let prev_cond := prev_result.property
    have prev_hom_is_homomorphism : isHomomorphism prev_hom prev_node.fact m := by
      have prev_cond_r := prev_cond.right
      simp only [prev_result] at prev_cond_r
      rw [← prev_ex] at prev_cond_r
      simp [Option.is_none_or] at prev_cond_r
      exact prev_cond_r

    let trg := Classical.choose trg_ex
    let trg_spec := Classical.choose_spec trg_ex
    let trg_active_for_current_step := trg_spec.left

    let trg_variant_for_m : RTrigger obs kb.rules := {
      val := {
        rule := trg.val.rule
        subs := fun t => prev_hom (trg.val.subs t)
      }
      property := trg.property
    }
    have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
      have : trg_variant_for_m.val.loaded (applyFactSet prev_hom prev_node.fact) := by
        apply PreTrigger.term_mapping_preserves_loadedness
        . exact prev_hom_is_homomorphism.left
        . exact trg_active_for_current_step.left
      apply Set.subsetTransitive
      exact ⟨this, prev_hom_is_homomorphism.right⟩
    have trg_variant_obsolete_on_m : obs.cond trg_variant_for_m.val m := by
      have m_models_trg : m.modelsRule obs trg_variant_for_m.val.rule := by exact m_is_model.right trg.val.rule trg.property
      unfold FactSet.modelsRule at m_models_trg
      apply m_models_trg
      constructor
      rfl
      apply trg_variant_loaded_for_m

    let h_obs_for_m_subs := Classical.choose_spec (obs.cond_implies_trg_is_satisfied trg_variant_obsolete_on_m)
    let head_index_for_m_subs := Classical.choose h_obs_for_m_subs

    have : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_step (inductive_homomorphism ct m m_is_model prev_step) prev_node (by rw [prev_ex]) trg_ex).val.fst = head_index_for_m_subs.val :: prev_result.val.fst := by
      unfold inductive_homomorphism_with_prev_node_and_trg
      simp [head_index_for_m_subs]
    simp [this]
    have isLt := head_index_for_m_subs.isLt
    simp only [trg_variant_for_m, trg] at isLt
    unfold PreTrigger.result
    simp only [PreTrigger.head_length_eq_mapped_head_length] at isLt
    simp
    exact isLt

theorem inductive_homomorphism_latest_index_lt_trg_result_length
  {ct : ChaseTree obs kb}
  (prev_step : Nat)
  (prev_node : ChaseNode obs kb.rules)
  (prev_ex : some prev_node = ct.tree.get (inductive_homomorphism ct m m_is_model prev_step).val.1)
  (trg_ex : exists_trigger_list obs kb.rules prev_node (ct.tree.children (inductive_homomorphism ct m m_is_model prev_step).val.1))
  : (inductive_homomorphism ct m m_is_model (prev_step+1)).val.1.head (by apply inductive_homomorphism_path_not_empty) < (Classical.choose trg_ex).val.result.length := by

    have : inductive_homomorphism ct m m_is_model (prev_step + 1) = inductive_homomorphism_with_prev_node ct m m_is_model prev_step (inductive_homomorphism ct m m_is_model prev_step) prev_node (by rw [prev_ex]) := by
      conv => left; unfold inductive_homomorphism
      simp
      split
      case h_1 heq => rw [heq] at prev_ex; contradiction
      case h_2 heq =>
        rw [heq] at prev_ex
        injection prev_ex with prev_ex
        simp [← prev_ex]
    simp [this]

    have : inductive_homomorphism_with_prev_node ct m m_is_model prev_step (inductive_homomorphism ct m m_is_model prev_step) prev_node (by rw [prev_ex]) = inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_step (inductive_homomorphism ct m m_is_model prev_step) prev_node (Eq.symm prev_ex) trg_ex := by
      conv => left; unfold inductive_homomorphism_with_prev_node
      simp
      split
      case h_1 _ h _ => apply False.elim; apply h; apply trg_ex
      case h_2 => simp
    simp [this]

    apply inductive_homomorphism_with_prev_node_and_trg_latest_index_lt_trg_result_length
    exact prev_ex

theorem inductive_homomorphism_tree_get_path_none_means_layer_empty {ct : ChaseTree obs kb} : ∀ n, ct.tree.get (inductive_homomorphism ct m m_is_model (n+1)).val.fst = none -> ct.tree.children (inductive_homomorphism ct m m_is_model n).val.fst = [] := by
  intro n succ_none
  unfold inductive_homomorphism at succ_none
  simp at succ_none
  split at succ_none
  . simp at succ_none; apply ct.tree.first_child_none_means_children_empty; exact succ_none
  case h_2 _ heq =>
    unfold inductive_homomorphism_with_prev_node at succ_none
    simp at succ_none
    split at succ_none
    . simp at succ_none; apply ct.tree.first_child_none_means_children_empty; exact succ_none
    case h_2 _ ex _ =>
      let child_index : Fin (ct.tree.children (inductive_homomorphism ct m m_is_model n).val.fst).length := ⟨
        (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model n _ _ heq ex).val.1.head (by apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty),
        by
          let trg_spec := Classical.choose_spec ex
          rw [← trg_spec.right]
          simp
          rw [List.enum_with_lt_length_eq]
          apply inductive_homomorphism_with_prev_node_and_trg_latest_index_lt_trg_result_length
          rw [heq]
      ⟩

      let child := (ct.tree.children (inductive_homomorphism ct m m_is_model n).val.fst)[child_index.val]
      have : some child = ct.tree.get (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model n _ _ heq ex).val.fst := by
        simp only [child]
        rw [ct.tree.getElem_children_eq_get_tree _ child_index]
        have : child_index.val :: (inductive_homomorphism ct m m_is_model n).val.fst = (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model n _ _ heq ex).val.fst := by rw [inductive_homomorphism_with_prev_node_and_trg_path_extends_prev]
        rw [this]

      rw [← this] at succ_none
      contradiction

theorem inductive_homomorphism_same_on_terms_in_next_step (ct : ChaseTree obs kb) (m : FactSet) (m_is_model : m.modelsKb obs kb) : ∀ i, (ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst).is_none_or (fun node => ∀ f t, f ∈ node.fact ∧ t ∈ f.terms.toSet -> (inductive_homomorphism ct m m_is_model i).val.snd t = (inductive_homomorphism ct m m_is_model i.succ).val.snd t) := by
  intro i
  cases eq : ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst with
  | none => simp [Option.is_none_or]
  | some node =>
    intro f t precondition
    conv => rhs; unfold inductive_homomorphism; simp
    split
    case h_1 _ => simp
    case h_2 heq =>
      unfold inductive_homomorphism_with_prev_node
      simp
      split
      . simp
      . unfold inductive_homomorphism_with_prev_node_and_trg
        simp
        split
        case h_1 c =>
          have property := (inductive_homomorphism ct m m_is_model i).property.right
          rw [eq] at property; simp [Option.is_none_or] at property
          exact property.left (GroundTerm.const c)
        case h_2 ft =>
          split
          case h_1 _ ex_f _ => rfl
          case h_2 _ n_ex_f _ =>
            apply False.elim; apply n_ex_f; exists f; constructor
            . rw [heq] at eq; injection eq with eq; rw [eq]; exact precondition.left
            . exact precondition.right

theorem inductive_homomorphism_same_on_all_following_terms (ct : ChaseTree obs kb) (m : FactSet) (m_is_model : m.modelsKb obs kb) : ∀ i, (ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst).is_none_or (fun node => ∀ j f t, f ∈ node.fact ∧ t ∈ f.terms.toSet -> (inductive_homomorphism ct m m_is_model i).val.snd t = (inductive_homomorphism ct m m_is_model (i+j)).val.snd t) := by
  intro i
  cases eq : ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst with
  | none => simp [Option.is_none_or]
  | some node =>
    intro j f t
    induction j with
    | zero => intros; rfl
    | succ j ih =>
      intro precond
      rw [ih precond]
      have next_step := inductive_homomorphism_same_on_terms_in_next_step ct m m_is_model (i + j)
      cases eq2 : ct.tree.get (inductive_homomorphism ct m m_is_model (i+j)).val.fst with
      | none =>
        conv => right; unfold inductive_homomorphism
        simp
        split
        case h_1 _ => simp
        case h_2 heq => rw [heq] at eq2; contradiction
      | some node2 =>
        rw [eq2] at next_step; simp [Option.is_none_or] at next_step
        specialize next_step f t
        apply next_step
        . have subset_following := chaseTreeSetIsSubsetOfAllFollowing ct (inductive_homomorphism ct m m_is_model i).val.fst ((inductive_homomorphism ct m m_is_model (i+j)).val.fst.take j)
          rw [eq] at subset_following
          simp at subset_following
          rw [← inductive_homomorphism_path_extends_all_prev i j] at subset_following
          rw [eq2] at subset_following
          simp [Option.is_none_or] at subset_following
          apply subset_following
          exact precond.left
        . exact precond.right

theorem chaseBranchResultModelsKb (cb : ChaseBranch obs kb) : cb.result.modelsKb obs kb := by
  constructor
  . unfold FactSet.modelsDb
    unfold ChaseBranch.result
    intro f h
    exists 0
    rw [cb.database_first]
    simp [Option.is_some_and]
    exact h
  . unfold FactSet.modelsRules
    intro r h
    unfold FactSet.modelsRule
    simp
    intro trg trg_rule trg_loaded
    apply Classical.byContradiction
    intro trg_not_obsolete
    cases (trgActiveForChaseResultMeansActiveAtSomeIndex cb trg ⟨trg_loaded, trg_not_obsolete⟩) with | intro i active_i =>
      have not_active_eventually := cb.fairness ⟨trg, by rw [← trg_rule] at h; apply h⟩
      cases not_active_eventually with | intro j not_active =>
        have not_active_j := not_active.left
        simp [Trigger.active] at not_active_j
        unfold Option.is_some_and at not_active_j
        split at not_active_j
        . contradiction
        case h_2 heq =>
          have obsolete_j := not_active_j (by
            simp [PreTrigger.loaded]
            unfold Option.is_some_and at active_i
            cases eq : cb.branch.infinite_list i with
            | none => rw [eq] at active_i; simp at active_i
            | some step_i =>
              rw [eq] at active_i; simp at active_i
              apply Set.subsetTransitive
              constructor
              . apply active_i.left
              . cases Decidable.em (i ≤ j) with
                | inl j_ge_i =>
                  cases Nat.le.dest j_ge_i with | intro m hm =>
                    have step_i_subs_following := chaseBranchSetIsSubsetOfAllFollowing cb i m
                    rw [eq] at step_i_subs_following
                    simp at step_i_subs_following
                    rw [hm, heq] at step_i_subs_following
                    simp [Option.is_none_or] at step_i_subs_following
                    exact step_i_subs_following
                | inr h =>
                  have h : j < i := Nat.lt_of_not_le h
                  have contra := not_active.right i h
                  rw [eq] at contra
                  simp [Option.is_none_or] at contra
                  contradiction
          )
          apply trg_not_obsolete
          apply obs.monotone
          have step_j_subs_result := chaseBranchSetIsSubsetOfResult cb j
          rw [heq] at step_j_subs_result
          simp [Option.is_none_or] at step_j_subs_result
          exact step_j_subs_result
          exact obsolete_j

theorem chaseTreeResultModelsKb (ct : ChaseTree obs kb) : ∀ fs, fs ∈ ct.result -> fs.modelsKb obs kb := by
  intro fs is_result
  unfold Set.element at is_result
  unfold ChaseTree.result at is_result
  cases is_result with | intro branch h =>
    rw [← h.right]
    apply chaseBranchResultModelsKb

theorem chaseTreeResultIsUniversal (ct : ChaseTree obs kb) : ∀ m, m.modelsKb obs kb -> ∃ (fs : FactSet) (h : GroundTermMapping), fs ∈ ct.result ∧ isHomomorphism h fs m := by
  intro m m_is_model

  let inductive_homomorphism_shortcut := inductive_homomorphism ct m m_is_model

  let indices : InfiniteList Nat := fun n => (inductive_homomorphism_shortcut (n + 1)).val.1.head (by apply inductive_homomorphism_path_not_empty)

  have indices_aux_result : ∀ n, (indices.take n).reverse = (inductive_homomorphism_shortcut n).val.1 := by
    intro n
    induction n with
    | zero =>
      simp [inductive_homomorphism_shortcut]
      unfold inductive_homomorphism
      unfold InfiniteList.take
      simp
    | succ n ih =>
      unfold InfiniteList.take
      rw [List.reverse_append]
      simp
      rw [inductive_homomorphism_path_extends_prev]
      simp
      exact ih

  let path : Nat -> Option (ChaseNode obs kb.rules) := fun n => (ct.tree.get (inductive_homomorphism_shortcut n).val.1)
  let nodes : PossiblyInfiniteList (ChaseNode obs kb.rules) := {
    infinite_list := path
    no_holes := by
      intro n path_not_none m
      simp only [path]
      simp only [path] at path_not_none
      unfold FiniteDegreeTree.get at path_not_none
      unfold PossiblyInfiniteTree.get at path_not_none
      have no_orphans := ct.tree.tree.no_orphans
        (inductive_homomorphism_shortcut n).val.1
        path_not_none
        ⟨(inductive_homomorphism_shortcut m).val.1, by
          exists ((indices.skip m).take (n - m)).reverse
          rw [← indices_aux_result m]
          rw [← List.reverse_append]
          rw [InfiniteList.combine_skip_take]
          exact indices_aux_result n
        ⟩
      exact no_orphans
  }
  let branch : ChaseBranch obs kb := {
    branch := nodes
    database_first := by
      simp only [nodes, path, inductive_homomorphism_shortcut]
      unfold inductive_homomorphism
      simp
      rw [ct.database_first]
    triggers_exist := by
      intro n
      cases eq : nodes.infinite_list n with
      | none => simp [Option.is_none_or]
      | some node =>
        simp [Option.is_none_or]
        simp only [nodes, path]
        simp only [nodes, path] at eq
        have ex_trg := ct.triggers_exist (inductive_homomorphism_shortcut n).val.1
        rw [eq] at ex_trg
        simp [Option.is_none_or] at ex_trg
        cases ex_trg with
        | inl ex_trg =>
          apply Or.inl
          unfold exists_trigger_opt_fs
          unfold exists_trigger_list at ex_trg
          let trg := Classical.choose ex_trg
          let h := Classical.choose_spec ex_trg
          exists trg
          constructor
          . exact h.left
          let i : Fin trg.val.result.length := ⟨((inductive_homomorphism_shortcut (n+1)).val.fst.head (inductive_homomorphism_path_not_empty n)), inductive_homomorphism_latest_index_lt_trg_result_length n node (by rw [← eq]) ex_trg⟩
          let i' : Fin (ct.tree.children (inductive_homomorphism_shortcut n).val.1).length := ⟨i.val, by rw [← h.right]; simp; rw [List.enum_with_lt_length_eq]; exact i.isLt⟩
          have i_lt_helper : i.val < trg.val.result.enum_with_lt.length := by rw [List.enum_with_lt_length_eq]; exact i.isLt
          simp only [i, trg] at i_lt_helper
          exists i
          rw [inductive_homomorphism_path_extends_prev]
          rw [← ct.tree.getElem_children_eq_get_tree _ i']
          simp only [← h.right]
          simp
          constructor
          . simp only [List.getElem_attach _ _ i_lt_helper]; rw [List.enum_with_lt_getElem_snd_eq_getElem]
          . simp only [List.getElem_attach _ _ i_lt_helper]; rw [List.enum_with_lt_getElem_fst_eq_index]
        | inr ex_trg =>
          apply Or.inr
          unfold not_exists_trigger_opt_fs
          unfold not_exists_trigger_list at ex_trg
          constructor
          . exact ex_trg.left
          rw [inductive_homomorphism_path_extends_prev]
          apply ct.tree.children_empty_means_all_following_none
          exact ex_trg.right
    fairness := by
      intro trg
      cases Classical.em (∃ n : Nat, nodes.infinite_list n ≠ none ∧ ∀ m : Nat, m > n -> nodes.infinite_list m = none) with
      | inl h =>
        cases h with | intro n hn =>
          exists n
          cases eq : nodes.infinite_list n with
          | none => rw [eq] at hn; simp at hn
          | some node =>
            simp [Option.is_some_and]
            constructor
            . apply ct.fairness_leaves
              unfold FiniteDegreeTree.leaves
              unfold PossiblyInfiniteTree.leaves
              simp only [Set.element]
              exists (inductive_homomorphism_shortcut n).val.fst
              constructor
              . simp only [nodes, path] at eq; exact eq
              . unfold PossiblyInfiniteList.empty
                unfold PossiblyInfiniteTree.children
                unfold InfiniteTreeSkeleton.children
                simp
                apply funext
                have next_none := hn.right (n+1) (by simp)
                have children_empty := inductive_homomorphism_tree_get_path_none_means_layer_empty n next_none
                have all_none := ct.tree.children_empty_means_all_following_none _ children_empty
                unfold FiniteDegreeTree.get at all_none
                unfold PossiblyInfiniteTree.get at all_none
                exact all_none
            . intro m hm
              have m_eq := hn.right m hm
              simp only [nodes] at m_eq
              rw [m_eq]
              simp [Option.is_none_or]
      | inr h =>
        have h : ¬ ∃ n : Nat, nodes.infinite_list n = none := by
          simp at h
          simp
          intro n
          induction n with
          | zero => simp [path, inductive_homomorphism_shortcut, inductive_homomorphism]; rw [ct.database_first]; simp
          | succ n ih =>
            specialize h n ih
            cases h with | intro m hm =>
              intro contra
              have no_holes := nodes.no_holes m
              simp only [nodes] at no_holes
              specialize no_holes hm.right
              cases Decidable.em ((n+1) = m) with
              | inl eq => rw [eq] at contra; have contra' := hm.right; contradiction
              | inr neq =>
                let n_succ_fin_m : Fin m := ⟨n+1, by apply Nat.lt_of_le_of_ne; apply Nat.succ_le_of_lt; exact hm.left; exact neq⟩
                specialize no_holes n_succ_fin_m
                contradiction
        cases ct.fairness_infinite_branches trg with | intro i hi =>
          exists i
          cases eq : nodes.infinite_list i with
          | none => apply False.elim; apply h; exists i
          | some node =>
            constructor
            . simp [Option.is_some_and]
              specialize hi ((inductive_homomorphism_shortcut i).val.1) (by rw [(inductive_homomorphism_shortcut i).property.left]; simp)
              simp only [nodes, path] at eq
              rw [eq] at hi
              simp [Option.is_none_or] at hi
              exact hi
            . intro j hj
              specialize hi ((inductive_homomorphism_shortcut j).val.1) (by rw [(inductive_homomorphism_shortcut j).property.left]; apply Nat.le_of_lt; apply hj)
              simp only [nodes, path]
              exact hi
  }
  let result := branch.result

  let global_h : GroundTermMapping := fun t =>
    let dec := Classical.propDecidable (∃ f, f ∈ result ∧ t ∈ f.terms.toSet)
    match dec with
      | Decidable.isTrue p =>
        let hfl := (Classical.choose_spec p).left
        let i := Classical.choose hfl
        let target_h := (inductive_homomorphism_shortcut i).val.2
        target_h t
      | Decidable.isFalse _ => t

  have : ∀ i, (branch.branch.infinite_list i).is_none_or (fun chase_node => ∀ f, f ∈ chase_node.fact -> applyFact global_h f = applyFact (inductive_homomorphism_shortcut i).val.snd f) := by
    intro i
    cases eq : branch.branch.infinite_list i with
    | none => simp [Option.is_none_or]
    | some node =>
      simp [Option.is_none_or]
      intro f f_in_node
      unfold applyFact
      simp [global_h]
      intro t t_in_f
      split
      case h_2 _ n_ex _ =>
        apply False.elim
        apply n_ex
        exists f
        constructor
        . have subset_result := chaseBranchSetIsSubsetOfResult branch i
          rw [eq] at subset_result; simp [Option.is_none_or] at subset_result
          apply subset_result
          exact f_in_node
        . rw [← List.listElementIffToSetElement]; exact t_in_f
      case h_1 _ ex _ =>
        let j := Classical.choose (Classical.choose_spec ex).left
        let j_spec := Classical.choose_spec (Classical.choose_spec ex).left
        cases Nat.le_total i j with
        | inl i_le_j =>
          have j_is_i_plus_k := Nat.le.dest i_le_j
          cases j_is_i_plus_k with | intro k hk =>
            simp [j] at hk
            rw [← hk]
            apply Eq.symm
            simp only [inductive_homomorphism_shortcut]
            have same_all_following := inductive_homomorphism_same_on_all_following_terms ct m m_is_model i
            simp only [branch, path, inductive_homomorphism_shortcut] at eq
            rw [eq] at same_all_following; simp [Option.is_none_or] at same_all_following
            apply same_all_following
            exact f_in_node
            rw [← List.listElementIffToSetElement]; exact t_in_f
        | inr j_le_i =>
          have i_is_j_plus_k := Nat.le.dest j_le_i
          cases i_is_j_plus_k with | intro k hk =>
            rw [← hk]
            simp only [inductive_homomorphism_shortcut]
            have same_all_following := inductive_homomorphism_same_on_all_following_terms ct m m_is_model j
            cases eq2 : branch.branch.infinite_list j with
            | none => rw [eq2] at j_spec; simp [Option.is_some_and] at j_spec
            | some _ =>
              rw [eq2] at j_spec; simp [Option.is_some_and] at j_spec
              simp only [branch, path, inductive_homomorphism_shortcut] at eq2
              rw [eq2] at same_all_following; simp [Option.is_none_or] at same_all_following
              apply same_all_following
              exact j_spec
              exact (Classical.choose_spec ex).right

  exists result
  exists global_h
  constructor
  . unfold ChaseTree.result
    unfold Set.element
    simp
    exists branch
    simp [result]
    unfold ChaseTree.branches
    unfold FiniteDegreeTree.branches
    unfold PossiblyInfiniteTree.branches
    unfold InfiniteTreeSkeleton.branches
    unfold Set.element
    simp
    exists indices
    intro n
    simp only [path]
    rw [indices_aux_result]
    unfold FiniteDegreeTree.get
    unfold PossiblyInfiniteTree.get
    rfl
  . constructor
    . intro gt
      split
      case h_1 _ c =>
        simp [global_h]
        split
        case h_1 _ p _ =>
          let hfl := (Classical.choose_spec p).left
          let i := Classical.choose hfl
          let i_spec := Classical.choose_spec hfl
          have property := (inductive_homomorphism_shortcut i).property.right
          simp only [branch, path] at i_spec
          cases eq : ct.tree.get (inductive_homomorphism_shortcut i).val.fst with
          | none => rw [eq] at i_spec; simp [Option.is_some_and] at i_spec
          | some node =>
            rw [eq] at property; simp [Option.is_none_or] at property
            exact property.left (GroundTerm.const c)
        . trivial
      . trivial
    . intro f hf
      simp only [result] at hf
      unfold ChaseBranch.result at hf
      unfold Set.element at hf
      unfold applyFactSet at hf
      cases hf with | intro e he =>
        let ⟨hel, her⟩ := he
        simp [Set.element] at hel
        cases hel with | intro n hn =>
          rw [← her]
          specialize this n
          simp only [branch] at this
          cases eq : path n with
          | none => rw [eq] at hn; simp [Option.is_some_and] at hn
          | some node =>
            rw [eq] at hn; simp [Option.is_some_and] at hn
            rw [eq] at this; simp [Option.is_none_or] at this
            specialize this e hn
            rw [this]
            have property := (inductive_homomorphism_shortcut n).property.right
            simp only [path] at eq
            rw [eq] at property; simp [Option.is_none_or] at property
            have : applyFactSet (inductive_homomorphism_shortcut n).val.snd node.fact ⊆ m := property.right
            unfold Set.subset at this
            apply this
            simp [Set.element, applyFactSet]
            exists e

-- TODO: universality result for special case of rules without disjunctions

