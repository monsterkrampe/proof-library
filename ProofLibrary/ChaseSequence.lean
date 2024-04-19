import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.Trigger
import ProofLibrary.Logic

def InfiniteList (α : Type u) := Nat → α  

structure ChaseSequence (kb : KnowledgeBase) where
  fact_sets : InfiniteList FactSet
  database_first : fact_sets 0 = kb.db
  triggers_exist : ∀ n : Nat, (
      ∃ trg : (RTrigger kb.rules), trg.val.ractive (fact_sets n) ∧ trg.val.result ∪ fact_sets n = fact_sets (n + 1)
    ) ∨ (
      ¬(∃ trg : (RTrigger kb.rules), trg.val.ractive (fact_sets n)) ∧ fact_sets n = fact_sets (n + 1)
    )
  fairness : ∀ (trg : (RTrigger kb.rules)) (i : Nat), (trg.val.ractive (fact_sets i)) → ∃ j : Nat, j ≥ i ∧ (¬ trg.val.ractive (fact_sets j))

namespace ChaseSequence
  def result {kb : KnowledgeBase} (cs : ChaseSequence kb) : FactSet := fun f => ∃ n : Nat, f ∈ cs.fact_sets n

  def terminates {kb : KnowledgeBase} (cs : ChaseSequence kb) : Prop :=
    ∃ n : Nat, cs.fact_sets n = cs.fact_sets (n + 1)
end ChaseSequence

theorem chaseSequenceSetIsSubsetOfNext (kb : KnowledgeBase) (cs : ChaseSequence kb) : ∀ n : Nat, cs.fact_sets n ⊆ cs.fact_sets (n+1) := by
  intro n f h
  cases cs.triggers_exist n 
  case inl g =>
    cases g with | intro trg trgH => 
      rw [← trgH.right]
      simp [Set.element, Set.union]
      apply Or.inr
      exact h
  case inr g =>
    rw [← g.right]
    simp [Set.element, Set.union]
    exact h
 
theorem chaseSequenceSetIsSubsetOfAllFollowing (kb : KnowledgeBase) (cs : ChaseSequence kb) : ∀ (n m : Nat), cs.fact_sets n ⊆ cs.fact_sets (n + m) := by
  intro n m
  induction m
  simp
  intro f h 
  exact h 
  intro f h 
  case succ i ih =>
    apply chaseSequenceSetIsSubsetOfNext kb cs (n + i)
    apply ih f
    exact h 

theorem chaseSequenceSetIsSubsetOfResult (kb : KnowledgeBase) (cs : ChaseSequence kb) : ∀ n : Nat, cs.fact_sets n ⊆ cs.result := by 
  intro n 
  intro e 
  intro inSet 
  simp [ChaseSequence.result, Set.element]
  exists n 

theorem trgLoadedForChaseResultMeansLoadedAtSomeIndex (kb : KnowledgeBase) (cs : ChaseSequence kb) : ∀ trg : Trigger, trg.loaded cs.result -> ∃ n : Nat, trg.loaded (cs.fact_sets n) := by
  intro trg 
  simp [ChaseSequence.result, Trigger.loaded]

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
          case inl h => simp [h]
          case inr h => apply Nat.le_of_lt; apply Nat.lt_of_succ_le; rw [← Nat.not_le_eq]; exact h
        have help_i : i ≤ Nat.max i j := by apply max_help_left
        have help_j : j ≤ Nat.max i j := by apply max_help_right
        
        constructor 
        apply Set.subsetTransitive _ (cs.fact_sets i) _
        constructor 
        intro e he 
        simp [Set.element] at he 
        rw [he]
        assumption
        cases Nat.le.dest help_i with | intro m hm => rw [← hm]; apply chaseSequenceSetIsSubsetOfAllFollowing kb cs i m
        cases Nat.le.dest help_j with | intro m hm => 
          rw [← hm]
          apply Set.subsetTransitive
          constructor
          apply hj
          apply chaseSequenceSetIsSubsetOfAllFollowing kb cs j m 

theorem trgRActiveForChaseResultMeansRActiveAtSomeIndex (kb : KnowledgeBase) (cs : ChaseSequence kb) : ∀ trg : Trigger, trg.ractive cs.result -> ∃ n : Nat, trg.ractive (cs.fact_sets n) := by 
  intro trg
  simp [ChaseSequence.result, Trigger.ractive]
  intro loaded ractive
  have trgLoadedForN := trgLoadedForChaseResultMeansLoadedAtSomeIndex kb cs trg loaded 
  cases trgLoadedForN with | intro n loadedN => 
    exists n 
    constructor 
    exact loadedN
    intro contra 
    cases contra with | intro s rActiveS => 
      have ractiveForall := notExistsToForall ractive 
      cases implToNotOr (notAndDeMorgan (ractiveForall s))
      case inl _ => have rActiveSLeft := rActiveS.left; contradiction
      case inr contra => 
        have rActiveSRight := rActiveS.right 
        have actualContra := Set.subsetTransitive _ _ _ (And.intro rActiveSRight (chaseSequenceSetIsSubsetOfResult kb cs n))
        contradiction

theorem rObsoletenessSubsetMonotone {trg : Trigger} {F G : FactSet} : F ⊆ G ∧ trg.robsolete F -> trg.robsolete G := by 
  intro ⟨sub, robsF⟩ 
  simp [Trigger.robsolete] at * 
  cases robsF with | intro s hs => 
    exists s 
    constructor 
    exact hs.left 
    apply Set.subsetTransitive 
    constructor 
    exact hs.right 
    exact sub 

theorem funcTermForExisVarInChaseMeansTriggerIsUsed (kb : KnowledgeBase) (cs : ChaseSequence kb) (trg : RTrigger kb.rules) (var : Variable) (i : Nat) : (trg.val.rule.frontier.elem var = false) ∧ (∃ f: Fact, f ∈ cs.fact_sets i ∧ ((trg.val.apply_to_var_or_const (VarOrConst.var var)) ∈ f.terms.toSet)) -> ∃ j, j ≤ i ∧ trg.val.result ∪ cs.fact_sets (j-1) = cs.fact_sets j := by 
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
          case inr => contradiction
          case inl _ _ all_terms_ff =>
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
          have : ∃ f, f ∈ Trigger.result trg'.val ∧ (trg.val.apply_to_var_or_const (VarOrConst.var var)) ∈ List.toSet f.terms := by 
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
          
          have : ∃ var2, trg'.val.rule.frontier.elem var2 = false ∧ (trg.val.apply_to_var_or_const (VarOrConst.var var)) = (trg'.val.apply_to_var_or_const (VarOrConst.var var2)) := by 
            cases this with | intro f hf =>
              have ⟨f_in_res, apply_var_in_f_terms⟩ := hf
              let i := trg'.val.idx_of_fact_in_result f f_in_res
              let atom_for_f := trg'.val.rule.head.get i

              cases List.inToSetMeansExistsIndex _ _ apply_var_in_f_terms with | intro k hk =>
                have f_is_at_its_idx : f = trg'.val.mapped_head.get ⟨i.val, by simp [Trigger.mapped_head]⟩ := by simp [i, Trigger.idx_of_fact_in_result]; apply List.idx_of_get

                have atom_arity_same_as_fact : f.terms.length = List.length (FunctionFreeAtom.terms atom_for_f) := by 
                  rw [f_is_at_its_idx]
                  unfold Trigger.mapped_head
                  unfold Trigger.apply_to_function_free_atom
                  rw [List.get_map]
                  simp

                let term_for_f := atom_for_f.terms.get ⟨k.val, (by 
                  rw [← atom_arity_same_as_fact]
                  exact k.isLt
                )⟩

                -- TODO: this is similar to stuff going on around line 590; check if we can unify
                have : (trg'.val.apply_to_var_or_const term_for_f) = f.terms.get k := by 
                  have : f.terms = (trg'.val.apply_to_function_free_atom atom_for_f).terms := by
                    conv => lhs; rw [f_is_at_its_idx]
                    rw [← Trigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]
                  rw [List.get_eq_of_eq this]
                  simp [Trigger.apply_to_function_free_atom, List.get_map]

                have : (trg.val.apply_to_var_or_const (VarOrConst.var var)) = (trg'.val.apply_to_var_or_const term_for_f) := by 
                  rw [← this] at hk
                  exact hk

                cases eq_term_for_f : term_for_f with 
                | const c => 
                  rw [eq_term_for_f] at this
                  simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var_not_in_frontier] at this
                  contradiction
                | var var_for_f =>
                  exists var_for_f
                  have var_for_f_not_in_frontier : trg'.val.rule.frontier.elem var_for_f = false := by 
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
                        unfold Trigger.mapped_body
                        simp [SubsTarget.apply]
                        unfold GroundSubstitution.apply_function_free_conj
                        apply List.mappedElemInMappedList
                        apply h_body_atom_for_f.left
                      . simp [SubsTarget.apply, GroundSubstitution.apply_function_free_atom]
                        simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const] at this
                        rw [this]
                        simp [GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, h]
                        apply List.existsIndexMeansInToSet
                        cases (List.inToSetMeansExistsIndex _ _ h_body_atom_for_f.right) with | intro l h_l =>
                          exists ⟨l, (by rw [List.length_map]; exact l.isLt)⟩
                          simp [List.get_map]
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
            unfold Trigger.mapped_head
            rw [← this.left]
            apply List.map_eq_map_if_functions_eq
            intro a _
            unfold Trigger.apply_to_function_free_atom
            simp
            apply List.map_eq_map_if_functions_eq
            intro voc hvoc
            cases voc with 
            | const c => simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] 
            | var v =>
              cases Decidable.em (trg.val.rule.frontier.elem v) with 
              | inl v_in_frontier => 
                simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term]
                rw [← this.left]
                simp [VarOrConst.skolemize, v_in_frontier]
                apply this.right
                apply List.listElementAlsoToSetElement
                apply v_in_frontier
              | inr v_not_in_frontier => 
                simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term]
                rw [← this.left]
                simp [VarOrConst.skolemize, v_not_in_frontier]
                apply congrArg
                rw [← FiniteTreeList.eqIffFromListEq]
                apply List.map_eq_map_if_functions_eq
                intro w hw
                rw [← this.right w]
                exact hw

          have : trg.val.result = trg'.val.result := by 
            unfold Trigger.result 
            rw [this]
          rw [this]
          exact h_trg'.right

theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (kb : KnowledgeBase) (cs : ChaseSequence kb) (trg : RTrigger kb.rules) (var : Variable) (i : Nat) : (trg.val.rule.frontier.elem var = false) ∧ (∃ f: Fact, f ∈ cs.fact_sets i ∧ (trg.val.apply_to_var_or_const (VarOrConst.var var)) ∈ f.terms.toSet) -> trg.val.result ⊆ cs.fact_sets i := by 
  intro h 
  cases funcTermForExisVarInChaseMeansTriggerIsUsed kb cs trg var i h with | intro j hj =>
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
  def terminates (kb : KnowledgeBase) : Prop :=
    ∃ cs : ChaseSequence kb, cs.terminates

  def universally_terminates (kb : KnowledgeBase) : Prop :=
    ∀ cs : ChaseSequence kb, cs.terminates
end KnowledgeBase

noncomputable def inductive_homomorphism (kb : KnowledgeBase) (cs : ChaseSequence kb) (m : FactSet) (mIsModel : m.modelsKb kb) : (i : Nat) -> { hom : GroundTermMapping // isHomomorphism hom (cs.fact_sets i) m }
| .zero => ⟨id, (by 
  constructor 
  unfold isIdOnConstants ; intro gt ; cases gt <;> simp
  rw [cs.database_first]
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
  let prev_hom := inductive_homomorphism kb cs m mIsModel j
  let trg_ex_dec := Classical.propDecidable (∃ trg : (RTrigger kb.rules), trg.val.ractive (cs.fact_sets j) ∧ trg.val.result ∪ cs.fact_sets j = cs.fact_sets (j + 1))
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
    let ⟨trg_act, trg_res⟩ := Classical.choose_spec trg_ex
    let trg_on_m : RTrigger kb.rules := {
      val := {
        rule := trg.val.rule
        subs := fun t => prev_hom.val (trg.val.subs t)
      }
      property := trg.property
    }

    have trg_loaded_for_m : trg_on_m.val.loaded m := by 
      have : trg_on_m.val.loaded (applyFactSet prev_hom (cs.fact_sets j)) := by 
        apply Trigger.term_mapping_preserves_loadedness
        exact prev_hom.property.left
        exact trg_act.left
      apply Set.subsetTransitive
      exact ⟨this, prev_hom.property.right⟩
    have m_models_trg : m.modelsRule trg_on_m.val.rule := by exact mIsModel.right trg.val.rule trg.property 
    have trg_obsolete_on_m : trg_on_m.val.robsolete m := by 
      have nactive := m_models_trg trg_on_m.val ⟨rfl, trg_loaded_for_m⟩ 
      cases Classical.em (trg_on_m.val.robsolete m) with 
      | inl h => exact h
      | inr nh => 
        have : trg_on_m.val.ractive m := ⟨trg_loaded_for_m, nh⟩
        contradiction

    let subs := Classical.choose trg_obsolete_on_m
    let hsubs := Classical.choose_spec trg_obsolete_on_m

    let new_h : GroundTermMapping := fun t =>
      match t with 
      | FiniteTree.leaf _ => t
      | FiniteTree.inner _ _ =>
        let tInChaseKDec := Classical.propDecidable (∃ f, f ∈ (cs.fact_sets j) ∧ t ∈ f.terms.toSet)
        match tInChaseKDec with 
        | Decidable.isTrue _ => prev_hom.val t
        | Decidable.isFalse _ =>
          let tInResultDec := Classical.propDecidable (∃ f, f ∈ trg.val.result ∧ t ∈ f.terms.toSet)
          match tInResultDec with 
          | Decidable.isFalse _ => t
          | Decidable.isTrue tInResult =>
            let f := Classical.choose tInResult
            let ⟨hfl, hfr⟩ := Classical.choose_spec tInResult

            let idx_f := trg.val.idx_of_fact_in_result f hfl
            let atom_in_head := trg.val.rule.head.get idx_f
            let idx_t_in_f := f.terms.idx_of t (List.listToSetElementAlsoListElement _ _ hfr)
            have idx_t_in_f_isLt := idx_t_in_f.isLt
            have f_is_at_its_idx : f = trg.val.mapped_head.get ⟨idx_f.val, by simp [Trigger.mapped_head]⟩ := by simp [idx_f, Trigger.idx_of_fact_in_result]; apply List.idx_of_get

            have atom_arity_same_as_fact : f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by 
                rw [f_is_at_its_idx]
                unfold Trigger.mapped_head
                unfold Trigger.apply_to_function_free_atom
                rw [List.get_map]
                simp

            let term_corresponding_to_t := atom_in_head.terms.get ⟨idx_t_in_f.val, (by 
              rw [← atom_arity_same_as_fact]
              exact idx_t_in_f_isLt
            )⟩

            subs.apply_var_or_const term_corresponding_to_t

    ⟨new_h, (by 
      constructor 
      . intro term 
        split 
        . simp 
        . trivial
      . rw [← trg_res]
        intro fact fact_in_chase
        unfold Set.element at fact_in_chase

        cases fact_in_chase with | intro fact' h_fact' =>
          cases h_fact' with | intro h_fact'_in_chase apply_h_f_and_f'_eq =>
            cases h_fact'_in_chase with 
            | inl hl => 
              let idx_f := trg.val.idx_of_fact_in_result fact' hl
              have f_is_at_its_idx : fact' = trg.val.mapped_head.get ⟨idx_f.val, by simp [Trigger.mapped_head]⟩ := by simp [idx_f, Trigger.idx_of_fact_in_result]; apply List.idx_of_get

              rw [← apply_h_f_and_f'_eq]
              rw [f_is_at_its_idx]
              unfold applyFact

              apply hsubs.right
              apply List.existsIndexMeansInToSet
              exists ⟨idx_f.val, (by simp [GroundSubstitution.apply_function_free_conj])⟩ 
              simp [SubsTarget.apply, GroundSubstitution.apply_function_free_conj, List.get_map, GroundSubstitution.apply_function_free_atom, Trigger.mapped_head, Trigger.apply_to_function_free_atom]
              rw [← List.map_eq_map_iff]
              intro t ht 
              cases t with 
              | const ct => simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const]
              | var vt => 
                simp [new_h, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const]
                split 
                case h_1 c h_c_eq =>
                  have : trg.val.rule.frontier.elem vt := by 
                    apply Decidable.byContradiction
                    intro opp
                    simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, opp] at h_c_eq
                  rw [hsubs.left vt this]
                  simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, this]
                  simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, this] at h_c_eq
                  rw [h_c_eq]
                  have this := prev_hom.property.left (FiniteTree.leaf c)
                  simp at this
                  rw [this]
                case h_2 => 
                  split 
                  case h_1 _ exis_f _ => 
                    have vtInFrontier : trg.val.rule.frontier.elem vt := by 
                      apply Decidable.byContradiction
                      intro vtNotInFrontier
                      simp at vtNotInFrontier

                      have : trg.val.result ⊆ cs.fact_sets j := by 
                        apply funcTermForExisVarInChaseMeansTriggerResultOccurs
                        constructor
                        apply vtNotInFrontier
                        apply exis_f

                      have : trg.val.robsolete (cs.fact_sets j) := by 
                        let obs_subs := fun v : Variable => trg.val.apply_to_var_or_const (VarOrConst.var v)

                        exists obs_subs
                        constructor
                        . intro v vInFrontier 
                          simp [obs_subs, Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, vInFrontier]
                        . simp [obs_subs, SubsTarget.apply, GroundSubstitution.apply_function_free_conj]
                          unfold GroundSubstitution.apply_function_free_atom
                          intro f' hf'
                          apply this
                          unfold Trigger.result
                          unfold Trigger.mapped_head
                          unfold Trigger.apply_to_function_free_atom

                          have : ∀ a : FunctionFreeAtom, (List.map (GroundSubstitution.apply_var_or_const obs_subs) a.terms) = (List.map (trg.val.apply_to_var_or_const) a.terms) := by 
                            intro a 
                            induction a.terms with 
                            | nil => simp [List.map]
                            | cons head tail ih => 
                              simp [List.map, ih] 
                              simp [obs_subs, SubsTarget.apply, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const, Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const] 
                              cases head with 
                              | var v => simp 
                              | const c => simp [VarOrConst.skolemize]

                          simp [← this]
                          apply hf'

                      have : ¬ trg.val.robsolete (cs.fact_sets j) := trg_act.right
                      contradiction

                    rw [hsubs.left]
                    simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, vtInFrontier]
                    have : trg.val.rule = trg_on_m.val.rule := by rfl
                    rw [← this]
                    apply vtInFrontier
                  case h_2 _ n_exis_f _ => 
                    have vtNotInFrontier : ¬ trg.val.rule.frontier.elem vt := by 
                      intro hcontra
                      have vtInBody := Rule.frontier_var_occurs_in_fact_in_body _ _ hcontra
                      cases vtInBody with | intro f hf =>
                        apply n_exis_f 
                        exists (trg.val.subs.apply_function_free_atom f)
                        constructor 
                        . apply trg_act.left
                          unfold Trigger.mapped_body
                          apply List.mappedElemInMappedList
                          apply hf.left
                        . simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, hcontra, GroundSubstitution.apply_function_free_atom]
                          have : trg.val.subs vt = trg.val.subs.apply_var_or_const (VarOrConst.var vt) := by simp [GroundSubstitution.apply_var_or_const]
                          rw [this]
                          apply List.mappedElemInMappedList
                          apply hf.right
                    split 
                    case h_1 _ n_exis_f' _ => 
                      apply False.elim 
                      apply n_exis_f'
                      exists fact'
                      constructor 
                      exact hl 
                      rw [f_is_at_its_idx]

                      rw [← Trigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]

                      apply List.existsIndexMeansInToSet
                      cases (List.inToSetMeansExistsIndex _ _ ht) with | intro term_idx h_term_idx =>
                        exists ⟨term_idx.val, (by 
                          rw [← Trigger.apply_to_function_free_atom_terms_same_length]
                          apply term_idx.isLt
                        )⟩
                        simp [GroundSubstitution.apply_atom, VarOrConst.skolemize, List.get_map, GroundSubstitution.apply_skolem_term, FunctionFreeAtom.skolemize, Trigger.apply_to_function_free_atom, Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const]
                        rw [← h_term_idx]
                    case h_2 _ exis_f' _ => 
                      split
                      case _ _ chosen_f_hl chosen_f_hr _ =>

                        let t := VarOrConst.var vt
                        let skolem_t := trg.val.skolemize_var_or_const t
                        let chosen_f := Classical.choose exis_f'

                        let idx_f := trg.val.idx_of_fact_in_result chosen_f chosen_f_hl
                        let atom_in_head := trg.val.rule.head.get idx_f
                        let idx_t_in_f := chosen_f.terms.idx_of (trg.val.apply_to_var_or_const t) (List.listToSetElementAlsoListElement _ _ chosen_f_hr)
                        have idx_t_in_f_isLt := idx_t_in_f.isLt
                        have f_is_at_its_idx : chosen_f = trg.val.mapped_head.get ⟨idx_f.val, by simp [Trigger.mapped_head]⟩ := by simp [idx_f, Trigger.idx_of_fact_in_result]; apply List.idx_of_get
                        have t_is_at_its_idx : (trg.val.apply_to_var_or_const t) = chosen_f.terms.get idx_t_in_f := by simp [idx_t_in_f]; apply List.idx_of_get

                        have atom_arity_same_as_fact : chosen_f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by 
                          rw [f_is_at_its_idx]
                          unfold Trigger.mapped_head
                          rw [List.get_map]
                          rw [← Trigger.apply_to_function_free_atom_terms_same_length]

                        let term_corresponding_to_t := atom_in_head.terms.get ⟨idx_t_in_f.val, (by 
                          rw [← atom_arity_same_as_fact]
                          exact idx_t_in_f_isLt
                        )⟩

                        let skolem_term_corresponding_to_t := trg.val.skolemize_var_or_const term_corresponding_to_t

                        have subs_application_is_injective_for_freshly_introduced_terms : ∀ s, trg.val.apply_to_skolemized_term skolem_t = trg.val.apply_to_var_or_const s -> skolem_t = trg.val.skolemize_var_or_const s := by 
                          intro s hs
                          cases s with 
                          | const const_s => 
                            simp [skolem_t, Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, VarOrConst.skolemize, vtNotInFrontier, GroundSubstitution.apply_skolem_term] at hs
                            contradiction
                          | var var_s =>
                            apply Trigger.subs_application_is_injective_for_freshly_introduced_terms
                            apply vtNotInFrontier
                            apply hs

                        have skolemized_ts_are_equal : skolem_term_corresponding_to_t = skolem_t := by 
                          apply Eq.symm 
                          apply subs_application_is_injective_for_freshly_introduced_terms
                          unfold Trigger.apply_to_var_or_const at t_is_at_its_idx
                          simp at t_is_at_its_idx
                          rw [t_is_at_its_idx]

                          have : chosen_f.terms = (trg.val.apply_to_function_free_atom atom_in_head).terms := by 
                            rw [f_is_at_its_idx]
                            rw [← Trigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]

                          rw [List.get_eq_of_eq this]

                          simp [Trigger.apply_to_function_free_atom, List.get_map]

                        have : term_corresponding_to_t = t := by 
                          apply VarOrConst.skolemize_injective trg.val.rule.id (Rule.frontier trg.val.rule)
                          apply skolemized_ts_are_equal

                        simp [term_corresponding_to_t] at this
                        rw [this]

            | inr hr => 
              apply prev_hom.property.right 
              exists fact'
              constructor
              exact hr 
              unfold applyFact at apply_h_f_and_f'_eq
              unfold applyFact
              rw [← apply_h_f_and_f'_eq]
              simp
              rw [← List.map_eq_map_iff]
              intro x hx
              cases x with 
              | leaf xc => simp [new_h]; apply prev_hom.property.left (GroundTerm.const xc)
              | inner xfs xfrontier => 
                simp [new_h] 
                have : ∃ f, f ∈ (cs.fact_sets j) ∧ (FiniteTree.inner xfs xfrontier) ∈ f.terms.toSet := by exists fact' 
                split
                . rfl
                . contradiction
    )⟩

theorem inductive_homomorphism_same_on_terms_in_next_step (kb : KnowledgeBase) (cs : ChaseSequence kb) (m : FactSet) (mIsModel : m.modelsKb kb) : ∀ i f t, f ∈ cs.fact_sets i ∧ t ∈ f.terms.toSet -> (inductive_homomorphism kb cs m mIsModel i).val t = (inductive_homomorphism kb cs m mIsModel (Nat.succ i)).val t := by 
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
    case h_1 c => exact (inductive_homomorphism kb cs m mIsModel i).property.left (GroundTerm.const c)
    case h_2 ft => 
      split 
      case h_1 _ ex_f _ => rfl
      case h_2 _ n_ex_f _ => apply False.elim; apply n_ex_f; exists f

theorem inductive_homomorphism_same_on_all_following_terms (kb : KnowledgeBase) (cs : ChaseSequence kb) (m : FactSet) (mIsModel : m.modelsKb kb) : ∀ i j f t, f ∈ cs.fact_sets i ∧ t ∈ f.terms.toSet -> (inductive_homomorphism kb cs m mIsModel i).val t = (inductive_homomorphism kb cs m mIsModel (i + j)).val t := by 
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

theorem chaseResultUnivModelsKb (kb : KnowledgeBase) (cs : ChaseSequence kb) : cs.result.universallyModelsKb kb := by
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
  intro trg trgRule _ contra 
  cases (trgRActiveForChaseResultMeansRActiveAtSomeIndex kb cs trg contra) with | intro i ractiveI => 
    have notActiveAtSomePoint := cs.fairness ⟨trg, by rw [← trgRule] at h; apply h⟩ i ractiveI 
    cases notActiveAtSomePoint with | intro j ractiveJ => 
      have ⟨jGeI, notRActiveJ⟩ := ractiveJ 
      simp [Trigger.ractive] at notRActiveJ 
      have obsoleteJ := notnotelim (notRActiveJ (by 
        simp [Trigger.loaded] 
        apply Set.subsetTransitive 
        constructor 
        apply ractiveI.left 
        cases Nat.le.dest jGeI with | intro m hm => rw [← hm]; apply chaseSequenceSetIsSubsetOfAllFollowing kb cs i m
      ))
      have obsoleteResult := rObsoletenessSubsetMonotone (And.intro (chaseSequenceSetIsSubsetOfResult kb cs j) obsoleteJ)
      have notObsoleteResult := contra.right 
      contradiction
  
  -- universality
  intro m mIsModel

  let inductive_homomorphism_shortcut := inductive_homomorphism kb cs m mIsModel

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
    apply List.map_eq_map_if_functions_eq
    intro t t_is_term_in_f
    split 
    case a.h_2 _ n_ex_f' _ => 
      apply False.elim 
      apply n_ex_f' 
      exists f 
      constructor 
      . apply chaseSequenceSetIsSubsetOfResult; apply f_in_step_i
      . apply t_is_term_in_f
    case a.h_1 _ ex_f' _ => 
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
            apply t_is_term_in_f
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

