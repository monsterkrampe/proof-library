import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.Trigger
import ProofLibrary.Logic

def InfiniteList (α : Type u) := Nat → α  

def RTrigger (r : RuleSet) := { trg : Trigger // trg.rule ∈ r}

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
  intro ⟨loaded, ractive⟩ 
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

theorem rObsoletenessSubsetMonotone (trg : Trigger) (F G : FactSet) : F ⊆ G ∧ trg.robsolete F -> trg.robsolete G := by 
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

theorem factInChaseSeqMustComeFromDBOrTriggerResult (kb : KnowledgeBase) (cs : ChaseSequence kb) (f : Fact) (i : Nat) : f ∈ cs.fact_sets i -> f ∈ kb.db.toFactSet ∨ ∃ j, j ≤ i ∧ f ∈ cs.fact_sets j ∧ ¬ (f ∈ cs.fact_sets (j-1)) ∧ ∃ trg : RTrigger kb.rules, (f ∈ trg.val.result ∧ trg.val.result ∪ cs.fact_sets (j-1) = cs.fact_sets j) := by
-- ∃ trg : RTrigger kb.rules, (f ∈ trg.val.result ∧ trg.val.result ⊆ cs.fact_sets i) := by 
  intro h 
  induction i with 
  | zero => rw [cs.database_first] at h; apply Or.inl; exact h 
  | succ j ih => 
    have trg_exis := cs.triggers_exist j 
    cases trg_exis with 
    | inr hr => 
      rw [← hr.right] at h
      cases ih h with
      | inl _ => apply Or.inl; assumption 
      | inr hr => apply Or.inr; cases hr with | intro k hk => exists k; constructor; apply Nat.le_succ_of_le; exact hk.left; exact hk.right
        --exists trg; constructor; exact htrg.left; apply Set.subsetTransitive; constructor; apply htrg.right; apply chaseSequenceSetIsSubsetOfNext
    | inl hl => 
      cases hl with | intro trg h_trg => 
        rw [← h_trg.right] at h
        cases h with 
        | inr hlr =>  
          cases ih hlr with 
          | inl _ => apply Or.inl; assumption
          | inr hr => apply Or.inr; cases hr with | intro k hk => exists k; constructor; apply Nat.le_succ_of_le; exact hk.left; exact hk.right
            --exists trg; constructor; exact htrg.left; apply Set.subsetTransitive; constructor; apply htrg.right; apply chaseSequenceSetIsSubsetOfNext
        | inl hll => 
          -- TODO: this should actually be decidable but we need to change the implementation for this
          cases Classical.em (f ∈ cs.fact_sets j) with 
          | inl h_f_in_j => 
            cases ih h_f_in_j with 
            | inl hl => apply Or.inl; exact hl
            | inr hr => apply Or.inr; cases hr with | intro k hk => exists k; constructor; apply Nat.le_succ_of_le; exact hk.left; exact hk.right
          | inr h_f_not_in_j => 
            apply Or.inr
            exists j+1
            constructor
            . simp 
            constructor
            . rw [← h_trg.right]; apply Or.inl; exact hll
            constructor
            . exact h_f_not_in_j
            . exists trg; constructor; exact hll; rw [← h_trg.right]; rfl

theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (kb : KnowledgeBase) (cs : ChaseSequence kb) (trg : Trigger) (var : Variable) (i : Nat) : (∃ headAtom : FunctionFreeAtom, trg.rule.head.elem headAtom ∧ headAtom.terms.elem (VarOrConst.var var)) ∧ (trg.rule.frontier.elem var = false) ∧ (∃ f: Fact, f ∈ cs.fact_sets i ∧ (trg.subs.apply_skolem_term (VarOrConst.skolemize trg.rule.id trg.rule.frontier (VarOrConst.var var))) ∈ f.terms.toSet) -> trg.result ⊆ cs.fact_sets i := by 
  intro ⟨var_in_head, var_not_in_frontier, exis_f⟩
  cases exis_f with | intro f hf => 
    have ⟨f_in_chase, var_in_f_terms⟩ := hf 

    -- FIXME: we should not do this for f but for the fact that freshly introduces the functional term 
    -- this might happen before f

    have f_res_from_trg' : ∃ j, j ≤ i ∧ f ∈ cs.fact_sets j ∧ ¬ (f ∈ cs.fact_sets (j-1)) ∧ ∃ trg : RTrigger kb.rules, (f ∈ trg.val.result ∧ trg.val.result ∪ cs.fact_sets (j-1) = cs.fact_sets j) := by
    -- ∃ trg : RTrigger kb.rules, (f ∈ trg.val.result ∧ trg.val.result ⊆ cs.fact_sets i) := by 
      cases factInChaseSeqMustComeFromDBOrTriggerResult kb cs f i f_in_chase with 
      | inr _ => assumption
      | inl hl => 
        apply False.elim 
        simp [Database.toFactSet, Set.element, Fact.toFunctionFreeFact] at hl 

        have : ¬(List.all f.terms fun t =>
          match t with
          | GroundTerm.const c => true
          | x => false) := by 
            apply List.neg_all_of_any_neg
            apply List.any_of_exists
            exists GroundSubstitution.apply_skolem_term trg.subs (VarOrConst.skolemize trg.rule.id trg.rule.frontier (VarOrConst.var var))
            constructor
            . apply var_in_f_terms
            . simp [GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var_not_in_frontier]
        split at hl 
        exact hl 
        case h_2 _ _ heq => apply (Option.someNotNone heq); split; contradiction; rfl

    cases f_res_from_trg' with | intro j hj => 
      let ⟨j_leq_i, h_in_j, h_not_in_before_j, h_ex_trg⟩ := hj
      cases h_ex_trg with | intro trg' htrg' =>
          --have : trg.rule = trg'.val.rule ∧ ∀ v, v ∈ trg.rule.frontier.toSet -> trg.subs.apply_term (VarOrConst.skolemize trg.rule.id trg.rule.frontier (VarOrConst.var v)) = trg'.val.subs.apply_term (VarOrConst.skolemize trg'.val.rule.id trg'.val.rule.frontier (VarOrConst.var v)) := by sorry
        -- FIXME: this might actually not hold!!!
        have : trg.rule = trg'.val.rule ∧ ∀ v, v ∈ trg.rule.frontier.toSet -> trg.subs v = trg'.val.subs v := by sorry
        have : trg.mapped_head = trg'.val.mapped_head := by 
          unfold Trigger.mapped_head
          rw [← this.left]
          apply List.map_eq_map_if_functions_eq
          intro a ha
          simp
          apply List.map_eq_map_if_functions_eq
          intro voc hvoc
          cases voc with 
          | const c => simp [SubsTarget.apply, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] 
          | var v =>
            cases Decidable.em (trg.rule.frontier.elem v) with 
            | inl v_in_frontier => 
              simp [VarOrConst.skolemize, v_in_frontier, SubsTarget.apply, GroundSubstitution.apply_skolem_term]
              apply this.right
              apply List.listElementAlsoToSetElement
              apply v_in_frontier
            | inr v_not_in_frontier => 
              simp [VarOrConst.skolemize, v_not_in_frontier, SubsTarget.apply, GroundSubstitution.apply_skolem_term]
              rw [← FiniteTreeList.eqIffFromListEq]
              apply List.map_eq_map_if_functions_eq
              intro w hw
              rw [← this.right w]
              exact hw

        have : trg.result = trg'.val.result := by 
          unfold Trigger.result 
          rw [this]
        rw [this]
        have : trg'.val.result ⊆ cs.fact_sets j := by 
          rw [← htrg'.right]
          apply Set.subsetUnionSomethingStillSubset
          apply Set.subsetOfSelf

        apply Set.subsetTransitive
        constructor
        apply this
        cases Nat.le.dest j_leq_i with | intro k hk => 
          rw [← hk]
          apply chaseSequenceSetIsSubsetOfAllFollowing

namespace KnowledgeBase
  def terminates (kb : KnowledgeBase) : Prop :=
    ∃ cs : ChaseSequence kb, cs.terminates

  def universally_terminates (kb : KnowledgeBase) : Prop :=
    ∀ cs : ChaseSequence kb, cs.terminates
end KnowledgeBase

noncomputable def inductive_homomorphism (kb : KnowledgeBase) (cs : ChaseSequence kb) (m : FactSet) (mIsModel : m.modelsKb kb) : (i : Nat) -> { hom : GroundTermMapping // isHomomorphism hom ∧ applyFactSet hom (cs.fact_sets i) ⊆ m }
| .zero => ⟨id, (by 
  constructor 
  unfold isHomomorphism ; intro gt ; cases gt <;> simp
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
      match t_eq : t with 
      | GroundTerm.const _ => t
      | GroundTerm.func ft =>
        let tInChaseKDec := Classical.propDecidable (∃ f, f ∈ (cs.fact_sets j) ∧ t ∈ f.terms.toSet)
        match tInChaseKDec with 
        | Decidable.isTrue _ => prev_hom.val t
        | Decidable.isFalse tNotInChaseK =>
          let tInResultDec := Classical.propDecidable (∃ f, f ∈ trg.val.result ∧ t ∈ f.terms.toSet)
          match tInResultDec with 
          | Decidable.isFalse _ => t
          | Decidable.isTrue tInResult =>
            let f := Classical.choose tInResult
            let ⟨hfl, hfr⟩ := Classical.choose_spec tInResult

            let idx_f := trg.val.idx_of_fact_in_result f hfl
            let atom_in_head := trg.val.rule.head.get idx_f
            -- let skolem_atom_in_head := atom_in_head.skolemize trg.val.rule.id trg.val.rule.frontier
            let idx_t_in_f := f.terms.idx_of t (List.listToSetElementAlsoListElement _ _ hfr)
            have idx_t_in_f_isLt := idx_t_in_f.isLt
            have f_is_at_its_idx : f = trg.val.mapped_head.get ⟨idx_f.val, by simp [Trigger.mapped_head, List.length_map, List.length_enum]; exact idx_f.isLt⟩ := by simp [Trigger.idx_of_fact_in_result]; apply List.idx_of_get

            have atom_arity_same_as_fact : f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by 
                rw [f_is_at_its_idx]
                unfold Trigger.mapped_head
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
              have f_is_at_its_idx : fact' = trg.val.mapped_head.get ⟨idx_f.val, by simp [Trigger.mapped_head, List.length_map, List.length_enum]; exact idx_f.isLt⟩ := by simp [Trigger.idx_of_fact_in_result]; apply List.idx_of_get

              rw [← apply_h_f_and_f'_eq]
              rw [f_is_at_its_idx]
              unfold applyFact

              apply hsubs.right
              apply List.existsIndexMeansInToSet
              exists ⟨idx_f.val, (by simp [SubsTarget.apply, GroundSubstitution.apply_function_free_conj]; apply idx_f.isLt)⟩ 
              simp [SubsTarget.apply, GroundSubstitution.apply_function_free_conj, List.get_map, GroundSubstitution.apply_function_free_atom, Trigger.mapped_head]
              rw [List.combine_nested_map]
              rw [← List.map_eq_map_iff]
              intro t ht 
              cases t with 
              | const ct => simp [VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const]
              | var vt => 
                simp [GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const]
                split 
                case h_1 c h_c_eq =>
                  have : trg.val.rule.frontier.elem vt := by 
                    apply Decidable.byContradiction
                    intro opp
                    simp [VarOrConst.skolemize, opp] at h_c_eq
                  rw [hsubs.left vt this]
                  simp [VarOrConst.skolemize, this]
                  simp [VarOrConst.skolemize, this] at h_c_eq
                  rw [h_c_eq]
                  rw [prev_hom.property.left (GroundTerm.const c)]
                case h_2 ft h_ft_eq => 
                  split 
                  case h_1 _ exis_f _ => 
                    have vtInHead : ∃ headAtom : FunctionFreeAtom, trg.val.rule.head.elem headAtom ∧ headAtom.terms.elem (VarOrConst.var vt) := by 
                      exists trg.val.rule.head.get idx_f
                      simp [List.elem, List.get]
                      constructor 
                      . apply List.listToSetElementAlsoListElement
                        apply List.listGetInToSet
                      . apply List.listToSetElementAlsoListElement
                        apply ht
                    have vtInFrontier : trg.val.rule.frontier.elem vt := by 
                      apply Decidable.byContradiction
                      intro vtNotInFrontier
                      simp at vtNotInFrontier

                      have : trg.val.result ⊆ cs.fact_sets j := by 
                        apply funcTermForExisVarInChaseMeansTriggerResultOccurs
                        constructor 
                        apply vtInHead
                        constructor
                        apply vtNotInFrontier
                        simp [GroundSubstitution.apply_skolem_term]
                        apply exis_f

                      have : trg.val.robsolete (cs.fact_sets j) := by 
                        let obs_subs := fun v : Variable => trg.val.subs.apply_skolem_term (VarOrConst.skolemize (trg.val.rule.id) (trg.val.rule.frontier) (VarOrConst.var v))
                        exists obs_subs
                        constructor
                        . intro v vInFrontier 
                          simp [obs_subs, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, vInFrontier]
                        . simp [obs_subs, SubsTarget.apply, GroundSubstitution.apply_function_free_conj]
                          unfold GroundSubstitution.apply_function_free_atom
                          intro f' hf'
                          apply this
                          unfold Trigger.result
                          unfold Trigger.mapped_head

                          have : ∀ a : FunctionFreeAtom, (List.map (GroundSubstitution.apply_var_or_const fun v => GroundSubstitution.apply_skolem_term trg.val.subs (VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule) (VarOrConst.var v))) a.terms) = (List.map (SubsTarget.apply trg.val.subs ∘ VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule)) a.terms) := by 
                            intro a 
                            induction a.terms with 
                            | nil => simp [List.map]
                            | cons head tail ih => 
                              simp [List.map, ih] 
                              simp [SubsTarget.apply, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const] 
                              cases head with 
                              | var v => simp 
                              | const c => simp [VarOrConst.skolemize]

                          simp [← this]
                          apply hf'

                      have : ¬ trg.val.robsolete (cs.fact_sets j) := trg_act.right
                      contradiction

                    rw [hsubs.left]
                    simp [VarOrConst.skolemize, vtInFrontier]
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
                        . simp [VarOrConst.skolemize, hcontra, GroundSubstitution.apply_function_free_atom]
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
                          rw [← GroundSubstitution.apply_same_length]
                          rw [← FunctionFreeAtom.skolemize_same_length]
                          apply term_idx.isLt
                        )⟩
                        simp [GroundSubstitution.apply_atom, VarOrConst.skolemize, List.get_map, GroundSubstitution.apply_skolem_term, FunctionFreeAtom.skolemize]
                        rw [← h_term_idx]
                    case h_2 _ exis_f' _ => 
                      split
                      case _ _ chosen_f_hl chosen_f_hr _ =>

                        -- let t := VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule) (VarOrConst.var vt)
                        let t := VarOrConst.var vt
                        let skolem_t := VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule) t
                        let chosen_f := Classical.choose exis_f'

                        let idx_f := trg.val.idx_of_fact_in_result chosen_f chosen_f_hl
                        let atom_in_head := trg.val.rule.head.get idx_f
                        let skolem_atom_in_head := atom_in_head.skolemize trg.val.rule.id trg.val.rule.frontier
                        let idx_t_in_f := chosen_f.terms.idx_of (trg.val.subs.apply_skolem_term skolem_t) (List.listToSetElementAlsoListElement _ _ chosen_f_hr)
                        have idx_t_in_f_isLt := idx_t_in_f.isLt
                        have f_is_at_its_idx : chosen_f = trg.val.mapped_head.get ⟨idx_f.val, by simp [Trigger.mapped_head, List.length_map, List.length_enum]; exact idx_f.isLt⟩ := by simp [Trigger.idx_of_fact_in_result]; apply List.idx_of_get
                        have t_is_at_its_idx : (trg.val.subs.apply_skolem_term skolem_t) = chosen_f.terms.get idx_t_in_f := by simp [idx_t_in_f]; apply List.idx_of_get

                        have skolem_atom_in_head_with_subs_is_f : trg.val.subs.apply_atom skolem_atom_in_head = chosen_f := by rw [f_is_at_its_idx]; exact trg.val.apply_subs_to_atom_at_idx_same_as_fact_at_idx idx_f

                        have skolem_atom_arity_same_as_fact : chosen_f.terms.length = List.length skolem_atom_in_head.terms := by 
                          apply Eq.symm
                          apply GroundSubstitution.eq_under_subs_means_same_length trg.val.subs
                          rw [← skolem_atom_in_head_with_subs_is_f]

                        have subs_application_is_injective_for_freshly_introduced_terms : ∀ s, s ∈ skolem_atom_in_head.terms.toSet ∧ trg.val.subs.apply_skolem_term skolem_t = trg.val.subs.apply_skolem_term s -> skolem_t = s := by 
                          -- TODO: resolve this by arguing that subs application is basically injective on fresh skolem term
                          sorry

                        have skolem_t_is_at_its_idx : skolem_t = skolem_atom_in_head.terms.get ⟨idx_t_in_f.val, (by rw[← skolem_atom_arity_same_as_fact]; exact idx_t_in_f_isLt)⟩ := by 
                          simp [idx_t_in_f]

                          have : skolem_atom_in_head.terms.elem skolem_t := by 
                            rw [← GroundSubstitution.eq_under_subs_means_elements_are_preserved _ _ _ (skolem_atom_in_head_with_subs_is_f) _ (subs_application_is_injective_for_freshly_introduced_terms)]
                            apply List.listToSetElementAlsoListElement
                            apply chosen_f_hr
                          have : (skolem_atom_in_head.terms.idx_of skolem_t this).val = idx_t_in_f.val := by 
                            apply Eq.symm
                            apply GroundSubstitution.eq_under_subs_means_indices_of_elements_are_preserved
                            apply skolem_atom_in_head_with_subs_is_f
                            apply subs_application_is_injective_for_freshly_introduced_terms

                          simp [← this]
                          apply List.idx_of_get

                        let skolem_term_corresponding_to_t := skolem_atom_in_head.terms.get ⟨idx_t_in_f.val, (by 
                          rw [← skolem_atom_arity_same_as_fact]
                          exact idx_t_in_f_isLt
                        )⟩

                        have skolemized_ts_are_equal : skolem_term_corresponding_to_t = skolem_t := by 
                          rw [skolem_t_is_at_its_idx]

                        have atom_arity_same_as_fact : chosen_f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by 
                          rw [f_is_at_its_idx]
                          unfold Trigger.mapped_head
                          rw [List.get_map]
                          simp

                        let term_corresponding_to_t := atom_in_head.terms.get ⟨idx_t_in_f.val, (by 
                          rw [← atom_arity_same_as_fact]
                          exact idx_t_in_f_isLt
                        )⟩
                        
                        have : VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule) term_corresponding_to_t = skolem_term_corresponding_to_t := by simp [FunctionFreeAtom.skolemize, List.get_map]

                        have : term_corresponding_to_t = t := by 
                          -- TODO: should follow from skolemized_ts_are_equal if we argue that skolemization is injective in the scope of a rule
                          apply VarOrConst.skolemize_injective trg.val.rule.id (Rule.frontier trg.val.rule)
                          rw [this]
                          apply skolemized_ts_are_equal

                        simp [GroundSubstitution.apply_skolem_term] at this
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
              | const xc => simp; apply prev_hom.property.left (GroundTerm.const xc)
              | func xfunc => 
                simp 
                have : ∃ f, f ∈ (cs.fact_sets j) ∧ (GroundTerm.func xfunc) ∈ f.terms.toSet := by exists fact' 
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
  simp [FactSet.modelsDb, ChaseSequence.result]
  intro f 
  intro h 
  simp [Set.element]
  exists 0
  rw [cs.database_first]
  exact h
  
  -- Rules modelled
  simp [FactSet.modelsRules]
  intro r 
  intro h 
  simp [FactSet.modelsRule]
  intro trg 
  intro ⟨ trgRule, _ ⟩
  intro contra 
  cases (trgRActiveForChaseResultMeansRActiveAtSomeIndex kb cs trg contra) with | intro i ractiveI => 
    have notActiveAtSomePoint := cs.fairness ⟨trg, by rw [← trgRule] at h; apply h⟩ i ractiveI 
    cases notActiveAtSomePoint with | intro j ractiveJ => 
      have ⟨jGeI, notRActiveJ⟩ := ractiveJ 
      simp [Trigger.ractive] at notRActiveJ 
      have obsoleteJ := notnotelim ((notAndDeMorgan notRActiveJ) (by 
        simp [Trigger.loaded] 
        apply Set.subsetTransitive 
        constructor 
        apply ractiveI.left 
        cases Nat.le.dest jGeI with | intro m hm => rw [← hm]; apply chaseSequenceSetIsSubsetOfAllFollowing kb cs i m
      ))
      have obsoleteResult := rObsoletenessSubsetMonotone _ _ _ (And.intro (chaseSequenceSetIsSubsetOfResult kb cs j) obsoleteJ)
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
    simp
    apply List.map_eq_map_if_functions_eq
    intro t t_is_term_in_f
    split 
    case a.h_2 _ n_ex_f' _ => 
      -- contradiction
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
            simp at hk
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
      simp 
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

