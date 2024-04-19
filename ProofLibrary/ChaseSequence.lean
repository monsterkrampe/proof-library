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

theorem factInChaseSeqMustComeFromDBOrTriggerResult (kb : KnowledgeBase) (cs : ChaseSequence kb) (f : Fact) (i : Nat) : f ∈ cs.fact_sets i -> f ∈ kb.db.toFactSet ∨ ∃ trg : RTrigger kb.rules, (f ∈ trg.val.result ∧ trg.val.result ⊆ cs.fact_sets i) := by 
  intro h 
  induction i with 
  | zero => rw [cs.database_first] at h; apply Or.inl; exact h 
  | succ j ih => 
    have trg_exis := cs.triggers_exist j 
    cases trg_exis with 
    | inr hr => 
      rw [← hr.right] at h
      cases ih h with
      | inl _ =>  apply Or.inl; assumption 
      | inr hr => apply Or.inr; cases hr with | intro trg htrg => exists trg; constructor; exact htrg.left; apply Set.subsetTransitive; constructor; apply htrg.right; apply chaseSequenceSetIsSubsetOfNext
    | inl hl => 
      cases hl with | intro trg h_trg => 
        rw [← h_trg.right] at h
        cases h with 
        | inr hlr => cases ih hlr with 
          | inl _ => apply Or.inl; assumption
          | inr hr => apply Or.inr; cases hr with | intro trg htrg => exists trg; constructor; exact htrg.left; apply Set.subsetTransitive; constructor; apply htrg.right; apply chaseSequenceSetIsSubsetOfNext
        | inl hll => apply Or.inr; exists trg; constructor; exact hll; rw [← h_trg.right]; unfold Set.union; intro f hf; apply Or.inl; apply hf

theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (kb : KnowledgeBase) (cs : ChaseSequence kb) (trg : Trigger) (var : Variable) (i : Nat) : (trg.rule.frontier.elem var = false) ∧ (∃ f: Fact, f ∈ cs.fact_sets i ∧ (trg.subs.apply_term (VarOrConst.skolemize trg.rule.id trg.rule.frontier (VarOrConst.var var))) ∈ f.terms.toSet) -> trg.result ⊆ cs.fact_sets i := by 
  intro ⟨var_not_in_frontier, exis_f⟩
  cases exis_f with | intro f hf => 
    have ⟨f_in_chase, var_in_f_terms⟩ := hf 

    have f_res_from_trg' : ∃ trg : RTrigger kb.rules, (f ∈ trg.val.result ∧ trg.val.result ⊆ cs.fact_sets i) := by cases factInChaseSeqMustComeFromDBOrTriggerResult kb cs f i f_in_chase with 
      | inr _ => assumption
      | inl hl => 
        apply False.elim 
        simp [Database.toFactSet, Set.element, Fact.toFunctionFreeFact] at hl 
        simp [GroundSubstitution.apply_term, VarOrConst.skolemize, var_not_in_frontier] at var_in_f_terms

        have : ¬(List.all f.terms fun t =>
          match t with
          | GroundTerm.const c => true
          | x => false) := by sorry
        split at hl 
        exact hl 
        case h_2 _ _ heq => apply (Option.someNotNone heq); split; contradiction; rfl

    cases f_res_from_trg' with | intro trg' htrg' =>
      have : trg.result ⊆ trg'.val.result := sorry
      apply Set.subsetTransitive
      constructor
      apply this
      apply htrg'.right

namespace KnowledgeBase
  def terminates (kb : KnowledgeBase) : Prop :=
    ∃ cs : ChaseSequence kb, cs.terminates

  def universally_terminates (kb : KnowledgeBase) : Prop :=
    ∀ cs : ChaseSequence kb, cs.terminates
end KnowledgeBase

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
  intro ⟨ trgRule, trgLoaded ⟩
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
  have inductive_claim : ∀ i : Nat, ∃ h, isHomomorphism h ∧ applyFactSet h (cs.fact_sets i) ⊆ m := by 
    intro i 
    induction i 
    exists id -- is the ID ok here?
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
    
    case succ k ih_k => 
      cases ih_k with | intro h ih_h => 
        cases cs.triggers_exist k
        case inr sequence_finished => 
          exists h 
          rw [← sequence_finished.right]
          exact ih_h
        case inl triggers_exist => 
          cases triggers_exist with | intro trg h_trg =>
            let ⟨trg_act, trg_res⟩ := h_trg
            let trg_on_m : RTrigger kb.rules := {
              val := {
                rule := trg.val.rule
                subs := fun t => h (trg.val.subs t)
              }
              property := trg.property
            }
            have trg_loaded_for_m : trg_on_m.val.loaded m := by 
              have : trg_on_m.val.loaded (applyFactSet h (cs.fact_sets k)) := by 
                apply Trigger.term_mapping_preserves_loadedness
                exact ih_h.left
                exact trg_act.left
              apply Set.subsetTransitive
              exact ⟨this, ih_h.right⟩
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
                let tInChaseKDec := Classical.propDecidable (∃ f, f ∈ (cs.fact_sets k) ∧ t ∈ f.terms.toSet)
                match tInChaseKDec with 
                | Decidable.isTrue _ => h t
                | Decidable.isFalse tNotInChaseK =>
                  let tInResultDec := Classical.propDecidable (∃ f, f ∈ trg.val.result ∧ t ∈ f.terms.toSet)
                  match tInResultDec with 
                  | Decidable.isFalse _ => t
                  | Decidable.isTrue tInResult =>
                    let f := Classical.choose tInResult
                    let ⟨hfl, hfr⟩ := Classical.choose_spec tInResult

                    let idx_f := trg.val.idx_of_fact_in_result f hfl
                    let atom_in_head := trg.val.rule.head.get idx_f
                    let skolem_atom_in_head := atom_in_head.skolemize trg.val.rule.id trg.val.rule.frontier
                    let idx_t_in_f := f.terms.idx_of t (List.listToSetElementAlsoListElement _ _ hfr)
                    have idx_t_in_f_isLt := idx_t_in_f.isLt
                    have f_is_at_its_idx : f = trg.val.mapped_head.get ⟨idx_f.val, by simp [Trigger.mapped_head, List.length_map, List.length_enum]; exact idx_f.isLt⟩ := by simp [Trigger.idx_of_fact_in_result]; apply List.idx_of_get
                    have t_is_at_its_idx : t = f.terms.get idx_t_in_f := by simp [idx_t_in_f]; apply List.idx_of_get

                    have skolem_atom_in_head_with_subs_is_f : trg.val.subs.apply_atom skolem_atom_in_head = f := by rw [f_is_at_its_idx]; exact trg.val.apply_subs_to_atom_at_idx_same_as_fact_at_idx idx_f

                    have skolem_atom_arity_same_as_fact : f.terms.length = List.length skolem_atom_in_head.terms := by 
                      apply Eq.symm
                      apply GroundSubstitution.eq_under_subs_means_same_length trg.val.subs
                      rw [← skolem_atom_in_head_with_subs_is_f]

                    let term_corresponding_to_t := skolem_atom_in_head.terms.get ⟨idx_t_in_f.val, (by 
                      rw [← skolem_atom_arity_same_as_fact]
                      exact idx_t_in_f_isLt
                    )⟩
                    -- have : trg.val.subs.apply_term term_corresponding_to_t = t := by 
                    --   rw [t_is_at_its_idx]
                    --   apply GroundSubstitution.eq_under_subs_means_term_is_eq trg.val.subs
                    --   rw [← skolem_atom_in_head_with_subs_is_f]

                    subs.apply_term term_corresponding_to_t
                    -- match term_corresponding_to_t with 
                    --   | Term.var v => subs v 
                    --   | Term.const c => by simp [GroundSubstitution.apply_term] at this; rw [t_eq] at this; contradiction
                    --   | Term.func func => subs.apply_term func

            exists new_h
            constructor 
            . intro term; cases term with 
              | const c => simp 
              | func _ => trivial
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
                    apply List.getIsInToSet
                    exists ⟨idx_f.val, (by simp [SubsTarget.apply, GroundSubstitution.apply_function_free_conj]; apply idx_f.isLt)⟩ 
                    simp [SubsTarget.apply, GroundSubstitution.apply_function_free_conj, List.get_map, GroundSubstitution.apply_function_free_atom, Trigger.mapped_head]
                    rw [List.combine_nested_map]
                    rw [← List.map_eq_map_iff]
                    intro t ht 
                    cases t with 
                    | const ct => simp [VarOrConst.skolemize, GroundSubstitution.apply_term, GroundSubstitution.apply_var_or_const]
                    | var vt => 
                      simp [GroundSubstitution.apply_term, GroundSubstitution.apply_var_or_const]
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
                        rw [ih_h.left (GroundTerm.const c)]
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

                            have : trg.val.result ⊆ cs.fact_sets k := by 
                              apply funcTermForExisVarInChaseMeansTriggerResultOccurs
                              constructor 
                              apply vtNotInFrontier
                              simp [GroundSubstitution.apply_term]
                              apply exis_f

                            have : trg.val.robsolete (cs.fact_sets k) := by 
                              let obs_subs := fun v : Variable => trg.val.subs.apply_term (VarOrConst.skolemize (trg.val.rule.id) (trg.val.rule.frontier) (VarOrConst.var v))
                              exists obs_subs
                              constructor
                              . intro v vInFrontier 
                                simp [obs_subs, GroundSubstitution.apply_term, VarOrConst.skolemize, vInFrontier]
                              . simp [obs_subs, SubsTarget.apply, GroundSubstitution.apply_function_free_conj]
                                unfold GroundSubstitution.apply_function_free_atom
                                intro f' hf'
                                apply this
                                unfold Trigger.result
                                unfold Trigger.mapped_head

                                have : ∀ a : FunctionFreeAtom, (List.map (GroundSubstitution.apply_var_or_const fun v => GroundSubstitution.apply_term trg.val.subs (VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule) (VarOrConst.var v))) a.terms) = (List.map (SubsTarget.apply trg.val.subs ∘ VarOrConst.skolemize trg.val.rule.id (Rule.frontier trg.val.rule)) a.terms) := by 
                                  intro a 
                                  induction a.terms with 
                                  | nil => simp [List.map]
                                  | cons head tail ih => 
                                    simp [List.map, ih] 
                                    simp [SubsTarget.apply, GroundSubstitution.apply_term, GroundSubstitution.apply_var_or_const] 
                                    cases head with 
                                    | var v => simp 
                                    | const c => simp [VarOrConst.skolemize]

                                simp [← this]
                                apply hf'

                            have : ¬ trg.val.robsolete (cs.fact_sets k) := trg_act.right

                            contradiction
                          rw [hsubs.left]
                          simp [VarOrConst.skolemize, vtInFrontier]
                          have : trg.val.rule = trg_on_m.val.rule := by rfl
                          rw [← this]
                          apply vtInFrontier
                        case h_2 _ n_exis_f _ => 
                          split 
                          case h_1 _ n_exis_f' _ => 
                            -- TODO: here we should run into a contradiction since we know that the term occurs in the trigger result
                            apply False.elim 
                            apply n_exis_f'
                            exists fact'
                            constructor 
                            exact hl 
                            rw [f_is_at_its_idx]
                            
                            -- just trying something here...
                            rw [← Trigger.apply_subs_to_atom_at_idx_same_as_fact_at_idx]


                            simp [VarOrConst.skolemize, Trigger.mapped_head, List.get_map]
                            cases Decidable.em (trg.val.rule.frontier.elem vt) with 
                            | inl vtInFrontier => 
                              simp [vtInFrontier] 
                              sorry
                            | inr vtNotInFrontier => 
                              simp [vtNotInFrontier] 
                              sorry

                            -- I think we should apply ht here to simplify somehow
                            -- have : List.elem vt trg.val.rule.frontier := by sorry
                            -- simp [this]
                            --
                            -- sorry
                          case h_2 _ exis_f' _ => 
                            -- TODO: this should be the lengthy case, where we really end up mapping according to subs
                            sorry
                  | inr hr => 
                    apply ih_h.right 
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
                    | const xc => simp; apply ih_h.left (GroundTerm.const xc)
                    | func xfunc => 
                      simp 
                      have : ∃ f, f ∈ (cs.fact_sets k) ∧ (GroundTerm.func xfunc) ∈ f.terms.toSet := by exists fact' 
                      split
                      . rfl
                      . contradiction

  let global_h : GroundTermMapping := fun t => 
    let dec := Classical.propDecidable (∃ f, f ∈ cs.result ∧ t ∈ f.terms.toSet)
    match dec with
      | Decidable.isTrue p => 
        let f := Classical.choose p 
        let ⟨hfl, hfr⟩ := Classical.choose_spec p
        let i := Classical.choose hfl
        let hi := Classical.choose_spec hfl
        let target_h := Classical.choose (inductive_claim i)
        target_h t
      | Decidable.isFalse _ => t
  exists global_h
  constructor
  intro gt 
  cases gt with
    | const c => 
      simp
      cases Classical.propDecidable (∃ f, f ∈ ChaseSequence.result cs ∧ GroundTerm.const c ∈ List.toSet f.terms) with 
        | isTrue p => 
          simp 
          let f := Classical.choose p 
          let ⟨hfl, hfr⟩ := Classical.choose_spec p
          let i := Classical.choose hfl
          let hi := Classical.choose_spec hfl
          let target_h := Classical.choose (inductive_claim i)
          let target_h_is_hom := (Classical.choose_spec (inductive_claim i)).left
          simp
          exact target_h_is_hom (GroundTerm.const c)
        | isFalse np => simp
    | _ => simp
  intro f hf
  unfold ChaseSequence.result at hf
  unfold Set.element at hf
  unfold applyFactSet at hf
  cases hf with | intro e he =>
    let ⟨hel, her⟩ := he 
    simp [Set.element] at hel
    cases hel with | intro n hn =>
      rw [← her]
      simp [applyFact]

      sorry 

      -- let target_h := Classical.choose (inductive_claim n)
      -- let target_h_apply := (Classical.choose_spec (inductive_claim n)).right
      -- have global_eq_target_on_e : applyFact global_h e = applyFact target_h e := by 
      --   unfold applyFact
      --   simp 
      --   apply List.map_eq_map_if_functions_eq
      --   intro x hx 
      --   split
      --   case a.h_2 _ h2 _ => 
      --     apply False.elim 
      --     apply h2 
      --     exists e
      --     constructor 
      --     unfold ChaseSequence.result 
      --     simp [Set.element]
      --     exists n
      --     apply hx
      --   split
      --   case a.h_1 _ h1 _ =>
      --     sorry
      -- rw [← her, global_eq_target_on_e]
      -- apply target_h_apply
      -- apply applyPreservesElement
      -- apply hn
  

