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

namespace KnowledgeBase
  def terminates (kb : KnowledgeBase) : Prop :=
    ∃ cs : ChaseSequence kb, cs.terminates

  def universally_terminates (kb : KnowledgeBase) : Prop :=
    ∀ cs : ChaseSequence kb, cs.terminates
end KnowledgeBase

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
    simp [applyFactSet]
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
              
            let new_h : GroundTermMapping := fun t =>
              let dec := Classical.propDecidable (∃ f, f ∈ (cs.fact_sets k ∪ trg.val.result) ∧ t ∈ f.terms.toSet)
              match dec with 
                | Decidable.isTrue p => 
                  let f := Classical.choose p 
                  let ⟨hfl, hfr⟩ := Classical.choose_spec p
                  let hfllDec := Classical.propDecidable (f ∈ cs.fact_sets k)
                  match hfllDec with 
                    | Decidable.isTrue _ => h t
                    | Decidable.isFalse nhfll => 
                      have hflr : f ∈ trg.val.result := by
                        cases hfl with 
                          | inl => contradiction
                          | inr => assumption
                      let idx_f := trg.val.idx_of_fact_in_result f hflr
                      let subs := Classical.choose trg_obsolete_on_m
                      let hsubs := Classical.choose_spec trg_obsolete_on_m
                      let atom_in_head := trg.val.rule.head.get idx_f
                      let idx_t_in_f := f.terms.idx_of t (List.listToSetElementAlsoListElement _ _ hfr)
                      have idx_t_in_f_isLt := idx_t_in_f.isLt
                      have f_is_at_its_idx : f = trg.val.mapped_head.get ⟨idx_f.val, by simp [Trigger.mapped_head, List.length_map, List.length_enum]; exact idx_f.isLt⟩ := by simp [Trigger.idx_of_fact_in_result]; apply List.idx_of_get
                      have atom_arity_same_as_fact : f.terms.length = List.length (FunctionFreeAtom.terms atom_in_head) := by 
                        rw [f_is_at_its_idx]
                        unfold Trigger.mapped_head
                        rw [List.get_map]
                        rw [List.get_enum]
                        simp

                      let var_or_const_corresponding_to_t := atom_in_head.terms.get ⟨idx_t_in_f.val, (by 
                        rw [← atom_arity_same_as_fact]
                        exact idx_t_in_f_isLt
                      )⟩
                      match var_or_const_corresponding_to_t with 
                      | VarOrConst.var v => subs v 
                      | VarOrConst.const c => GroundTerm.const c
                | Decidable.isFalse _ => t
            exists new_h
            constructor 
            . intro term; cases term with 
              | const c => 
                simp 
                let dec := Classical.propDecidable (∃ f, f ∈ (cs.fact_sets k ∪ trg.val.result) ∧ (GroundTerm.const c) ∈ f.terms.toSet)
                cases dec_eq : dec with 
                | isTrue p =>
                  simp [dec_eq]
                  let f := Classical.choose p 
                  let ⟨hfl, hfr⟩ := Classical.choose_spec p
                  let hfllDec := Classical.propDecidable (f ∈ cs.fact_sets k)
                  cases hfllDec_eq : hfllDec with
                  | isTrue pp => simp [hfllDec_eq]; exact ih_h.left (GroundTerm.const c)
                  | isFalse np => simp [hfllDec_eq]; sorry
                | isFalse _ => simp [dec_eq]
              | func _ => trivial
            . sorry
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
      let target_h := Classical.choose (inductive_claim n)
      let target_h_apply := (Classical.choose_spec (inductive_claim n)).right
      have global_eq_target_on_e : applyFact global_h e = applyFact target_h e := by 
        sorry
      rw [← her, global_eq_target_on_e]
      apply target_h_apply
      apply applyPreservesElement
      apply hn
  

