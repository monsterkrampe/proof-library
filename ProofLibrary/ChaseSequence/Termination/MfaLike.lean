import ProofLibrary.ChaseSequence.Termination.Basic

section Defs

  variable (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  -- This is essentially the same as a GroundSubstitution only that it maps constants instead of variables
  abbrev ConstantMapping := sig.C -> GroundTerm sig

end Defs


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace ConstantMapping

  def apply_ground_term (g : ConstantMapping sig) (t : GroundTerm sig) : GroundTerm sig := t.mapLeaves g

  def apply_fact (g : ConstantMapping sig) (f : Fact sig) : Fact sig := {
    predicate := f.predicate
    terms := f.terms.map g.apply_ground_term
    arity_ok := by rw [List.length_map]; exact f.arity_ok
  }

  def apply_fact_set (g : ConstantMapping sig) (fs : FactSet sig) : FactSet sig := fun f => ∃ f', f' ∈ fs ∧ f = g.apply_fact f'

end ConstantMapping

namespace KnowledgeBase

  def parallelSkolemChase (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) : InfiniteList (FactSet sig)
  | .zero => kb.db.toFactSet
  | .succ n =>
    let prev_step := parallelSkolemChase kb det n
    fun f => f ∈ prev_step ∨ (∃ (trg : RTrigger (SkolemObsoleteness sig) kb.rules), trg.val.active prev_step ∧ f ∈ trg.val.result[0]'(by unfold RuleSet.isDeterministic at det; unfold Rule.isDeterministic at det; unfold PreTrigger.result; rw [List.length_map, ← PreTrigger.head_length_eq_mapped_head_length, det trg.val.rule trg.property]; simp))

  theorem parallelSkolemChase_subset_all_following (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) (n m : Nat) : kb.parallelSkolemChase det n ⊆ kb.parallelSkolemChase det (n+m) := by
    induction m with
    | zero => apply Set.subsetOfSelf
    | succ m ih =>
      rw [← Nat.add_assoc]
      conv => right; unfold parallelSkolemChase
      intro f f_mem
      apply Or.inl
      apply ih
      exact f_mem

  def skolemChaseResult (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) : FactSet sig := fun f => ∃ n, f ∈ parallelSkolemChase kb det n

  theorem skolemChaseResult_eq_every_chase_branch_result (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) : ∀ (cb : ChaseBranch (SkolemObsoleteness sig) kb), cb.result = kb.skolemChaseResult det := by
    unfold RuleSet.isDeterministic at det
    unfold Rule.isDeterministic at det
    intro cb
    apply funext
    intro f
    apply propext
    unfold ChaseBranch.result
    unfold skolemChaseResult
    constructor
    . intro h
      rcases h with ⟨n, h⟩
      induction n generalizing f with
      | zero =>
        rw [cb.database_first, Option.is_some_and] at h
        exists 0
      | succ n ih =>
        -- should be easy enough: get n from induction hypothesis and then use n+1
        cases eq_node : cb.branch.infinite_list (n+1) with
        | none => rw [eq_node, Option.is_some_and] at h; simp at h
        | some node =>
          cases eq_prev : cb.branch.infinite_list n with
          | none => have no_holes := cb.branch.no_holes (n+1); simp [eq_node] at no_holes; specialize no_holes ⟨n, by simp⟩; apply False.elim; apply no_holes; exact eq_prev
          | some prev_node =>
            have trg_ex := cb.triggers_exist n
            rw [eq_prev, Option.is_none_or] at trg_ex
            cases trg_ex with
            | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq_node; simp at eq_node
            | inl trg_ex =>
              unfold exists_trigger_opt_fs at trg_ex
              rcases trg_ex with ⟨trg, trg_active, disj_index, step_eq⟩
              rw [← step_eq, Option.is_some_and] at h
              simp at h
              cases h with
              | inl h =>
                specialize ih f
                rw [eq_prev, Option.is_some_and] at ih
                specialize ih h
                exact ih
              | inr h =>
                have : ∃ n, prev_node.fact.val ⊆ kb.parallelSkolemChase det n := by
                  have prev_finite := prev_node.fact.property
                  rcases prev_finite with ⟨prev_l, _, prev_l_eq⟩

                  have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e ∈  prev_node.fact.val) -> ∃ n, (∀ e, e ∈ l -> e ∈ kb.parallelSkolemChase det n) := by
                    intro l l_sub
                    induction l with
                    | nil => exists 0; intro e; simp
                    | cons hd tl ih_inner =>
                      have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
                      rcases from_ih with ⟨n_from_ih, from_ih⟩

                      have from_hd := ih hd
                      rw [eq_prev, Option.is_some_and] at from_hd
                      specialize from_hd (by apply l_sub; simp)
                      rcases from_hd with ⟨n_from_hd, from_hd⟩

                      cases Decidable.em (n_from_ih ≤ n_from_hd) with
                      | inl le =>
                        exists n_from_hd
                        intro f f_mem
                        simp at f_mem
                        cases f_mem with
                        | inl f_mem => rw [f_mem]; exact from_hd
                        | inr f_mem =>
                          rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                          rw [le]
                          apply kb.parallelSkolemChase_subset_all_following det n_from_ih diff
                          apply from_ih; exact f_mem
                      | inr lt =>
                        simp at lt
                        have le := Nat.le_of_lt lt
                        exists n_from_ih
                        intro f f_mem
                        simp at f_mem
                        cases f_mem with
                        | inr f_mem => apply from_ih; exact f_mem
                        | inl f_mem =>
                          rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                          rw [le]
                          apply kb.parallelSkolemChase_subset_all_following det n_from_hd diff
                          rw [f_mem]; exact from_hd

                  specialize this prev_l (by intro f; exact (prev_l_eq f).mp)
                  rcases this with ⟨n, this⟩
                  exists n
                  intro f
                  rw [← prev_l_eq]
                  exact this f
                rcases this with ⟨n, prev_subs⟩

                exists n+1
                unfold parallelSkolemChase

                have disj_index_zero : disj_index.val = 0 := by
                  have isLt := disj_index.isLt
                  unfold PreTrigger.result at isLt
                  simp only [List.length_map] at isLt
                  rw [← PreTrigger.head_length_eq_mapped_head_length] at isLt
                  rw [det _ trg.property, Nat.lt_one_iff] at isLt
                  exact isLt


                -- TODO: would be Decidable if we define sets in the parallelSkolemChase to be finite
                cases Classical.em (f ∈ kb.parallelSkolemChase det n) with
                | inl mem => apply Or.inl; exact mem
                | inr not_mem =>
                  apply Or.inr
                  exists trg
                  constructor
                  . unfold Trigger.active
                    constructor
                    . unfold PreTrigger.loaded
                      apply Set.subsetTransitive _ prev_node.fact.val _
                      constructor
                      . exact trg_active.left
                      . exact prev_subs
                    . intro contra
                      apply not_mem
                      rcases contra with ⟨i, contra⟩
                      apply contra
                      simp only [disj_index_zero] at h
                      unfold PreTrigger.result at h
                      rw [List.getElem_map, ← List.inIffInToSet] at h
                      have : i.val = 0 := by
                        have isLt := i.isLt
                        simp only [← PreTrigger.head_length_eq_mapped_head_length] at isLt
                        rw [det _ trg.property, Nat.lt_one_iff] at isLt
                        exact isLt
                      rw [← List.inIffInToSet, List.get_eq_getElem]
                      simp only [this]
                      exact h
                  . simp only [disj_index_zero] at h
                    exact h
    . intro h
      rcases h with ⟨n, h⟩
      induction n generalizing f with
      | zero =>
        exists 0
        rw [cb.database_first, Option.is_some_and]
        exact h
      | succ n ih =>
        -- we need to invoke fairness somehow
        unfold parallelSkolemChase at h
        cases h with
        | inl h => exact ih _ h
        | inr h =>
          rcases h with ⟨trg, trg_active, f_mem⟩

          have trg_loaded_somewhere : ∃ n, (cb.branch.infinite_list n).is_some_and (fun node => trg.val.loaded node.fact.val) := by
            have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e ∈ trg.val.mapped_body) -> ∃ n, (cb.branch.infinite_list n).is_some_and (fun node => (∀ e, e ∈ l -> e ∈ node.fact.val)) := by
              intro l l_sub
              induction l with
              | nil => exists 0; rw [cb.database_first, Option.is_some_and]; simp
              | cons hd tl ih_inner =>
                have from_ih := ih_inner (by intro f f_mem; apply l_sub; simp [f_mem])
                rcases from_ih with ⟨n_from_ih, from_ih⟩

                cases eq_from_ih : cb.branch.infinite_list n_from_ih with
                | none => rw [eq_from_ih, Option.is_some_and] at from_ih; simp at from_ih
                | some node_from_ih =>
                rw [eq_from_ih, Option.is_some_and] at from_ih

                have from_hd := ih hd (by apply trg_active.left; rw [← List.inIffInToSet]; apply l_sub; simp)
                rcases from_hd with ⟨n_from_hd, from_hd⟩

                cases eq_from_hd : cb.branch.infinite_list n_from_hd with
                | none => rw [eq_from_hd, Option.is_some_and] at from_hd; simp at from_hd
                | some node_from_hd =>
                rw [eq_from_hd, Option.is_some_and] at from_hd

                cases Decidable.em (n_from_ih ≤ n_from_hd) with
                | inl le =>
                  exists n_from_hd
                  rw [eq_from_hd, Option.is_some_and]
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inl f_mem => rw [f_mem]; exact from_hd
                  | inr f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    have subsetAllFollowing := chaseBranchSetIsSubsetOfAllFollowing cb n_from_ih diff
                    simp only [eq_from_ih] at subsetAllFollowing
                    rw [← le, eq_from_hd, Option.is_none_or] at subsetAllFollowing
                    apply subsetAllFollowing
                    apply from_ih; exact f_mem
                | inr lt =>
                  simp at lt
                  have le := Nat.le_of_lt lt
                  exists n_from_ih
                  rw [eq_from_ih, Option.is_some_and]
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inr f_mem => apply from_ih; exact f_mem
                  | inl f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    have subsetAllFollowing := chaseBranchSetIsSubsetOfAllFollowing cb n_from_hd diff
                    simp only [eq_from_hd] at subsetAllFollowing
                    rw [← le, eq_from_ih, Option.is_none_or] at subsetAllFollowing
                    apply subsetAllFollowing
                    rw [f_mem]; exact from_hd

            specialize this trg.val.mapped_body (by simp)
            rcases this with ⟨n, this⟩
            exists n
            cases eq : cb.branch.infinite_list n with
            | none => rw [eq, Option.is_some_and] at this; simp at this
            | some node =>
              rw [Option.is_some_and]
              rw [eq, Option.is_some_and] at this
              intro f
              rw [← List.inIffInToSet]
              apply this
          rcases trg_loaded_somewhere with ⟨loaded_n, trg_loaded_somewhere⟩
          cases eq_node_loaded : cb.branch.infinite_list loaded_n with
          | none => rw [eq_node_loaded, Option.is_some_and] at trg_loaded_somewhere; simp at trg_loaded_somewhere
          | some node_loaded =>
          rw [eq_node_loaded, Option.is_some_and] at trg_loaded_somewhere

          have fair := cb.fairness trg
          rcases fair with ⟨fairness_n, fair⟩
          cases eq_node_fairness : cb.branch.infinite_list fairness_n with
          | none => rw [eq_node_fairness, Option.is_some_and] at fair; simp at fair
          | some node_fairness =>
          rw [eq_node_fairness, Option.is_some_and] at fair

          cases Decidable.em (loaded_n ≤ fairness_n) with
          | inl le =>
            exists fairness_n
            rw [eq_node_fairness, Option.is_some_and]
            have trg_not_active := fair.left
            unfold Trigger.active at trg_not_active
            simp only [not_and, Classical.not_not] at trg_not_active

            have trg_loaded : trg.val.loaded node_fairness.fact.val := by
              intro f f_mem
              rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
              have subsetAllFollowing := chaseBranchSetIsSubsetOfAllFollowing cb loaded_n diff
              simp only [eq_node_loaded] at subsetAllFollowing
              rw [← le, eq_node_fairness, Option.is_none_or] at subsetAllFollowing
              apply subsetAllFollowing
              apply trg_loaded_somewhere
              exact f_mem

            specialize trg_not_active trg_loaded
            rcases trg_not_active with ⟨disj_index, trg_not_active⟩
            apply trg_not_active
            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              simp only [← PreTrigger.head_length_eq_mapped_head_length] at isLt
              rw [det _ trg.property, Nat.lt_one_iff] at isLt
              exact isLt
            unfold PreTrigger.result at f_mem
            rw [List.getElem_map, ← List.inIffInToSet] at f_mem
            rw [← List.inIffInToSet, List.get_eq_getElem]
            simp only [disj_index_zero]
            exact f_mem
          | inr lt =>
            simp at lt

            exists loaded_n
            rw [eq_node_loaded, Option.is_some_and]
            have trg_not_active := fair.right loaded_n lt
            rw [eq_node_loaded, Option.is_none_or] at trg_not_active
            unfold Trigger.active at trg_not_active
            simp only [not_and, Classical.not_not] at trg_not_active

            specialize trg_not_active trg_loaded_somewhere
            rcases trg_not_active with ⟨disj_index, trg_not_active⟩
            apply trg_not_active
            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              simp only [← PreTrigger.head_length_eq_mapped_head_length] at isLt
              rw [det _ trg.property, Nat.lt_one_iff] at isLt
              exact isLt
            unfold PreTrigger.result at f_mem
            rw [List.getElem_map, ← List.inIffInToSet] at f_mem
            rw [← List.inIffInToSet, List.get_eq_getElem]
            simp only [disj_index_zero]
            exact f_mem

end KnowledgeBase

namespace RuleSet

  def criticalInstance (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : Database sig :=
    ⟨fun f => f.predicate ∈ rs.predicates ∧ ∀ t, t ∈ f.terms -> t = special_const, by
      have preds_finite := rs.predicates_finite_of_finite finite
      rcases preds_finite with ⟨l, nodup, eq⟩
      exists (l.map (fun p => {
        predicate := p
        terms := List.repeat special_const (sig.arity p)
        arity_ok := by rw [List.length_repeat]
      })).eraseDupsKeepRight
      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro f
        rw [List.mem_eraseDupsKeepRight_iff]
        simp [Set.element]
        constructor
        . intro h
          rcases h with ⟨p, p_mem, f_eq⟩
          rw [← f_eq]
          rw [eq] at p_mem
          constructor
          . exact p_mem
          . intro t
            apply List.mem_repeat
        . intro h
          exists f.predicate
          constructor
          . rw [eq]; exact h.left
          . rw [FunctionFreeFact.ext_iff]
            simp
            rw [List.repeat_eq_iff_all_val]
            constructor
            . exact f.arity_ok
            . exact h.right
    ⟩

  def mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (det : rs.isDeterministic) (special_const : sig.C) : FactSet sig :=
    let kb : KnowledgeBase sig := {
      rules := rs
      db := criticalInstance rs finite special_const
    }
    kb.skolemChaseResult det

  theorem mfaSet_contains_every_chase_step_for_every_kb_expect_for_facts_with_predicates_not_from_rs (rs : RuleSet sig) (finite : rs.rules.finite) (det : rs.isDeterministic) (special_const : sig.C) : ∀ {db : Database sig} (cb : ChaseBranch (SkolemObsoleteness sig) { rules := rs, db := db }) (n : Nat), (cb.branch.infinite_list n).is_none_or (fun node => ∀ f, f.predicate ∈ rs.predicates -> f ∈ (ConstantMapping.apply_fact_set (fun _ => GroundTerm.const special_const) node.fact.val) -> f ∈ (rs.mfaSet finite det special_const)) := by
    intro db cb n
    induction n with
    | zero =>
      rw [cb.database_first, Option.is_none_or]
      simp only
      intro f f_predicate f_mem
      exists 0
      unfold KnowledgeBase.parallelSkolemChase
      unfold Database.toFactSet
      unfold criticalInstance
      simp only

      unfold ConstantMapping.apply_fact_set at f_mem
      rcases f_mem with ⟨f', f'_mem, f_eq⟩

      have every_t_special_const : ∀ t, t ∈ f.terms -> t = GroundTerm.const special_const := by
        intro t t_mem
        rw [f_eq] at t_mem
        unfold ConstantMapping.apply_fact at t_mem
        simp only [List.mem_map] at t_mem
        rcases t_mem with ⟨s, s_mem, t_eq⟩

        have isFunctionFree := db.toFactSet.property.right
        specialize isFunctionFree _ f'_mem
        specialize isFunctionFree _ s_mem
        rcases isFunctionFree with ⟨c, s_eq⟩
        rw [← t_eq, s_eq]
        simp [ConstantMapping.apply_ground_term, FiniteTree.mapLeaves]
      have f_func_free : f.isFunctionFree := by
        intro t t_mem
        exists special_const
        apply every_t_special_const
        exact t_mem

      exists f.toFunctionFreeFact f_func_free
      constructor
      . unfold Fact.toFunctionFreeFact
        constructor
        . exact f_predicate
        . simp
          intro c t t_mem c_eq
          specialize every_t_special_const t t_mem
          rw [← c_eq]
          simp only [every_t_special_const]
          simp [GroundTerm.toConst]
      . rw [Fact.toFact_after_toFunctionFreeFact_is_id]
    | succ n ih =>
      cases eq_node : cb.branch.infinite_list (n+1) with
      | none => simp [Option.is_none_or]
      | some node =>
        rw [Option.is_none_or]
        cases eq_prev_node : cb.branch.infinite_list n with
        | none => have no_holes := cb.branch.no_holes (n+1); simp [eq_node] at no_holes; specialize no_holes ⟨n, by simp⟩; contradiction
        | some prev_node =>
          rw [eq_prev_node, Option.is_none_or] at ih

          have trg_ex := cb.triggers_exist n
          rw [eq_prev_node, Option.is_none_or] at trg_ex
          cases trg_ex with
          | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [eq_node] at trg_ex; simp at trg_ex
          | inl trg_ex =>
            unfold exists_trigger_opt_fs at trg_ex
            rcases trg_ex with ⟨trg, trg_active, disj_index, trg_result_eq⟩
            rw [eq_node] at trg_result_eq
            injection trg_result_eq with trg_result_eq

            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              unfold PreTrigger.result at isLt
              simp only [List.length_map] at isLt
              rw [← PreTrigger.head_length_eq_mapped_head_length] at isLt
              rw [det _ trg.property, Nat.lt_one_iff] at isLt
              exact isLt

            intro f f_predicate f_mem
            rcases f_mem with ⟨f', f'_mem, f_eq⟩
            simp only [← trg_result_eq] at f'_mem
            cases f'_mem with
            | inl f'_mem =>
              apply ih
              . exact f_predicate
              . exists f'
            | inr f'_mem =>
              unfold RuleSet.mfaSet
              unfold KnowledgeBase.skolemChaseResult

              have : ∃ n, (ConstantMapping.apply_fact_set (fun _ => GroundTerm.const special_const) prev_node.fact.val) ⊆ { rules := rs, db := rs.criticalInstance finite special_const : KnowledgeBase sig }.parallelSkolemChase det n := by
                sorry

              rcases this with ⟨n, prev_node_subs_parallel_chase⟩
              exists (n+1)
              unfold KnowledgeBase.parallelSkolemChase
              apply Or.inr
              exists ⟨⟨trg.val.rule, (ConstantMapping.apply_ground_term (fun _ => GroundTerm.const special_const)) ∘ trg.val.subs⟩, by exact trg.property⟩
              constructor
              . sorry
              . unfold PreTrigger.result at f'_mem
                simp only [List.get_eq_getElem, disj_index_zero] at f'_mem
                rw [List.getElem_map, ← List.inIffInToSet] at f'_mem
                unfold PreTrigger.mapped_head at f'_mem
                simp at f'_mem
                rcases f'_mem with ⟨a, a_mem, f'_eq⟩

                unfold PreTrigger.result
                rw [List.getElem_map, ← List.inIffInToSet]
                unfold PreTrigger.mapped_head
                simp
                exists a
                constructor
                . exact a_mem
                . rw [f_eq, ← f'_eq]
                  unfold PreTrigger.apply_to_function_free_atom
                  unfold ConstantMapping.apply_fact
                  unfold PreTrigger.apply_to_var_or_const
                  unfold PreTrigger.apply_to_skolemized_term
                  unfold PreTrigger.skolemize_var_or_const
                  simp?
                  sorry

end RuleSet

