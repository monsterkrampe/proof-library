import ProofLibrary.ChaseSequence.Termination.Basic

section Defs

  variable (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  -- This is essentially the same as a GroundSubstitution only that it maps constants instead of variables
  abbrev ConstantMapping := sig.C -> GroundTerm sig

  abbrev StrictConstantMapping := sig.C -> sig.C

  abbrev UniformConstantMapping (c : sig.C) : StrictConstantMapping sig := fun _ => c

end Defs


namespace ConstantMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def apply_ground_term (g : ConstantMapping sig) (t : GroundTerm sig) : GroundTerm sig := t.mapLeaves g

  theorem apply_ground_term_swap_apply_skolem_term (g : ConstantMapping sig) (subs : GroundSubstitution sig) : ∀ t, (∀ c, t ≠ SkolemTerm.const c) -> g.apply_ground_term (subs.apply_skolem_term t) = GroundSubstitution.apply_skolem_term (g.apply_ground_term ∘ subs) t := by
    intro t
    cases t with
    | var v =>
      intros
      unfold GroundSubstitution.apply_skolem_term
      simp
    | const c => simp
    | func f ts =>
      intros
      conv => left; unfold ConstantMapping.apply_ground_term; unfold FiniteTree.mapLeaves; unfold GroundSubstitution.apply_skolem_term
      conv => right; unfold GroundSubstitution.apply_skolem_term
      simp
      rw [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
      unfold ConstantMapping.apply_ground_term
      rw [List.map_map]
      rfl


  variable [DecidableEq sig.P]

  def apply_fact (g : ConstantMapping sig) (f : Fact sig) : Fact sig := {
    predicate := f.predicate
    terms := f.terms.map g.apply_ground_term
    arity_ok := by rw [List.length_map]; exact f.arity_ok
  }

  theorem apply_fact_swap_apply_to_function_free_atom (g : ConstantMapping sig) (trg : PreTrigger sig) (a : FunctionFreeAtom sig) (h : ∃ c, (∀ d, g d = c) ∧ (∀ d, VarOrConst.const d ∈ a.terms -> c = GroundTerm.const d)) : ∀ i, g.apply_fact (trg.apply_to_function_free_atom i a) = PreTrigger.apply_to_function_free_atom { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs } i a := by
    intro i
    unfold PreTrigger.apply_to_function_free_atom
    unfold ConstantMapping.apply_fact
    unfold PreTrigger.apply_to_var_or_const
    unfold PreTrigger.apply_to_skolemized_term
    unfold PreTrigger.skolemize_var_or_const
    simp
    intro voc voc_mem
    cases voc with
    | var v =>
      rw [ConstantMapping.apply_ground_term_swap_apply_skolem_term]
      intro c contra
      simp [VarOrConst.skolemize] at contra
      split at contra <;> contradiction
    | const d =>
      unfold VarOrConst.skolemize
      unfold GroundSubstitution.apply_skolem_term
      unfold ConstantMapping.apply_ground_term
      unfold FiniteTree.mapLeaves
      simp only
      rcases h with ⟨c, g_eq, mem_a_eq⟩
      rw [g_eq]
      apply mem_a_eq
      exact voc_mem

  def apply_fact_set (g : ConstantMapping sig) (fs : FactSet sig) : FactSet sig := fun f => ∃ f', f' ∈ fs ∧ f = g.apply_fact f'

  theorem apply_fact_mem_apply_fact_set_of_mem (g : ConstantMapping sig) (f : Fact sig) (fs : FactSet sig) : f ∈ fs -> g.apply_fact f ∈ g.apply_fact_set fs := by
    intro f_mem
    exists f

end ConstantMapping

namespace StrictConstantMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def toConstantMapping (g : StrictConstantMapping sig) : ConstantMapping sig := fun c => GroundTerm.const (g c)

  def apply_var_or_const (g : StrictConstantMapping sig) : VarOrConst sig -> VarOrConst sig
  | .var v => .var v
  | .const c => .const (g c)

  theorem apply_var_or_const_filterVars_eq (g : StrictConstantMapping sig) (vocs : List (VarOrConst sig)) : VarOrConst.filterVars (vocs.map g.apply_var_or_const) = VarOrConst.filterVars vocs := by
    induction vocs with
    | nil => simp
    | cons hd tl ih =>
      cases hd <;> (
        simp only [VarOrConst.filterVars, StrictConstantMapping.apply_var_or_const]
        rw [ih]
      )


  variable [DecidableEq sig.P]

  def apply_function_free_atom (g : StrictConstantMapping sig) (a : FunctionFreeAtom sig) : FunctionFreeAtom sig := {
    predicate := a.predicate
    terms := a.terms.map g.apply_var_or_const
    arity_ok := by rw [List.length_map]; exact a.arity_ok
  }

  theorem apply_function_free_atom_vars_eq (g : StrictConstantMapping sig) (a : FunctionFreeAtom sig) : (g.apply_function_free_atom a).variables = a.variables := by
    unfold apply_function_free_atom
    unfold FunctionFreeAtom.variables
    simp only
    rw [apply_var_or_const_filterVars_eq]

  def apply_function_free_conj (g : StrictConstantMapping sig) (conj : FunctionFreeConjunction sig) : FunctionFreeConjunction sig := conj.map g.apply_function_free_atom

  theorem apply_function_free_conj_vars_eq (g : StrictConstantMapping sig) (conj : FunctionFreeConjunction sig) : (g.apply_function_free_conj conj).vars = conj.vars := by
    unfold apply_function_free_conj
    unfold FunctionFreeConjunction.vars
    rw [List.map_map]
    have : conj.map (FunctionFreeAtom.variables ∘ g.apply_function_free_atom) = conj.map FunctionFreeAtom.variables := by
      simp only [List.map_inj_left]
      intro a a_mem
      rw [Function.comp_apply]
      apply apply_function_free_atom_vars_eq
    rw [this]

  def apply_rule (g : StrictConstantMapping sig) (rule : Rule sig) : Rule sig := {
    id := rule.id
    body := g.apply_function_free_conj rule.body
    head := rule.head.map g.apply_function_free_conj
  }

  theorem apply_rule_id_eq (g : StrictConstantMapping sig) (rule : Rule sig) : (g.apply_rule rule).id = rule.id := by simp [apply_rule]

  theorem apply_rule_frontier_eq (g : StrictConstantMapping sig) (rule : Rule sig) : (g.apply_rule rule).frontier = rule.frontier := by
    unfold apply_rule
    unfold Rule.frontier
    rw [apply_function_free_conj_vars_eq]
    apply List.filter_eq_of_all_eq
    intro e e_mem
    simp only [List.any_eq, decide_eq_decide, decide_eq_true_eq, List.mem_map]
    constructor
    . intro h
      rcases h with ⟨applied, h, mem_applied⟩
      rcases h with ⟨conj, conj_mem, h⟩
      exists conj
      constructor
      . exact conj_mem
      . rw [← h] at mem_applied
        rw [apply_function_free_conj_vars_eq] at mem_applied
        exact mem_applied
    . intro h
      rcases h with ⟨conj, conj_mem, h⟩
      exists g.apply_function_free_conj conj
      constructor
      . exists conj
      . rw [apply_function_free_conj_vars_eq]
        exact h

end StrictConstantMapping


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

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

  def mfaKb (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : KnowledgeBase sig := {
    rules := {
      rules := fun r => ∃ r', r' ∈ rs.rules ∧ r = (UniformConstantMapping sig special_const).apply_rule r'
      id_unique := by
        intro r1 r2 h
        rcases h with ⟨r1_mem, r2_mem, id_eq⟩
        rcases r1_mem with ⟨r1', r1'_mem, r1_eq⟩
        rcases r2_mem with ⟨r2', r2'_mem, r2_eq⟩
        have : r1' = r2' := by
          apply rs.id_unique
          constructor
          . exact r1'_mem
          constructor
          . exact r2'_mem
          rw [r1_eq, r2_eq] at id_eq
          simp only [StrictConstantMapping.apply_rule] at id_eq
          exact id_eq
        rw [r1_eq, this, r2_eq]
    }
    db := criticalInstance rs finite special_const
  }

  theorem mfaKb_det_of_rs_det (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : rs.isDeterministic -> (rs.mfaKb finite special_const).rules.isDeterministic := by
    intro det r r_mem
    rcases r_mem with ⟨r', r'_mem, r_eq⟩
    rw [r_eq]
    unfold StrictConstantMapping.apply_rule
    unfold Rule.isDeterministic
    simp only [List.length_map]
    exact det r' r'_mem

  def mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (det : rs.isDeterministic) (special_const : sig.C) : FactSet sig :=
    (rs.mfaKb finite special_const).skolemChaseResult (mfaKb_det_of_rs_det rs finite special_const det)

  theorem mfaSet_contains_every_chase_step_for_every_kb_expect_for_facts_with_predicates_not_from_rs (rs : RuleSet sig) (finite : rs.rules.finite) (det : rs.isDeterministic) (special_const : sig.C) : ∀ {db : Database sig} (cb : ChaseBranch obs { rules := rs, db := db }) (n : Nat), (cb.branch.infinite_list n).is_none_or (fun node => ∀ f, f.predicate ∈ rs.predicates -> f ∈ node.fact.val -> ((UniformConstantMapping sig special_const).toConstantMapping.apply_fact f) ∈ (rs.mfaSet finite det special_const)) := by
    intro db cb n
    induction n with
    | zero =>
      rw [cb.database_first, Option.is_none_or]
      simp only
      intro f f_predicate f_mem
      exists 0
      unfold KnowledgeBase.parallelSkolemChase
      unfold Database.toFactSet
      unfold RuleSet.mfaKb
      unfold criticalInstance
      simp only

      have every_t_special_const : ∀ t, t ∈ ((UniformConstantMapping sig special_const).toConstantMapping.apply_fact f).terms -> t = GroundTerm.const special_const := by
        intro t t_mem
        unfold ConstantMapping.apply_fact at t_mem
        simp only [List.mem_map] at t_mem
        rcases t_mem with ⟨s, s_mem, t_eq⟩

        have isFunctionFree := db.toFactSet.property.right
        specialize isFunctionFree _ f_mem
        specialize isFunctionFree _ s_mem
        rcases isFunctionFree with ⟨c, s_eq⟩
        rw [← t_eq, s_eq]
        simp [ConstantMapping.apply_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping]
      have f_func_free : ((UniformConstantMapping sig special_const).toConstantMapping.apply_fact f).isFunctionFree := by
        intro t t_mem
        exists special_const
        apply every_t_special_const
        exact t_mem

      exists ((UniformConstantMapping sig special_const).toConstantMapping.apply_fact f).toFunctionFreeFact f_func_free
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
            simp only [← trg_result_eq] at f_mem
            cases f_mem with
            | inl f_mem =>
              apply ih
              . exact f_predicate
              . exact f_mem
            | inr f_mem =>
              unfold RuleSet.mfaSet
              unfold KnowledgeBase.skolemChaseResult

              have : ∃ n, ∀ f, f.predicate ∈ rs.predicates -> f ∈ prev_node.fact.val -> ((UniformConstantMapping sig special_const).toConstantMapping.apply_fact f) ∈ (rs.mfaKb finite special_const).parallelSkolemChase (rs.mfaKb_det_of_rs_det finite special_const det) n := by
                let kb := rs.mfaKb finite special_const
                have kb_det := (rs.mfaKb_det_of_rs_det finite special_const det)
                let prev_filtered : FactSet sig := fun f => f.predicate ∈ rs.predicates ∧ f ∈ prev_node.fact.val
                have prev_finite : prev_filtered.finite := by
                  rcases prev_node.fact.property with ⟨prev_l, _, prev_l_eq⟩
                  rcases (RuleSet.predicates_finite_of_finite _ finite) with ⟨preds_l, _, preds_l_eq⟩
                  exists (prev_l.filter (fun f => f.predicate ∈ preds_l)).eraseDupsKeepRight
                  constructor
                  . apply List.nodup_eraseDupsKeepRight
                  . intro f
                    rw [List.mem_eraseDupsKeepRight_iff, List.mem_filter]
                    rw [prev_l_eq]
                    unfold prev_filtered
                    simp [preds_l_eq, Set.element, And.comm]
                rcases prev_finite with ⟨prev_l, _, prev_l_eq⟩

                have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e.predicate ∈ rs.predicates ∧ e ∈ prev_node.fact.val) -> ∃ n, (∀ e, e ∈ l -> ((UniformConstantMapping sig special_const).toConstantMapping.apply_fact e) ∈ (kb.parallelSkolemChase kb_det n)) := by
                  intro l l_sub
                  induction l with
                  | nil => exists 0; intro e; simp
                  | cons hd tl ih_inner =>
                    have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
                    rcases from_ih with ⟨n_from_ih, from_ih⟩

                    have from_hd := ih hd (l_sub hd (by simp)).left (l_sub hd (by simp)).right
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
                        apply kb.parallelSkolemChase_subset_all_following kb_det n_from_ih diff
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
                        apply kb.parallelSkolemChase_subset_all_following kb_det n_from_hd diff
                        rw [f_mem]; exact from_hd

                specialize this prev_l (by
                  intro f f_mem
                  rw [prev_l_eq] at f_mem
                  unfold prev_filtered at f_mem
                  exact f_mem
                )

                rcases this with ⟨n, this⟩
                exists n
                intro f f_pred f_mem
                specialize this f (by
                  rw [prev_l_eq]
                  unfold prev_filtered
                  constructor
                  . exact f_pred
                  . exact f_mem
                )
                exact this

              rcases this with ⟨n, prev_node_subs_parallel_chase⟩
              exists (n+1)
              unfold KnowledgeBase.parallelSkolemChase
              simp only [Set.element]

              rw [Classical.or_iff_not_imp_left]
              intro f_not_in_prev

              exists ⟨⟨(UniformConstantMapping sig special_const).apply_rule trg.val.rule, (UniformConstantMapping sig special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs⟩, by
                simp only [RuleSet.mfaKb]
                exists trg.val.rule
                constructor
                . exact trg.property
                . rfl
              ⟩
              constructor
              . constructor
                . apply Set.subsetTransitive _ (fun f => f.predicate ∈ rs.predicates ∧ f ∈ ((UniformConstantMapping sig special_const).toConstantMapping.apply_fact_set prev_node.fact.val)) _
                  constructor
                  . intro f f_mem
                    rw [← List.inIffInToSet] at f_mem
                    simp only [PreTrigger.mapped_body, SubsTarget.apply, GroundSubstitution.apply_function_free_conj, List.mem_map] at f_mem
                    rcases f_mem with ⟨a, a_mem, f_eq⟩
                    unfold StrictConstantMapping.apply_rule at a_mem
                    unfold StrictConstantMapping.apply_function_free_conj at a_mem
                    simp only [List.mem_map] at a_mem
                    rcases a_mem with ⟨a', a'_mem, a_eq⟩
                    simp only [Set.element]
                    constructor
                    . rw [← f_eq]
                      simp only [GroundSubstitution.apply_function_free_atom]
                      unfold RuleSet.predicates
                      exists trg.val.rule
                      constructor
                      . exact trg.property
                      . unfold Rule.predicates
                        rw [List.mem_append]
                        apply Or.inl
                        unfold FunctionFreeConjunction.predicates
                        rw [List.mem_map]
                        exists a'
                        constructor
                        . exact a'_mem
                        . rw [← a_eq]
                          simp [StrictConstantMapping.apply_function_free_atom]
                    . exists trg.val.subs.apply_function_free_atom a'
                      constructor
                      . apply trg_active.left
                        rw [← List.inIffInToSet]
                        simp only [PreTrigger.mapped_body, SubsTarget.apply, GroundSubstitution.apply_function_free_conj, List.mem_map]
                        exists a'
                      . rw [← f_eq]
                        unfold ConstantMapping.apply_fact
                        unfold GroundSubstitution.apply_function_free_atom

                        -- we need to apply g to every constant in every rule in rs to achieve this
                        rw [← a_eq]
                        simp [StrictConstantMapping.apply_function_free_atom]
                        intro voc voc_mem
                        cases voc with
                        | var v =>
                          simp [GroundSubstitution.apply_var_or_const, StrictConstantMapping.apply_var_or_const]
                        | const c =>
                          simp [GroundSubstitution.apply_var_or_const, StrictConstantMapping.apply_var_or_const, ConstantMapping.apply_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping]
                  . intro f f_mem
                    rcases f_mem with ⟨f_pred, f', f'_mem, f_eq⟩
                    rw [f_eq]
                    apply prev_node_subs_parallel_chase
                    . rw [f_eq] at f_pred
                      simp only [ConstantMapping.apply_fact] at f_pred
                      exact f_pred
                    . exact f'_mem
                . intro contra
                  simp only [SkolemObsoleteness] at contra
                  rcases contra with ⟨i, contra⟩

                  have i_zero : i.val = 0 := by
                    have isLt := i.isLt
                    simp only [← PreTrigger.head_length_eq_mapped_head_length] at isLt
                    unfold StrictConstantMapping.apply_rule at isLt
                    simp only [List.length_map] at isLt
                    rw [det _ trg.property, Nat.lt_one_iff] at isLt
                    exact isLt
                  apply f_not_in_prev
                  apply contra
                  rw [← List.inIffInToSet, List.get_eq_getElem]
                  simp only [i_zero]
                  unfold PreTrigger.mapped_head
                  simp
                  unfold PreTrigger.result at f_mem
                  unfold PreTrigger.mapped_head at f_mem
                  rw [List.get_eq_getElem] at f_mem
                  simp only [disj_index_zero] at f_mem
                  simp at f_mem
                  rw [← List.inIffInToSet, List.mem_map] at f_mem
                  rcases f_mem with ⟨a, a_mem, f_eq⟩

                  exists (UniformConstantMapping sig special_const).apply_function_free_atom a
                  constructor
                  . unfold StrictConstantMapping.apply_rule
                    unfold StrictConstantMapping.apply_function_free_conj
                    simp only [List.getElem_map, List.mem_map]
                    exists a
                  . rw [← f_eq]
                    simp only [ConstantMapping.apply_fact, PreTrigger.apply_to_function_free_atom, StrictConstantMapping.apply_function_free_atom, PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, PreTrigger.apply_to_skolemized_term, Fact.mk.injEq, true_and, List.map_map, List.map_inj_left, Function.comp_apply]
                    intro voc voc_mem
                    cases voc with
                    | var v =>
                      simp only [StrictConstantMapping.apply_var_or_const]
                      rw [← ConstantMapping.apply_ground_term_swap_apply_skolem_term]
                      . rw [StrictConstantMapping.apply_rule_id_eq, StrictConstantMapping.apply_rule_frontier_eq]
                      . intros
                        unfold VarOrConst.skolemize
                        simp only
                        split <;> simp
                    | const c =>
                      simp only [StrictConstantMapping.apply_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, ConstantMapping.apply_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping]
              . unfold PreTrigger.result at f_mem
                simp only [List.get_eq_getElem, disj_index_zero] at f_mem
                rw [List.getElem_map, ← List.inIffInToSet] at f_mem
                unfold PreTrigger.mapped_head at f_mem
                simp at f_mem
                rcases f_mem with ⟨a, a_mem, f_eq⟩

                unfold PreTrigger.result
                rw [List.getElem_map]
                apply List.listElementAlsoToSetElement
                unfold PreTrigger.mapped_head
                simp

                exists (UniformConstantMapping sig special_const).apply_function_free_atom a
                constructor
                . unfold StrictConstantMapping.apply_rule
                  unfold StrictConstantMapping.apply_function_free_conj
                  simp only [List.getElem_map, List.mem_map]
                  exists a
                . rw [← f_eq]
                  simp only [ConstantMapping.apply_fact, PreTrigger.apply_to_function_free_atom, StrictConstantMapping.apply_function_free_atom, PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, PreTrigger.apply_to_skolemized_term, Fact.mk.injEq, true_and, List.map_map, List.map_inj_left, Function.comp_apply]
                  intro voc voc_mem
                  cases voc with
                  | var v =>
                    simp only [StrictConstantMapping.apply_var_or_const]
                    rw [← ConstantMapping.apply_ground_term_swap_apply_skolem_term]
                    . rw [StrictConstantMapping.apply_rule_id_eq, StrictConstantMapping.apply_rule_frontier_eq]
                    . intros
                      unfold VarOrConst.skolemize
                      simp only
                      split <;> simp
                  | const c =>
                    simp only [StrictConstantMapping.apply_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, ConstantMapping.apply_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping]

end RuleSet

