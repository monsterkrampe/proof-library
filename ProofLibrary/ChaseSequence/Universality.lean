import ProofLibrary.ChaseSequence.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

abbrev InductiveHomomorphismResult (ct : ChaseTree obs kb) (m : FactSet sig) (depth : Nat) := {pair : (List Nat) × (GroundTermMapping sig) // pair.1.length = depth ∧ (ct.tree.get pair.1).is_none_or (fun fs => pair.2.isHomomorphism fs.fact m) }

-- TODO: split up the following definition (rather the proofs inside) to get rid of heartbeat increase
set_option maxHeartbeats 1000000

noncomputable def inductive_homomorphism_with_prev_node_and_trg (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : InductiveHomomorphismResult ct m (prev_depth + 1) :=
  let prev_path := prev_result.val.fst
  let prev_hom := prev_result.val.snd
  let prev_cond := prev_result.property
  have prev_hom_is_homomorphism : prev_hom.isHomomorphism prev_node_unwrapped.fact m := by
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
    have : trg_variant_for_m.val.loaded (prev_hom.applyFactSet prev_node_unwrapped.fact) := by
      apply PreTrigger.term_mapping_preserves_loadedness
      . exact prev_hom_is_homomorphism.left
      . exact trg_active_for_current_step.left
    apply Set.subsetTransitive
    exact ⟨this, prev_hom_is_homomorphism.right⟩
  have trg_variant_satisfied_on_m : trg_variant_for_m.val.satisfied m := by
    have m_models_rule : m.modelsRule trg_variant_for_m.val.rule := by exact m_is_model.right trg.val.rule trg.property
    unfold FactSet.modelsRule at m_models_rule
    apply m_models_rule
    apply trg_variant_loaded_for_m

  let obs_for_m_subs := Classical.choose trg_variant_satisfied_on_m
  let h_obs_for_m_subs := Classical.choose_spec trg_variant_satisfied_on_m
  let head_index_for_m_subs := Classical.choose h_obs_for_m_subs
  let h_obs_at_head_index_for_m_subs := Classical.choose_spec h_obs_for_m_subs

  let result_index_for_trg : Fin trg.val.result.length := ⟨head_index_for_m_subs.val, by unfold PreTrigger.result; unfold PreTrigger.mapped_head; simp [List.enum_with_lt_length_eq]⟩

  let next_hom : GroundTermMapping sig := fun t =>
    match t with
    | FiniteTree.leaf _ => t
    | FiniteTree.inner _ _ =>
      let t_in_step_j_dec := Classical.propDecidable (∃ f, f ∈ prev_node_unwrapped.fact.val ∧ t ∈ f.terms.toSet)
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
        unfold GroundTermMapping.applyFact
        simp
        intro ground_term _
        have : ∃ f, f ∈ prev_node_unwrapped.fact.val ∧ ground_term ∈ f.terms.toSet := by
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
        unfold GroundTermMapping.applyFact

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
        let head_disjunct : List (FunctionFreeAtom sig) := trg.val.rule.head[head_index_for_m_subs.val]
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

noncomputable def inductive_homomorphism_with_prev_node (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) : InductiveHomomorphismResult ct m (prev_depth + 1) :=
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

noncomputable def inductive_homomorphism (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) : (depth : Nat) ->
  InductiveHomomorphismResult ct m depth
| .zero => ⟨([], id), by
  simp [Option.is_none_or]; rw [ct.database_first]; simp
  constructor
  . unfold GroundTermMapping.isIdOnConstants; intro gt ; cases gt <;> simp
  . intro el
    simp [Set.element]
    intro el_in_set
    cases el_in_set with | intro f hf =>
      apply m_is_model.left
      simp [Set.element]
      have : f = el := by have hfr := hf.right; simp [GroundTermMapping.applyFact, List.map_id'] at hfr; exact hfr
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

theorem inductive_homomorphism_with_prev_node_and_trg_path_not_empty (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1 ≠ [] := by
  unfold inductive_homomorphism_with_prev_node_and_trg
  simp

theorem inductive_homomorphism_path_not_empty {ct : ChaseTree obs kb} : ∀ n, (inductive_homomorphism ct m m_is_model (n+1)).val.1 ≠ [] := by
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

theorem inductive_homomorphism_with_prev_node_and_trg_path_extends_prev (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1 = ((inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1.head (by apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty)) :: prev_result.val.fst := by
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
    have prev_hom_is_homomorphism : prev_hom.isHomomorphism prev_node.fact m := by
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
      have : trg_variant_for_m.val.loaded (prev_hom.applyFactSet prev_node.fact) := by
        apply PreTrigger.term_mapping_preserves_loadedness
        . exact prev_hom_is_homomorphism.left
        . exact trg_active_for_current_step.left
      apply Set.subsetTransitive
      exact ⟨this, prev_hom_is_homomorphism.right⟩
    have trg_variant_satisfied_on_m : trg_variant_for_m.val.satisfied m := by
      have m_models_rule : m.modelsRule trg_variant_for_m.val.rule := by exact m_is_model.right trg.val.rule trg.property
      unfold FactSet.modelsRule at m_models_rule
      apply m_models_rule
      apply trg_variant_loaded_for_m

    let h_obs_for_m_subs := Classical.choose_spec trg_variant_satisfied_on_m
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

theorem inductive_homomorphism_same_on_terms_in_next_step (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) : ∀ i, (ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst).is_none_or (fun node => ∀ f t, f ∈ node.fact.val ∧ t ∈ f.terms.toSet -> (inductive_homomorphism ct m m_is_model i).val.snd t = (inductive_homomorphism ct m m_is_model i.succ).val.snd t) := by
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

theorem inductive_homomorphism_same_on_all_following_terms (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) : ∀ i, (ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst).is_none_or (fun node => ∀ j f t, f ∈ node.fact.val ∧ t ∈ f.terms.toSet -> (inductive_homomorphism ct m m_is_model i).val.snd t = (inductive_homomorphism ct m m_is_model (i+j)).val.snd t) := by
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

theorem chaseTreeResultIsUniversal (ct : ChaseTree obs kb) : ∀ (m : FactSet sig), m.modelsKb kb -> ∃ (fs : FactSet sig) (h : GroundTermMapping sig), fs ∈ ct.result ∧ h.isHomomorphism fs m := by
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
          exists i
          rw [inductive_homomorphism_path_extends_prev]
          rw [← ct.tree.getElem_children_eq_get_tree _ i']
          simp only [← h.right]
          simp
          constructor
          . rw [List.enum_with_lt_getElem_snd_eq_getElem]
          . rw [List.enum_with_lt_getElem_fst_eq_index]
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

  let global_h : GroundTermMapping sig := fun t =>
    let dec := Classical.propDecidable (∃ f, f ∈ result ∧ t ∈ f.terms.toSet)
    match dec with
      | Decidable.isTrue p =>
        let hfl := (Classical.choose_spec p).left
        let i := Classical.choose hfl
        let target_h := (inductive_homomorphism_shortcut i).val.2
        target_h t
      | Decidable.isFalse _ => t

  have : ∀ i, (branch.branch.infinite_list i).is_none_or (fun chase_node => ∀ f, f ∈ chase_node.fact.val -> global_h.applyFact f = (inductive_homomorphism_shortcut i).val.snd.applyFact f) := by
    intro i
    cases eq : branch.branch.infinite_list i with
    | none => simp [Option.is_none_or]
    | some node =>
      simp [Option.is_none_or]
      intro f f_in_node
      unfold GroundTermMapping.applyFact
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
      unfold GroundTermMapping.applyFactSet at hf
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
            have : (inductive_homomorphism_shortcut n).val.snd.applyFactSet node.fact ⊆ m := property.right
            unfold Set.subset at this
            apply this
            simp [Set.element, GroundTermMapping.applyFactSet]
            exists e

