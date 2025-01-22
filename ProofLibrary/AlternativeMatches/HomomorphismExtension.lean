import ProofLibrary.AlternativeMatches.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace ChaseBranch

  noncomputable def extend_hom_to_next_step_internal (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.fact cb.result) (node' : ChaseNode obs kb.rules) (node_k_succ : cb.branch.infinite_list (k + 1) = node') :
      { h' : GroundTermMapping sig // (∀ t, t ∈ node.fact.val.terms -> h' t = h t) ∧ h'.isHomomorphism node'.fact cb.result } :=
    have : exists_trigger_opt_fs obs kb.rules node (cb.branch.infinite_list (k + 1)) := by
      have trg_ex := cb.triggers_exist k
      rw [node_k] at trg_ex
      simp only [Option.is_none_or] at trg_ex
      cases trg_ex with
      | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [node_k_succ] at trg_ex; simp at trg_ex
      | inl trg_ex => exact trg_ex
    let trg := Classical.choose this
    have ⟨trg_active, trg_res⟩ := Classical.choose_spec this
    let disj_index := Classical.choose trg_res
    have trg_res := Classical.choose_spec trg_res

    let disj_index' : Fin trg.val.rule.head.length := ⟨disj_index.val, by rw [PreTrigger.head_length_eq_mapped_head_length]; have isLt := disj_index.isLt; unfold PreTrigger.result at isLt; simp only [List.length_map] at isLt; exact isLt⟩

    let trg' : PreTrigger sig := ⟨trg.val.rule, h ∘ trg.val.subs⟩
    have trg'_loaded : trg'.loaded cb.result := by
      apply Set.subsetTransitive _ (h.applyFactSet node.fact) _
      constructor
      . apply PreTrigger.term_mapping_preserves_loadedness
        . exact hom.left
        . exact trg_active.left
      . apply hom.right
    have trg'_satisfied : trg'.satisfied_for_disj cb.result disj_index' := by
      unfold PreTrigger.satisfied_for_disj
      have modelsRule : cb.result.modelsRule trg'.rule := by
        have modelsKb := chaseBranchResultModelsKb cb
        exact modelsKb.right trg'.rule trg.property
      specialize modelsRule trg'.subs trg'_loaded
      rcases modelsRule with ⟨i, s', s'_frontier, s'_contains⟩
      exists s'
      constructor
      . exact s'_frontier
      . -- kb.isDeterministic is required here
        have : i = disj_index' := by
          have isLt := i.isLt
          have := det trg'.rule trg.property
          unfold Rule.isDeterministic at this
          simp [this] at isLt
          have isLt' := disj_index'.isLt
          have := det trg.val.rule trg.property
          unfold Rule.isDeterministic at this
          simp [this] at isLt'
          rw [Fin.ext_iff]
          rw [isLt, isLt']
        rw [this] at s'_contains
        exact s'_contains

    let subs := Classical.choose trg'_satisfied
    have ⟨subs_frontier, subs_contained⟩ := Classical.choose_spec trg'_satisfied

    let h' : GroundTermMapping sig := fun t =>
      match ((trg.val.rule.head.get disj_index').vars.find? (fun v => (¬ v ∈ trg.val.rule.frontier) ∧ (trg.val.apply_to_var_or_const disj_index.val (VarOrConst.var v) = t))) with
      | none => h t
      | some v => subs v

    have h'_is_id_on_const : h'.isIdOnConstants := by
      intro voc
      cases voc with
      | inner _ _ => simp
      | leaf c =>
        simp
        unfold h'
        rw [List.find?_eq_none.mpr]
        . simp; exact hom.left (GroundTerm.const c)
        . simp
          intro v _ not_frontier contra
          simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, not_frontier] at contra

    have h'_is_subs_on_head_vars : ∀ v, v ∈ (trg.val.rule.head.get disj_index').vars -> (h' (trg.val.apply_to_var_or_const disj_index.val (VarOrConst.var v))) = subs v := by
      intro v v_mem
      cases Decidable.em (v ∈ trg.val.rule.frontier) with
      | inl v_frontier =>
        simp only [subs]
        rw [subs_frontier _ v_frontier]
        simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, v_frontier]
        unfold h'
        rw [List.find?_eq_none.mpr]
        simp
        intro u u_mem u_frontier contra
        have u_result_not_in_frontier_image := trg.val.result_term_not_in_frontier_image_of_var_not_in_frontier disj_index u u_frontier
        apply u_result_not_in_frontier_image
        rw [contra]
        simp
        exists v
      | inr v_frontier =>
        unfold h'
        rw [List.find?_eq_some_iff_append.mpr]
        simp
        constructor
        . exact v_frontier
        . rw [List.mem_iff_append_and_not_in_first] at v_mem
          rcases v_mem with ⟨as, bs, v_mem, v_not_in_as⟩
          exists as
          constructor
          . exists bs
          . intro u u_mem
            apply Or.inr
            intro contra
            have skolem_eq := trg.val.subs_application_is_injective_for_freshly_introduced_terms disj_index' v_frontier u (Eq.symm contra)
            unfold PreTrigger.skolemize_var_or_const at skolem_eq
            have terms_eq := VarOrConst.skolemize_injective _ _ _ _ _ skolem_eq
            injection terms_eq with terms_eq
            rw [terms_eq] at v_not_in_as
            contradiction

    have h'_is_h_on_terms_in_node : ∀ t, t ∈ node.fact.val.terms -> h' t = h t := by
      intro t t_mem
      unfold h'
      rw [List.find?_eq_none.mpr]
      simp
      intro v v_head v_not_frontier contra
      have : trg.val.result.get disj_index ⊆ node.fact := by
        -- kb.isDeterministic is used here but likely we could show a similar theorem used here also for branches
        apply funcTermForExisVarInChaseTreeMeansTriggerResultOccurs (cb.intoTree det) trg disj_index v node (List.repeat 0 k)
        constructor
        . unfold ChaseBranch.intoTree
          unfold FiniteDegreeTree.get
          unfold PossiblyInfiniteTree.get
          simp
          rw [List.length_repeat, node_k]
          simp
          have := List.all_eq_val_repeat 0 k
          simp at this
          exact this
        constructor
        . exact v_not_frontier
        . unfold FactSet.terms at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          exists f
          constructor
          . exact f_mem
          . rw [contra]; exact t_mem
      have trg_obs := obs.contains_trg_result_implies_cond disj_index this
      have not_obs := trg_active.right
      contradiction

    ⟨h', by
      constructor
      . exact h'_is_h_on_terms_in_node
      . rw [← trg_res] at node_k_succ
        injection node_k_succ with node_k_succ
        rw [← node_k_succ]
        constructor
        . exact h'_is_id_on_const
        . unfold GroundTermMapping.applyFactSet
          intro f f_mem
          rcases f_mem with ⟨f, f_mem, f_eq⟩
          cases f_mem with
          | inl f_mem => apply hom.right; exists f; constructor; exact f_mem; rw [← f_eq]; unfold GroundTermMapping.applyFact; simp; intro t t_mem; rw [h'_is_h_on_terms_in_node]; unfold FactSet.terms; exists f
          | inr f_mem =>
            rw [← f_eq]
            apply subs_contained
            have : (subs.apply_function_free_conj (trg'.rule.head.get disj_index')).toSet = h'.applyFactSet (trg.val.result.get disj_index) := by
              apply funext
              intro f
              have inIffInToSet := (subs.apply_function_free_conj (trg'.rule.head.get disj_index')).inIffInToSet f
              simp only [Set.element] at inIffInToSet
              rw [← inIffInToSet]
              unfold GroundTermMapping.applyFactSet
              unfold GroundSubstitution.apply_function_free_conj
              unfold PreTrigger.result
              unfold PreTrigger.mapped_head
              simp
              constructor
              . intro pre
                rcases pre with ⟨a, a_mem, a_eq⟩
                exists trg.val.apply_to_function_free_atom disj_index.val a
                constructor
                . rw [← List.inIffInToSet]; simp; exists a
                . rw [← a_eq]
                  simp [PreTrigger.apply_to_function_free_atom, GroundTermMapping.applyFact, GroundSubstitution.apply_function_free_atom]
                  intro voc voc_mem
                  cases voc with
                  | const c => simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, PreTrigger.apply_to_skolemized_term, GroundSubstitution.apply_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize]; exact h'_is_id_on_const (GroundTerm.const c)
                  | var v =>
                    rw [h'_is_subs_on_head_vars]
                    simp [GroundSubstitution.apply_var_or_const]
                    unfold FunctionFreeConjunction.vars
                    simp
                    exists a.variables
                    constructor
                    . exists a
                    . unfold FunctionFreeAtom.variables
                      apply VarOrConst.mem_filterVars_of_var
                      exact voc_mem
              . intro pre
                rcases pre with ⟨b, b_mem, b_eq⟩
                rw [← List.inIffInToSet] at b_mem
                simp at b_mem
                rcases b_mem with ⟨a, a_mem, a_eq⟩
                exists a
                constructor
                . exact a_mem
                . rw [← b_eq, ← a_eq]
                  simp [PreTrigger.apply_to_function_free_atom, GroundTermMapping.applyFact, GroundSubstitution.apply_function_free_atom]
                  intro voc voc_mem
                  cases voc with
                  | const c => simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, PreTrigger.apply_to_skolemized_term, GroundSubstitution.apply_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize]; rw [h'_is_id_on_const (GroundTerm.const c)]
                  | var v =>
                    rw [h'_is_subs_on_head_vars]
                    simp [GroundSubstitution.apply_var_or_const]
                    unfold FunctionFreeConjunction.vars
                    simp
                    exists a.variables
                    constructor
                    . exists a
                    . unfold FunctionFreeAtom.variables
                      apply VarOrConst.mem_filterVars_of_var
                      exact voc_mem
            rw [this]
            exists f
    ⟩

  noncomputable def extend_hom_to_next_step (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.fact cb.result) :
      GroundTermMapping sig :=
    match eq : cb.branch.infinite_list (k + 1) with
    | .none => h
    | .some node' =>
      (extend_hom_to_next_step_internal cb det k node node_k h hom node' eq).val

  theorem extend_hom_to_next_step_eq (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.fact cb.result) :
      extend_hom_to_next_step cb det k node node_k h hom = match eq : cb.branch.infinite_list (k + 1) with
      | .none => h
      | .some node' => (extend_hom_to_next_step_internal cb det k node node_k h hom node' eq).val := by
    unfold extend_hom_to_next_step
    simp

  theorem extended_hom_same_on_next_extensions (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.fact cb.result) : ∀ t, t ∈ node.fact.val.terms -> extend_hom_to_next_step cb det k node node_k h hom t = h t := by
    intro t t_mem
    rw [extend_hom_to_next_step_eq]
    split
    . rfl
    case h_2 node' eq =>
      let result := extend_hom_to_next_step_internal cb det k node node_k h hom node' eq
      rw [result.property.left]
      exact t_mem

  theorem extended_hom_isHomomorphism_on_next_extensions (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.fact cb.result) : (cb.branch.infinite_list (k + 1)).is_none_or (fun node' => (extend_hom_to_next_step cb det k node node_k h hom).isHomomorphism node'.fact cb.result) := by
    rw [extend_hom_to_next_step_eq]
    split
    case h_1 eq => simp [eq, Option.is_none_or]
    case h_2 node' eq =>
      simp [eq, Option.is_none_or]
      let result := extend_hom_to_next_step_internal cb det k node node_k h hom node' eq
      exact result.property.right

  noncomputable def extend_hom_to_any_following_step (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.fact cb.result) : (step_width : Nat) ->
    { h' : GroundTermMapping sig // (cb.branch.infinite_list (k+step_width)).is_none_or (fun node' => h'.isHomomorphism node'.fact cb.result) }
  | .zero => ⟨h, by simp [node_k, Option.is_none_or]; exact hom⟩
  | .succ step_width =>
    let prev_hom := extend_hom_to_any_following_step cb det k node node_k h hom step_width

    match eq : cb.branch.infinite_list (k + step_width) with
    | .none =>
      ⟨prev_hom.val, by
        cases eq2 : cb.branch.infinite_list (k + (step_width + 1)) with
        | none => simp [eq2, Option.is_none_or]
        | some _ =>
          have no_holes := cb.branch.no_holes (k + (step_width + 1))
          rw [eq2] at no_holes
          simp at no_holes
          specialize no_holes ⟨k + step_width, by simp⟩
          rw [eq] at no_holes
          simp at no_holes
      ⟩
    | .some node' =>
      ⟨extend_hom_to_next_step cb det (k + step_width) node' eq prev_hom.val (by
        have property := prev_hom.property
        simp only [eq, Option.is_none_or] at property
        exact property
      ), by apply extended_hom_isHomomorphism_on_next_extensions⟩

  theorem extended_hom_same_on_all_following_extensions (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.fact cb.result) : ∀ (i j : Nat), (cb.branch.infinite_list (k + i)).is_none_or (fun node' => ∀ t, t ∈ node'.fact.val.terms -> (extend_hom_to_any_following_step cb det k node node_k h hom (i + j)).val t = (extend_hom_to_any_following_step cb det k node node_k h hom i).val t) := by
    intro i j
    simp [Option.is_none_or]
    split
    . simp
    case h_2 _ _ node' eq =>
      simp only [Option.is_none_or]
      induction j with
      | zero => intros; rfl
      | succ j ih =>
        intro t t_mem
        specialize ih t t_mem
        conv => left; unfold extend_hom_to_any_following_step
        simp
        split
        . simp; exact ih
        case h_2 _ eq2 =>
          simp
          rw [extended_hom_same_on_next_extensions]
          . exact ih
          . have all_following := chaseBranchSetIsSubsetOfAllFollowing cb (k + i) j
            rw [← Nat.add_assoc] at eq2
            rw [eq, eq2] at all_following
            simp [Option.is_none_or] at all_following
            unfold FactSet.terms
            rcases t_mem with ⟨f, f_mem, t_mem⟩
            exists f
            constructor
            . apply all_following; exact f_mem
            . exact t_mem

  theorem hom_for_step_extendable_result (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (h : GroundTermMapping sig) :
      (cb.branch.infinite_list k).is_none_or (fun node => h.isHomomorphism node.fact cb.result ->
      ∃ (h' : GroundTermMapping sig), (∀ t, t ∈ node.fact.val.terms -> h' t = h t) ∧ h'.isHomomorphism cb.result cb.result) := by
    cases eq : cb.branch.infinite_list k with
    | none => simp [Option.is_none_or]
    | some node =>
      rw [Option.is_none_or]
      intro hom

      let target_h (i : Nat) := extend_hom_to_any_following_step cb det k node eq h hom i

      let global_h : GroundTermMapping sig := fun t =>
        let dec := Classical.propDecidable (∃ f, f ∈ cb.result ∧ t ∈ f.terms)
        match dec with
          | Decidable.isTrue p =>
            let hfl := (Classical.choose_spec p).left
            let i := Classical.choose hfl
            if i ≤ k then h t else (target_h (i-k)).val t
          | Decidable.isFalse _ => t

      have id_on_const : ∀ (c : sig.C), global_h (GroundTerm.const c) = (GroundTerm.const c) := by
        intro c
        simp [global_h]
        split
        case h_1 _ ex_f _ =>
          let hfl := (Classical.choose_spec ex_f).left
          let i := Classical.choose hfl
          split
          . exact hom.left (GroundTerm.const c)
          case isFalse lt =>
            simp at lt
            have i_spec := Classical.choose_spec hfl
            cases eq2 : cb.branch.infinite_list i with
            | none => rw [eq2] at i_spec; simp [Option.is_some_and] at i_spec
            | some node' =>
              have target_hom := (target_h (i-k)).property
              simp only [Nat.add_sub_of_le (Nat.le_of_lt lt), eq2, Option.is_none_or] at target_hom
              exact target_hom.left (GroundTerm.const c)
        . rfl

      have apply_uniform_in_step : ∀ i, (cb.branch.infinite_list i).is_none_or (fun node => ∀ f, f ∈ node.fact.val -> global_h.applyFact f = (target_h (i - k)).val.applyFact f) := by
        intro i
        cases eq2 : cb.branch.infinite_list i with
        | none => simp [Option.is_none_or]
        | some node' =>
          simp [Option.is_none_or]
          intro f f_mem
          unfold GroundTermMapping.applyFact
          simp [global_h]
          intro t t_mem
          split
          case h_2 _ n_ex _ =>
            apply False.elim
            apply n_ex
            exists f
            constructor
            . have subset_result := chaseBranchSetIsSubsetOfResult cb i
              rw [eq2] at subset_result; simp [Option.is_none_or] at subset_result
              apply subset_result
              exact f_mem
            . exact t_mem
          case h_1 _ ex _ =>
            let j := Classical.choose (Classical.choose_spec ex).left
            have j_spec := Classical.choose_spec (Classical.choose_spec ex).left
            have spec := Classical.choose_spec ex
            cases eq3 : cb.branch.infinite_list j with
            | none => rw [eq3] at j_spec; simp [Option.is_some_and] at j_spec
            | some node'' =>
              rw [eq3] at j_spec; simp [Option.is_some_and] at j_spec
              split
              case isTrue le =>
                unfold target_h
                have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom 0 (i - k)
                simp [eq, Option.is_none_or] at target_h_same
                specialize target_h_same t
                have : 0 + (i - k) = i - k := by simp
                rw [this] at target_h_same
                rw [target_h_same]
                . unfold extend_hom_to_any_following_step
                  simp
                . have all_following := chaseBranchSetIsSubsetOfAllFollowing cb j (k - j)
                  rw [eq3] at all_following; simp at all_following
                  rw [Nat.add_sub_of_le le] at all_following
                  rw [eq] at all_following; simp [Option.is_none_or] at all_following
                  unfold FactSet.terms
                  exists (Classical.choose ex)
                  constructor
                  . apply all_following; exact j_spec
                  . exact spec.right
              case isFalse gt =>
                simp at gt
                cases Decidable.em (i ≤ j) with
                | inl le2 =>
                  cases Decidable.em (i ≤ k) with
                  | inl le3 =>
                    have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom 0 (j - k)
                    simp [eq, Option.is_none_or] at target_h_same
                    specialize target_h_same t
                    have : 0 + (j - k) = j - k := by simp
                    rw [this] at target_h_same
                    rw [target_h_same]
                    . rw [Nat.sub_eq_zero_of_le le3]
                    . have all_following := chaseBranchSetIsSubsetOfAllFollowing cb i (k - i)
                      rw [eq2] at all_following; simp at all_following
                      rw [Nat.add_sub_of_le le3] at all_following
                      rw [eq] at all_following; simp [Option.is_none_or] at all_following
                      unfold FactSet.terms
                      exists f
                      constructor
                      . apply all_following; exact f_mem
                      . exact t_mem
                  | inr gt3 =>
                    simp at gt3
                    have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom (i - k) (j - i)
                    simp only [Nat.add_sub_of_le (Nat.le_of_lt gt3), eq2, Option.is_none_or] at target_h_same
                    specialize target_h_same t
                    have : (i - k + (j - i)) = j - k := by omega
                    rw [this] at target_h_same
                    rw [target_h_same]
                    exists f
                | inr gt2 =>
                  simp at gt2
                  have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom (j - k) (i - j)
                  simp only [Nat.add_sub_of_le (Nat.le_of_lt gt), eq3, Option.is_none_or] at target_h_same
                  specialize target_h_same t
                  have : (j - k + (i - j)) = i - k := by omega
                  rw [this] at target_h_same
                  rw [target_h_same]
                  exists Classical.choose ex
                  constructor
                  . exact j_spec
                  . exact spec.right

      exists global_h
      constructor
      . intro t t_mem
        unfold global_h
        have ex_f : ∃ f, f ∈ cb.result ∧ t ∈ f.terms := by
          unfold FactSet.terms at t_mem
          rcases t_mem with ⟨f, f_mem, f_eq⟩
          exists f
          constructor
          . have sub_result := chaseBranchSetIsSubsetOfResult cb k
            simp [eq, Option.is_none_or] at sub_result
            apply sub_result
            exact f_mem
          . exact f_eq
        simp
        split
        . split
          . rfl
          case isFalse lt =>
            let hfl := (Classical.choose_spec ex_f).left
            let i := Classical.choose hfl
            have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom 0 (i - k)
            simp [eq, Option.is_none_or] at target_h_same
            specialize target_h_same t t_mem
            have : 0 + (i - k) = i - k := by simp
            unfold target_h
            rw [← this, target_h_same]
            unfold extend_hom_to_any_following_step
            simp
        . contradiction
      . constructor
        . intro t
          cases t with
          | inner _ _ => simp
          | leaf c =>
            simp
            exact id_on_const c
        . intro f f_mem
          unfold GroundTermMapping.applyFactSet at f_mem
          rcases f_mem with ⟨f_arg, f_arg_mem, f_eq⟩
          unfold ChaseBranch.result at f_arg_mem
          rcases f_arg_mem with ⟨n, f_arg_mem⟩
          cases eq2 : cb.branch.infinite_list n with
          | none => simp [eq2, Option.is_some_and] at f_arg_mem
          | some node' =>
            simp [eq2, Option.is_some_and] at f_arg_mem
            have := apply_uniform_in_step n
            rw [eq2, Option.is_none_or] at this
            specialize this _ f_arg_mem
            rw [this] at f_eq
            rw [← f_eq]
            have target_h_property := (target_h (n-k)).property
            cases Decidable.em (n ≤ k) with
            | inl le =>
              simp [Nat.sub_eq_zero_of_le le] at target_h_property
              rw [eq, Option.is_none_or] at target_h_property
              apply target_h_property.right
              apply GroundTermMapping.applyPreservesElement
              have all_following := chaseBranchSetIsSubsetOfAllFollowing cb n (k - n)
              rw [eq2] at all_following
              simp at all_following
              rw [Nat.add_sub_of_le le] at all_following
              rw [eq] at all_following
              simp [Option.is_none_or] at all_following
              apply all_following
              exact f_arg_mem
            | inr gt =>
              simp at gt
              simp only [Nat.add_sub_of_le (Nat.le_of_lt gt), eq2, Option.is_none_or] at target_h_property
              apply target_h_property.right
              apply GroundTermMapping.applyPreservesElement
              exact f_arg_mem

end ChaseBranch

