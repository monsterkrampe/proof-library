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

  def apply_pre_ground_term (g : ConstantMapping sig) (t : PreGroundTerm sig) : PreGroundTerm sig := t.mapLeaves (fun c => (g c).val)

  mutual

    theorem apply_pre_ground_term_arity_ok (g : ConstantMapping sig) (t : FiniteTree (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok t) : PreGroundTerm.arity_ok (g.apply_pre_ground_term t) := by
      cases t with
      | leaf c =>
        unfold apply_pre_ground_term
        unfold FiniteTree.mapLeaves
        exact (g c).property
      | inner f ts =>
        unfold PreGroundTerm.arity_ok at arity_ok
        rw [Bool.and_eq_true] at arity_ok
        unfold apply_pre_ground_term
        unfold FiniteTree.mapLeaves
        unfold PreGroundTerm.arity_ok
        rw [Bool.and_eq_true]
        constructor
        . rw [FiniteTree.length_mapLeavesList]
          exact arity_ok.left
        . apply apply_pre_ground_term_list_arity_ok
          exact arity_ok.right

    theorem apply_pre_ground_term_list_arity_ok (g : ConstantMapping sig) (ts : FiniteTreeList (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok_list ts) : PreGroundTerm.arity_ok_list (FiniteTree.mapLeavesList (fun c => (g c).val) ts) := by
      cases ts with
      | nil => simp [FiniteTree.mapLeavesList, PreGroundTerm.arity_ok_list]
      | cons hd tl =>
        unfold PreGroundTerm.arity_ok_list at arity_ok
        rw [Bool.and_eq_true] at arity_ok
        unfold FiniteTree.mapLeavesList
        unfold PreGroundTerm.arity_ok_list
        rw [Bool.and_eq_true]
        constructor
        . apply apply_pre_ground_term_arity_ok; exact arity_ok.left
        . apply apply_pre_ground_term_list_arity_ok; exact arity_ok.right

  end

  def apply_ground_term (g : ConstantMapping sig) (t : GroundTerm sig) : GroundTerm sig := ⟨g.apply_pre_ground_term t.val, g.apply_pre_ground_term_arity_ok t.val t.property⟩

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
      simp only [apply_pre_ground_term, FiniteTree.mapLeaves]
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
      unfold ConstantMapping.apply_pre_ground_term
      unfold FiniteTree.mapLeaves
      unfold GroundTerm.const
      apply Subtype.eq
      simp only
      rcases h with ⟨c, g_eq, mem_a_eq⟩
      rw [g_eq]
      rw [mem_a_eq d]
      . simp [GroundTerm.const]
      . exact voc_mem

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
    unfold List.flatMap
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

section ArgumentsForImages

  namespace StrictConstantMapping

    variable {sig : Signature} [DecidableEq sig.C]

    def arguments_for_constant (g : StrictConstantMapping sig) (possible_constants : List sig.C) (c : sig.C) : List sig.C :=
      possible_constants.filter (fun d => g d = c)

    theorem apply_to_arguments_yields_original_constant (g : StrictConstantMapping sig) (possible_constants : List sig.C) (c : sig.C) :
        ∀ arg, arg ∈ g.arguments_for_constant possible_constants c ↔ (arg ∈ possible_constants ∧ g arg = c) := by
      intro arg
      unfold arguments_for_constant
      simp

    variable [DecidableEq sig.V]

    mutual
      def arguments_for_pre_term (g : StrictConstantMapping sig) (possible_constants : List sig.C) : FiniteTree (SkolemFS sig) sig.C -> List (PreGroundTerm sig)
      | .leaf c => (g.arguments_for_constant possible_constants c).map (fun arg => .leaf arg)
      | .inner func ts =>
        (g.arguments_for_pre_term_list possible_constants ts).map (fun ts =>
          .inner func (FiniteTreeList.fromList ts)
        )
      def arguments_for_pre_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) : FiniteTreeList (SkolemFS sig) sig.C -> List (List (PreGroundTerm sig))
      | .nil => [[]]
      | .cons hd tl =>
        let arguments_tail := g.arguments_for_pre_term_list possible_constants tl
        (g.arguments_for_pre_term possible_constants hd).flatMap (fun arg =>
          arguments_tail.map (fun arg_list =>
            arg :: arg_list
          )
        )
    end

    mutual
      theorem apply_to_arguments_yields_original_pre_term (g : StrictConstantMapping sig) (possible_constants : List sig.C) (term : FiniteTree (SkolemFS sig) sig.C) :
          ∀ arg, arg ∈ g.arguments_for_pre_term possible_constants term ↔ ((∀ c, c ∈ arg.leaves -> c ∈ possible_constants) ∧ g.toConstantMapping.apply_pre_ground_term arg = term) := by
        intro arg
        constructor
        . intro h
          cases term with
          | leaf c =>
            unfold arguments_for_pre_term at h
            rw [List.mem_map] at h
            rcases h with ⟨a, a_mem, arg_eq⟩
            rw [apply_to_arguments_yields_original_constant] at a_mem
            constructor
            . intro d d_mem
              rw [← arg_eq] at d_mem
              unfold FiniteTree.leaves at d_mem
              simp at d_mem
              rw [d_mem]
              exact a_mem.left
            . rw [← arg_eq]
              unfold ConstantMapping.apply_pre_ground_term
              unfold FiniteTree.mapLeaves
              unfold toConstantMapping
              rw [a_mem.right]
              rfl
          | inner func ts =>
            unfold arguments_for_pre_term at h
            rw [List.mem_map] at h
            rcases h with ⟨a, a_mem, arg_eq⟩
            rw [apply_to_arguments_yields_original_pre_term_list] at a_mem
            constructor
            . intro d d_mem
              rw [← arg_eq] at d_mem
              unfold FiniteTree.leaves at d_mem
              apply a_mem.left
              exact d_mem
            . rw [← arg_eq]
              unfold ConstantMapping.apply_pre_ground_term
              unfold FiniteTree.mapLeaves
              rw [a_mem.right]
        . intro h
          cases term with
          | leaf c =>
            unfold arguments_for_pre_term
            rw [List.mem_map]
            cases arg with
            | leaf d =>
              exists d
              rw [apply_to_arguments_yields_original_constant]
              constructor
              . constructor
                . apply h.left
                  unfold FiniteTree.leaves
                  simp
                . have r := h.right
                  unfold ConstantMapping.apply_pre_ground_term at r
                  unfold toConstantMapping at r
                  unfold FiniteTree.mapLeaves at r
                  injection r with r
              . rfl
            | inner func args =>
              have contra := h.right
              simp [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves] at contra
          | inner func ts =>
            unfold arguments_for_pre_term
            rw [List.mem_map]
            cases arg with
            | leaf d =>
              have contra := h.right
              simp [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, toConstantMapping, GroundTerm.const] at contra
            | inner func' args =>
              exists args
              rw [apply_to_arguments_yields_original_pre_term_list]
              constructor
              . constructor
                . intro d d_mem
                  apply h.left
                  unfold FiniteTree.leaves
                  rw [FiniteTreeList.toListFromListIsId] at d_mem
                  exact d_mem
                . have r := h.right
                  unfold ConstantMapping.apply_pre_ground_term at r
                  unfold FiniteTree.mapLeaves at r
                  injection r with func_eq args_eq
                  rw [FiniteTreeList.toListFromListIsId]
                  exact args_eq
              . have r := h.right
                unfold ConstantMapping.apply_pre_ground_term at r
                unfold FiniteTree.mapLeaves at r
                injection r with func_eq args_eq
                rw [FiniteTreeList.toListFromListIsId]
                rw [func_eq]

      theorem apply_to_arguments_yields_original_pre_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : FiniteTreeList (SkolemFS sig) sig.C) :
          ∀ args, args ∈ g.arguments_for_pre_term_list possible_constants ts ↔ ((∀ c, c ∈ (FiniteTree.leavesList (FiniteTreeList.fromList args)) -> c ∈ possible_constants) ∧ ((FiniteTree.mapLeavesList (fun leaf => g.toConstantMapping leaf) (FiniteTreeList.fromList args)) = ts)) := by
        intro args
        constructor
        . intro h
          cases ts with
          | nil =>
            simp [arguments_for_pre_term_list] at h
            rw [h]
            simp [FiniteTreeList.fromList, FiniteTree.mapLeavesList, FiniteTree.leavesList]
          | cons hd tl =>
            unfold arguments_for_pre_term_list at h
            rw [List.mem_flatMap] at h
            rcases h with ⟨hd_arg, hd_arg_mem, args_mem⟩
            rw [List.mem_map] at args_mem
            rcases args_mem with ⟨tl_args, tl_args_mem, args_eq⟩
            rw [apply_to_arguments_yields_original_pre_term] at hd_arg_mem
            rw [apply_to_arguments_yields_original_pre_term_list] at tl_args_mem
            rw [← args_eq]
            constructor
            . intro d d_mem
              unfold FiniteTreeList.fromList at d_mem
              unfold FiniteTree.leavesList at d_mem
              rw [List.mem_append] at d_mem
              cases d_mem with
              | inl d_mem => apply hd_arg_mem.left; exact d_mem
              | inr d_mem => apply tl_args_mem.left; exact d_mem
            . unfold FiniteTreeList.fromList
              unfold FiniteTree.mapLeavesList
              unfold ConstantMapping.apply_pre_ground_term at hd_arg_mem
              rw [hd_arg_mem.right]
              rw [tl_args_mem.right]
        . intro h
          cases ts with
          | nil =>
            cases args with
            | nil => simp [arguments_for_pre_term_list]
            | cons hd_arg tl_arg =>
              have r := h.right
              simp [FiniteTreeList.fromList, FiniteTree.mapLeavesList] at r
          | cons hd tl =>
            cases args with
            | nil =>
              have r := h.right
              simp [FiniteTreeList.fromList, FiniteTree.mapLeavesList] at r
            | cons hd_arg tl_arg =>
              unfold arguments_for_pre_term_list
              unfold FiniteTreeList.fromList at h
              unfold FiniteTree.leavesList at h
              unfold FiniteTree.mapLeavesList at h
              rw [List.mem_flatMap]
              exists hd_arg
              constructor
              . rw [apply_to_arguments_yields_original_pre_term]
                constructor
                . intro d d_mem
                  apply h.left
                  rw [List.mem_append]
                  apply Or.inl
                  exact d_mem
                . injection h.right
              . rw [List.mem_map]
                exists tl_arg
                simp only [and_true]
                rw [apply_to_arguments_yields_original_pre_term_list]
                constructor
                . intro d d_mem
                  apply h.left
                  rw [List.mem_append]
                  apply Or.inr
                  exact d_mem
                . injection h.right
    end

    theorem arguments_for_pre_term_list_length_preserved (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : FiniteTreeList (SkolemFS sig) sig.C) :
        ∀ res, res ∈ (g.arguments_for_pre_term_list possible_constants ts) -> res.length = ts.toList.length := by
      cases ts with
      | nil => simp [arguments_for_pre_term_list, FiniteTreeList.toList]
      | cons hd tl =>
        intro res res_mem
        unfold arguments_for_pre_term_list at res_mem
        rw [List.mem_flatMap] at res_mem
        rcases res_mem with ⟨arg, arg_for_hd, res_mem⟩
        rw [List.mem_map] at res_mem
        rcases res_mem with ⟨args, args_for_tl, res_mem⟩
        rw [← res_mem]
        unfold FiniteTreeList.toList
        rw [List.length_cons]
        rw [List.length_cons]
        rw [Nat.add_right_cancel_iff]
        exact g.arguments_for_pre_term_list_length_preserved possible_constants tl args args_for_tl

    mutual

      theorem arguments_for_pre_term_arity_ok (g : StrictConstantMapping sig) (possible_constants : List sig.C) (t : FiniteTree (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok t) : ∀ t', t' ∈ (g.arguments_for_pre_term possible_constants t) -> PreGroundTerm.arity_ok t' := by
        intro t' t'_mem
        unfold arguments_for_pre_term at t'_mem
        cases t with
        | leaf c =>
          rw [List.mem_map] at t'_mem
          rcases t'_mem with ⟨d, d_mem, t'_eq⟩
          rw [← t'_eq]
          simp [PreGroundTerm.arity_ok]
        | inner f ts =>
          unfold PreGroundTerm.arity_ok at arity_ok
          rw [Bool.and_eq_true] at arity_ok
          rw [List.mem_map] at t'_mem
          rcases t'_mem with ⟨ts', ts'_mem, t'_eq⟩
          rw [← t'_eq]
          simp only [PreGroundTerm.arity_ok]
          rw [Bool.and_eq_true]
          constructor
          . rw [FiniteTreeList.fromListToListIsId]
            rw [g.arguments_for_pre_term_list_length_preserved possible_constants ts ts' ts'_mem]
            exact arity_ok.left
          . apply g.arguments_for_pre_term_list_arity_ok possible_constants ts _ ts' ts'_mem
            exact arity_ok.right

      theorem arguments_for_pre_term_list_arity_ok (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : FiniteTreeList (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok_list ts) : ∀ ts', ts' ∈ (g.arguments_for_pre_term_list possible_constants ts) -> PreGroundTerm.arity_ok_list (FiniteTreeList.fromList ts') := by
        intro ts' ts'_mem
        cases ts with
        | nil => simp [arguments_for_pre_term_list] at ts'_mem; rw [ts'_mem]; simp [PreGroundTerm.arity_ok_list]
        | cons hd tl =>
          unfold PreGroundTerm.arity_ok_list at arity_ok
          rw [Bool.and_eq_true] at arity_ok
          unfold arguments_for_pre_term_list at ts'_mem
          simp only [List.mem_flatMap, List.mem_map] at ts'_mem
          rcases ts'_mem with ⟨arg_hd, arg_hd_mem, arg_tl, arg_tl_mem, ts'_eq⟩
          rw [← ts'_eq]
          unfold FiniteTreeList.fromList
          unfold PreGroundTerm.arity_ok_list
          rw [Bool.and_eq_true]
          constructor
          . apply g.arguments_for_pre_term_arity_ok possible_constants hd _ _ arg_hd_mem
            exact arity_ok.left
          . apply g.arguments_for_pre_term_list_arity_ok possible_constants tl _ _ arg_tl_mem
            exact arity_ok.right

    end

    /- def arguments_for_term (g : StrictConstantMapping sig) (possible_constants : List sig.C) (t : GroundTerm sig) : List (GroundTerm sig) := -/
    /-   (g.arguments_for_pre_term possible_constants t.val).attach.map (fun ⟨t', mem⟩ => -/
    /-     ⟨t', g.arguments_for_pre_term_arity_ok possible_constants t.val t.property t' mem⟩ -/
    /-   ) -/

    def arguments_for_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : List (GroundTerm sig)) : List (List (GroundTerm sig)) :=
      (g.arguments_for_pre_term_list possible_constants (FiniteTreeList.fromList ts.unattach)).attach.map (fun ⟨ts', mem⟩ =>
        have arity_ok := g.arguments_for_pre_term_list_arity_ok possible_constants (FiniteTreeList.fromList ts.unattach) (by
          rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]
          intro t t_mem
          rw [FiniteTreeList.fromListToListIsId] at t_mem
          unfold List.unattach at t_mem
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨t', _, t_eq⟩
          rw [← t_eq]
          exact t'.property
        ) ts' mem

        ts'.attach.map (fun ⟨t, mem⟩ =>
          ⟨t, by
            rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem] at arity_ok
            apply arity_ok
            rw [FiniteTreeList.fromListToListIsId]
            exact mem
          ⟩
        )
      )

    theorem apply_to_arguments_yields_original_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : List (GroundTerm sig)) :
        ∀ args, args ∈ g.arguments_for_term_list possible_constants ts ↔ ((∀ c, c ∈ (FiniteTree.leavesList (FiniteTreeList.fromList args.unattach)) -> c ∈ possible_constants) ∧ (args.map (fun arg => g.toConstantMapping.apply_ground_term arg) = ts)) := by
      intro args

      have := g.apply_to_arguments_yields_original_pre_term_list possible_constants (FiniteTreeList.fromList ts.unattach)

      unfold arguments_for_term_list
      constructor
      . intro h
        simp at h
        rcases h with ⟨args', h, eq⟩
        rw [← List.pmap_eq_map_attach] at eq
        rw [← eq]

        rw [this] at h
        rw [FiniteTree.mapLeavesList_fromList_eq_fromList_map] at h
        rw [← FiniteTreeList.eqIffFromListEq] at h
        constructor
        . intro c c_mem
          unfold List.unattach at c_mem
          rw [List.map_pmap] at c_mem
          simp at c_mem
          apply h.left
          exact c_mem
        . rw [← List.eq_iff_unattach_eq]
          simp only [← h.right]
          unfold ConstantMapping.apply_ground_term
          unfold ConstantMapping.apply_pre_ground_term
          rw [List.map_pmap]
          unfold List.unattach
          rw [List.map_pmap]
          rw [List.pmap_eq_map]
      . intro h
        simp
        exists args.unattach
        exists (by
          rw [this]
          constructor
          . exact h.left
          . rw [← h.right]
            rw [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
            rw [← FiniteTreeList.eqIffFromListEq]
            unfold ConstantMapping.apply_ground_term
            unfold ConstantMapping.apply_pre_ground_term
            unfold List.unattach
            simp
        )
        rw [← List.pmap_eq_map_attach]
        rw [← List.eq_iff_unattach_eq]
        unfold List.unattach
        rw [List.map_pmap]
        rw [List.pmap_eq_map]
        simp

    variable [DecidableEq sig.P]

    def arguments_for_fact (g : StrictConstantMapping sig) (possible_constants : List sig.C) (f : Fact sig) : List (Fact sig) :=
      (g.arguments_for_term_list possible_constants f.terms).attach.map (fun ⟨ts, mem⟩ =>
        {
          predicate := f.predicate
          terms := ts
          arity_ok := by
            unfold arguments_for_term_list at mem
            rw [List.mem_map] at mem
            rcases mem with ⟨ts', ts'_mem, ts_eq⟩
            rw [← ts_eq]
            simp only [List.length_map, List.length_attach]
            rw [g.arguments_for_pre_term_list_length_preserved possible_constants (FiniteTreeList.fromList f.terms.unattach) ts'.val _]
            . rw [FiniteTreeList.fromListToListIsId, List.length_unattach]
              exact f.arity_ok
            . unfold List.attach at ts'_mem
              unfold List.attachWith at ts'_mem
              rw [List.mem_pmap] at ts'_mem
              rcases ts'_mem with ⟨_, ts'_mem, eq⟩
              rw [← eq]
              exact ts'_mem
        }
      )

    theorem apply_to_arguments_yields_original_fact (g : StrictConstantMapping sig) (possible_constants : List sig.C) (f : Fact sig) :
        ∀ arg, arg ∈ g.arguments_for_fact possible_constants f ↔ ((∀ c, c ∈ arg.constants -> c ∈ possible_constants) ∧ g.toConstantMapping.apply_fact arg = f) := by
      intro arg
      unfold arguments_for_fact
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]

      have := g.apply_to_arguments_yields_original_term_list possible_constants f.terms

      constructor
      . intro h
        rcases h with ⟨ts, mem, arg_eq⟩
        rw [← arg_eq]
        unfold ConstantMapping.apply_fact
        rw [Fact.ext_iff]
        simp only [true_and]

        specialize this ts
        rw [this] at mem
        exact mem
      . intro h
        specialize this arg.terms
        exists arg.terms
        exists (by
          apply this.mpr
          constructor
          . exact h.left
          . have r := h.right
            unfold ConstantMapping.apply_fact at r
            rw [Fact.ext_iff] at r
            exact r.right
        )
        have r := h.right
        unfold ConstantMapping.apply_fact at r
        rw [Fact.ext_iff] at r
        apply Fact.ext
        . rw [← r.left]
        . rfl

  end StrictConstantMapping

end ArgumentsForImages


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

  theorem parallelSkolemChase_predicates (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) :
      ∀ n, (kb.parallelSkolemChase det n).predicates ⊆ (kb.rules.predicates ∪ kb.db.toFactSet.val.predicates) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      apply Set.subsetUnionSomethingStillSubset'
      apply Set.subsetOfSelf
    | succ n ih =>
      unfold parallelSkolemChase
      intro p p_mem
      rcases p_mem with ⟨f, f_mem, p_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.result at f_mem
        unfold PreTrigger.mapped_head at f_mem
        rw [List.getElem_map, ← List.inIffInToSet, List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_enum] at a_mem
        apply Or.inl
        exists trg.val.rule
        constructor
        . exact trg.property
        . unfold Rule.predicates
          rw [List.mem_append]
          apply Or.inr
          rw [List.mem_flatMap]
          exists trg.val.rule.head[0]'(by
            unfold RuleSet.isDeterministic at det
            unfold Rule.isDeterministic at det
            rw [det]
            . simp
            . exact trg.property
          )
          constructor
          . simp
          . unfold FunctionFreeConjunction.predicates
            rw [List.mem_map]
            exists a
            constructor
            . exact a_mem
            . rw [← p_mem, ← f_mem]
              simp [PreTrigger.apply_to_function_free_atom]

  theorem parallelSkolemChase_constants (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) :
      ∀ n, (kb.parallelSkolemChase det n).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      apply Set.subsetUnionSomethingStillSubset'
      rw [Database.toFactSet_constants_same]
      apply Set.subsetOfSelf
    | succ n ih =>
      unfold parallelSkolemChase
      intro c c_mem
      rcases c_mem with ⟨f, f_mem, c_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.result at f_mem
        unfold PreTrigger.mapped_head at f_mem
        rw [List.getElem_map, ← List.inIffInToSet, List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_enum] at a_mem
        apply Or.inl
        exists trg.val.rule
        constructor
        . exact trg.property
        . unfold Rule.head_constants
          rw [List.mem_flatMap]
          exists trg.val.rule.head[0]'(by
            unfold RuleSet.isDeterministic at det
            unfold Rule.isDeterministic at det
            rw [det]
            . simp
            . exact trg.property
          )
          constructor
          . simp
          . unfold FunctionFreeConjunction.consts
            rw [List.mem_flatMap]
            exists a
            constructor
            . exact a_mem
            . rw [← f_mem] at c_mem
              simp only [PreTrigger.apply_to_function_free_atom] at c_mem
              sorry

  theorem parallelSkolemChase_functions (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) :
      ∀ n, (kb.parallelSkolemChase det n).function_symbols ⊆ (kb.rules.skolem_functions) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      intro func func_mem
      unfold FactSet.function_symbols at func_mem
      rcases func_mem with ⟨f, f_mem, func_mem⟩
      unfold Fact.function_symbols at func_mem
      rcases func_mem with ⟨t, t_mem, func_mem⟩
      cases eq : t.val with
      | leaf c => simp [eq, FiniteTree.innerLabels] at func_mem
      | inner _ _ =>
        have func_free := kb.db.toFactSet.property.right
        specialize func_free f f_mem t t_mem
        rcases func_free with ⟨c, t_eq⟩
        rw [t_eq] at eq
        simp [GroundTerm.const] at eq
    | succ n ih =>
      unfold parallelSkolemChase
      intro func func_mem
      rcases func_mem with ⟨f, f_mem, func_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.result at f_mem
        unfold PreTrigger.mapped_head at f_mem
        rw [List.getElem_map, ← List.inIffInToSet, List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_enum] at a_mem
        exists trg.val.rule
        constructor
        . exact trg.property
        . unfold Rule.skolem_functions
          sorry

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

  theorem skolemChaseResult_predicates (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) :
      (kb.skolemChaseResult det).predicates ⊆ (kb.rules.predicates ∪ kb.db.toFactSet.val.predicates) := by
    intro p p_mem
    rcases p_mem with ⟨f, f_mem, p_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_predicates det n
    exists f

  theorem skolemChaseResult_constants (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) :
      (kb.skolemChaseResult det).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
    intro c c_mem
    rcases c_mem with ⟨f, f_mem, c_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_constants det n
    exists f

  theorem skolemChaseResult_functions (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) :
      (kb.skolemChaseResult det).function_symbols ⊆ (kb.rules.skolem_functions) := by
    intro func func_mem
    rcases func_mem with ⟨f, f_mem, func_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_functions det n
    exists f

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
        simp [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]
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
          intro c t t_arity_ok t_mem c_eq
          specialize every_t_special_const ⟨t, t_arity_ok⟩ t_mem
          rw [← c_eq]
          simp only [every_t_special_const]
          simp [GroundTerm.const, GroundTerm.toConst]
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
                          simp [GroundSubstitution.apply_var_or_const, StrictConstantMapping.apply_var_or_const, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]
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
                      simp only [StrictConstantMapping.apply_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]
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
                    simp only [StrictConstantMapping.apply_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]

  theorem filtered_cb_result_subset_mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (det : rs.isDeterministic) (special_const : sig.C) : ∀ {db : Database sig} (cb : ChaseBranch obs { rules := rs, db := db }), ((UniformConstantMapping sig special_const).toConstantMapping.apply_fact_set (fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result)) ⊆ (rs.mfaSet finite det special_const) := by
    intro db cb f f_mem

    rcases f_mem with ⟨f', f'_mem, f_eq⟩
    rcases f'_mem with ⟨f'_pred, f'_mem⟩
    rcases f'_mem with ⟨n, f'_mem⟩
    rw [f_eq]

    cases eq : cb.branch.infinite_list n with
    | none => simp [eq, Option.is_some_and] at f'_mem
    | some node =>
      have := rs.mfaSet_contains_every_chase_step_for_every_kb_expect_for_facts_with_predicates_not_from_rs finite det special_const cb n
      rw [eq, Option.is_none_or] at this
      apply this
      . exact f'_pred
      . rw [eq, Option.is_some_and] at f'_mem
        exact f'_mem

  theorem terminates_of_mfaSet_finite [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (det : rs.isDeterministic) : (rs.mfaSet rs_finite det Inhabited.default).finite -> rs.terminates obs := by
    intro mfa_finite
    unfold RuleSet.terminates
    intro db
    unfold KnowledgeBase.terminates
    intro ct
    unfold ChaseTree.terminates
    intro cb cb_mem
    rw [ChaseBranch.terminates_iff_result_finite]

    let res_filtered : FactSet sig := fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result
    have res_filtered_finite : res_filtered.finite := by
      have : ((UniformConstantMapping sig Inhabited.default).toConstantMapping.apply_fact_set (fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result)).finite :=
        Set.finite_of_subset_finite mfa_finite (rs.filtered_cb_result_subset_mfaSet rs_finite det Inhabited.default cb)

      rcases this with ⟨l, _, l_eq⟩

      let db_constants := db.constants
      rcases db_constants.property with ⟨l_db_c, _, l_db_c_eq⟩

      let rs_constants := rs.head_constants
      have rs_constants_finite : rs_constants.finite := RuleSet.head_constants_finite_of_finite _ rs_finite
      rcases rs_constants_finite with ⟨l_rs_c, _, l_rs_c_eq⟩

      let arguments : FactSet sig := fun f => (∀ c, c ∈ f.constants -> (c ∈ l_db_c ++ l_rs_c)) ∧ ((UniformConstantMapping sig default).toConstantMapping.apply_fact f) ∈ ((UniformConstantMapping sig default).toConstantMapping.apply_fact_set res_filtered)
      have arguments_fin : arguments.finite := by
        exists (l.flatMap (fun f => (UniformConstantMapping sig default).arguments_for_fact (l_db_c ++ l_rs_c) f)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro f
          rw [List.mem_eraseDupsKeepRight_iff, List.mem_flatMap]
          constructor
          . intro h
            rcases h with ⟨f', f'_mem, f_mem⟩
            rw [l_eq] at f'_mem
            have : f' = (UniformConstantMapping sig default).toConstantMapping.apply_fact f := by
              have := (UniformConstantMapping sig default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c) f'
              rw [((this _).mp _).right]
              exact f_mem
            rw [this] at f'_mem
            constructor
            . have := (UniformConstantMapping sig default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c) f' f
              apply (this.mp _).left
              exact f_mem
            . exact f'_mem
          . intro h
            exists (UniformConstantMapping sig default).toConstantMapping.apply_fact f
            constructor
            . rw [l_eq]
              exact h.right
            . rw [(UniformConstantMapping sig default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c)]
              simp only [and_true]
              exact h.left

      apply Set.finite_of_subset_finite arguments_fin
      intro f f_mem
      constructor
      . rcases f_mem.right with ⟨step, f_mem⟩
        intro c c_mem
        have := constantsInChaseBranchAreFromDatabase cb step
        cases eq_step : cb.branch.infinite_list step with
        | none => rw [eq_step] at f_mem; simp [Option.is_some_and] at f_mem
        | some node =>
          rw [eq_step, Option.is_some_and] at f_mem
          rw [eq_step, Option.is_none_or] at this
          specialize this c (by exists f)
          rw [List.mem_append]
          cases this with
          | inl this => apply Or.inl; rw [l_db_c_eq]; exact this
          | inr this => apply Or.inr; rw [l_rs_c_eq]; exact this
      . apply ConstantMapping.apply_fact_mem_apply_fact_set_of_mem
        exact f_mem

    have res_sub_db_and_filtered : cb.result ⊆ db.toFactSet.val ∪ res_filtered := by
      have each_step_sub_db_and_filtered : ∀ n, (cb.branch.infinite_list n).is_none_or (fun node => node.fact.val ⊆ db.toFactSet.val ∪ res_filtered) := by
        intro n
        induction n with
        | zero => rw [cb.database_first, Option.is_none_or]; intro f f_mem; apply Or.inl; exact f_mem
        | succ n ih =>
          cases eq_node : cb.branch.infinite_list (n+1) with
          | none => simp [eq_node, Option.is_none_or]
          | some node =>
            cases eq_prev : cb.branch.infinite_list n with
            | none =>
              have no_holes := cb.branch.no_holes (n+1)
              simp [eq_node] at no_holes
              specialize no_holes ⟨n, by simp⟩
              simp [eq_prev] at no_holes
            | some prev =>
              rw [eq_prev, Option.is_none_or] at ih
              rw [Option.is_none_or]
              intro f f_mem

              have trg_ex := cb.triggers_exist n
              rw [eq_prev, Option.is_none_or] at trg_ex
              cases trg_ex with
              | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq_node; simp at eq_node
              | inl trg_ex =>
                unfold exists_trigger_opt_fs at trg_ex
                rcases trg_ex with ⟨trg, trg_active, disj_index, step_eq⟩
                rw [eq_node] at step_eq
                injection step_eq with step_eq
                rw [← step_eq] at f_mem
                cases f_mem with
                | inl f_mem => apply ih; exact f_mem
                | inr f_mem =>
                  apply Or.inr
                  constructor
                  . -- since f occur in the trigger result, its predicate occurs in the rule and must therefore occur in the ruleset
                    simp only [List.get_eq_getElem, PreTrigger.result, List.getElem_map] at f_mem
                    rw [← List.inIffInToSet] at f_mem
                    simp only [PreTrigger.mapped_head] at f_mem
                    simp at f_mem
                    rcases f_mem with ⟨a, a_mem, f_eq⟩
                    rw [← f_eq]
                    simp only [PreTrigger.apply_to_function_free_atom]
                    exists trg.val.rule
                    constructor
                    . exact trg.property
                    . unfold Rule.predicates
                      rw [List.mem_append]
                      apply Or.inr
                      rw [List.mem_flatMap]
                      exists trg.val.rule.head[disj_index.val]'(by
                        have isLt := disj_index.isLt
                        unfold PreTrigger.result at isLt
                        simp only [List.length_map, ← PreTrigger.head_length_eq_mapped_head_length] at isLt
                        exact isLt
                      )
                      simp only [List.getElem_mem, true_and]
                      unfold FunctionFreeConjunction.predicates
                      rw [List.mem_map]
                      exists a
                  . exists (n+1)
                    rw [eq_node, Option.is_some_and, ← step_eq]
                    apply Or.inr
                    exact f_mem

      intro f f_mem
      rcases f_mem with ⟨n, f_mem⟩
      cases eq_node : cb.branch.infinite_list n with
      | none => simp [eq_node, Option.is_some_and] at f_mem
      | some node =>
        rw [eq_node, Option.is_some_and] at f_mem
        specialize each_step_sub_db_and_filtered n
        rw [eq_node, Option.is_none_or] at each_step_sub_db_and_filtered
        apply each_step_sub_db_and_filtered
        exact f_mem

    apply Set.finite_of_subset_finite _ res_sub_db_and_filtered
    apply Set.union_finite_of_both_finite
    . exact db.toFactSet.property.left
    . exact res_filtered_finite

  def isMfa [Inhabited sig.C] (rs : RuleSet sig) (finite : rs.rules.finite) (det : rs.isDeterministic) : Prop :=
    ∀ t, t ∈ (rs.mfaSet finite det default).terms -> ¬ PreGroundTerm.cyclic t.val

  theorem terminates_of_isMfa [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (det : rs.isDeterministic) : rs.isMfa rs_finite det -> rs.terminates obs := by
    intro isMfa
    apply rs.terminates_of_mfaSet_finite rs_finite det
    apply FactSet.finite_of_preds_finite_of_terms_finite
    . apply Set.finite_of_subset_finite _ (KnowledgeBase.skolemChaseResult_predicates (rs.mfaKb rs_finite default) (rs.mfaKb_det_of_rs_det rs_finite default det))
      apply Set.union_finite_of_both_finite
      . apply RuleSet.predicates_finite_of_finite
        unfold mfaKb
        simp only
        rcases rs_finite with ⟨l, _, l_eq⟩
        exists (l.map (UniformConstantMapping sig default).apply_rule).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro r
          rw [List.mem_eraseDupsKeepRight_iff]
          rw [List.mem_map]
          constructor
          . intro h
            rcases h with ⟨r', r'_mem, r_eq⟩
            exists r'
            constructor
            . rw [← l_eq]
              exact r'_mem
            . rw [r_eq]
          . intro h
            rcases h with ⟨r', r'_mem, r_eq⟩
            exists r'
            constructor
            . rw [l_eq]
              exact r'_mem
            . rw [r_eq]
      . have prop := (rs.mfaKb rs_finite default).db.toFactSet.property.left
        rcases prop with ⟨l, _, l_eq⟩
        exists (l.map (fun f => f.predicate)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro p
          rw [List.mem_eraseDupsKeepRight_iff]
          rw [List.mem_map]
          unfold FactSet.predicates
          constructor
          . intro h
            rcases h with ⟨f, f_mem, p_eq⟩
            exists f
            constructor
            . rw [← l_eq]
              exact f_mem
            . exact p_eq
          . intro h
            rcases h with ⟨f, f_mem, p_eq⟩
            exists f
            constructor
            . rw [l_eq]
              exact f_mem
            . exact p_eq
    . unfold RuleSet.isMfa at isMfa
      let funcs : Set (SkolemFS sig) := rs.skolem_functions
      have funcs_finite : funcs.finite := rs.skolem_functions_finite_of_finite rs_finite
      rcases funcs_finite with ⟨l_funcs, l_funcs_nodup, funcs_eq⟩
      let overapproximation : Set (GroundTerm sig) := fun t => (t.val.depth ≤ l_funcs.length + 1 ∧ (∀ c, c ∈ t.val.leaves -> c = default) ∧ (∀ func, func ∈ t.val.innerLabels -> func ∈ l_funcs))
      have overapproximation_finite : overapproximation.finite := by
        exists (all_terms_limited_by_depth [default] l_funcs (l_funcs.length + 1)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro t
          rw [List.mem_eraseDupsKeepRight_iff]
          rw [mem_all_terms_limited_by_depth]
          simp only [overapproximation, List.mem_singleton]
          rfl
      apply Set.finite_of_subset_finite overapproximation_finite
      intro t t_mem

      have : ∀ func, func ∈ t.val.innerLabels -> func ∈ l_funcs := by
        intro func func_mem
        rw [funcs_eq]
        unfold funcs

        have : rs.skolem_functions = (rs.mfaKb rs_finite default).rules.skolem_functions := by
          unfold mfaKb
          unfold RuleSet.skolem_functions
          simp only
          -- TODO: show more general result on Constant Mapping: constant mapping on rules do not change skolem functions
          sorry
        rw [this]

        apply (KnowledgeBase.skolemChaseResult_functions (rs.mfaKb rs_finite default) (rs.mfaKb_det_of_rs_det rs_finite default det))
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        exists f
        constructor
        . exact f_mem
        . exists t

      unfold overapproximation
      constructor
      . apply Decidable.byContradiction
        intro contra
        apply isMfa t t_mem
        apply PreGroundTerm.cyclic_of_depth_too_big t l_funcs
        . exact l_funcs_nodup
        . exact this
        . simp at contra
          apply Nat.succ_le_of_lt
          exact contra
      constructor
      . intro c c_mem

        have := (KnowledgeBase.skolemChaseResult_constants (rs.mfaKb rs_finite default) (rs.mfaKb_det_of_rs_det rs_finite default det))

        -- TODO: show that mfaKb only features the special constant!

        sorry
      . exact this

end RuleSet

