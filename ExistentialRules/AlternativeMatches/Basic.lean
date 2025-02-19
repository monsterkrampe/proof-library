import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.ChaseSequence.Deterministic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundTermMapping

  def isAlternativeMatch (h_alt : GroundTermMapping sig) (trg : PreTrigger sig) (disj_index : Fin trg.result.length) (fs : FactSet sig) : Prop :=
    (h_alt.isHomomorphism (trg.result.get disj_index) fs) ∧
    (∀ t, t ∈ trg.rule.frontier.map trg.subs -> h_alt t = t) ∧
    (∃ n, (n ∈ (trg.result.get disj_index).terms) ∧ (¬ n ∈ (h_alt.applyFactSet (trg.result.get disj_index)).terms))

end GroundTermMapping

namespace PreTrigger

  -- TODO: cleanup the proof; seems like we need lemmas on PreTrigger and Substitution Interaction (likely also useful elsewhere)
  theorem satisfied_of_alternativeMatch (trg : PreTrigger sig) (fs : FactSet sig) : ∀ (h_alt : GroundTermMapping sig) (disj_index : Fin trg.result.length), h_alt.isAlternativeMatch trg disj_index fs -> trg.satisfied fs := by
    intro h_alt disj_index is_alt_match
    exists ⟨disj_index.val, by have isLt := disj_index.isLt; rw [PreTrigger.head_length_eq_mapped_head_length]; unfold PreTrigger.result at isLt; simp at isLt; exact isLt⟩
    exists (h_alt ∘ trg.apply_to_var_or_const disj_index ∘ VarOrConst.var)
    constructor
    . intro v v_in_frontier
      simp only [Function.comp_apply]
      simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, v_in_frontier]
      apply is_alt_match.right.left
      simp
      exists v
    . intro f f_mem
      apply is_alt_match.left.right
      rw [List.mem_toSet] at f_mem
      unfold GroundSubstitution.apply_function_free_conj at f_mem
      simp at f_mem
      simp [PreTrigger.result, PreTrigger.mapped_head]
      unfold GroundTermMapping.applyFactSet
      rcases f_mem with ⟨a, a_mem, a_eq⟩
      exists trg.apply_to_function_free_atom disj_index a
      constructor
      . rw [List.mem_toSet]
        simp
        exists a
      . unfold PreTrigger.apply_to_function_free_atom
        unfold GroundTermMapping.applyFact
        simp
        unfold GroundSubstitution.apply_function_free_atom at a_eq
        rw [← a_eq]
        simp [PreTrigger.apply_to_var_or_const]
        intro t t_mem
        unfold PreTrigger.apply_to_skolemized_term
        unfold PreTrigger.skolemize_var_or_const
        simp [GroundSubstitution.apply_var_or_const]
        cases t with
        | const c => simp [VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]; apply is_alt_match.left.left (GroundTerm.const c)
        | var v => simp

  theorem alternativeMatch_of_satisfied (trg : PreTrigger sig) (fs : FactSet sig) (disj_index : Fin trg.result.length) (gt : GroundTerm sig) (gt_in_res_but_not_fs : gt ∈ (trg.result.get disj_index).terms ∧ ¬ gt ∈ fs.terms) : trg.satisfied_for_disj fs ⟨disj_index, by rw [PreTrigger.head_length_eq_mapped_head_length]; have isLt := disj_index.isLt; unfold PreTrigger.result at isLt; simp at isLt; exact isLt⟩ -> ∃ (h_alt : GroundTermMapping sig), h_alt.isAlternativeMatch trg disj_index fs := by
    intro satisfied
    rcases satisfied with ⟨s, s_frontier, s_subs⟩

    let h_alt : GroundTermMapping sig := fun t =>
      if t ∈ trg.rule.frontier.map trg.subs then t else match t.val with
        | .leaf c => t
        | .inner skolem_fs _ => s skolem_fs.var

    have : h_alt.applyFactSet (trg.result.get disj_index) ⊆ fs := by
      intro f f_mem
      apply s_subs
      unfold GroundTermMapping.applyFactSet at f_mem
      rcases f_mem with ⟨f', f'_mem, f'_eq⟩
      simp [PreTrigger.result, PreTrigger.mapped_head] at f'_mem
      rw [List.mem_toSet] at f'_mem
      simp at f'_mem
      rcases f'_mem with ⟨a, a_mem, a_eq⟩

      rw [List.mem_toSet]
      simp [GroundSubstitution.apply_function_free_conj]
      exists a
      constructor
      . exact a_mem
      . rw [← f'_eq, ← a_eq]
        simp [GroundSubstitution.apply_function_free_atom, GroundTermMapping.applyFact, PreTrigger.apply_to_function_free_atom]
        intro voc voc_mem
        cases voc with
        | const c =>
          simp [GroundSubstitution.apply_var_or_const, PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, PreTrigger.apply_to_skolemized_term, GroundSubstitution.apply_skolem_term]
          simp [h_alt, GroundTerm.const]
        | var v =>
          simp [GroundSubstitution.apply_var_or_const]
          cases Decidable.em (v ∈ trg.rule.frontier) with
          | inl v_in_frontier =>
            simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, PreTrigger.apply_to_skolemized_term, GroundSubstitution.apply_skolem_term]
            simp [v_in_frontier, h_alt]
            have : ∃ a, a ∈ trg.rule.frontier ∧ trg.subs a = trg.subs v := by exists v
            simp [this]
            apply s_frontier
            exact v_in_frontier
          | inr v_not_in_frontier =>
            simp only [h_alt]
            have : ¬ trg.apply_to_var_or_const disj_index.val (VarOrConst.var v) ∈ trg.rule.frontier.map trg.subs := by
              apply PreTrigger.result_term_not_in_frontier_image_of_var_not_in_frontier
              exact v_not_in_frontier
            simp [this]
            simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, PreTrigger.apply_to_skolemized_term, GroundSubstitution.apply_skolem_term]
            simp [v_not_in_frontier]

    exists h_alt
    constructor
    . constructor
      . intro t; cases eq : t.val with
        | leaf c => simp [h_alt, eq]
        | inner _ _ => simp
      . exact this
    constructor
    . intro t ht; simp only [h_alt, ht]; simp
    . exists gt
      constructor
      . exact gt_in_res_but_not_fs.left
      . intro contra
        apply gt_in_res_but_not_fs.right
        rcases contra with ⟨f, f_mem, gt_mem⟩
        exists f
        constructor
        . apply this; exact f_mem
        . exact gt_mem

end PreTrigger

