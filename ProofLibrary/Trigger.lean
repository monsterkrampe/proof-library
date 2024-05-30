import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.SubstitutionAndHomomorphismBasics

structure Trigger where
  rule : Rule
  subs : GroundSubstitution

namespace Trigger
  def skolemize_var_or_const (trg : Trigger) (var_or_const : VarOrConst) : SkolemTerm := 
    var_or_const.skolemize trg.rule.id trg.rule.frontier

  def apply_to_skolemized_term (trg : Trigger) (skolem_term : SkolemTerm) : GroundTerm :=
    trg.subs.apply_skolem_term skolem_term

  def apply_to_var_or_const (trg : Trigger) : VarOrConst -> GroundTerm := 
    (trg.apply_to_skolemized_term ∘ trg.skolemize_var_or_const)

  def apply_to_function_free_atom (trg : Trigger) (atom : FunctionFreeAtom) : Fact :=
    {
      predicate := atom.predicate
      terms := atom.terms.map trg.apply_to_var_or_const
    }

  theorem apply_to_function_free_atom_terms_same_length (trg : Trigger) (atom : FunctionFreeAtom) : atom.terms.length = (trg.apply_to_function_free_atom atom).terms.length := by 
    unfold apply_to_function_free_atom
    simp

  def mapped_body (trg : Trigger) : List Fact := SubsTarget.apply trg.subs trg.rule.body
  def mapped_head (trg : Trigger) : List (List Fact) := trg.rule.head.map (fun h => h.map trg.apply_to_function_free_atom)

  theorem head_length_eq_mapped_head_length (trg : Trigger) : trg.rule.head.length = trg.mapped_head.length := by 
    unfold mapped_head
    rw [List.length_map]

  def result (trg : Trigger) : List FactSet :=
    trg.mapped_head.map List.toSet

  theorem subs_application_is_injective_for_freshly_introduced_terms {t : Variable} (trg : Trigger) (t_not_in_frontier : ¬ trg.rule.frontier.elem t) : ∀ s, (trg.apply_to_var_or_const (VarOrConst.var t) = trg.apply_to_var_or_const (VarOrConst.var s)) -> trg.skolemize_var_or_const (VarOrConst.var t) = trg.skolemize_var_or_const (VarOrConst.var s) := by 
    intro s apply_eq_for_t_and_s
    cases Decidable.em (trg.rule.frontier.elem s) with 
    | inr hr => 
      simp [t_not_in_frontier, hr, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at apply_eq_for_t_and_s
      simp [t_not_in_frontier, hr, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize]
      injection apply_eq_for_t_and_s with tree_node_eq
      injection tree_node_eq
    | inl hl => 
      simp [t_not_in_frontier, hl, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at apply_eq_for_t_and_s
      apply False.elim
      let tree_for_s := trg.apply_to_var_or_const (VarOrConst.var s)
      let ts := trg.rule.frontier.map (fun fv => trg.subs fv)
      let a : SkolemFS := { ruleId := trg.rule.id, var := t }
      apply FiniteTree.tree_eq_while_contained_is_impossible tree_for_s (FiniteTreeList.fromList ts) a
      simp [tree_for_s, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, hl]
      apply apply_eq_for_t_and_s
      simp [tree_for_s, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, hl]
      apply List.listToSetElementAlsoListElement
      rw [FiniteTreeList.fromListToListIsId]
      apply List.mappedElemInMappedList
      apply List.listElementAlsoToSetElement
      apply hl

  def idx_of_fact_in_result (trg : Trigger) (f : Fact) (disj_index : Fin trg.result.length) (f_in_res : f ∈ trg.result.get disj_index) : Fin (trg.rule.head.get ⟨disj_index.val, (by rw [head_length_eq_mapped_head_length]; have isLt := disj_index.isLt; unfold result at isLt; simp only [List.length_map] at isLt; exact isLt)⟩).length :=
    let disj_index_mapped_head : Fin trg.mapped_head.length := ⟨disj_index.val, (by have isLt := disj_index.isLt; unfold result at isLt; simp only [List.length_map] at isLt; exact isLt)⟩
    let fin_mapped := (trg.mapped_head.get disj_index_mapped_head).idx_of f ((trg.mapped_head.get disj_index_mapped_head).listToSetElementAlsoListElement f (by unfold result at f_in_res; rw [List.get_map] at f_in_res; apply f_in_res))
    have fin_mapped_isLt := fin_mapped.isLt
    ⟨fin_mapped.val, by simp only [mapped_head, List.length_map, List.get_map] at fin_mapped_isLt; exact fin_mapped_isLt⟩

  theorem apply_subs_to_atom_at_idx_same_as_fact_at_idx (trg : Trigger) (disj_index : Fin trg.rule.head.length) (idx : Fin (trg.rule.head.get disj_index).length) : trg.apply_to_function_free_atom ((trg.rule.head.get disj_index).get idx) = (trg.mapped_head.get ⟨disj_index.val, (by rw [← head_length_eq_mapped_head_length]; exact disj_index.isLt)⟩).get ⟨idx.val, (by unfold mapped_head; rw [List.get_map]; rw [List.length_map]; exact idx.isLt)⟩ := by 
    unfold mapped_head
    have : (trg.rule.head.map (fun h => h.map trg.apply_to_function_free_atom)).get ⟨disj_index.val, (by rw [List.length_map]; exact disj_index.isLt)⟩ = (trg.rule.head.get disj_index).map trg.apply_to_function_free_atom := by 
      rw [List.get_map]
    rw [List.get_eq_of_eq this]
    rw [List.get_map]
  
  def loaded (trg : Trigger) (F : FactSet) : Prop :=
    trg.mapped_body.toSet ⊆ F

  def sobsolete (trg : Trigger) (F : FactSet) : Prop := 
    ∃ i : Fin trg.mapped_head.length, (trg.mapped_head.get i).toSet ⊆ F

  def sactive (trg : Trigger) (F : FactSet) : Prop :=
    trg.loaded F ∧ ¬ (trg.sobsolete F)

  def robsolete (trg : Trigger) (F : FactSet) : Prop := 
    ∃ (s : GroundSubstitution) (i : Fin trg.rule.head.length),
      (∀ v, List.elem v (Rule.frontier trg.rule) → s v = trg.subs v) ∧
      ((s.apply_function_free_conj (trg.rule.head.get i)).toSet ⊆ F)

  def ractive (trg : Trigger) (F : FactSet) : Prop :=
    trg.loaded F ∧ ¬ (trg.robsolete F)

  theorem term_mapping_preserves_loadedness (trg : Trigger) (F : FactSet) (h : GroundTermMapping) (hh : isIdOnConstants h) : trg.loaded F -> { rule := trg.rule, subs := h ∘ trg.subs : Trigger }.loaded (applyFactSet h F) := by 
    simp [loaded, mapped_body]
    induction trg.rule.body with 
    | nil => intro _ _ _; contradiction
    | cons head tail ih => 
      intro base f hf
      simp [Set.element, Set.union, List.toSet] at hf
      cases hf with 
      | inl hl => 
        have := Set.element_mapping_preserves_membership (GroundSubstitution.apply_function_free_atom trg.subs head) F (applyFact h)
        have := this (base (GroundSubstitution.apply_function_free_atom trg.subs head) (by apply Or.inl; simp [Set.element]))
        simp [Set.element, applyFactSet]
        simp [Set.element] at this 
        cases this with | intro e he => 
          exists e
          rw [hl] 
          constructor 
          exact he.left 
          rw [← he.right]
          simp [applyFact, GroundSubstitution.apply_function_free_atom]
          induction head.terms with 
          | nil => simp [List.map]
          | cons t_head t_tail t_ih => 
            simp [List.map]
            constructor
            . cases t_head with 
              | var v => simp [GroundSubstitution.apply_var_or_const]
              | const c => simp [GroundSubstitution.apply_var_or_const]; apply hh (GroundTerm.const c)
            . apply t_ih
      | inr hr => 
        apply ih
        intro _ hf'; apply base; apply Or.inr; apply hf'
        exact hr 
end Trigger

namespace FactSet
  def modelsDb (fs : FactSet) (db : Database) : Prop :=
    db.toFactSet ⊆ fs

  def modelsRule (fs : FactSet) (rule : Rule) : Prop :=
    ∀ trg : Trigger,
      (trg.rule = rule ∧ trg.loaded fs)
      -> trg.robsolete fs -- the rule is ractive iff it is not satisfied under FOL semantics

  def modelsRules (fs : FactSet) (rules : RuleSet) : Prop :=
    ∀ r, r ∈ rules.rules -> fs.modelsRule r

  def modelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsDb kb.db ∧ fs.modelsRules kb.rules

  def universallyModelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsKb kb ∧ 
    (∀ m : FactSet, m.modelsKb kb -> ∃ (h : GroundTermMapping), isHomomorphism h fs m)
end FactSet

def RTrigger (r : RuleSet) := { trg : Trigger // trg.rule ∈ r.rules}

namespace RTrigger 
  theorem funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame 
    {rs : RuleSet} 
    (trg1 trg2 : RTrigger rs) 
    (var1 var2 : Variable) 
    (var1_not_in_frontier : trg1.val.rule.frontier.elem var1 = false) 
    (var2_not_in_frontier : trg2.val.rule.frontier.elem var2 = false) 
    : 
    (trg1.val.apply_to_var_or_const (VarOrConst.var var1)) = (trg2.val.apply_to_var_or_const (VarOrConst.var var2))
    -> 
    trg1.val.rule = trg2.val.rule ∧ ∀ v, v ∈ trg1.val.rule.frontier.toSet -> trg1.val.subs v = trg2.val.subs v := by 
    intro applications_eq 
    simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var1_not_in_frontier, var2_not_in_frontier] at applications_eq
    injection applications_eq with rule_ids_and_vars_eq arguments_eq
    simp at rule_ids_and_vars_eq
    have rules_eq : trg1.val.rule = trg2.val.rule := by 
      apply rs.id_unique
      constructor
      exact trg1.property
      constructor
      exact trg2.property
      exact rule_ids_and_vars_eq.left
    constructor
    . exact rules_eq
    . let right := arguments_eq 
      rw [← FiniteTreeList.eqIffFromListEq _ _] at right
      have : trg1.val.rule.frontier = trg2.val.rule.frontier := by rw [rules_eq]
      rw [← this] at right
      rw [← List.map_eq_map_iff] at right
      apply right
end RTrigger
