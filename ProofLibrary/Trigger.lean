import ProofLibrary.List
import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.SubstitutionAndHomomorphismBasics

structure Trigger where
  rule : Rule
  subs : GroundSubstitution

namespace Trigger
  def mapped_body (trg : Trigger) : List Fact := SubsTarget.apply trg.subs trg.rule.body
  def mapped_head (trg : Trigger) : List Fact := List.map (fun (i, a) => {
      predicate := a.predicate 
      terms := List.map ((SubsTarget.apply trg.subs) ∘ (VarOrConst.skolemize i trg.rule.frontier)) a.terms
    }) (List.enum trg.rule.head)

  def result (trg : Trigger) : FactSet :=
    trg.mapped_head.toSet

  def idx_of_fact_in_result (trg : Trigger) (f : Fact) (f_in_res : f ∈ trg.result) : Fin trg.rule.head.length :=
    let fin_mapped := trg.mapped_head.idx_of f (trg.mapped_head.listToSetElementAlsoListElement f f_in_res)
    have fin_mapped_isLt := fin_mapped.isLt
    ⟨fin_mapped.val, by simp [mapped_head, List.length_map, List.length_enum] at fin_mapped_isLt; exact fin_mapped_isLt⟩
  
  def loaded (trg : Trigger) (F : FactSet) : Prop :=
    trg.mapped_body ⊆ F

  def sobsolete (trg : Trigger) (F : FactSet) : Prop := 
    trg.mapped_head ⊆ F

  def sactive (trg : Trigger) (F : FactSet) : Prop :=
    trg.loaded F ∧ ¬ (trg.sobsolete F)

  def robsolete (trg : Trigger) (F : FactSet) : Prop := 
    ∃ s : GroundSubstitution,
      (∀ v, List.elem v (Rule.frontier trg.rule) → s v = trg.subs v) ∧
      (
        let l : List Fact := SubsTarget.apply s trg.rule.head
        l ⊆ F
      )

  def ractive (trg : Trigger) (F : FactSet) : Prop :=
    trg.loaded F ∧ ¬ (trg.robsolete F)

  theorem term_mapping_preserves_loadedness (trg : Trigger) (F : FactSet) (h : GroundTermMapping) (hh : isHomomorphism h) : trg.loaded F -> { rule := trg.rule, subs := h ∘ trg.subs : Trigger }.loaded (applyFactSet h F) := by 
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
          rw [List.combine_nested_map]
          simp [GroundSubstitution.apply_var_or_const]
          induction head.terms with 
          | nil => simp [List.map]
          | cons t_head t_tail t_ih => 
            simp [List.map]
            constructor
            . cases t_head with 
              | var v => simp 
              | const c => simp; apply hh (GroundTerm.const c)
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
      -> ¬ trg.ractive fs -- the rule is ractive iff it is not satisfied under FOL semantics

  def modelsRules (fs : FactSet) (rules : RuleSet) : Prop :=
    ∀ r, r ∈ rules -> fs.modelsRule r

  def modelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsDb kb.db ∧ fs.modelsRules kb.rules

  def universallyModelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsKb kb ∧ 
    (∀ m : FactSet,
      m.modelsKb kb ->
      ∃ (h : GroundTermMapping),
        isHomomorphism h ∧
        (applyFactSet h fs) ⊆ m
    )
end FactSet
