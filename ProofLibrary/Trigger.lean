import ProofLibrary.List
import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.SubstitutionAndHomomorphismBasics

structure Trigger where
  rule : Rule
  subs : GroundSubstitution

namespace Trigger
  def mapped_body (trg : Trigger) : List Fact := SubsTarget.apply trg.subs trg.rule.body
  def mapped_head (trg : Trigger) : List Fact := SubsTarget.apply trg.subs (Rule.skolemize trg.rule).head

  def result (trg : Trigger) : FactSet :=
    trg.mapped_head.toSet
  
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
