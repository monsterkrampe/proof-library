import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.SubstitutionAndHomomorphismBasics

namespace FactSet
  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def modelsDb (fs : FactSet sig) (db : Database sig) : Prop :=
    db.toFactSet ⊆ fs

  def modelsRule (fs : FactSet sig) (rule : Rule sig) : Prop :=
    ∀ (s : GroundSubstitution sig),
      ((s.apply_function_free_conj rule.body).toSet ⊆ fs) ->
        ∃ (s' : GroundSubstitution sig) (i : Fin rule.head.length),
          (∀ v, v ∈ rule.frontier → s' v = s v) ∧
          ((s'.apply_function_free_conj (rule.head.get i)).toSet ⊆ fs)

  def modelsRules (fs : FactSet sig) (rules : RuleSet sig) : Prop :=
    ∀ r, r ∈ rules.rules -> fs.modelsRule r

  def modelsKb (fs : FactSet sig) (kb : KnowledgeBase sig) : Prop :=
    fs.modelsDb kb.db ∧ fs.modelsRules kb.rules

  def universallyModelsKb (fs : FactSet sig) (kb : KnowledgeBase sig) : Prop :=
    fs.modelsKb kb ∧
    (∀ (m : FactSet sig), m.modelsKb kb -> ∃ (h : GroundTermMapping sig), h.isHomomorphism fs m)
end FactSet

