import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.Trigger

def InfiniteList (α : Type u) := Nat → α  

structure ChaseSequence (kb : KnowledgeBase) where
  fact_sets : InfiniteList FactSet
  database_first : fact_sets 0 = kb.db
  triggers_exist : ∀ n : Nat, (
      ∃ trg : Trigger, trg.ractive (fact_sets n) ∧ trg.result = fact_sets (n + 1)
    ) ∨ (
      ¬(∃ trg : Trigger, trg.ractive (fact_sets n)) ∧ fact_sets n = fact_sets (n + 1)
    )
  fairness : ∀ (trg : Trigger) (i : Nat), (trg.ractive (fact_sets i)) → ∃ j : Nat, j ≥ i ∧ (¬ trg.ractive (fact_sets j))

namespace ChaseSequence
  -- def result {kb : KnowledgeBase} (cs : ChaseSequence kb) : FactSet := sorry

  def terminates {kb : KnowledgeBase} (cs : ChaseSequence kb) : Prop :=
    ∃ n : Nat, cs.fact_sets n = cs.fact_sets (n + 1)
end ChaseSequence

namespace KnowledgeBase
  def terminates (kb : KnowledgeBase) : Prop :=
    ∃ cs : ChaseSequence kb, cs.terminates

  def universally_terminates (kb : KnowledgeBase) : Prop :=
    ∀ cs : ChaseSequence kb, cs.terminates
end KnowledgeBase
