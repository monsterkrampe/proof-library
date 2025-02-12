import ProofLibrary.Set.Basic
import ProofLibrary.List

namespace Set

  def finite (X : Set α) : Prop := ∃ (l : List α), l.Nodup ∧ ∀ (e : α), e ∈ l ↔ e ∈ X

  theorem finite_of_subset_finite [DecidableEq α] {a b : Set α} (fin : b.finite) : a ⊆ b -> a.finite := by
    intro sub
    rcases fin with ⟨l, _, l_eq⟩
    exists (l.filter (fun e =>
      have := Classical.propDecidable (e ∈ a)
      decide (e ∈ a)
    )).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro e
      rw [List.mem_eraseDupsKeepRight_iff, List.mem_filter]
      simp
      intro e_mem
      rw [l_eq]
      apply sub
      exact e_mem

  theorem union_finite_of_both_finite [DecidableEq α] {a b : Set α} (fin_a : a.finite) (fin_b : b.finite) : (a ∪ b).finite := by
    rcases fin_a with ⟨l, _, l_eq⟩
    rcases fin_b with ⟨k, _, k_eq⟩
    exists (l ++ k).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro e
      rw [List.mem_eraseDupsKeepRight_iff, List.mem_append]
      constructor
      . intro h
        cases h with
        | inl h => apply Or.inl; rw [← l_eq]; exact h
        | inr h => apply Or.inr; rw [← k_eq]; exact h
      . intro h
        cases h with
        | inl h => apply Or.inl; rw [l_eq]; exact h
        | inr h => apply Or.inr; rw [k_eq]; exact h

end Set

