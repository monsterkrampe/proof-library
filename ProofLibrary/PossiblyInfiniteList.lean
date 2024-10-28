import ProofLibrary.List

def InfiniteList (α : Type u) := Nat -> α

namespace InfiniteList
  def take (l : InfiniteList α) : Nat -> List α
  | 0 => []
  | n+1 => (l.take n) ++ [l n]

  def skip (l : InfiniteList α) (m : Nat) : InfiniteList α := fun n => l (n + m)

  theorem skip_zero_eq (l : InfiniteList α) : l.skip 0 = l := by unfold skip; simp only [Nat.add_zero]

  theorem skip_m_get_sub_eq_get (l : InfiniteList α) (n m : Nat) (h : m ≤ n) : (l.skip m) (n - m) = l n := by
    unfold skip
    rw [← Nat.sub_add_comm h]
    simp

  theorem combine_skip_take (l : InfiniteList α) (n : Nat) (m : Fin n) : l.take m ++ (l.skip m).take (n-m) = l.take n := by
    induction n with
    | zero =>
      apply False.elim
      apply Nat.not_lt_zero
      apply m.isLt
    | succ k ih =>
      have : k.succ - m = (k-m).succ := by
        simp only [Nat.succ_eq_add_one]
        rw [Nat.sub_add_comm]
        apply Nat.le_of_lt_succ
        exact m.isLt
      rw [this]
      simp only [take]
      rw [skip_m_get_sub_eq_get (h := by apply Nat.le_of_lt_succ; exact m.isLt)]
      rw [← List.append_assoc]
      cases Decidable.em (m < k) with
      | inl hl =>
        rw [ih ⟨m.val, hl⟩]
      | inr hr =>
        have : m = k := by cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ m.isLt); contradiction; assumption
        rw [this]
        simp [take]
end InfiniteList

structure PossiblyInfiniteList (α : Type u) where
  infinite_list : InfiniteList (Option α)
  no_holes : ∀ n : Nat, infinite_list n ≠ none -> ∀ m : Fin n, infinite_list m ≠ none

namespace PossiblyInfiniteList
  def empty : PossiblyInfiniteList α := {
    infinite_list := fun _ => none
    no_holes := by intros; contradiction
  }
end PossiblyInfiniteList

