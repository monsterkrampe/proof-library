-- import Mathlib.Data.Stream.Defs

def Stream' (α : Type u) := Nat -> α 

structure PossiblyInfiniteList (α) where
  infinite_list : Stream' (Option α)
  no_holes : ∀ n : Nat, infinite_list n ≠ none -> ∀ m : Nat, m < n -> infinite_list m ≠ none
