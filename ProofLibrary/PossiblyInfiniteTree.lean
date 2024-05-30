import ProofLibrary.Option
import ProofLibrary.List
import ProofLibrary.PossiblyInfiniteList

def InfiniteTreeSkeleton (α : Type u) := (List Nat) -> α

namespace InfiniteTreeSkeleton
  def children (tree : InfiniteTreeSkeleton α) (node : List Nat) : InfiniteList α := fun n => tree (node ++ [n])

  def branch_for (tree : InfiniteTreeSkeleton α) (address : InfiniteList Nat) : InfiniteList α := fun n => tree (address.take n)

  -- def branches (tree : InfiniteTreeSkeleton α) : Set (InfiniteList α) := fun branch => ∃ nodes : InfiniteList Nat, 
  --   ∀ n : Nat, branch n = tree (nodes.take n) 
end InfiniteTreeSkeleton

structure PossiblyInfiniteTree (α : Type u) where 
  infinite_tree : InfiniteTreeSkeleton (Option α)
  no_orphans : ∀ node : List Nat, infinite_tree node ≠ none -> ∀ parent : { l : List Nat // ∃ diff, l ++ diff = node}, infinite_tree parent ≠ none
  no_holes_in_children : ∀ node : List Nat, ∀ n : Nat, (infinite_tree.children node) n ≠ none -> ∀ m : Fin n, (infinite_tree.children node) m ≠ none

namespace PossiblyInfiniteTree
  def get (tree : PossiblyInfiniteTree α) (node : List Nat) : Option α := tree.infinite_tree node

  def children (tree : PossiblyInfiniteTree α) (node : List Nat) : PossiblyInfiniteList α := {
    infinite_list := tree.infinite_tree.children node,
    no_holes := by apply tree.no_holes_in_children
  }

  def branch_for (tree : PossiblyInfiniteTree α) (address : InfiniteList Nat) : PossiblyInfiniteList α := {
    infinite_list := tree.infinite_tree.branch_for address,
    no_holes := by 
      intro n h m 
      -- unfold InfiniteTreeSkeleton.branch_for
      apply tree.no_orphans (address.take n) h (⟨address.take m, _⟩)
      exists (address.skip m).take (n - m)
      rw [InfiniteList.combine_skip_take]
  }

  -- def branches (tree : PossiblyInfiniteTree α) : Set (PossiblyInfiniteList α) := fun pil => pil.infinite_list ∈ tree.infinite_tree.branches

  def leaves (tree : PossiblyInfiniteTree α) : Set α := fun a => ∃ node : List Nat, tree.get node = some a ∧ tree.children node = PossiblyInfiniteList.empty
end PossiblyInfiniteTree

structure FiniteDegreeTree (α : Type u) where 
  tree : PossiblyInfiniteTree α 
  finitely_many_children : ∀ node : List Nat, ∃ k, (tree.children node).infinite_list k = none ∧ ∀ k' : Fin k, (tree.children node).infinite_list k' ≠ none

namespace FiniteDegreeTree
  def get (tree : FiniteDegreeTree α) (node : List Nat) : Option α := tree.tree.get node

  def children (tree : FiniteDegreeTree α) (node : List Nat) : List α := 
    -- have k : Nat := by sorry
    let rec loop (n : Nat) (l : List α) : List α := match eq : (tree.tree.children node).infinite_list n with 
      | .none => l
      | .some a => 
        have : Classical.choose (tree.finitely_many_children node) - (n+1) < Classical.choose (tree.finitely_many_children node) - n := by 
          apply Nat.sub_add_lt_sub
          . apply Classical.byContradiction
            intro contra 
            simp at contra
            have hk_none := (Classical.choose_spec (tree.finitely_many_children node)).left
            have hk_not_none : (tree.tree.children node).infinite_list (Classical.choose (tree.finitely_many_children node)) ≠ none := by 
              simp only [PossiblyInfiniteTree.children]
              simp only [PossiblyInfiniteTree.children] at eq
              have goal := 
                tree.tree.no_holes_in_children 
                node 
                n 
                (by apply Option.someNotNone; apply eq) 
                ⟨Classical.choose (tree.finitely_many_children node), by 
                  cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ contra) with 
                  | inl hl => 
                    simp only [PossiblyInfiniteTree.children] at hk_none
                    rw [hl] at hk_none
                    have eq_not_none := Option.someNotNone eq
                    contradiction
                  | inr hr => exact hr
                ⟩ 
              exact goal
            contradiction
          . simp
        loop (n+1) (l ++ [a])
    termination_by Classical.choose (tree.finitely_many_children node) - n
    loop 0 []

  def branch_for (tree : FiniteDegreeTree α) (address : InfiniteList Nat) : PossiblyInfiniteList α := tree.tree.branch_for address

  -- def branches (tree : FiniteDegreeTree α) : Set (PossiblyInfiniteList α) := tree.tree.branches

  def leaves (tree : FiniteDegreeTree α) : Set α := tree.tree.leaves
end FiniteDegreeTree

