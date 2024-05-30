import ProofLibrary.Fin
import ProofLibrary.Option
import ProofLibrary.List
import ProofLibrary.PossiblyInfiniteList

-- NOTE: all finite lists indicating positions are right to left; infinite lists left to right (don't ask)

def InfiniteTreeSkeleton (α : Type u) := (List Nat) -> α

namespace InfiniteTreeSkeleton
  def children (tree : InfiniteTreeSkeleton α) (node : List Nat) : InfiniteList α := fun n => tree (n :: node)

  -- def branch_for (tree : InfiniteTreeSkeleton α) (address : InfiniteList Nat) : InfiniteList α := fun n => tree (address.take n)

  def branches (tree : InfiniteTreeSkeleton α) : Set (InfiniteList α) := fun branch => ∃ nodes : InfiniteList Nat, 
    ∀ n : Nat, branch n = tree (nodes.take n).reverse 
end InfiniteTreeSkeleton

structure PossiblyInfiniteTree (α : Type u) where 
  infinite_tree : InfiniteTreeSkeleton (Option α)
  no_orphans : ∀ node : List Nat, infinite_tree node ≠ none -> ∀ parent : { l : List Nat // ∃ diff, diff ++ l = node }, infinite_tree parent ≠ none
  no_holes_in_children : ∀ node : List Nat, ∀ n : Nat, (infinite_tree.children node) n ≠ none -> ∀ m : Fin n, (infinite_tree.children node) m ≠ none

namespace PossiblyInfiniteTree
  def get (tree : PossiblyInfiniteTree α) (node : List Nat) : Option α := tree.infinite_tree node

  def children (tree : PossiblyInfiniteTree α) (node : List Nat) : PossiblyInfiniteList α := {
    infinite_list := tree.infinite_tree.children node,
    no_holes := by apply tree.no_holes_in_children
  }

  theorem children_empty_when_not_existing (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.get node = none -> tree.children node = PossiblyInfiniteList.empty := by 
    intro h
    unfold children
    unfold PossiblyInfiniteList.empty
    simp
    apply funext
    intro index
    have dec : Decidable (tree.infinite_tree.children node index = none) := Option.decidable_eq_none
    apply dec.byContradiction
    intro contra
    let parent : { l : List Nat // ∃ diff, diff ++ l = index :: node } := ⟨node, by exists [index]⟩
    have : tree.infinite_tree parent ≠ none := by 
      apply no_orphans
      unfold InfiniteTreeSkeleton.children at contra
      exact contra
    contradiction

  theorem children_empty_means_all_following_none (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.children node = PossiblyInfiniteList.empty -> ∀ i, tree.get (i :: node) = none := by 
    intro h i
    unfold get
    unfold children at h
    unfold PossiblyInfiniteList.empty at h
    simp at h
    unfold InfiniteTreeSkeleton.children at h
    apply congr h
    rfl

  def branches (tree : PossiblyInfiniteTree α) : Set (PossiblyInfiniteList α) := fun pil => pil.infinite_list ∈ tree.infinite_tree.branches

  def leaves (tree : PossiblyInfiniteTree α) : Set α := fun a => ∃ node : List Nat, tree.get node = some a ∧ tree.children node = PossiblyInfiniteList.empty
end PossiblyInfiniteTree

structure FiniteDegreeTree (α : Type u) where 
  tree : PossiblyInfiniteTree α 
  finitely_many_children : ∀ node : List Nat, ∃ k, (tree.children node).infinite_list k = none ∧ ∀ k' : Fin k, (tree.children node).infinite_list k' ≠ none

namespace FiniteDegreeTree
  def get (tree : FiniteDegreeTree α) (node : List Nat) : Option α := tree.tree.get node

  def children (tree : FiniteDegreeTree α) (node : List Nat) : List α := 
    let rec loop (n : Nat) : List α := match eq : (tree.tree.children node).infinite_list n with 
      | .none => []
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
        a :: loop (n+1)
    termination_by Classical.choose (tree.finitely_many_children node) - n
    loop 0

    theorem in_children_loop_iff_step (tree : FiniteDegreeTree α) (node : List Nat) : ∀ (el : α) (n : Nat), (el ∈ children.loop tree node n) ↔ ((some el = (tree.tree.children node).infinite_list n) ∨ el ∈ children.loop tree node (n+1)) := by 
    intro el n
    cases eq : (tree.tree.children node).infinite_list n with 
    | none => 
      simp 
      unfold children.loop
      constructor
      . intro contra
        apply False.elim
        simp [eq] at contra
        split at contra
        . contradiction
        case h_2 _ heq => 
          rw [eq] at heq
          contradiction
      . intro h
        let fin : Fin (n+1) := ⟨n, by simp⟩
        have : ¬ (tree.tree.children node).infinite_list fin = none := by 
          apply tree.tree.no_holes_in_children
          cases eq2 : (tree.tree.children node).infinite_list (n+1) with 
          | none => 
            split at h
            . contradiction
            case a.none.h_2 _ heq => 
              rw [eq2] at heq
              contradiction
          | some a => 
            apply Option.someNotNone 
            apply eq2
        contradiction
    | some a => 
      constructor
      . intro h
        unfold children.loop at h
        split at h
        . contradiction
        case h_2 a' heq => 
          simp at h
          cases h with 
          | inl h => apply Or.inl; rw [h, ←eq, heq]
          | inr h => apply Or.inr; apply h
      . intro h
        unfold children.loop
        split
        case h_1 heq => rw [heq] at eq; contradiction
        case h_2 a heq => 
          simp
          cases h with 
          | inl h => apply Or.inl; rw [heq] at eq; injection eq with eq; injection h with h; rw [h, eq]
          | inr h => apply Or.inr; apply h

  theorem in_children_loop_iff (tree : FiniteDegreeTree α) (node : List Nat) : ∀ (el : α) (n m : Nat), (el ∈ children.loop tree node n) ↔ ((∃ i : Fin m, some el = (tree.tree.children node).infinite_list (n+i)) ∨ el ∈ children.loop tree node (n+m)) := by 
    intro el n m
    
    induction m with 
    | zero => simp; intro i; have contra := i.isLt; contradiction
    | succ m ih =>
      rw [ih]
      constructor
      . intro h
        cases h with 
        | inl h => 
          apply Or.inl
          cases h with | intro i hi => 
            exists ⟨i.val, by apply Nat.lt_trans; apply i.isLt; simp⟩  
        | inr h => 
          have h_iff_step := (tree.in_children_loop_iff_step node el (n + m)).mp h
          cases h_iff_step with 
          | inl h => 
            apply Or.inl
            let fin : Fin (m+1) := ⟨m, by simp⟩ 
            exists fin
          | inr h => apply Or.inr; apply h
      . intro h
        cases h with 
        | inl h => 
          rw [tree.in_children_loop_iff_step]
          rw [← or_assoc]
          apply Or.inl
          cases h with | intro i hi =>
            have fin_cases := i.eq_last_or_prev_fin
            cases fin_cases with 
            | inl h => rw [h] at hi; apply Or.inr; apply hi
            | inr h => 
              cases h with | intro j hj => 
                rw [hj] at hi
                apply Or.inl
                exists j
        | inr h => 
          apply Or.inr
          rw [tree.in_children_loop_iff_step]
          apply Or.inr 
          apply h

  theorem in_children_iff_loop_index_exists (tree : FiniteDegreeTree α) (node : List Nat) : ∀ (el : α), (el ∈ tree.children node) ↔ (∃ n l, (children.loop tree node n) = el :: l) := by 
    intro el
    unfold children
    constructor
    . cases tree.finitely_many_children node with | intro k hk =>
        rw [tree.in_children_loop_iff node el 0 k]
        intro h
        cases h with 
        | inr h => 
          simp at h
          unfold children.loop at h
          split at h
          . contradiction
          case h_2 a heq => 
            have contra := hk.left
            rw [heq] at contra
            contradiction
        | inl h => 
          cases h with | intro i hi =>
            simp at hi
            exists i
            exists children.loop tree node (i+1)
            conv => left; unfold children.loop
            split
            case h_1 heq => rw [heq] at hi; contradiction
            case h_2 a heq => 
              simp
              rw [heq] at hi
              injection hi with hi
              rw [hi]
    . intro h
      cases h with | intro n h => cases h with | intro l h =>
        rw [tree.in_children_loop_iff node el 0 n]
        apply Or.inr
        simp
        rw [h]
        simp

  theorem in_children_iff_index_exists (tree : FiniteDegreeTree α) (node : List Nat) : ∀ (el : α), (el ∈ tree.children node) ↔ (∃ n, (tree.tree.children node).infinite_list n = some el) := by 
    intro el
    rw [in_children_iff_loop_index_exists]
    constructor 
    . intro h 
      cases h with | intro n h => cases h with | intro l h =>
        exists n
        unfold children.loop at h
        split at h
        . contradiction
        case h_2 a heq => 
          simp at h
          rw [heq]
          rw [h.left]
    . intro h
      cases h with | intro n h =>
        exists n
        exists children.loop tree node (n+1)
        conv => left; unfold children.loop
        split
        case h_1 heq => rw [heq] at h; contradiction
        case h_2 a heq => 
          simp
          rw [heq] at h
          injection h

  theorem children_empty_when_not_existing (tree : FiniteDegreeTree α) (node : List Nat) : tree.get node = none -> tree.children node = [] := by 
    intro h
    unfold children
    unfold children.loop
    unfold get at h
    have : tree.tree.children node = PossiblyInfiniteList.empty := by apply PossiblyInfiniteTree.children_empty_when_not_existing; exact h
    have : (tree.tree.children node).infinite_list 0 = none := by rw [this]; unfold PossiblyInfiniteList.empty; simp
    simp
    rw [this]

  theorem children_empty_means_all_following_none (tree : FiniteDegreeTree α) (node : List Nat) : tree.children node = [] -> ∀ i, tree.get (i :: node) = none := by 
    intro h 
    unfold children at h
    unfold children.loop at h
    unfold get
    apply PossiblyInfiniteTree.children_empty_means_all_following_none

    have zero_th_child_none : (tree.tree.children node).infinite_list 0 = none := by 
      have dec : Decidable ((tree.tree.children node).infinite_list 0 = none) := Option.decidable_eq_none
      apply dec.byContradiction
      intro contra
      split at h
      . contradiction
      . simp at h

    have : ∀ i, (tree.tree.children node).infinite_list i = none := by 
      intro i
      cases i with 
      | zero => apply zero_th_child_none
      | succ i => 
        have dec : Decidable ((tree.tree.children node).infinite_list (i+1) = none) := Option.decidable_eq_none
        apply dec.byContradiction
        intro contra
        let zero_fin : Fin (i+1) := ⟨0, by simp⟩
        have : ¬ (tree.tree.children node).infinite_list zero_fin = none := by 
          apply (tree.tree.children node).no_holes
          apply contra
        contradiction
    unfold PossiblyInfiniteTree.children
    unfold PossiblyInfiniteList.empty
    simp
    apply funext
    unfold PossiblyInfiniteTree.children at this
    simp at this
    apply this

  -- def branch_for (tree : FiniteDegreeTree α) (address : InfiniteList Nat) : PossiblyInfiniteList α := tree.tree.branch_for address

  def branches (tree : FiniteDegreeTree α) : Set (PossiblyInfiniteList α) := tree.tree.branches

  def leaves (tree : FiniteDegreeTree α) : Set α := tree.tree.leaves
end FiniteDegreeTree

