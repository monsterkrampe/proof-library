import ProofLibrary.Fin
import ProofLibrary.Option
import ProofLibrary.List
import ProofLibrary.PossiblyInfiniteList

-- NOTE: all finite lists indicating positions are right to left; infinite lists left to right (don't ask)

def InfiniteTreeSkeleton (α : Type u) := (List Nat) -> α

namespace InfiniteTreeSkeleton

  def children (tree : InfiniteTreeSkeleton α) (node : List Nat) : InfiniteList α := fun n => tree (n :: node)

  def branches_through (tree : InfiniteTreeSkeleton α) (node : List Nat) : Set (InfiniteList α) := fun branch =>
    ∃ nodes : InfiniteList Nat, (∀ n : Nat, branch n = tree (nodes.take n).reverse) ∧ (nodes.take node.length).reverse = node

  def branches (tree : InfiniteTreeSkeleton α) : Set (InfiniteList α) := tree.branches_through []

  theorem branches_through_eq_union_children (tree : InfiniteTreeSkeleton α) (node : List Nat) : tree.branches_through node = fun b => ∃ (i : Nat), b ∈ tree.branches_through (i :: node) := by
    unfold branches_through
    apply funext
    simp
    intro b
    constructor
    . intro ⟨nodes, h⟩
      exists nodes node.length
      simp [Set.element]
      exists nodes
      constructor
      . exact h.left
      . unfold InfiniteList.take
        simp
        rw [← List.reverse_eq_iff]
        exact h.right
    . intro h
      rcases h with ⟨i, nodes, h⟩
      exists nodes
      constructor
      . exact h.left
      . have hr := h.right
        unfold InfiniteList.take at hr
        rw [← List.reverse_inj] at hr
        rw [List.reverse_append] at hr
        rw [List.reverse_append] at hr
        simp at hr
        exact hr.right

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

  theorem first_child_none_means_children_empty (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.get (0::node) = none -> tree.children node = PossiblyInfiniteList.empty := by
    intro h
    unfold PossiblyInfiniteList.empty
    unfold children
    unfold InfiniteTreeSkeleton.children
    simp
    apply funext
    intro n
    cases n with
    | zero => exact h
    | succ n =>
      apply Option.decidable_eq_none.byContradiction
      intro contra
      have no_holes := tree.no_holes_in_children node (n+1)
      unfold children at no_holes
      unfold InfiniteTreeSkeleton.children at no_holes
      specialize no_holes contra ⟨0, by simp⟩
      contradiction

  theorem getElem_children_eq_get_tree (tree : PossiblyInfiniteTree α) (node : List Nat) (index : Nat) : (tree.children node).infinite_list index = tree.get (index :: node) := by
    unfold children
    unfold get
    unfold InfiniteTreeSkeleton.children
    simp

  def branches_through (tree : PossiblyInfiniteTree α) (node : List Nat) : Set (PossiblyInfiniteList α) := fun pil =>
    pil.infinite_list ∈ tree.infinite_tree.branches_through node

  def branches (tree : PossiblyInfiniteTree α) : Set (PossiblyInfiniteList α) := fun pil =>
    pil.infinite_list ∈ tree.infinite_tree.branches

  theorem branches_through_eq_union_children (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.branches_through node = fun b => ∃ (i : Nat), b ∈ tree.branches_through (i :: node) := by
    unfold branches_through
    apply funext
    simp
    intro pil
    rw [tree.infinite_tree.branches_through_eq_union_children]
    constructor
    . intro h
      rcases h with ⟨i, h⟩
      exists i
    . intro h
      rcases h with ⟨i, h⟩
      exists i

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

  theorem first_child_none_means_children_empty (tree : FiniteDegreeTree α) (node : List Nat) : tree.get (0::node) = none -> tree.children node = [] := by
    intro h
    have lifted_children_none := tree.tree.first_child_none_means_children_empty node h
    unfold children
    unfold children.loop
    split
    case h_1 _ => rfl
    case h_2 heq => rw [lifted_children_none] at heq; simp [PossiblyInfiniteList.empty] at heq

  theorem getElem_children_eq_loop_at_index (tree : FiniteDegreeTree α) (node : List Nat) (index : Nat) : ∀ c, (children.loop tree node c)[index]? = (children.loop tree node (index + c))[0]? := by
    induction index with
    | zero => simp
    | succ index ih =>
      intro c
      conv => left; unfold children.loop
      split
      case h_1 heq =>
        unfold children.loop
        have : (tree.tree.children node).infinite_list (index + 1 + c) = none := by
          apply Option.decidable_eq_none.byContradiction
          intro contra
          let m : Fin (index + 1 + c) := ⟨c, by simp⟩
          apply (tree.tree.children node).no_holes (index + 1 + c) contra m
          simp [m]
          exact heq
        simp
        rw [this]
      case h_2 heq =>
        simp
        rw [ih]
        rw [Nat.add_assoc, Nat.add_comm c 1]

  theorem getElem_children_eq_getElem_tree_children (tree : FiniteDegreeTree α) (node : List Nat) (index : Nat) : (tree.children node)[index]? = (tree.tree.children node).infinite_list index := by
    unfold children
    rw [getElem_children_eq_loop_at_index]
    simp
    unfold children.loop
    split
    case h_1 heq => rw [heq]; simp
    case h_2 heq => simp; rw [heq]

  theorem getElem_children_eq_get_tree (tree : FiniteDegreeTree α) (node : List Nat) (index : Fin (tree.children node).length) : (tree.children node)[index.val] = tree.get (index.val :: node) := by
    unfold get
    rw [← List.getElem?_eq_getElem]
    rw [getElem_children_eq_getElem_tree_children]
    apply PossiblyInfiniteTree.getElem_children_eq_get_tree

  theorem children_eq_lifted_children (tree : FiniteDegreeTree α) (node : List Nat) : PossiblyInfiniteList.fromList (tree.children node) = tree.tree.children node := by
    rw [PossiblyInfiniteList.eq_iff_same_on_all_indices]
    intro n
    rw [PossiblyInfiniteList.get_fromList_eq_list_getElem]
    apply getElem_children_eq_getElem_tree_children

  def branches_through (tree : FiniteDegreeTree α) (node : List Nat) : Set (PossiblyInfiniteList α) := tree.tree.branches_through node

  def branches (tree : FiniteDegreeTree α) : Set (PossiblyInfiniteList α) := tree.tree.branches

  theorem branches_through_eq_union_children (tree : FiniteDegreeTree α) (node : List Nat) : tree.branches_through node = fun b => ∃ (i : Nat), b ∈ tree.branches_through (i :: node) := by
    unfold branches_through
    rw [tree.tree.branches_through_eq_union_children]

  def leaves (tree : FiniteDegreeTree α) : Set α := tree.tree.leaves

  theorem branches_through_finite_of_none (tree : FiniteDegreeTree α) (node : List Nat) : tree.get node = none -> (tree.branches_through node).finite := by
    intro is_none
    let branch_for_node : PossiblyInfiniteList α := ⟨fun n => if n ≤ node.length then tree.get (node.drop (node.length - n)) else none, by
      intro n not_none
      cases Decidable.em (n ≤ node.length) with
      | inr lt => simp [lt] at not_none
      | inl le =>
        simp [le] at not_none
        intro m
        have m_le : m ≤ node.length := by apply Nat.le_trans; apply Nat.le_of_lt m.isLt; exact le
        simp [m_le]
        have no_orphans := tree.tree.no_orphans (node.drop (node.length - n)) not_none ⟨(node.drop (node.length - m)), by
          exists (node.drop (node.length - n)).take (n - m)
          rw [List.take_drop]
          have : node.length - n + (n - m.val) = node.length - m.val := by
            rw [← Nat.add_sub_assoc (by apply Nat.le_of_lt; exact m.isLt)]
            rw [← Nat.sub_add_comm le]
            simp
          rw [this]
          rw [← List.drop_append_of_le_length (by rw [List.length_take_of_le (by simp), Nat.sub_le_sub_iff_left m_le]; apply Nat.le_of_lt; exact m.isLt)]
          simp
        ⟩
        exact no_orphans
    ⟩
    exists [branch_for_node]
    constructor
    . simp
    . intro e
      constructor
      . intro h
        simp at h
        rw [h]
        let nodes : InfiniteList Nat := fun n => if lt : n < node.length then node[node.length - (n+1)] else (tree.children node).length
        have : ∀ n, n ≤ node.length -> (nodes.take n).reverse = node.drop (node.length - n) := by
          intro n
          induction n with
          | zero => simp [InfiniteList.take]
          | succ n ih =>
            intro le
            unfold InfiniteList.take
            simp
            rw [ih (by apply Nat.le_of_succ_le le)]
            unfold nodes
            have lt : n < node.length := by apply Nat.lt_of_succ_le le
            simp [lt]
            conv => right; rw [List.drop_eq_getElem_cons (by apply Nat.sub_lt_self; simp; exact le)]
            have : node.length - (n + 1) + 1 = node.length - n := by omega
            rw [this]
        exists nodes
        constructor
        . intro n
          cases Decidable.em (n ≤ node.length) with
          | inl le =>
            rw [this n le]
            simp [le]
            rfl
          | inr lt =>
            simp [lt]
            have no_orphans := tree.tree.no_orphans (nodes.take n).reverse
            apply Eq.symm
            apply Option.decidable_eq_none.byContradiction
            intro contra
            specialize no_orphans contra ⟨node, by
              exists ((nodes.skip (node.length)).take (n - node.length)).reverse
              have : node = (nodes.take (node.length)).reverse := by
                rw [this node.length]
                . simp
                . simp
              conv => left; right; rw [this]
              rw [← List.reverse_append]
              rw [InfiniteList.combine_skip_take nodes n ⟨node.length, by apply Nat.lt_of_not_le; exact lt⟩]
            ⟩
            apply no_orphans
            exact is_none
        . rw [this]
          . simp
          . simp
      . intro h
        rcases h with ⟨nodes, h⟩
        simp
        rw [PossiblyInfiniteList.eq_iff_same_on_all_indices]
        intro n
        rw [h.left]
        unfold branch_for_node
        simp
        cases Decidable.em (n ≤ node.length) with
        | inl le =>
          simp [le]
          have : (nodes.take n).reverse = node.drop (node.length - n) := by
            conv => right; right; rw [← h.right]
            rw [List.drop_reverse]
            rw [InfiniteList.length_take]
            rw [InfiniteList.take_after_take]
            rw [Nat.sub_sub_self le]
            simp [Nat.min_eq_right le]
          rw [this]
          rfl
        | inr lt =>
          simp [lt]

          have no_orphans := tree.tree.no_orphans (nodes.take n).reverse
          apply Option.decidable_eq_none.byContradiction
          intro contra
          specialize no_orphans contra ⟨node, by
            exists ((nodes.skip (node.length)).take (n - node.length)).reverse
            conv => left; right; rw [← h.right]
            rw [← List.reverse_append]
            rw [InfiniteList.combine_skip_take nodes n ⟨node.length, by apply Nat.lt_of_not_le; exact lt⟩]
          ⟩
          apply no_orphans
          exact is_none

  theorem branches_through_finite_of_branches_through_children_finite (tree : FiniteDegreeTree α) (node : List Nat) : (∀ i, (tree.branches_through (i :: node)).finite) -> (tree.branches_through node).finite := by
    intro h
    have dec := Classical.typeDecidableEq (PossiblyInfiniteList α)
    let branch_for_node : PossiblyInfiniteList α := ⟨fun n => if n ≤ node.length then tree.get (node.drop (node.length - n)) else none, by
      intro n not_none
      cases Decidable.em (n ≤ node.length) with
      | inr lt => simp [lt] at not_none
      | inl le =>
        simp [le] at not_none
        intro m
        have m_le : m ≤ node.length := by apply Nat.le_trans; apply Nat.le_of_lt m.isLt; exact le
        simp [m_le]
        have no_orphans := tree.tree.no_orphans (node.drop (node.length - n)) not_none ⟨(node.drop (node.length - m)), by
          exists (node.drop (node.length - n)).take (n - m)
          rw [List.take_drop]
          have : node.length - n + (n - m.val) = node.length - m.val := by
            rw [← Nat.add_sub_assoc (by apply Nat.le_of_lt; exact m.isLt)]
            rw [← Nat.sub_add_comm le]
            simp
          rw [this]
          rw [← List.drop_append_of_le_length (by rw [List.length_take_of_le (by simp), Nat.sub_le_sub_iff_left m_le]; apply Nat.le_of_lt; exact m.isLt)]
          simp
        ⟩
        exact no_orphans
    ⟩
    let branches_for_i (i : Nat) := Classical.choose (h i)
    let target_list : List (PossiblyInfiniteList α) := (branch_for_node :: ((tree.children node).enum_with_lt.map (fun (i, _) => branches_for_i i.val)).flatten).eraseDupsKeepRight
    exists target_list
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro branch
      unfold target_list
      rw [List.mem_eraseDupsKeepRight_iff]
      simp
      constructor
      . intro pre
        cases pre with
        | inl eq =>
          let nodes : InfiniteList Nat := fun n => if lt : n < node.length then node[node.length - (n+1)] else (tree.children node).length
          have : ∀ n, n ≤ node.length -> (nodes.take n).reverse = node.drop (node.length - n) := by
            intro n
            induction n with
            | zero => simp [InfiniteList.take]
            | succ n ih =>
              intro le
              unfold InfiniteList.take
              simp
              rw [ih (by apply Nat.le_of_succ_le le)]
              unfold nodes
              have lt : n < node.length := by apply Nat.lt_of_succ_le le
              simp [lt]
              conv => right; rw [List.drop_eq_getElem_cons (by apply Nat.sub_lt_self; simp; exact le)]
              have : node.length - (n + 1) + 1 = node.length - n := by omega
              rw [this]
          exists nodes
          constructor
          . rw [eq]
            intro n
            cases Decidable.em (n ≤ node.length) with
            | inl le =>
              rw [this n le]
              simp [le]
              rfl
            | inr lt =>
              simp [lt]
              have : tree.tree.infinite_tree (nodes.take (node.length + 1)).reverse = none := by
                have child_none : (tree.children node)[nodes node.length]? = none := by
                  apply List.getElem?_eq_none
                  unfold nodes
                  simp
                rw [getElem_children_eq_getElem_tree_children, PossiblyInfiniteTree.getElem_children_eq_get_tree] at child_none
                unfold PossiblyInfiniteTree.get at child_none
                unfold InfiniteList.take
                simp
                rw [this]
                . simp
                  exact child_none
                . simp
              have le : node.length + 1 ≤ n := by apply Nat.succ_le_of_lt; apply Nat.lt_of_not_ge; exact lt
              cases Nat.eq_or_lt_of_le le with
              | inl eq => rw [← eq, this]
              | inr lt =>
                have no_orphans := tree.tree.no_orphans (nodes.take n).reverse
                apply Eq.symm
                apply Option.decidable_eq_none.byContradiction
                intro contra
                specialize no_orphans contra ⟨(nodes.take (node.length + 1)).reverse, by
                  exists ((nodes.skip (node.length + 1)).take (n - (node.length + 1))).reverse
                  rw [← List.reverse_append]
                  rw [InfiniteList.combine_skip_take nodes n ⟨node.length + 1, lt⟩]
                ⟩
                apply no_orphans
                exact this
          . rw [this]
            . simp
            . simp
        | inr pre =>
          rcases pre with ⟨branches, ex_i, branch_mem⟩
          rcases ex_i with ⟨i, _, eq⟩
          rw [branches_through_eq_union_children]
          exists i.val
          have spec := Classical.choose_spec (h i.val)
          rw [← spec.right]
          unfold branches_for_i at eq
          rw [eq]
          exact branch_mem
      . intro pre
        rw [branches_through_eq_union_children] at pre
        rcases pre with ⟨i, pre⟩
        cases Decidable.em (i < (tree.children node).length) with
        | inl lt =>
          apply Or.inr
          exists branches_for_i i
          constructor
          . let i_fin : Fin (tree.children node).length := ⟨i, lt⟩
            exists i_fin
            constructor
            . exists (tree.children node)[i_fin]
              rw [List.mem_enum_with_lt_iff_mem_enum]
              rw [List.mem_enum_iff_getElem?]
              simp
            . rfl
          . have spec := Classical.choose_spec (h i)
            unfold branches_for_i
            rw [spec.right]
            exact pre
        | inr not_lt =>
          apply Or.inl
          rcases pre with ⟨nodes, pre⟩
          unfold branch_for_node
          rw [PossiblyInfiniteList.eq_iff_same_on_all_indices]
          intro n
          rw [pre.left n]
          have pre_r := pre.right
          simp [InfiniteList.take] at pre_r
          simp
          cases Decidable.em (n ≤ node.length) with
          | inl le =>
            simp [le]
            have : (nodes.take n).reverse = node.drop (node.length - n) := by
              conv => right; right; rw [← pre_r.right]
              rw [List.drop_reverse]
              rw [InfiniteList.length_take]
              rw [InfiniteList.take_after_take]
              rw [Nat.sub_sub_self le]
              simp [Nat.min_eq_right le]
            rw [this]
            rfl
          | inr lt =>
            simp [lt]
            have : tree.tree.infinite_tree (nodes.take (node.length + 1)).reverse = none := by
              have : (tree.children node)[nodes node.length]? = none := by
                apply List.getElem?_eq_none
                rw [pre_r.left]
                apply Nat.le_of_not_gt
                exact not_lt
              rw [getElem_children_eq_getElem_tree_children, PossiblyInfiniteTree.getElem_children_eq_get_tree] at this
              unfold PossiblyInfiniteTree.get at this
              unfold InfiniteList.take
              simp
              rw [pre_r.right]
              exact this
            have le : node.length + 1 ≤ n := by apply Nat.succ_le_of_lt; apply Nat.lt_of_not_ge; exact lt
            cases Nat.eq_or_lt_of_le le with
            | inl eq => rw [← eq]; exact this
            | inr lt =>
              have no_orphans := tree.tree.no_orphans (nodes.take n).reverse
              apply Option.decidable_eq_none.byContradiction
              intro contra
              specialize no_orphans contra ⟨(nodes.take (node.length + 1)).reverse, by
                exists ((nodes.skip (node.length + 1)).take (n - (node.length + 1))).reverse
                rw [← List.reverse_append]
                rw [InfiniteList.combine_skip_take nodes n ⟨node.length + 1, lt⟩]
              ⟩
              apply no_orphans
              exact this

  noncomputable def infinite_branching_node_for_depth_of_branches_infinite (tree : FiniteDegreeTree α) (not_finite : ¬ tree.branches.finite) : (depth : Nat) -> { node : List Nat // node.length = depth ∧ ¬ (tree.branches_through node).finite }
  | .zero => ⟨[], by constructor; rfl; exact not_finite⟩
  | .succ depth =>
    let prev_res := infinite_branching_node_for_depth_of_branches_infinite tree not_finite depth
    let prev_node := prev_res.val
    let length_eq := prev_res.property.left
    let not_finite := prev_res.property.right
    have : ¬ ∀ i, (tree.branches_through (i :: prev_node)).finite := by
      intro contra
      apply not_finite
      apply branches_through_finite_of_branches_through_children_finite
      exact contra
    have : ∃ i, ¬ (tree.branches_through (i :: prev_node)).finite := by simp at this; exact this
    let i := Classical.choose this
    let i_spec := Classical.choose_spec this

    ⟨i :: prev_node, by
      constructor
      . simp; exact length_eq
      . exact i_spec
    ⟩

  theorem infinite_branching_node_extends_previous (tree : FiniteDegreeTree α) (not_finite : ¬ tree.branches.finite) (depth : Nat) : (infinite_branching_node_for_depth_of_branches_infinite tree not_finite depth.succ).val = (infinite_branching_node_for_depth_of_branches_infinite tree not_finite depth.succ).val.head (by simp [infinite_branching_node_for_depth_of_branches_infinite]) :: (infinite_branching_node_for_depth_of_branches_infinite tree not_finite depth).val := by
    simp [infinite_branching_node_for_depth_of_branches_infinite]

  theorem branches_finite_of_each_finite (tree : FiniteDegreeTree α) : (∀ branch, branch ∈ tree.branches -> ∃ i, branch.infinite_list i = none) -> tree.branches.finite := by
    intro h

    apply Classical.byContradiction
    intro contra
    simp at contra

    have : ∃ (nodes : InfiniteList Nat), ∀ (i : Nat), ¬ (tree.branches_through (nodes.take i).reverse).finite := by
      let nodes : InfiniteList Nat := fun n => (infinite_branching_node_for_depth_of_branches_infinite tree contra n.succ).val.head (by
        simp [infinite_branching_node_for_depth_of_branches_infinite]
      )
      have : ∀ i, (nodes.take i).reverse = (infinite_branching_node_for_depth_of_branches_infinite tree contra i).val := by
        intro i
        induction i with
        | zero => simp [InfiniteList.take, infinite_branching_node_for_depth_of_branches_infinite]
        | succ i ih =>
          unfold InfiniteList.take
          unfold nodes
          simp
          rw [ih]
          conv => right; rw [infinite_branching_node_extends_previous]
      exists nodes
      intro i
      rw [this]
      have prop := (infinite_branching_node_for_depth_of_branches_infinite tree contra i).property
      exact prop.right

    rcases this with ⟨nodes, all_infinite⟩

    let branch : PossiblyInfiniteList α := ⟨fun n => tree.get (nodes.take n).reverse, by
      intro n not_none m contra
      apply all_infinite m.val
      apply branches_through_finite_of_none
      exact contra
    ⟩

    specialize h branch (by
      exists nodes
      constructor
      . intro n
        rfl
      . rfl
    )

    rcases h with ⟨i, hi⟩
    apply all_infinite i
    apply branches_through_finite_of_none
    exact hi
end FiniteDegreeTree

