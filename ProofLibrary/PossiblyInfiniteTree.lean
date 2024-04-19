import ProofLibrary.Option
import ProofLibrary.List
import ProofLibrary.PossiblyInfiniteList
import Std.Data.List.Lemmas

structure NodeInformation (α) where
  value : α
  number_of_children : Nat

structure PossiblyInfiniteTree (α : Type u) where
  data : PossiblyInfiniteList (List (NodeInformation α))
  consistency : ∀ depth : Nat, match (data.infinite_list depth) with
    | none => True
    | some list => match (list.map (fun ni => ni.number_of_children)).sum with
      | Nat.zero => (data.infinite_list (depth + 1)) = none
      | Nat.succ n => ∃ next_layer, (data.infinite_list (depth + 1)) = some next_layer ∧ next_layer.length = Nat.succ n

structure NodeInPossiblyInfiniteTree (α) where
  tree : PossiblyInfiniteTree α
  depth : Nat
  position_in_layer : Nat
  layer_exists : ∃ layer, tree.data.infinite_list depth = some layer
  layer_large_enough : ∀ layer, tree.data.infinite_list depth = some layer -> position_in_layer < layer.length

namespace NodeInPossiblyInfiniteTree
  def layer (node : NodeInPossiblyInfiniteTree α) : List (NodeInformation α) :=
    let layer_opt := node.tree.data.infinite_list node.depth
    let layer := layer_opt.unwrap (by
      cases node.layer_exists with | intro x h =>
        exact layer_opt.someNotNone h
    )
    layer

  theorem nodeLayerIsLayerAtDepth (node : NodeInPossiblyInfiniteTree α) : node.tree.data.infinite_list node.depth = some node.layer := by
    cases node.layer_exists with | intro x h =>
      simp [layer]
      rw [Option.someRevertsUnwrap]

  def node_info (node : NodeInPossiblyInfiniteTree α) : NodeInformation α :=
    let layer := node.layer
    layer.get ⟨node.position_in_layer, (by
      have h := node.layer_large_enough layer
      apply h
      rw [nodeLayerIsLayerAtDepth]
    )⟩

  theorem nodeInfoIsInLayer (node : NodeInPossiblyInfiniteTree α) : node.node_info ∈ node.layer.toSet := by
    simp [node_info]
    apply List.listGetInToSet

  def children (node : NodeInPossiblyInfiniteTree α) : List (NodeInPossiblyInfiniteTree α) :=
    let current_layer := node.layer
    let next_layer_opt := node.tree.data.infinite_list (node.depth + 1)
    let current_layer_before_this := current_layer.before_index node.position_in_layer
    let node_info := node.node_info
    let number_of_children := node_info.number_of_children
    let layer_mapped := current_layer.map (fun ni => ni.number_of_children)
    let number_of_children_before := (current_layer_before_this.map (fun ni => ni.number_of_children)).sum

    have no_children_in_mapped_layer : number_of_children ∈ layer_mapped.toSet := by
      apply List.mappedElemInMappedList
      apply nodeInfoIsInLayer

    have no_children_le_sum_layer_mapped : number_of_children ≤ layer_mapped.sum := by
      apply List.everyElementLeSum
      exact no_children_in_mapped_layer

    have no_c_before_add_no_c_le_layer_length : number_of_children_before + number_of_children ≤ layer_mapped.sum := by
      sorry

    match equality_noc : node_info.number_of_children with
      | Nat.zero => List.nil
      | Nat.succ n =>
        let sumNeZero : layer_mapped.sum ≠ 0 := by
          apply Nat.not_eq_zero_of_lt
          apply Nat.lt_of_lt_of_le
          apply Nat.zero_lt_of_ne_zero
          exact Nat.succ_ne_zero n
          rw [←equality_noc]
          exact no_children_le_sum_layer_mapped

        match equality_sum : layer_mapped.sum with
          | Nat.zero => absurd equality_sum sumNeZero
          | Nat.succ m =>
            let consistency := node.tree.consistency node.depth
            have nextLayerExists : next_layer_opt ≠ none := by
              simp [nodeLayerIsLayerAtDepth] at consistency
              simp [equality_sum] at consistency
              cases consistency with | intro _ h =>
                have layer_exists := h.left
                exact Option.someNotNone layer_exists

            let next_layer := next_layer_opt.unwrap nextLayerExists
            let child_information := (next_layer.drop number_of_children_before).take number_of_children

            child_information.enum_with_lt.map (fun (indexWithLt, info) => {
              tree := node.tree,
              depth := node.depth + 1,
              position_in_layer := number_of_children_before + indexWithLt.index,
              layer_exists := by
                exists next_layer
                simp
                rw [Option.someRevertsUnwrap]
              layer_large_enough := by
                intro layer h
                have someNextEqSomeLayer : some next_layer = some layer := by simp [Option.someRevertsUnwrap, h]
                have nextEqLayer : next_layer = layer := Option.someEqImpliesEq someNextEqSomeLayer
                rw [← nextEqLayer]
                simp [nodeLayerIsLayerAtDepth] at consistency
                simp [equality_sum] at consistency
                cases consistency with | intro next_layer' h' =>
                  let ⟨exis, count⟩ := h'
                  rw [h, ← someNextEqSomeLayer] at exis
                  have nextEqNextPrime : next_layer = next_layer' := Option.someEqImpliesEq exis
                  rw [← nextEqNextPrime] at count
                  rw [count, ← equality_sum]
                  have indexLt := indexWithLt.lt
                  have child_info_length_le_no_children : child_information.length ≤ number_of_children := by apply List.length_take_le
                  -- TODO: continue here
                  sorry
            })

  /- TODO: maybe also define siblings similarly, i.e. as node.layer but with NodeInPossiblyInfiniteTree instead of just NodeInformation -/
end NodeInPossiblyInfiniteTree
