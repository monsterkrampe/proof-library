import ProofLibrary.Option
import ProofLibrary.List
import ProofLibrary.PossiblyInfiniteList

structure NodeInformation (α) where
  value : α
  number_of_children : Nat

structure PossiblyInfiniteTree (α : Type u) where
  data : PossiblyInfiniteList (List (NodeInformation α))
  consistency : ∀ depth : Nat, match (data.infinite_list depth) with
    | none => True
    | some list => match (list.map (fun ni => ni.number_of_children)).sum with
      | Nat.zero => (data.infinite_list (depth + 1)) = none
      | Nat.succ n => (data.infinite_list (depth + 1)) = some next_layer ∧ next_layer.length = Nat.succ n

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

  /-
  def children (node : NodeInPossiblyInfiniteTree α) : List (NodeInPossiblyInfiniteTree α) :=
    let current_layer := node.layer
    let next_layer_opt := node.tree.data.infinite_list (node.depth + 1)
    let current_layer_before_this := current_layer.before_index node.position_in_layer
    let node_info := node.node_info
    let number_of_children := node_info.number_of_children
    let layer_mapped := current_layer.map (fun ni => ni.number_of_children)

    have no_children_in_mapped_layer : number_of_children ∈ layer_mapped.toSet := by
      apply List.mappedElemInMappedList
      apply nodeInfoIsInLayer

    have no_children_le_sum_layer_mapped : number_of_children ≤ layer_mapped.sum := by
      apply List.everyElementLeSum
      exact no_children_in_mapped_layer

    match equality : number_of_children with
      | Nat.zero => List.nil
      | Nat.succ n =>
        have consistency := node.tree.consistency node.depth
        -- TODO: continue here
        have something := by
          simp [nodeLayerIsLayerAtDepth] at consistency

        sorry
  -/

  /- TODO: maybe also define siblings similarly, i.e. as node.layer but with NodeInPossiblyInfiniteTree instead of just NodeInformation -/
end NodeInPossiblyInfiniteTree
