-- NOTE: Inductive Trees are always finite!

mutual
  inductive FiniteTree (α : Type u) (β : Type v) where
    | leaf : β -> FiniteTree α β
    | inner : α -> FiniteTreeList α β -> FiniteTree α β

  inductive FiniteTreeList (α : Type u) (β : Type v) where
    | nil  : FiniteTreeList α β
    | cons : FiniteTree α β -> FiniteTreeList α β -> FiniteTreeList α β
end

namespace FiniteTreeList
  def toList : FiniteTreeList α β -> List (FiniteTree α β)
    | FiniteTreeList.nil => List.nil
    | FiniteTreeList.cons t ts => List.cons t (toList ts)

  def fromList : List (FiniteTree α β) -> FiniteTreeList α β
    | List.nil => FiniteTreeList.nil
    | List.cons t ts => FiniteTreeList.cons t (fromList ts)

  instance : Coe (FiniteTreeList α β) (List (FiniteTree α β)) where
    coe := toList

  instance : Coe (List (FiniteTree α β)) (FiniteTreeList α β) where
    coe := fromList
end FiniteTreeList

namespace FiniteTree
  mutual
    def depth : FiniteTree α β -> Nat
      | FiniteTree.leaf _ => 1
      | FiniteTree.inner _ ts => 1 + depthList ts

    def depthList : FiniteTreeList α β -> Nat
      | FiniteTreeList.nil => 0
      | FiniteTreeList.cons t ts => max (depth t) (depthList ts)
  end

  mutual
    def leaves : FiniteTree α β -> List β
      | FiniteTree.leaf b => List.cons b List.nil
      | FiniteTree.inner _ ts => leavesList ts

    def leavesList : FiniteTreeList α β -> List β
      | FiniteTreeList.nil => List.nil
      | FiniteTreeList.cons t ts => (leaves t) ++ (leavesList ts)
  end

  mutual
    def mapLeaves (f : β -> FiniteTree α γ) (t : FiniteTree α β) : FiniteTree α γ := match t with
      | FiniteTree.leaf b => f b
      | FiniteTree.inner a ts => FiniteTree.inner a (mapLeavesList f ts)

    def mapLeavesList (f : β -> FiniteTree α γ) (ts : FiniteTreeList α β) : FiniteTreeList α γ := match ts with
      | FiniteTreeList.nil => FiniteTreeList.nil
      | FiniteTreeList.cons t ts => FiniteTreeList.cons (mapLeaves f t) (mapLeavesList f ts)
  end

  def nodeLabel : FiniteTree α α -> α
    | FiniteTree.leaf a => a
    | FiniteTree.inner a _ => a

  -- check that f holds for each node in the tree
  mutual
    def forEach (t : FiniteTree α β) (f : (FiniteTree α β) -> Prop) : Prop :=
      match t with
        | FiniteTree.leaf _ => f t
        | FiniteTree.inner _ ts => (f t) ∧ (forEachList ts f)

    def forEachList (ts : FiniteTreeList α β) (f : (FiniteTree α β) -> Prop) : Prop :=
      match ts with
        | FiniteTreeList.nil => True
        | FiniteTreeList.cons t ts => (forEach t f) ∧ (forEachList ts f)
  end

  mutual
    def privateNodesInDepthK (t : FiniteTree α β) (depth : Nat) (currentDepth : Nat) : List (FiniteTree α β) :=
      ite (currentDepth > depth) [] (
        ite (currentDepth = depth) [t] (match t with
          | FiniteTree.leaf _ => [t]
          | FiniteTree.inner _ ts => privateNodesInDepthKList ts depth (currentDepth + 1)
        )
      )

    def privateNodesInDepthKList (ts : FiniteTreeList α β) (depth : Nat) (currentDepth : Nat) : List (FiniteTree α β) :=
      ite (currentDepth > depth) [] (
        ite (currentDepth = depth) ts.toList (match ts with
          | FiniteTreeList.nil => []
          | FiniteTreeList.cons t ts => (privateNodesInDepthK t depth currentDepth) ++ (privateNodesInDepthKList ts depth currentDepth)
        )
      )
  end

  def nodesInDepthK (t : FiniteTree α β) (depth : Nat) : List (FiniteTree α β) := t.privateNodesInDepthK depth 0
end FiniteTree
