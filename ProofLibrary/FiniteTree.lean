-- NOTE: Inductive Trees are always finite!
import ProofLibrary.List

mutual
  inductive FiniteTree (α : Type u) (β : Type v) where
    | leaf : β -> FiniteTree α β
    | inner : α -> FiniteTreeList α β -> FiniteTree α β

  inductive FiniteTreeList (α : Type u) (β : Type v) where
    | nil  : FiniteTreeList α β
    | cons : FiniteTree α β -> FiniteTreeList α β -> FiniteTreeList α β
end

mutual
  def finiteTreeEq [DecidableEq α] [DecidableEq β] (a b : FiniteTree α β) : Decidable (a = b) :=
    match a with 
      | .leaf la => match b with 
        | .leaf lb => if eq_ls : la = lb 
          then isTrue (by simp [eq_ls]) 
          else isFalse (by 
            let unwrap := fun (x : FiniteTree α β) (hx : ∀ a b, x ≠ FiniteTree.inner a b) => match x with 
              | FiniteTree.leaf lx => lx
              | FiniteTree.inner a b => absurd rfl (hx a b)
            intro contra
            have : la = lb := by
              have ha : la = unwrap (FiniteTree.leaf la) (by intro _ _ contra; exact FiniteTree.noConfusion contra) := by rfl  
              have hb : lb = unwrap (FiniteTree.leaf lb) (by intro _ _ contra; exact FiniteTree.noConfusion contra) := by rfl  
              rw [ha, hb]
              simp [contra]
            contradiction
          )
        | .inner _ _ => isFalse (by intro contra; exact FiniteTree.noConfusion contra)
      | .inner la ca => match b with
        | .leaf lb => isFalse (by intro contra; exact FiniteTree.noConfusion contra)
        | .inner lb cb => if eq_ls : la = lb 
          then match finiteTreeListEq ca cb with
            | .isTrue p => isTrue (by simp [eq_ls, p])
            | .isFalse np => isFalse (by 
            let unwrap := fun (x : FiniteTree α β) (hx : ∀ a, x ≠ FiniteTree.leaf a) => match x with 
              | FiniteTree.leaf a => absurd rfl (hx a)
              | FiniteTree.inner _ b => b
            intro contra
            have : ca = cb := by
              have ha : ca = unwrap (FiniteTree.inner la ca) (by intro _ contra; exact FiniteTree.noConfusion contra) := by rfl  
              have hb : cb = unwrap (FiniteTree.inner lb cb) (by intro _ contra; exact FiniteTree.noConfusion contra) := by rfl  
              rw [ha, hb]
              simp [contra]
            contradiction
          )
          else isFalse (by 
            let unwrap := fun (x : FiniteTree α β) (hx : ∀ a, x ≠ FiniteTree.leaf a) => match x with 
              | FiniteTree.leaf a => absurd rfl (hx a)
              | FiniteTree.inner a _ => a
            intro contra
            have : la = lb := by
              have ha : la = unwrap (FiniteTree.inner la ca) (by intro _ contra; exact FiniteTree.noConfusion contra) := by rfl  
              have hb : lb = unwrap (FiniteTree.inner lb cb) (by intro _ contra; exact FiniteTree.noConfusion contra) := by rfl  
              rw [ha, hb]
              simp [contra]
            contradiction
          )

  def finiteTreeListEq [DecidableEq α] [DecidableEq β] (a b : FiniteTreeList α β) : Decidable (a = b) :=
    match a with 
      | .nil => match b with 
        | .nil => isTrue (by rfl)
        | .cons _ _ => isFalse (by intro contra; exact FiniteTreeList.noConfusion contra)
      | .cons ta la => match b with 
        | .nil => isFalse (by intro contra; exact FiniteTreeList.noConfusion contra)
        | .cons tb lb => match finiteTreeEq ta tb with 
          | .isTrue tp => match finiteTreeListEq la lb with 
            | .isTrue lp => isTrue (by simp [tp, lp])
            | .isFalse lnp => isFalse (by 
              let unwrap := fun (x : FiniteTreeList α β) (hx : x ≠ FiniteTreeList.nil) => match x with 
                | FiniteTreeList.nil => absurd rfl hx
                | FiniteTreeList.cons _ b => b
              intro contra
              have : la = lb := by
                have ha : la = unwrap (FiniteTreeList.cons ta la) (by intro contra; exact FiniteTreeList.noConfusion contra) := by rfl
                have hb : lb = unwrap (FiniteTreeList.cons tb lb) (by intro contra; exact FiniteTreeList.noConfusion contra) := by rfl
                rw [ha, hb]
                simp [contra]
              contradiction
            )
          | .isFalse tnp => isFalse (by
            let unwrap := fun (x : FiniteTreeList α β) (hx : x ≠ FiniteTreeList.nil) => match x with 
              | FiniteTreeList.nil => absurd rfl hx
              | FiniteTreeList.cons a _ => a
            intro contra
            have : ta = tb := by
              have ha : ta = unwrap (FiniteTreeList.cons ta la) (by intro contra; exact FiniteTreeList.noConfusion contra) := by rfl
              have hb : tb = unwrap (FiniteTreeList.cons tb lb) (by intro contra; exact FiniteTreeList.noConfusion contra) := by rfl
              rw [ha, hb]
              simp [contra]
            contradiction
          )
end

instance [DecidableEq α] [DecidableEq β] (a b : FiniteTree α β) : Decidable (a = b) := finiteTreeEq a b
instance [DecidableEq α] [DecidableEq β] (a b : FiniteTreeList α β) : Decidable (a = b) := finiteTreeListEq a b

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

  theorem eqIffFromListEq (as bs : List (FiniteTree α β)) : as = bs ↔ fromList as = fromList bs := by 
    induction as generalizing bs with 
    | nil => cases bs; constructor; intros; rfl; intros; rfl; constructor; intros; contradiction; intros; contradiction
    | cons a as ih => 
      cases bs with 
      | nil => constructor; intros; contradiction; intros; contradiction
      | cons b bs => 
        constructor
        intro h
        injection h with head tail
        simp [fromList]
        constructor; exact head; rw [← ih]; exact tail
        intro h 
        simp [fromList] at h
        simp [h.left]
        rw [ih]
        exact h.right

  theorem toListFromListIsId (as : FiniteTreeList α β) : FiniteTreeList.fromList as.toList = as := by 
    cases as with 
    | nil => simp [toList, fromList]
    | cons a as => simp [toList, fromList]; apply toListFromListIsId

  theorem fromListToListIsId (as : List (FiniteTree α β)) : (FiniteTreeList.fromList as).toList = as := by 
    induction as with 
    | nil => simp [toList, fromList]
    | cons a as ih => simp [toList, fromList]; apply ih

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

  -- TODO: should we remove this? I think we do not need this anymore...
  mutual
    theorem mapLeavesEqIfMapEqOnLeaves (f : β -> FiniteTree α γ) (g : β -> FiniteTree α γ) (t : FiniteTree α β) : t.leaves.map f = t.leaves.map g -> t.mapLeaves f = t.mapLeaves g := by 
      cases t with 
      | leaf _ => unfold mapLeaves; unfold leaves; simp [List.map]; intros; assumption
      | inner _ _ => 
        unfold mapLeaves; unfold leaves; simp
        apply mapLeavesListEqIfMapEqOnLeavesList

    theorem mapLeavesListEqIfMapEqOnLeavesList (f : β -> FiniteTree α γ) (g : β -> FiniteTree α γ) (ts : FiniteTreeList α β) : (leavesList ts).map f = (leavesList ts).map g -> mapLeavesList f ts = mapLeavesList g ts := by 
      cases ts with 
      | nil => unfold mapLeavesList; unfold leavesList; simp [List.map]
      | cons t ts => 
        unfold mapLeavesList; unfold leavesList
        intro h
        have h : t.leaves.map f = t.leaves.map g ∧ (leavesList ts).map f = (leavesList ts).map g := by 
          apply List.concatEqMeansPartsEqIfSameLength
          . simp [List.length_map]
          . rw [List.mapConcatEqMapParts] at h
            rw [List.mapConcatEqMapParts] at h
            exact h
        have : t.mapLeaves f = t.mapLeaves g := by 
          apply mapLeavesEqIfMapEqOnLeaves
          apply h.left
        rw [this]
        have : mapLeavesList f ts = mapLeavesList g ts := by 
          apply mapLeavesListEqIfMapEqOnLeavesList
          apply h.right
        rw [this]
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

  mutual 
    theorem tree_eq_while_contained_is_impossible [DecidableEq α] [DecidableEq β] (t : FiniteTree α β) (ts : FiniteTreeList α β) (a : α) (h_eq : FiniteTree.inner a ts = t) (h_contains : ts.toList.elem t) : False := by 
      cases t with 
      | leaf _ => contradiction
      | inner label children =>
        injection h_eq with _ children_eq
        apply treelist_eq_while_contained_is_impossible children ts
        rw [← children_eq]
        intros 
        assumption
        apply h_contains

    theorem treelist_eq_while_contained_is_impossible [DecidableEq α] [DecidableEq β] (children ts : FiniteTreeList α β) (label : α) (ts_subset_children : ∀ t, ts.toList.elem t -> children.toList.elem t) (h_contains : ts.toList.elem (FiniteTree.inner label children)) : False := by 
      cases ts with 
      | nil => contradiction
      | cons t ts =>
        simp [FiniteTreeList.toList, List.elem] at h_contains
        split at h_contains
        case h_1 _ beq => 
          have eq := LawfulBEq.eq_of_beq beq
          apply tree_eq_while_contained_is_impossible t children
          apply eq
          apply ts_subset_children
          simp [FiniteTreeList.toList, List.elem]
        case h_2 _ _ => 
          apply treelist_eq_while_contained_is_impossible children ts
          intro any_t t_elem_ts
          apply ts_subset_children
          simp [FiniteTreeList.toList, List.elem, t_elem_ts]
          split; rfl; rfl
          apply h_contains
  end
end FiniteTree
