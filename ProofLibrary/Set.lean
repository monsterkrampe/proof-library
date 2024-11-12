-- TODO: maybe use mathlib set instead of defining this ourselves

def Set (α) := α -> Prop

namespace Set
  def emptyset : Set α := fun _ => False
  notation:max "∅" => emptyset

  def element (e : α) (X : Set α) : Prop := X e
  infixr:75 " ∈ " => element

  theorem element_mapping_preserves_membership (e : α) (X : Set α) (f : α -> α) : e ∈ X -> f e ∈ (fun e' => ∃ e'', X e'' ∧ e' = f e'') := by
    intro helem
    exists e

  def finite (X : Set α) : Prop := ∃ (l : List α), ∀ (e : α), e ∈ l ↔ e ∈ X

  def union (X Y : Set α) : Set α := fun e => e ∈ X ∨ e ∈ Y
  infixr:65 " ∪ " => union

  def subset (X Y : Set α) : Prop := ∀ e : α, e ∈ X -> e ∈ Y
  infixr:50 " ⊆ " => subset

  theorem subsetOfSelf (X : Set α) : X ⊆ X := by
    intros _ h
    exact h

  theorem subsetTransitive (a b c : Set α) : a ⊆ b ∧ b ⊆ c -> a ⊆ c := by
    intro ⟨ha, hb⟩
    intro e he
    apply hb
    apply ha
    assumption

  theorem subsetUnionSomethingStillSubset (a b c : Set α) : a ⊆ b -> a ⊆ b ∪ c := by
    intro aSubB e eInA
    apply Or.inl
    apply aSubB
    exact eInA

  theorem subsetUnionSomethingStillSubset' (a b c : Set α) : a ⊆ c -> a ⊆ b ∪ c := by
    intro aSubC e eInA
    apply Or.inr
    apply aSubC
    exact eInA

  theorem unionSubsetEachSubset (a b c : Set α) : a ∪ b ⊆ c ↔ a ⊆ c ∧ b ⊆ c := by
    constructor
    -- mp
    intro h
    simp [union, subset] at h
    simp [subset]
    constructor
    -- left
    intro e hl
    apply h
    simp [element]
    apply Or.inl
    exact hl
    -- right
    intro e hr
    apply h
    simp [element]
    apply Or.inr
    exact hr
    -- mpr
    intro ⟨ha, hb⟩
    unfold Set.union
    unfold Set.subset
    intro e
    unfold Set.element
    simp
    intro h
    cases h
    -- inl
    apply ha
    assumption
    -- inr
    apply hb
    assumption
end Set
