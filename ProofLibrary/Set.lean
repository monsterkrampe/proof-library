-- TODO: maybe use mathlib set instead of defining this ourselves

def Set (α) := α -> Prop

namespace Set
  def emptyset : Set α := fun _ => False
  notation:max "∅" => emptyset

  def element (e : α) (X : Set α) : Prop := X e
  infixr:75 " ∈ " => element

  def union (X Y : Set α) : Set α := fun e => e ∈ X ∨ e ∈ Y
  infixr:65 " ∪ " => union

  def subset (X Y : Set α) : Prop := ∀ e : α, e ∈ X -> e ∈ Y
  infixr:50 " ⊆ " => subset

  theorem subsetOfSelf (X : Set α) : X ⊆ X := by
    intros _ h
    exact h

  theorem subsetUnionSomethingStillSubset (a b c : Set α) : a ⊆ b -> a ⊆ b ∪ c := by
    intro aSubB e eInA
    apply Or.inl
    apply aSubB
    exact eInA
end Set
