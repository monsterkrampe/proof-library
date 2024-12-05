import ProofLibrary.SubstitutionAndHomomorphismBasics

namespace Function

  def injective (f : α -> β) : Prop := ∀ a b, f a = f b -> a = b

  def surjective (f : α -> β) : Prop := ∀ b, ∃ a, f a = b

end Function

namespace GroundTermMapping

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  -- TODO: do we really need this?
  def injective (h : GroundTermMapping sig) (terms : Set (GroundTerm sig)) : Prop :=
    ∀ t t', (t ∈ terms ∧ t' ∈ terms) -> (h t = h t' -> t = t')

  -- TODO: do we really need this?
  def surjective (h : GroundTermMapping sig) (terms : Set (GroundTerm sig)) : Prop :=
    ∀ t', t' ∈ terms -> ∃ t, h t = t'

  def strong (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
    ∀ e, ¬ e ∈ A -> ¬ (h.applyFact e) ∈ B

  -- TODO: is this really usable?
  theorem surjective_of_injective_of_closed_on_list (h : GroundTermMapping sig) (terms : List (GroundTerm sig)) (inj : h.injective terms.toSet) (closed : ∀ (l : List _), ∀ t, t ∈ l -> h t ∈ l) : h.surjective terms.toSet := by
    induction terms with
    | nil => sorry
    | cons hd tl ih =>
      specialize ih (sorry)
      unfold surjective
      intro b b_mem
      rw [← List.inIffInToSet] at b_mem
      simp at b_mem
      cases b_mem with
      | inl b_mem => sorry
      | inr b_mem =>
        unfold surjective at ih
        rw [List.inIffInToSet] at b_mem
        specialize ih b b_mem
        exact ih

end GroundTermMapping

namespace FactSet

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def isWeakCore (fs : FactSet sig) : Prop :=
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs fs ∧ h.injective fs.terms

  def isStrongCore (fs : FactSet sig) : Prop :=
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs fs ∧ h.injective fs.terms ∧ h.surjective fs.terms

  theorem isStrongCore_of_isWeakCore_of_finite (fs : FactSet sig) (weakCore : fs.isWeakCore) (finite : fs.finite) : fs.isStrongCore := by
    rcases finite with ⟨l, finite⟩
    unfold isStrongCore
    intro h isHom
    specialize weakCore h isHom
    rcases weakCore with ⟨strong, injective⟩
    constructor
    . exact strong
    constructor
    . exact injective
    . intro b b_mem
      sorry

end FactSet

