import ProofLibrary.List
import ProofLibrary.KnowledgeBaseBasics

section Defs

  variable (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  abbrev GroundSubstitution := sig.V -> GroundTerm sig

  abbrev GroundTermMapping := GroundTerm sig -> GroundTerm sig

  class SubsTarget (α) (β) where
    apply : GroundSubstitution sig -> α -> β


end Defs


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundSubstitution
  def apply_var_or_const (σ : GroundSubstitution sig) : VarOrConst sig -> GroundTerm sig
    | .var v => σ v
    | .const c => GroundTerm.const c

  def apply_skolem_term (σ : GroundSubstitution sig) : SkolemTerm sig -> GroundTerm sig
    | .var v => σ v
    | .const c => GroundTerm.const c
    | .func fs frontier => FiniteTree.inner fs (FiniteTreeList.fromList (frontier.map (fun fv => σ fv)))

  def apply_atom (σ : GroundSubstitution sig) (ϕ : Atom sig) : Fact sig :=
    { predicate := ϕ.predicate, terms := List.map (apply_skolem_term σ) ϕ.terms }

  def apply_function_free_atom (σ : GroundSubstitution sig) (ϕ : FunctionFreeAtom sig) : Fact sig :=
    { predicate := ϕ.predicate, terms := List.map (apply_var_or_const σ) ϕ.terms }

  def apply_function_free_conj (σ : GroundSubstitution sig) (conj : FunctionFreeConjunction sig) : List (Fact sig) :=
    (List.map (apply_function_free_atom σ)) conj

  theorem apply_same_length (σ : GroundSubstitution sig) (a : Atom sig) : a.terms.length = (σ.apply_atom a).terms.length := by
    simp [apply_atom]

  theorem eq_under_subs_means_same_length (σ : GroundSubstitution sig) (a : Atom sig) (f : Fact sig) (h : σ.apply_atom a = f) : (a.terms.length = f.terms.length) := by
    rw [← h]
    simp [apply_atom]

  theorem eq_under_subs_means_term_is_eq (σ : GroundSubstitution sig) (a : Atom sig) (f : Fact sig) (idx : Fin a.terms.length) (h : σ.apply_atom a = f) : (σ.apply_skolem_term (a.terms.get idx) = f.terms.get { val := idx.val, isLt := (by rw [← eq_under_subs_means_same_length σ a f h]; exact idx.isLt) }) := by
    cases h
    simp [apply_atom]

  -- TODO: is the extra assumption with injectivity reasonable?
  theorem eq_under_subs_means_elements_are_preserved (σ : GroundSubstitution sig) (a : Atom sig) (f : Fact sig) (h : σ.apply_atom a = f) : ∀ t, (∀ s, s ∈ a.terms.toSet ∧ σ.apply_skolem_term t = σ.apply_skolem_term s -> t = s) -> ((σ.apply_skolem_term t) ∈ f.terms ↔ t ∈ a.terms) := by
    intro t ht
    rw [List.mem_iff_get]
    rw [List.mem_iff_get]
    constructor
    . intro ⟨i, hi⟩
      let j : Fin a.terms.length := ⟨i.val, (by rw [eq_under_subs_means_same_length σ a f h]; exact i.isLt)⟩
      exists j
      rw [← eq_under_subs_means_term_is_eq σ a f j h] at hi
      apply Eq.symm
      apply ht
      constructor
      . apply List.listGetInToSet
      . rw [hi]
    . intro ⟨i, hi⟩
      let j : Fin f.terms.length := ⟨i.val, (by rw [← eq_under_subs_means_same_length σ a f h]; exact i.isLt)⟩
      exists j
      rw [← eq_under_subs_means_term_is_eq σ a f i h]
      rw [hi]

  -- TODO: is the extra assumption with injectivity reasonable?
  theorem eq_under_subs_means_indices_of_elements_are_preserved (σ : GroundSubstitution sig) (a : Atom sig) (f : Fact sig) (h : σ.apply_atom a = f) (t : SkolemTerm sig) (ht : t ∈ a.terms) (hs : ∀ s, s ∈ a.terms.toSet ∧ σ.apply_skolem_term t = σ.apply_skolem_term s -> t = s) : (f.terms.idx_of (σ.apply_skolem_term t) (by rw [eq_under_subs_means_elements_are_preserved σ a f h t hs]; exact ht)).val = ((a.terms.idx_of t) ht).val := by
    have : f.terms = a.terms.map σ.apply_skolem_term := by rw [← h]; unfold apply_atom; simp
    rw [List.idx_of_eq_of_list_eq _ _ this _ _]
    apply Eq.symm
    apply List.idx_of_eq_under_map
    apply hs

end GroundSubstitution

instance : SubsTarget sig (SkolemTerm sig) (GroundTerm sig) where
  apply := GroundSubstitution.apply_skolem_term
-- instance : SubsTarget Term GroundTerm where
--   apply := GroundSubstitution.apply_term
instance : SubsTarget sig (Atom sig) (Fact sig) where
  apply := GroundSubstitution.apply_atom
instance : SubsTarget sig (FunctionFreeAtom sig) (Fact sig) where
  apply := GroundSubstitution.apply_function_free_atom
instance : SubsTarget sig (FunctionFreeConjunction sig) (List (Fact sig)) where
  apply := GroundSubstitution.apply_function_free_conj

namespace GroundTermMapping

  def isIdOnConstants (h : GroundTermMapping sig) : Prop :=
    ∀ (t : GroundTerm sig), match t with
      | GroundTerm.const _ => h t = t
      | _ => True

  def applyFact (h : GroundTermMapping sig) (f : Fact sig) : Fact sig :=
    { predicate := f.predicate, terms := List.map h f.terms }

  theorem applyFact_compose (g h : GroundTermMapping sig) : applyFact (h ∘ g) = (applyFact h) ∘ (applyFact g) := by
    apply funext
    intro t
    simp [applyFact]

  def applyFactSet (h : GroundTermMapping sig) (fs : FactSet sig) : FactSet sig :=
    fun f' : Fact sig => ∃ (f : Fact sig), (f ∈ fs) ∧ ((h.applyFact f) = f')

  theorem applyFactSet_compose (g h : GroundTermMapping sig) : applyFactSet (h ∘ g) = (applyFactSet h) ∘ (applyFactSet g) := by
    apply funext
    intro fs
    apply funext
    intro f
    simp [applyFactSet, applyFact_compose]
    constructor
    . intro pre
      rcases pre with ⟨f', f'_mem, f'_eq⟩
      exists g.applyFact f'
      constructor
      . exists f'
      . exact f'_eq
    . intro pre
      rcases pre with ⟨f', f'_mem, f'_eq⟩
      rcases f'_mem with ⟨f'', f''_mem, f''_eq⟩
      exists f''
      constructor
      . exact f''_mem
      . rw [f''_eq, f'_eq]

  theorem applyPreservesElement (h : GroundTermMapping sig) (f : Fact sig) (fs : FactSet sig) : f ∈ fs -> applyFact h f ∈ applyFactSet h fs := by
    intro hf
    simp [Set.element] at *
    unfold applyFactSet
    exists f

  theorem applyFactSet_subset_of_subset (h : GroundTermMapping sig) (as bs : FactSet sig) : as ⊆ bs -> h.applyFactSet as ⊆ h.applyFactSet bs := by
    intro subset
    unfold GroundTermMapping.applyFactSet
    intro f f_mem
    rcases f_mem with ⟨f', f'_mem, f'_eq⟩
    exists f'
    constructor
    . apply subset; exact f'_mem
    . exact f'_eq

  def isHomomorphism (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
    isIdOnConstants h ∧ (h.applyFactSet A ⊆ B)

  theorem isHomomorphism_compose (g h : GroundTermMapping sig) (A B C : FactSet sig) :
      g.isHomomorphism A B -> h.isHomomorphism B C -> isHomomorphism (h ∘ g) A C := by
    intro g_hom h_hom
    constructor
    . intro t
      cases t with
      | inner _ _ => simp
      | leaf c =>
        simp
        have g_const := g_hom.left (FiniteTree.leaf c)
        simp at g_const
        rw [g_const]
        have g_const := h_hom.left (FiniteTree.leaf c)
        simp at g_const
        rw [g_const]
    . rw [applyFactSet_compose]
      intro f f_mem_compose
      rcases f_mem_compose with ⟨f', f'_mem, f'_eq⟩
      apply h_hom.right
      exists f'
      constructor
      . apply g_hom.right
        exact f'_mem
      . exact f'_eq

end GroundTermMapping

