import ProofLibrary.List
import ProofLibrary.KnowledgeBaseBasics

def GroundSubstitution := Variable -> GroundTerm

def GroundTermMapping := GroundTerm -> GroundTerm

namespace GroundSubstitution
  def apply_var_or_const (σ : GroundSubstitution) : VarOrConst -> GroundTerm
    | .var v => σ v
    | .const c => GroundTerm.const c

  def apply_skolem_term (σ : GroundSubstitution) : SkolemTerm -> GroundTerm
    | .var v => σ v
    | .const c => GroundTerm.const c
    | .func fs frontier => FiniteTree.inner fs (FiniteTreeList.fromList (frontier.map (fun fv => σ fv))) 

  -- def apply_term (σ : GroundSubstitution) : Term -> GroundTerm
  --   | .var v => σ v
  --   | .const c => GroundTerm.const c
  --   | .func ft => GroundTerm.func (FiniteTree.mapLeaves (fun voc => match voc with
  --     | .var v => match σ v with
  --       | .const c => FiniteTree.leaf c
  --       | .func ft => ft
  --     | .const c => FiniteTree.leaf c
  --   ) ft)

  def apply_atom (σ : GroundSubstitution) (ϕ : Atom) : Fact :=
    { predicate := ϕ.predicate, terms := List.map (apply_skolem_term σ) ϕ.terms }

  def apply_function_free_atom (σ : GroundSubstitution) (ϕ : FunctionFreeAtom) : Fact :=
    { predicate := ϕ.predicate, terms := List.map (apply_var_or_const σ) ϕ.terms }

  def apply_function_free_conj (σ : GroundSubstitution) (conj : FunctionFreeConjunction) : List Fact :=
    (List.map (apply_function_free_atom σ)) conj

  theorem apply_same_length (σ : GroundSubstitution) (a : Atom) : a.terms.length = (σ.apply_atom a).terms.length := by 
    simp [apply_atom]

  theorem eq_under_subs_means_same_length (σ : GroundSubstitution) (a : Atom) (f : Fact) (h : σ.apply_atom a = f) : (a.terms.length = f.terms.length) := by 
    rw [← h]
    simp [apply_atom]

  theorem eq_under_subs_means_term_is_eq (σ : GroundSubstitution) (a : Atom) (f : Fact) (idx : Fin a.terms.length) (h : σ.apply_atom a = f) : (σ.apply_skolem_term (a.terms.get idx) = f.terms.get { val := idx.val, isLt := (by rw [← eq_under_subs_means_same_length σ a f h]; exact idx.isLt) }) := by
    cases h
    simp [apply_atom, List.get_map]

  -- TODO: is the extra assumption with injectivity reasonable?
  theorem eq_under_subs_means_elements_are_preserved [DecidableEq SkolemTerm] (σ : GroundSubstitution) (a : Atom) (f : Fact) (h : σ.apply_atom a = f) : ∀ t, (∀ s, s ∈ a.terms.toSet ∧ σ.apply_skolem_term t = σ.apply_skolem_term s -> t = s) -> ((σ.apply_skolem_term t) ∈ f.terms ↔ t ∈ a.terms) := by 
    intro t ht
    rw [List.listElementIffToSetElement] 
    rw [List.listElementIffToSetElement] 
    rw [← List.existsIndexIffInToSet]
    rw [← List.existsIndexIffInToSet]
    constructor
    . intro ⟨i, hi⟩
      let j : Fin a.terms.length := ⟨i.val, (by rw [eq_under_subs_means_same_length σ a f h]; exact i.isLt)⟩
      exists j
      rw [← eq_under_subs_means_term_is_eq σ a f j h] at hi
      apply ht
      constructor
      . apply List.listGetInToSet 
      . apply hi
    . intro ⟨i, hi⟩
      let j : Fin f.terms.length := ⟨i.val, (by rw [← eq_under_subs_means_same_length σ a f h]; exact i.isLt)⟩
      exists j
      rw [← eq_under_subs_means_term_is_eq σ a f i h]
      rw [hi]

  -- TODO: is the extra assumption with injectivity reasonable?
  theorem eq_under_subs_means_indices_of_elements_are_preserved [DecidableEq SkolemTerm] (σ : GroundSubstitution) (a : Atom) (f : Fact) (h : σ.apply_atom a = f) (t : SkolemTerm) (ht : t ∈ a.terms) (hs : ∀ s, s ∈ a.terms.toSet ∧ σ.apply_skolem_term t = σ.apply_skolem_term s -> t = s) : (f.terms.idx_of (σ.apply_skolem_term t) (by rw [eq_under_subs_means_elements_are_preserved σ a f h t hs]; exact ht)).val = ((a.terms.idx_of t) ht).val := by 
    have : f.terms = a.terms.map σ.apply_skolem_term := by rw [← h]; unfold apply_atom; simp
    rw [List.idx_of_eq_of_list_eq _ _ this _ _]
    apply Eq.symm
    apply List.idx_of_eq_under_map
    apply hs

end GroundSubstitution

class SubsTarget (α) (β) where
  apply : GroundSubstitution -> α -> β

instance : SubsTarget SkolemTerm GroundTerm where
  apply := GroundSubstitution.apply_skolem_term
-- instance : SubsTarget Term GroundTerm where
--   apply := GroundSubstitution.apply_term
instance : SubsTarget Atom Fact where
  apply := GroundSubstitution.apply_atom
instance : SubsTarget FunctionFreeAtom Fact where
  apply := GroundSubstitution.apply_function_free_atom
instance : SubsTarget FunctionFreeConjunction (List Fact) where
  apply := GroundSubstitution.apply_function_free_conj

def isIdOnConstants (h : GroundTermMapping) : Prop :=
  ∀ t : GroundTerm, match t with
    | GroundTerm.const _ => h t = t
    | _ => True

def applyFact (h : GroundTermMapping) (f : Fact) : Fact :=
  { predicate := f.predicate, terms := List.map h f.terms }

def applyFactSet (h : GroundTermMapping) (fs : FactSet) : FactSet :=
  fun f' : Fact => ∃ f : Fact, (f ∈ fs) ∧ ((applyFact h f) = f')

def isHomomorphism (h : GroundTermMapping) (A B : FactSet) : Prop :=
  isIdOnConstants h ∧ (applyFactSet h A ⊆ B)

theorem applyPreservesElement (h : GroundTermMapping) (f : Fact) (fs : FactSet) : f ∈ fs -> applyFact h f ∈ applyFactSet h fs := by 
  intro hf
  simp [Set.element] at *
  unfold applyFactSet
  exists f

