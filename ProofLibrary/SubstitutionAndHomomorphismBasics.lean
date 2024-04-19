import ProofLibrary.List
import ProofLibrary.KnowledgeBaseBasics

def GroundSubstitution := Variable -> GroundTerm

def GroundTermMapping := GroundTerm -> GroundTerm

namespace GroundSubstitution
  def apply_var_or_const (σ : GroundSubstitution) : VarOrConst -> GroundTerm
    | VarOrConst.var v => σ v
    | VarOrConst.const c => GroundTerm.const c

  def apply_term (σ : GroundSubstitution) : Term -> GroundTerm
    | Term.var v => σ v
    | Term.const c => GroundTerm.const c
    | Term.func ft => GroundTerm.func (FiniteTree.mapLeaves (fun voc => match voc with
      | VarOrConst.var v => match σ v with
        | GroundTerm.const c => FiniteTree.leaf c
        | GroundTerm.func ft => ft
      | VarOrConst.const c => FiniteTree.leaf c
    ) ft)

  def apply_atom (σ : GroundSubstitution) (ϕ : Atom) : Fact :=
    { predicate := ϕ.predicate, terms := List.map (apply_term σ) ϕ.terms }

  def apply_function_free_atom (σ : GroundSubstitution) (ϕ : FunctionFreeAtom) : Fact :=
    { predicate := ϕ.predicate, terms := List.map (apply_var_or_const σ) ϕ.terms }

  def apply_function_free_conj (σ : GroundSubstitution) (conj : FunctionFreeConjunction) : List Fact :=
    (List.map (apply_function_free_atom σ)) conj

  theorem apply_same_length (σ : GroundSubstitution) (a : Atom) : a.terms.length = (σ.apply_atom a).terms.length := by 
    simp [apply_atom]

  theorem eq_under_subs_means_same_length (σ : GroundSubstitution) (a : Atom) (f : Fact) (h : σ.apply_atom a = f) : (a.terms.length = f.terms.length) := by 
    rw [← h]
    simp [apply_atom]

  theorem eq_under_subs_means_term_is_eq (σ : GroundSubstitution) (a : Atom) (f : Fact) (idx : Fin a.terms.length) (h : σ.apply_atom a = f) : (σ.apply_term (a.terms.get idx) = f.terms.get { val := idx.val, isLt := (by rw [← eq_under_subs_means_same_length σ a f h]; exact idx.isLt) }) := by
    cases h
    simp [apply_atom, List.get_map]

end GroundSubstitution

class SubsTarget (α) (β) where
  apply : GroundSubstitution -> α -> β

instance : SubsTarget Term GroundTerm where
  apply := GroundSubstitution.apply_term
instance : SubsTarget Atom Fact where
  apply := GroundSubstitution.apply_atom
instance : SubsTarget FunctionFreeAtom Fact where
  apply := GroundSubstitution.apply_function_free_atom
instance : SubsTarget FunctionFreeConjunction (List Fact) where
  apply := GroundSubstitution.apply_function_free_conj

def isHomomorphism (h : GroundTermMapping) : Prop :=
  ∀ t : GroundTerm, match t with
    | GroundTerm.const _ => h t = t
    | _ => True

def applyFact (h : GroundTermMapping) (f : Fact) : Fact :=
  { predicate := f.predicate, terms := List.map h f.terms }

def applyFactSet (h : GroundTermMapping) (fs : FactSet) : FactSet :=
  fun f' : Fact => ∃ f : Fact, (f ∈ fs) ∧ ((applyFact h f) = f')

theorem applyPreservesElement (h : GroundTermMapping) (f : Fact) (fs : FactSet) : f ∈ fs -> applyFact h f ∈ applyFactSet h fs := by 
  intro hf
  simp [Set.element] at *
  unfold applyFactSet
  exists f

