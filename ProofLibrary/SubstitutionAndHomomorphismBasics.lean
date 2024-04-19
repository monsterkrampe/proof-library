import ProofLibrary.KnowledgeBaseBasics

def GroundSubstitution := Variable -> GroundTerm

def GroundTermMapping := GroundTerm -> GroundTerm

namespace GroundSubstitution
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
  def apply_conj (σ : GroundSubstitution) (conj : Conjunction) : List Fact :=
    (List.map (apply_atom σ)) conj
end GroundSubstitution

class SubsTarget (α) (β) where
  apply : GroundSubstitution -> α -> β

instance : SubsTarget Term GroundTerm where
  apply := GroundSubstitution.apply_term
instance : SubsTarget Atom Fact where
  apply := GroundSubstitution.apply_atom
instance : SubsTarget Conjunction (List Fact) where
  apply := GroundSubstitution.apply_conj

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

