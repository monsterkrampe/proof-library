import ProofLibrary.List
import ProofLibrary.Set
import ProofLibrary.TermBasics

section StructuralDefs

  @[ext]
  structure FunctionFreeFact (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] where
    predicate : sig.P
    terms : List sig.C
    deriving DecidableEq

  @[ext]
  structure Fact (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (GroundTerm sig)
    deriving DecidableEq

  structure FunctionFreeAtom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (VarOrConst sig)
    deriving DecidableEq

  structure Atom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (SkolemTerm sig)
    deriving DecidableEq

  variable (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  abbrev FunctionFreeConjunction := List (FunctionFreeAtom sig)

  -- normally, we would only allow variables in atoms in rules... does this break later?
  structure Rule where
    id : Nat
    body : FunctionFreeConjunction sig
    head : List (FunctionFreeConjunction sig)

  structure RuleSet where
    rules : Set (Rule sig)
    id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.id = r2.id -> r1 = r2

  abbrev FactSet := Set (Fact sig)

  abbrev Database := { X : Set (FunctionFreeFact sig) // X.finite }

  structure KnowledgeBase where
    db : Database sig
    rules : RuleSet sig

end StructuralDefs


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace FunctionFreeAtom

  def variables (a : FunctionFreeAtom sig) : List sig.V := VarOrConst.filterVars a.terms

  def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) : Atom sig := { predicate := a.predicate, terms := a.terms.map (VarOrConst.skolemize ruleId disjunctIndex frontier) }

  theorem skolemize_same_length (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) : a.terms.length = (a.skolemize ruleId disjunctIndex frontier).terms.length := by
    unfold skolemize
    rw [List.length_map]

  theorem skolem_term_in_skolem_atom_if_term_in_atom (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) (t : VarOrConst sig) : t ∈ a.terms.toSet -> (↑(t.skolemize ruleId disjunctIndex frontier)) ∈ (a.skolemize ruleId disjunctIndex frontier).terms.toSet := by
    unfold skolemize
    induction a.terms with
    | nil => intros; contradiction
    | cons head tail ih =>
      simp [Set.element, List.toSet]
      intro h
      cases h with
      | inl hl => apply Or.inl; simp [Set.element] at hl; rw [hl]; simp [Set.element]
      | inr hr => apply Or.inr; apply ih; apply hr

end FunctionFreeAtom

namespace FunctionFreeConjunction

  def vars (conj : FunctionFreeConjunction sig) : List sig.V := (conj.map FunctionFreeAtom.variables).flatten

  theorem v_in_vars_occurs_in_fact (conj : FunctionFreeConjunction sig) : ∀ v, v ∈ conj.vars -> ∃ f, f ∈ conj ∧ (VarOrConst.var v) ∈ f.terms := by
    unfold vars
    cases conj with
    | nil => intros; contradiction
    | cons head tail =>
      intro v vInVars
      rw [List.mem_flatten] at vInVars
      cases vInVars with | intro L' hL' =>
        simp only [List.mem_map] at hL'
        cases hL'.left with | intro e' he' =>
          exists e'
          constructor
          . exact he'.left
          . have : v ∈ e'.variables := by
              rw [he'.right]
              apply hL'.right

            apply VarOrConst.filterVars_occur_in_original_list
            unfold FunctionFreeAtom.variables at this
            apply this

end FunctionFreeConjunction

namespace Rule

  def frontier (r : Rule sig) : List sig.V :=
    -- NOTE: using ∈ does not really work here because it produces a Prop which can not always be simply cast into Bool
    List.filter (fun v => r.head.any (fun h => v ∈ h.vars)) (FunctionFreeConjunction.vars r.body)

  theorem frontier_var_occurs_in_fact_in_body (r : Rule sig) : ∀ v, v ∈ r.frontier -> ∃ f, f ∈ r.body ∧ (VarOrConst.var v) ∈ f.terms := by
    unfold frontier
    cases r.body with
    | nil => intros; contradiction
    | cons head tail =>
      intro v vInFrontier
      have vInBody := List.elemFilterAlsoElemList _ _ v vInFrontier
      have exFactInBody := FunctionFreeConjunction.v_in_vars_occurs_in_fact _ v vInBody
      exact exFactInBody

  def Rule.isDatalog (r : Rule sig) : Bool :=
    r.head.all (fun h => h.vars.all (fun v => v ∈ r.body.vars))

end Rule

def RuleSet.isDeterministic (rs : RuleSet sig) : Prop := ∀ (r : Rule sig), r ∈ rs.rules -> r.head.length = 1

def KnowledgeBase.isDeterministic (kb : KnowledgeBase sig) : Prop := kb.rules.isDeterministic

def FunctionFreeFact.toFact (f : FunctionFreeFact sig) : Fact sig := {
  predicate := f.predicate,
  terms := f.terms.map GroundTerm.const
}

def Fact.toFunctionFreeFact (f : Fact sig) : Option (FunctionFreeFact sig) :=
  if h :
    (List.all
      f.terms
      (fun t => match t with
        | GroundTerm.const _ => true
        | _ => false
      )
    )
  then
    (Option.some ({ predicate := f.predicate, terms := (f.terms.attach.map (fun ⟨t, t_elem⟩ => match eq : t with
      | .leaf c => c
      | .inner _ _ => by
        -- This cannot happen since we check before that everything is a constant
        simp at h
        specialize h t
        rw [eq] at h
        specialize h t_elem
        simp at h
    )) }))
  else
    (Option.none)

theorem FunctionFreeFact.toFunctionFreeFact_after_toFact_is_id : ∀ (f : FunctionFreeFact sig), f.toFact.toFunctionFreeFact = some f := by
  intro f
  unfold toFact
  unfold Fact.toFunctionFreeFact
  simp
  apply FunctionFreeFact.ext
  . simp
  . simp
    rw [List.map_attach, List.pmap_map]
    simp

theorem Fact.toFact_after_toFunctionFreeFact_is_id : ∀ (f : Fact sig), f.toFunctionFreeFact.is_none_or (fun fff => fff.toFact = f) := by
  intro f
  cases eq : f.toFunctionFreeFact with
  | none => simp [Option.is_none_or]
  | some fff =>
    simp [Option.is_none_or]
    unfold FunctionFreeFact.toFact
    unfold toFunctionFreeFact at eq
    split at eq
    case isTrue h =>
      injection eq with eq
      rw [← eq]
      simp
      apply Fact.ext
      . simp
      . simp
        rw [List.map_attach]
        simp
        apply List.ext_get
        . simp
        intro n _ _
        simp
        split
        case h_1 _ _ heq _ => rw [heq]; rfl
        case h_2 _ _ heq _ =>
          simp at h
          specialize h f.terms[n] (by apply List.getElem_mem)
          rw [heq] at h
          simp at h
    case isFalse _ => contradiction

def FactSet.terms (fs : FactSet sig) : Set (GroundTerm sig) := fun t => ∃ f, f ∈ fs ∧ t ∈ f.terms

theorem FactSet.terms_finite_of_finite (fs : FactSet sig) (finite : fs.finite) : fs.terms.finite := by
  rcases finite with ⟨l, nodup, finite⟩
  exists (l.map Fact.terms).flatten.eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro e
    constructor
    . intro in_l
      unfold FactSet.terms
      simp [List.mem_eraseDupsKeepRight_iff, List.mem_flatten] at in_l
      rcases in_l with ⟨terms, ex_f, e_in_terms⟩
      rcases ex_f with ⟨f, f_in_l, terms_eq⟩
      exists f
      constructor
      . rw [← finite]; exact f_in_l
      . rw [terms_eq]; exact e_in_terms
    . intro in_fs
      unfold FactSet.terms at in_fs
      simp [List.mem_eraseDupsKeepRight_iff, List.mem_flatten]
      rcases in_fs with ⟨f, f_in_fs, e_in_f⟩
      exists f.terms
      constructor
      . exists f
        constructor
        . rw [finite]; exact f_in_fs
        . rfl
      . exact e_in_f

def Database.toFactSet (db : Database sig) : { fs : FactSet sig // fs.finite } := ⟨
  fun x => match (Fact.toFunctionFreeFact x) with
    | Option.none => False
    | Option.some fff => fff ∈ db.val,
  by
    cases db.property with | intro l property =>
      exists (l.map FunctionFreeFact.toFact).eraseDupsKeepRight
      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro e
        rw [List.mem_eraseDupsKeepRight_iff]
        simp
        constructor
        . intro h; cases h with | intro e' h =>
          simp [Set.element]
          rw [← h.right]
          rw [FunctionFreeFact.toFunctionFreeFact_after_toFact_is_id]
          simp
          simp [Set.element] at property
          rw [← property.right e']
          exact h.left
        . intro h
          simp [Set.element] at h
          cases eq : e.toFunctionFreeFact with
          | none => simp [eq] at h
          | some e' =>
            exists e'
            simp [eq] at h
            constructor
            . rw [property.right e']; exact h
            . have aux := Fact.toFact_after_toFunctionFreeFact_is_id e
              rw [eq] at aux
              simp [Option.is_none_or] at aux
              exact aux
⟩

