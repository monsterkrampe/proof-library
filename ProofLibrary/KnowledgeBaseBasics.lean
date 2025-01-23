import ProofLibrary.List
import ProofLibrary.Set
import ProofLibrary.TermBasics

section StructuralDefs

  @[ext]
  structure FunctionFreeFact (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] where
    predicate : sig.P
    terms : List sig.C
    arity_ok : terms.length = sig.arity predicate
    deriving DecidableEq

  @[ext]
  structure Fact (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (GroundTerm sig)
    arity_ok : terms.length = sig.arity predicate
    deriving DecidableEq

  structure FunctionFreeAtom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (VarOrConst sig)
    arity_ok : terms.length = sig.arity predicate
    deriving DecidableEq

  structure Atom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (SkolemTerm sig)
    arity_ok : terms.length = sig.arity predicate
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

  def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) : Atom sig := { predicate := a.predicate, terms := a.terms.map (VarOrConst.skolemize ruleId disjunctIndex frontier), arity_ok := by rw [List.length_map, a.arity_ok] }

  theorem skolemize_same_length (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) : a.terms.length = (a.skolemize ruleId disjunctIndex frontier).terms.length := by
    unfold skolemize
    rw [List.length_map]

  theorem skolem_term_in_skolem_atom_if_term_in_atom (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) (t : VarOrConst sig) : t ∈ a.terms.toSet -> (↑(t.skolemize ruleId disjunctIndex frontier)) ∈ (a.skolemize ruleId disjunctIndex frontier).terms.toSet := by
    unfold skolemize

    have : ∀ (ts : List (VarOrConst sig)), t ∈ ts -> (t.skolemize ruleId disjunctIndex frontier) ∈ ts.map (VarOrConst.skolemize ruleId disjunctIndex frontier) := by
      intro ts
      induction ts with
      | nil => intros; contradiction
      | cons head tail ih =>
        intro h
        rw [List.mem_cons] at h
        rw [List.map_cons, List.mem_cons]
        cases h with
        | inl hl => apply Or.inl; simp [Set.element] at hl; rw [hl]
        | inr hr => apply Or.inr; apply ih; apply hr

    intro mem
    rw [← List.inIffInToSet] at mem
    rw [← List.inIffInToSet]
    apply this a.terms
    exact mem

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

  def predicates (conj : FunctionFreeConjunction sig) : List sig.P := conj.map FunctionFreeAtom.predicate

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

  def isDatalog (r : Rule sig) : Bool :=
    r.head.all (fun h => h.vars.all (fun v => v ∈ r.body.vars))

  def isDeterministic (r : Rule sig) : Prop := r.head.length = 1

  def predicates (r : Rule sig) : List sig.P := r.body.predicates ++ (r.head.flatMap FunctionFreeConjunction.predicates)

end Rule

namespace RuleSet

  def isDeterministic (rs : RuleSet sig) : Prop := ∀ (r : Rule sig), r ∈ rs.rules -> r.isDeterministic

  def predicates (rs : RuleSet sig) : Set sig.P := fun p => ∃ r, r ∈ rs.rules ∧ p ∈ r.predicates

  theorem predicates_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.predicates.finite := by
    intro finite
    rcases finite with ⟨l, nodup, eq⟩
    exists (l.flatMap Rule.predicates).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro p
      rw [List.mem_eraseDupsKeepRight_iff]
      unfold predicates
      simp only [List.mem_flatMap]
      constructor <;> (intro h; rcases h with ⟨r, h⟩; exists r)
      . rw [← eq]; assumption
      . rw [eq]; assumption

end RuleSet

def KnowledgeBase.isDeterministic (kb : KnowledgeBase sig) : Prop := kb.rules.isDeterministic

def Fact.isFunctionFree (f : Fact sig) : Prop := ∀ t, t ∈ f.terms -> ∃ c, t = GroundTerm.const c
def FactSet.isFunctionFree (fs : FactSet sig) : Prop := ∀ f, f ∈ fs -> f.isFunctionFree

def FunctionFreeFact.toFact (f : FunctionFreeFact sig) : Fact sig := {
  predicate := f.predicate,
  terms := f.terms.map GroundTerm.const,
  arity_ok := by rw [List.length_map, f.arity_ok]
}

theorem FunctionFreeFact.toFact_isFunctionFree (f : FunctionFreeFact sig) : f.toFact.isFunctionFree := by
  intro t t_mem
  unfold toFact at t_mem
  simp at t_mem
  rcases t_mem with ⟨c, _, t_eq⟩
  exists c
  rw [t_eq]

def Fact.toFunctionFreeFact (f : Fact sig) (isFunctionFree : f.isFunctionFree) : FunctionFreeFact sig :={
  predicate := f.predicate
  terms := f.terms.attach.map (fun t => t.val.toConst (isFunctionFree t.val t.property))
  arity_ok := by rw [List.length_map, List.length_attach, f.arity_ok]
}

theorem FunctionFreeFact.toFunctionFreeFact_after_toFact_is_id (f : FunctionFreeFact sig) : f.toFact.toFunctionFreeFact (f.toFact_isFunctionFree) = f := by
  unfold toFact
  unfold Fact.toFunctionFreeFact
  simp
  apply FunctionFreeFact.ext
  . simp
  . simp only [GroundTerm.toConst]
    rw [List.map_attach, List.pmap_map]
    simp

theorem Fact.toFact_after_toFunctionFreeFact_is_id (f : Fact sig) (isFunctionFree : f.isFunctionFree) : (f.toFunctionFreeFact isFunctionFree).toFact = f := by
  unfold toFunctionFreeFact
  unfold FunctionFreeFact.toFact
  simp
  apply Fact.ext
  . simp
  . simp only [List.map_attach]
    apply List.ext_get
    . simp
    intro n _ _
    simp
    specialize isFunctionFree f.terms[n] (by simp)
    rcases isFunctionFree with ⟨c, isFunctionFree⟩
    simp only [isFunctionFree]
    unfold GroundTerm.toConst
    simp

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

def Database.toFactSet (db : Database sig) : { fs : FactSet sig // fs.finite ∧ fs.isFunctionFree } := ⟨
  (fun f => ∃ f', f' ∈ db.val ∧ f'.toFact = f),
  (by
    rcases db.property with ⟨l, _, l_eq⟩
    exists (l.map FunctionFreeFact.toFact).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro f
      rw [List.mem_eraseDupsKeepRight_iff]
      rw [List.mem_map]
      simp only [l_eq]
      simp [Set.element]
  ),
  (by
    intro f f_mem
    rcases f_mem with ⟨_, _, f_eq⟩
    rw [← f_eq]
    apply FunctionFreeFact.toFact_isFunctionFree
  ),
⟩

