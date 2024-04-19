import ProofLibrary.List
import ProofLibrary.Set
import ProofLibrary.TermBasics

structure FunctionFreeFact where
  predicate : Predicate
  terms : List Constant

structure Fact where
  predicate : Predicate
  terms : List GroundTerm
  deriving DecidableEq

structure FunctionFreeAtom where
  predicate : Predicate
  terms : List VarOrConst
  deriving DecidableEq

structure Atom where
  predicate : Predicate
  terms : List SkolemTerm

-- TODO: remove duplicates here maybe
def FunctionFreeAtom.variables (a : FunctionFreeAtom) : List Variable := VarOrConst.filterVars a.terms

def FunctionFreeAtom.skolemize (ruleId : Nat) (frontier : List Variable) (a : FunctionFreeAtom) : Atom := { predicate := a.predicate, terms := a.terms.map (VarOrConst.skolemize ruleId frontier) }

theorem FunctionFreeAtom.skolemize_same_length (ruleId : Nat) (frontier : List Variable) (a : FunctionFreeAtom) : a.terms.length = (a.skolemize ruleId frontier).terms.length := by 
  unfold skolemize
  rw [List.length_map]

theorem FunctionFreeAtom.skolem_term_in_skolem_atom_if_term_in_atom (ruleId : Nat) (frontier : List Variable) (a : FunctionFreeAtom) (t : VarOrConst) : t ∈ a.terms.toSet -> (↑(t.skolemize ruleId frontier)) ∈ (a.skolemize ruleId frontier).terms.toSet := by 
  unfold skolemize
  induction a.terms with 
  | nil => intros; contradiction
  | cons head tail ih => 
    simp [Set.element, List.toSet]
    intro h 
    cases h with 
    | inl hl => apply Or.inl; simp [Set.element] at hl; rw [hl]; simp [Set.element]
    | inr hr => apply Or.inr; apply ih; apply hr

def FunctionFreeConjunction := List FunctionFreeAtom
-- def Conjunction := List Atom

def FunctionFreeConjunction.vars (conj : FunctionFreeConjunction) : List Variable :=
  List.foldl (fun acc vs => acc ++ vs) (List.nil) (List.map FunctionFreeAtom.variables conj)

theorem FunctionFreeConjunction.v_in_vars_occurs_in_fact (conj : FunctionFreeConjunction) : ∀ v, List.elem v conj.vars -> ∃ f, f ∈ conj.toSet ∧ (VarOrConst.var v) ∈ f.terms.toSet := by
  unfold vars
  cases conj with 
  | nil => intros; contradiction
  | cons head tail =>
    intro v vInVars
    have vInSomeMappedAtom := List.elemFlattenAlsoElemSomeList _ _ vInVars
    cases vInSomeMappedAtom with | intro L' hL' =>
      have vInSomeOriginalAtom := List.exElemInMappedListMeansOriginalElemExistsThatMapsToIt _ _ _ hL'.left
      cases vInSomeOriginalAtom with | intro e' he' =>
        exists e'
        constructor
        . apply List.listElementAlsoToSetElement 
          exact he'.left
        . have : v ∈ (FunctionFreeAtom.variables e').toSet := by 
            apply List.listElementAlsoToSetElement 
            have hL'right := hL'.right
            rw [he'.right] at hL'right
            apply hL'right

          apply VarOrConst.filterVars_occur_in_original_list
          unfold FunctionFreeAtom.variables at this
          apply this

-- normally, we would only allow variables in atoms in rules... does this break later?
structure Rule where
  id : Nat
  body : FunctionFreeConjunction
  head : FunctionFreeConjunction

def Rule.frontier (r : Rule) : List Variable :=
  -- NOTE: using ∈ does not really work here because it produces a Prop which can not always be simply cast into Bool
  List.filter (fun v => r.head.vars.elem v) (FunctionFreeConjunction.vars r.body)

theorem Rule.frontier_var_occurs_in_fact_in_body (r : Rule) : ∀ v, List.elem v r.frontier -> ∃ f, f ∈ r.body.toSet ∧ (VarOrConst.var v) ∈ f.terms.toSet := by 
  unfold frontier
  cases r.body with
  | nil => intros; contradiction
  | cons head tail => 
    intro v vInFrontier
    have vInBody := List.elemFilterAlsoElemList _ _ v vInFrontier
    have exFactInBody := FunctionFreeConjunction.v_in_vars_occurs_in_fact _ v vInBody
    exact exFactInBody

-- def Rule.skolemize (r : Rule) : Rule :=
--   { body := r.body, head :=
--     List.map (fun (i, a) => {
--       predicate := a.predicate,
--       terms := List.map (Term.skolemize i (Rule.frontier r)) a.terms
--     }) (List.enum r.head)
--   }

def Rule.isDatalog (r : Rule) : Bool :=
  List.all r.head.vars (fun v => r.body.vars.elem v)

def RuleSet := Set Rule

def FactSet := Set Fact

def Database := Set FunctionFreeFact

structure KnowledgeBase where
  db : Database
  rules : RuleSet

def Fact.toFunctionFreeFact (f : Fact) : Option FunctionFreeFact :=
  ite
    (List.all
      f.terms
      (fun t => match t with
        | GroundTerm.const _ => true
        | _ => false
      )
    )
    (Option.some ({ predicate := f.predicate, terms := (List.map (fun t => match t with
      | GroundTerm.const c => c
      | _ => { id := 0 } -- TODO: this cannot happen since we check before that everything is a constant
    ) f.terms) }))
    (Option.none)

def Database.toFactSet (db : Database) : FactSet := fun x => match (Fact.toFunctionFreeFact x) with
  | Option.none => False
  | Option.some fff => fff ∈ db

instance : Coe Database FactSet where
  coe := Database.toFactSet
