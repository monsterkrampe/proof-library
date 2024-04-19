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
  terms : List VariableOrConstant

structure Atom where
  predicate : Predicate
  terms : List Term

-- TODO: remove duplicates here maybe
def FunctionFreeAtom.variables (a : FunctionFreeAtom) : List Variable := List.foldl (fun acc t => acc ++ Term.variables t) List.nil a.terms

def FunctionFreeConjunction := List FunctionFreeAtom
-- def Conjunction := List Atom

def FunctionFreeConjunction.vars (conj : FunctionFreeConjunction) : List Variable :=
  List.foldl (fun acc vs => acc ++ vs) (List.nil) (List.map FunctionFreeAtom.variables conj)

-- normally, we would only allow variables in atoms in rules... does this break later?
structure Rule where
  body : FunctionFreeConjunction
  head : FunctionFreeConjunction

def Rule.frontier (r : Rule) : List Variable :=
  -- NOTE: using ∈ does not really work here because it produces a Prop which can not always be simply cast into Bool
  List.filter (fun v => r.head.vars.elem v) (FunctionFreeConjunction.vars r.body)

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
