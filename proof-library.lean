def Set (α) := α -> Prop

def emptyset : Set α := fun _ => False
notation:max "∅" => emptyset

def Set.element (e : α) (X : Set α) : Prop := X e
infixr:75 " ∈ " => Set.element

def Set.union (X Y : Set α) : Set α := fun e => e ∈ X ∨ e ∈ Y
infixr:65 " ∪ " => Set.union

def Set.subset (X Y : Set α) : Prop := ∀ e : α, e ∈ X → e ∈ Y
infixr:50 " ⊆ " => Set.subset

def List.toSet : List α -> Set α
  | nil => ∅
  | cons h tail => (fun e => e = h) ∪ (List.toSet tail)

instance : Coe (List α) (Set α) where
  coe := List.toSet

structure Predicate where
  id : Nat

structure Variable where
  id : Nat

instance : BEq Variable where
  beq a b := a.id = b.id

structure Constant where
  id : Nat

/- I think we only need skolem function symbols
structure FunctionSymbol where
  id : Nat
-/

structure SkolemFS where
  rule : Rule
  var : Variable

mutual
  inductive GroundTerm where
    | Constant (c : Constant) : GroundTerm
    | Functional (f : SkolemFS) (ts : GroundTermList) : GroundTerm

  inductive GroundTermList where
    | Single (t : GroundTerm) : GroundTermList
    | List (t : GroundTerm) (ts : GroundTermList) : GroundTermList
end

mutual
  def GroundTerm.depth : GroundTerm -> Nat
    | GroundTerm.Constant _ => 0
    | GroundTerm.Functional f ts => 1 + GroundTermList.depth ts

  def GroundTermList.depth : GroundTermList -> Nat
    | GroundTermList.Single t => GroundTerm.depth t
    | GroundTermList.List t ts => GroundTerm.depth t + GroundTermList.depth ts
end

mutual
  inductive Term where
    | Variable (v : Variable) : Term
    | Constant (c : Constant) : Term
    | Functional (f : SkolemFS) (ts : TermList) : Term

  inductive TermList where
    | Single (t : Term) : TermList
    | List (t : Term) (ts : TermList) : TermList
end

mutual
  def GroundTerm.toTerm : GroundTerm -> Term
    | GroundTerm.Constant c => Term.Constant c
    | GroundTerm.Functional f ts => Term.Functional f (GroundTermList.toTerm ts)

  def GroundTermList.toTerm : GroundTermList -> TermList
    | GroundTermList.Single t => TermList.Single (GroundTerm.toTerm t)
    | GroundTermList.List t ts => TermList.List (GroundTerm.toTerm t) (GroundTermList.toTerm ts)
end

instance : Coe GroundTerm Term where
  coe := GroundTerm.toTerm

mutual
  def Term.variable : Term -> Option Variable
    | Term.Variable v => Option.some v
    | Term.Constant _ => Option.none
    | Term.Functional _ _ => Option.none

  def TermList.variables : TermList -> List Variable
    | TermList.Single t => match (Term.variable t) with
      | some v => List.cons v List.nil
      | none => List.nil
    | TermList.List t ts => match (Term.variable t) with
      | some v => List.cons v (TermList.variables ts)
      | none => TermList.variables ts
end

structure FunctionFreeFact where
  predicate : Fact
  terms : List Constant

structure Fact where
  predicate : Predicate
  terms : GroundTermList

structure Atom where
  predicate : Predicate
  terms : TermList

def Atom.variables (a : Atom) : List Variable := TermList.variables a.terms

def Conjunction := List Atom

def Conjunction.vars (conj : Conjunction) : List Variable :=
  List.foldl (fun acc vs => acc ++ vs) (List.nil) (List.map Atom.variables conj)

-- normally, we would only allow variables in atoms in rules... does this break later?
structure Rule where
  body : Conjunction
  head : Conjunction

def Rule.frontier (r : Rule) : List Variable :=
  -- NOTE: using ∈ does not really work here because it produces a Prop which can not always be simply cast into Bool
  List.filter (fun v => not (List.elem v (Conjunction.vars r.head))) (Conjunction.vars r.body)

def Rule.skolemize (r : Rule) : Rule :=
  { body := r.body, head :=
    List.map (fun a => { predicate := a.predicate, terms :=
      (List.map (fun t => match t with
        | Term.Variable v => v -- TODO: skolemize here
        | t => t
      ) a.terms)
    }) r.head
  }

def RuleSet := Set Rule

def FactSet := Set Fact

def Database := Set FunctionFreeFact

structure KnowledgeBase where
  db : Database
  rules : RuleSet

def GroundSubstitution := Variable -> GroundTerm

mutual
  def GroundSubstitution.apply_term (σ : GroundSubstitution) : Term -> GroundTerm
    | Term.Variable v => σ v
    | Term.Constant c => GroundTerm.Constant c
    | Term.Functional f ts => GroundTerm.Functional f (GroundSubstitution.apply_list σ ts)

  def GroundSubstitution.apply_list (σ : GroundSubstitution) : TermList -> GroundTermList
    | TermList.Single t => GroundTermList.Single (GroundSubstitution.apply_term σ t)
    | TermList.List t ts => GroundTermList.List (GroundSubstitution.apply_term σ t) (GroundSubstitution.apply_list σ ts)
end

def GroundSubstitution.apply_atom (σ : GroundSubstitution) (ϕ : Atom) : Fact :=
  { predicate := ϕ.predicate, terms := GroundSubstitution.apply_list σ ϕ.terms }
def GroundSubstitution.apply_conj (σ : GroundSubstitution) (conj : Conjunction) : List Fact :=
  (List.map (GroundSubstitution.apply_atom σ)) conj

class SubsTarget (α) (β) where
  apply : GroundSubstitution -> α -> β

instance : SubsTarget Term GroundTerm where
  apply := GroundSubstitution.apply_term
instance : SubsTarget TermList GroundTermList where
  apply := GroundSubstitution.apply_list
instance : SubsTarget Atom Fact where
  apply := GroundSubstitution.apply_atom
instance : SubsTarget Conjunction (List Fact) where
  apply := GroundSubstitution.apply_conj

structure Trigger where
  rule : Rule
  subs : GroundSubstitution

def Trigger.loaded (trg : Trigger) (F : FactSet) : Prop :=
  let l : List Fact := SubsTarget.apply trg.subs trg.rule.body
  l ⊆ F

/- FIXME
def Trigger.sactive (trg : Trigger) (F : FactSet) : Prop := sorry

def Trigger.ractive (trg : Trigger) (F : FactSet) : Prop := sorry
-/
