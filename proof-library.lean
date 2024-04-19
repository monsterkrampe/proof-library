def Set (α) := α -> Prop

def Set.element (e : α) (X : Set α) : Prop := X e
infixr:75 " ∈ " => Set.element

def Set.union (X Y : Set α) : Set α := fun a => a ∈ X ∨ a ∈ Y
infixr:65 " ∪ " => Set.union

def Set.subset (X Y : Set α) : Prop := ∀ e : α, e ∈ X → e ∈ Y
infixr:50 " ⊆ " => Set.subset

structure Predicate where
  id : α

structure Variable where
  id : α

structure Constant where
  id : α

structure FunctionSymbol where
  id : α

mutual
  inductive GroundTerm where
    | Constant (c : Constant) : GroundTerm
    | Functional (f : FunctionSymbol) (ts : GroundTermList) : GroundTerm

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
    | Functional (f : FunctionSymbol) (ts : TermList): Term

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
  coe gt := GroundTerm.toTerm gt

structure FunctionFreeFact where
  predicate : Fact
  terms : List Constant

structure Fact where
  predicate : Predicate
  terms : GroundTermList

structure Atom where
  predicate : Predicate
  terms : TermList

def Conjunction := List Atom

structure Rule where
  body : Conjunction
  head : Conjunction

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
