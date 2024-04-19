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

mutual
    inductive Tree (α : Type u) (β : Type v) where
      | leaf : β -> Tree α β
      | inner : α -> TreeList α β -> Tree α β

    inductive TreeList (α : Type u) (β : Type v)where
      | nil  : TreeList α β
      | cons : Tree α β -> TreeList α β -> TreeList α β
end

def TreeList.toList : TreeList α β -> List (Tree α β)
  | TreeList.nil => List.nil
  | TreeList.cons t ts => List.cons t (TreeList.toList ts)

def TreeList.fromList : List (Tree α β) -> TreeList α β
  | List.nil => TreeList.nil
  | List.cons t ts => TreeList.cons t (TreeList.fromList ts)

instance : Coe (TreeList α β) (List (Tree α β)) where
  coe := TreeList.toList

instance : Coe (List (Tree α β)) (TreeList α β) where
  coe := TreeList.fromList

mutual
  def Tree.depth : Tree α β -> Nat
    | Tree.leaf _ => 1
    | Tree.inner _ ts => 1 + TreeList.depth ts

  def TreeList.depth : TreeList α β -> Nat
    | TreeList.nil => 0
    | TreeList.cons t ts => max (Tree.depth t) (TreeList.depth ts)
end

mutual
  def Tree.leaves : Tree α β -> List β
    | Tree.leaf b => List.cons b List.nil
    | Tree.inner _ ts => TreeList.leaves ts

  def TreeList.leaves : TreeList α β -> List β
    | TreeList.nil => List.nil
    | TreeList.cons t ts => (Tree.leaves t) ++ (TreeList.leaves ts)
end

mutual
  def Tree.mapLeaves (f : β -> Tree α γ) (t : Tree α β) : Tree α γ := match t with
    | Tree.leaf b => f b
    | Tree.inner a ts => Tree.inner a (TreeList.mapLeaves f ts)

  def TreeList.mapLeaves (f : β -> Tree α γ) (ts : TreeList α β) : TreeList α γ := match ts with
    | TreeList.nil => TreeList.nil
    | TreeList.cons t ts => TreeList.cons (Tree.mapLeaves f t) (TreeList.mapLeaves f ts)
end

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
  ruleId : Nat
  var : Variable

inductive GroundTerm where
  | const (c : Constant) : GroundTerm
  | func (ft : Tree SkolemFS Constant) : GroundTerm

def GroundTerm.depth : GroundTerm -> Nat
  | GroundTerm.const _ => 0
  | GroundTerm.func ft => Tree.depth ft

inductive VarOrConst where
  | var (v : Variable) : VarOrConst
  | const (c : Constant) : VarOrConst

def VarOrConst.isVar : VarOrConst -> Bool
  | VarOrConst.var _ => true
  | VarOrConst.const _ => false

def VarOrConst.filterVars : List VarOrConst -> List Variable
  | List.nil => List.nil
  | List.cons voc vocs => match voc with
    | VarOrConst.var v => List.cons v (VarOrConst.filterVars vocs)
    | VarOrConst.const _ => (VarOrConst.filterVars vocs)

inductive Term where
  | var (v : Variable) : Term
  | const (c : Constant) : Term
  | func (ft : Tree SkolemFS VarOrConst) : Term

def GroundTerm.toTerm : GroundTerm -> Term
  | GroundTerm.const c => Term.const c
  | GroundTerm.func ft => Term.func (Tree.mapLeaves (fun c => Tree.leaf (VarOrConst.const c)) ft)

instance : Coe GroundTerm Term where
  coe := GroundTerm.toTerm

def Term.variables : Term -> List Variable
  | Term.var v => List.cons v List.nil
  | Term.const _ => List.nil
  | Term.func ft => VarOrConst.filterVars (Tree.leaves ft)

def Term.skolemize (ruleId : Nat) (frontier : List Variable) (t : Term) : Term :=
  match t with
    | Term.var v => ite (List.elem v frontier)
      (Term.var v)
      (Term.func (Tree.inner { ruleId := ruleId, var := v} (TreeList.fromList (List.map (fun fv => Tree.leaf (VarOrConst.var fv)) frontier))))
    | t => t

structure FunctionFreeFact where
  predicate : Predicate
  terms : List Constant

structure Fact where
  predicate : Predicate
  terms : List GroundTerm

structure Atom where
  predicate : Predicate
  terms : List Term

-- TODO: remove duplicates here maybe
def Atom.variables (a : Atom) : List Variable := List.foldl (fun acc t => acc ++ Term.variables t) List.nil a.terms

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
    List.map (fun (i, a) => {
      predicate := a.predicate,
      terms := List.map (Term.skolemize i (Rule.frontier r)) a.terms
    }) (List.enum r.head)
  }

def RuleSet := Set Rule

def FactSet := Set Fact

def Database := Set FunctionFreeFact

structure KnowledgeBase where
  db : Database
  rules : RuleSet

def GroundSubstitution := Variable -> GroundTerm

def GroundSubstitution.apply_term (σ : GroundSubstitution) : Term -> GroundTerm
  | Term.var v => σ v
  | Term.const c => GroundTerm.const c
  | Term.func ft => GroundTerm.func (Tree.mapLeaves (fun voc => match voc with
    | VarOrConst.var v => match σ v with
      | GroundTerm.const c => Tree.leaf c
      | GroundTerm.func ft => ft
    | VarOrConst.const c => Tree.leaf c
  ) ft)

def GroundSubstitution.apply_atom (σ : GroundSubstitution) (ϕ : Atom) : Fact :=
  { predicate := ϕ.predicate, terms := List.map (GroundSubstitution.apply_term σ) ϕ.terms }
def GroundSubstitution.apply_conj (σ : GroundSubstitution) (conj : Conjunction) : List Fact :=
  (List.map (GroundSubstitution.apply_atom σ)) conj

class SubsTarget (α) (β) where
  apply : GroundSubstitution -> α -> β

instance : SubsTarget Term GroundTerm where
  apply := GroundSubstitution.apply_term
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

def Trigger.sactive (trg : Trigger) (F : FactSet) : Prop :=
  Trigger.loaded trg F ∧ ¬ (
    let l : List Fact := SubsTarget.apply trg.subs (Rule.skolemize trg.rule).head
    l ⊆ F
  )

def Trigger.ractive (trg : Trigger) (F : FactSet) : Prop :=
  Trigger.loaded trg F ∧ ¬ (
    ∃ s : GroundSubstitution,
      (∀ v, List.elem v (Rule.frontier trg.rule) → s v = trg.subs v) ∧
      (
        let l : List Fact := SubsTarget.apply s trg.rule.head
        l ⊆ F
      )
  )
