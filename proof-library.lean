section
  def Set (α) := α -> Prop

  namespace Set
    def emptyset : Set α := fun _ => False
    notation:max "∅" => emptyset

    def element (e : α) (X : Set α) : Prop := X e
    infixr:75 " ∈ " => element

    def union (X Y : Set α) : Set α := fun e => e ∈ X ∨ e ∈ Y
    infixr:65 " ∪ " => union

    def subset (X Y : Set α) : Prop := ∀ e : α, e ∈ X → e ∈ Y
    infixr:50 " ⊆ " => subset
  end Set

  namespace List
    def toSet : List α -> Set α
      | nil => ∅
      | cons h tail => (fun e => e = h) ∪ (List.toSet tail)

    instance : Coe (List α) (Set α) where
      coe := toSet

    def isFinite (l : List α) : Prop :=
      ∃ k : Nat,
        l.length <= k

    /- This already exists as List.getLast?
    def last : List α -> Option α
      | List.nil => Option.none
      | List.cons a as => match as with
        | List.nil => Option.some a
        | List.cons _ _ => as.last
    -/
  end List

  theorem subsetUnionSomethingStillSubset (a b c : Set α) : a ⊆ b -> a ⊆ b ∪ c := by
    intro aSubB e eInA
    apply Or.inl
    apply aSubB
    exact eInA

  structure NEList (α) where
    list : List α
    non_empty : ∃ h t, list = List.cons h t

  namespace NEList
    def toList (nel : NEList α) : List α := nel.list

    def last (nel : NEList α) : α := nel.list.getLast (by
      cases nel.non_empty
      case intro head tailhyp =>
        cases tailhyp
        case intro tail h =>
          intro hn

          have g : head :: tail ≠ [] := fun g' => List.noConfusion g'
          rw [← h] at g
          exact absurd hn g
    )

    /-
    def last (ne : NEList α) : α :=
      match ne.list with
        | List.nil =>
          let h : ne.list = List.nil := sorry
          let hn : ne.list ≠ List.nil := sorry
          absurd h hn
        | List.cons a as => match as.last with
          | Option.none => a
          | Option.some a' => a'
    -/

    instance : Coe (NEList α) (List α) where
      coe := toList

    theorem concatAlsoNonEmpty (ne : NEList α) (l : List α) : ∃ h t, (NEList.toList ne) ++ l = h :: t := by
      let branch_ne := ne.non_empty
      cases branch_ne
      case intro hne thne =>
        cases thne
        case intro tne hypne =>
          constructor
          constructor
          case w => exact hne
          case h.w => exact tne ++ l
          case h.h =>
            have essentially_goal : ne.list ++ l = hne :: (tne ++ l) := by
              rw [hypne]
              rfl
            exact essentially_goal
  end NEList
end

section
  mutual
      inductive Tree (α : Type u) (β : Type v) where
        | leaf : β -> Tree α β
        | inner : α -> TreeList α β -> Tree α β

      inductive TreeList (α : Type u) (β : Type v)where
        | nil  : TreeList α β
        | cons : Tree α β -> TreeList α β -> TreeList α β
  end

  namespace TreeList
    def toList : TreeList α β -> List (Tree α β)
      | TreeList.nil => List.nil
      | TreeList.cons t ts => List.cons t (toList ts)

    def fromList : List (Tree α β) -> TreeList α β
      | List.nil => TreeList.nil
      | List.cons t ts => TreeList.cons t (fromList ts)

    instance : Coe (TreeList α β) (List (Tree α β)) where
      coe := toList

    instance : Coe (List (Tree α β)) (TreeList α β) where
      coe := fromList
  end TreeList

  namespace Tree
    mutual
      def depth : Tree α β -> Nat
        | Tree.leaf _ => 1
        | Tree.inner _ ts => 1 + depthList ts

      def depthList : TreeList α β -> Nat
        | TreeList.nil => 0
        | TreeList.cons t ts => max (depth t) (depthList ts)
    end

    mutual
      def leaves : Tree α β -> List β
        | Tree.leaf b => List.cons b List.nil
        | Tree.inner _ ts => leavesList ts

      def leavesList : TreeList α β -> List β
        | TreeList.nil => List.nil
        | TreeList.cons t ts => (leaves t) ++ (leavesList ts)
    end

    mutual
      def mapLeaves (f : β -> Tree α γ) (t : Tree α β) : Tree α γ := match t with
        | Tree.leaf b => f b
        | Tree.inner a ts => Tree.inner a (mapLeavesList f ts)

      def mapLeavesList (f : β -> Tree α γ) (ts : TreeList α β) : TreeList α γ := match ts with
        | TreeList.nil => TreeList.nil
        | TreeList.cons t ts => TreeList.cons (mapLeaves f t) (mapLeavesList f ts)
    end

    def nodeLabel : Tree α α -> α
      | Tree.leaf a => a
      | Tree.inner a _ => a

    -- check that f holds for each node in the tree
    mutual
      def forEach (t : Tree α β) (f : (Tree α β) -> Prop) : Prop :=
        match t with
          | Tree.leaf _ => f t
          | Tree.inner _ ts => (f t) ∧ (forEachList ts f)

      def forEachList (ts : TreeList α β) (f : (Tree α β) -> Prop) : Prop :=
        match ts with
          | TreeList.nil => True
          | TreeList.cons t ts => (forEach t f) ∧ (forEachList ts f)
    end

    mutual
      def privateNodesInDepthK (t : Tree α β) (depth : Nat) (currentDepth : Nat) : List (Tree α β) :=
        ite (currentDepth > depth) [] (
          ite (currentDepth = depth) [t] (match t with
            | Tree.leaf _ => [t]
            | Tree.inner _ ts => privateNodesInDepthKList ts depth (currentDepth + 1)
          )
        )

      def privateNodesInDepthKList (ts : TreeList α β) (depth : Nat) (currentDepth : Nat) : List (Tree α β) :=
        ite (currentDepth > depth) [] (
          ite (currentDepth = depth) ts.toList (match ts with
            | TreeList.nil => []
            | TreeList.cons t ts => (privateNodesInDepthK t depth currentDepth) ++ (privateNodesInDepthKList ts depth currentDepth)
          )
        )
    end

    def nodesInDepthK (t : Tree α β) (depth : Nat) : List (Tree α β) := t.privateNodesInDepthK depth 0
  end Tree
end

section
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
end

section
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
    List.filter (fun v => r.head.vars.elem v) (Conjunction.vars r.body)

  def Rule.skolemize (r : Rule) : Rule :=
    { body := r.body, head :=
      List.map (fun (i, a) => {
        predicate := a.predicate,
        terms := List.map (Term.skolemize i (Rule.frontier r)) a.terms
      }) (List.enum r.head)
    }

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
        | _ => { id := 0 } -- TODO: this cannot happen since we check before the everything is a constant
      ) f.terms) }))
      (Option.none)

  def Database.toFactSet (db : Database) : FactSet := fun x => match (Fact.toFunctionFreeFact x) with
    | Option.none => False
    | Option.some fff => fff ∈ db

  instance : Coe Database FactSet where
    coe := Database.toFactSet
end

section
  def GroundSubstitution := Variable -> GroundTerm

  namespace GroundSubstitution
    def apply_term (σ : GroundSubstitution) : Term -> GroundTerm
      | Term.var v => σ v
      | Term.const c => GroundTerm.const c
      | Term.func ft => GroundTerm.func (Tree.mapLeaves (fun voc => match voc with
        | VarOrConst.var v => match σ v with
          | GroundTerm.const c => Tree.leaf c
          | GroundTerm.func ft => ft
        | VarOrConst.const c => Tree.leaf c
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
end

section
  structure Trigger where
    rule : Rule
    subs : GroundSubstitution

  namespace Trigger
    def loaded (trg : Trigger) (F : FactSet) : Prop :=
      let l : List Fact := SubsTarget.apply trg.subs trg.rule.body
      l ⊆ F

    def sactive (trg : Trigger) (F : FactSet) : Prop :=
      loaded trg F ∧ ¬ (
        let l : List Fact := SubsTarget.apply trg.subs (Rule.skolemize trg.rule).head
        l ⊆ F
      )

    def ractive (trg : Trigger) (F : FactSet) : Prop :=
      loaded trg F ∧ ¬ (
        ∃ s : GroundSubstitution,
          (∀ v, List.elem v (Rule.frontier trg.rule) → s v = trg.subs v) ∧
          (
            let l : List Fact := SubsTarget.apply s trg.rule.head
            l ⊆ F
          )
      )

    def result (trg : Trigger) : FactSet :=
      let l : List Fact := SubsTarget.apply trg.subs (Rule.skolemize trg.rule).head
      List.toSet l
  end Trigger
end

section
  def isHomomorphism (h : GroundTerm -> GroundTerm) : Prop :=
    ∀ t : GroundTerm, match t with
      | GroundTerm.const _ => h t = t
      | _ => True

  def applyFact (h : GroundTerm -> GroundTerm) (f : Fact) : Fact :=
    { predicate := f.predicate, terms := List.map h f.terms }

  def applyFactSet (h : GroundTerm -> GroundTerm) (fs : FactSet) : FactSet :=
    fun f' : Fact => ∃ f : Fact, (f ∈ fs) ∧ ((applyFact h f) = f')
end

namespace FactSet
  def modelsDb (fs : FactSet) (db : Database) : Prop :=
    db.toFactSet ⊆ fs

  def modelsRule (fs : FactSet) (rule : Rule) : Prop :=
    ∀ trg : Trigger,
      (trg.rule = rule ∧ trg.loaded fs)
      -> ¬ trg.ractive fs -- the rule is ractive iff it is not satisfied under FOL semantics

  def modelsRules (fs : FactSet) (rules : RuleSet) : Prop :=
    ∀ r, r ∈ rules -> fs.modelsRule r

  def modelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsDb kb.db ∧ fs.modelsRules kb.rules
end FactSet

def universallyModelsKb (lfs : List FactSet) (kb : KnowledgeBase) : Prop :=
  (∀ fs : FactSet, fs ∈ lfs.toSet -> fs.modelsKb kb) ∧
  (∀ m : FactSet,
    m.modelsKb kb ->
    ∃ (fs : FactSet) (h : GroundTerm -> GroundTerm),
      fs ∈ lfs.toSet ∧
      isHomomorphism h ∧
      (applyFactSet h fs) ⊆ m
  )

section
  structure ChaseTree where
    kb : KnowledgeBase
    tree : Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger))
    isSkolem :
      -- 1. we have nodes, edges, fact labels and trigger labels (no need to check this)
      -- 2. root is labeled with (db, none)
      (match Tree.nodeLabel tree with
        | ⟨fs, otrg⟩ => fs = kb.db ∧ otrg = Option.none)
      ∧
      -- 3. children of nodes are labeled properly
      (Tree.forEach tree (fun t => match t with
        | Tree.leaf _ => True
        | Tree.inner ⟨fs, _⟩ children =>
          ∃ trg : Trigger,
            trg.sactive fs
            ∧
            children.toList.length = 1
            ∧
            (∀ c : Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger)),
              c ∈ children.toList.toSet -> match c.nodeLabel with
              | ⟨cfs, cotrg⟩ => cfs = (fs ∪ trg.result) ∧ match cotrg with
                | Option.none => False
                | Option.some ctrg => ctrg = trg)
            ∧
            ((not trg.rule.isDatalog) -> ∀ dltrg : Trigger,
              dltrg.rule.isDatalog -> ¬ (dltrg.sactive fs))
      ))
      ∧
      -- 4a. leaf nodes are closed under all rules
      (Tree.forEach tree (fun t => match t with
        | Tree.inner _ _ => True
        | Tree.leaf ⟨fs, _⟩ =>
          ∀ trg : Trigger, ¬ (trg.sactive fs)
      ))
      ∧
      -- 4b. triggers are not active after finitely many steps (fairness)
      (∀ trg : Trigger, ∃ k : Nat,
        ∀ fs : FactSet, fs ∈ (List.map (fun t => match t with | Tree.leaf ⟨fs, _⟩ => fs | Tree.inner ⟨fs, _⟩ _ => fs) (tree.nodesInDepthK k)).toSet -> ¬ (trg.sactive fs)
      )

  namespace ChaseTree
    mutual
      def privateBranches (t : Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger))) (branch : NEList (Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger)))) : List (NEList (Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger)))) :=
        match t with
          | Tree.leaf _ => [{ list := branch ++ [t], non_empty := NEList.concatAlsoNonEmpty branch [t]}]
          | Tree.inner _ ts => ChaseTree.privateBranchesList ts { list := branch ++ [t], non_empty := NEList.concatAlsoNonEmpty branch [t] }
          --List.foldl (fun acc t' => acc ++ ChaseTree.privateBranches t' (branch ++ [t])) List.nil ts

      def privateBranchesList (ts : TreeList (FactSet × (Option Trigger)) (FactSet × (Option Trigger))) (branch : NEList (Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger)))) : List (NEList (Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger)))) :=
        match ts with
          | TreeList.nil => []
          | TreeList.cons t ts' => (ChaseTree.privateBranches t branch) ++ (ChaseTree.privateBranchesList ts' branch)
    end

    def branches (ct : ChaseTree) : List (NEList (Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger)))) :=
      [{ list := [ct.tree], non_empty := by
        constructor
        constructor
        case w => exact ct.tree
        case h.w => exact []
        case h.h => rfl
      }]

    def terminates (ct : ChaseTree) : Prop :=
      ∀ b, b ∈ ct.branches.toSet -> b.toList.isFinite

    def result (ct : ChaseTree) : List FactSet :=
      ct.branches.map (fun b => match b.last.nodeLabel with | ⟨fs, _⟩ => fs)
  end ChaseTree
end

theorem ChaseResultIsUniversalModel (ct : ChaseTree) (kb : KnowledgeBase) : ct.kb = kb -> universallyModelsKb ct.result kb := by
  intro h
  constructor

  case left =>
    intros fs fsInCt
    constructor
    case left =>
      sorry
    case right =>
      sorry

  case right =>
    intro m mModelsKb
    sorry
