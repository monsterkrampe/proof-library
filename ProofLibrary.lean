section
  namespace Option
    def unwrap : (opt : Option α) -> (opt ≠ none) -> α
      | none, h => absurd rfl h
      | some a, _ => a

    theorem someRevertsUnwrap (opt : Option α) (h : opt ≠ none) : some (opt.unwrap h) = opt := by
      cases opt with
        | none => exact absurd rfl h
        | some x => rfl

    theorem someNotNone : opt = some x -> opt ≠ none := by
      intro h
      have noConf : some x ≠ none := by
        intro g
        exact Option.noConfusion g
      rw [h]
      exact noConf

    theorem notSomeIsNone : (∀ x, opt ≠ some x) -> opt = none := by
      intro h
      cases opt with
        | none => rfl
        | some y =>
          have someYNeqSomeY := h y
          exact absurd rfl someYNeqSomeY

  end Option

  def Set (α) := α -> Prop

  namespace Set
    def emptyset : Set α := fun _ => False
    notation:max "∅" => emptyset

    def element (e : α) (X : Set α) : Prop := X e
    infixr:75 " ∈ " => element

    def union (X Y : Set α) : Set α := fun e => e ∈ X ∨ e ∈ Y
    infixr:65 " ∪ " => union

    def subset (X Y : Set α) : Prop := ∀ e : α, e ∈ X -> e ∈ Y
    infixr:50 " ⊆ " => subset

    theorem subsetOfSelf (X : Set α) : X ⊆ X := by
      intros _ h
      exact h

    theorem subsetUnionSomethingStillSubset (a b c : Set α) : a ⊆ b -> a ⊆ b ∪ c := by
      intro aSubB e eInA
      apply Or.inl
      apply aSubB
      exact eInA
  end Set

  namespace List
    def toSet : List α -> Set α
      | nil => ∅
      | cons h tail => (fun e => e = h) ∪ (List.toSet tail)

    instance : Coe (List α) (Set α) where
      coe := toSet

    theorem listGetInToSet (L : List α) (indexFin : Fin L.length) : L.get indexFin ∈ L.toSet := by
      let ⟨index, indexSmallEnough⟩ := indexFin
      cases L with
        | nil => simp [List.toSet, Set.element, Set.emptyset]; simp [List.length] at indexSmallEnough; exact absurd indexSmallEnough (Nat.not_lt_zero index)
        | cons a as => cases index with
          | zero => simp [List.get, List.toSet, Set.element, Set.union]
          | succ n => simp [List.get, List.toSet, Set.element, Set.union]; apply Or.inr; apply listGetInToSet

    theorem mappedElemInMappedList (L : List α) (e : α) (fn : α -> β) : e ∈ L.toSet -> fn e ∈ (L.map fn).toSet := by
      intro h
      cases L with
        | nil => contradiction
        | cons a as =>
          simp [List.map, toSet, Set.element, Set.union]
          simp [toSet, Set.element, Set.union] at h
          cases h with
            | inl eIsA => apply Or.inl; rw [eIsA]
            | inr eInAs => apply Or.inr; apply mappedElemInMappedList; exact eInAs

    def sum : List Nat -> Nat
      | nil => 0
      | cons h tail => h + tail.sum

    theorem headLeSum (L : List Nat) : L = List.cons h tail -> h ≤ L.sum := by
      intro e
      rw [e]
      simp [sum]
      exact Nat.le_add_right h (sum tail)

    theorem tailSumLeSum (L : List Nat) : L = List.cons h tail -> tail.sum ≤ L.sum := by
      intro e
      rw [e]
      simp [sum]
      rw [Nat.add_comm]
      exact Nat.le_add_right (sum tail) h

    theorem everyElementLeSum (L : List Nat) : ∀ e, e ∈ L.toSet -> e ≤ L.sum := by
      intros e h
      cases L with
        | nil => simp [List.toSet, Set.element, Set.emptyset] at h
        | cons h tail =>
          simp [List.toSet, Set.element, Set.union] at h
          cases h with
            | inl hl => rw [hl]; apply headLeSum; rfl
            | inr hr =>
              have eLeThisTailSum := everyElementLeSum tail e hr
              have thisTailSumLeSum : tail.sum ≤ (h :: tail).sum := by apply tailSumLeSum; rfl
              exact Nat.le_trans eLeThisTailSum thisTailSumLeSum

    def before_index : List α -> Nat -> List α
      | nil => fun _ => nil
      | cons h tail => fun i => match i with
        | Nat.zero => nil
        | Nat.succ i => cons h (tail.before_index i)

    /- NOTE: inductive lists are always finite!
    def isFinite (l : List α) : Prop :=
      ∃ k : Nat,
        l.length <= k
    -/

    /- This already exists as List.getLast?
    def last : List α -> Option α
      | List.nil => Option.none
      | List.cons a as => match as with
        | List.nil => Option.some a
        | List.cons _ _ => as.last
    -/
  end List

  structure FiniteSet (α) where
    S : Set α
    isFinite : ∃ L : List α, ∀ e : α, e ∈ S -> e ∈ L.toSet

  def InfiniteList (α) := Nat -> α

  structure PossiblyInfiniteList (α) where
    infinite_list : InfiniteList (Option α)
    no_holes : ∀ n : Nat, infinite_list n ≠ none -> ∀ m : Nat, m < n -> infinite_list m ≠ none

  structure NEList (α) where
    list : PossiblyInfiniteList α
    non_empty : list.infinite_list 0 ≠ none

  namespace NEList
    def toList (nel : NEList α) : PossiblyInfiniteList α := nel.list

    /- NOTE: this does not really work if the list if infinite; maybe we do not need it anymore
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
    -/

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

    instance : Coe (NEList α) (PossiblyInfiniteList α) where
      coe := toList

    /- NOTE: concating does not really work for infinite lists; maybe we do not need this anymore
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
    -/
  end NEList
end

-- NOTE: Inductive Trees are always finite!
section
  mutual
      inductive FiniteTree (α : Type u) (β : Type v) where
        | leaf : β -> FiniteTree α β
        | inner : α -> FiniteTreeList α β -> FiniteTree α β

      inductive FiniteTreeList (α : Type u) (β : Type v) where
        | nil  : FiniteTreeList α β
        | cons : FiniteTree α β -> FiniteTreeList α β -> FiniteTreeList α β
  end

  namespace FiniteTreeList
    def toList : FiniteTreeList α β -> List (FiniteTree α β)
      | FiniteTreeList.nil => List.nil
      | FiniteTreeList.cons t ts => List.cons t (toList ts)

    def fromList : List (FiniteTree α β) -> FiniteTreeList α β
      | List.nil => FiniteTreeList.nil
      | List.cons t ts => FiniteTreeList.cons t (fromList ts)

    instance : Coe (FiniteTreeList α β) (List (FiniteTree α β)) where
      coe := toList

    instance : Coe (List (FiniteTree α β)) (FiniteTreeList α β) where
      coe := fromList
  end FiniteTreeList

  namespace FiniteTree
    mutual
      def depth : FiniteTree α β -> Nat
        | FiniteTree.leaf _ => 1
        | FiniteTree.inner _ ts => 1 + depthList ts

      def depthList : FiniteTreeList α β -> Nat
        | FiniteTreeList.nil => 0
        | FiniteTreeList.cons t ts => max (depth t) (depthList ts)
    end

    mutual
      def leaves : FiniteTree α β -> List β
        | FiniteTree.leaf b => List.cons b List.nil
        | FiniteTree.inner _ ts => leavesList ts

      def leavesList : FiniteTreeList α β -> List β
        | FiniteTreeList.nil => List.nil
        | FiniteTreeList.cons t ts => (leaves t) ++ (leavesList ts)
    end

    mutual
      def mapLeaves (f : β -> FiniteTree α γ) (t : FiniteTree α β) : FiniteTree α γ := match t with
        | FiniteTree.leaf b => f b
        | FiniteTree.inner a ts => FiniteTree.inner a (mapLeavesList f ts)

      def mapLeavesList (f : β -> FiniteTree α γ) (ts : FiniteTreeList α β) : FiniteTreeList α γ := match ts with
        | FiniteTreeList.nil => FiniteTreeList.nil
        | FiniteTreeList.cons t ts => FiniteTreeList.cons (mapLeaves f t) (mapLeavesList f ts)
    end

    def nodeLabel : FiniteTree α α -> α
      | FiniteTree.leaf a => a
      | FiniteTree.inner a _ => a

    -- check that f holds for each node in the tree
    mutual
      def forEach (t : FiniteTree α β) (f : (FiniteTree α β) -> Prop) : Prop :=
        match t with
          | FiniteTree.leaf _ => f t
          | FiniteTree.inner _ ts => (f t) ∧ (forEachList ts f)

      def forEachList (ts : FiniteTreeList α β) (f : (FiniteTree α β) -> Prop) : Prop :=
        match ts with
          | FiniteTreeList.nil => True
          | FiniteTreeList.cons t ts => (forEach t f) ∧ (forEachList ts f)
    end

    mutual
      def privateNodesInDepthK (t : FiniteTree α β) (depth : Nat) (currentDepth : Nat) : List (FiniteTree α β) :=
        ite (currentDepth > depth) [] (
          ite (currentDepth = depth) [t] (match t with
            | FiniteTree.leaf _ => [t]
            | FiniteTree.inner _ ts => privateNodesInDepthKList ts depth (currentDepth + 1)
          )
        )

      def privateNodesInDepthKList (ts : FiniteTreeList α β) (depth : Nat) (currentDepth : Nat) : List (FiniteTree α β) :=
        ite (currentDepth > depth) [] (
          ite (currentDepth = depth) ts.toList (match ts with
            | FiniteTreeList.nil => []
            | FiniteTreeList.cons t ts => (privateNodesInDepthK t depth currentDepth) ++ (privateNodesInDepthKList ts depth currentDepth)
          )
        )
    end

    def nodesInDepthK (t : FiniteTree α β) (depth : Nat) : List (FiniteTree α β) := t.privateNodesInDepthK depth 0
  end FiniteTree

  structure NodeInformation (α) where
    value : α
    number_of_children : Nat

  structure PossiblyInfiniteTree (α : Type u) where
    data : PossiblyInfiniteList (List (NodeInformation α))
    consistency : ∀ depth : Nat, match (data.infinite_list depth) with
      | none => True
      | some list => match (list.map (fun ni => ni.number_of_children)).sum with
        | Nat.zero => (data.infinite_list (depth + 1)) = none
        | Nat.succ n => (data.infinite_list (depth + 1)) = some next_layer ∧ next_layer.length = Nat.succ n

  structure NodeInPossiblyInfiniteTree (α) where
    tree : PossiblyInfiniteTree α
    depth : Nat
    position_in_layer : Nat
    layer_exists : ∃ layer, tree.data.infinite_list depth = some layer
    layer_large_enough : ∀ layer, tree.data.infinite_list depth = some layer -> position_in_layer < layer.length

  namespace NodeInPossiblyInfiniteTree
    def layer (node : NodeInPossiblyInfiniteTree α) : List (NodeInformation α) :=
      let layer_opt := node.tree.data.infinite_list node.depth
      let layer := layer_opt.unwrap (by
        cases node.layer_exists with | intro x h =>
          exact layer_opt.someNotNone h
      )
      layer

    theorem nodeLayerIsLayerAtDepth (node : NodeInPossiblyInfiniteTree α) : node.tree.data.infinite_list node.depth = some node.layer := by
      cases node.layer_exists with | intro x h =>
        simp [layer]
        rw [Option.someRevertsUnwrap]

    def node_info (node : NodeInPossiblyInfiniteTree α) : NodeInformation α :=
      let layer := node.layer
      layer.get ⟨node.position_in_layer, (by
        have h := node.layer_large_enough layer
        apply h
        rw [nodeLayerIsLayerAtDepth]
      )⟩

    theorem nodeInfoIsInLayer (node : NodeInPossiblyInfiniteTree α) : node.node_info ∈ node.layer.toSet := by
      simp [node_info]
      apply List.listGetInToSet

    /-
    def children (node : NodeInPossiblyInfiniteTree α) : List (NodeInPossiblyInfiniteTree α) :=
      let current_layer := node.layer
      let next_layer_opt := node.tree.data.infinite_list (node.depth + 1)
      let current_layer_before_this := current_layer.before_index node.position_in_layer
      let node_info := node.node_info
      let number_of_children := node_info.number_of_children
      let layer_mapped := current_layer.map (fun ni => ni.number_of_children)

      have no_children_in_mapped_layer : number_of_children ∈ layer_mapped.toSet := by
        apply List.mappedElemInMappedList
        apply nodeInfoIsInLayer

      have no_children_le_sum_layer_mapped : number_of_children ≤ layer_mapped.sum := by
        apply List.everyElementLeSum
        exact no_children_in_mapped_layer

      match equality : number_of_children with
        | Nat.zero => List.nil
        | Nat.succ n =>
          have consistency := node.tree.consistency node.depth
          -- TODO: continue here
          have something := by
            simp [nodeLayerIsLayerAtDepth] at consistency

          sorry
    -/

    /- TODO: maybe also define siblings similarly, i.e. as node.layer but with NodeInPossiblyInfiniteTree instead of just NodeInformation -/
  end NodeInPossiblyInfiniteTree
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
    | func (ft : FiniteTree SkolemFS Constant) : GroundTerm

  def GroundTerm.depth : GroundTerm -> Nat
    | GroundTerm.const _ => 0
    | GroundTerm.func ft => FiniteTree.depth ft

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
    | func (ft : FiniteTree SkolemFS VarOrConst) : Term

  def GroundTerm.toTerm : GroundTerm -> Term
    | GroundTerm.const c => Term.const c
    | GroundTerm.func ft => Term.func (FiniteTree.mapLeaves (fun c => FiniteTree.leaf (VarOrConst.const c)) ft)

  instance : Coe GroundTerm Term where
    coe := GroundTerm.toTerm

  def Term.variables : Term -> List Variable
    | Term.var v => List.cons v List.nil
    | Term.const _ => List.nil
    | Term.func ft => VarOrConst.filterVars ft.leaves

  def Term.skolemize (ruleId : Nat) (frontier : List Variable) (t : Term) : Term :=
    match t with
      | Term.var v => ite (List.elem v frontier)
        (Term.var v)
        (Term.func (FiniteTree.inner { ruleId := ruleId, var := v} (FiniteTreeList.fromList (List.map (fun fv => FiniteTree.leaf (VarOrConst.var fv)) frontier))))
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
        | _ => { id := 0 } -- TODO: this cannot happen since we check before that everything is a constant
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
/-
section
  -- SkolemChaseTree
  structure ChaseTree where
    kb : KnowledgeBase
    tree : Tree (FactSet × (Option Trigger)) (FactSet × (Option Trigger))
    -- 1. we have nodes, edges, fact labels and trigger labels (no need to check this)
    -- 2. root is labeled with (db, none)
    rootIsDb : tree.nodeLabel.fst = kb.db ∧ tree.nodeLabel.snd = Option.none
    -- 3. children of nodes are labeled properly
    childLabelsConsistent : (Tree.forEach tree (fun t => match t with
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
    -- 4a. leaf nodes are closed under all rules
    leafNodesClosed : (Tree.forEach tree (fun t => match t with
        | Tree.inner _ _ => True
        | Tree.leaf ⟨fs, _⟩ =>
          ∀ trg : Trigger, ¬ (trg.sactive fs)
      ))
    -- 4b. triggers are not active after finitely many steps (fairness)
    fair : (∀ trg : Trigger, ∃ k : Nat,
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
      ChaseTree.privateBranches ct.tree { list := [ct.tree], non_empty := by
        constructor
        constructor
        case w => exact ct.tree
        case h.w => exact []
        case h.h => rfl
      }

    /- NOTE: since our chase trees are inductive trees, every chase tree is finite
    def terminates (ct : ChaseTree) : Prop :=
      ∀ b, b ∈ ct.branches.toSet -> b.toList.isFinite
    -/

    def result (ct : ChaseTree) : List FactSet :=
      ct.branches.map (fun b => match b.last.nodeLabel with | ⟨fs, _⟩ => fs)

    -- TODO: theorem childFsSuperSet (c p : Tree (FactSet × (Option Trigger)) :
  end ChaseTree
end

theorem ChaseResultIsUniversalModel (ct : ChaseTree) (kb : KnowledgeBase) : ct.kb = kb -> universallyModelsKb ct.result kb := by
  intro kbIsKb
  constructor

  case left =>
    intros fs fsInCt
    constructor
    case left =>
      have ⟨rootIsDb, _⟩ := ct.rootIsDb
      have dbSubSetRoot : kb.db.toFactSet ⊆ (Tree.nodeLabel ct.tree).fst := by
        rw [rootIsDb, kbIsKb]
        apply Set.subsetOfSelf

      sorry
    case right =>
      sorry

  case right =>
    intro m mModelsKb
    sorry
-/
