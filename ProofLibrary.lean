import ProofLibrary.ChaseSequence
import ProofLibrary.FiniteTree
import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.List
import ProofLibrary.Option
import ProofLibrary.PossiblyInfiniteList
import ProofLibrary.PossiblyInfiniteTree
import ProofLibrary.Set
import ProofLibrary.SubstitutionAndHomomorphismBasics
import ProofLibrary.TermBasics
import ProofLibrary.Trigger

section
  structure FiniteSet (α) where
    S : Set α
    isFinite : ∃ L : List α, ∀ e : α, e ∈ S -> e ∈ L.toSet

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

def universallyModelsKb (lfs : List FactSet) (kb : KnowledgeBase) : Prop :=
  (∀ fs : FactSet, fs ∈ lfs.toSet -> fs.modelsKb kb) ∧
  (∀ m : FactSet,
    m.modelsKb kb ->
    ∃ (fs : FactSet) (h : GroundTermMapping),
      fs ∈ lfs.toSet ∧
      isHomomorphism h fs m 
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
