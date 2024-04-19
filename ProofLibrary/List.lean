import ProofLibrary.Set

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

  -- TODO: is there some more idiomatic way to get a lt proof with indices in enum?
  structure IndexWithLt (length : Nat) where
    index : Nat
    lt : index < length

  def enum_with_lt_from : (l : List α) -> (start totalLength : Nat) -> (start + l.length = totalLength) -> List ((IndexWithLt totalLength) × α)
    | nil => fun _ _ _ => nil
    | cons head tail => fun s tl h =>
      cons ({ index := s, lt := (by
        rw [← h]
        simp
        apply Nat.lt_succ_of_le
        apply Nat.le_add_right
      ) }, head) (tail.enum_with_lt_from (s + 1) tl (by
        rw [← h]
        rw [Nat.add_assoc, Nat.add_comm 1 _, ← Nat.succ_eq_add_one]
        simp
      ))

  def enum_with_lt (l : List α) : List ((IndexWithLt l.length) × α) :=
    l.enum_with_lt_from 0 l.length (by simp)
end List
