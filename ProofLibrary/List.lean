import ProofLibrary.Set

namespace List
  def toSet : List α -> Set α
    | nil => ∅
    | cons h tail => (fun e => e = h) ∪ (List.toSet tail)

  instance : Coe (List α) (Set α) where
    coe := toSet

  theorem listToSetElementAlsoListElement [BEq α] [LawfulBEq α] (L : List α) (e : α) : e ∈ L.toSet -> L.elem e := by 
    induction L with 
      | nil => intro h; contradiction
      | cons head tail ih => intro h; simp [Set.element, toSet] at h; cases h with 
        | inl left => simp [Set.element] at left; simp [left, elem]
        | inr right => simp [elem]; cases e == head with | true => rfl | false => exact (ih right) 

  theorem listGetInToSet (L : List α) (indexFin : Fin L.length) : L.get indexFin ∈ L.toSet := by
    let ⟨index, indexSmallEnough⟩ := indexFin
    cases L with
      | nil => simp [List.toSet, Set.element, Set.emptyset]; simp [List.length] at indexSmallEnough; exact absurd indexSmallEnough (Nat.not_lt_zero index)
      | cons a as => cases index with
        | zero => simp [List.get, List.toSet, Set.element, Set.union]
        | succ n => simp [List.get, List.toSet, Set.element, Set.union]; apply Or.inr; apply listGetInToSet

  theorem map_id' (L : List α) : L.map id = L := by
    induction L 
    case nil => simp [List.map]
    case cons _ _ ih => simp [List.map, ih]

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

  theorem combine_nested_map (L : List α) (f : α -> β) (g : β -> γ) : List.map g (List.map f L) = List.map (g ∘ f) L := by
    induction L 
    case nil => simp [map]
    case cons _ _ ih => simp [map, ih]

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

  theorem before_and_element_le_sum (L : List Nat) (pos : Fin (L.length)) : (L.before_index pos.val).sum + (L.get pos) ≤ L.sum := by
    let ⟨index, indexSmallEnough⟩ := pos
    cases L with
      | nil => simp [List.length] at indexSmallEnough; exact absurd indexSmallEnough (Nat.not_lt_zero index)
      | cons head tail =>
        simp [before_index]
        cases index with
          | zero => simp [sum, List.get, Nat.le_add_right]
          | succ j =>
            simp [sum, List.get]
            rw [Nat.add_assoc]
            apply Nat.add_le_add_left
            apply before_and_element_le_sum tail ⟨j, (by
              simp at indexSmallEnough
              apply Nat.lt_of_succ_lt_succ
              exact indexSmallEnough
            )⟩

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
  def enum_with_lt_from : (l : List α) -> (start totalLength : Nat) -> (start + l.length = totalLength) -> List ((Fin totalLength) × α)
    | nil => fun _ _ _ => nil
    | cons head tail => fun s tl h =>
      cons ({ val := s, isLt := (by
        rw [← h]
        simp
        apply Nat.lt_succ_of_le
        apply Nat.le_add_right
      ) }, head) (tail.enum_with_lt_from (s + 1) tl (by
        rw [← h]
        rw [Nat.add_assoc, Nat.add_comm 1 _, ← Nat.succ_eq_add_one]
        simp
      ))

  def enum_with_lt (l : List α) : List ((Fin l.length) × α) :=
    l.enum_with_lt_from 0 l.length (by simp)

  def idx_of_with_count [DecidableEq α] (l : List α) (e : α) (e_in_l : l.elem e) (c : Nat) : Fin (c + l.length) :=
    match l with 
      | nil => by contradiction
      | cons h tail => if eq : e == h then ⟨c, by simp [length]; rw [← Nat.add_zero c]; apply (Nat.add_lt_add_left (by show 0 < (tail.length + 1); apply Nat.zero_lt_of_ne_zero; apply Nat.succ_ne_zero) c)⟩ else 
        let res := tail.idx_of_with_count e (by unfold elem at e_in_l; simp [eq] at e_in_l; exact e_in_l) (c + 1) 
        ⟨res.val, by simp [length]; rw [@Nat.add_comm tail.length 1, ← Nat.add_assoc]; exact res.isLt⟩

  def idx_of [DecidableEq α] (l : List α) (e : α) (e_in_l : l.elem e) : Fin l.length :=
    let tmp_fin := l.idx_of_with_count e e_in_l 0
    have tmp_fin_isLt := tmp_fin.isLt
    ⟨tmp_fin.val, by simp at tmp_fin_isLt; exact tmp_fin_isLt⟩

  theorem idx_of_get [DecidableEq α] (l : List α) (e : α) (e_in_l : l.elem e) (isLt : (l.idx_of e e_in_l < l.length)) : l.get ⟨(l.idx_of e e_in_l).val, isLt⟩ = e := by sorry

  theorem length_enum_from (l : List α) (n m : Nat): (l.enumFrom n).length = (l.enumFrom m).length := by 
    induction l generalizing n m with 
    | nil => simp [enumFrom]
    | cons a as ih => unfold enumFrom; unfold length; simp; apply ih

  theorem length_enum (l : List α) : l.enum.length = l.length := by 
    induction l with 
    | nil => simp [enum, enumFrom]
    | cons a as ih => unfold enum at *; unfold enumFrom; unfold length; simp; rw [← ih]; apply length_enum_from
end List

