import ProofLibrary.Set
import ProofLibrary.Option

section
  -- copied from mathlib
  theorem Nat.min_le_right (a b : Nat) : min a b ≤ b := by rw [Nat.min_def]; split; trivial; simp
  theorem Nat.min_le_left (a b : Nat) : min a b ≤ a := by 
    rw [Nat.min_def]
    split 
    simp 
    cases Nat.lt_or_ge a b with 
    | inl hl => have : a ≤ b := Nat.le_of_lt hl; contradiction
    | inr hr => trivial
  theorem Nat.min_eq_left {a b : Nat} (h : a ≤ b) : min a b = a := by simp [Nat.min_def, h]
  theorem Nat.min_eq_right {a b : Nat} (h : b ≤ a) : min a b = b := by 
    simp [Nat.min_def]
    cases Nat.eq_or_lt_of_le h with  
    | inl hl => simp [hl] 
    | inr hr => simp [Nat.not_le_of_gt hr]
  theorem Nat.zero_min (a : Nat) : min 0 a = 0 := Nat.min_eq_left (zero_le a)
  theorem Nat.min_zero (a : Nat) : min a 0 = 0 := Nat.min_eq_right (zero_le a)
  theorem Nat.succ_le_succ_iff {a b : Nat} : succ a ≤ succ b ↔ a ≤ b :=
    ⟨le_of_succ_le_succ, succ_le_succ⟩
  theorem Nat.min_succ_succ (x y : Nat) : min (succ x) (succ y) = succ (min x y) := by
    simp [Nat.min_def, Nat.succ_le_succ_iff]; split <;> rfl

  theorem List.take_succ_cons : (a :: as).take (i + 1) = a :: as.take i := rfl
  theorem List.length_take : ∀ (i : Nat) (l : List α), length (take i l) = min i (length l)
    | 0, l => by simp [List.length, Nat.zero_min]
    | Nat.succ n, [] => by simp [List.length, Nat.min_zero]
    | Nat.succ n, _ :: l => by simp [Nat.min_succ_succ, Nat.add_one, length_take, take_succ_cons]
  theorem List.length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [List.length_take, Nat.min_le_left]

  theorem List.get?_eq_get : ∀ {l : List α} {n} (h : n < l.length), l.get? n = some (get l ⟨n, h⟩)
  | _ :: _, 0, _ => rfl
  | _ :: l, _+1, _ => get?_eq_get (l := l) _
  theorem List.get?_map (f : α → β) : ∀ l n, (map f l).get? n = (l.get? n).map f
    | [], _ => rfl
    | _ :: _, 0 => rfl
    | _ :: l, n+1 => get?_map f l n
  theorem List.get_map (f : α → β) {l n} : get (map f l) n = f (get l ⟨n, length_map l f ▸ n.2⟩) := 
    Option.some.inj <| by rw [← get?_eq_get, get?_map, get?_eq_get]; rfl
end 

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

  theorem idx_of_with_count_succ [DecidableEq α] (l : List α) (e : α) (e_in_l : l.elem e) (c : Nat) : (idx_of_with_count l e e_in_l (c + 1)).val = (idx_of_with_count l e e_in_l c).val + 1 := by
    induction l generalizing c with 
    | nil => contradiction
    | cons b bs ih =>
      unfold idx_of_with_count
      by_cases e == b
      case inl hl => simp [hl]
      case inr hr => simp [hr]; apply ih

  def idx_of [DecidableEq α] (l : List α) (e : α) (e_in_l : l.elem e) : Fin l.length :=
    let tmp_fin := l.idx_of_with_count e e_in_l 0
    have tmp_fin_isLt := tmp_fin.isLt
    ⟨tmp_fin.val, by simp at tmp_fin_isLt; exact tmp_fin_isLt⟩

  theorem get_prepend_succ [DecidableEq α] (l : List α) (a : α) (i : Fin l.length) (j : Fin (a::l).length) (h : j = Fin.succ i) : l.get i = (a::l).get j := by rw [h]; simp [get]

  theorem idx_of_prepend_succ [DecidableEq α] (l : List α) (e a : α) (e_in_l : l.elem e) (h : e ≠ a) : ((a::l).idx_of e (by unfold elem; split <;> trivial)) = Fin.succ (l.idx_of e e_in_l) := by 
    simp [idx_of, idx_of_with_count, h, Fin.succ]
    apply idx_of_with_count_succ

  theorem idx_of_get [DecidableEq α] (l : List α) (e : α) (e_in_l : l.elem e) (isLt : (l.idx_of e e_in_l < l.length)) : e = l.get ⟨(l.idx_of e e_in_l).val, isLt⟩ := by 
    induction l with 
    | nil => contradiction
    | cons a as ih =>
      by_cases h : e = a
      . simp [get, h, idx_of, idx_of_with_count]
      . have e_in_as : as.elem e := by 
          unfold elem at e_in_l
          split at e_in_l 
          case h_1 heq => 
            have : e = a := LawfulBEq.eq_of_beq heq
            contradiction
          case h_2 => trivial
        have isLt_as : (as.idx_of e e_in_as).val < as.length := by 
          exact (as.idx_of e e_in_as).isLt
        have ih_plugged_in := ih e_in_as isLt_as    
        apply Eq.trans 
        exact ih_plugged_in
        rw [get_prepend_succ as a (as.idx_of e e_in_as) ((a::as).idx_of e e_in_l) (idx_of_prepend_succ as e a e_in_as h)]

  theorem length_enum_from (l : List α) (n m : Nat): (l.enumFrom n).length = (l.enumFrom m).length := by 
    induction l generalizing n m with 
    | nil => simp [enumFrom]
    | cons a as ih => unfold enumFrom; unfold length; simp; apply ih

  theorem length_enum_from' (l : List α) (n : Nat) : (l.enumFrom n).length = l.length := by 
    induction l generalizing n with
    | nil => simp [enumFrom]
    | cons a as ih => unfold enumFrom; unfold length; simp; apply ih

  theorem length_enum (l : List α) : l.enum.length = l.length := by 
    induction l with 
    | nil => simp [enum, enumFrom]
    | cons a as ih => unfold enum at *; unfold enumFrom; unfold length; simp; rw [← ih]; apply length_enum_from

  theorem get_enum_from (l : List α) (n : Nat) (i : Fin l.length) : (l.enumFrom n).get ⟨i.val, (by rw [l.length_enum_from' n]; exact i.isLt)⟩ = (n + i.val, l.get i) := by 
    rw [← Option.someInj, ← get?_eq_get]
    induction l generalizing n with
    | nil => have : i.val < 0 := i.isLt; contradiction
    | cons a as ih => cases eq : i.val with 
      | zero => simp [get?, enumFrom]; rw [← Option.someInj, ← get?_eq_get]; rw [eq]; simp[get?]
      | succ j => 
        simp [get?, enumFrom]
        let jFin : Fin as.length := ⟨j, (by have isLt := i.isLt; unfold length at isLt; rw [eq] at isLt; apply Nat.lt_of_succ_lt_succ; exact isLt)⟩ 
        rw [ih (n+1) jFin]
        simp 
        constructor
        . rw [Nat.add_assoc, Nat.add_comm 1 j]
        . rw [← Option.someInj, ← get?_eq_get, ← get?_eq_get]; rw [eq]; simp [get?]

  theorem get_enum (l : List α) (i : Fin l.length) : l.enum.get ⟨i.val, (by rw [length_enum]; exact i.isLt)⟩ = (i.val, l.get i) := by 
    unfold enum
    simp [get_enum_from]
end List

