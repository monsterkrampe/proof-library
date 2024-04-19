import ProofLibrary.Set
import ProofLibrary.Option

section
  -- copied from mathlib
  theorem Nat.min_succ_succ (x y : Nat) : min (succ x) (succ y) = succ (min x y) := by
    simp [Nat.min_def, Nat.succ_le_succ_iff]; split <;> rfl

  theorem List.take_succ_cons : (a :: as).take (i + 1) = a :: as.take i := rfl
  theorem List.length_take : ∀ (i : Nat) (l : List α), length (take i l) = min i (length l)
    | 0, l => by simp [List.length, Nat.zero_min]
    | Nat.succ n, [] => by simp [List.length, Nat.min_zero]
    | Nat.succ n, _ :: l => by simp [Nat.min_succ_succ, Nat.add_one, length_take, take_succ_cons]
  theorem List.length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [List.length_take, Nat.min_le_left]

  theorem List.get_map (f : α → β) {l n} : get (map f l) n = f (get l ⟨n, length_map l f ▸ n.2⟩) := 
    Option.some.inj <| by rw [← get?_eq_get, get?_map, get?_eq_get]; rfl
end 

namespace List
  def toSet : List α -> Set α
    | nil => ∅
    | cons h tail => (fun e => e = h) ∪ (List.toSet tail)

  theorem inIffInToSet (l : List α) (e : α) : e ∈ l ↔ e ∈ l.toSet := by 
    induction l with 
    | nil => constructor <;> (intros; contradiction)
    | cons a as ih => 
      constructor
      . intro h_in; simp at h_in; cases h_in with 
        | inl h_in_head => left; unfold Set.element; rw [h_in_head]
        | inr h_in_tail => right; rw [← ih]; exact h_in_tail
      . intro h_in; simp; cases h_in with 
        | inl h_in_head => left; unfold Set.element at h_in_head; rw [h_in_head]
        | inr h_in_tail => right; rw [ih]; exact h_in_tail

  theorem listToSetElementAlsoListElement [BEq α] [LawfulBEq α] (L : List α) (e : α) : e ∈ L.toSet -> L.elem e := by 
    induction L with 
      | nil => intros; contradiction
      | cons head tail ih => intro h; simp [Set.element, toSet] at h; cases h with 
        | inl left => simp [Set.element] at left; simp [left, elem]
        | inr right => simp [elem]; cases e == head with | true => rfl | false => exact (ih right) 

  theorem listElementAlsoToSetElement [BEq α] [LawfulBEq α] (L : List α) (e : α) : L.elem e -> e ∈ L.toSet := by 
    induction L with  
      | nil => intros; contradiction 
      | cons head tail ih => 
        unfold elem; unfold Set.element; unfold toSet; split 
        case h_1 _ h => intros; apply Or.inl; unfold Set.element; apply LawfulBEq.eq_of_beq; exact h
        case h_2 => intro h; apply Or.inr; apply ih; apply h

  theorem listElementIffToSetElement [BEq α] [LawfulBEq α] (L : List α) (e : α) : L.elem e ↔ e ∈ L.toSet := by 
    constructor; apply listElementAlsoToSetElement; apply listToSetElementAlsoListElement

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

  theorem exElemInMappedListMeansOriginalElemExistsThatMapsToIt [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] (L : List α) (f : α -> β) (e : β): List.elem e (L.map f) -> (∃ e', List.elem e' L ∧ e = f e') := by 
    induction L with 
    | nil => intros; contradiction
    | cons head tail ih =>
      intro he 
      simp [elem, map] at he
      split at he
      . exists head; constructor; simp [elem]; apply LawfulBEq.eq_of_beq; assumption
      . cases ih he with | intro e' he' => 
        exists e'
        constructor 
        . unfold elem; split; rfl; exact he'.left
        . exact he'.right

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
      case pos hl => simp [hl]
      case neg hr => simp [hr]; apply ih

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

  theorem idx_of_with_count_eq_of_list_eq [DecidableEq α] (l l' : List α) (h : l = l') (e : α) (he : l.elem e) : ∀ c, (l.idx_of_with_count e he c).val = (l'.idx_of_with_count e (by rw [← h]; exact he) c).val := by 
    cases l with 
    | nil => cases l'; simp; contradiction
    | cons head tail => cases l' with 
      | nil => contradiction 
      | cons head' tail' => 
        have heads_eq : head = head' := by injection h
        have tails_eq : tail = tail' := by injection h
        simp [idx_of_with_count] 
        split
        case inl he => simp [he, heads_eq]
        case inr he => simp [heads_eq] at he; simp [he]; intro c; apply idx_of_with_count_eq_of_list_eq; apply tails_eq

  theorem idx_of_eq_of_list_eq [DecidableEq α] (l l' : List α) (h : l = l') (e : α) (he : l.elem e) : (l.idx_of e he).val = (l'.idx_of e (by rw [← h]; exact he)).val := by 
    apply idx_of_with_count_eq_of_list_eq
    apply h

  theorem idx_of_with_count_eq_under_map [DecidableEq α] [DecidableEq β] (l : List α) (e : α) (he : l.elem e) (f : α -> β) (hf : ∀ e', e' ∈ l.toSet ∧ f e = f e' -> e = e') : ∀ c, (l.idx_of_with_count e he c).val = ((l.map f).idx_of_with_count (f e) (by apply listToSetElementAlsoListElement; apply mappedElemInMappedList; apply listElementAlsoToSetElement; exact he) c).val := by
    induction l with 
    | nil => contradiction 
    | cons head tail ih => 
      intro c 
      simp [idx_of_with_count]
      split 
      case inl he => simp [he]
      case inr he => 
        have : ¬ f e = f head := by 
          intro hcontra; 
          have : e = head := by apply hf; constructor; unfold toSet; apply Or.inl; rfl; apply hcontra
          contradiction
        simp [this]
        apply ih
        intro e' ⟨e'InTail, feEqfe'⟩
        apply hf
        constructor 
        apply Or.inr
        apply e'InTail
        apply feEqfe'

  theorem idx_of_eq_under_map [DecidableEq α] [DecidableEq β] (l : List α) (e : α) (he : l.elem e) (f : α -> β) (hf : ∀ e', e' ∈ l.toSet ∧ f e = f e' -> e = e') : (l.idx_of e he).val = ((l.map f).idx_of (f e) (by apply listToSetElementAlsoListElement; apply mappedElemInMappedList; apply listElementAlsoToSetElement; exact he)).val := by
    apply idx_of_with_count_eq_under_map 
    apply hf

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

  theorem map_eq_map_then_functions_eq (h : (List.map f l) = (List.map g l)) : ∀ x, x ∈ l.toSet -> f x = g x := by 
    intro x x_in_l
    induction l with 
    | nil => trivial  
    | cons a as ih => 
      simp [map] at h 
      simp [toSet, Set.element, Set.union] at x_in_l
      cases x_in_l with 
      | inl hl => rw [hl]; exact h.left
      | inr hr => exact ih h.right hr

  theorem map_eq_map_if_functions_eq (l : List α) : (∀ x, x ∈ l.toSet -> f x = g x) -> l.map f = l.map g := by 
    intro h
    induction l with 
    | nil => trivial 
    | cons a as ih => 
      simp [map]
      constructor 
      apply h
      simp [toSet, Set.element, Set.union]
      apply ih 
      intro x x_in_as
      apply h 
      simp [toSet, Set.element, Set.union]
      apply Or.inr 
      apply x_in_as
  
  theorem map_eq_map_iff (l : List α) : (∀ x, x ∈ l.toSet -> f x = g x) ↔ l.map f = l.map g := by 
    constructor 
    apply map_eq_map_if_functions_eq 
    apply map_eq_map_then_functions_eq

  theorem neg_all_of_any_neg (l : List α) (p : α -> Bool) : l.any (fun a => ¬p a) -> ¬l.all p := by 
    simp
    intro x _ _
    exists x 

  theorem any_of_exists (l : List α) (p : α -> Bool) : (∃ a, a ∈ l.toSet ∧ p a) -> l.any p = true := by 
    simp
    intro x _ _
    exists x
    constructor
    . rw [inIffInToSet]
      assumption
    . assumption

  theorem inToSetMeansExistsIndex [DecidableEq α] (L : List α) (e : α) : e ∈ L.toSet -> ∃ i, e = L.get i := by 
    intro h
    exists L.idx_of e (listToSetElementAlsoListElement L e h)
    rw [← idx_of_get]

  theorem existsIndexMeansInToSet (L : List α) (e : α) : (∃ i, e = L.get i) -> e ∈ L.toSet := by 
    intro ⟨i, hi⟩
    rw [hi]
    apply listGetInToSet
 
  theorem existsIndexIffInToSet [DecidableEq α] (L : List α) (e : α) : (∃ i, e = L.get i) ↔ e ∈ L.toSet := by 
    constructor; apply existsIndexMeansInToSet; apply inToSetMeansExistsIndex

  theorem elemFilterAlsoElemList [BEq α] (L : List α) (f : α -> Bool) : ∀ e, (L.filter f).elem e -> L.elem e := by 
    induction L with 
    | nil => intros; contradiction
    | cons head tail ih => 
      unfold filter
      split
      . intro e; unfold elem; split; trivial; apply ih
      . intros; unfold elem; split; rfl; apply ih; assumption

  theorem elemConcatIffElemOfOne [BEq α] (L L' : List α) : ∀ e, List.elem e (L ++ L') ↔ L.elem e ∨ L'.elem e := by 
    induction L with 
    | nil => simp
    | cons head tail ih => 
      intro e
      cases (Decidable.em (e == head)) with 
      | inl hl => simp [elem, hl]
      | inr hr => simp [elem, hr]; apply ih

  def flatten (L : List (List α)) : List α := L.foldl (fun acc L' => acc ++ L') (List.nil)

  theorem elemFlattenAlsoElemSomeListHelper [BEq α] [LawfulBEq α] (L : List (List α)) : ∀ e L', ¬ L'.elem e ∧ (L.foldl (fun acc L'' => acc ++ L'') L').elem e -> ∃ L'', L.elem L'' ∧ L''.elem e := by 
    induction L with 
    | nil => intro _ _ ⟨not_elem, elem_flatten⟩; contradiction
    | cons head tail ih => 
      intro e L' he
      simp [foldl] at he

      cases Decidable.em (head.elem e) with
      | inl e_in_head => exists head; constructor; simp [elem]; exact e_in_head
      | inr not_e_in_head => 
        have ex_l_in_tail := ih e (L' ++ head) (by 
          constructor
          . rw [elemConcatIffElemOfOne]; intro hcontra; cases hcontra with | inl hl => rw [he.left] at hl; contradiction | inr hr => contradiction 
          . exact he.right
        )
        cases ex_l_in_tail with | intro l hl =>
          exists l 
          constructor 
          . unfold elem; split; rfl; exact hl.left
          . exact hl.right

  theorem elemFlattenAlsoElemSomeList [BEq α] [LawfulBEq α] (L : List (List α)) : ∀ e, (L.foldl (fun acc L' => acc ++ L') (List.nil)).elem e -> ∃ L', L.elem L' ∧ L'.elem e := by
    intro e h_flatten
    exact elemFlattenAlsoElemSomeListHelper L e List.nil (by 
      constructor
      . simp [elem]
      . exact h_flatten
    )

  theorem concatEqMeansPartsEqIfSameLength (as bs cs ds : List α) (h : as.length = cs.length) : as ++ bs = cs ++ ds -> as = cs ∧ bs = ds := by 
    induction as generalizing cs with 
    | nil => cases cs with | nil => simp | cons _ _ => contradiction
    | cons a as ih => 
      cases cs with 
      | nil => contradiction
      | cons c cs => 
        intro h_eq
        injection h_eq with head tail
        injection h with h
        simp at h
        constructor
        . rw [head]
          rw [(ih cs h tail).left]
        . exact (ih cs h tail).right

  theorem mapConcatEqMapParts (as bs : List α) (f : α -> β) : List.map f (as ++ bs) = as.map f ++ bs.map f := by 
    simp

  theorem get_eq_of_eq {as bs : List α} (h : as = bs) (idx : Fin as.length) : as.get idx = bs.get ⟨idx.val, (by rw [← h]; exact idx.isLt)⟩ := by
    cases h; rfl
end List

