import ProofLibrary.Set
import ProofLibrary.Option

section
  -- copied from mathlib
  theorem Nat.min_succ_succ (x y : Nat) : min (succ x) (succ y) = succ (min x y) := by
    simp [Nat.min_def, Nat.succ_le_succ_iff]; split <;> rfl
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

  theorem listToSetElementAlsoListElement [BEq α] [LawfulBEq α] (L : List α) (e : α) : e ∈ L.toSet -> e ∈ L := by
    induction L with
      | nil => intros; contradiction
      | cons head tail ih => intro h; simp [Set.element, toSet] at h; cases h with
        | inl left => simp [Set.element] at left; simp [left]
        | inr right => simp; cases eq : e == head with | true => apply Or.inl; apply LawfulBEq.eq_of_beq; exact eq | false => apply Or.inr; exact (ih right)

  theorem listElementAlsoToSetElement (L : List α) (e : α) : e ∈ L -> e ∈ L.toSet := by
    induction L with
      | nil => intros; contradiction
      | cons head tail ih =>
        simp; unfold Set.element; unfold toSet; intro h_inList; cases h_inList with
        | inl hl => apply Or.inl; unfold Set.element; exact hl
        | inr hr => apply Or.inr; apply ih; apply hr

  theorem listElementIffToSetElement [BEq α] [LawfulBEq α] (L : List α) (e : α) : e ∈ L ↔ e ∈ L.toSet := by
    constructor; apply listElementAlsoToSetElement; apply listToSetElementAlsoListElement

  theorem listGetInToSet (L : List α) (indexFin : Fin L.length) : L.get indexFin ∈ L.toSet := by
    let ⟨index, indexSmallEnough⟩ := indexFin
    cases L with
      | nil => simp at indexSmallEnough
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

  theorem combine_nested_map (L : List α) (f : α -> β) (g : β -> γ) : List.map g (List.map f L) = List.map (g ∘ f) L := by
    induction L
    case nil => simp [map]
    case cons _ _ ih => simp [map, ih]

  def before_index : List α -> Nat -> List α
    | nil => fun _ => nil
    | cons h tail => fun i => match i with
      | Nat.zero => nil
      | Nat.succ i => cons h (tail.before_index i)

  theorem before_and_element_le_sum (L : List Nat) (pos : Fin (L.length)) : (L.before_index pos.val).sum + (L.get pos) ≤ L.sum := by
    let ⟨index, indexSmallEnough⟩ := pos
    cases L with
      | nil => simp at indexSmallEnough
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

  def enum_with_lt (l : List α) : List ((Fin l.length) × α) :=
    l.enum.attach.map (fun ⟨pair, h⟩ => (⟨pair.fst, by apply List.fst_lt_of_mem_enum; exact h⟩, pair.snd))

  theorem enum_with_lt_length_eq (l : List α) : l.enum_with_lt.length = l.length := by unfold enum_with_lt; simp

  theorem enum_with_lt_getElem_fst_eq_index (l : List α) (index : Nat) (h : index < l.length) : (l.enum_with_lt[index]'(by rw [enum_with_lt_length_eq]; exact h)).fst = ⟨index, h⟩ := by
    unfold enum_with_lt
    simp

  theorem enum_with_lt_getElem_snd_eq_getElem (l : List α) (index : Nat) (h : index < l.length) : (l.enum_with_lt[index]'(by rw [enum_with_lt_length_eq]; exact h)).snd = l[index] := by
    unfold enum_with_lt
    simp

  theorem mem_enum_with_lt_iff_mem_enum (l : List α) : ∀ (i : Fin l.length) (el : α), (i, el) ∈ l.enum_with_lt ↔ (i.val, el) ∈ l.enum := by
    intro i el
    unfold enum_with_lt
    simp
    constructor
    . intro h
      cases h with | intro ival h =>
        cases h with | intro h eq =>
          rw [← eq]
          exact h
    . intro h; exists i.val; exists h

  theorem mk_mem_enum_with_lt_iff_getElem (l : List α) : ∀ (i : Fin l.length) (el : α), (i, el) ∈ l.enum_with_lt ↔ l[i.val] = el := by
    intro i el
    rw [mem_enum_with_lt_iff_mem_enum]
    rw [List.mk_mem_enum_iff_getElem?]
    simp

  def idx_of_with_count [DecidableEq α] (l : List α) (e : α) (e_in_l : e ∈ l) (c : Nat) : Fin (c + l.length) :=
    match l with
      | nil => by contradiction
      | cons h tail => if eq : e == h then ⟨c, by simp⟩ else
        let res := tail.idx_of_with_count e (by cases e_in_l; simp at eq; assumption) (c + 1)
        ⟨res.val, by simp [length]; rw [@Nat.add_comm tail.length 1, ← Nat.add_assoc]; exact res.isLt⟩

  theorem idx_of_with_count_succ [DecidableEq α] (l : List α) (e : α) (e_in_l : e ∈ l) (c : Nat) : (idx_of_with_count l e e_in_l (c + 1)).val = (idx_of_with_count l e e_in_l c).val + 1 := by
    induction l generalizing c with
    | nil => contradiction
    | cons b bs ih =>
      unfold idx_of_with_count
      by_cases e == b
      case pos hl => simp [hl]
      case neg hr => simp [hr]; apply ih

  def idx_of [DecidableEq α] (l : List α) (e : α) (e_in_l : e ∈ l) : Fin l.length :=
    let tmp_fin := l.idx_of_with_count e e_in_l 0
    have tmp_fin_isLt := tmp_fin.isLt
    ⟨tmp_fin.val, by simp at tmp_fin_isLt; exact tmp_fin_isLt⟩

  theorem get_prepend_succ [DecidableEq α] (l : List α) (a : α) (i : Fin l.length) (j : Fin (a::l).length) (h : j = Fin.succ i) : l.get i = (a::l).get j := by rw [h]; simp [get]

  theorem idx_of_prepend_succ [DecidableEq α] (l : List α) (e a : α) (e_in_l : e ∈ l) (h : e ≠ a) : ((a::l).idx_of e (by right; trivial)) = Fin.succ (l.idx_of e e_in_l) := by
    simp [idx_of, idx_of_with_count, h, Fin.succ]
    apply idx_of_with_count_succ

  theorem idx_of_get [DecidableEq α] (l : List α) (e : α) (e_in_l : e ∈ l) (isLt : (l.idx_of e e_in_l < l.length)) : e = l.get ⟨(l.idx_of e e_in_l).val, isLt⟩ := by
    induction l with
    | nil => contradiction
    | cons a as ih =>
      by_cases h : e = a
      . simp [get, h, idx_of, idx_of_with_count]
      . have e_in_as : e ∈ as := by
          cases e_in_l
          . contradiction
          . trivial
        have isLt_as : (as.idx_of e e_in_as).val < as.length := by
          exact (as.idx_of e e_in_as).isLt
        have ih_plugged_in := ih e_in_as isLt_as
        apply Eq.trans
        exact ih_plugged_in
        rw [get_prepend_succ as a (as.idx_of e e_in_as) ((a::as).idx_of e e_in_l) (idx_of_prepend_succ as e a e_in_as h)]

  theorem idx_of_with_count_eq_of_list_eq [DecidableEq α] (l l' : List α) (h : l = l') (e : α) (he : e ∈ l) : ∀ c, (l.idx_of_with_count e he c).val = (l'.idx_of_with_count e (by rw [← h]; exact he) c).val := by
    cases l with
    | nil => cases l'; simp; contradiction
    | cons head tail => cases l' with
      | nil => contradiction
      | cons head' tail' =>
        have heads_eq : head = head' := by injection h
        have tails_eq : tail = tail' := by injection h
        simp [idx_of_with_count]
        split
        case isTrue he => simp [he, heads_eq]
        case isFalse he => simp [heads_eq] at he; simp [he]; intro c; apply idx_of_with_count_eq_of_list_eq; apply tails_eq

  theorem idx_of_eq_of_list_eq [DecidableEq α] (l l' : List α) (h : l = l') (e : α) (he : e ∈ l) : (l.idx_of e he).val = (l'.idx_of e (by rw [← h]; exact he)).val := by
    apply idx_of_with_count_eq_of_list_eq
    apply h

  theorem idx_of_with_count_eq_under_map [DecidableEq α] [DecidableEq β] (l : List α) (e : α) (he : e ∈ l) (f : α -> β) (hf : ∀ e', e' ∈ l.toSet ∧ f e = f e' -> e = e') : ∀ c, (l.idx_of_with_count e he c).val = ((l.map f).idx_of_with_count (f e) (by apply listToSetElementAlsoListElement; apply mappedElemInMappedList; apply listElementAlsoToSetElement; exact he) c).val := by
    induction l with
    | nil => contradiction
    | cons head tail ih =>
      intro c
      simp [idx_of_with_count]
      split
      case isTrue he => simp [he]
      case isFalse he =>
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

  theorem idx_of_eq_under_map [DecidableEq α] [DecidableEq β] (l : List α) (e : α) (he : e ∈ l) (f : α -> β) (hf : ∀ e', e' ∈ l.toSet ∧ f e = f e' -> e = e') : (l.idx_of e he).val = ((l.map f).idx_of (f e) (by apply listToSetElementAlsoListElement; apply mappedElemInMappedList; apply listElementAlsoToSetElement; exact he)).val := by
    apply idx_of_with_count_eq_under_map
    apply hf

  theorem length_enum_from' (l : List α) (n : Nat) : (l.enumFrom n).length = l.length := by simp

  theorem length_enum (l : List α) : l.enum.length = l.length := by simp

  theorem get_enum_from (l : List α) (n : Nat) (i : Fin l.length) : (l.enumFrom n).get ⟨i.val, (by rw [l.length_enum_from' n]; exact i.isLt)⟩ = (n + i.val, l.get i) := by
    rw [← Option.someInj, ← get?_eq_get]
    induction l generalizing n with
    | nil => have : i.val < 0 := i.isLt; contradiction
    | cons a as ih => cases eq : i.val with
      | zero => simp [get?, enumFrom]; rw [← Option.someInj]; simp [eq]
      | succ j =>
        unfold enumFrom
        unfold get?
        let jFin : Fin as.length := ⟨j, (by have isLt := i.isLt; unfold length at isLt; rw [eq] at isLt; apply Nat.lt_of_succ_lt_succ; exact isLt)⟩
        rw [ih (n+1) jFin]
        simp
        constructor
        . rw [Nat.add_assoc, Nat.add_comm 1 j]
        . rw [← Option.someInj]; simp [eq]

  theorem get_enum (l : List α) (i : Fin l.length) : l.enum.get ⟨i.val, (by rw [length_enum]; exact i.isLt)⟩ = (i.val, l.get i) := by
    unfold enum
    rw [get_enum_from]
    simp

  theorem map_eq_map_then_functions_eq (h : (List.map f l) = (List.map g l)) : ∀ x, x ∈ l.toSet -> f x = g x := by
    intro x x_in_l
    induction l with
    | nil => trivial
    | cons a as ih =>
      unfold map at h
      rw [List.cons_eq_cons] at h
      simp [toSet, Set.element, Set.union] at x_in_l
      cases x_in_l with
      | inl hl => rw [hl]; exact h.left
      | inr hr => exact ih h.right hr

  theorem map_eq_map_if_functions_eq (l : List α) : (∀ x, x ∈ l.toSet -> f x = g x) -> l.map f = l.map g := by
    intro h
    induction l with
    | nil => trivial
    | cons a as ih =>
      unfold map
      rw [List.cons_eq_cons]
      constructor
      apply h
      simp [toSet, Set.element, Set.union]
      apply ih
      intro x x_in_as
      apply h
      simp [toSet, Set.element, Set.union]
      apply Or.inr
      apply x_in_as

  theorem neg_all_of_any_neg (l : List α) (p : α -> Bool) : l.any (fun a => ¬p a) -> ¬l.all p := by simp

  theorem any_of_exists (l : List α) (p : α -> Bool) : (∃ a, a ∈ l ∧ p a) -> l.any p = true := by
    simp

  theorem elemFilterAlsoElemList (L : List α) (f : α -> Bool) : ∀ e, e ∈ (L.filter f) -> e ∈ L := by
    induction L with
    | nil => intros; contradiction
    | cons head tail ih =>
      unfold filter
      split
      . intro e; intro h; cases h; left; right; apply ih; assumption
      . intros; right; apply ih; assumption

  theorem elemConcatIffElemOfOne (L L' : List α) : ∀ e, e ∈ (L ++ L') ↔ e ∈ L ∨ e ∈ L' := by simp

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
        constructor
        . rw [head]
          rw [(ih cs h tail).left]
        . exact (ih cs h tail).right

  theorem mapConcatEqMapParts (as bs : List α) (f : α -> β) : List.map f (as ++ bs) = as.map f ++ bs.map f := by simp

  theorem get_eq_of_eq {as bs : List α} (h : as = bs) (idx : Fin as.length) : as.get idx = bs.get ⟨idx.val, (by rw [← h]; exact idx.isLt)⟩ := by
    cases h; rfl

  theorem head_cons_tail (l : List α)  (h : l ≠ []) : l = (l.head h) :: l.tail := by
    cases l with
    | nil => contradiction
    | cons head tail => simp

  def eraseDupsKeepRight [DecidableEq α] : List α -> List α
  | [] => []
  | hd::tl => if hd ∈ tl then tl.eraseDupsKeepRight else hd::(tl.eraseDupsKeepRight)

  theorem mem_eraseDupsKeepRight_iff [DecidableEq α] (l : List α) : ∀ e, e ∈ l.eraseDupsKeepRight ↔ e ∈ l := by
    induction l with
    | nil => simp [eraseDupsKeepRight]
    | cons hd tl ih =>
      unfold eraseDupsKeepRight
      intro e
      cases Decidable.em (hd ∈ tl) with
      | inl mem => simp [mem]; rw [ih]; simp; intro eq; rw [eq]; exact mem
      | inr not_mem => simp [not_mem]; rw [ih]

  theorem nodup_eraseDupsKeepRight [DecidableEq α] (l : List α) : l.eraseDupsKeepRight.Nodup := by
    induction l with
    | nil => simp [eraseDupsKeepRight]
    | cons hd tl ih =>
      simp only [eraseDupsKeepRight]
      cases Decidable.em (hd ∈ tl) with
      | inl mem => simp [mem, ih]
      | inr not_mem => simp [not_mem, ih]; rw [mem_eraseDupsKeepRight_iff]; exact not_mem

  theorem mem_iff_append_and_not_in_first [DecidableEq α] (l : List α) (e : α) : e ∈ l ↔ ∃ as bs, l = as ++ (e :: bs) ∧ ¬ e ∈ as := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      constructor
      . intro h
        cases Decidable.em (e = hd) with
        | inl eq =>
          exists []
          exists tl
          simp [eq]
        | inr neq =>
          simp [neq] at h
          rcases ih.mp h with ⟨as, bs, eq, n_mem⟩
          exists hd :: as
          exists bs
          simp [eq, neq, n_mem]
      . intro h
        rcases h with ⟨as, bs, eq, _⟩
        simp [eq]

  theorem map_id_of_id_on_all_mem (l : List α) (f : α -> α) (id_on_all_mem : ∀ e, e ∈ l -> f e = e) : l.map f = l := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      unfold map
      rw [id_on_all_mem hd]
      . rw [ih]
        intro e e_mem
        apply id_on_all_mem
        simp [e_mem]
      . simp

end List

def List.repeat (val : α) : Nat -> List α
| .zero => []
| .succ n => val :: List.repeat val n

theorem List.length_repeat (val : α) : ∀ n, (List.repeat val n).length = n := by
  intro n
  induction n with
  | zero => simp [List.repeat]
  | succ n ih => simp [List.repeat]; exact ih

theorem List.all_eq_val_repeat [DecidableEq α] (val : α) : ∀ n, (List.repeat val n).all (fun e => e = val) = true := by
  intro n
  induction n with
  | zero => simp [List.repeat]
  | succ n ih =>
    unfold List.repeat
    rw [List.all_cons, ih]
    simp

theorem List.repeat_split : ∀ (n k l : Nat), n = k + l -> List.repeat val n = List.repeat val k ++ List.repeat val l := by
  intro n k l h
  induction k generalizing n with
  | zero => simp [h, List.repeat]
  | succ k ih =>
    conv => right; left; unfold List.repeat
    simp
    specialize ih (k+l) rfl
    rw [← ih]
    conv at h => right; rw [Nat.add_assoc, Nat.add_comm 1 l, ← Nat.add_assoc]
    cases n with
    | zero => simp at h
    | succ n =>
      conv => left; unfold List.repeat
      simp at h
      rw [h]

