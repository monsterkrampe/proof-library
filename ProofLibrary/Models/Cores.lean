import ProofLibrary.SubstitutionAndHomomorphismBasics

namespace List

  theorem length_le_of_nodup_of_all_mem [DecidableEq α] (as bs : List α) (nodup : as.Nodup) (all_mem : ∀ e, e ∈ as -> e ∈ bs) : as.length ≤ bs.length := by
    induction as generalizing bs with
    | nil => simp
    | cons a as ih =>
      let bs_without_a := bs.erase a
      simp at nodup
      specialize ih
        bs_without_a
        nodup.right
        (by intro c c_mem; rw [List.mem_erase_of_ne]; apply all_mem; simp [c_mem]; intro contra; rw [contra] at c_mem; apply nodup.left; exact c_mem)
      rw [List.length_erase_of_mem (by apply all_mem; simp)] at ih
      rw [Nat.le_sub_one_iff_lt (by apply List.length_pos_of_mem; apply all_mem a; simp)] at ih
      apply Nat.succ_le_of_lt
      exact ih

  theorem equiv_of_nodup_of_length_eq_of_all_mem [DecidableEq α] (as bs : List α) (nodup : as.Nodup) (eq_length : as.length = bs.length) (all_mem : ∀ e, e ∈ as -> e ∈ bs) : ∀ e, e ∈ as ↔ e ∈ bs := by
    intro e
    constructor
    . apply all_mem
    . intro mem_bs
      induction as generalizing bs e with
      | nil => cases bs; simp at mem_bs; simp at eq_length
      | cons a as ih =>
        let bs_without_a := bs.erase a
        simp at nodup
        specialize ih
          bs_without_a
          nodup.right
          (by rw [List.length_erase_of_mem, ← eq_length]; simp; apply all_mem; simp)
          (by intro c c_mem; rw [List.mem_erase_of_ne]; apply all_mem; simp [c_mem]; intro contra; rw [contra] at c_mem; apply nodup.left; exact c_mem)
        cases Decidable.em (e = a) with
        | inl eq => simp [eq]
        | inr neq =>
          simp; apply Or.inr
          apply ih
          rw [List.mem_erase_of_ne]
          exact mem_bs
          exact neq
end List

namespace Function

  def injective_for_domain_set (f : α -> β) (domain : Set α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'
  def surjective_for_domain_and_image_set (f : α -> β) (domain : Set α) (image : Set β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

  def injective_for_domain_list (f : α -> β) (domain : List α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'
  def surjective_for_domain_and_image_list (f : α -> β) (domain : List α) (image : List β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

  theorem injective_set_list_equiv (f : α -> β) (domain_set : Set α) (domain_list : List α) (eq : ∀ e, e ∈ domain_list ↔ e ∈ domain_set) : f.injective_for_domain_set domain_set ↔ f.injective_for_domain_list domain_list := by
    constructor
    . intro h a a' a_mem a'_mem f_eq
      apply h
      . rw [← eq]; assumption
      . rw [← eq]; assumption
      . exact f_eq
    . intro h a a' a_mem a'_mem f_eq
      apply h
      . rw [eq]; assumption
      . rw [eq]; assumption
      . exact f_eq

  theorem surjective_set_list_equiv (f : α -> β)
      (domain_set : Set α) (domain_list : List α) (eq_domain : ∀ e, e ∈ domain_list ↔ e ∈ domain_set)
      (image_set : Set β) (image_list : List β) (eq_image : ∀ e, e ∈ image_list ↔ e ∈ image_set) :
      f.surjective_for_domain_and_image_set domain_set image_set ↔ f.surjective_for_domain_and_image_list domain_list image_list := by
    constructor
    . intro h b b_mem
      specialize h b (by rw [← eq_image]; exact b_mem)
      rcases h with ⟨a, a_mem, a_eq⟩
      exists a
      constructor
      . rw [eq_domain]; exact a_mem
      . exact a_eq
    . intro h b b_mem
      specialize h b (by rw [eq_image]; exact b_mem)
      rcases h with ⟨a, a_mem, a_eq⟩
      exists a
      constructor
      . rw [← eq_domain]; exact a_mem
      . exact a_eq

  theorem injective_for_domain_list_cons (f : α -> β) (hd : α) (tl : List α) : f.injective_for_domain_list (hd::tl) -> f.injective_for_domain_list tl := by
    intro h a a' a_mem a'_mem eq
    apply h
    . simp [a_mem]
    . simp [a'_mem]
    . exact eq

  def image [DecidableEq β] (f : α -> β) : List α -> List β
  | [] => []
  | hd::tl =>
    let tl_img := image f tl
    if f hd ∈ tl_img then tl_img else (f hd)::tl_img

  theorem mapping_mem_image_of_mem [DecidableEq β] (f : α -> β) (domain : List α) : ∀ a, a ∈ domain -> f a ∈ (image f domain) := by
    intro a a_mem
    induction domain with
    | nil => simp at a_mem
    | cons hd tl ih =>
      simp [image]
      cases Decidable.em (f hd ∈ image f tl) with
      | inl hd_mem => simp [image, hd_mem]; cases a_mem; exact hd_mem; apply ih; assumption
      | inr hd_not_mem => simp [image, hd_not_mem]; cases a_mem; apply Or.inl; rfl; apply Or.inr; apply ih; assumption

  theorem nodup_image [DecidableEq β] (f : α -> β) (domain : List α) : (image f domain).Nodup := by
    induction domain with
    | nil => simp [image]
    | cons hd tl ih =>
      cases Decidable.em (f hd ∈ image f tl) with
      | inl hd_mem => simp [image, hd_mem]; exact ih
      | inr hd_not_mem => simp [image, hd_not_mem]; exact ih

  theorem length_image [DecidableEq β] (f : α -> β) (domain : List α) : (image f domain).length ≤ domain.length := by
    induction domain with
    | nil => simp [image]
    | cons hd tl ih => simp [image]; split; apply Nat.le_trans; exact ih; simp; simp; exact ih

  theorem surjective_on_own_image [DecidableEq β] (f : α -> β) (domain : List α) : f.surjective_for_domain_and_image_list domain (image f domain) := by
    induction domain with
    | nil => simp [surjective_for_domain_and_image_list, image]
    | cons hd tl ih =>
      intro b b_mem
      cases Decidable.em (f hd ∈ image f tl) with
      | inl hd_mem => simp [image, hd_mem] at b_mem; rcases ih b b_mem with ⟨a, ha⟩; exists a; simp [ha]
      | inr hd_not_mem =>
        simp [image, hd_not_mem] at b_mem
        cases b_mem with
        | inr b_mem => rcases ih b b_mem with ⟨a, ha⟩; exists a; simp [ha]
        | inl b_mem => exists hd; simp [b_mem]

  theorem image_contained_of_closed [DecidableEq α] (f : α -> α) (domain : List α) (closed : ∀ e, e ∈ domain -> f e ∈ domain) : ∀ e, e ∈ image f domain -> e ∈ domain := by
    intro b b_mem
    rcases surjective_on_own_image f domain b b_mem with ⟨a, a_mem, a_eq⟩
    rw [← a_eq]
    apply closed
    exact a_mem

  theorem injective_iff_length_image_eq_of_nodup [DecidableEq β] (f : α -> β) (domain : List α) (nodup : domain.Nodup) : f.injective_for_domain_list domain ↔ (image f domain).length = domain.length := by
    constructor
    . intro inj
      induction domain with
      | nil => simp [image]
      | cons hd tl ih =>
        cases Decidable.em (f hd ∈ image f tl) with
        | inl hd_mem =>
          apply False.elim
          simp at nodup
          apply nodup.left
          rcases surjective_on_own_image f tl (f hd) hd_mem with ⟨a, a_mem, a_eq⟩
          specialize inj a hd (by simp [a_mem]) (by simp) a_eq
          rw [← inj]
          exact a_mem
        | inr hd_not_mem =>
          simp [image, hd_not_mem]
          apply ih
          . simp at nodup; exact nodup.right
          . apply injective_for_domain_list_cons; exact inj
    . intro length_eq
      induction domain with
      | nil => simp [injective_for_domain_list]
      | cons hd tl ih =>
        cases Decidable.em (f hd ∈ image f tl) with
        | inl hd_mem =>
          simp [image, hd_mem] at length_eq
          have contra := length_image f tl
          rw [length_eq] at contra
          simp [Nat.succ_le] at contra
        | inr hd_not_mem =>
          simp [image, hd_not_mem] at length_eq
          intro a a' a_mem a'_mem eq
          cases a_mem
          . cases a'_mem
            . rfl
            . apply False.elim
              apply hd_not_mem
              rw [eq]
              apply mapping_mem_image_of_mem
              assumption
          . cases a'_mem
            . apply False.elim
              apply hd_not_mem
              rw [← eq]
              apply mapping_mem_image_of_mem
              assumption
            . simp at nodup
              specialize ih nodup.right length_eq
              apply ih <;> assumption

  theorem surjective_on_target_iff_all_in_image [DecidableEq β] (f : α -> β) (domain : List α) (target_image : List β) : f.surjective_for_domain_and_image_list domain target_image ↔ ∀ b, b ∈ target_image -> b ∈ image f domain := by
    constructor
    . intro surj b b_mem
      specialize surj b b_mem
      rcases surj with ⟨a, a_mem, a_eq⟩
      rw [← a_eq]
      apply mapping_mem_image_of_mem
      exact a_mem
    . intro h b b_mem
      apply surjective_on_own_image
      apply h
      exact b_mem

  theorem injective_iff_surjective_of_nodup_of_closed [DecidableEq α] (f : α -> α) (l : List α) (nodup : l.Nodup) (closed : ∀ e, e ∈ l -> f e ∈ l) : f.injective_for_domain_list l ↔ f.surjective_for_domain_and_image_list l l := by
    constructor
    . intro inj

      have : ∀ e, e ∈ image f l ↔ e ∈ l := by
        apply List.equiv_of_nodup_of_length_eq_of_all_mem
        . apply nodup_image
        . rw [injective_iff_length_image_eq_of_nodup] at inj
          rw [inj]
          exact nodup
        . intro e e_mem
          apply image_contained_of_closed
          . exact closed
          . exact e_mem

      rw [surjective_on_target_iff_all_in_image]
      intro b
      apply (this b).mpr
    . intro surj
      rw [surjective_on_target_iff_all_in_image] at surj
      rw [injective_iff_length_image_eq_of_nodup _ _ nodup]
      rw [Nat.eq_iff_le_and_ge]
      constructor
      . exact length_image f l
      . exact List.length_le_of_nodup_of_all_mem l (image f l) nodup surj

end Function



namespace GroundTermMapping

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def strong (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
    ∀ e, ¬ e ∈ A -> ¬ (h.applyFact e) ∈ B

end GroundTermMapping

namespace FactSet

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def isWeakCore (fs : FactSet sig) : Prop :=
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs fs ∧ h.injective_for_domain_set fs.terms

  def isStrongCore (fs : FactSet sig) : Prop :=
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs fs ∧ h.injective_for_domain_set fs.terms ∧ h.surjective_for_domain_and_image_set fs.terms fs.terms

  theorem isStrongCore_of_isWeakCore_of_finite (fs : FactSet sig) (weakCore : fs.isWeakCore) (finite : fs.finite) : fs.isStrongCore := by
    rcases finite with ⟨l, finite⟩
    unfold isStrongCore
    intro h isHom
    specialize weakCore h isHom
    rcases weakCore with ⟨strong, injective⟩
    constructor
    . exact strong
    constructor
    . exact injective
    . let terms_list := (l.map Fact.terms).flatten -- TODO: maybe dedup needed...
      rw [Function.surjective_set_list_equiv h fs.terms terms_list sorry fs.terms terms_list sorry]
      rw [← Function.injective_iff_surjective_of_nodup_of_closed h terms_list sorry sorry]
      rw [← Function.injective_set_list_equiv h fs.terms terms_list sorry]
      exact injective

end FactSet

