import ProofLibrary.SubstitutionAndHomomorphismBasics
import ProofLibrary.Models.Basic

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

  def image_set (f : α -> β) (A : Set α) : Set β := fun b => ∃ a, a ∈ A ∧ f a = b

  def injective_for_domain_set (f : α -> β) (domain : Set α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'
  def surjective_for_domain_and_image_set (f : α -> β) (domain : Set α) (image : Set β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

  theorem injective_of_injective_compose (f : α -> β) (g : β -> γ) (domain : Set α) :
      injective_for_domain_set (g ∘ f) domain -> injective_for_domain_set f domain := by
    intro inj a a' a_dom a'_dom image_eq
    apply inj a a' a_dom a'_dom
    simp [image_eq]

  theorem surjective_of_surjective_from_subset (f : α -> β) (domain : Set α) (image : Set β) :
      f.surjective_for_domain_and_image_set domain image ->
      ∀ domain', domain ⊆ domain' -> f.surjective_for_domain_and_image_set domain' image := by
    intro surj dom' dom'_sub b b_mem
    rcases surj b b_mem with ⟨a, a_mem, a_eq⟩
    exists a
    constructor
    . apply dom'_sub; exact a_mem
    . exact a_eq

  theorem surjective_of_surjective_compose (f : α -> β) (g : β -> γ) (domain : Set α) (image : Set γ) :
      surjective_for_domain_and_image_set (g ∘ f) domain image ->
      surjective_for_domain_and_image_set g (f.image_set domain) image := by
    intro surj b b_mem
    rcases surj b b_mem with ⟨a, a_mem, a_eq⟩
    exists f a
    constructor
    . exists a
    . exact a_eq

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

  theorem strong_of_compose_strong (g h : GroundTermMapping sig) (A B C : FactSet sig) :
      h.isHomomorphism B C -> GroundTermMapping.strong (h ∘ g) A C -> g.strong A B := by
    intro h_hom compose_strong
    intro e e_not_mem_a e_mem_b
    apply compose_strong e
    . exact e_not_mem_a
    . apply h_hom.right (GroundTermMapping.applyFact (h ∘ g) e)
      exists (g.applyFact e)
      constructor
      . exact e_mem_b
      . rw [applyFact_compose]
        simp

end GroundTermMapping

namespace FactSet

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def isWeakCore (fs : FactSet sig) : Prop :=
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs fs ∧ h.injective_for_domain_set fs.terms

  def isStrongCore (fs : FactSet sig) : Prop :=
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs fs ∧ h.injective_for_domain_set fs.terms ∧ h.surjective_for_domain_and_image_set fs.terms fs.terms

  theorem hom_surjective_of_finite_of_injective (fs : FactSet sig) (finite : fs.finite) : ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.injective_for_domain_set fs.terms -> h.surjective_for_domain_and_image_set fs.terms fs.terms := by
    rcases finite with ⟨l, finite⟩
    intro h isHom inj

    let terms_list := (l.map Fact.terms).flatten.eraseDupsKeepRight
    have nodup_terms_list : terms_list.Nodup := by apply List.nodup_eraseDupsKeepRight
    have mem_terms_list : ∀ e, e ∈ terms_list ↔ e ∈ fs.terms := by
      simp only [terms_list]
      intro e
      rw [List.mem_eraseDupsKeepRight_iff]
      unfold FactSet.terms
      simp
      constructor
      . intro h
        rcases h with ⟨ts, h, ts_mem⟩
        rcases h with ⟨f, f_mem, eq⟩
        exists f
        rw [eq]
        rw [← finite.right f]
        constructor <;> assumption
      . intro h
        rcases h with ⟨f, f_mem, e_mem⟩
        exists f.terms
        constructor
        . exists f; rw [finite.right f]; constructor; exact f_mem; rfl
        . exact e_mem
    have closed : ∀ e, e ∈ terms_list -> h e ∈ terms_list := by
      simp only [terms_list]
      intro e
      rw [List.mem_eraseDupsKeepRight_iff]
      rw [List.mem_eraseDupsKeepRight_iff]
      simp
      intro f f_mem e_in_f
      let f' := h.applyFact f
      have f'_mem : f' ∈ fs := by
        apply isHom.right
        unfold GroundTermMapping.applyFactSet
        exists f
        rw [← finite.right]
        constructor
        . exact f_mem
        . rfl
      exists f'.terms
      constructor
      . exists f'
        constructor
        . rw [finite.right]; exact f'_mem
        . rfl
      . simp only [f', GroundTermMapping.applyFact]
        simp
        exists e

    rw [Function.surjective_set_list_equiv h fs.terms terms_list mem_terms_list fs.terms terms_list mem_terms_list]
    rw [← Function.injective_iff_surjective_of_nodup_of_closed h terms_list nodup_terms_list closed]
    rw [← Function.injective_set_list_equiv h fs.terms terms_list mem_terms_list]
    exact inj

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
    . apply hom_surjective_of_finite_of_injective
      . unfold Set.finite; exists l
      . exact isHom
      . exact injective

  theorem every_universal_weakCore_isomorphic_to_universal_strongCore
      {kb : KnowledgeBase sig}
      (sc : FactSet sig) (sc_universal : sc.universallyModelsKb kb) (sc_strong : sc.isStrongCore)
      (wc : FactSet sig) (wc_universal : wc.universallyModelsKb kb) (wc_weak : wc.isWeakCore) :
      ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc sc ∧ iso.injective_for_domain_set wc.terms ∧ iso.surjective_for_domain_and_image_set wc.terms sc.terms := by

    rcases sc_universal.right wc wc_universal.left with ⟨h_sc_wc, h_sc_wc_hom⟩
    rcases wc_universal.right sc sc_universal.left with ⟨h_wc_sc, h_wc_sc_hom⟩

    specialize wc_weak (h_sc_wc ∘ h_wc_sc) (by
      apply GroundTermMapping.isHomomorphism_compose
      . exact h_wc_sc_hom
      . exact h_sc_wc_hom
    )

    specialize sc_strong (h_wc_sc ∘ h_sc_wc) (by
      apply GroundTermMapping.isHomomorphism_compose
      . exact h_sc_wc_hom
      . exact h_wc_sc_hom
    )

    exists h_wc_sc
    constructor
    . exact h_wc_sc_hom
    constructor
    -- strong since h_sc_wc ∘ h_wc_sc is strong
    . apply GroundTermMapping.strong_of_compose_strong h_wc_sc h_sc_wc wc sc wc h_sc_wc_hom
      exact wc_weak.left
    constructor
    -- injective since h_sc_wc ∘ h_wc_sc is injetive
    . apply Function.injective_of_injective_compose h_wc_sc h_sc_wc
      exact wc_weak.right
    -- surjective since h_wc_sc ∘ h_sc_wc is surjetive
    . apply Function.surjective_of_surjective_from_subset
      . apply Function.surjective_of_surjective_compose h_sc_wc h_wc_sc sc.terms
        exact sc_strong.right.right
      . intro t t_mem_image
        rcases t_mem_image with ⟨arg, arg_mem, arg_eq⟩
        rcases arg_mem with ⟨f, f_mem, f_eq⟩
        exists (h_sc_wc.applyFact f)
        constructor
        . apply h_sc_wc_hom.right
          exists f
        . unfold GroundTermMapping.applyFact
          simp
          exists arg

end FactSet

