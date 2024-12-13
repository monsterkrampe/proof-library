import ProofLibrary.AlternativeMatches.Basic
import ProofLibrary.AlternativeMatches.HomomorphismExtension
import ProofLibrary.Models.Cores

theorem prop_for_nat_has_minimal_such_nat (prop : Nat -> Prop) : ∀ i, prop i -> (∃ i, prop i ∧ ∀ (j : Fin i), ¬ prop j.val) := by
  intro i h
  -- TODO: can we do this without classical? at least going through all j < i should be possible; only prop might not be decidable
  cases Classical.em (∃ (j : Fin i), prop j.val) with
  | inl ex =>
    rcases ex with ⟨j, hj⟩
    exact prop_for_nat_has_minimal_such_nat prop j.val hj
  | inr nex =>
    simp at nex
    exists i

namespace GroundTermMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def repeat_hom (h : GroundTermMapping sig) : Nat -> GroundTermMapping sig
  | .zero => id
  | .succ j => h ∘ (h.repeat_hom j)

  theorem repeat_hom_swap (h : GroundTermMapping sig) (i : Nat) : ∀ t, h (h.repeat_hom i t) = (h.repeat_hom i) (h t) := by
    intro t
    induction i with
    | zero => unfold repeat_hom; simp
    | succ i ih =>
      unfold repeat_hom
      simp
      rw [ih]

  theorem repeat_hom_id_on_const (h : GroundTermMapping sig) (idOnConst : h.isIdOnConstants) : ∀ i, (h.repeat_hom i).isIdOnConstants := by
    intro i
    induction i with
    | zero => unfold repeat_hom; unfold isIdOnConstants; intro t; split <;> simp
    | succ i ih =>
      intro t
      cases t with
      | inner _ _ => simp
      | leaf c =>
        simp
        unfold repeat_hom
        simp
        rw [ih (FiniteTree.leaf c)]
        rw [idOnConst (FiniteTree.leaf c)]

  theorem repeat_hom_add (h : GroundTermMapping sig) (n m : Nat) : ∀ t, h.repeat_hom (n + m) t = h.repeat_hom n (h.repeat_hom m t) := by
    intro t
    induction m with
    | zero => simp [repeat_hom]
    | succ m ih =>
      conv => left; unfold repeat_hom
      conv => right; right; unfold repeat_hom
      simp
      rw [ih]
      rw [h.repeat_hom_swap]

  theorem repeat_hom_cycle_mul (h : GroundTermMapping sig) (t : GroundTerm sig) (n : Nat) : h.repeat_hom n t = t -> ∀ m, h.repeat_hom (n * m) t = t := by
    intro cycle m
    induction m with
    | zero => simp [repeat_hom]
    | succ m ih =>
      rw [Nat.mul_add]
      rw [repeat_hom_add]
      simp
      rw [cycle, ih]

  theorem repeat_hom_move_cycle (h : GroundTermMapping sig) (t : GroundTerm sig) (n : Nat) : h.repeat_hom n t = t -> ∀ s m, h.repeat_hom m t = s -> h.repeat_hom n s = s := by
    intro cycle s m reaches_s
    induction m generalizing t with
    | zero => simp [repeat_hom] at reaches_s; rw [← reaches_s]; exact cycle
    | succ m ih =>
      apply ih (h t)
      . rw [← h.repeat_hom_swap]
        rw [cycle]
      . simp [repeat_hom] at reaches_s
        rw [h.repeat_hom_swap] at reaches_s
        exact reaches_s


  variable [DecidableEq sig.P]

  theorem repeat_hom_isHomomorphism (h : GroundTermMapping sig) (fs : FactSet sig) (hom : h.isHomomorphism fs fs) : ∀ i, (h.repeat_hom i).isHomomorphism fs fs := by
    intro i
    constructor
    . apply repeat_hom_id_on_const; exact hom.left
    . induction i with
      | zero =>
        simp [repeat_hom]
        intro f f_mem
        rcases f_mem with ⟨f', f'_mem, f_eq⟩
        have : f = f' := by
          unfold applyFact at f_eq
          . rw [← f_eq]; simp
        rw [this]
        exact f'_mem
      | succ i ih =>
        unfold repeat_hom
        rw [applyFactSet_compose]
        simp
        intro f f_mem
        apply hom.right
        have lifted_ih := h.applyFactSet_subset_of_subset _ _ ih
        apply lifted_ih
        exact f_mem


  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def is_alt_match_at_chase_step (h : GroundTermMapping sig) (cb : ChaseBranch obs kb) (i : Nat) : Prop :=
    cb.branch.infinite_list (i + 1) = none ∨
    (∃ node origin, cb.branch.infinite_list (i + 1) = some node ∧ node.origin = some origin
      ∧ h.isAlternativeMatch origin.fst.val origin.snd cb.result)

end GroundTermMapping


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

namespace ChaseBranch

  def has_alt_match_at_step (cb : ChaseBranch obs kb) (i : Nat) : Prop := ∃ (h : GroundTermMapping sig), h.is_alt_match_at_chase_step cb i

  def has_alt_match (cb : ChaseBranch obs kb) : Prop := ∃ i, cb.has_alt_match_at_step i

  theorem result_isWeakCore_of_noAltMatch (cb : ChaseBranch obs kb) : ¬ cb.has_alt_match -> cb.result.isWeakCore := by
    sorry

  theorem result_isStrongCore_of_noAltMatch (cb : ChaseBranch obs kb) : ¬ cb.has_alt_match -> cb.result.isStrongCore := by
    unfold FactSet.isStrongCore
    intro noAltMatch h endo
    have ⟨strong, inj⟩ := cb.result_isWeakCore_of_noAltMatch noAltMatch h endo
    constructor
    . exact strong
    constructor
    . exact inj
    . apply Classical.byContradiction
      intro contra
      unfold Function.surjective_for_domain_and_image_set at contra
      simp at contra
      rcases contra with ⟨t, t_mem, contra⟩

      let term_property (ts : Set (GroundTerm sig)) (t : GroundTerm sig) := ∃ j, ∀ k, j ≤ k -> ∀ t', t' ∈ ts -> ¬ (h.repeat_hom k) t' = t
      let step_property (i : Nat) := (cb.branch.infinite_list i).is_none_or (fun node => ∃ t, t ∈ node.fact.val.terms ∧ term_property node.fact.val.terms t)

      have contra_stronger : ∀ k, 1 ≤ k -> ∀ (s : GroundTerm sig), s ∈ cb.result.terms -> ¬ (h.repeat_hom k) s = t := by
        intro k k_leq
        induction k with
        | zero => simp at k_leq
        | succ k ih =>
          cases k with
          | zero => simp [GroundTermMapping.repeat_hom]; apply contra
          | succ k =>
            simp at ih
            unfold GroundTermMapping.repeat_hom
            intro s s_mem
            specialize ih (h s)
            simp
            rw [h.repeat_hom_swap]
            apply ih
            rcases s_mem with ⟨f, f_mem, s_mem⟩
            exists h.applyFact f
            constructor
            . apply endo.right; exists f
            . simp [GroundTermMapping.applyFact]; exists s

      -- there exists a smallest chase step with such a term (not necessarily t)
      have : ∃ i, step_property i ∧ ∀ (j : Fin i), ¬ step_property j.val := by
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        rcases f_mem with ⟨step, f_mem⟩
        apply prop_for_nat_has_minimal_such_nat step_property step
        cases eq : cb.branch.infinite_list step with
        | none => simp [eq, Option.is_some_and] at f_mem
        | some node =>
          simp [eq, Option.is_some_and] at f_mem
          unfold step_property
          rw [eq, Option.is_none_or]
          exists t
          constructor
          . exists f
          . exists 1
            intro k k_leq s s_mem; apply contra_stronger
            exact k_leq
            rcases s_mem with ⟨f', f'_mem, s_mem⟩
            exists f'
            constructor
            . have subs_result := chaseBranchSetIsSubsetOfResult cb step
              rw [eq, Option.is_none_or] at subs_result
              apply subs_result
              exact f'_mem
            . exact s_mem
      rcases this with ⟨step, prop_step, smallest⟩

      apply noAltMatch
      exists (step-1)

      have step_ne_0 : step ≠ 0 := by
        intro contra
        unfold step_property at prop_step
        rw [contra] at prop_step
        have db_first := cb.database_first
        rw [db_first] at prop_step
        simp [Option.is_none_or] at prop_step
        rcases prop_step with ⟨t, t_mem, t_prop⟩
        rcases t_mem with ⟨f, f_mem, t_mem⟩

        cases t with
        | inner sfs ftl =>
          unfold Database.toFactSet at f_mem
          simp [Set.element] at f_mem
          unfold Fact.toFunctionFreeFact at f_mem
          split at f_mem
          . exact f_mem
          case h_2 _ _ eq =>
            split at eq
            case isTrue all =>
              rw [List.all_eq_false.mpr _] at all
              . simp at all
              . exists (FiniteTree.inner sfs ftl); constructor; exact t_mem; simp
            . simp at eq
        | leaf c =>
          rcases t_prop with ⟨j, t_prop⟩
          specialize t_prop j (by simp) (FiniteTree.leaf c)
          apply t_prop
          . exists f
          . rw [(h.repeat_hom_id_on_const _ j) (FiniteTree.leaf c)]; exact endo.left

      cases eq : cb.branch.infinite_list step with
      | none => exists id; simp [GroundTermMapping.is_alt_match_at_chase_step]; apply Or.inl; rw [Nat.sub_one_add_one step_ne_0]; exact eq
      | some node =>
        cases eq2 : cb.branch.infinite_list (step-1) with
        | none =>
          have no_holes := cb.branch.no_holes step
          simp [eq] at no_holes
          specialize no_holes ⟨step - 1, by apply Nat.sub_one_lt; exact step_ne_0⟩
          apply False.elim
          apply no_holes
          exact eq2
        | some prev_node =>
          specialize smallest ⟨step-1, by apply Nat.sub_one_lt; exact step_ne_0⟩

          unfold step_property at smallest
          rw [eq2, Option.is_none_or] at smallest
          unfold term_property at smallest
          simp at smallest

          have step_finite := prev_node.fact.property
          rcases step_finite with ⟨l_facts, step_finite⟩
          let l_terms := (l_facts.map Fact.terms).flatten

          have l_terms_eq : ∀ (s : GroundTerm sig), s ∈ prev_node.fact.val.terms ↔ s ∈ l_terms := by
            intro s
            constructor
            . intro s_mem
              rcases s_mem with ⟨f, f_mem, s_mem⟩
              simp [l_terms]
              exists f.terms
              constructor
              . exists f; constructor; rw [step_finite.right]; exact f_mem; rfl
              . exact s_mem
            . intro s_mem
              simp [l_terms] at s_mem
              rcases s_mem with ⟨terms, terms_eq, s_mem⟩
              rcases terms_eq with ⟨f, f_mem, f_eq⟩
              exists f
              constructor
              . rw [← step_finite.right]; exact f_mem
              . rw [f_eq]; exact s_mem

          have : ∀ s, s ∈ prev_node.fact.val.terms -> ∃ l, 1 ≤ l ∧ (h.repeat_hom l) s = s := by
            have aux : ∀ (l_terms : List (GroundTerm sig)), (∀ t, t ∈ l_terms -> ∀ j, ∃ k, j ≤ k ∧ ∃ s, s ∈ l_terms ∧ (h.repeat_hom k) s = t) -> (∀ s, s ∈ l_terms -> ∃ l, 1 ≤ l ∧ (h.repeat_hom l) s = s) := by
              intro l_terms smallest
              induction l_terms with
              | nil => simp
              | cons hd tl ih =>
                specialize ih (by
                  intro t t_mem j
                  have smallest_for_t := smallest t (by simp [t_mem]) j
                  rcases smallest_for_t with ⟨k, k_le, s, s_mem, s_eq⟩
                  simp at s_mem
                  cases s_mem with
                  | inr s_mem => exists k; constructor; exact k_le; exists s
                  | inl s_mem =>
                    have smallest_for_s := smallest s (by simp [s_mem]) 1
                    rcases smallest_for_s with ⟨l, l_le, u, u_mem, u_eq⟩
                    simp at u_mem
                    cases u_mem with
                    | inl u_mem =>
                      exists (((k / l) + 1) * l)
                      constructor
                      .
                        rw [Nat.add_mul]
                        apply Nat.le_trans
                        . exact k_le
                        . apply Nat.le_of_lt
                          simp
                          -- NOTE: taken from https://github.com/leanprover-community/mathlib4/blob/3f813de52d8cffaa73e27edd62364eec90eac633/Mathlib/Data/Nat/Defs.lean#L473-L474
                          rw [← Nat.succ_mul, ← Nat.div_lt_iff_lt_mul (by apply Nat.lt_of_succ_le; exact l_le)]; exact Nat.lt_succ_self _
                      . exists t
                        constructor
                        . exact t_mem
                        . apply h.repeat_hom_move_cycle s
                          . rw [Nat.mul_comm]
                            apply h.repeat_hom_cycle_mul
                            rw [u_mem, ← s_mem] at u_eq
                            exact u_eq
                          . exact s_eq
                    | inr u_mem =>
                      exists (k + l)
                      constructor
                      . apply Nat.le_add_right_of_le; exact k_le
                      . exists u
                        constructor
                        . exact u_mem
                        . rw [GroundTermMapping.repeat_hom_add]
                          rw [u_eq, s_eq]
                )

                intro s s_mem
                simp at s_mem
                cases s_mem with
                | inl s_mem =>
                  specialize smallest s (by rw [s_mem]; simp) 1
                  rcases smallest with ⟨k, k_le, t, t_mem, t_eq⟩
                  simp at t_mem
                  cases t_mem with
                  | inl t_mem => exists k; constructor; exact k_le; rw [t_mem, ← s_mem] at t_eq; exact t_eq
                  | inr t_mem =>
                    specialize ih t t_mem
                    rcases ih with ⟨l, l_le, ih⟩
                    exists l
                    constructor
                    . exact l_le
                    . apply h.repeat_hom_move_cycle t
                      . exact ih
                      . exact t_eq
                | inr s_mem =>
                  apply ih
                  exact s_mem
            intro s s_mem
            rw [l_terms_eq] at s_mem
            apply aux l_terms
            . intro t t_mem j
              specialize smallest t (by rw [l_terms_eq]; exact t_mem) j
              rcases smallest with ⟨k, k_le, u, u_mem, u_eq⟩
              rw [l_terms_eq] at u_mem
              exists k
              constructor
              . exact k_le
              . exists u
            . exact s_mem


          -- swapped quantifiers in previous this
          have : ∃ l, 1 ≤ l ∧ ∀ s, s ∈ prev_node.fact.val.terms -> (h.repeat_hom l) s = s := by
            have aux : ∀ (l_terms : List (GroundTerm sig)), (∀ s, s ∈ l_terms -> ∃ l, 1 ≤ l ∧ (h.repeat_hom l) s = s) -> ∃ l, 1 ≤ l ∧ ∀ s, s ∈ l_terms -> (h.repeat_hom l) s = s := by
              intro l_terms precond
              induction l_terms with
              | nil => exists 1; simp
              | cons hd tl ih =>
                specialize ih (by intro s s_mem; apply precond; simp [s_mem])
                rcases ih with ⟨l_ih, l_ih_le, ih⟩
                rcases precond hd (by simp) with ⟨l_hd, l_hd_le, precond⟩
                exists l_hd * l_ih
                constructor
                . apply Nat.le_trans; exact l_hd_le; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_ih_le
                . intro s s_mem
                  simp at s_mem
                  cases s_mem with
                  | inl s_mem => rw [s_mem, h.repeat_hom_cycle_mul]; exact precond
                  | inr s_mem => specialize ih s s_mem; rw [Nat.mul_comm, h.repeat_hom_cycle_mul]; exact ih
            rcases aux l_terms (by intro s s_mem; rw [← l_terms_eq] at s_mem; apply this; exact s_mem) with ⟨l, l_le, aux⟩
            exists l
            constructor
            . exact l_le
            . intro s s_mem
              rw [l_terms_eq] at s_mem
              apply aux
              exact s_mem

          rcases this with ⟨l, l_le, hom_id⟩
          unfold step_property at prop_step
          rw [eq, Option.is_none_or] at prop_step
          rcases prop_step with ⟨t, t_mem, i, prop_step⟩

          exists (h.repeat_hom ((i+1) * l)) -- we just need some multiple of l >= i here
          have endo' : (h.repeat_hom ((i+1) * l)).isHomomorphism cb.result cb.result := by
            apply h.repeat_hom_isHomomorphism
            exact endo
          unfold GroundTermMapping.is_alt_match_at_chase_step
          apply Or.inr
          exists node
          cases eq_origin : node.origin with
          | none =>
            have origin_is_some := cb.origin_is_some (step - 1)
            rw [Nat.sub_one_add_one step_ne_0, eq, Option.is_none_or] at origin_is_some
            rw [eq_origin] at origin_is_some
            simp at origin_is_some
          | some origin =>
            exists origin
            rw [Nat.sub_one_add_one step_ne_0, eq]
            simp
            constructor
            . constructor
              . exact endo'.left
              . have origin_res_in_fact := node.fact_contains_origin_result
                rw [eq_origin, Option.is_none_or] at origin_res_in_fact
                apply Set.subsetTransitive _ ((h.repeat_hom ((i + 1) * l)).applyFactSet node.fact.val) _
                constructor
                . exact ((h.repeat_hom ((i + 1) * l)).applyFactSet_subset_of_subset _ _ origin_res_in_fact)
                . apply Set.subsetTransitive _ ((h.repeat_hom ((i + 1) * l)).applyFactSet cb.result) _
                  constructor
                  . apply GroundTermMapping.applyFactSet_subset_of_subset
                    have subs_res := chaseBranchSetIsSubsetOfResult cb step
                    rw [eq, Option.is_none_or] at subs_res
                    exact subs_res
                  . apply endo'.right
            constructor
            . intro t t_mem
              simp at t_mem
              rw [Nat.mul_comm]
              apply h.repeat_hom_cycle_mul
              apply hom_id
              have orig_trg_active := cb.origin_trg_is_active (step-1) node prev_node (by rw [Nat.sub_one_add_one step_ne_0]; exact eq) eq2
              have loaded := orig_trg_active.left
              unfold PreTrigger.loaded at loaded
              unfold PreTrigger.mapped_body at loaded
              rcases t_mem with ⟨v, v_mem, v_eq⟩
              rcases origin.fst.val.rule.frontier_var_occurs_in_fact_in_body _ v_mem with ⟨a, a_mem, v_mem⟩
              exists origin.fst.val.subs.apply_function_free_atom a
              constructor
              . apply loaded
                rw [← List.inIffInToSet]
                simp only [SubsTarget.apply]
                unfold GroundSubstitution.apply_function_free_conj
                simp
                exists a
                constructor
                . simp [eq_origin]; exact a_mem
                . simp [eq_origin]
              . simp [GroundSubstitution.apply_function_free_atom]
                exists VarOrConst.var v
            . exists t
              have node_fact_is_prev_fact_union_origin_res := cb.origin_trg_result_yields_next_node_fact (step-1) node prev_node (by rw [Nat.sub_one_add_one step_ne_0]; exact eq) eq2 origin eq_origin
              constructor
              . have t_not_mem_prev : ¬ t ∈ prev_node.fact.val.terms := by
                  intro t_mem
                  rcases t_mem with ⟨f, f_mem, t_mem⟩
                  apply prop_step ((i + 1) * l) _ t
                  . exists f; constructor; rw [node_fact_is_prev_fact_union_origin_res]; apply Or.inl; exact f_mem; exact t_mem
                  . rw [Nat.mul_comm]; apply h.repeat_hom_cycle_mul; apply hom_id; exists f
                  . apply Nat.le_trans; apply Nat.le_succ; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_le
                rw [node_fact_is_prev_fact_union_origin_res] at t_mem
                rcases t_mem with ⟨f, f_mem, t_mem⟩
                cases f_mem with
                | inl f_mem => apply False.elim; apply t_not_mem_prev; exists f
                | inr f_mem => exists f
              . intro t_mem
                rcases t_mem with ⟨f, f_mem, t_mem⟩
                rcases f_mem with ⟨f', f'_mem, f_eq⟩
                rw [← f_eq] at t_mem
                simp [GroundTermMapping.applyFact] at t_mem
                rcases t_mem with ⟨t', t'_mem, t_eq⟩
                apply prop_step ((i + 1) * l) _ t'
                . exists f'; constructor; rw [node_fact_is_prev_fact_union_origin_res]; apply Or.inr; exact f'_mem; exact t'_mem
                . exact t_eq
                . apply Nat.le_trans; apply Nat.le_succ; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_le

end ChaseBranch

