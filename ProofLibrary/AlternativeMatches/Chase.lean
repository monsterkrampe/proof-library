import ProofLibrary.AlternativeMatches.Basic
import ProofLibrary.AlternativeMatches.HomomorphismExtension
import ProofLibrary.Models.Cores
import ProofLibrary.KnowledgeBaseBasics

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

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]
  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def is_alt_match_at_chase_step_for (h : GroundTermMapping sig) (cb : ChaseBranch obs kb) (i : Nat) (fs : FactSet sig) : Prop :=
    ∃ node origin, cb.branch.infinite_list (i + 1) = some node ∧ node.origin = some origin
      ∧ h.isAlternativeMatch origin.fst.val origin.snd fs

end GroundTermMapping


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

namespace ChaseBranch

  def has_alt_match_at_step_for (cb : ChaseBranch obs kb) (i : Nat) (fs : FactSet sig) : Prop := ∃ (h : GroundTermMapping sig), h.is_alt_match_at_chase_step_for cb i fs

  def has_alt_match_for (cb : ChaseBranch obs kb) (fs : FactSet sig) : Prop := ∃ i, cb.has_alt_match_at_step_for i fs

  def has_alt_match (cb : ChaseBranch obs kb) : Prop := cb.has_alt_match_for cb.result

  theorem result_isWeakCore_of_noAltMatch (cb : ChaseBranch obs kb) (det : kb.isDeterministic) : ¬ cb.has_alt_match -> cb.result.isWeakCore := by
    intro noAltMatch h_0 h_0_hom
    apply Classical.byContradiction
    intro contra
    have contra := implToNotOr (notAndDeMorgan contra)

    have : ∀ k, (cb.branch.infinite_list k).is_none_or (fun node => ∃ (h_k : GroundTermMapping sig), (h_k.isHomomorphism cb.result cb.result) ∧ ((∀ (f : Fact sig), (∀ (t : GroundTerm sig), t ∈ f.terms -> t ∈ cb.result.terms) -> ¬ f ∈ cb.result -> h_0.applyFact f ∈ cb.result -> h_k.applyFact f ∈ cb.result) ∧ (∀ s t, s ∈ cb.result.terms -> t ∈ cb.result.terms -> s ≠ t -> h_0 s = h_0 t -> h_k s = h_k t)) ∧ (∀ t, t ∈ node.fact.val.terms -> h_k t = t)) := by
      intro k
      induction k with
      | zero =>
        rw [cb.database_first, Option.is_none_or]
        exists h_0
        constructor
        . exact h_0_hom
        . constructor
          . constructor
            . simp
            . simp
          . intro t t_mem
            simp at t_mem
            rcases t_mem with ⟨f, f_mem, t_mem⟩
            cases t with
            | inner sfs ftl =>
              unfold Database.toFactSet at f_mem
              simp [Set.element] at f_mem
              unfold Fact.toFunctionFreeFact at f_mem
              split at f_mem
              . simp at f_mem
              case h_2 _ _ eq =>
                split at eq
                case isTrue all =>
                  rw [List.all_eq_false.mpr _] at all
                  . simp at all
                  . exists (FiniteTree.inner sfs ftl); constructor; exact t_mem; simp
                . simp at eq
            | leaf c =>
              exact h_0_hom.left (FiniteTree.leaf c)
      | succ k ih =>
        cases eq : cb.branch.infinite_list (k+1) with
        | none => simp [Option.is_none_or]
        | some node =>
          rw [Option.is_none_or]
          cases eq2 : cb.branch.infinite_list k with
          | none =>
            have no_holes := cb.branch.no_holes (k + 1)
            simp [eq] at no_holes
            specialize no_holes ⟨k, by simp⟩
            contradiction
          | some node2 =>
            rw [eq2, Option.is_none_or] at ih
            rcases ih with ⟨h_k, h_k_hom, retains, identity⟩

            cases eq_origin : node.origin with
            | none =>
              have is_some := cb.origin_is_some k
              rw [eq, Option.is_none_or] at is_some
              rw [eq_origin] at is_some
              simp at is_some
            | some origin =>
              have node_fact_is_prev_fact_union_origin_res := cb.origin_trg_result_yields_next_node_fact k node node2 eq eq2 origin eq_origin
              have origin_trg_active := cb.origin_trg_is_active k node node2 eq eq2

              let trg_res_terms := (origin.fst.val.result.get origin.snd).terms

              have h_surj_on_trg_res : h_k.surjective_for_domain_and_image_set trg_res_terms trg_res_terms := by
                apply Classical.byContradiction
                intro not_surj
                apply noAltMatch
                exists k
                exists h_k
                exists node
                exists origin
                constructor
                . exact eq
                constructor
                . exact eq_origin
                . constructor
                  . constructor
                    . exact h_k_hom.left
                    . apply Set.subsetTransitive _ (h_k.applyFactSet cb.result) _
                      constructor
                      . apply GroundTermMapping.applyFactSet_subset_of_subset
                        apply Set.subsetTransitive _ node.fact.val _
                        constructor
                        . rw [node_fact_is_prev_fact_union_origin_res]
                          apply Set.subsetUnionSomethingStillSubset'
                          apply Set.subsetOfSelf
                        . have subset_res := chaseBranchSetIsSubsetOfResult cb (k+1)
                          rw [eq, Option.is_none_or] at subset_res
                          exact subset_res
                      . exact h_k_hom.right
                  constructor
                  . intro t t_mem
                    apply identity
                    simp at t_mem
                    rcases t_mem with ⟨v, v_mem, v_eq⟩
                    rcases origin.fst.val.rule.frontier_var_occurs_in_fact_in_body v v_mem with ⟨a, a_mem, v_mem⟩
                    exists origin.fst.val.subs.apply_function_free_atom a
                    constructor
                    . apply origin_trg_active.left
                      rw [← List.inIffInToSet]
                      simp [PreTrigger.mapped_body, SubsTarget.apply, GroundSubstitution.apply_function_free_conj]
                      exists a
                      constructor
                      . simp [eq_origin]; exact a_mem
                      . simp [eq_origin]
                    . rw [← v_eq]
                      simp [GroundSubstitution.apply_function_free_atom]
                      exists VarOrConst.var v
                  . unfold Function.surjective_for_domain_and_image_set at not_surj
                    simp at not_surj
                    rcases not_surj with ⟨t, t_mem, no_arg_for_t⟩
                    exists t
                    constructor
                    . exact t_mem
                    . intro t_mem_image
                      rcases t_mem_image with ⟨f, f_mem, t_mem_image⟩
                      rcases f_mem with ⟨f', f'_mem, f_eq⟩
                      rw [← f_eq] at t_mem_image
                      simp [GroundTermMapping.applyFact] at t_mem_image
                      rcases t_mem_image with ⟨t', t'_mem_image, t_eq⟩
                      apply no_arg_for_t t'
                      . exists f'
                      . exact t_eq

              have h_surj_on_step : h_k.surjective_for_domain_and_image_set node.fact.val.terms node.fact.val.terms := by
                rw [node_fact_is_prev_fact_union_origin_res]
                intro t t_mem
                rcases t_mem with ⟨f, f_mem, t_mem⟩
                simp at f_mem
                cases f_mem with
                | inl f_mem =>
                  exists t
                  constructor
                  . exists f; constructor; apply Or.inl; exact f_mem; exact t_mem
                  . apply identity; exists f
                | inr f_mem =>
                  rcases h_surj_on_trg_res t (by exists f) with ⟨s, s_mem, s_eq⟩
                  rcases s_mem with ⟨f', f'_mem, s_mem⟩
                  exists s
                  constructor
                  . exists f'; constructor; apply Or.inr; exact f'_mem; exact s_mem
                  . exact s_eq

              have node_terms_finite := node.fact.val.terms_finite_of_finite node.fact.property
              rcases node_terms_finite with ⟨l_terms, l_terms_nodup, l_terms_eq⟩

              rw [h_k.surjective_set_list_equiv _ _ l_terms_eq _ _ l_terms_eq] at h_surj_on_step

              have h_inj_on_step : h_k.injective_for_domain_list l_terms := Function.injective_of_surjective_of_nodup h_k l_terms l_terms_nodup h_surj_on_step
              have h_closed_on_step : ∀ t, t ∈ l_terms -> h_k t ∈ l_terms := Function.closed_of_injective_of_surjective_of_nodup h_k l_terms l_terms_nodup h_inj_on_step h_surj_on_step

              have inv_ex := h_k.exists_repetition_that_is_inverse_of_surj l_terms h_surj_on_step
              rcases inv_ex with ⟨repetition_number, inv_prop⟩
              let inv := h_k.repeat_hom repetition_number

              have extend_inv := cb.hom_for_step_extendable_result det (k+1) inv
              rw [eq, Option.is_none_or] at extend_inv
              specialize extend_inv (by
                constructor
                . apply h_k.repeat_hom_id_on_const
                  exact h_k_hom.left
                . have is_hom := h_k.repeat_hom_isHomomorphism cb.result h_k_hom repetition_number
                  apply Set.subsetTransitive _ (inv.applyFactSet cb.result) _
                  constructor
                  . apply inv.applyFactSet_subset_of_subset
                    have subset_res := chaseBranchSetIsSubsetOfResult cb (k+1)
                    rw [eq, Option.is_none_or] at subset_res
                    apply subset_res
                  . unfold inv
                    apply is_hom.right
              )

              rcases extend_inv with ⟨extended_inv, extended_inv_eq, extended_inv_hom⟩
              exists extended_inv ∘ h_k
              constructor
              . apply GroundTermMapping.isHomomorphism_compose _ _ _ cb.result _
                . exact h_k_hom
                . exact extended_inv_hom
              constructor
              . constructor
                . intro f terms_mem f_mem apply_mem
                  rw [GroundTermMapping.applyFact_compose]
                  simp
                  apply extended_inv_hom.right
                  apply GroundTermMapping.applyPreservesElement
                  exact retains.left f terms_mem f_mem apply_mem
                . intro s t s_mem t_mem neq h_0_eq
                  simp
                  rw [retains.right s t s_mem t_mem neq h_0_eq]
              . intro t t_mem
                simp
                rw [extended_inv_eq]
                . rw [← l_terms_eq] at t_mem
                  unfold inv
                  rw [inv_prop t t_mem]
                . rw [← l_terms_eq]
                  rw [← l_terms_eq] at t_mem
                  apply h_closed_on_step
                  exact t_mem

    cases contra with
    | inl not_strong =>
      apply not_strong
      unfold GroundTermMapping.strong
      intro f f_dom f_mem apply_f_mem

      have step_ex : ∀ (terms : List (GroundTerm sig)), (∀ t, t ∈ terms -> t ∈ cb.result.terms) -> ∃ i, (cb.branch.infinite_list i).is_some_and (fun node => ∀ t, t ∈ terms -> t ∈ node.fact.val.terms) := by
        intro terms id_on_terms
        induction terms with
        | nil => exists 0; rw [cb.database_first, Option.is_some_and]; simp
        | cons hd tl ih =>
          rcases ih (by intro t t_mem; apply id_on_terms; simp [t_mem]) with ⟨i_ih, ih⟩
          specialize id_on_terms hd (by simp)
          rcases id_on_terms with ⟨f, f_mem, hd_mem⟩
          rcases f_mem with ⟨i_hd, f_mem⟩

          cases eq_hd : cb.branch.infinite_list i_hd with
          | none => simp [eq_hd, Option.is_some_and] at f_mem
          | some node_hd =>
            rw [eq_hd, Option.is_some_and] at f_mem
            cases eq_ih : cb.branch.infinite_list i_ih with
            | none => simp [eq_ih, Option.is_some_and] at ih
            | some node_ih =>
              rw [eq_ih, Option.is_some_and] at ih
              cases Decidable.em (i_hd ≤ i_ih) with
              | inl le =>
                exists i_ih
                rw [eq_ih, Option.is_some_and]
                intro t t_mem
                simp at t_mem
                cases t_mem with
                | inl t_mem =>
                  rw [t_mem]
                  exists f
                  constructor
                  . have all_following := chaseBranchSetIsSubsetOfAllFollowing cb i_hd (i_ih - i_hd)
                    simp [eq_hd] at all_following
                    rw [Nat.add_sub_of_le le, eq_ih, Option.is_none_or] at all_following
                    apply all_following
                    exact f_mem
                  . exact hd_mem
                | inr t_mem =>
                  apply ih
                  exact t_mem
              | inr lt =>
                simp at lt
                exists i_hd
                rw [eq_hd, Option.is_some_and]
                intro t t_mem
                simp at t_mem
                cases t_mem with
                | inl t_mem =>
                  rw [t_mem]
                  exists f
                | inr t_mem =>
                  specialize ih t t_mem
                  rcases ih with ⟨f', f'_mem, t_mem⟩
                  exists f'
                  constructor
                  . have all_following := chaseBranchSetIsSubsetOfAllFollowing cb i_ih (i_hd - i_ih)
                    simp [eq_ih] at all_following
                    rw [Nat.add_sub_of_le (Nat.le_of_lt lt), eq_hd, Option.is_none_or] at all_following
                    apply all_following
                    exact f'_mem
                  . exact t_mem

      specialize step_ex f.terms f_dom
      rcases step_ex with ⟨step, step_ex⟩

      cases eq : cb.branch.infinite_list step with
      | none => rw [eq, Option.is_some_and] at step_ex; contradiction
      | some node =>
        rw [eq, Option.is_some_and] at step_ex
        specialize this step
        rw [eq, Option.is_none_or] at this
        rcases this with ⟨h_k, _, retains, identity⟩
        have retains := retains.left f f_dom f_mem apply_f_mem

        have : h_k.applyFact f = f := by
          unfold GroundTermMapping.applyFact
          rw [Fact.ext_iff]
          constructor
          . simp
          . simp
            apply List.map_id_of_id_on_all_mem
            intro t t_mem
            apply identity
            apply step_ex
            exact t_mem
        apply f_mem
        rw [← this]
        exact retains
    | inr not_inj =>
      apply not_inj
      intro s t s_mem t_mem image_eq
      apply Classical.byContradiction
      intro neq

      rcases s_mem with ⟨f_s, f_s_mem, s_mem⟩
      rcases t_mem with ⟨f_t, f_t_mem, t_mem⟩
      rcases f_s_mem with ⟨step_s, f_s_mem⟩
      rcases f_t_mem with ⟨step_t, f_t_mem⟩
      cases eq_s : cb.branch.infinite_list step_s with
      | none => simp [eq_s, Option.is_some_and] at f_s_mem
      | some node_s =>
        rw [eq_s, Option.is_some_and] at f_s_mem
        cases eq_t : cb.branch.infinite_list step_t with
        | none => simp [eq_t, Option.is_some_and] at f_t_mem
        | some node_t =>
          rw [eq_t, Option.is_some_and] at f_t_mem
          cases Decidable.em (step_s ≤ step_t) with
          | inl le =>
            specialize this step_t
            rw [eq_t, Option.is_none_or] at this
            rcases this with ⟨h_k, _, retains, identity⟩
            have retains := retains.right
            specialize retains s t
              (by exists f_s; constructor; exists step_s; rw [eq_s, Option.is_some_and]; exact f_s_mem; exact s_mem)
              (by exists f_t; constructor; exists step_t; rw [eq_t, Option.is_some_and]; exact f_t_mem; exact t_mem)
              neq image_eq
            have id_s := identity s (by
              exists f_s
              constructor
              . have all_following := chaseBranchSetIsSubsetOfAllFollowing cb step_s (step_t - step_s)
                simp [eq_s] at all_following
                rw [Nat.add_sub_of_le le, eq_t, Option.is_none_or] at all_following
                apply all_following
                exact f_s_mem
              . exact s_mem
            )
            have id_t := identity t (by exists f_t)
            rw [id_s, id_t] at retains
            apply neq
            apply retains
          | inr lt =>
            simp at lt
            specialize this step_s
            rw [eq_s, Option.is_none_or] at this
            rcases this with ⟨h_k, _, retains, identity⟩
            have retains := retains.right
            specialize retains s t
              (by exists f_s; constructor; exists step_s; rw [eq_s, Option.is_some_and]; exact f_s_mem; exact s_mem)
              (by exists f_t; constructor; exists step_t; rw [eq_t, Option.is_some_and]; exact f_t_mem; exact t_mem)
              neq image_eq
            have id_s := identity s (by exists f_s)
            have id_t := identity t (by
              exists f_t
              constructor
              . have all_following := chaseBranchSetIsSubsetOfAllFollowing cb step_t (step_s - step_t)
                simp [eq_t] at all_following
                rw [Nat.add_sub_of_le (Nat.le_of_lt lt), eq_s, Option.is_none_or] at all_following
                apply all_following
                exact f_t_mem
              . exact t_mem
            )
            rw [id_s, id_t] at retains
            apply neq
            apply retains

  theorem non_id_endomorphism_of_altMatch (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (altMatch : cb.has_alt_match) : ∃ (endo : GroundTermMapping sig), endo.isHomomorphism cb.result cb.result ∧ ∃ t, endo t ≠ t := by
    rcases altMatch with ⟨step, h_alt, node, origin, eq_node, eq_origin, altMatch⟩

    cases eq_prev : cb.branch.infinite_list step with
    | none =>
      have no_holes := cb.branch.no_holes (step + 1)
      simp [eq_node] at no_holes
      specialize no_holes ⟨step, by simp⟩
      contradiction
    | some prev_node =>
      have ts_finite := prev_node.fact.val.terms_finite_of_finite prev_node.fact.property
      rcases ts_finite with ⟨ts, nodup, eq_ts⟩

      let h : GroundTermMapping sig := fun t => if t ∈ ts then t else h_alt t
      have hom : h.isHomomorphism node.fact.val cb.result := by
        have trg_ex := cb.triggers_exist step
        rw [eq_prev, Option.is_none_or] at trg_ex
        cases trg_ex with
        | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq_node; simp at eq_node
        | inl trg_ex =>
          unfold exists_trigger_opt_fs at trg_ex
          rw [eq_node] at trg_ex
          rcases trg_ex with ⟨trg, trg_active, disj_index, eq_result⟩
          injection eq_result with eq_result
          have eq_trg_origin : origin = ⟨trg, disj_index⟩ := by rw [← Option.some_inj, ← eq_origin, ← eq_result]
          rw [← eq_result]
          simp only
          constructor
          . intro t
            cases t with
            | inner _ _ => simp
            | leaf c =>
              simp only
              unfold h
              split
              . rfl
              . have := altMatch.left.left (FiniteTree.leaf c)
                simp only at this
                exact this
          . intro f f_mem
            unfold GroundTermMapping.applyFactSet at f_mem
            rcases f_mem with ⟨f', f'_mem, f_eq⟩
            cases f'_mem with
            | inl f'_mem =>
              rw [← f_eq]
              have subset_res := chaseBranchSetIsSubsetOfResult cb step
              rw [eq_prev, Option.is_none_or] at subset_res
              apply subset_res
              have : h.applyFact f' = f' := by
                unfold GroundTermMapping.applyFact
                rw [Fact.ext_iff]
                simp
                rw [List.map_id_of_id_on_all_mem]
                intro t t_mem
                unfold h
                have : t ∈ ts := by rw [eq_ts]; exists f'
                simp [this]
              rw [this]
              exact f'_mem
            | inr f'_mem =>
              have alt_hom := altMatch.left.right
              apply alt_hom f
              exists f'
              constructor
              . rw [eq_trg_origin]; exact f'_mem
              . rw [← f_eq]
                unfold GroundTermMapping.applyFact
                simp
                intro t t_mem
                unfold h
                split
                case isTrue t_mem_ts =>
                  simp only [PreTrigger.result, PreTrigger.mapped_head] at f'_mem
                  simp at f'_mem
                  rw [← List.inIffInToSet] at f'_mem
                  simp at f'_mem

                  rcases f'_mem with ⟨a, a_mem, f'_eq⟩
                  rw [← f'_eq] at t_mem
                  simp only [PreTrigger.apply_to_function_free_atom] at t_mem
                  simp at t_mem

                  rcases t_mem with ⟨voc, voc_mem, t_eq⟩

                  cases voc with
                  | const c =>
                    simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term] at t_eq
                    rw [← t_eq]
                    have id_const := altMatch.left.left (GroundTerm.const c)
                    simp at id_const
                    exact id_const
                  | var v =>
                    have := altMatch.right.left
                    apply this

                    cases Decidable.em (v ∈ trg.val.rule.frontier) with
                    | inl v_in_frontier =>
                      rw [← t_eq, eq_trg_origin]
                      simp only [List.mem_map]
                      exists v
                      constructor
                      . exact v_in_frontier
                      . simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]
                        simp [v_in_frontier]
                    | inr v_not_in_frontier =>
                      -- kb.isDeterministic is used here but likely we could show a similar theorem used here also for branches
                      have := funcTermForExisVarInChaseTreeMeansTriggerResultOccurs (cb.intoTree det) trg disj_index v prev_node (List.repeat 0 step)
                      apply False.elim
                      apply trg_active.right
                      apply obs.contains_trg_result_implies_cond disj_index
                      apply this
                      constructor
                      . unfold ChaseBranch.intoTree
                        unfold FiniteDegreeTree.get
                        unfold PossiblyInfiniteTree.get
                        simp
                        rw [List.length_repeat, eq_prev]
                        simp
                        have := List.all_eq_val_repeat 0 step
                        simp at this
                        exact this
                      constructor
                      . exact v_not_in_frontier
                      . rw [eq_ts] at t_mem_ts
                        rcases t_mem_ts with ⟨f, f_mem, t_mem⟩
                        exists f
                        constructor
                        . exact f_mem
                        . rw [t_eq]
                          exact t_mem
                . rfl

      have hom_extension := cb.hom_for_step_extendable_result det (step+1) h
      rw [eq_node, Option.is_none_or] at hom_extension
      specialize hom_extension hom
      rcases hom_extension with ⟨ext, same_as_before, ext_hom⟩
      exists ext
      constructor
      . exact ext_hom
      . rcases altMatch with ⟨h_alt_hom, same_on_frontier, n, n_mem, n_not_mem_mapped⟩
        rcases n_mem with ⟨f, f_mem, n_mem⟩
        exists n
        intro contra
        rw [same_as_before n (by
          exists f
          constructor
          . have := node.fact_contains_origin_result
            rw [eq_origin, Option.is_none_or] at this
            apply this
            exact f_mem
          . exact n_mem
        )] at contra
        unfold h at contra
        cases Decidable.em (n ∈ ts) with
        | inl n_in_ts =>
          apply n_not_mem_mapped
          exists (h_alt.applyFact f)
          constructor
          . apply h_alt.applyPreservesElement
            exact f_mem
          . unfold GroundTermMapping.applyFact
            simp
            exists n
            constructor
            . exact n_mem
            . -- this is all copy pasted from an argument already given above
              simp only [PreTrigger.result, PreTrigger.mapped_head] at f_mem
              simp at f_mem
              rw [← List.inIffInToSet] at f_mem
              simp at f_mem

              rcases f_mem with ⟨a, a_mem, f_eq⟩
              rw [← f_eq] at n_mem
              simp only [PreTrigger.apply_to_function_free_atom] at n_mem
              simp at n_mem

              rcases n_mem with ⟨voc, voc_mem, n_eq⟩

              cases voc with
              | const c =>
                simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term] at n_eq
                rw [← n_eq]
                have id_const := h_alt_hom.left (GroundTerm.const c)
                simp at id_const
                exact id_const
              | var v =>
                apply same_on_frontier
                cases Decidable.em (v ∈ origin.fst.val.rule.frontier) with
                | inl v_in_frontier =>
                  rw [← n_eq]
                  simp only [List.mem_map]
                  exists v
                  constructor
                  . exact v_in_frontier
                  . simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]
                    simp [v_in_frontier]
                | inr v_not_in_frontier =>
                  -- kb.isDeterministic is used here but likely we could show a similar theorem used here also for branches
                  have := funcTermForExisVarInChaseTreeMeansTriggerResultOccurs (cb.intoTree det) origin.fst origin.snd v prev_node (List.repeat 0 step)
                  apply False.elim
                  have trg_active : origin.fst.val.active prev_node.fact.val := by
                    have trg_ex := cb.triggers_exist step
                    rw [eq_prev, Option.is_none_or] at trg_ex
                    cases trg_ex with
                    | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq_node; simp at eq_node
                    | inl trg_ex =>
                      unfold exists_trigger_opt_fs at trg_ex
                      rw [eq_node] at trg_ex
                      rcases trg_ex with ⟨trg, trg_active, disj_index, eq_result⟩
                      injection eq_result with eq_result
                      have eq_trg_origin : origin = ⟨trg, disj_index⟩ := by rw [← Option.some_inj, ← eq_origin, ← eq_result]
                      rw [eq_trg_origin]
                      exact trg_active
                  apply trg_active.right
                  apply obs.contains_trg_result_implies_cond origin.snd
                  apply this
                  constructor
                  . unfold ChaseBranch.intoTree
                    unfold FiniteDegreeTree.get
                    unfold PossiblyInfiniteTree.get
                    simp
                    rw [List.length_repeat, eq_prev]
                    simp
                    have := List.all_eq_val_repeat 0 step
                    simp at this
                    exact this
                  constructor
                  . exact v_not_in_frontier
                  . rw [eq_ts] at n_in_ts
                    rcases n_in_ts with ⟨f, f_mem, n_mem⟩
                    exists f
                    constructor
                    . exact f_mem
                    . rw [n_eq]
                      exact n_mem
        | inr n_not_in_ts =>
          simp [n_not_in_ts] at contra
          apply n_not_mem_mapped
          exists (h_alt.applyFact f)
          constructor
          . apply h_alt.applyPreservesElement
            exact f_mem
          . unfold GroundTermMapping.applyFact
            simp
            exists n

  theorem altMatch_of_some_not_reaches_self (cb : ChaseBranch obs kb) (fs : FactSet sig) (h : GroundTermMapping sig) (hom_res : h.isHomomorphism cb.result fs) (hom_fs : h.isHomomorphism fs fs) (t : GroundTerm sig) (t_mem : t ∈ cb.result.terms) (t_not_reaches_self : ∀ j, 1 ≤ j -> (h.repeat_hom j) t ≠ t) : cb.has_alt_match_for fs := by

    let term_property (ts : Set (GroundTerm sig)) (t : GroundTerm sig) := ∀ j, 1 ≤ j -> (h.repeat_hom j) t ≠ t
    let step_property (i : Nat) := (cb.branch.infinite_list i).is_some_and (fun node => ∃ t, t ∈ node.fact.val.terms ∧ term_property node.fact.val.terms t)

    have : ∃ i, step_property i ∧ ∀ (j : Fin i), ¬ step_property j.val := by
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases f_mem with ⟨step, f_mem⟩
      apply prop_for_nat_has_minimal_such_nat step_property step
      cases eq : cb.branch.infinite_list step with
      | none => simp [eq, Option.is_some_and] at f_mem
      | some node =>
        simp [eq, Option.is_some_and] at f_mem
        unfold step_property
        rw [eq, Option.is_some_and]
        exists t
        constructor
        . exists f
        . apply t_not_reaches_self
    rcases this with ⟨step, prop_step, smallest⟩

    exists (step-1)

    have step_ne_0 : step ≠ 0 := by
      intro contra
      unfold step_property at prop_step
      rw [contra] at prop_step
      have db_first := cb.database_first
      rw [db_first] at prop_step
      simp [Option.is_some_and] at prop_step
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
        specialize t_prop 1 (by simp)
        apply t_prop
        rw [(h.repeat_hom_id_on_const _ 1) (FiniteTree.leaf c)]; exact hom_res.left

    cases eq : cb.branch.infinite_list step with
    | none =>
      unfold step_property at prop_step
      rw [eq, Option.is_some_and] at prop_step
      contradiction
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
        rw [eq2, Option.is_some_and] at smallest
        unfold term_property at smallest
        simp at smallest

        have : ∃ l, 1 ≤ l ∧ ∀ s, s ∈ prev_node.fact.val.terms -> (h.repeat_hom l) s = s := by
          have step_finite := prev_node.fact.property
          have l_terms_finite := prev_node.fact.val.terms_finite_of_finite step_finite
          rcases l_terms_finite with ⟨l_terms, l_terms_nodup, l_terms_eq⟩
          rcases h.repeat_globally_of_each_repeats l_terms (by intro s s_mem; rw [l_terms_eq] at s_mem; apply smallest; exact s_mem) with ⟨l, l_le, aux⟩
          exists l
          constructor
          . exact l_le
          . intro s s_mem
            rw [← l_terms_eq] at s_mem
            apply aux
            exact s_mem

        rcases this with ⟨l, l_le, hom_id⟩
        unfold step_property at prop_step
        rw [eq, Option.is_some_and] at prop_step

        have prop_step : ∃ t, t ∈ node.fact.val.terms ∧ ∃ k, ∀ j, k ≤ j -> ∀ s, s ∈ node.fact.val.terms -> (h.repeat_hom j) s ≠ t := by
          apply Classical.byContradiction
          intro contra
          simp at contra
          have step_finite := node.fact.property
          have l_terms_finite := node.fact.val.terms_finite_of_finite step_finite
          rcases l_terms_finite with ⟨l_terms, l_terms_nodup, l_terms_eq⟩
          have reaches_self := h.repeat_each_reaches_self_of_each_reachable l_terms (by
            intro t t_mem
            rw [l_terms_eq] at t_mem
            specialize contra t t_mem 1
            rcases contra with ⟨k, k_le, s, s_mem, s_eq⟩
            exists k
            constructor
            . exact k_le
            . exists s
              rw [l_terms_eq]
              constructor
              . exact s_mem
              . exact s_eq
          )
          rcases prop_step with ⟨t, t_mem, prop_step⟩
          specialize reaches_self t (by rw [l_terms_eq]; exact t_mem)
          rcases reaches_self with ⟨l, l_le, reaches_self⟩
          apply prop_step l
          . exact l_le
          . exact reaches_self

        rcases prop_step with ⟨t, t_mem, k, prop_step⟩

        exists (h.repeat_hom ((k + 1) * l)) -- we just need a multiple of l >= k
        have hom_res' : (h.repeat_hom ((k + 1) * l)).isHomomorphism cb.result fs := by
          have : (k + 1) * l = ((k + 1) * l - 1) + 1 := by
            rw [Nat.sub_one_add_one]
            apply Nat.mul_ne_zero
            . simp
            . apply Nat.not_eq_zero_of_lt; apply Nat.lt_of_succ_le; exact l_le
          have : h.repeat_hom ((k + 1) * l) = h.repeat_hom (((k + 1) * l) - 1) ∘ h := by
            apply funext
            intro t
            simp
            have eq : h t = (h.repeat_hom 1) t := by simp [GroundTermMapping.repeat_hom]
            rw [eq, ← h.repeat_hom_add]
            rw [← this]
          rw [this]
          apply GroundTermMapping.isHomomorphism_compose h _ cb.result fs fs
          . exact hom_res
          . apply h.repeat_hom_isHomomorphism; exact hom_fs
        unfold GroundTermMapping.is_alt_match_at_chase_step_for
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
            . exact hom_res'.left
            . have origin_res_in_fact := node.fact_contains_origin_result
              rw [eq_origin, Option.is_none_or] at origin_res_in_fact
              apply Set.subsetTransitive _ ((h.repeat_hom ((k + 1) * l)).applyFactSet node.fact.val) _
              constructor
              . exact ((h.repeat_hom ((k + 1) * l)).applyFactSet_subset_of_subset _ _ origin_res_in_fact)
              . apply Set.subsetTransitive _ ((h.repeat_hom ((k + 1) * l)).applyFactSet cb.result) _
                constructor
                . apply GroundTermMapping.applyFactSet_subset_of_subset
                  have subs_res := chaseBranchSetIsSubsetOfResult cb step
                  rw [eq, Option.is_none_or] at subs_res
                  exact subs_res
                . apply hom_res'.right
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
                apply prop_step ((k + 1) * l) _ t
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
              apply prop_step ((k + 1) * l) _ t'
              . exists f'; constructor; rw [node_fact_is_prev_fact_union_origin_res]; apply Or.inr; exact f'_mem; exact t'_mem
              . exact t_eq
              . apply Nat.le_trans; apply Nat.le_succ; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_le

  theorem every_endo_surjective_of_noAltMatch (cb : ChaseBranch obs kb) : ¬ cb.has_alt_match -> ∀ (h : GroundTermMapping sig), h.isHomomorphism cb.result cb.result -> h.surjective_for_domain_and_image_set cb.result.terms cb.result.terms := by
    intro noAltMatch h endo
    apply Classical.byContradiction
    intro contra
    unfold Function.surjective_for_domain_and_image_set at contra
    simp at contra
    rcases contra with ⟨t, t_mem, contra⟩


    apply noAltMatch
    apply cb.altMatch_of_some_not_reaches_self cb.result h endo endo t t_mem

    intro j j_le eq
    apply contra ((h.repeat_hom (j-1)) t)
    . have hom := h.repeat_hom_isHomomorphism cb.result endo (j-1)
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      exists (h.repeat_hom (j-1)).applyFact f
      constructor
      . apply hom.right
        apply GroundTermMapping.applyPreservesElement
        exact f_mem
      . simp [GroundTermMapping.applyFact]
        exists t
    . have repeat_add := h.repeat_hom_add 1 (j - 1) t
      conv at repeat_add => right; simp [GroundTermMapping.repeat_hom]
      rw [← repeat_add]
      rw [Nat.add_comm, Nat.sub_one_add_one (Nat.not_eq_zero_of_lt (Nat.lt_of_succ_le j_le))]
      exact eq

  theorem result_isStrongCore_of_noAltMatch (cb : ChaseBranch obs kb) (det : kb.isDeterministic) : ¬ cb.has_alt_match -> cb.result.isStrongCore := by
    unfold FactSet.isStrongCore
    intro noAltMatch h endo
    have ⟨strong, inj⟩ := cb.result_isWeakCore_of_noAltMatch det noAltMatch h endo
    constructor
    . exact strong
    constructor
    . exact inj
    . apply every_endo_surjective_of_noAltMatch
      . exact noAltMatch
      . exact endo

  theorem core_superset_of_chase_result
      (cb : ChaseBranch obs kb) (fs : FactSet sig) (fs_super : cb.result ⊆ fs) (noAltMatch : ¬ cb.has_alt_match_for fs) :
      ∀ (sub_fs : FactSet sig), sub_fs.homSubset fs -> cb.result ⊆ sub_fs := by
    intro sub_fs sub_fs_sub
    rcases sub_fs_sub with ⟨sub_fs_sub, h, hom⟩

    apply Classical.byContradiction
    intro not_subsumes

    have hom_fs : h.isHomomorphism fs fs := by
      constructor
      . apply hom.left
      . apply Set.subsetTransitive _ sub_fs _
        constructor
        . apply hom.right
        . exact sub_fs_sub

    have hom_sub_fs : h.isHomomorphism sub_fs sub_fs := by
      constructor
      . apply hom.left
      . apply Set.subsetTransitive _ (h.applyFactSet fs) _
        constructor
        . apply GroundTermMapping.applyFactSet_subset_of_subset; exact sub_fs_sub
        . apply hom.right

    have : ∃ t, t ∈ cb.result.terms ∧ ∀ j, 1 ≤ j -> (h.repeat_hom j) t ≠ t := by
      apply Classical.byContradiction
      intro contra
      simp at contra
      apply not_subsumes

      intro f f_mem
      rcases f_mem with ⟨step, f_mem⟩
      cases eq : cb.branch.infinite_list step with
      | none => simp [eq, Option.is_some_and] at f_mem
      | some node =>
        rw [eq, Option.is_some_and] at f_mem

        have : ∃ j, 1 ≤ j ∧ ∀ t, t ∈ node.fact.val.terms -> (h.repeat_hom j) t = t := by
          have terms_finite := node.fact.val.terms_finite_of_finite node.fact.property
          rcases terms_finite with ⟨terms, terms_nodup, terms_eq⟩
          have repeats_globally := h.repeat_globally_of_each_repeats terms (by
            intro s s_mem
            apply contra
            rw [terms_eq] at s_mem
            rcases s_mem with ⟨f, f_mem, s_mem⟩
            exists f
            constructor
            . exists step; rw [eq, Option.is_some_and]; exact f_mem
            . exact s_mem
          )
          rcases repeats_globally with ⟨j, j_le, repeats_globally⟩
          exists j
          constructor
          . exact j_le
          . intro t t_mem
            apply repeats_globally
            rw [terms_eq]
            exact t_mem
        rcases this with ⟨j, j_le, each_repeats⟩

        have : (h.repeat_hom j).applyFact f = f := by
          simp [GroundTermMapping.applyFact]
          have : f.terms.map (h.repeat_hom j) = f.terms := by
            apply List.map_id_of_id_on_all_mem
            intro t t_mem
            apply each_repeats
            exists f
          rw [this]
        rw [← this]
        have : (h.repeat_hom j).isHomomorphism fs sub_fs := by
          have : h.repeat_hom j = h.repeat_hom (j-1) ∘ h := by
            apply funext
            intro t
            simp
            have : h t = h.repeat_hom 1 t := by simp [GroundTermMapping.repeat_hom]
            rw [this, ← h.repeat_hom_add]
            rw [Nat.sub_one_add_one (Nat.not_eq_zero_of_lt (Nat.lt_of_succ_le j_le))]
          rw [this]
          apply GroundTermMapping.isHomomorphism_compose h (h.repeat_hom (j-1)) fs sub_fs sub_fs
          . exact hom
          . apply h.repeat_hom_isHomomorphism; exact hom_sub_fs
        apply this.right
        apply GroundTermMapping.applyPreservesElement
        apply fs_super
        exists step
        rw [eq, Option.is_some_and]
        exact f_mem

    rcases this with ⟨t, t_mem, not_repeats⟩

    apply noAltMatch
    apply cb.altMatch_of_some_not_reaches_self fs h _ _ t t_mem
    . exact not_repeats
    . constructor
      . apply hom.left
      . apply Set.subsetTransitive _ (h.applyFactSet fs) _
        constructor
        . apply GroundTermMapping.applyFactSet_subset_of_subset
          exact fs_super
        . apply hom_fs.right
    . exact hom_fs

end ChaseBranch

