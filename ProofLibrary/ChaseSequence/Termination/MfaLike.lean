import ProofLibrary.ChaseSequence.Termination.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace KnowledgeBase

  def parallelSkolemChase (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) : InfiniteList (FactSet sig)
  | .zero => kb.db.toFactSet
  | .succ n =>
    let prev_step := parallelSkolemChase kb det n
    fun f => f ∈ prev_step ∨ (∃ (trg : RTrigger (SkolemObsoleteness sig) kb.rules), trg.val.active prev_step ∧ f ∈ trg.val.result[0]'(by unfold RuleSet.isDeterministic at det; unfold Rule.isDeterministic at det; unfold PreTrigger.result; rw [List.length_map, ← PreTrigger.head_length_eq_mapped_head_length, det trg.val.rule trg.property]; simp))

  theorem parallelSkolemChase_subset_all_following (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) (n m : Nat) : kb.parallelSkolemChase det n ⊆ kb.parallelSkolemChase det (n+m) := by
    induction m with
    | zero => apply Set.subsetOfSelf
    | succ m ih =>
      rw [← Nat.add_assoc]
      conv => right; unfold parallelSkolemChase
      intro f f_mem
      apply Or.inl
      apply ih
      exact f_mem

  def skolemChaseResult (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) : FactSet sig := fun f => ∃ n, f ∈ parallelSkolemChase kb det n

  theorem skolemChaseResult_eq_every_chase_branch_result (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) : ∀ (cb : ChaseBranch (SkolemObsoleteness sig) kb), cb.result = kb.skolemChaseResult det := by
    unfold RuleSet.isDeterministic at det
    unfold Rule.isDeterministic at det
    intro cb
    apply funext
    intro f
    apply propext
    unfold ChaseBranch.result
    unfold skolemChaseResult
    constructor
    . intro h
      rcases h with ⟨n, h⟩
      induction n generalizing f with
      | zero =>
        rw [cb.database_first, Option.is_some_and] at h
        exists 0
      | succ n ih =>
        -- should be easy enough: get n from induction hypothesis and then use n+1
        cases eq_node : cb.branch.infinite_list (n+1) with
        | none => rw [eq_node, Option.is_some_and] at h; simp at h
        | some node =>
          cases eq_prev : cb.branch.infinite_list n with
          | none => have no_holes := cb.branch.no_holes (n+1); simp [eq_node] at no_holes; specialize no_holes ⟨n, by simp⟩; apply False.elim; apply no_holes; exact eq_prev
          | some prev_node =>
            have trg_ex := cb.triggers_exist n
            rw [eq_prev, Option.is_none_or] at trg_ex
            cases trg_ex with
            | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq_node; simp at eq_node
            | inl trg_ex =>
              unfold exists_trigger_opt_fs at trg_ex
              rcases trg_ex with ⟨trg, trg_active, disj_index, step_eq⟩
              rw [← step_eq, Option.is_some_and] at h
              simp at h
              cases h with
              | inl h =>
                specialize ih f
                rw [eq_prev, Option.is_some_and] at ih
                specialize ih h
                exact ih
              | inr h =>
                have : ∃ n, prev_node.fact.val ⊆ kb.parallelSkolemChase det n := by
                  have prev_finite := prev_node.fact.property
                  rcases prev_finite with ⟨prev_l, _, prev_l_eq⟩

                  have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e ∈  prev_node.fact.val) -> ∃ n, (∀ e, e ∈ l -> e ∈ kb.parallelSkolemChase det n) := by
                    intro l l_sub
                    induction l with
                    | nil => exists 0; intro e; simp
                    | cons hd tl ih_inner =>
                      have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
                      rcases from_ih with ⟨n_from_ih, from_ih⟩

                      have from_hd := ih hd
                      rw [eq_prev, Option.is_some_and] at from_hd
                      specialize from_hd (by apply l_sub; simp)
                      rcases from_hd with ⟨n_from_hd, from_hd⟩

                      cases Decidable.em (n_from_ih ≤ n_from_hd) with
                      | inl le =>
                        exists n_from_hd
                        intro f f_mem
                        simp at f_mem
                        cases f_mem with
                        | inl f_mem => rw [f_mem]; exact from_hd
                        | inr f_mem =>
                          rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                          rw [le]
                          apply kb.parallelSkolemChase_subset_all_following det n_from_ih diff
                          apply from_ih; exact f_mem
                      | inr lt =>
                        simp at lt
                        have le := Nat.le_of_lt lt
                        exists n_from_ih
                        intro f f_mem
                        simp at f_mem
                        cases f_mem with
                        | inr f_mem => apply from_ih; exact f_mem
                        | inl f_mem =>
                          rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                          rw [le]
                          apply kb.parallelSkolemChase_subset_all_following det n_from_hd diff
                          rw [f_mem]; exact from_hd

                  specialize this prev_l (by intro f; exact (prev_l_eq f).mp)
                  rcases this with ⟨n, this⟩
                  exists n
                  intro f
                  rw [← prev_l_eq]
                  exact this f
                rcases this with ⟨n, prev_subs⟩

                exists n+1
                unfold parallelSkolemChase

                have disj_index_zero : disj_index.val = 0 := by
                  have isLt := disj_index.isLt
                  unfold PreTrigger.result at isLt
                  simp only [List.length_map] at isLt
                  rw [← PreTrigger.head_length_eq_mapped_head_length] at isLt
                  rw [det _ trg.property, Nat.lt_one_iff] at isLt
                  exact isLt


                -- TODO: would be Decidable if we define sets in the parallelSkolemChase to be finite
                cases Classical.em (f ∈ kb.parallelSkolemChase det n) with
                | inl mem => apply Or.inl; exact mem
                | inr not_mem =>
                  apply Or.inr
                  exists trg
                  constructor
                  . unfold Trigger.active
                    constructor
                    . unfold PreTrigger.loaded
                      apply Set.subsetTransitive _ prev_node.fact.val _
                      constructor
                      . exact trg_active.left
                      . exact prev_subs
                    . intro contra
                      apply not_mem
                      rcases contra with ⟨i, contra⟩
                      apply contra
                      simp only [disj_index_zero] at h
                      unfold PreTrigger.result at h
                      rw [List.getElem_map, ← List.inIffInToSet] at h
                      have : i.val = 0 := by
                        have isLt := i.isLt
                        /- unfold PreTrigger.result at isLt -/
                        /- simp only [List.length_map] at isLt -/
                        simp only [← PreTrigger.head_length_eq_mapped_head_length] at isLt
                        rw [det _ trg.property, Nat.lt_one_iff] at isLt
                        exact isLt
                      rw [← List.inIffInToSet, List.get_eq_getElem]
                      simp only [this]
                      exact h
                  . simp only [disj_index_zero] at h
                    exact h
    . intro h
      rcases h with ⟨n, h⟩
      induction n with
      | zero =>
        exists 0
        rw [cb.database_first, Option.is_some_and]
        exact h
      | succ n ih =>
        -- not as "easy" as the other direcition, we need to invoke fairness somehow and likely need to show that only finitely many triggers are active at the same time...
        sorry

end KnowledgeBase

namespace RuleSet

  def criticalInstance (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : Database sig :=
    ⟨fun f => f.predicate ∈ rs.predicates ∧ ∀ t, t ∈ f.terms -> t = special_const, by
      have preds_finite := rs.predicates_finite_of_finite finite
      rcases preds_finite with ⟨l, nodup, eq⟩
      exists (l.map (fun p => {
        predicate := p
        terms := List.repeat special_const (sig.arity p)
        arity_ok := by rw [List.length_repeat]
      })).eraseDupsKeepRight
      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro f
        rw [List.mem_eraseDupsKeepRight_iff]
        simp [Set.element]
        constructor
        . intro h
          rcases h with ⟨p, p_mem, f_eq⟩
          rw [← f_eq]
          rw [eq] at p_mem
          constructor
          . exact p_mem
          . intro t
            apply List.mem_repeat
        . intro h
          exists f.predicate
          constructor
          . rw [eq]; exact h.left
          . rw [FunctionFreeFact.ext_iff]
            simp
            rw [List.repeat_eq_iff_all_val]
            constructor
            . exact f.arity_ok
            . exact h.right
    ⟩

  def mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (det : rs.isDeterministic) (special_const : sig.C) : FactSet sig :=
    let kb : KnowledgeBase sig := {
      rules := rs
      db := criticalInstance rs finite special_const
    }
    kb.skolemChaseResult det

end RuleSet

