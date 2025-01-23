import ProofLibrary.ChaseSequence.Termination.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

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

