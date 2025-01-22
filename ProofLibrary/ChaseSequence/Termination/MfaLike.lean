import ProofLibrary.ChaseSequence.Termination.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

def criticalInstance (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : Database sig :=
  ⟨fun f => f.predicate ∈ rs.predicates ∧ ∀ t, t ∈ f.terms -> t = special_const, by
    have preds_finite := rs.predicates_finite_of_finite finite
    rcases preds_finite with ⟨l, nodup, eq⟩
    exists l.map (fun p => {
      predicate := p
      terms := List.repeat special_const (sig.arity p)
      arity_ok := by rw [List.length_repeat]
    })
    constructor
    . sorry
    . intro f
      simp
      constructor
      . intro h
        rcases h with ⟨p, p_mem, f_eq⟩
        rw [← f_eq]
        simp [Set.element]
        rw [eq] at p_mem
        constructor
        . exact p_mem
        . intro t
          sorry
      sorry
  ⟩

