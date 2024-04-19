namespace Option
  def unwrap : (opt : Option α) -> (opt ≠ none) -> α
    | none, h => absurd rfl h
    | some a, _ => a

  theorem someRevertsUnwrap (opt : Option α) (h : opt ≠ none) : some (opt.unwrap h) = opt := by
    cases opt with
      | none => exact absurd rfl h
      | some x => rfl

  theorem someNotNone : opt = some x -> opt ≠ none := by
    intro h
    have noConf : some x ≠ none := by
      intro g
      exact Option.noConfusion g
    rw [h]
    exact noConf

  theorem notSomeIsNone : (∀ x, opt ≠ some x) -> opt = none := by
    intro h
    cases opt with
      | none => rfl
      | some y =>
        have someYNeqSomeY := h y
        exact absurd rfl someYNeqSomeY
end Option
