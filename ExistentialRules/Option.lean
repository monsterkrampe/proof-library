namespace Option
  def is_none_or : Option α -> (α -> Prop) -> Prop
    | none, _ => True
    | some a, pred => pred a

  def is_some_and : Option α -> (α -> Prop) -> Prop
    | none, _ => False
    | some a, pred => pred a

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

  theorem someEqImpliesEq : (some a = some b) -> a = b := by
    intro h
    let aNotNone : (some a) ≠ none := Option.someNotNone rfl
    let bNotNone : (some b) ≠ none := Option.someNotNone rfl
    have ha : a = (some a).unwrap aNotNone := by rfl
    have hb : b = (some b).unwrap bNotNone := by rfl
    rw [ha, hb]
    simp [h]

  theorem someInj : (some a = some b) ↔ a = b := by simp

  theorem is_none_or_of_eq_some {o : Option α} {a : α} {f : α -> Prop} (eq : o = some a) : o.is_none_or f = f a := by
    rw [eq]; simp [is_none_or]

end Option
