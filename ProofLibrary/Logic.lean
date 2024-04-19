theorem notExistsToForall {p : α -> Prop} : (¬∃ x, p x) -> ∀ x, ¬(p x) := by 
  intro h 
  intro x 
  intro px 
  have : ∃ x, p x := by exists x 
  contradiction

theorem notAndDeMorgan : ¬(a ∧ b) -> (a -> ¬b) := by 
  intro h 
  intro a 
  intro b 
  have aAndB := And.intro a b 
  contradiction

-- requires classical logic

theorem implToNotOr : (a -> b) -> (¬a ∨ b) := by 
  intro h 
  by_cases a 
  case inl ha => apply Or.inr; apply h; apply ha 
  case inr ha => apply Or.inl; apply ha  

theorem notnotelim : ¬¬p -> p := by 
  by_cases p 
  case inl hp => intro _; exact hp 
  case inr hnp => intro nnp; contradiction

