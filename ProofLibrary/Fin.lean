namespace Fin
  theorem eq_last_or_prev_fin (fin : Fin (n + 1)) : fin.val = n ∨ ∃ (fin2 : Fin n), fin.val = fin2.val := by 
    cases (Decidable.em (fin = n)) with 
    | inl h => apply Or.inl; apply h
    | inr h => apply Or.inr; exists ⟨fin.val, by apply Nat.lt_of_le_of_ne; apply Nat.le_of_lt_succ; apply fin.isLt; apply h⟩ 
end Fin

