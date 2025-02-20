import ExistentialRules.Terms.Basic

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

def all_term_lists_of_length (candidate_terms : List (GroundTerm sig)) : Nat -> List (List (GroundTerm sig))
| .zero => [[]]
| .succ n =>
  let prev_terms := all_term_lists_of_length candidate_terms n
  candidate_terms.flatMap (fun t =>
    prev_terms.map (fun ts =>
      t :: ts
    )
  )

theorem mem_all_term_lists_of_length (candidate_terms : List (GroundTerm sig)) (length : Nat) : ∀ ts, ts ∈ (all_term_lists_of_length candidate_terms length) ↔ (ts.length = length ∧ (∀ t, t ∈ ts -> t ∈ candidate_terms)) := by
  induction length with
  | zero => intro ts; unfold all_term_lists_of_length; simp; intro eq t _ mem; rw [eq] at mem; simp at mem
  | succ length ih =>
    intro ts
    unfold all_term_lists_of_length
    simp only [List.mem_flatMap, List.mem_map]

    constructor
    . intro h
      rcases h with ⟨t, t_mem, prev, prev_mem, ts_eq⟩
      rw [← ts_eq]
      specialize ih prev
      have ih := ih.mp prev_mem
      constructor
      . rw [List.length_cons, ih.left]
      . intro t' t'_mem
        rw [List.mem_cons] at t'_mem
        cases t'_mem with
        | inl t'_mem => rw [t'_mem]; apply t_mem
        | inr t'_mem => apply ih.right; exact t'_mem
    . intro h
      cases ts with
      | nil => simp at h
      | cons hd tl =>
        exists hd
        constructor
        . apply h.right
          simp
        . exists tl
          constructor
          . rw [ih]
            constructor
            . have l := h.left
              rw [List.length_cons, Nat.add_right_cancel_iff] at l
              exact l
            . intro t t_mem
              apply h.right
              simp [t_mem]
          . rfl

def all_terms_limited_by_depth (constants : List sig.C) (funcs : List (SkolemFS sig)) : Nat -> List (GroundTerm sig)
| 0 => []
| 1 => constants.map GroundTerm.const
| .succ (.succ depth) =>
  let prev := all_terms_limited_by_depth constants funcs (.succ depth)
  funcs.flatMap (fun func =>
    (all_term_lists_of_length prev func.arity).attach.map (fun ⟨ts, mem⟩ =>
      GroundTerm.func func ts (by
        rw [mem_all_term_lists_of_length] at mem
        exact mem.left
      )
    )
  ) ++ prev

theorem mem_all_terms_limited_by_depth (constants : List sig.C) (funcs : List (SkolemFS sig)) (depth : Nat) :
    ∀ t, t ∈ (all_terms_limited_by_depth constants funcs depth) ↔ (t.depth ≤ depth ∧ (∀ c, c ∈ t.constants -> c ∈ constants) ∧ (∀ func, func ∈ t.functions -> func ∈ funcs)) := by
  induction depth with
  | zero =>
    simp [all_terms_limited_by_depth]
    intro t _ t_depth
    cases t <;> simp [GroundTerm.depth, FiniteTree.depth] at t_depth
  | succ depth ih =>
    intro t
    unfold all_terms_limited_by_depth

    cases depth with
    | zero =>
      simp only [Nat.zero_add]
      constructor
      . intro h
        rw [List.mem_map] at h
        rcases h with ⟨c, c_mem, h⟩
        rw [← h]
        rw [GroundTerm.depth_const]
        rw [GroundTerm.constants_const]
        rw [GroundTerm.functions_const]
        simp [c_mem]
      . intro h
        cases eq : t with
        | const c =>
          rw [List.mem_map]
          exists c
          constructor
          . apply h.right.left
            simp [eq, GroundTerm.constants_const]
          . rfl
        | func _ ts _ =>
          have contra := h.left
          rw [eq, GroundTerm.depth_func] at contra
          cases eq : (ts.map GroundTerm.depth).max? with
          | none => simp [eq] at contra
          | some m =>
            cases m with
            | zero =>
              rw [List.max?_eq_some_iff] at eq
              . have contra := eq.left
                rw [List.mem_map] at contra
                rcases contra with ⟨t, t_mem, contra⟩
                cases t <;> simp [GroundTerm.depth_const, GroundTerm.depth_func] at contra
              . simp
              . intro a b; cases Decidable.em (a ≤ b) with
                | inl le => apply Or.inr; apply Nat.max_eq_right; exact le
                | inr le => apply Or.inl; apply Nat.max_eq_left; apply Nat.le_of_not_le; exact le
              . intros; apply Nat.max_le
            | succ m =>
              rw [eq, Nat.add_comm] at contra
              simp at contra

    | succ depth =>
      have aux : ∀ (ts : List (GroundTerm sig)),
          ((∀ (t : GroundTerm sig), t ∈ ts -> t ∈ (all_terms_limited_by_depth constants funcs depth.succ)) ↔
          ((ts.all (fun t => t.depth ≤ depth.succ)) ∧ (∀ c, c ∈ (ts.flatMap GroundTerm.constants) -> c ∈ constants) ∧ (∀ func, func ∈ (ts.flatMap GroundTerm.functions) -> func ∈ funcs))) := by
        intro ts
        induction ts with
        | nil => simp
        | cons hd tl ih_inner =>
          simp only [List.mem_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.flatMap_cons, List.mem_append]
          constructor
          . intro h
            have ih := (ih hd).mp (by apply h; simp)
            have ih_inner := ih_inner.mp (by intro _ t_mem; apply h; apply Or.inr; exact t_mem)
            constructor
            . constructor
              . exact ih.left
              . exact ih_inner.left
            constructor
            . intro c c_mem
              cases c_mem with
              | inl c_mem => apply ih.right.left; exact c_mem
              | inr c_mem => apply ih_inner.right.left; exact c_mem
            . intro f f_mem
              cases f_mem with
              | inl f_mem => apply ih.right.right; exact f_mem
              | inr f_mem => apply ih_inner.right.right; exact f_mem
          . intro h
            intro t t_mem
            cases t_mem with
            | inl t_mem =>
              rw [t_mem, ih]
              constructor
              . exact h.left.left
              constructor
              . intro c c_mem
                apply h.right.left
                apply Or.inl
                exact c_mem
              . intro f f_mem
                apply h.right.right
                apply Or.inl
                exact f_mem
            | inr t_mem =>
              apply ih_inner.mpr
              . constructor
                . exact h.left.right
                constructor
                . intro c c_mem
                  apply h.right.left
                  apply Or.inr
                  exact c_mem
                . intro f f_mem
                  apply h.right.right
                  apply Or.inr
                  exact f_mem
              . exact t_mem

      constructor
      . intro h
        rw [List.mem_append] at h
        cases h with
        | inr h =>
          rw [ih] at h
          constructor
          . apply Nat.le_succ_of_le
            exact h.left
          constructor
          . exact h.right.left
          . exact h.right.right
        | inl h =>
          simp only [List.mem_flatMap, List.mem_map] at h
          rcases h with ⟨func, func_mem, ts, ts_mem, t_eq⟩
          rw [← t_eq]
          unfold List.attach at ts_mem
          unfold List.attachWith at ts_mem
          rw [List.mem_pmap] at ts_mem
          rcases ts_mem with ⟨ts_val, ts_mem, ts_eq⟩
          rw [mem_all_term_lists_of_length] at ts_mem

          rw [GroundTerm.depth_func]
          rw [GroundTerm.constants_func]
          rw [GroundTerm.functions_func]

          have this := (aux ts_val).mp (by
            intro t t_mem
            apply ts_mem.right
            exact t_mem
          )

          rw [← ts_eq]
          constructor
          . rw [Nat.add_comm]
            apply Nat.succ_le_succ
            cases eq : (ts_val.map GroundTerm.depth).max? with
            | none => simp
            | some m =>
              rw [Option.getD_some, (ts_val.map GroundTerm.depth).max?_le_iff]
              have depth_ts := List.all_eq_true.mp this.left
              . simp only [decide_eq_true_iff] at depth_ts
                intro d d_mem
                rw [List.mem_map] at d_mem
                rcases d_mem with ⟨t, t_mem, d_mem⟩
                rw [← d_mem]
                apply depth_ts
                exact t_mem
              . intros; apply Nat.max_le
              . exact eq
          constructor
          . exact this.right.left
          . intro func' func'_mem
            rw [List.mem_cons] at func'_mem
            cases func'_mem with
            | inl func'_mem => rw [func'_mem]; exact func_mem
            | inr func'_mem => apply this.right.right; exact func'_mem

      . intro h
        rw [List.mem_append]
        simp only [List.mem_flatMap, List.mem_map]
        rcases h with ⟨depth_le, consts_mem, funcs_mem⟩
        rw [Nat.le_iff_lt_or_eq] at depth_le
        cases depth_le with
        | inl depth_le =>
          apply Or.inr
          rw [ih]
          constructor
          . apply Nat.le_of_lt_succ
            exact depth_le
          constructor
          . exact consts_mem
          . exact funcs_mem
        | inr depth_le =>
          cases eq : t with
          | const _ => rw [eq] at depth_le; simp [GroundTerm.depth_const] at depth_le
          | func t_func ts =>
            rw [eq, GroundTerm.depth_func] at depth_le
            rw [eq, GroundTerm.constants_func] at consts_mem
            rw [eq, GroundTerm.functions_func] at funcs_mem
            rw [Nat.add_comm, Nat.add_right_cancel_iff] at depth_le

            have this := (aux ts).mpr (by
              constructor
              . rw [List.all_eq_true]
                intro t t_mem
                rw [decide_eq_true_iff]
                cases eq : (ts.map GroundTerm.depth).max? with
                | none => rw [List.max?_eq_none_iff, List.map_eq_nil_iff] at eq; rw [eq] at t_mem; simp at t_mem
                | some m =>
                  rw [eq, Option.getD_some, ← Nat.succ_eq_add_one] at depth_le
                  rw [List.max?_eq_some_iff] at eq
                  . rw [← depth_le]
                    apply eq.right
                    rw [List.mem_map]
                    exists t
                  . simp
                  . intro a b; cases Decidable.em (a ≤ b) with
                    | inl le => apply Or.inr; apply Nat.max_eq_right; exact le
                    | inr le => apply Or.inl; apply Nat.max_eq_left; apply Nat.le_of_not_le; exact le
                  . intros; apply Nat.max_le
              constructor
              . exact consts_mem
              . intro func func_mem
                apply funcs_mem
                simp [func_mem]
            )

            apply Or.inl
            exists t_func
            constructor
            . apply funcs_mem
              simp

            have ts_mem : ts ∈ all_term_lists_of_length (all_terms_limited_by_depth constants funcs depth.succ) t_func.arity := by
              rw [mem_all_term_lists_of_length]
              constructor
              . have prop := t.property
                unfold PreGroundTerm.arity_ok at prop
                simp only [eq, GroundTerm.func, Bool.and_eq_true, beq_iff_eq] at prop
                rw [FiniteTreeList.fromListToListIsId, List.length_unattach] at prop
                exact prop.left
              . intro t t_mem
                apply this
                exact t_mem

            exists ⟨ts, ts_mem⟩
            simp

