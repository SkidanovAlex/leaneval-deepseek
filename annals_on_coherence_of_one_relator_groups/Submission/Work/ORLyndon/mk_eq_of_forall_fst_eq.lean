import Mathlib

namespace Work.ORLyndon

/-- A one-letter word with a positive letter is the corresponding generator. -/
theorem mk_singleton_true {α : Type*} (a : α) :
    FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl

/-- A one-letter word with a negative letter is the inverse of the corresponding generator. -/
theorem mk_singleton_false {α : Type*} (a : α) :
    FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
  have h : FreeGroup.invRev [(a, true)] = [(a, false)] := by simp [FreeGroup.invRev]
  have hh := FreeGroup.inv_mk (L := [(a, true)])
  rw [h] at hh
  exact hh.symm

/-- If every letter of a word `L` has the same underlying generator `g`, then `mk L` is the
`∓1`-power of `of g` whose exponent is the exponent sum of `L`, i.e. the number of positive
letters minus the number of negative letters. -/
theorem mk_eq_of_forall_fst_eq {α : Type*} [DecidableEq α] {L : List (α × Bool)} {g : α}
    (h : ∀ p ∈ L, p.1 = g) :
    FreeGroup.mk L = FreeGroup.of g ^ ((L.map (fun p => if p.2 then (1 : ℤ) else -1)).sum) := by
  induction L with
  | nil => simp [FreeGroup.one_eq_mk]
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    have ha : a = g := h (a, b) (by simp)
    have hrest : ∀ q ∈ rest, q.1 = g := fun q hq => h q (by simp [hq])
    have hih := ih hrest
    conv_lhs => rw [← List.singleton_append, ← FreeGroup.mul_mk]
    rw [List.map_cons, List.sum_cons, hih]
    subst ha
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [mk_singleton_false, zpow_add, zpow_neg_one]
    · simp only [↓reduceIte]
      rw [mk_singleton_true, zpow_one_add]

end Work.ORLyndon
