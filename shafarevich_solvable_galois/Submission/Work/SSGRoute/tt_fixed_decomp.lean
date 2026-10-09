import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Decomposition of a `σ`-invariant `ZMod 2`-valued function on a finite type with an
involution `σ`: `ε` splits as a "coboundary-type" part `lam p + lam (σ p)` plus a part `s`
that is supported on the fixed points of `σ`.

The construction is explicit: on each two-element orbit `{p, σ p}` (with `σ p ≠ p`) the
order `P` distinguishes a minimal representative `r = min p (σ p)`, and we set
`lam r = ε r`, `lam (σ r) = 0`; this makes `lam p + lam (σ p) = ε p` on the orbit. On fixed
points `lam` vanishes and `s` carries the value of `ε`. -/
theorem tt_fixed_decomp {P : Type*} [Fintype P] [DecidableEq P] [LinearOrder P]
    (σ : P → P) (hσ : ∀ p, σ (σ p) = p) (ε : P → ZMod 2) (hε : ∀ p, ε (σ p) = ε p) :
    ∃ lam s : P → ZMod 2, (∀ p, σ p ≠ p → s p = 0) ∧ ∀ p, ε p = lam p + lam (σ p) + s p := by
  classical
  refine ⟨fun p => if p < σ p then ε p else 0, fun p => if σ p = p then ε p else 0, ?_, ?_⟩
  · intro p hp
    simp [hp]
  · intro p
    by_cases hfix : σ p = p
    · simp [hfix]
    · rcases lt_or_gt_of_ne hfix with hlt | hgt
      · have h1 : ¬ p < σ p := not_lt_of_gt hlt
        have h2 : σ p < σ (σ p) := by rw [hσ p]; exact hlt
        simp [hfix, h1, h2, hε p]
      · have h2 : ¬ σ p < σ (σ p) := by rw [hσ p]; exact not_lt_of_gt hgt
        simp [hfix, hgt, h2]

end Work.SSGRoute
