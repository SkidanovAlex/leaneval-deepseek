/-
Finite differences (forward difference operator), stated with the convention

  `fdiff n f h z = ∑_{j=0}^{n} (-1)^{n-j} C(n,j) f (z - j h)`.

This is `Δ^n f` for the step `h` (up to the sign convention `h ↔ -h`).
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.MRMT.Found

/-- Coefficient of the `j`-th term of the `n`-th finite difference:
`(-1)^{n-j} * C(n,j)`. -/
def fdCoeff (n j : ℕ) : ℝ := (-1 : ℝ) ^ (n - j) * (n.choose j : ℝ)

/-- The `n`-th finite difference of `f` with step `h`, at the point `z`:
`∑_{j=0}^{n} (-1)^{n-j} C(n,j) f (z - j h)`. -/
def fdiff {E : Type*} [AddCommMonoid E] [Module ℝ E] (n : ℕ) (f : ℂ → E) (h z : ℂ) : E :=
  ∑ j ∈ Finset.range (n+1), fdCoeff n j • f (z - (j : ℂ) * h)

@[simp] lemma fdiff_zero {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : ℂ → E) (h z : ℂ) :
    fdiff 0 f h z = f z := by
  simp [fdiff, fdCoeff]

end Work.MRMT.Found
