import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Gronwall (area-theorem) coefficient bound: shared definitions

This module sets up the vocabulary in which the leaf `Work.LandLeaves.gronwallCoeff`
(and the lemmas delegated for it) are stated.

For `U : ℂ → ℂ` holomorphic on the unit ball with `U 0 = 1` and
`z ↦ z * U (1/z²)` injective on `{|z| > 1}`, the target is

`∑_{k<N} (2k+1) * ‖U^{(k+1)}(0)/(k+1)!‖² ≤ 1`

which is the classical area theorem (Gronwall's inequality) for the odd
exterior-univalent function `z * U (1/z²) = z + ∑_{k≥1} u_k z^{1-2k}`.
-/

namespace Work.LandLeaves

/-- The `k`-th Taylor coefficient of `U` at `0`: `U^{(k)}(0)/k!`. -/
noncomputable def gco (U : ℂ → ℂ) (k : ℕ) : ℂ := ((k.factorial : ℂ))⁻¹ * iteratedDeriv k U 0

/-- The exterior map `z ↦ z * U (1/z²)`. -/
noncomputable def gF (U : ℂ → ℂ) (z : ℂ) : ℂ := z * U ((z * z)⁻¹)

/-- The complement of the image of the exterior of radius `r`:
`gK U r = ℂ ∖ gF U '' {z | r < ‖z‖}`. -/
def gK (U : ℂ → ℂ) (r : ℝ) : Set ℂ := {w | ¬ ∃ z, r < ‖z‖ ∧ gF U z = w}

/-- The "area functional" `π r² - π ∑_k (2k+1) ‖u_{k+1}‖² / r^{4k+2}`. -/
noncomputable def gW (U : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.pi * r ^ 2 - Real.pi * ∑' k : ℕ, (2 * (k : ℝ) + 1) * ‖gco U (k + 1)‖ ^ 2 / r ^ (4 * k + 2)

@[simp] lemma gco_zero (U : ℂ → ℂ) (hU0 : U 0 = 1) : gco U 0 = 1 := by
  simp [gco, hU0]

end Work.LandLeaves
