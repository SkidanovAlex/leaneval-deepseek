import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared vocabulary for the `L^∞` bound on the Friedrichs truncation `STruncR`

This file fixes the objects used by the proof of
`Work.Diff.STE.Lead.STruncR_sup_le`:

* `diff2 i a` is the *second difference* of a coefficient family `a : (Fin n → ℤ) → ℂ` in the
  coordinate `i`, `(diff2 i a) m = a (m - 2eᵢ) - 2 a (m - eᵢ) + a m`;
* `diffL l a` iterates `diff2` over a list of coordinates;
* `coef ρ ε` is the coefficient family of the Friedrichs truncation, `m ↦ ρ (ε • m)`;
* `kernel ρ ε` is the truncated kernel `x ↦ Σ'_m ρ (ε • m) e^{2πi m·x}` (the real Fourier multiplier
  of `trunc ρ ε` applied to a Dirac mass), a finite sum since `ρ` is compactly supported;
* `psi ε` is the auxiliary weight `t ↦ 1` for `dist t ℤ < ε` and `t ↦ (ε / dist t ℤ)²` otherwise;
  it dominates the homogeneous SBP factor `ε²‖e^{2πit} - 1‖^{-2}` in the far region and has
  `∫_0^1 psi ε ≤ 4 ε`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.Lead.KSBP

/-- The second difference in one coordinate of a coefficient family on `ℤⁿ`:
`(diff2 i a) m = a (m - 2eᵢ) - 2 a (m - eᵢ) + a m`. -/
def diff2 {n : ℕ} (i : Fin n) (a : (Fin n → ℤ) → ℂ) : (Fin n → ℤ) → ℂ :=
  fun m => a (m - (2 : ℤ) • Pi.single i (1 : ℤ)) - 2 * a (m - Pi.single i (1 : ℤ)) + a m

/-- The iterated second difference along a list of coordinates. -/
def diffL {n : ℕ} (l : List (Fin n)) (a : (Fin n → ℤ) → ℂ) : (Fin n → ℤ) → ℂ :=
  l.foldr (fun i b => diff2 i b) a

/-- The coefficient family of the Friedrichs truncation: `m ↦ ρ (ε • m)`. -/
def coef {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) : (Fin n → ℤ) → ℂ :=
  fun m => ((ρ (fun i => ε * (m i : ℝ)) : ℝ) : ℂ)

/-- The truncated kernel `x ↦ Σ'_m ρ (ε • m) e^{2πi m·x}`. -/
def kernel {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) : (Fin n → ℝ) → ℂ :=
  fun x => ∑' m : Fin n → ℤ, coef ρ ε m * Work.Diff.STE.fourierExp m x

/-- The auxiliary weight replacing the SBP factor in the far region: `1` near the lattice and
`(4ε/‖e^{2πit}-1‖)²` far from it. -/
def psi (ε t : ℝ) : ℝ :=
  if ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖ < 4 * ε then 1
  else (4 * ε / ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖) ^ 2

end Work.Diff.STE.Lead.KSBP
