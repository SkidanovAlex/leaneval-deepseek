/-
Copyright: work module for the Elgindi finite-time singularity project.

# `L12Aux/Defs` — the angular `L²`-functionals of a `ClassC` profile

This module fixes the two functionals used by the target `Qang_small_z`:

* `Pz x k z = ∫_θ (D_z^k x (z,θ))² · sin(2θ)^{-η} dθ` — the `sin(2θ)^{-η}`-weighted angular
  `L²`-energy of the `k`-th `D_z`-iterate;
* `Qz x k z = ∫_θ D_z^k x (z,θ) · D_z^{k+1} x (z,θ) · sin(2θ)^{-η} dθ` — the angular
  correlation of two consecutive iterates, so that `z · (Pz x k)' z = 2 · Qz x k z`.

The rôle of these functionals is that the vanishing rate `Qang x k z = O(z^{3/2})` of the
angular moment `Work.Elliptic.Qang x k z = ∫_θ K(θ) D_z^k x(z,θ) dθ` (the target of
`Qang_small_z`) is proved by the chain

  `|Qang x k z| ≤ √(∫ K² sin^η) · √(Pz x k z)`  (Cauchy–Schwarz in `θ`),
  `Pz x k z ≤ z³ (4 J₀ + J₁)`  (`J₀ = ∫_{0}^{1} Pz x k t / t⁴ dt`,
  `J₁ = ∫_{0}^{1} Pz x (k+1) t / t⁴ dt`),

the second being the local Poincaré bound fed by `z (Pz x k)' = 2 Qz x k` and
`|z (Pz x k)'| ≤ 2 √(Pz x k · Pz x (k+1))` (Cauchy–Schwarz in `θ` again).

`sin(2θ)^{-η}` is `Real.rpow`, so it takes the value `0` at the two endpoints `θ = 0, π/2`;
all statements below are therefore about honest real-valued integrals.

Everything here is definitional and `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `sin(2θ)^{-η}`-weighted angular `L²`-energy of the `k`-th `D_z`-iterate of `x`:
`Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² · sin(2θ)^{-η} dθ`. -/
def Pz (x : Work.FTS.Galerkin.Fn) (k : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter k x z θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The angular correlation of two consecutive `D_z`-iterates of `x`:
`Qz x k z = ∫_{Iθ} D_z^k x (z,θ) · D_z^{k+1} x (z,θ) · sin(2θ)^{-η} dθ`.

It is the numerator of the derivative of `Pz`: `z · (Pz x k)' z = 2 · Qz x k z`. -/
def Qz (x : Work.FTS.Galerkin.Fn) (k : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter k x z θ * Work.Spaces.DzIter (k + 1) x z θ
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `sin(2θ) ≥ 0` on the angular interval `Iθ`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  have h : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
  obtain ⟨h1, h2⟩ := h
  exact Real.sin_nonneg_of_mem_Icc
    ⟨by linarith, by linarith [h2, Real.pi_pos]⟩

/-- `Pz` is an integral of a nonnegative integrand, hence nonnegative. -/
theorem Pz_nonneg (x : Work.FTS.Galerkin.Fn) (k : ℕ) (z : ℝ) : 0 ≤ Pz x k z := by
  refine MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ)
    (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc) fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)

/-- **The angular weight identity.**  The weighted `D_z`-summand of `HkIntegrand` is the
`sin(2θ)^{-η}`-weighted square of the same derivative: on `Iθ`,
`(D_z^k x · w/ sin(2θ)^{η/2})² = (D_z^k x)² · sin(2θ)^{-η} · w²`. -/
theorem summand_sq_eq (x : Work.FTS.Galerkin.Fn) (k : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter k x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.w z) ^ 2 := by
  have hs := sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    simp only [Real.zero_rpow (show (-(Work.Spaces.eta)) ≠ 0 by norm_num [Work.Spaces.eta]),
      Real.zero_rpow (show (Work.Spaces.eta / 2) ≠ 0 by norm_num [Work.Spaces.eta]),
      mul_zero, div_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add h]
      ring_nf
    rw [mul_pow, div_pow, hsq, Real.rpow_neg h.le]
    field_simp

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
