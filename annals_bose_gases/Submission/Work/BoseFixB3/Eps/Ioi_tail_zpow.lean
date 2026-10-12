import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Eps.Ioi_tail_zpow`

The exact one-dimensional tail integral

    `∫_κ^∞ r ^ 2 * (r ^ N)⁻¹ dr = κ ^ (3 - N) / (N - 3)   (N ≥ 4, κ > 0)`.

On `(κ, ∞)` with `κ > 0` the integrand rewrites as the real power `r ^ (2 - N)`
(`r ^ 2 * (r ^ N)⁻¹ = r ^ (2 - N)`), and since `2 - N < -1` the value follows from
Mathlib's `integral_Ioi_rpow_of_lt`.  The integer exponent `3 - N` on the right is
the real exponent `3 - N`, i.e. `κ ^ (3 - N) / (N - 3)`.
-/

namespace Work.BoseFixB3.Eps

set_option autoImplicit false

/-- Pointwise real-power identity: for `r > 0`, `r ^ 2 * (r ^ N)⁻¹ = r ^ (2 - N)`. -/
lemma sq_mul_pow_inv_eq_rpow (N : ℕ) {r : ℝ} (hr : 0 < r) :
    r ^ 2 * (r ^ N)⁻¹ = r ^ ((2 : ℝ) - N) := by
  rw [← div_eq_mul_inv, ← Real.rpow_natCast r 2, ← Real.rpow_natCast r N]
  rw [← Real.rpow_sub hr]
  push_cast
  ring_nf

theorem Ioi_tail_zpow (N : ℕ) (hN : 4 ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    (∫ r in Set.Ioi κ, r ^ 2 * (r ^ N)⁻¹) = κ ^ (3 - (N : ℤ)) / ((N : ℝ) - 3) := by
  have hNr4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hconv : (∫ r in Set.Ioi κ, r ^ 2 * (r ^ N)⁻¹)
      = ∫ r in Set.Ioi κ, r ^ ((2 : ℝ) - N) := by
    refine MeasureTheory.setIntegral_congr_fun isOpen_Ioi.measurableSet (fun r hr => ?_)
    exact sq_mul_pow_inv_eq_rpow N (lt_trans hκ hr)
  rw [hconv, integral_Ioi_rpow_of_lt (by linarith : (2 : ℝ) - N < -1) hκ]
  have hexp : (2 : ℝ) - N + 1 = (3 : ℝ) - N := by ring
  rw [hexp]
  have hcast : ((3 : ℝ) - N) = ((3 - (N : ℤ) : ℤ) : ℝ) := by push_cast; ring
  have hden : (((3 - (N : ℤ) : ℤ) : ℝ)) = -(((N : ℝ)) - 3) := by push_cast; ring
  rw [hcast, Real.rpow_intCast, hden, neg_div_neg_eq]

end Work.BoseFixB3.Eps
