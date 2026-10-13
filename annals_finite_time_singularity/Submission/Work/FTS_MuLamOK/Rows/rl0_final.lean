import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Rl0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

/-- The `α`-power appearing in the final arithmetic (`α ^ (-(3/2))`) is the inverse of
`α √α`: the two agree because `α ^ (3/2) = α ^ 1 * α ^ (1/2) = α * √α`. -/
theorem rpow_neg_three_halves (α : ℝ) (hα : 0 < α) :
    α ^ (-(3 / 2 : ℝ)) = (α * Real.sqrt α)⁻¹ := by
  have h32 : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have h1 : α ^ (-(3 / 2 : ℝ)) * (α * Real.sqrt α) = 1 := by
    rw [← h32, ← Real.rpow_add hα, show (-(3 / 2 : ℝ)) + 3 / 2 = 0 by norm_num,
      Real.rpow_zero]
  exact eq_inv_of_mul_eq_one_left h1

/-- **The final arithmetic row of the `N₀` estimate.**

The two coefficients `A₀`, `B₀` of the pointwise bound for `N₀` (see `H6Pair6Aux/Rl0Defs`)
satisfy the fully explicit estimate
`3 √(7 (A₀ X² + π B₀)) ≤ 10⁵ (α² + √α X + α^{-3/2} X²)` on `0 < α ≤ 1`, `X ≥ 0`.

The proof squares the inequality and bounds the left-hand side term by term: from
`A₀ ≤ 90 X²/α² + 16 α²` and `B₀ ≤ 25600 α⁴ + 90000 α² X²` one gets
`63 (A₀X² + πB₀) ≤ 5670 X⁴/α² + 1008 α²X² + 1612800π α⁴ + 5670000π α²X²`, and each of the
four summands is a coefficient times `(X²/(α√α))² = X⁴/α³ ≥ X⁴/α²`, `(√α X)² = αX² ≥ α²X²`
or `(α²)² = α⁴`, so the whole left-hand side is at most
`(1008 + 5670000π) ((α²)² + (√αX)² + (X²/(α√α))²) ≤ (1008 + 5670000π) (α² + √αX + X²/(α√α))²`
with `1008 + 5670000π ≤ 10^10` because `π ≤ 4`. -/
theorem rl0_final {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    3 * Real.sqrt (7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X))
      ≤ 10 ^ 5 * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hX4 : 0 ≤ X ^ 4 := by positivity
  have hs0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hpi0 : 0 ≤ Real.pi := Real.pi_nonneg
  have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
  have hsq : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  -- the constant of the estimate
  have hM0 : 0 ≤ (1008 : ℝ) + 5670000 * Real.pi := by nlinarith [hpi0]
  have hM5670 : (5670 : ℝ) ≤ 1008 + 5670000 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hM1612800 : 1612800 * Real.pi ≤ 1008 + 5670000 * Real.pi := by nlinarith [hpi0]
  have hM10 : (1008 : ℝ) + 5670000 * Real.pi ≤ 10 ^ 10 := by nlinarith [hpi4]
  -- ## the two coefficient bounds
  have hL1 : Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
      ≤ 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2) := by
    have h := mul_le_mul_of_nonneg_right
      (Work.FTS.StrongPersist.H6Pair6Aux.A₀_le (X := X) hα hα1) hX2
    have he : (90 * X ^ 2 / α ^ 2 + 16 * α ^ 2) * X ^ 2
        = 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2) := by ring
    linarith [h, he.le, he.ge]
  have hL2 : Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X
      ≤ 25600 * Real.pi * α ^ 4 + 90000 * Real.pi * (α ^ 2 * X ^ 2) := by
    have h := mul_le_mul_of_nonneg_left
      (Work.FTS.StrongPersist.H6Pair6Aux.B₀_le α X) hpi0
    have he : Real.pi * (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2)
        = 25600 * Real.pi * α ^ 4 + 90000 * Real.pi * (α ^ 2 * X ^ 2) := by ring
    linarith [h, he.le, he.ge]
  have hLhi : Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X
      ≤ 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2)
        + 25600 * Real.pi * α ^ 4 + 90000 * Real.pi * (α ^ 2 * X ^ 2) := by
    linarith [hL1, hL2]
  -- ## multiply by `63 = 7 * 9`
  have h63 : 63 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)
      ≤ 5670 * (X ^ 4 / α ^ 2) + 1008 * (α ^ 2 * X ^ 2)
        + 1612800 * Real.pi * α ^ 4 + 5670000 * Real.pi * (α ^ 2 * X ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hLhi (by norm_num : (0 : ℝ) ≤ 63)
    have he : 63 * (90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2)
          + 25600 * Real.pi * α ^ 4 + 90000 * Real.pi * (α ^ 2 * X ^ 2))
        = 5670 * (X ^ 4 / α ^ 2) + 1008 * (α ^ 2 * X ^ 2)
          + 1612800 * Real.pi * α ^ 4 + 5670000 * Real.pi * (α ^ 2 * X ^ 2) := by ring
    linarith [h, he.le, he.ge]
  -- ## the three profiles: `X⁴/α² ≤ (X²/(α√α))²`, `α²X² ≤ (√αX)²`, `α⁴ = (α²)²`
  have hden : (α * Real.sqrt α) ^ 2 = α ^ 3 := by
    rw [mul_pow, hsq]; ring
  have hr2 : ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 = X ^ 4 / α ^ 3 := by
    rw [mul_pow, inv_pow, hden]; ring
  have hsX : (Real.sqrt α * X) ^ 2 = α * X ^ 2 := by rw [mul_pow, hsq]
  have h32 : α ^ 3 ≤ α ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hα1 (sq_nonneg α)
    nlinarith [h]
  have hc1 : X ^ 4 / α ^ 2 ≤ ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 := by
    rw [hr2]
    exact div_le_div_of_nonneg_left hX4 (by positivity) h32
  have hc2 : α ^ 2 * X ^ 2 ≤ (Real.sqrt α * X) ^ 2 := by
    rw [hsX]
    have h1 : 0 ≤ α * X ^ 2 := mul_nonneg hα.le hX2
    have h2 : α * X ^ 2 * (α - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1 (sub_nonpos.mpr hα1)
    nlinarith [h2]
  -- ## the four summands
  have hT1 : 5670 * (X ^ 4 / α ^ 2)
      ≤ ((1008 : ℝ) + 5670000 * Real.pi) * ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 := by
    have h1 : 5670 * (X ^ 4 / α ^ 2)
        ≤ ((1008 : ℝ) + 5670000 * Real.pi) * (X ^ 4 / α ^ 2) :=
      mul_le_mul_of_nonneg_right hM5670 (by positivity)
    have h2 : ((1008 : ℝ) + 5670000 * Real.pi) * (X ^ 4 / α ^ 2)
        ≤ ((1008 : ℝ) + 5670000 * Real.pi) * ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hc1 hM0
    linarith [h1, h2]
  have hT24 : 1008 * (α ^ 2 * X ^ 2) + 5670000 * Real.pi * (α ^ 2 * X ^ 2)
      ≤ ((1008 : ℝ) + 5670000 * Real.pi) * (Real.sqrt α * X) ^ 2 := by
    have hfac : 1008 * (α ^ 2 * X ^ 2) + 5670000 * Real.pi * (α ^ 2 * X ^ 2)
        = ((1008 : ℝ) + 5670000 * Real.pi) * (α ^ 2 * X ^ 2) := by ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hc2 hM0
  have hT3 : 1612800 * Real.pi * α ^ 4
      ≤ ((1008 : ℝ) + 5670000 * Real.pi) * (α ^ 2) ^ 2 := by
    have he : (α ^ 2) ^ 2 = α ^ 4 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hM1612800 (by positivity)
  -- ## assemble
  have hSsum : 5670 * (X ^ 4 / α ^ 2) + 1008 * (α ^ 2 * X ^ 2)
        + 1612800 * Real.pi * α ^ 4 + 5670000 * Real.pi * (α ^ 2 * X ^ 2)
      ≤ ((1008 : ℝ) + 5670000 * Real.pi)
        * ((α ^ 2) ^ 2 + (Real.sqrt α * X) ^ 2 + ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2) := by
    nlinarith [hT1, hT24, hT3]
  have hp0 : 0 ≤ α ^ 2 := by positivity
  have hq0 : 0 ≤ Real.sqrt α * X := mul_nonneg hs0 hX
  have hr0 : 0 ≤ (α * Real.sqrt α)⁻¹ * X ^ 2 :=
    mul_nonneg (inv_nonneg.mpr (mul_nonneg hα.le hs0)) hX2
  have hpqr : (α ^ 2) ^ 2 + (Real.sqrt α * X) ^ 2 + ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2
      ≤ (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 := by
    nlinarith [mul_nonneg hp0 hq0, mul_nonneg hp0 hr0, mul_nonneg hq0 hr0]
  have hS0 : 0 ≤ α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2 :=
    add_nonneg (add_nonneg hp0 hq0) hr0
  have hkey : 63 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)
      ≤ 10 ^ 10 * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 := by
    have hΨ0 : 0 ≤ (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 :=
      sq_nonneg _
    have h1 : ((1008 : ℝ) + 5670000 * Real.pi)
          * ((α ^ 2) ^ 2 + (Real.sqrt α * X) ^ 2 + ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2)
        ≤ ((1008 : ℝ) + 5670000 * Real.pi)
          * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hpqr hM0
    have h2 : ((1008 : ℝ) + 5670000 * Real.pi)
          * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2
        ≤ 10 ^ 10 * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hM10 hΨ0
    linarith [h63, hSsum, h1, h2]
  -- ## the square root
  have h63' : 3 * Real.sqrt (7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X))
      = Real.sqrt (63 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)) := by
    rw [show (63 : ℝ) * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
          + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)
        = 9 * (7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
          + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
      show Real.sqrt 9 = 3 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [h63', rpow_neg_three_halves α hα]
  refine le_trans (Real.sqrt_le_sqrt hkey) ?_
  have hsq10 : 10 ^ 10 * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2
      = ((10 : ℝ) ^ 5 * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2)) ^ 2 := by
    rw [show (10 : ℝ) ^ 10 = ((10 : ℝ) ^ 5) ^ 2 by norm_num]
    ring
  rw [hsq10, Real.sqrt_sq (mul_nonneg (by norm_num) hS0)]

end Work.FTS_MuLamOK.Rows
