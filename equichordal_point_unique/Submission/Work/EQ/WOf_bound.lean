import Mathlib
import Submission.Work.EQ.GermSetup
import Submission.Work.EQ.SqrtNearOne

/-!
# The bound `‖WOf ρ u‖ ≤ 2`

With `β = betaOf ρ u = -1 + u² ρ u` and `S = SOf ρ u = (1 + u² β²)^{1/2}` one has
`WOf ρ u = β²/(1 + S)`.  On the disc `‖u‖ ≤ germR a`, if `‖ρ‖ ≤ 1` there,
then `‖β‖ ≤ 1 + (germR a)²`, while `‖1 + S‖ ≥ 1`
(`norm_sqHalf_add_one_ge_one`, valid as soon as `‖u² β²‖ < 1`).
Hence `‖WOf ρ u‖ ≤ (1 + (germR a)²)² ≤ 2`, because `germR a ≤ 1/16`.
-/

namespace Work.EQ

open Complex Metric

theorem WOf_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) {u : ℂ} (hu : ‖u‖ ≤ germR a) :
    ‖WOf ρ u‖ ≤ 2 := by
  -- Bound on `β = -1 + u²ρu`.
  have hβ : ‖betaOf ρ u‖ ≤ 1 + (germR a) ^ 2 := by
    have h1 : ‖(-1 : ℂ) + u ^ 2 * ρ u‖ ≤ ‖(-1 : ℂ)‖ + ‖u ^ 2 * ρ u‖ := norm_add_le _ _
    have h2 : ‖u ^ 2 * ρ u‖ ≤ (germR a) ^ 2 := by
      simp only [norm_mul, norm_pow]
      calc ‖u‖ ^ 2 * ‖ρ u‖ ≤ (germR a) ^ 2 * 1 :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg u) hu 2) (hρ u hu) (norm_nonneg _)
              (by positivity)
        _ = (germR a) ^ 2 := by ring
    simp only [norm_neg, norm_one] at h1
    rw [betaOf]
    linarith
  have hβ2 : ‖betaOf ρ u‖ ^ 2 ≤ (1 + (germR a) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hβ 2
  -- The argument `u²β²` of the square root has norm `< 1`.
  have hz : ‖u ^ 2 * (betaOf ρ u) ^ 2‖ < 1 := by
    simp only [norm_mul, norm_pow]
    have hu2 : ‖u‖ ^ 2 ≤ (germR a) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
    have hgsq : (germR a) ^ 2 ≤ 1 / 256 := germR_sq_le ha0 ha1
    have hsum : (1 + (germR a) ^ 2) ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg (germR a)]
    calc ‖u‖ ^ 2 * ‖betaOf ρ u‖ ^ 2
        ≤ (germR a) ^ 2 * (1 + (germR a) ^ 2) ^ 2 :=
          mul_le_mul hu2 hβ2 (by positivity) (by positivity)
      _ ≤ (1 / 256) * 2 := mul_le_mul hgsq hsum (by positivity) (by norm_num)
      _ < 1 := by norm_num
  -- The denominator `1 + S` has norm at least one.
  have hden : 1 ≤ ‖SOf ρ u + 1‖ := by
    have h := norm_sqHalf_add_one_ge_one hz
    simpa only [SOf, sqHalf] using h
  have hden' : 1 ≤ ‖1 + SOf ρ u‖ := by rw [add_comm]; exact hden
  have hdpos : (0 : ℝ) < ‖1 + SOf ρ u‖ := lt_of_lt_of_le one_pos hden'
  rw [WOf, norm_div, norm_pow]
  rw [div_le_iff₀ hdpos]
  calc ‖betaOf ρ u‖ ^ 2 ≤ (1 + (germR a) ^ 2) ^ 2 := hβ2
    _ ≤ 2 := by
        have hgsq : (germR a) ^ 2 ≤ 1 / 256 := germR_sq_le ha0 ha1
        nlinarith [sq_nonneg (germR a)]
    _ ≤ 2 * ‖1 + SOf ρ u‖ := by nlinarith [hden']

end Work.EQ
