import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Defs

namespace Commons.Analysis.InnerProductSpace

/-- Auxiliary real inequality: if `0 < c` and `c / (1 + e ^ 2) ≤ r ≤ c * (1 + e ^ 2)`,
then `|r - c| ≤ c * e ^ 2`. -/
private lemma abs_sub_le_mul_sq {r c e : ℝ} (hc : 0 < c)
    (hrlo : c / (1 + e ^ 2) ≤ r) (hrhi : r ≤ c * (1 + e ^ 2)) :
    |r - c| ≤ c * e ^ 2 := by
  have hpos : (0:ℝ) < 1 + e ^ 2 := by positivity
  have hkey : c - c / (1 + e ^ 2) ≤ c * e ^ 2 := by
    have h1 : c - c * e ^ 2 ≤ c / (1 + e ^ 2) := by
      rw [le_div_iff₀ hpos]
      nlinarith [mul_nonneg hc.le (sq_nonneg (e ^ 2))]
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem norm_sub_smul_sq_le_ratio {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u a : F} {c e : ℝ} (hc : 0 < c) (hu : 0 < ‖u‖) (ha : ‖a‖ = 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hrlo : c / (1 + e ^ 2) ≤ ‖u‖) (hrhi : ‖u‖ ≤ c * (1 + e ^ 2))
    (hδ : ‖(‖u‖)⁻¹ • u - a‖ ≤ 64 * e) :
    ‖u - c • a‖ ^ 2 ≤ 2 ^ 16 * e ^ 2 * c ^ 2 := by
  have _ha : ‖a‖ = 1 := ha
  have hrne : ‖u‖ ≠ 0 := ne_of_gt hu
  -- the unit vector `v = ‖u‖⁻¹ • u`
  have hvn : ‖(‖u‖)⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hu, inv_mul_cancel₀ hrne]
  have hvu : ‖u‖ • ((‖u‖)⁻¹ • u) = u := by
    rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
  -- decomposition of the vector whose norm we bound
  have hdecomp : u - c • a = (‖u‖ - c) • ((‖u‖)⁻¹ • u) + c • ((‖u‖)⁻¹ • u - a) := by
    rw [smul_sub, sub_smul, hvu]
    abel
  -- first summand: `‖(‖u‖ - c) • v‖ ≤ c * e ^ 2`
  have hstep1 : ‖(‖u‖ - c) • ((‖u‖)⁻¹ • u)‖ ≤ c * e ^ 2 := by
    rw [norm_smul, hvn, mul_one, Real.norm_eq_abs]
    exact abs_sub_le_mul_sq hc hrlo hrhi
  -- second summand: `‖c • (v - a)‖ ≤ c * (64 * e)`
  have hstep2 : ‖c • ((‖u‖)⁻¹ • u - a)‖ ≤ c * (64 * e) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hδ hc.le
  -- triangle inequality
  have hsum : ‖u - c • a‖ ≤ c * e ^ 2 + c * (64 * e) := by
    rw [hdecomp]
    calc ‖(‖u‖ - c) • ((‖u‖)⁻¹ • u) + c • ((‖u‖)⁻¹ • u - a)‖
        ≤ ‖(‖u‖ - c) • ((‖u‖)⁻¹ • u)‖ + ‖c • ((‖u‖)⁻¹ • u - a)‖ := norm_add_le _ _
      _ ≤ c * e ^ 2 + c * (64 * e) := add_le_add hstep1 hstep2
  have harith : c * e ^ 2 + c * (64 * e) ≤ 129 * c * e := by
    nlinarith [he0, he1, hc, mul_nonneg hc.le he0, mul_nonneg (mul_nonneg hc.le he0) (sub_nonneg.mpr he1)]
  have hbound : ‖u - c • a‖ ≤ 129 * c * e := le_trans hsum harith
  -- square both sides
  have hnn : 0 ≤ ‖u - c • a‖ := norm_nonneg _
  have hsq : ‖u - c • a‖ ^ 2 ≤ (129 * c * e) ^ 2 := pow_le_pow_left₀ hnn hbound 2
  have hrhs : (129 * c * e) ^ 2 ≤ 2 ^ 16 * e ^ 2 * c ^ 2 := by
    have h65536 : (2:ℝ) ^ 16 = 65536 := by norm_num
    rw [h65536]
    nlinarith [sq_nonneg (c * e)]
  exact le_trans hsq hrhs

end Commons.Analysis.InnerProductSpace