import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum.RealSqrt

namespace Commons.Analysis.InnerProductSpace

theorem half_mul_norm_mul_norm_le_inner_add_smul {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {X A E : F} {s ν : ℝ} (hs : 0 < s) (hν : 0 < ν) (hA : ν ≤ ‖A‖) (hX : 50 * ‖X‖ ≤ s * ν) (hE : 16 * ‖E‖ ≤ Real.sqrt 2 * ν) : (1 / 2) * ‖X + s • A‖ * ‖A + E‖ ≤ inner ℝ (X + s • A) (A + E) := by
  have ha_pos : 0 < ‖A‖ := lt_of_lt_of_le hν hA
  have hx_nn : 0 ≤ ‖X‖ := norm_nonneg X
  have he_nn : 0 ≤ ‖E‖ := norm_nonneg E
  have hsqrt2_le : Real.sqrt 2 ≤ 2 := by
    have h : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    rwa [show Real.sqrt 4 = 2 by norm_num] at h
  -- norm estimates
  have hn1 : ‖X + s • A‖ ≤ ‖X‖ + s * ‖A‖ := by
    calc ‖X + s • A‖ ≤ ‖X‖ + ‖s • A‖ := norm_add_le _ _
      _ = ‖X‖ + s * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hn2 : ‖A + E‖ ≤ ‖A‖ + ‖E‖ := norm_add_le _ _
  -- LHS bound
  have hL : (1 / 2) * ‖X + s • A‖ * ‖A + E‖ ≤ (1 / 2) * (‖X‖ + s * ‖A‖) * (‖A‖ + ‖E‖) := by
    have h1 : (1 / 2) * ‖X + s • A‖ ≤ (1 / 2) * (‖X‖ + s * ‖A‖) :=
      mul_le_mul_of_nonneg_left hn1 (by norm_num)
    exact mul_le_mul h1 hn2 (norm_nonneg _) (by positivity)
  -- expansion of the inner product
  have hexp : inner ℝ (X + s • A) (A + E) =
      inner ℝ X A + inner ℝ X E + s * inner ℝ A A + s * inner ℝ A E := by
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left, real_inner_smul_left]
    ring
  have hAA : inner ℝ A A = ‖A‖ ^ 2 := real_inner_self_eq_norm_sq A
  -- lower bounds for each inner product
  have hXA : -(‖X‖ * ‖A‖) ≤ inner ℝ X A := neg_le_of_abs_le (abs_real_inner_le_norm X A)
  have hXE : -(‖X‖ * ‖E‖) ≤ inner ℝ X E := neg_le_of_abs_le (abs_real_inner_le_norm X E)
  have hAE : -(‖A‖ * ‖E‖) ≤ inner ℝ A E := neg_le_of_abs_le (abs_real_inner_le_norm A E)
  have hInner : -(‖X‖ * ‖A‖) - ‖X‖ * ‖E‖ + s * ‖A‖ ^ 2 - s * (‖A‖ * ‖E‖) ≤
      inner ℝ (X + s • A) (A + E) := by
    rw [hexp, hAA]
    nlinarith [hXA, hXE, hAE, hs]
  -- scalar estimates
  have hx50 : 50 * ‖X‖ ≤ s * ‖A‖ := by nlinarith [hX, hA, hs.le]
  have he8 : 8 * ‖E‖ ≤ ‖A‖ := by nlinarith [hE, hsqrt2_le, hA, hν.le]
  have hA3E : (5 / 8) * ‖A‖ ≤ ‖A‖ - 3 * ‖E‖ := by nlinarith [he8]
  have hstep1 : (5 / 8) * s * ‖A‖ ^ 2 ≤ s * ‖A‖ * (‖A‖ - 3 * ‖E‖) := by
    have hsa : 0 ≤ s * ‖A‖ := by positivity
    have h := mul_le_mul_of_nonneg_left hA3E hsa
    nlinarith [h]
  have h3x : 3 * ‖X‖ ≤ (3 / 50) * (s * ‖A‖) := by nlinarith [hx50]
  have hae : ‖A‖ + ‖E‖ ≤ (9 / 8) * ‖A‖ := by nlinarith [he8]
  have hstep2 : 3 * ‖X‖ * (‖A‖ + ‖E‖) ≤ (27 / 400) * s * ‖A‖ ^ 2 := by
    have h := mul_le_mul h3x hae (by positivity) (by positivity)
    nlinarith [h]
  have hscalar : (1 / 2) * (‖X‖ + s * ‖A‖) * (‖A‖ + ‖E‖) ≤
      -(‖X‖ * ‖A‖) - ‖X‖ * ‖E‖ + s * ‖A‖ ^ 2 - s * (‖A‖ * ‖E‖) := by
    have hnn : 0 ≤ (223 / 400) * s * ‖A‖ ^ 2 := by positivity
    nlinarith [hstep1, hstep2, hnn]
  calc (1 / 2) * ‖X + s • A‖ * ‖A + E‖
      ≤ (1 / 2) * (‖X‖ + s * ‖A‖) * (‖A‖ + ‖E‖) := hL
    _ ≤ -(‖X‖ * ‖A‖) - ‖X‖ * ‖E‖ + s * ‖A‖ ^ 2 - s * (‖A‖ * ‖E‖) := hscalar
    _ ≤ inner ℝ (X + s • A) (A + E) := hInner

end Commons.Analysis.InnerProductSpace