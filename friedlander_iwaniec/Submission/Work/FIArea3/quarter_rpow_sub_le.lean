import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm

namespace Work.FIArea3

/-- The elementary real-variable gain of *FI* §10: if `N < a, b ≤ (1+θ)N` with `0 ≤ θ ≤ 1`, then
`(ab)^{-1/4} = (√(ab))^{-1/2}` differs from `N^{-1/2}` by at most `θ/(2√N)`.  This is the factor `θ`
that makes the trivial estimate sufficient for (10.10). -/
theorem quarter_rpow_sub_le {N θ a b : ℝ} (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ha : N < a) (ha' : a ≤ (1 + θ) * N) (hb : N < b) (hb' : b ≤ (1 + θ) * N) :
    |(a * b) ^ (-(1 : ℝ) / 4) - N ^ (-(1 : ℝ) / 2)| ≤ θ / (2 * Real.sqrt N) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hapos : 0 < a := lt_trans hNpos ha
  have hbpos : 0 < b := lt_trans hNpos hb
  have habpos : 0 < a * b := mul_pos hapos hbpos
  -- `N^2 < ab`, hence `ab^{-1/4} < N^{-1/2}` (base monotonicity for a negative exponent)
  have hN2lt : N ^ 2 < a * b := by
    have h := mul_lt_mul ha (le_of_lt hb) hNpos hapos.le
    nlinarith [h]
  have hNsq : N ≤ N ^ 2 := by nlinarith [hN]
  -- `ab ≤ (1+θ)^2 N^2`, hence `ab^{-1/4} ≥ (1+θ)^{-1/2} N^{-1/2}`
  have hab_le : a * b ≤ (1 + θ) ^ 2 * N ^ 2 := by
    have h := mul_le_mul ha' hb' hbpos.le (by positivity : (0 : ℝ) ≤ (1 + θ) * N)
    nlinarith [h]
  -- rewrite `(N^2)^{-1/4}` as `N^{-1/2}`
  have hN2 : (N ^ 2) ^ (-(1 : ℝ) / 4) = N ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_mul hNpos.le]
    norm_num
  have hA_lt_B : (a * b) ^ (-(1 : ℝ) / 4) < N ^ (-(1 : ℝ) / 2) := by
    rw [← hN2]
    exact Real.rpow_lt_rpow_of_neg (pow_pos hNpos 2) hN2lt (by norm_num)
  -- rewrite `((1+θ)^2 N^2)^{-1/4}` as `(1+θ)^{-1/2} N^{-1/2}`
  have hsplit : ((1 + θ) ^ 2 * N ^ 2) ^ (-(1 : ℝ) / 4)
      = (1 + θ) ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have h1 : ((1 + θ) ^ 2) ^ (-(1 : ℝ) / 4) = (1 + θ) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (1 + θ) 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + θ)]
      norm_num
    rw [h1, hN2]
  have hA_ge : ((1 + θ) ^ 2 * N ^ 2) ^ (-(1 : ℝ) / 4) ≤ (a * b) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos habpos hab_le (by norm_num)
  rw [hsplit] at hA_ge
  have hBsubA_le : N ^ (-(1 : ℝ) / 2) - (a * b) ^ (-(1 : ℝ) / 4)
      ≤ N ^ (-(1 : ℝ) / 2) * (1 - (1 + θ) ^ (-(1 : ℝ) / 2)) := by
    nlinarith [hA_ge]
  -- the elementary inequality `1 - (1+θ)^{-1/2} ≤ θ/2` for `0 ≤ θ ≤ 1`
  have hkey : 1 - (1 + θ) ^ (-(1 : ℝ) / 2) ≤ θ / 2 := by
    have htpos : (0 : ℝ) < 1 + θ := by linarith
    have hnonneg : (0 : ℝ) ≤ 1 - θ / 2 := by linarith
    have h3 : (0 : ℝ) ≤ 3 - θ := by linarith
    have hsq : (1 + θ) * (1 - θ / 2) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sq_nonneg θ) h3]
    have hle : Real.sqrt ((1 + θ) * (1 - θ / 2) ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 + θ) ((1 - θ / 2) ^ 2), Real.sqrt_sq hnonneg,
      Real.sqrt_one] at hle
    have hsqrt_pos : 0 < Real.sqrt (1 + θ) := Real.sqrt_pos.mpr htpos
    have h1 : 1 - θ / 2 ≤ 1 / Real.sqrt (1 + θ) := by
      rw [le_div_iff₀ hsqrt_pos]
      nlinarith [hle]
    have h2 : (1 + θ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt (1 + θ) := by
      rw [show (-(1 : ℝ) / 2) = -(1 / 2) by norm_num, Real.rpow_neg (le_of_lt htpos) (1 / 2),
        Real.sqrt_eq_rpow]
      field_simp
    rw [h2]
    linarith
  have hNhalf_eq : N ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt N := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by norm_num, Real.rpow_neg hNpos.le (1 / 2),
      Real.sqrt_eq_rpow]
    field_simp
  have hstep2 : N ^ (-(1 : ℝ) / 2) * (1 - (1 + θ) ^ (-(1 : ℝ) / 2))
      ≤ θ / (2 * Real.sqrt N) := by
    calc N ^ (-(1 : ℝ) / 2) * (1 - (1 + θ) ^ (-(1 : ℝ) / 2))
        ≤ N ^ (-(1 : ℝ) / 2) * (θ / 2) :=
          mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hNpos.le _)
      _ = θ / (2 * Real.sqrt N) := by
          rw [hNhalf_eq]
          field_simp
  rw [abs_of_neg (by linarith)]
  linarith [hBsubA_le.trans hstep2]

end Work.FIArea3
