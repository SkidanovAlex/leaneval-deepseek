import Mathlib
import Submission.Commons.Analysis.Integral.circle_l2_mean_le_rpow_quarter

namespace Commons.Analysis.Integral

open MeasureTheory Set Real Filter
open scoped Topology

/-- Arithmetic identity behind the second Landen/AGM step: for `T > 0`,
`(T·((T+1)/2)^2)^(1/4)` is the reciprocal of `(T^2)^(-1/8)·√(2/(1+T))`. -/
private lemma inv_rpow_quarter_eq_mul (T : ℝ) (hT : 0 < T) :
    ((T * ((T + 1) / 2) ^ 2) ^ (1 / 4 : ℝ))⁻¹
      = (T ^ 2) ^ (-(1 / 8 : ℝ)) * Real.sqrt (2 / (1 + T)) := by
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have h1 : (0 : ℝ) < (T + 1) / 2 := by linarith
  have hbase : (0 : ℝ) ≤ T * ((T + 1) / 2) ^ 2 := by positivity
  have e1 : (((T + 1) / 2) ^ 2) ^ (-(1 / 4 : ℝ)) = ((T + 1) / 2) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast ((T + 1) / 2) 2,
      ← Real.rpow_mul (le_of_lt h1) ((2 : ℕ) : ℝ) (-(1 / 4 : ℝ)),
      show ((2 : ℕ) : ℝ) * (-(1 / 4 : ℝ)) = -(1 / 2 : ℝ) by norm_num]
  have e2 : Real.sqrt (2 / (1 + T)) = ((T + 1) / 2) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, show 2 / (1 + T) = ((T + 1) / 2)⁻¹ by field_simp; ring]
    rw [Real.inv_rpow (le_of_lt h1) (1 / 2 : ℝ), Real.rpow_neg (le_of_lt h1) (1 / 2 : ℝ)]
  have e3 : (T ^ 2) ^ (-(1 / 8 : ℝ)) = T ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast T 2,
      ← Real.rpow_mul hT0 ((2 : ℕ) : ℝ) (-(1 / 8 : ℝ)),
      show ((2 : ℕ) : ℝ) * (-(1 / 8 : ℝ)) = -(1 / 4 : ℝ) by norm_num]
  rw [← Real.rpow_neg hbase (1 / 4 : ℝ),
    Real.mul_rpow (le_of_lt hT) (by positivity), e1, e3, e2]

theorem circle_l2_mean_le_rpow_eighth {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 / Real.pi) * ∫ θ in (0)..Real.pi,
        (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹
      ≤ (1 - s ^ 2) ^ (-(1 / 8 : ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - s ^ 2))) := by
  have hA : 0 < 1 + s := by linarith
  have hB : 0 < 1 - s := by linarith
  have hP : 0 < 1 - s ^ 2 := by nlinarith [hs0, hs1]
  set T : ℝ := Real.sqrt (1 - s ^ 2) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; exact Real.sqrt_pos.mpr hP
  have hTsq : T ^ 2 = 1 - s ^ 2 := by rw [hTdef]; exact Real.sq_sqrt hP.le
  have hYpos : (0 : ℝ) < (T * ((T + 1) / 2) ^ 2) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  -- Step 1: `circle_l2_mean_eq` turns the circle mean into `(2/π)·Φ((1+s)², (1-s)²)`.
  have hI := circle_l2_mean_eq s hs0 hs1
  -- Step 2: Landen (AGM) step with `(a,b) = (1+s, 1-s)`.
  have hL1 : (∫ x in Ioi (0 : ℝ),
        (Real.sqrt ((x ^ 2 + (1 + s) ^ 2) * (x ^ 2 + (1 - s) ^ 2)))⁻¹)
      = ∫ x in Ioi (0 : ℝ), (Real.sqrt ((x ^ 2 + (1 - s ^ 2)) * (x ^ 2 + 1)))⁻¹ := by
    have h := integral_inv_sqrt_prod_landen (a := 1 + s) (b := 1 - s) hA hB
    simpa only [show (1 + s) * (1 - s) = 1 - s ^ 2 by ring,
      show ((1 + s) + (1 - s)) / 2 = 1 by ring, one_pow] using h
  -- Step 3: Landen (AGM) step with `(a,b) = (T, 1)`, `T = √(1-s²)`.
  have hL2 : (∫ x in Ioi (0 : ℝ), (Real.sqrt ((x ^ 2 + (1 - s ^ 2)) * (x ^ 2 + 1)))⁻¹)
      = ∫ x in Ioi (0 : ℝ),
          (Real.sqrt ((x ^ 2 + T) * (x ^ 2 + ((T + 1) / 2) ^ 2)))⁻¹ := by
    have h := integral_inv_sqrt_prod_landen (a := T) (b := 1) hTpos (by norm_num)
    simpa only [mul_one, one_pow, hTsq] using h
  -- Step 4: the AM-GM bound `∫ ≤ π/(2 (PQ)^{1/4})`.
  have hD : (∫ x in Ioi (0 : ℝ),
        (Real.sqrt ((x ^ 2 + T) * (x ^ 2 + ((T + 1) / 2) ^ 2)))⁻¹)
      ≤ Real.pi / (2 * (T * ((T + 1) / 2) ^ 2) ^ (1 / 4 : ℝ)) :=
    integral_inv_sqrt_prod_le T (((T + 1) / 2) ^ 2) hTpos (by positivity)
  have hchain : (∫ x in Ioi (0 : ℝ),
        (Real.sqrt ((x ^ 2 + (1 + s) ^ 2) * (x ^ 2 + (1 - s) ^ 2)))⁻¹)
      ≤ Real.pi / (2 * (T * ((T + 1) / 2) ^ 2) ^ (1 / 4 : ℝ)) := by
    rw [hL1, hL2]; exact hD
  -- Step 5: cancel `π` and identify the resulting reciprocal with the target RHS.
  have hYne : (T * ((T + 1) / 2) ^ 2) ^ (1 / 4 : ℝ) ≠ 0 := ne_of_gt hYpos
  have hstep2 : (1 / Real.pi)
        * (2 * (Real.pi / (2 * (T * ((T + 1) / 2) ^ 2) ^ (1 / 4 : ℝ))))
      = ((T * ((T + 1) / 2) ^ 2) ^ (1 / 4 : ℝ))⁻¹ := by
    field_simp
  have hstep1 : (1 / Real.pi)
        * (2 * (∫ x in Ioi (0 : ℝ),
            (Real.sqrt ((x ^ 2 + (1 + s) ^ 2) * (x ^ 2 + (1 - s) ^ 2)))⁻¹))
      ≤ (1 / Real.pi)
        * (2 * (Real.pi / (2 * (T * ((T + 1) / 2) ^ 2) ^ (1 / 4 : ℝ)))) := by
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul_of_nonneg_left hchain (by norm_num)
    · positivity
  rw [hstep2, inv_rpow_quarter_eq_mul T hTpos] at hstep1
  rw [hI, ← hTsq]
  exact hstep1

end Commons.Analysis.Integral
