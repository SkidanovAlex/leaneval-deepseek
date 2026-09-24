import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.cbar_integral_le

namespace Work.NumberTheory.Chen.BTermCount

open MeasureTheory intervalIntegral

/-! ## Rational constants for the sharp BJS bound at the sift limit `1/10`

This file collects the (rational) numerical constants used to certify

`∫_{1/10}^{1/3} log (2 − 3β)/(β (1 − β)) dβ ≤ 1/2`,

together with the elementary `log` bounds about them, so that the analytic pieces can be proved
against a single interface.

The strategy is: substitute `β = (2−u)/3`, splitting the resulting integral into
`P2 = ∫_1^{17/10} log u/(2−u) du` and `P1 = ∫_1^{17/10} log u/(1+u) du`.

* `P2` is further substituted to `∫_{3/10}^1 log (2−y)/y dy = log 2 · log (10/3) + ∫_{3/10}^1 log(1−y/2)/y`,
  and the last integral is bounded by the four term Taylor bound `log (1−z) ≤ −z − z²/2 − z³/3 − z⁴/4`,
  giving `P2 ≤ cbarHalfC1 * cbarHalfC2 − cbarHalfR4`.
* `P1` is split at `6/5`, where `1/(1+u) ≤ (6/11)/u` resp. `≤ (17/27)/u`, giving
  `P1 ≤ (17/54)(log (17/10))² − (25/594)(log (6/5))²`
  `≤ (17/54) cbarHalfC3² − (25/594) cbarHalfLb1²`.
* The certificate is `cbarHalfC1*cbarHalfC2 − cbarHalfR4 + (17/54)cbarHalfC3² − (25/594)cbarHalfLb1²
  ≤ 1/2` (its value is `0.4975090…`). -/

/-- `log 2`, in the rational decimal form furnished by Mathlib's `Real.log_two_lt_d9`. -/
noncomputable def cbarHalfC1 : ℝ := 6931471808/10^10

/-- Truncation after `10` terms of `log (6/5) = ∑_{m ≥ 1} (1/6)^m/m`, a lower bound for `log (6/5)`. -/
noncomputable def cbarHalfLb1 : ℝ := ∑ m ∈ Finset.range 10, (1/6:ℝ)^(m+1)/(m+1)

/-- Truncation after `10` terms of `log (20/17) = ∑_{m ≥ 1} (3/20)^m/m`, a lower bound for
`log (20/17)`. -/
noncomputable def cbarHalfLb2 : ℝ := ∑ m ∈ Finset.range 10, (3/20:ℝ)^(m+1)/(m+1)

/-- `cbarHalfC2 := 2 log 2 − log (6/5) = log (10/3)`, rounded up. -/
noncomputable def cbarHalfC2 : ℝ := 2*cbarHalfC1 - cbarHalfLb1

/-- `cbarHalfC3 := log 2 − log (20/17) = log (17/10)`, rounded up. -/
noncomputable def cbarHalfC3 : ℝ := cbarHalfC1 - cbarHalfLb2

/-- `∫_{3/10}^1 (1/2 + y/8 + y²/24 + y³/64) dy = 9775031/23040000`, the value of the four term
Taylor majorant of `−log (1 − y/2)/y` integrated over `[3/10, 1]`. -/
noncomputable def cbarHalfR4 : ℝ := 9775031/23040000

/-- Truncation of the series `-log (1-z) = ∑_{m ≥ 1} z^m/m`: for `0 ≤ z < 1` and every `N`,
`log (1-z) ≤ -∑_{m<N} z^{m+1}/(m+1)`. -/
theorem cbarHalf_log_trunc (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (N : ℕ) :
    Real.log (1 - z) ≤ -(∑ m ∈ Finset.range N, z^(m+1)/(m+1)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := z) (by rwa [abs_of_nonneg hz0])
  have h2 : (∑ m ∈ Finset.range N, z^(m+1)/(m+1)) ≤ ∑' n : ℕ, z^(n+1)/(n+1) :=
    Summable.sum_le_tsum (Finset.range N)
      (fun b _ => div_nonneg (pow_nonneg hz0 (b+1)) (by positivity)) h.summable
  rw [h.tsum_eq] at h2
  linarith

theorem cbarHalf_log_two_lt : Real.log 2 < cbarHalfC1 := by
  have h := log_two_lt_rat
  simpa [cbarHalfC1] using h

theorem cbarHalfC1_nonneg : 0 ≤ cbarHalfC1 := by norm_num [cbarHalfC1]

theorem cbarHalfLb1_nonneg : 0 ≤ cbarHalfLb1 := by
  rw [cbarHalfLb1]
  refine Finset.sum_nonneg fun m _ => div_nonneg (pow_nonneg (by norm_num) _) (by positivity)

theorem cbarHalfLb2_nonneg : 0 ≤ cbarHalfLb2 := by
  rw [cbarHalfLb2]
  refine Finset.sum_nonneg fun m _ => div_nonneg (pow_nonneg (by norm_num) _) (by positivity)

theorem cbarHalfLb1_le_log : cbarHalfLb1 ≤ Real.log (6/5) := by
  have h := cbarHalf_log_trunc (1/6) (by norm_num) (by norm_num) 10
  have hlog : Real.log (1 - (1:ℝ)/6) = -Real.log (6/5) := by
    rw [show (1:ℝ) - 1/6 = 5/6 by norm_num, ← Real.log_inv]
    norm_num
  rw [hlog] at h
  have h' : (∑ m ∈ Finset.range 10, (1/6:ℝ)^(m+1)/(m+1)) ≤ Real.log (6/5) := by linarith
  simpa [cbarHalfLb1] using h'

theorem cbarHalfLb2_le_log : cbarHalfLb2 ≤ Real.log (20/17) := by
  have h := cbarHalf_log_trunc (3/20) (by norm_num) (by norm_num) 10
  have hlog : Real.log (1 - (3:ℝ)/20) = -Real.log (20/17) := by
    rw [show (1:ℝ) - 3/20 = 17/20 by norm_num, ← Real.log_inv]
    norm_num
  rw [hlog] at h
  have h' : (∑ m ∈ Finset.range 10, (3/20:ℝ)^(m+1)/(m+1)) ≤ Real.log (20/17) := by linarith
  simpa [cbarHalfLb2] using h'

/-- `log (10/3) = 2 log 2 − log (6/5) ≤ cbarHalfC2`. -/
theorem cbarHalf_log_ten_thirds_le : Real.log (10/3) ≤ cbarHalfC2 := by
  have hsplit : Real.log (10/3) = Real.log 4 - Real.log (6/5) := by
    rw [← Real.log_div (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (6:ℝ)/5 ≠ 0)]
    norm_num
  rw [hsplit, Real.log_four_eq, cbarHalfC2]
  linarith [cbarHalf_log_two_lt.le, cbarHalfLb1_le_log]

/-- `log (17/10) = log 2 − log (20/17) ≤ cbarHalfC3`. -/
theorem cbarHalf_log_seventeen_tenths_le : Real.log (17/10) ≤ cbarHalfC3 := by
  have hsplit : Real.log (17/10) = Real.log 2 - Real.log (20/17) := by
    rw [← Real.log_div (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (20:ℝ)/17 ≠ 0)]
    norm_num
  rw [hsplit, cbarHalfC3]
  linarith [cbarHalf_log_two_lt.le, cbarHalfLb2_le_log]

theorem cbarHalf_log_ten_thirds_nonneg : 0 ≤ Real.log (10/3) := Real.log_nonneg (by norm_num)

theorem cbarHalf_log_seventeen_tenths_nonneg : 0 ≤ Real.log (17/10) := Real.log_nonneg (by norm_num)

/-- The final rational certificate: `cbarHalfC1*cbarHalfC2 − cbarHalfR4 + (17/54)cbarHalfC3²
− (25/594)cbarHalfLb1² ≤ 1/2` (the left hand side is `0.4975090746…`). -/
theorem cbarHalf_cert :
    cbarHalfC1*cbarHalfC2 - cbarHalfR4 + (17/54)*cbarHalfC3^2 - (25/594)*cbarHalfLb1^2
      ≤ (1/2 : ℝ) := by
  norm_num [cbarHalfC1, cbarHalfC2, cbarHalfC3, cbarHalfLb1, cbarHalfLb2, cbarHalfR4,
    Finset.sum_range_succ]

end Work.NumberTheory.Chen.BTermCount
