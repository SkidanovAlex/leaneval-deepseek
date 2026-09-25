import Mathlib
import Submission.Work.RHContract.A.regionII.abnum
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range

/-!
# Region II: `log n ≤ logU n` on `173 ≤ n ≤ 501`

`logU n` is the upper bound for `log n` used in `abAbd`; it is the tangent line to `log`
at `274` (for `n ≤ 368`) or at `512` (for `n ≥ 369`), with the value `log 274`
(resp. `log 512`) replaced by the certified rational upper bracket `lg274u` (resp.
`lg512u`).  Since the tangent at a point of a concave function lies above the graph, the
comparison reduces to the two certified numeric bounds `log 274 ≤ lg274u`,
`log 512 ≤ lg512u`, both obtained from `ThetaBracket.log_le_utOf`.
-/

set_option maxHeartbeats 0

namespace Work.RHContract.A.regionII

open Commons.NumberTheory.Chebyshev.ThetaBracket
open Work.RHContract.A.RegionII

noncomputable section

/-- `utOf 274 = 5613282966`. -/
private lemma utOf_274 : utOf 274 = 5613282966 := by decide

/-- `utOf 512 = 6238440000`. -/
private lemma utOf_512 : utOf 512 = 6238440000 := by decide

/-- `log 274 ≤ lg274u = 5613282966/10^9`. -/
private lemma log274_le_lg274u : Real.log 274 ≤ lg274u := by
  have h := log_le_utOf 274 (by norm_num)
  rw [utOf_274] at h
  have h' : (10 : ℝ) ^ 9 * Real.log (274 : ℝ) ≤ (5613282966 : ℝ) := by simpa using h
  unfold lg274u
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 9), mul_comm]
  linarith

/-- `log 512 ≤ lg512u = 6238440000/10^9`. -/
private lemma log512_le_lg512u : Real.log 512 ≤ lg512u := by
  have h := log_le_utOf 512 (by norm_num)
  rw [utOf_512] at h
  have h' : (10 : ℝ) ^ 9 * Real.log (512 : ℝ) ≤ (6238440000 : ℝ) := by simpa using h
  unfold lg512u
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 9), mul_comm]
  linarith

/-- The tangent line to `log` at a positive point lies above the graph. -/
private lemma log_le_tangent (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    Real.log x ≤ Real.log a + (x - a) / a := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ha)] at h
  have hsub : x / a - 1 = (x - a) / a := by
    field_simp
  linarith

theorem log_le_logU (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 501) :
    Real.log (n : ℝ) ≤ Work.RHContract.A.RegionII.logU n := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  rw [logU]
  split_ifs with hn
  · have h := log_le_tangent 274 (n : ℝ) (by norm_num) hnpos
    linarith [h, log274_le_lg274u]
  · have h := log_le_tangent 512 (n : ℝ) (by norm_num) hnpos
    linarith [h, log512_le_lg512u]

end

end Work.RHContract.A.regionII
