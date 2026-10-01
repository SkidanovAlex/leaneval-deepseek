import Mathlib

namespace Work.LinnikAreas.OtherCharRepel

/-- Elementary threshold for the logarithmic quantities appearing in the
"other character" repulsion argument.  For all `q` beyond an absolute constant,
`log q ≥ 12`, `log log q ≥ 2`, the ratio `√(log log q) / log q` lies in `(0,1)`,
and `√(log log q) ≥ 1/100`. -/
theorem logThresholdThirteen : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    (0 : ℝ) < Real.log (q : ℝ) ∧ (12 : ℝ) ≤ Real.log (q : ℝ) ∧
    (2 : ℝ) ≤ Real.log (Real.log (q : ℝ)) ∧
    (0 : ℝ) < Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ∧
    Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) < 1 ∧
    (1 : ℝ)/100 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
  refine ⟨2^18, ?_⟩
  intro q hq
  have hqR : (2:ℝ)^18 ≤ (q:ℝ) := by
    have : ((2:ℕ)^18 : ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    simpa using this
  have h2pos : (0:ℝ) < (2:ℝ)^18 := by positivity
  have hlogq_ge : (12:ℝ) ≤ Real.log (q:ℝ) := by
    have hmono : Real.log ((2:ℝ)^18) ≤ Real.log (q:ℝ) := Real.log_le_log h2pos hqR
    have hp : Real.log ((2:ℝ)^18) = 18 * Real.log 2 := by
      rw [Real.log_pow]; norm_num
    have hge : (12:ℝ) ≤ 18 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
    linarith [hmono, hp]
  have hlogq_pos : (0:ℝ) < Real.log (q:ℝ) := by linarith
  have hlog12 : (2:ℝ) ≤ Real.log 12 := by
    have h1 : Real.log (8:ℝ) ≤ Real.log 12 := Real.log_le_log (by norm_num) (by norm_num)
    have h8 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      have hcast : (8:ℝ) = (2:ℝ)^3 := by norm_num
      rw [hcast, Real.log_pow]; norm_num
    have hge : (2:ℝ) ≤ 3 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
    linarith [h1, h8]
  have hloglogq : (2:ℝ) ≤ Real.log (Real.log (q:ℝ)) := by
    have h : Real.log 12 ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log (by norm_num) hlogq_ge
    linarith
  have hloglogq_pos : (0:ℝ) < Real.log (Real.log (q:ℝ)) := by linarith
  have hsqrt_pos : (0:ℝ) < Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.sqrt_pos.mpr hloglogq_pos
  have hlt : Real.log (Real.log (q:ℝ)) < (Real.log (q:ℝ))^2 := by
    have h1 : Real.log (Real.log (q:ℝ)) ≤ Real.log (q:ℝ) - 1 := Real.log_le_sub_one_of_pos hlogq_pos
    have h2 : Real.log (q:ℝ) - 1 < (Real.log (q:ℝ))^2 := by nlinarith
    linarith
  have hsqrt_lt : Real.sqrt (Real.log (Real.log (q:ℝ))) < Real.log (q:ℝ) := by
    have h2 : Real.sqrt (Real.log (Real.log (q:ℝ))) < Real.sqrt ((Real.log (q:ℝ))^2) :=
      Real.sqrt_lt_sqrt (le_of_lt hloglogq_pos) hlt
    rwa [Real.sqrt_sq (le_of_lt hlogq_pos)] at h2
  have hsqrt_ge : (1:ℝ)/100 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.sqrt_le_sqrt hloglogq
    have h3 : (1:ℝ)/100 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith
  refine ⟨hlogq_pos, hlogq_ge, hloglogq, ?_, ?_, hsqrt_ge⟩
  · exact div_pos hsqrt_pos hlogq_pos
  · rw [div_lt_one hlogq_pos]; exact hsqrt_lt

end Work.LinnikAreas.OtherCharRepel
