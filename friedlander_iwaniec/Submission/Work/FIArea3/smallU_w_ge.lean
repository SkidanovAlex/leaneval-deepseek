import Mathlib
import Submission.Work.FITop.Defs
import Submission.Work.FIArea3.loglog_x_gt_eighteen

namespace Work.FIArea3

/-- The small-`u` regime forces `log N` to be huge.  From `θ√N ≥ 1/10` and
`θ = (log x)^{-A'}` with `A' ≥ 2^{20}` one gets `log N ≥ 2A'·loglog x - log 100`, and
`loglog x > 18` (`Work.FIArea3.loglog_x_gt_eighteen`, which uses the same hypothesis), whence
`log N > 2·2^{20}·18 - log 100 > 37000000`. -/
theorem smallU_w_ge (Pa : Work.FITop.Params)
    (hu : (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N) :
    (37000000 : ℝ) < Real.log (Pa.N : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlogx_gt1 : (1 : ℝ) < Real.log (Pa.x : ℝ) :=
    lt_of_lt_of_le (by linarith [Real.log_three_gt_d9]) (Real.log_le_log (by norm_num) hx3)
  have hlogxpos : 0 < Real.log (Pa.x : ℝ) := lt_trans one_pos hlogx_gt1
  -- `loglog x > 18` (the sibling lemma, with the same hypothesis)
  have hLLgt : (18 : ℝ) < Real.log (Real.log (Pa.x : ℝ)) :=
    Work.FIArea3.loglog_x_gt_eighteen Pa hu
  have hLLpos : 0 < Real.log (Real.log (Pa.x : ℝ)) := by linarith
  have hA20 : (2 : ℝ) ^ 20 ≤ Pa.A' := by linarith [Pa.hA, Pa.hA']
  have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
  -- `θ√N ≥ 1/10` gives `√N ≥ 1/(10θ)`
  have hdiv : (1 / 10) / Pa.θ ≤ Real.sqrt Pa.N := by
    rw [div_le_iff₀ Pa.hθ0]
    have hcomm : Real.sqrt Pa.N * Pa.θ = Pa.θ * Real.sqrt Pa.N := mul_comm _ _
    linarith [hu]
  -- squaring: `N ≥ 1/(100 θ²)`
  have hsq : ((1 / 10) / Pa.θ) ^ 2 ≤ Pa.N := by
    have h1 : (0 : ℝ) ≤ (1 / 10) / Pa.θ := div_nonneg (by norm_num) Pa.hθ0.le
    have h2 : ((1 / 10) / Pa.θ) ^ 2 ≤ (Real.sqrt Pa.N) ^ 2 := pow_le_pow_left₀ h1 hdiv 2
    rwa [Real.sq_sqrt hNpos.le] at h2
  have hsq' : 1 / (100 * Pa.θ ^ 2) ≤ Pa.N := by
    have heq : ((1 / 10) / Pa.θ) ^ 2 = 1 / (100 * Pa.θ ^ 2) := by
      field_simp
      ring
    rwa [heq] at hsq
  have hpos' : 0 < 1 / (100 * Pa.θ ^ 2) :=
    div_pos one_pos (mul_pos (by norm_num) (pow_pos Pa.hθ0 2))
  have hlogN_ge : Real.log (1 / (100 * Pa.θ ^ 2)) ≤ Real.log Pa.N :=
    Real.log_le_log hpos' hsq'
  -- `log (1/(100θ²)) = 2A'·loglog x - log 100`, using `θ = (log x)^{-A'}`
  have hlogval : Real.log (1 / (100 * Pa.θ ^ 2)) =
      2 * Pa.A' * Real.log (Real.log (Pa.x : ℝ)) - Real.log 100 := by
    rw [one_div, Real.log_inv,
      Real.log_mul (by norm_num) (pow_ne_zero 2 Pa.hθ0.ne'), Real.log_pow]
    rw [Pa.hθ, Real.log_rpow hlogxpos]
    ring
  have hkey : 2 * Pa.A' * Real.log (Real.log (Pa.x : ℝ)) - Real.log 100 ≤ Real.log Pa.N := by
    rw [← hlogval]; exact hlogN_ge
  have hlog100 : Real.log 100 ≤ 99 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100)
    linarith
  have h2 : 2 * (2 : ℝ) ^ 20 * 18 < 2 * Pa.A' * Real.log (Real.log (Pa.x : ℝ)) := by
    nlinarith [hA20, hLLgt, hLLpos]
  have hnum : (37000000 : ℝ) < 2 * (2 : ℝ) ^ 20 * 18 - 99 := by norm_num
  linarith [hkey, h2, hlog100, hnum]

end Work.FIArea3
