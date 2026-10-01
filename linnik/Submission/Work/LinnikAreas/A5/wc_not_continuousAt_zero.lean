import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.Basic

namespace Work.LinnikAreas.A5

open Complex DirichletCharacter Metric Filter
open scoped Interval Topology BigOperators

/-- The normalised test function `wc K lam` is not continuous at `0` for `K > 0`, `lam > 0`:
it equals `1` at `0` but vanishes on the whole left half-line, so the left limit is `0`. -/
theorem wc_not_continuousAt_zero (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    ¬ ContinuousAt (Work.LinnikAreas.A5.wc K lam) 0 := by
  intro h
  -- value at the origin
  have h1 : wc K lam 0 = 1 := by
    rw [wc_of_nonneg (le_refl (0:ℝ)), f1_zero hK.le]
    have hne : Real.sinh (K * lam) ≠ 0 := by
      apply Real.sinh_ne_zero.mpr; positivity
    field_simp
  -- a sequence approaching `0` from the left
  have hseq : Tendsto (fun n : ℕ => -(1/(n+1:ℝ))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    simpa using this
  have htend : Tendsto (wc K lam) (𝓝 0) (𝓝 (wc K lam 0)) := h
  have hcomp : Tendsto (fun n : ℕ => wc K lam (-(1/(n+1:ℝ)))) atTop (𝓝 (wc K lam 0)) := by
    simpa only [Function.comp_def] using htend.comp hseq
  -- on this sequence `wc` is identically zero
  have hconst : (fun n : ℕ => wc K lam (-(1/(n+1:ℝ)))) = (fun _ => (0:ℝ)) := by
    funext n
    rw [wc_of_neg]
    have : (0:ℝ) < 1/(n+1:ℝ) := by positivity
    linarith
  rw [hconst, h1] at hcomp
  have hb : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h2 : (1:ℝ) = 0 := tendsto_nhds_unique hcomp hb
  norm_num at h2

end Work.LinnikAreas.A5
