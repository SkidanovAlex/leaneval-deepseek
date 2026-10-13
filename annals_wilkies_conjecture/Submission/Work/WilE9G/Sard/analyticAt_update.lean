import Mathlib

namespace Work.WilE9G.Sard

/-- **Analyticity of the "replace one coordinate by a function" map.**  If `h` is analytic at `x₀`
then so is `z ↦ Function.update z i (h z)`. -/
theorem analyticAt_update {n : ℕ} {h : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (i : Fin n) (hh : AnalyticAt ℝ h x₀) :
    AnalyticAt ℝ (fun z => Function.update z i (h z)) x₀ := by
  refine analyticAt_pi_iff.2 fun j => ?_
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    exact hh
  · simp only [Function.update_of_ne hj]
    exact (ContinuousLinearMap.proj (R := ℝ) j).analyticAt x₀

end Work.WilE9G.Sard
