import Mathlib

namespace Commons.Analysis.Calculus

open scoped ContDiff Topology

/-- The directional derivative field `p ↦ fderiv ℝ U p (1,0)` is smooth when
`U` is smooth. -/
lemma contDiff_fderiv_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : ℝ × E → ℝ} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (fun p : ℝ × E => fderiv ℝ U p (1, 0)) := by
  have hfderiv : ContDiff ℝ ∞ (fderiv ℝ U) := by
    exact hU.fderiv_right (by simp)
  exact hfderiv.clm_apply contDiff_const

/-- The parametric derivative is the directional derivative of `U` in the
first coordinate, i.e. `fderiv ℝ U (p.1, p.2) (1, 0)`. -/
lemma deriv_param_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : ℝ × E → ℝ} (hU : ContDiff ℝ ∞ U) (p : ℝ × E) :
    deriv (fun x : ℝ => U (x, p.2)) p.1 = fderiv ℝ U p (1, 0) := by
  have h1 : HasFDerivAt (fun x : ℝ => (x, p.2)) (ContinuousLinearMap.inl ℝ ℝ E) p.1 := by
    simpa [ContinuousLinearMap.inl] using
      (hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1)
  have hU_diff : DifferentiableAt ℝ U p := hU.differentiable (by simp) p
  have hcomp := (hU_diff.hasFDerivAt).comp p.1 h1
  have hderiv := hcomp.hasDerivAt
  have hderiv' : HasDerivAt (fun x : ℝ => U (x, p.2))
      ((fderiv ℝ U p ∘SL ContinuousLinearMap.inl ℝ ℝ E) 1) p.1 := by
    simpa [Function.comp_def] using hderiv
  rw [hderiv'.deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- **Parametric smoothness of iterated derivatives.**

If `U : ℝ × E → ℝ` is smooth, then for each `i` the parametrized `i`-th
derivative

`p ↦ iteratedDeriv i (fun x : ℝ => U (x, p.2)) p.1`

is smooth on `ℝ × E`.  This is the composition lemma needed to turn smoothness
of the Faà-di-Bruno polynomial in the jet variable into smoothness of the
kernel in its slope variable. -/
lemma contDiff_iteratedDeriv_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (i : ℕ) :
    ∀ {U : ℝ × E → ℝ}, ContDiff ℝ ∞ U →
      ContDiff ℝ ∞ (fun p : ℝ × E =>
        iteratedDeriv i (fun x : ℝ => U (x, p.2)) p.1) := by
  induction i with
  | zero =>
      intro U hU
      simp only [iteratedDeriv_zero]
      exact hU.comp (by fun_prop)
  | succ i ih =>
      intro U hU
      let U' : ℝ × E → ℝ := fun p => fderiv ℝ U p (1, 0)
      have hU' : ContDiff ℝ ∞ U' := contDiff_fderiv_param hU
      have hgoal_eq :
          (fun p : ℝ × E => iteratedDeriv (i + 1) (fun x : ℝ => U (x, p.2)) p.1) =
            (fun p : ℝ × E => iteratedDeriv i (fun x : ℝ => U' (x, p.2)) p.1) := by
        funext p
        rw [iteratedDeriv_succ']
        congr 1
        funext x
        exact deriv_param_eq_fderiv hU (x, p.2)
      rw [hgoal_eq]
      exact ih hU'

end Commons.Analysis.Calculus
