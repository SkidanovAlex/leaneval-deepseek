import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder

open scoped Topology

namespace Commons.Analysis.Calculus

/-- Auxiliary general second-order chain rule for a curve `h : ℝ → E`, evaluated at `0`.
For `f` of class `C²` and `h` twice differentiable at `0` with `h 0 = x`,
`h'(0) = h'` and `h''(0) = h''`,
```
(f ∘ h)''(0) = D²f(x)[h', h'] + Df(x)·h''.
```
-/
lemma iteratedDeriv_two_comp_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (h : ℝ → E) (x h' h'' : E) (hx : h 0 = x)
    (h1 : HasDerivAt h h' 0) (h2 : HasDerivAt (deriv h) h'' 0)
    (hdiff : ∀ᶠ θ in 𝓝 (0 : ℝ), DifferentiableAt ℝ h θ) :
    iteratedDeriv 2 (fun θ : ℝ => f (h θ)) 0
      = (fderiv ℝ (fderiv ℝ f) x h') h' + (fderiv ℝ f x) h'' := by
  subst hx
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (h 0) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hd0 : DifferentiableAt ℝ h 0 := h1.differentiableAt
  have hev : deriv (fun θ : ℝ => f (h θ)) =ᶠ[𝓝 (0 : ℝ)]
      fun θ => (fderiv ℝ f (h θ)) (deriv h θ) := by
    filter_upwards [hdiff] with θ hθ
    exact fderiv_comp_deriv θ (l := f) (hf_diff.differentiableAt) hθ
  have hc_diff : DifferentiableAt ℝ (fun θ : ℝ => fderiv ℝ f (h θ)) 0 :=
    DifferentiableAt.fun_comp' 0 (g := fderiv ℝ f) (f := h) hfd hd0
  have hu_diff : DifferentiableAt ℝ (deriv h) 0 := h2.differentiableAt
  have hstep : deriv (fun θ : ℝ => (fderiv ℝ f (h θ)) (deriv h θ)) 0
      = deriv (fun θ : ℝ => fderiv ℝ f (h θ)) 0 (deriv h 0)
        + (fderiv ℝ f (h 0)) (deriv (deriv h) 0) :=
    deriv_clm_apply hc_diff hu_diff
  have hderiv_c : deriv (fun θ : ℝ => fderiv ℝ f (h θ)) 0
      = (fderiv ℝ (fderiv ℝ f) (h 0)) (deriv h 0) := by
    have hc := fderiv_comp_deriv 0 (l := fderiv ℝ f) (f := h) hfd hd0
    simpa [Function.comp_def] using hc
  have hmain : deriv (fun θ : ℝ => (fderiv ℝ f (h θ)) (deriv h θ)) 0
      = (fderiv ℝ (fderiv ℝ f) (h 0) h') h' + (fderiv ℝ f (h 0)) h'' := by
    rw [hstep, hderiv_c, h1.deriv, h2.deriv]
  calc iteratedDeriv 2 (fun θ : ℝ => f (h θ)) 0
      = deriv (deriv (fun θ : ℝ => f (h θ))) 0 := by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    _ = deriv (fun θ : ℝ => (fderiv ℝ f (h θ)) (deriv h θ)) 0 := hev.deriv_eq
    _ = (fderiv ℝ (fderiv ℝ f) (h 0) h') h' + (fderiv ℝ f (h 0)) h'' := hmain

section TrigCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative at `0` of the parametrised curve `θ ↦ t • (cos θ • y + sin θ • v)`. -/
lemma hasDerivAt_trigCurve (t : ℝ) (y v : E) :
    HasDerivAt (fun θ : ℝ => t • (Real.cos θ • y + Real.sin θ • v)) (t • v) 0 := by
  have hc : HasDerivAt (fun θ : ℝ => Real.cos θ • y) ((-Real.sin 0) • y) 0 :=
    (Real.hasDerivAt_cos 0).smul_const y
  have hs : HasDerivAt (fun θ : ℝ => Real.sin θ • v) ((Real.cos 0) • v) 0 :=
    (Real.hasDerivAt_sin 0).smul_const v
  have h := (hc.add hs).const_smul t
  have hgoal : t • v = t • ((-Real.sin 0) • y + (Real.cos 0) • v) := by
    simp [Real.cos_zero, Real.sin_zero]
  rw [hgoal]
  exact h

/-- The derivative of the parametrised curve `θ ↦ t • (cos θ • y + sin θ • v)`. -/
lemma deriv_trigCurve (t : ℝ) (y v : E) :
    deriv (fun θ : ℝ => t • (Real.cos θ • y + Real.sin θ • v))
      = fun θ => t • ((-Real.sin θ) • y + Real.cos θ • v) := by
  funext θ
  have hc : HasDerivAt (fun θ : ℝ => Real.cos θ • y) ((-Real.sin θ) • y) θ :=
    (Real.hasDerivAt_cos θ).smul_const y
  have hs : HasDerivAt (fun θ : ℝ => Real.sin θ • v) ((Real.cos θ) • v) θ :=
    (Real.hasDerivAt_sin θ).smul_const v
  exact ((hc.add hs).const_smul t).deriv

/-- The second derivative at `0` of the parametrised curve, namely `t • (-y)`. -/
lemma hasDerivAt_deriv_trigCurve (t : ℝ) (y v : E) :
    HasDerivAt (deriv (fun θ : ℝ => t • (Real.cos θ • y + Real.sin θ • v))) (t • (-y)) 0 := by
  rw [deriv_trigCurve]
  have hc : HasDerivAt (fun θ : ℝ => (-Real.sin θ) • y) ((-Real.cos 0) • y) 0 :=
    ((Real.hasDerivAt_sin 0).neg).smul_const y
  have hs : HasDerivAt (fun θ : ℝ => (Real.cos θ) • v) ((-Real.sin 0) • v) 0 :=
    (Real.hasDerivAt_cos 0).smul_const v
  have h := (hc.add hs).const_smul t
  have hgoal : t • (-y) = t • ((-Real.cos 0) • y + (-Real.sin 0) • v) := by
    simp [Real.cos_zero, Real.sin_zero]
  rw [hgoal]
  exact h

/-- The parametrised curve `θ ↦ t • (cos θ • y + sin θ • v)` is differentiable. -/
lemma differentiable_trigCurve (t : ℝ) (y v : E) :
    Differentiable ℝ (fun θ : ℝ => t • (Real.cos θ • y + Real.sin θ • v)) := by
  fun_prop

end TrigCurve

/-- The second derivative as a bilinear form, on the diagonal, of a scaled vector. -/
lemma clm_smul_smul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] (E →L[ℝ] ℝ)) (t : ℝ) (v : E) :
    (L (t • v)) (t • v) = t ^ 2 * (L v v) := by
  rw [map_smul L t v]
  rw [smul_apply]
  rw [map_smul (L v) t v]
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- A continuous linear functional evaluated on `t • (-y)`. -/
lemma clm_smul_neg_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : E →L[ℝ] ℝ) (t : ℝ) (y : E) :
    M (t • (-y)) = -t * M y := by
  rw [map_smul, map_neg, smul_eq_mul]
  ring

theorem iteratedDeriv_two_comp_curve {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ContDiff ℝ 2 f) (t : ℝ) (y v : EuclideanSpace ℝ (Fin d)) :
    iteratedDeriv 2 (fun θ : ℝ => f (t • (Real.cos θ • y + Real.sin θ • v))) 0
      = t ^ 2 * ((iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v))
        - t * (fderiv ℝ f (t • y)) y := by
  have hd : ∀ᶠ θ in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (fun θ : ℝ => t • (Real.cos θ • y + Real.sin θ • v)) θ :=
    Filter.Eventually.of_forall fun θ => (differentiable_trigCurve t y v).differentiableAt
  have hx : (fun θ : ℝ => t • (Real.cos θ • y + Real.sin θ • v)) 0 = t • y := by
    simp [Real.cos_zero, Real.sin_zero]
  have aux := iteratedDeriv_two_comp_aux f hf
    (fun θ : ℝ => t • (Real.cos θ • y + Real.sin θ • v)) (t • y) (t • v) (t • (-y)) hx
    (hasDerivAt_trigCurve t y v) (hasDerivAt_deriv_trigCurve t y v) hd
  rw [aux, iteratedFDeriv_two_apply, clm_smul_smul_apply, clm_smul_neg_apply]
  ring

end Commons.Analysis.Calculus