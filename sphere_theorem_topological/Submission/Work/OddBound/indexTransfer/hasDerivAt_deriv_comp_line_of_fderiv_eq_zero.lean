import Mathlib
import Submission.Work.OddBound.indexTransfer.Infra

open scoped ContDiff Topology
open Filter

namespace Work.OddBound.indexTransfer

/-- Second derivative along a line, at a critical point.

Let `F : H → ℝ` be `C²` at `x₀` with vanishing derivative `fderiv ℝ F x₀ = 0`, let
`φ : ℝ × ℝ → H` be `C²` at `0` with `φ 0 = x₀`, and let `X : ℝ × ℝ`.  Then the function
`σ ↦ F (φ (σ • X))` has, along the line `σ ↦ σ • X` through the critical point, second
derivative `D²F(x₀)(Dφ(0) X, Dφ(0) X)` at `σ = 0`:

`HasDerivAt (deriv (fun σ ↦ F (φ (σ • X)))) (D²F(x₀) (Dφ(0) X) (Dφ(0) X)) 0`.

The hypothesis `fderiv ℝ F x₀ = 0` kills the term `D F(x₀)(D²φ(0)(X,X))` coming from the
chain rule, so only the Hessian term survives. -/
theorem hasDerivAt_deriv_comp_line_of_fderiv_eq_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → ℝ} {x₀ : H} {φ : ℝ × ℝ → H} {X : ℝ × ℝ}
    (hF : ContDiffAt ℝ 2 F x₀) (hφ : ContDiffAt ℝ 2 φ 0) (hx : φ 0 = x₀)
    (hD : fderiv ℝ F x₀ = 0) :
    HasDerivAt (deriv (fun σ : ℝ => F (φ (σ • X))))
      ((fderiv ℝ (fderiv ℝ F) x₀) ((fderiv ℝ φ 0) X) ((fderiv ℝ φ 0) X)) 0 := by
  -- Abbreviations: the point `u = Dφ(0) X`, the CLM-valued map `c`, the vector-valued map `z`
  -- and the linear parametrisation `L` of the line `t ↦ t • X`.
  set u : H := (fderiv ℝ φ 0) X with hu_def
  set c : ℝ → (H →L[ℝ] ℝ) := fun σ => fderiv ℝ F (φ (σ • X)) with hc_def
  set z : ℝ → H := fun σ => (fderiv ℝ φ (σ • X)) X with hz_def
  set L : ℝ →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight X with hL_def
  have hLapp : ∀ t : ℝ, L t = t • X := fun t => by
    rw [hL_def, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  have hL_cont : Continuous (fun t : ℝ => t • X) := by
    rw [show (fun t : ℝ => t • X) = ⇑L from (funext hLapp).symm]
    exact L.continuous
  have hψ : ∀ σ : ℝ, HasFDerivAt (fun t : ℝ => t • X) L σ := fun σ => by
    rw [hL_def]
    exact (hasFDerivAt_id σ).smul_const X
  have hline : Tendsto (fun t : ℝ => t • X) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ × ℝ)) := by
    simpa using hL_cont.tendsto (0 : ℝ)
  -- `φ` (resp. `F`) is differentiable on a neighbourhood of `0` (resp. `x₀`).
  have hφ_near : ∀ᶠ y in 𝓝 (0 : ℝ × ℝ), DifferentiableAt ℝ φ y := by
    obtain ⟨v, hv, hφv⟩ := hφ.contDiffOn (m := 1) (by norm_num) (by intro h; simp at h)
    obtain ⟨w, hwv, hwopen, hxw⟩ := mem_nhds_iff.mp hv
    filter_upwards [hwopen.mem_nhds hxw] with y hy
    exact ((hφv.mono hwv).differentiableOn (by norm_num)).differentiableAt (hwopen.mem_nhds hy)
  have hF_near : ∀ᶠ y in 𝓝 x₀, DifferentiableAt ℝ F y := by
    obtain ⟨v, hv, hFv⟩ := hF.contDiffOn (m := 1) (by norm_num) (by intro h; simp at h)
    obtain ⟨w, hwv, hwopen, hxw⟩ := mem_nhds_iff.mp hv
    filter_upwards [hwopen.mem_nhds hxw] with y hy
    exact ((hFv.mono hwv).differentiableOn (by norm_num)).differentiableAt (hwopen.mem_nhds hy)
  have hΦ_cont : Tendsto (fun σ : ℝ => φ (σ • X)) (𝓝 0) (𝓝 x₀) := by
    have h1 : Tendsto (fun σ : ℝ => φ (σ • X)) (𝓝 (0 : ℝ)) (𝓝 (φ 0)) :=
      Filter.Tendsto.comp hφ.continuousAt hline
    simpa [hx] using h1
  have hΦ_near : ∀ᶠ σ : ℝ in 𝓝 0, DifferentiableAt ℝ φ (σ • X) :=
    hline.eventually hφ_near
  have hF_along : ∀ᶠ σ : ℝ in 𝓝 0, DifferentiableAt ℝ F (φ (σ • X)) :=
    hΦ_cont.eventually hF_near
  -- First order chain rules at the base points.
  have hφ1 : HasFDerivAt φ (fderiv ℝ φ 0) 0 := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hΦ0 : HasFDerivAt (fun σ : ℝ => φ (σ • X)) ((fderiv ℝ φ 0).comp L) 0 := by
    have h := HasFDerivAt.comp (x := (0 : ℝ)) (f := fun σ : ℝ => σ • X) (g := φ)
      (by simpa using hφ1) (hψ 0)
    simpa [Function.comp_def] using h
  have hDF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x₀) x₀ :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc_deriv : HasFDerivAt c ((fderiv ℝ (fderiv ℝ F) x₀).comp ((fderiv ℝ φ 0).comp L)) 0 := by
    have hDF' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x₀)
        ((fun σ : ℝ => φ (σ • X)) 0) := by
      rw [show (fun σ : ℝ => φ (σ • X)) 0 = x₀ from by simp [hx]]
      exact hDF
    have h := HasFDerivAt.comp (x := (0 : ℝ)) (f := fun σ : ℝ => φ (σ • X))
      (g := fderiv ℝ F) hDF' hΦ0
    simpa [hc_def, Function.comp_def] using h
  have hDφ : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) 0) 0 :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hz_deriv : HasFDerivAt z (((fderiv ℝ (fderiv ℝ φ) 0).comp L).flip X) 0 := by
    have hB : HasFDerivAt (fun σ : ℝ => fderiv ℝ φ (σ • X))
        ((fderiv ℝ (fderiv ℝ φ) 0).comp L) 0 := by
      have h := HasFDerivAt.comp (x := (0 : ℝ)) (f := fun σ : ℝ => σ • X) (g := fderiv ℝ φ)
        (by simpa using hDφ) (hψ 0)
      simpa [Function.comp_def] using h
    have h := hB.clm_apply (hasFDerivAt_const X (0 : ℝ))
    simp only [ContinuousLinearMap.comp_zero, zero_add] at h
    simpa [hz_def] using h
  -- The product rule for `σ ↦ c σ (z σ)`; the hypothesis `fderiv ℝ F x₀ = 0` kills the
  -- second summand, and the first one is evaluated at `u = z 0`.
  have hE : HasFDerivAt (fun σ : ℝ => c σ (z σ))
      (((fderiv ℝ (fderiv ℝ F) x₀).comp ((fderiv ℝ φ 0).comp L)).flip u) 0 := by
    have h := hc_deriv.clm_apply hz_deriv
    have hc0 : c 0 = 0 := by simp [hc_def, hx, hD]
    have hz0 : z 0 = u := by simp [hz_def, hu_def]
    simp only [hc0, hz0, ContinuousLinearMap.zero_comp, zero_add] at h
    simpa using h
  have hE' : HasDerivAt (fun σ : ℝ => c σ (z σ)) ((fderiv ℝ (fderiv ℝ F) x₀) u u) 0 := by
    simpa [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, hLapp, hu_def]
      using hE.hasDerivAt
  -- Near `0`, `deriv (fun σ ↦ F (φ (σ • X)))` is given by the first order chain rule.
  have hev : (deriv (fun σ : ℝ => F (φ (σ • X)))) =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => c σ (z σ)) := by
    filter_upwards [hΦ_near, hF_along] with σ hσ hσ'
    have hinner : HasFDerivAt (fun τ : ℝ => φ (τ • X)) ((fderiv ℝ φ (σ • X)).comp L) σ := by
      simpa [Function.comp_def] using HasFDerivAt.comp σ hσ.hasFDerivAt (hψ σ)
    have hout : HasFDerivAt (fun τ : ℝ => F (φ (τ • X)))
        ((fderiv ℝ F (φ (σ • X))).comp ((fderiv ℝ φ (σ • X)).comp L)) σ := by
      simpa [Function.comp_def] using HasFDerivAt.comp σ hσ'.hasFDerivAt hinner
    rw [← fderiv_apply_one_eq_deriv (f := fun τ : ℝ => F (φ (τ • X))) (x := σ), hout.fderiv]
    simp [ContinuousLinearMap.comp_apply, hLapp, hc_def, hz_def]
  exact hE'.congr_of_eventuallyEq hev

end Work.OddBound.indexTransfer
