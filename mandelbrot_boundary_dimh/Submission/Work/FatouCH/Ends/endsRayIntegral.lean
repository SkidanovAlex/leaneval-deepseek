import Mathlib

namespace Work.FatouCH.Ends

open Set Metric Complex MeasureTheory
open scoped Topology intervalIntegral

/-- Fundamental-theorem-of-calculus bound along a curve of unit speed: the increment of `B` between
two parameters is bounded by the integral of the pointwise bound `ψ` for the derivative of `B` along
the curve.  (`γ t = x + t * I` and `γ t = x - t * I` are the two intended instances.) -/
theorem endsRayIntegral {B : ℂ → ℂ} {γ γ' : ℝ → ℂ} {ψ : ℝ → ℝ} {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hγ : ∀ t : ℝ, T₀ ≤ t → HasDerivAt γ (γ' t) t)
    (hγc : ContinuousOn γ' (Set.Ici T₀))
    (hγ1 : ∀ t : ℝ, T₀ ≤ t → ‖γ' t‖ = 1)
    (hd : ∀ t : ℝ, T₀ ≤ t → DifferentiableAt ℂ B (γ t))
    (hψc : ContinuousOn ψ (Set.Ici T₀))
    (hbd : ∀ t : ℝ, T₀ ≤ t → ‖deriv B (γ t)‖ ≤ ψ t) :
    ∀ T₂ T₁ : ℝ, T₀ ≤ T₁ → T₁ ≤ T₂ →
      ‖B (γ T₂) - B (γ T₁)‖ ≤ ∫ t in T₁..T₂, ψ t := by
  -- We use the "fencing" theorem on `[T₁,T₂]`: `f t = B (γ t) - B (γ T₁)` is fenced by the
  -- primitive `u ↦ ∫ t in T₁..u, ψ t` of `ψ`, whose derivative is `ψ`.
  -- (`hT₀` and the continuity of `γ'` are not needed by this argument.)
  have _ := hT₀
  have _ := hγc
  intro T₂ T₁ hT₁ hT₁₂
  -- `γ` and `B ∘ γ` are continuous on `[T₁,T₂]`.
  have hFcont : ContinuousOn (fun t => B (γ t) - B (γ T₁)) (Icc T₁ T₂) := by
    refine ContinuousOn.sub ?_ continuousOn_const
    intro x hx
    exact (((hd x (hT₁.trans hx.1)).continuousAt).comp
      (hγ x (hT₁.trans hx.1)).continuousAt).continuousWithinAt
  -- the chain rule: the derivative of `t ↦ B (γ t)` is `γ' t * deriv B (γ t)`
  have hf' : ∀ x ∈ Ico T₁ T₂,
      HasDerivWithinAt (fun t => B (γ t) - B (γ T₁)) (γ' x * deriv B (γ x)) (Ici x) x := by
    intro x hx
    have hxT₀ : T₀ ≤ x := hT₁.trans hx.1
    have hraw : HasDerivAt (B ∘ γ) (γ' x • deriv B (γ x)) x :=
      HasDerivAt.scomp x ((hd x hxT₀).hasDerivAt) (hγ x hxT₀)
    have hcomp : HasDerivAt (fun t => B (γ t)) (γ' x * deriv B (γ x)) x := by
      simpa only [Function.comp_def, smul_eq_mul] using hraw
    exact ((hcomp.sub_const (B (γ T₁))).hasDerivWithinAt).mono (subset_univ _)
  -- continuity of the primitive of `ψ` on `[T₁,T₂]`
  have hΨcont : ContinuousOn (fun u => ∫ t in T₁..u, ψ t) (Icc T₁ T₂) := by
    have hInt : IntegrableOn ψ (uIcc T₁ T₂) volume := by
      rw [uIcc_of_le hT₁₂]
      exact (hψc.mono (fun y hy => hT₁.trans hy.1)).integrableOn_compact isCompact_Icc
    have h := intervalIntegral.continuousOn_primitive_interval (f := ψ) (a := T₁) (b := T₂) hInt
    rwa [uIcc_of_le hT₁₂] at h
  -- the primitive of `ψ` has right derivative `ψ x` at every `x ∈ [T₁,T₂)`
  have hΨderiv : ∀ x ∈ Ico T₁ T₂,
      HasDerivWithinAt (fun u => ∫ t in T₁..u, ψ t) (ψ x) (Ici x) x := by
    intro x hx
    have hxT₀ : T₀ ≤ x := hT₁.trans hx.1
    have hcont : ContinuousOn ψ (uIcc T₁ x) := by
      rw [uIcc_of_le hx.1]
      exact hψc.mono (fun y hy => hT₁.trans hy.1)
    have hint : IntervalIntegrable ψ volume T₁ x := ContinuousOn.intervalIntegrable hcont
    have hcw : ContinuousWithinAt ψ (Ioi x) x :=
      (hψc x hxT₀).mono (fun y hy => hxT₀.trans hy.le)
    have hmeas : StronglyMeasurableAtFilter ψ (𝓝[Ioi x] x) volume :=
      (hψc.mono (fun y hy => hxT₀.trans hy.le)).stronglyMeasurableAtFilter_nhdsWithin
        measurableSet_Ioi x
    exact intervalIntegral.integral_hasDerivWithinAt_right (f := ψ) (a := T₁) (b := x)
      (s := Ici x) (t := Ioi x) hint hmeas hcw
  -- the pointwise bound for the derivative along the curve
  have hbound : ∀ x ∈ Ico T₁ T₂, ‖γ' x * deriv B (γ x)‖ ≤ ψ x := by
    intro x hx
    have hxT₀ : T₀ ≤ x := hT₁.trans hx.1
    calc ‖γ' x * deriv B (γ x)‖ = ‖γ' x‖ * ‖deriv B (γ x)‖ := norm_mul _ _
      _ = ‖deriv B (γ x)‖ := by rw [hγ1 x hxT₀, one_mul]
      _ ≤ ψ x := hbd x hxT₀
  have ha : ‖(fun t => B (γ t) - B (γ T₁)) T₁‖ ≤ (fun u => ∫ t in T₁..u, ψ t) T₁ := by simp
  have key : ∀ x ∈ Icc T₁ T₂,
      ‖(fun t => B (γ t) - B (γ T₁)) x‖ ≤ (fun u => ∫ t in T₁..u, ψ t) x :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := T₁) (b := T₂)
      (f := fun t => B (γ t) - B (γ T₁)) (f' := fun x => γ' x * deriv B (γ x))
      (B := fun u => ∫ t in T₁..u, ψ t) (B' := ψ)
      hFcont hf' ha hΨcont hΨderiv hbound
  simpa using key (x := T₂) (show T₂ ∈ Icc T₁ T₂ from ⟨hT₁₂, le_rfl⟩)

end Work.FatouCH.Ends
