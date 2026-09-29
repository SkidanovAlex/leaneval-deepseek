import Mathlib

namespace Work.TMComp.MAnalytic

open MeasureTheory Set Complex

/-- Continuity in the parameter `η` of the circle integral
`η ↦ ∮ ζ in C(0, r), (ζ ^ (m + 1))⁻¹ • F ζ η`, for `0 < r ≤ r₁` and `F` jointly
continuous on `closedBall 0 r₁ ×ˢ closedBall 0 r₁`.

The parametrised integrand `(θ, η) ↦ deriv (circleMap 0 r) θ • ((circleMap 0 r θ) ^ (m+1))⁻¹ • F (circleMap 0 r θ) η`
is jointly continuous: the circle `circleMap 0 r θ` stays in `closedBall 0 r₁` because
`‖circleMap 0 r θ‖ = |r| = r ≤ r₁`, and the factor `(circleMap 0 r θ) ^ (m+1)` is invertible
because `circleMap 0 r θ ≠ 0` for `r > 0`.  The parametric interval-integral continuity lemma
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` then gives the result
after rewriting the circle integral as an interval integral over `[0, 2π]`. -/
theorem continuousOn_circleIntegral_parameter {r r₁ : ℝ} (hr : 0 < r) (hrr : r ≤ r₁)
    {F : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2)
      (Metric.closedBall 0 r₁ ×ˢ Metric.closedBall 0 r₁))
    (m : ℕ) :
    ContinuousOn (fun η : ℂ => ∮ ζ in C(0, r), (ζ ^ (m + 1))⁻¹ • F ζ η)
      (Metric.closedBall 0 r₁) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : ↥(Metric.closedBall (0 : ℂ) r₁) =>
    ∮ ζ in C(0, r), (ζ ^ (m + 1))⁻¹ • F ζ x.1)
  -- The parametrised integrand, written as an uncurried function on `s × ℝ`.
  let f : ↥(Metric.closedBall (0 : ℂ) r₁) → ℝ → ℂ :=
    fun η θ => deriv (circleMap 0 r) θ • ((circleMap 0 r θ ^ (m + 1))⁻¹ • F (circleMap 0 r θ) η.1)
  -- `circleMap 0 r θ` never vanishes when `r > 0`.
  have hcne : ∀ θ : ℝ, circleMap 0 r θ ≠ 0 := by
    intro θ h
    have h2 := norm_circleMap_zero r θ
    rw [h, norm_zero, abs_of_pos hr] at h2
    exact hr.ne' h2.symm
  -- The circle lies in `closedBall 0 r₁`.
  have hmem : ∀ θ : ℝ, circleMap 0 r θ ∈ Metric.closedBall (0 : ℂ) r₁ := by
    intro θ
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_circleMap_zero,
      abs_of_pos hr]
    exact hrr
  -- Joint continuity of `(θ, η) ↦ F (circleMap 0 r θ) η` on `s × ℝ`.
  have hFc : Continuous (fun p : ↥(Metric.closedBall (0 : ℂ) r₁) × ℝ =>
      F (circleMap 0 r p.2) p.1.1) := by
    have hg : Continuous (fun p : ↥(Metric.closedBall (0 : ℂ) r₁) × ℝ =>
        ((circleMap 0 r p.2, p.1.1) : ℂ × ℂ)) :=
      ((continuous_circleMap 0 r).comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst)
    refine hcont.comp_continuous hg fun p => ?_
    exact ⟨hmem p.2, p.1.2⟩
  have hder : Continuous (fun p : ↥(Metric.closedBall (0 : ℂ) r₁) × ℝ =>
      deriv (circleMap 0 r) p.2) := by
    simp only [deriv_circleMap]
    fun_prop
  have hinv : Continuous (fun p : ↥(Metric.closedBall (0 : ℂ) r₁) × ℝ =>
      (circleMap 0 r p.2 ^ (m + 1))⁻¹) := by
    refine Continuous.inv₀ ?_ fun p => pow_ne_zero _ (hcne p.2)
    fun_prop
  have hf : Continuous (Function.uncurry f) := by
    show Continuous (fun p : ↥(Metric.closedBall (0 : ℂ) r₁) × ℝ =>
      deriv (circleMap 0 r) p.2 • ((circleMap 0 r p.2 ^ (m + 1))⁻¹ • F (circleMap 0 r p.2) p.1.1))
    exact hder.smul (hinv.smul hFc)
  have hmain := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hf 0 (2 * Real.pi)
  convert hmain using 1
  ext x
  rfl

end Work.TMComp.MAnalytic
