import Mathlib

set_option linter.unusedVariables false

namespace Work.Fatou.Analysis

open MeasureTheory Set Complex
open scoped ENNReal Real

/-- Polar-coordinate formula for the Lebesgue integral over an annulus:
for a measurable `F : ℂ → ℝ≥0∞` and `1 ≤ R`, the integral over the closed annulus
`1 ≤ ‖z‖ ≤ R` equals the iterated integral over `r ∈ [1,R]` and `θ ∈ [-π,π]` of
`r * F (r * exp (θ * I))`.

The map `(r,θ) ↦ r * exp (θ * I)` is the inverse polar coordinate map of
`Complex.polarCoord`, with Jacobian `r`; the boundary identifications (the two
edges `θ = ±π`, and the range endpoints `r = 1`, `r = R`) are null sets, and
Mathlib's `Complex.lintegral_comp_polarCoord_symm` supplies the change of
variables in the convenient "indicator" form. -/
theorem lintegral_annulus_eq_polar (F : ℂ → ENNReal) (hF : Measurable F) (R : ℝ) (hR : 1 ≤ R) :
    ∫⁻ z in Metric.closedBall (0:ℂ) R \ Metric.ball (0:ℂ) 1, F z =
      ∫⁻ r in Set.Icc (1:ℝ) R, ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
        ENNReal.ofReal r * F (r * Complex.exp (θ * Complex.I)) := by
  set A : Set ℂ := Metric.closedBall (0:ℂ) R \ Metric.ball (0:ℂ) 1 with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]; exact Metric.isClosed_closedBall.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hφ : Measurable (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ)) := by
    have h : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ))
        = fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; rw [Complex.polarCoord_symm_apply]
    rw [h]; fun_prop
  have hmeasG : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p)) := by
    fun_prop
  -- the pullback of the annulus under the inverse polar map
  set V : Set (ℝ × ℝ) :=
    Complex.polarCoord.target ∩ (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ)) ⁻¹' A with hV
  have hVmeas : MeasurableSet V := by
    rw [hV]
    exact Complex.polarCoord.open_target.measurableSet.inter (hAmeas.preimage hφ)
  have hTmeas : MeasurableSet Complex.polarCoord.target := Complex.polarCoord.open_target.measurableSet
  -- on the open polar target, `symm p ∈ A` means exactly `1 ≤ p.1 ≤ R`
  have hTU : V = Set.Icc (1:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi := by
    rw [hV]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Complex.polarCoord_target, Set.mem_prod,
      Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc, hA, Set.mem_sdiff, Metric.mem_closedBall,
      Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, not_lt]
    constructor
    · rintro ⟨⟨h0, hθ⟩, hle, hge⟩
      exact ⟨⟨(abs_of_pos h0) ▸ hge, (abs_of_pos h0).symm.trans_le hle⟩, hθ⟩
    · rintro ⟨⟨h1, h2⟩, hθ⟩
      have h0 : (0:ℝ) < p.1 := lt_of_lt_of_le zero_lt_one h1
      exact ⟨⟨h0, hθ⟩, by rwa [abs_of_pos h0], by rwa [abs_of_pos h0]⟩
  -- restrict the polar change of variables to the annulus
  have hmain : ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 * (A.indicator F) (Complex.polarCoord.symm p)
      = ∫⁻ p in V, ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p) := by
    have hpt : EqOn (fun p => ENNReal.ofReal p.1 * (A.indicator F) (Complex.polarCoord.symm p))
        (fun p => V.indicator (fun p => ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p)) p)
        Complex.polarCoord.target := by
      intro p hp
      show ENNReal.ofReal p.1 * (A.indicator F) (Complex.polarCoord.symm p)
        = V.indicator (fun p => ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p)) p
      by_cases h : (Complex.polarCoord.symm p : ℂ) ∈ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by rw [hV]; exact ⟨hp, h⟩)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (by rw [hV]; rintro ⟨-, h'⟩; exact h h'), mul_zero]
    have hTV : Complex.polarCoord.target ∩ V = V := by rw [hV, ← Set.inter_assoc, Set.inter_self]
    rw [setLIntegral_congr_fun hTmeas hpt,
      ← lintegral_indicator hTmeas
        (V.indicator (fun p => ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p))),
      Set.indicator_indicator, hTV,
      lintegral_indicator hVmeas (fun p => ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p))]
  calc ∫⁻ z in Metric.closedBall (0:ℂ) R \ Metric.ball (0:ℂ) 1, F z
      = ∫⁻ z in A, F z := by rw [hA]
    _ = ∫⁻ z, A.indicator F z := (lintegral_indicator hAmeas F).symm
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (A.indicator F) (Complex.polarCoord.symm p) :=
        (Complex.lintegral_comp_polarCoord_symm (A.indicator F)).symm
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 * (A.indicator F) (Complex.polarCoord.symm p) := by
        simp only [smul_eq_mul]
    _ = ∫⁻ p in V, ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p) := hmain
    _ = ∫⁻ p in Set.Icc (1:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p) := by rw [hTU]
    _ = ∫⁻ r in Set.Icc (1:ℝ) R, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r * F (Complex.polarCoord.symm (r, θ)) :=
        setLIntegral_prod _ hmeasG.aemeasurable
    _ = ∫⁻ r in Set.Icc (1:ℝ) R, ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
          ENNReal.ofReal r * F (Complex.polarCoord.symm (r, θ)) := by
        refine setLIntegral_congr_fun measurableSet_Icc (fun r _ => ?_)
        exact setLIntegral_congr
          (f := fun θ => ENNReal.ofReal r * F (Complex.polarCoord.symm (r, θ))) Ioo_ae_eq_Icc
    _ = ∫⁻ r in Set.Icc (1:ℝ) R, ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
          ENNReal.ofReal r * F (r * Complex.exp (θ * Complex.I)) := by
        refine setLIntegral_congr_fun measurableSet_Icc (fun r _ => ?_)
        refine setLIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        rw [Complex.polarCoord_symm_apply, Complex.exp_ofReal_mul_I]

end Work.Fatou.Analysis
