/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. strong measurability of the `ε`-slice of the `ℋ¹`-energy `√D`

For `f` smooth on the *open* quadrant (`Work.FTS.EllipticEst.SmoothOpen f`), `z > 0` and
`ε > 0`, the function

  `q ↦ √ (∫_{Iθ} sin(2σ)^{2-γ} · (∂_θ f (z e^{-ε q}) σ)²)`

(which is the profile `√D` of the `ε`-scheme evaluated along the logarithmic dilation
`q ↦ z e^{-ε q}` of the fake time) is a.e. strongly measurable for Lebesgue measure on `ℝ`.

Route.  `Iθ = [0, π/2]` differs from the open interval `(0, π/2)` by the two null endpoints
(`Measure.restrict_congr_set` + `MeasureTheory.Ioo_ae_eq_Icc`), so it suffices to integrate over
`(0, π/2)`.  There the *uncurried* integrand
`p ↦ sin(2 p.2)^{2-γ} · (∂_θ f (z e^{-ε p.1}) p.2)²` is continuous on the open set
`ℝ × (0, π/2)`: the shift `p ↦ (z e^{-ε p.1}, p.2)` maps that set into the open quadrant `Q0`
(where `∂_θ f` is continuous by `SmoothOpen.pth`) and `sin(2 p.2) > 0` there.  Hence the
integrand is a.e. strongly measurable for the product of Lebesgue measure with the restricted
measure, and Mathlib's Fubini measurability
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` makes the `σ`-integral a.e. strongly
measurable as a function of `q`.  Composing with the continuous `Real.sqrt` finishes.

Note that the hypotheses `hα` and `hε` are *not* used: the statement holds for every `α`, `ε`,
being a purely regularity assertion (the *size* statements about `√D` are the ones that need
`α ∈ (0,1]` and `ε > 0`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

set_option linter.unusedVariables false

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem SqrtDMeas {α z ε : ℝ} (hα : α ∈ Set.Ioc 0 1) (hz : 0 < z) (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun q : ℝ => Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f (z * Real.exp (-(ε * q))) σ) ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  -- `Iθ = [0, π/2]` and the open interval `(0, π/2)` carry the same restricted measure.
  have hIθ : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  -- The uncurried integrand is continuous on `ℝ × (0, π/2)`.
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
      * (Work.Spaces.pth f (z * Real.exp (-(ε * p.1))) p.2) ^ 2)
      (Set.univ ×ˢ Set.Ioo 0 (π / 2)) := by
    have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
        (Set.univ ×ˢ Set.Ioo 0 (π / 2)) := by
      have h1 : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) := by fun_prop
      refine h1.continuousOn.rpow_const ?_
      intro p hp
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])))
    have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth f (z * Real.exp (-(ε * p.1))) p.2)
        (Set.univ ×ˢ Set.Ioo 0 (π / 2)) := by
      have hφ : Continuous (fun p : ℝ × ℝ => (z * Real.exp (-(ε * p.1)), p.2)) := by fun_prop
      have hmap : Set.MapsTo (fun p : ℝ × ℝ => (z * Real.exp (-(ε * p.1)), p.2))
          (Set.univ ×ˢ Set.Ioo 0 (π / 2)) Work.FTS.EllipticEst.Q0 := by
        intro p hp
        rw [Work.FTS.EllipticEst.mem_Q0]
        exact ⟨mul_pos hz (Real.exp_pos _), hp.2.1, hp.2.2⟩
      have h2 := (hso.pth).continuousOn.comp hφ.continuousOn hmap
      simpa [Function.comp_def, Function.uncurry] using h2
    exact hsin.mul (hpth.pow 2)
  -- `volume ⊗ (volume ↾ (0,π/2))` is the restriction of the planar measure to `ℝ × (0,π/2)`.
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) : MeasureTheory.Measure (ℝ × ℝ))
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (Set.univ ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [← MeasureTheory.Measure.prod_restrict (s := Set.univ) (t := Set.Ioo 0 (π / 2)),
      MeasureTheory.Measure.restrict_univ]
  -- Joint a.e. strong measurability of the integrand.
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f (z * Real.exp (-(ε * p.1))) p.2) ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)))) : MeasureTheory.Measure (ℝ × ℝ)) := by
    have hmeas : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ)) measurableSet_Ioo
    have h := hcont.aestronglyMeasurable
      (μ := MeasureTheory.volume.prod MeasureTheory.volume) hmeas
    rw [← hprod] at h
    exact h
  -- Fubini measurability of the parametrised angular integral.
  have hint : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ => ∫ σ, (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f (z * Real.exp (-(ε * q))) σ) ^ 2
        ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)))) MeasureTheory.volume :=
    hjoint.integral_prod_right'
  -- Compose with the continuous square root and change the measure back to `Iθ`.
  have := Real.continuous_sqrt.comp_aestronglyMeasurable hint
  simpa only [hIθ] using this

end Work.FTS.StrongEps.EpsLocalPStar
