import Mathlib
import Submission.Work.Pert.tools
import Submission.Work.Pert.RBlock3
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.pert2v2

theorem end_const_le_seg {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ef : ℂ → ℂ} {cm cp : ℂ} {y δ : ℝ} (hδ : 0 < δ) (hy : d.η₀ < y)
    (hper : ∀ w : ℂ, y ≤ w.im → Ef (w + 1) = Ef w + 1)
    (hdiff : DifferentiableOn ℂ (fun w => Ef w - w) {w : ℂ | y ≤ w.im})
    (hlim : Filter.Tendsto (fun w : ℂ => Ef w - w)
      (Filter.comap Complex.im Filter.atTop) (nhds (cp - cm)))
    (hseg : ∀ x : ℝ, ‖(Ef ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))
        - (d.E ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))‖ < δ / 2) :
    ‖cm - cp‖ < δ := by
  -- `P` is the `1`-periodic extension of `Ef - id` off the half plane `{y ≤ Im w}`.
  set P : ℂ → ℂ := fun w => if y ≤ w.im then Ef w - w else 0 with hP
  have hPdiff : ∀ M : ℝ, y ≤ M →
      DifferentiableOn ℂ P {w : ℂ | y ≤ w.im ∧ w.im ≤ M} := by
    intro M hM
    have h1 : DifferentiableOn ℂ (fun w : ℂ => Ef w - w)
        {w : ℂ | y ≤ w.im ∧ w.im ≤ M} := hdiff.mono (fun w hw => hw.1)
    exact h1.congr (fun w hw => by simp only [hP]; rw [if_pos hw.1])
  have hPper : ∀ w : ℂ, P (w + 1) = P w := by
    intro w
    have him : (w + 1).im = w.im := by simp
    simp only [hP]
    by_cases h : y ≤ w.im
    · rw [if_pos h, if_pos (by rw [him]; exact h)]
      have h2 := hper w h
      linear_combination h2
    · rw [if_neg h, if_neg (by rw [him]; exact h)]
  have hPlim : Filter.Tendsto P (Filter.comap Complex.im Filter.atTop) (nhds (cp - cm)) := by
    refine Filter.Tendsto.congr' ?_ hlim
    refine Filter.eventually_comap.mpr (Filter.eventually_atTop.mpr ⟨y, fun b hb w hwb => ?_⟩)
    simp only [hP]
    rw [if_pos (by rw [hwb]; exact hb)]
  -- (A.4.4): the mean of `Ef - id` over one period equals its end limit `cp - cm`.
  have hmeanP := Work.Pert.intervalIntegral_period_eq_of_tendsto hPdiff hPper hPlim
  have hmeanEf : ∫ x in (0 : ℝ)..1,
      (Ef ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I)) = cp - cm := by
    rw [← hmeanP]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [hP]
    rw [if_pos (by simp : y ≤ ((x : ℂ) + y * Complex.I).im)]
  -- the datum's mean vanishes (the normalisation (4.1.5))
  have hmeanDE := Work.Pert.ParabData.integral_E_sub_id d hy
  -- integrability of both integrands along the line `{Im = y}`
  have hmapSeg : Set.MapsTo (fun x : ℝ => (x : ℂ) + y * Complex.I) (Set.uIcc 0 1)
      {w : ℂ | y ≤ w.im} := by
    intro x hx
    simp
  have hintEf : IntervalIntegrable
      (fun x : ℝ => Ef ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))
      MeasureTheory.volume 0 1 :=
    (ContinuousOn.comp hdiff.continuousOn (by fun_prop) hmapSeg).intervalIntegrable
  have hintDE : IntervalIntegrable
      (fun x : ℝ => d.E ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))
      MeasureTheory.volume 0 1 :=
    (ContinuousOn.comp
      ((Work.Pert.ParabData.E_facts d hy).1.sub differentiableOn_id).continuousOn
      (by fun_prop) hmapSeg).intervalIntegrable
  -- combine: the mean of `Ef - d.E` is `cp - cm - 0 = cp - cm`
  have hcombine : (∫ x in (0 : ℝ)..1,
        (Ef ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I)))
      - ∫ x in (0 : ℝ)..1,
        (d.E ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))
      = ∫ x in (0 : ℝ)..1,
        (Ef ((x : ℂ) + y * Complex.I) - d.E ((x : ℂ) + y * Complex.I)) := by
    rw [← intervalIntegral.integral_sub hintEf hintDE]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  have hgc : ∫ x in (0 : ℝ)..1,
      (Ef ((x : ℂ) + y * Complex.I) - d.E ((x : ℂ) + y * Complex.I)) = cp - cm := by
    rw [← hcombine, hmeanEf, hmeanDE, sub_zero]
  -- bound the mean by the pointwise bound on the segment
  have hbound : ‖cp - cm‖ ≤ δ / 2 := by
    rw [← hgc]
    have hle : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
        ‖Ef ((x : ℂ) + y * Complex.I) - d.E ((x : ℂ) + y * Complex.I)‖ ≤ δ / 2 := by
      intro x hx
      refine le_of_lt ?_
      have h := hseg x
      rwa [show (Ef ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))
            - (d.E ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))
          = Ef ((x : ℂ) + y * Complex.I) - d.E ((x : ℂ) + y * Complex.I) from by ring] at h
    have := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun x : ℝ =>
      Ef ((x : ℂ) + y * Complex.I) - d.E ((x : ℂ) + y * Complex.I)) (C := δ / 2) hle
    simpa using this
  rw [norm_sub_rev]
  linarith

end Work.Pert.pert2v2
