import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.annulusCoreSetup
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# The winding number of the unit circle about an interior point

`Work.Smooth.SphereJordan.pcwindNumberCircleCurve`: the topological winding number of the standard
unit circle about any point of the open unit disc is `1`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- The norm of a point of the circle curve is one. -/
theorem pcnorm_circleCurve_apply (θ : ℝ) : ‖pccircleCurve.γ θ‖ = 1 := by
  rw [pccircleCurve_apply, Work.Smooth.Jordan.circlePoint_coe]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- **The winding number of the unit circle about an interior point is `1`.** -/
theorem pcwindNumberCircleCurve (x : ℂ) (hx : ‖x‖ < 1) :
    windNumber pccircleCurve.γ pccircleCurve.cont x = 1 := by
  set c₀ : C(unitInterval, ℂ) := curveLoop pccircleCurve.γ pccircleCurve.cont with hc₀def
  set c₁ : C(unitInterval, ℂ) := curveLoop
    (fun t : ℝ => pccircleCurve.γ t - x) (pccircleCurve.cont.sub continuous_const) with hc₁def
  have hc₀ : ∀ t : unitInterval, c₀ t = pccircleCurve.γ (2 * Real.pi * (t : ℝ)) := fun t => rfl
  have hc₁ : ∀ t : unitInterval, c₁ t = pccircleCurve.γ (2 * Real.pi * (t : ℝ)) - x := fun t => rfl
  have hne₀ : ∀ t : unitInterval, c₀ t ≠ 0 := by
    intro t h
    have h1 : ‖c₀ t‖ = 1 := by rw [hc₀ t, pcnorm_circleCurve_apply]
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hne₁ : ∀ t : unitInterval, c₁ t ≠ 0 := by
    intro t h
    have h1 : ‖pccircleCurve.γ (2 * Real.pi * (t : ℝ))‖ = 1 := pcnorm_circleCurve_apply _
    have h2 : x = pccircleCurve.γ (2 * Real.pi * (t : ℝ)) := (sub_eq_zero.mp h).symm
    rw [h2, h1] at hx
    exact lt_irrefl 1 hx
  have hloop₀ : c₀ 0 = c₀ 1 := by
    rw [hc₀ 0, hc₀ 1]
    rw [show (2 : ℝ) * Real.pi * ((0 : unitInterval) : ℝ) = 0 by simp,
      show (2 : ℝ) * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi by simp]
    exact (show pccircleCurve.γ (2 * Real.pi) = pccircleCurve.γ 0 from by
      simpa using (pccircleCurve.periodic_apply 0)).symm
  set H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => pccircleCurve.γ (2 * Real.pi * ((p.1 : unitInterval) : ℝ))
        - (((p.2 : unitInterval) : ℝ) • x), by
      refine Continuous.sub ?_ ?_
      · exact pccircleCurve.cont.comp
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
      · exact (continuous_subtype_val.comp continuous_snd).smul continuous_const⟩ with hHdef
  have hH : ∀ p : unitInterval × unitInterval, H p =
      pccircleCurve.γ (2 * Real.pi * ((p.1 : unitInterval) : ℝ))
        - (((p.2 : unitInterval) : ℝ) • x) := fun p => rfl
  have hHne : ∀ p : unitInterval × unitInterval, H p ≠ 0 := by
    rintro ⟨t, s⟩ h
    rw [hH] at h
    have h' : (((s : unitInterval) : ℝ) • x)
        = pccircleCurve.γ (2 * Real.pi * ((t : unitInterval) : ℝ)) := (sub_eq_zero.mp h).symm
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have h1 : ‖(((s : unitInterval) : ℝ) • x)‖ = 1 := by
      rw [h', pcnorm_circleCurve_apply]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0] at h1
    have h2 : (s : ℝ) * ‖x‖ ≤ ‖x‖ := by nlinarith [norm_nonneg x, hs1, hs0]
    linarith
  have hH0 : ∀ t : unitInterval, H (t, 0) = c₀ t := by
    intro t
    simp [hH, hc₀ t]
  have hH1 : ∀ t : unitInterval, H (t, 1) = c₁ t := by
    intro t
    simp [hH, hc₁ t]
  have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
    intro s
    rw [hH, hH]
    rw [show (2 : ℝ) * Real.pi * ((0 : unitInterval) : ℝ) = 0 by simp,
      show (2 : ℝ) * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi by simp]
    rw [show pccircleCurve.γ (2 * Real.pi) = pccircleCurve.γ 0 from by
      simpa using (pccircleCurve.periodic_apply 0)]
  have hspec : loopIndex c₀ = 1 := by
    set Λ : C(unitInterval, ℂ) :=
      ⟨fun t : unitInterval => (((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I,
        by fun_prop⟩ with hΛdef
    have hΛ : ∀ t : unitInterval, Complex.exp (Λ t) = c₀ t := by
      intro t
      simp only [hc₀ t, hΛdef, ContinuousMap.coe_mk, pccircleCurve_apply,
        Work.Smooth.Jordan.circlePoint_coe]
    have h := loopIndex_spec c₀ hne₀ hloop₀ Λ hΛ
    have hleft : Λ 1 - Λ 0 = 2 * (Real.pi : ℂ) * Complex.I := by
      have h1 : Λ 1 = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
        rw [hΛdef]; simp
      have h0 : Λ 0 = 0 := by
        rw [hΛdef]; simp
      rw [h1, h0, sub_zero]
      push_cast
      ring
    have h2 : (loopIndex c₀ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = 1 * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [← h, hleft, one_mul]
    have h3 : (loopIndex c₀ : ℂ) = 1 :=
      mul_right_cancel₀ (by
        rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = 2 * ↑Real.pi * Complex.I from by
          push_cast; ring]
        exact two_pi_I_ne_zero) h2
    exact_mod_cast h3
  have hhom := loopIndex_eq_of_homotopy hne₀ hne₁ H hHne hH0 hH1 hHloop
  show loopIndex c₁ = 1
  rw [← hhom]
  exact hspec

end

end Work.Smooth.SphereJordan
