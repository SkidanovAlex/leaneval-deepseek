import Mathlib
import Submission.Work.Koebe.lintegral_cauchy_ball_lt_top

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Koebe

open MeasureTheory Complex

/-!
# Polar coordinates on a ball in `ℂ`

The main result of this file is the iterated-integral form of the polar-coordinate
formula for the Lebesgue integral over a ball of `ℂ`:

`∫ w in Metric.ball 0 Λ, (ζ - w)⁻¹ = ∫ r in Ioo 0 Λ, ∫ θ in Ioo (-π) π, r * (ζ - r * exp (I θ))⁻¹`.

The proof goes through Mathlib's polar-coordinate change of variables for `ℂ`
(`Complex.integral_comp_polarCoord_symm`) plus Fubini on the product `ℝ × ℝ`
(`MeasureTheory.setIntegral_prod`), for which the local integrability of the
Cauchy kernel `w ↦ (ζ - w)⁻¹` (proved in
`Submission/Work/Koebe/lintegral_cauchy_ball_lt_top.lean`) is needed.
-/

/-- `Complex.polarCoord.symm` in terms of the complex exponential. -/
lemma polar_symm_eq_mul_exp (p : ℝ × ℝ) :
    (Complex.polarCoord.symm p : ℂ) = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_ofReal_mul_I]

/-- **Polar coordinates for `lintegral`s.**  For any nonnegative function `u` on `ℂ`,
its integral over the ball of radius `Λ` equals the integral of `r * u (r e^{iθ})`
over the rectangle `(0, Λ) × (-π, π)`. -/
lemma lintegral_ball_polar (Λ : ℝ) (u : ℂ → ENNReal) :
    ∫⁻ p in (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi),
        ENNReal.ofReal p.1 * u (Complex.polarCoord.symm p)
      = ∫⁻ w in Metric.ball (0:ℂ) Λ, u w := by
  classical
  have hT : MeasurableSet (polarCoord.target : Set (ℝ × ℝ)) :=
    Complex.polarCoord.open_target.measurableSet
  have hS : MeasurableSet (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ⊆ (polarCoord.target : Set (ℝ × ℝ)) := fun p hp => ⟨hp.1.1, hp.2⟩
  have hR : ∫⁻ w in Metric.ball (0:ℂ) Λ, u w
      = ∫⁻ p in (polarCoord.target : Set (ℝ × ℝ)),
          ENNReal.ofReal p.1 * (Metric.ball (0:ℂ) Λ).indicator u
            (Complex.polarCoord.symm p) := by
    rw [← lintegral_indicator measurableSet_ball]
    rw [← Complex.lintegral_comp_polarCoord_symm ((Metric.ball (0:ℂ) Λ).indicator u)]
    rfl
  have hpt : (polarCoord.target : Set (ℝ × ℝ)).indicator
        (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (Metric.ball (0:ℂ) Λ).indicator u
          (Complex.polarCoord.symm p))
      = (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * u (Complex.polarCoord.symm p)) := by
    funext p
    by_cases hp : p ∈ (polarCoord.target : Set (ℝ × ℝ))
    · have hp1 : 0 < p.1 := hp.1
      have hp2 : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
      have hmem : p ∈ (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi) ↔ p.1 < Λ := by
        constructor
        · intro h; exact h.1.2
        · intro h; exact ⟨⟨hp1, h⟩, hp2⟩
      have hnb : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) Λ ↔ p.1 < Λ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm,
          abs_of_pos hp1]
      rw [Set.indicator_of_mem hp]
      by_cases h : p.1 < Λ
      · rw [Set.indicator_of_mem (hnb.mpr h), Set.indicator_of_mem (hmem.mpr h)]
      · rw [Set.indicator_of_notMem (fun hh => h (hnb.mp hh)),
          Set.indicator_of_notMem (fun hh => h (hmem.mp hh)), mul_zero]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h => hp (hsub h))]
  calc ∫⁻ p in (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi),
        ENNReal.ofReal p.1 * u (Complex.polarCoord.symm p)
      = ∫⁻ p, (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * u (Complex.polarCoord.symm p)) p :=
        (lintegral_indicator hS _).symm
    _ = ∫⁻ p, (polarCoord.target : Set (ℝ × ℝ)).indicator
          (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (Metric.ball (0:ℂ) Λ).indicator u
            (Complex.polarCoord.symm p)) p := by rw [hpt]
    _ = ∫⁻ p in (polarCoord.target : Set (ℝ × ℝ)),
          ENNReal.ofReal p.1 * (Metric.ball (0:ℂ) Λ).indicator u
            (Complex.polarCoord.symm p) := lintegral_indicator hT _
    _ = ∫⁻ w in Metric.ball (0:ℂ) Λ, u w := hR.symm

/-- **Polar coordinates for the Bochner integral over a ball.**  No integrability
assumption is needed: this is the change-of-variables formula of
`Complex.integral_comp_polarCoord_symm` combined with the observation that, on
`(0, ∞) × (-π, π)`, membership of `r e^{iθ}` in the ball of radius `Λ` is
equivalent to `r < Λ`. -/
lemma setIntegral_ball_polar (Λ : ℝ) (f : ℂ → ℂ) :
    ∫ w in Metric.ball (0:ℂ) Λ, f w
      = ∫ p in (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi),
          p.1 • f (Complex.polarCoord.symm p) := by
  classical
  have hT : MeasurableSet (polarCoord.target : Set (ℝ × ℝ)) :=
    Complex.polarCoord.open_target.measurableSet
  have hS : MeasurableSet (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ⊆ (polarCoord.target : Set (ℝ × ℝ)) := fun p hp => ⟨hp.1.1, hp.2⟩
  have hpt : (polarCoord.target : Set (ℝ × ℝ)).indicator
        (fun p : ℝ × ℝ => p.1 • (Metric.ball (0:ℂ) Λ).indicator f
          (Complex.polarCoord.symm p))
      = (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p)) := by
    funext p
    by_cases hp : p ∈ (polarCoord.target : Set (ℝ × ℝ))
    · have hp1 : 0 < p.1 := hp.1
      have hp2 : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
      have hmem : p ∈ (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi) ↔ p.1 < Λ := by
        constructor
        · intro h; exact h.1.2
        · intro h; exact ⟨⟨hp1, h⟩, hp2⟩
      have hnb : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) Λ ↔ p.1 < Λ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm,
          abs_of_pos hp1]
      rw [Set.indicator_of_mem hp]
      by_cases h : p.1 < Λ
      · rw [Set.indicator_of_mem (hnb.mpr h), Set.indicator_of_mem (hmem.mpr h)]
      · rw [Set.indicator_of_notMem (fun hh => h (hnb.mp hh)),
          Set.indicator_of_notMem (fun hh => h (hmem.mp hh)), smul_zero]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h => hp (hsub h))]
  rw [← integral_indicator measurableSet_ball]
  rw [← Complex.integral_comp_polarCoord_symm ((Metric.ball (0:ℂ) Λ).indicator f)]
  rw [← integral_indicator hT
    (f := fun p : ℝ × ℝ => p.1 • (Metric.ball (0:ℂ) Λ).indicator f
      (Complex.polarCoord.symm p))]
  rw [hpt]
  rw [integral_indicator hS
    (f := fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))]

/-- The polar-coordinate integrand of the Cauchy kernel is integrable on the rectangle. -/
lemma integrableOn_polar_cauchy (Λ : ℝ) (ζ : ℂ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (ζ - (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))⁻¹)
      (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  classical
  have hS : MeasurableSet (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  refine ⟨?_, ?_⟩
  · measurability
  · rw [hasFiniteIntegral_iff_norm]
    have h1 : ∫⁻ p in (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi),
          ENNReal.ofReal ‖(p.1 : ℂ) * (ζ - (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))⁻¹‖
        = ∫⁻ p in (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi),
          ENNReal.ofReal p.1 * ENNReal.ofReal ‖(ζ - Complex.polarCoord.symm p)⁻¹‖ := by
      refine setLIntegral_congr_fun hS fun p hp => ?_
      have hp1 : 0 < p.1 := hp.1.1
      have hsm : (p.1 : ℂ) * (ζ - (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))⁻¹
          = p.1 • (ζ - Complex.polarCoord.symm p)⁻¹ := by
        rw [Complex.real_smul, polar_symm_eq_mul_exp]
      rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos hp1,
        ENNReal.ofReal_mul (le_of_lt hp1)]
    rw [h1, lintegral_ball_polar Λ (fun w : ℂ => ENNReal.ofReal ‖(ζ - w)⁻¹‖)]
    exact lintegral_cauchy_ball_lt_top Λ ζ

theorem polar_ball_iterated (Λ : ℝ) (ζ : ℂ) :
    ∫ w in Metric.ball (0:ℂ) Λ, (ζ - w)⁻¹
      = ∫ r in Set.Ioo (0:ℝ) Λ,
          ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            (r : ℂ) * (ζ - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))⁻¹ := by
  have hS : MeasurableSet (Set.Ioo (0:ℝ) Λ ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hFub := setIntegral_prod
    (fun p : ℝ × ℝ =>
      (p.1 : ℂ) * (ζ - (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))⁻¹)
    (s := Set.Ioo (0:ℝ) Λ) (t := Set.Ioo (-Real.pi) Real.pi)
    (integrableOn_polar_cauchy Λ ζ)
  rw [← hFub]
  exact (setIntegral_ball_polar Λ (fun w : ℂ => (ζ - w)⁻¹)).trans
    (setIntegral_congr_fun hS fun p _ => by
      rw [Complex.real_smul, polar_symm_eq_mul_exp]).symm

end Work.Koebe
