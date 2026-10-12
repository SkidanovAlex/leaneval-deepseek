import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Commons.Analysis.Fourier.gauss_sq_integrable_volume
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped Real

namespace Commons.Analysis.Fourier

/-- For `0 < s` and any `x`, the `p`-translated Gaussian kernel is integrable over
`V = EuclideanSpace ℝ (Fin 3)`, and its (Bochner) integral equals `s^(3/2)`:
`Integrable (fun y : V => Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s)) volume` and
`∫ y, Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s) = s ^ (3 / 2 : ℝ)`. -/
theorem gauss_translate_integrable {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
        (fun y : EuclideanSpace ℝ (Fin 3) => Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s)) ∧
      (∫ y : EuclideanSpace ℝ (Fin 3), Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s)) =
        s ^ (3 / 2 : ℝ) := by
  let b : ℝ := Real.pi / s
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos Real.pi_pos hs
  -- The integrand is the translate `y ↦ g (x - y)` of the centred Gaussian `g z = exp(-b‖z‖²)`.
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => Real.exp (-(b * ‖z‖ ^ 2))
  have hrewrite : ∀ y : EuclideanSpace ℝ (Fin 3),
      Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s) = g (x - y) := by
    intro y
    dsimp [g, b]
    congr 1
    ring
  -- The centred Gaussian is integrable and its total mass is `(π / b) ^ (3/2)`.
  have hg : Integrable g ∧ (∫ z : EuclideanSpace ℝ (Fin 3), g z) = (Real.pi / b) ^ (3 / 2 : ℝ) := by
    simpa [g] using (gauss_sq_integrable_volume (b := b) hb)
  constructor
  · -- integrability: translation of an integrable function is integrable (Haar measure).
    have htrans : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => g (x - y)) :=
      MeasureTheory.Integrable.comp_sub_left (μ := volume) hg.1 x
    exact htrans.congr (ae_of_all volume (fun y => (hrewrite y).symm))
  · -- integral: translation-invariance of the volume, then the Gaussian mass formula.
    calc
      (∫ y : EuclideanSpace ℝ (Fin 3), Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s))
          = ∫ y : EuclideanSpace ℝ (Fin 3), g (x - y) := by
            apply integral_congr_ae
            exact ae_of_all volume (fun y => hrewrite y)
      _ = (∫ z : EuclideanSpace ℝ (Fin 3), g z) := by
            have htrans := MeasureTheory.integral_sub_left_eq_self (μ := volume) (f := g) x
            simpa using htrans
      _ = s ^ (3 / 2 : ℝ) := by
            have hdiv : Real.pi / b = s := by
              dsimp [b]
              field_simp [Real.pi_ne_zero, ne_of_gt hs]
            rw [hg.2, hdiv]

end Commons.Analysis.Fourier
