import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.lattice_sum_inv_fourth_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- The convolution `w ⋆ w` (in the form used for the far image) has `L¹`-mass at most
`(∫ w)²`; in fact the two are equal since `volume` on `EuclideanSpace ℝ (Fin 3)` is a Haar
measure.  The proof is a Tonelli swap followed by the translation/reflection invariance of
Lebesgue measure. -/
theorem farImage_convolution_lintegral_le {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw0 : 0 ≤ w) (hwm : Measurable w) (hwi : MeasureTheory.Integrable w MeasureTheory.volume) :
    (∫⁻ u, (∫⁻ y, ENNReal.ofReal (w y) * ENNReal.ofReal (w (y - u)) ∂MeasureTheory.volume) ∂MeasureTheory.volume)
      ≤ ENNReal.ofReal (∫ x, w x) * ENNReal.ofReal (∫ x, w x) := by
  have hw0' : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))] w :=
    Filter.Eventually.of_forall hw0
  have hlin : (∫⁻ y, ENNReal.ofReal (w y) ∂MeasureTheory.volume)
      = ENNReal.ofReal (∫ x, w x) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hwi hw0').symm
  have hmeas : Measurable (Function.uncurry (fun u y : EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (w y) * ENNReal.ofReal (w (y - u)))) :=
    (hwm.ennreal_ofReal.comp measurable_snd).mul
      (hwm.ennreal_ofReal.comp (measurable_snd.sub measurable_fst))
  have hinner : ∀ y : EuclideanSpace ℝ (Fin 3),
      (∫⁻ u, ENNReal.ofReal (w y) * ENNReal.ofReal (w (y - u)) ∂MeasureTheory.volume)
        = ENNReal.ofReal (w y) * ENNReal.ofReal (∫ x, w x) := by
    intro y
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [MeasureTheory.lintegral_sub_left_eq_self (fun a : EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (w a)) y, hlin]
  rw [MeasureTheory.lintegral_lintegral_swap
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      (f := fun u y : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal (w y) * ENNReal.ofReal (w (y - u)))
      hmeas.aemeasurable]
  simp only [hinner]
  rw [MeasureTheory.lintegral_mul_const _ hwm.ennreal_ofReal, hlin]

end Work.BoseBoxFock
