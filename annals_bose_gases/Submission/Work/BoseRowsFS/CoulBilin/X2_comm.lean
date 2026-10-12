import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseRowsFS.CoulBilin

/-- **Symmetry of the Coulomb double `∫⁻` in its two slots.**

For measurable `f g : ℝ³ → ℝ`, with `X2 u v := ∫⁻ x, ∫⁻ y, ofReal (u x * v y / ‖x−y‖)`,

  `X2 f g = X2 g f`.

No positivity is needed (`∫⁻` is a nonnegative integral): the two variables are exchanged under
the product-measure-preserving swap `(x,y) ↦ (y,x)` (or, in the iterated form, by Tonelli's
`lintegral_lintegral_swap`), and `‖y−x‖ = ‖x−y‖`, `f y * g x = g x * f y`. -/
theorem X2_comm {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f) (hg : MeasureTheory.AEStronglyMeasurable g) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * g y / ‖x - y‖))
      = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x * f y / ‖x - y‖)) := by
  -- Joint a.e.-measurability of the integrand, needed for Tonelli's swap.
  have hf1 : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f z.1)
      (volume.prod volume) :=
    (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).aemeasurable
  have hg1 : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => g z.2)
      (volume.prod volume) :=
    (hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).aemeasurable
  have hmul : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      f z.1 * g z.2) (volume.prod volume) := hf1.mul hg1
  have hnorm : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ‖z.1 - z.2‖) (volume.prod volume) :=
    (continuous_fst.sub continuous_snd).norm.aemeasurable
  have hdiv : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      f z.1 * g z.2 / ‖z.1 - z.2‖) (volume.prod volume) := hmul.div hnorm
  have hmeas : AEMeasurable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (f x * g y / ‖x - y‖)) (volume.prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hdiv
  -- Exchange the two integrations, then the two sides differ only by the renaming `x ↔ y`.
  rw [lintegral_lintegral_swap hmeas]
  apply lintegral_congr; intro y
  apply lintegral_congr; intro x
  rw [mul_comm (f x) (g y), norm_sub_rev]

end Work.BoseRowsFS.CoulBilin
