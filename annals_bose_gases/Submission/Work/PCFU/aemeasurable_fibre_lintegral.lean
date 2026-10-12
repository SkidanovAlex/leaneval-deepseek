import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.dictBricks
import Submission.Work.BoseFixB1S.PiLintegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A.e. measurability of the squared fibre `lintegral`

For a configuration space `X n = (ℝ³)ⁿ`, a measurable slot `j : Fin n` and an a.e. measurable
potential `V : X n → ℝ`, the map

  `x ↦ ∫⁻ u, ENNReal.ofReal ((V (Function.update x j u)) ^ 2)`

is a.e. measurable for the volume on `X n`.

The proof is a single Fubini/Tonelli step, reusing the product-measure peel of
`Work.BoseFixB1S.PiLintegral`: `volume` on `X n = Fin n → ℝ³` is the product measure
`Measure.pi (fun _ ↦ volume)` (`MeasureTheory.volume_pi`, definitionally), and the map
`(z, r) ↦ Function.update r j z` is a *measure-preserving bijection*
`ℝ³ × (Fin k → ℝ³) ≃ (Fin (k+1) → ℝ³)` (`MeasurableEquiv.piFinSuccAbove`).  Hence
`y ↦ ENNReal.ofReal ((V y) ^ 2)` is a.e. measurable on the product, and integrating it in the
peeled coordinate returns an a.e. measurable function (Tonelli,
`AEMeasurable.lintegral_prod_left'`).
-/

namespace Work.PCFU

open MeasureTheory
open scoped ENNReal

/-- **A.e. measurability of the squared fibre `lintegral`.** -/
theorem aemeasurable_fibre_lintegral {n : ℕ} (j : Fin n) {V : Submission.BoseGases.X n → ℝ}
    (hV : AEMeasurable V (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :
    AEMeasurable (fun x : Submission.BoseGases.X n =>
        ∫⁻ u : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal ((V (Function.update x j u)) ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
  cases n with
  | zero => exact j.elim0
  | succ k =>
    have hφ : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ 2)) := by fun_prop
    have hF : AEMeasurable (fun y : Submission.BoseGases.X (k + 1) =>
        ENNReal.ofReal ((V y) ^ 2))
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (k + 1))) :=
      hφ.comp_aemeasurable' hV
    exact Work.BoseFixB1S.aemeasurable_pi_slice_lintegral
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) j hF

end Work.PCFU
