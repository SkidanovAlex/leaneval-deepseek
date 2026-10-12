import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.slotFibre_pointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.measurable_boxQInd`

Measurability of FS's box mean-free projection `boxQInd volA A i Ψ = 1_A(x_i)·Ψ − P_{B,i}Ψ`
(`Work.UBBInputs8.boxQInd`, FS `eq:HBU`) as a function of the configuration `x`, assuming the
state `Ψ` and the box `A` are measurable.  The only non-trivial ingredient is the Fubini
measurability of the slot integral `x ↦ ∫ z in A, Ψ (update x i z)`, which follows from
joint measurability of `(x, z) ↦ update x i z`.
-/

namespace Work.SlotWord

open MeasureTheory

theorem measurable_boxQInd {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hA : MeasurableSet A) (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ) :
    Measurable (Work.UBBInputs8.boxQInd volA A i Ψ) := by
  have hP : Measurable
      (fun x : Submission.BoseGases.X N => A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply i)
  have hInt : Measurable
      (fun x : Submission.BoseGases.X N => ∫ z in A, Ψ (Function.update x i z)) := by
    have huncurry : StronglyMeasurable
        (Function.uncurry fun x : Submission.BoseGases.X N =>
          fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x i z)) :=
      hΨ.stronglyMeasurable.comp_measurable (measurable_update')
    exact (huncurry.integral_prod_right (ν := volume.restrict A)).measurable
  have hPind : Measurable (Work.UBBInputs8.boxPInd volA A i Ψ) := by
    unfold Work.UBBInputs8.boxPInd
    exact (measurable_const.mul hInt).mul hP
  have hbox : Work.UBBInputs8.boxQInd volA A i Ψ
      = fun x => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          - Work.UBBInputs8.boxPInd volA A i Ψ x := rfl
  rw [hbox]
  exact (hP.mul hΨ).sub hPind

end Work.SlotWord
