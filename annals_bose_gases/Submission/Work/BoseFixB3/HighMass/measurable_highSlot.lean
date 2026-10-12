import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Submission.Work.BoseFixB3.CS.highSlot_stronglyMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/HighMass/measurable_highSlot`

`highSlot fc κ ℓ j Φ` is the slot-`j` lift of the complementary multiplier `1 − f_L`
(`Work.BoseFixB3.highSlot`, `Work.BoseFixB3.highMult`), i.e. the pointwise difference

`highSlot fc κ ℓ j Φ x = Φ x − lowSlot fc κ ℓ j Φ x`,

where `lowSlot` is the corpus's slot-`j` momentum multiplier `f_L` applied to the slot-`j`
fibre (`Submission.Work.BoseBoxFix.lowSlot` / `lowMult`).

Measurability of this function is the standard integral-form argument: the slot integral
over momentum is handled by `MeasureTheory.StronglyMeasurable.integral_prod_right`, which
gives strong measurability of `x ↦ lowSlot fc κ ℓ j Φ x` for continuous `Φ`
(`Submission.Work.BoseFixB3.Split.lowSlotStronglyMeasurable`, packaged in
`Submission.Work.BoseFixB3.CS.highSlot_stronglyMeasurable`), and on the second-countable
codomain `ℝ` strong measurability is equivalent to measurability
(`stronglyMeasurable_iff_measurable`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.HighMass

/-- `highSlot` applied to a continuous `n`-body state is measurable: it is the difference of
the continuous `x ↦ Φ x` and the strongly measurable slot multiplier `lowSlot`, and on the
second-countable space `ℝ` strong measurability implies measurability. -/
theorem measurable_highSlot {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Measurable (fun x : Submission.BoseGases.X n => Work.BoseFixB3.highSlot fc κ ℓ j Φ x) :=
  stronglyMeasurable_iff_measurable.mp
    (Work.BoseFixB3.CS.highSlot_stronglyMeasurable (κ := κ) (ℓ := ℓ) j hΦ)

end Work.BoseFixB3.HighMass
