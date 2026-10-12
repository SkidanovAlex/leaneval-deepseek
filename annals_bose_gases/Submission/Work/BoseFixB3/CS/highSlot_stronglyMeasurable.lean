import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Submission.Work.BoseFixB3.Split.lowSlotStronglyMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS

open MeasureTheory

/-- `highSlot` is the complementary half `(1 − f_L)` of the low/high momentum split, so it
is the difference of the strongly measurable `x ↦ Ψ x` (continuous by hypothesis) and the
strongly measurable `x ↦ lowSlot fc κ ℓ j Ψ x` (proved in
`Submission.Work.BoseFixB3.Split.lowSlotStronglyMeasurable`, where the slot integral over
momentum is handled by `StronglyMeasurable.integral_prod_right`). -/
theorem highSlot_stronglyMeasurable {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} {n : ℕ}
    (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) :
    MeasureTheory.StronglyMeasurable
      (fun x : Submission.BoseGases.X n => Work.BoseFixB3.highSlot fc κ ℓ j Ψ x) := by
  have hlow : StronglyMeasurable
      (fun x : Submission.BoseGases.X n => Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) :=
    Work.BoseFixB3.Split.lowSlotStronglyMeasurable (fc := fc) (κ := κ) (ℓ := ℓ) j hΨ
  have hsub : StronglyMeasurable
      (fun x : Submission.BoseGases.X n =>
        Ψ x - Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) :=
    hΨ.stronglyMeasurable.sub hlow
  have hgoal : (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ j Ψ x)
      = fun x : Submission.BoseGases.X n =>
        Ψ x - Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x := by
    funext x
    rw [Work.BoseFixB3.highSlot]
  rw [hgoal]
  exact hsub

end Work.BoseFixB3.CS
