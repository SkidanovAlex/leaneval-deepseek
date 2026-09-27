import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.FlowerCopy.LocalInput
import Submission.Work.EKLComp.plaque_propor
import Submission.Work.EKLComp.condExpKernel_pos

/-!
# `Work.EKLRelCross.glue_pieces`

The inputs of the construction of leafwise measures which follow immediately from
already-proved results:

* `localFlowerInput_of` (in `FlowerCopy/LocalInput.lean`) — the local flower
  (Pisa 6.7 + 6.9–6.15);
* `proporPiece_of_horo` — proportionality of the conditional measures of two plaque algebras
  (Pisa 5.17 + 6.17), from `Work.EKLComp.plaque_propor`;
* `posPiece_of_horo` — positivity of the conditional measure of a plaque algebra on plaques
  (Pisa 6.20), from `Work.EKLComp.condExpKernel_pos`.
-/

open MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract Work.EKLComp

/-- **Pisa 5.17 + 6.17**: the conditional measures of two plaque algebras are proportional on the
intersection of their atoms, a.e. on the intersection of the domains. -/
theorem proporPiece_of_horo {U : Subgroup SL3} (hU : IsHoro U) {μ : Measure X3}
    [IsProbabilityMeasure μ] : ProporPiece U μ := by
  intro Z₁ Z₂ 𝔪₁ 𝔪₂ h₁ h₂
  exact plaque_propor U μ Z₁ Z₂ 𝔪₁ 𝔪₂ h₁ h₂

/-- **Pisa 6.20**: the conditional measure of a plaque algebra is positive on the image of an open
neighbourhood of the identity inside `U`. -/
theorem posPiece_of_horo {U : Subgroup SL3} (hU : IsHoro U) {μ : Measure X3}
    [IsProbabilityMeasure μ] : PosPiece U μ := by
  intro Z 𝔪 h𝔪 O hO h1
  exact condExpKernel_pos U hU.1 Z 𝔪 h𝔪 μ O hO h1

end Work.EKLRelCross
