import Submission.Work.BoxShrink.PinchOff.RefuteDrop
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Config
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.omega_rank_two
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.transverseSlice_drop
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.tameClosedSlice_drop
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.sphereTrace_inessential_drop
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.sigma_inessential_drop
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.halfUp_inessential_drop
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.halfDown_inessential_drop

/-!
# The honest residual of the pinch is false: `¬ DropCase`

Assembling the pieces of this directory at the `RefuteDrop` configuration
(`RefuteDrop/Config.lean`: the linear diffeomorphism `dropDiffeo`, `dropS = 7/5`, `dropC = 0`,
`dropCyc = swap 0 2`, `dropU = 0`), all *five* hypotheses of `DropCase` hold while its conclusion
fails:

* `TransverseSlice` — `transverseSlice_drop`;
* `TameClosedSlice` — `tameClosedSlice_drop`;
* hS, the box-sphere trace inessential — `sphereTrace_inessential_drop`;
* hZ, the slice inessential — `sigma_inessential_drop`;
* `W(Halves) = ⊥` — from `halfUp_inessential_drop`, `halfDown_inessential_drop` via the additivity
  of the winding span over disjoint open pieces;
* and yet `W(Ω) = ⊤` — `omega_rank_two` — so `finrank W(Ω) = 2 > 1`.

Hence `¬ DropCase`, and with it the refutation of `KeyTameClosed` (equivalently the parent
chapter's `PinchNoJump` under the general position of the cutting plane, i.e. Pardon's Lemma 3
conclusion without his counting).  Pardon's counting is therefore not a convenience: the ledger's
`bubble` field has to be the *counted* form `Work.BoxShrink.Pinch.CountingHalf`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-- **The two closed halves of the counterexample are jointly inessential.** -/
theorem halves_inessential_drop :
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus dropDiffeo)
      (Halves dropDiffeo dropS dropC dropCyc dropU) = ⊥ := by
  rw [Halves, Work.SurgeryInvariance.Span.union_eq_sup
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion _ _ _ _ _)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion _ _ _ _ _)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion _ _ _ _ _),
    halfUp_inessential_drop, halfDown_inessential_drop, sup_bot_eq]

/-- **The conclusion of `DropCase` fails at the counterexample**: `finrank W(Ω) = 2`. -/
theorem not_finrank_le_one_drop :
    ¬ (Module.finrank ℚ
        ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus dropDiffeo)
          (Omega dropDiffeo dropS dropC dropCyc)) ≤ 1) := by
  rw [omega_rank_two]
  have h2 : Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) = 2 := by
    rw [finrank_top, Module.finrank_prod]
    simp
  rw [h2]
  norm_num

/-- **`DropCase` is false.** -/
theorem not_dropCase : ¬ DropCase :=
  Work.BoxShrink.PinchOff.not_dropCase_of_counterexample
    ⟨dropDiffeo, dropS, dropC, dropCyc, dropU, transverseSlice_drop, tameClosedSlice_drop,
      sphereTrace_inessential_drop, sigma_inessential_drop, halves_inessential_drop,
      not_finrank_le_one_drop⟩

/-- **The honest residual `KeyTameClosed` of the area is false.** -/
theorem not_keyTameClosed : ¬ KeyTameClosed :=
  fun h => not_dropCase (Work.BoxShrink.PinchOff.dropCase_of_keyTameClosed h)

end

end Work.BoxShrink.PinchOff.RefuteDrop
