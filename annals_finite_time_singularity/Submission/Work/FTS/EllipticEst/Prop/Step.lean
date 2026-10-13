/-
# `Prop.step` — the induction step of `prop:Hk`

Elgindi's §"General `ℋ^k` case" (Annals **194** (2021), tex 986–1008): for `k ≥ 3`, the
level-`(k-1)` estimate together with the level-`0` (`η`-weighted) estimate gives the level-`k`
estimate, with an `α`-uniform constant.

## The assembly

The *assembly* `EllEstUnif_step_of_pieces` (the exact splitting
`HkSq α k f ≤ HkSq α (k-1) f + (k+1) HkSq α (k-1) (D_zf) + Tk α k f` plus the bookkeeping) is
taken from the clean-cone copy `TT.ESW.StepPieces`.  Its inputs are supplied by proved
declarations with clean cones:

* `hstep`  ⟸ `remov.HkSq_step_le`;
* `hshift` ⟸ `remov.HkSq_Dz_shift_le`;
* `hpos`   ⟸ `TT.ESW.Shift.EllWeakPos_DzIter_one_shift_of_two_le` (the admissibility of the
  radially differentiated datum; the clean-cone copy of `remov.EllWeakPos_DzIter_one_shift`);
* `hcore`  ⟸ `remov.EllEstUnif_top_core_of_halves` applied to the two top-slot bounds
  `remov.A_top_slot_bound` (the clean-cone copy `remov.TopCoreB.ATopClean`, `#print axioms`
  clean) and `Prop.bSlotTop` (a clean-cone copy of the `∂_θθΨ`-slot);
* `hsmF`, `hsmA`, `hsmB` ⟸ `remov.smoothOpen_slices_weak`;
* `hAz`, `hBz` ⟸ `remov.Dz_slice_identities` (the clean-cone copy `AeS1.DzSliceIdentities`).

No `R̃`-slot (`remov.Rtilde_Tk_bound`) is needed: the `∂_θθΨ`-slot is proved *directly*, without
the rearrangement `R̃ = ∂_θθΨ + α²z²∂_zzΨ`.-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TT.ESW.StepPieces
import Submission.Work.FTS.EllipticEst.TT.ESW.ShiftWeak
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.ATopClean
import Submission.Work.FTS.EllipticEst.AeS1.DzSliceIdentities
import Submission.Work.FTS.EllipticEst.Prop.bSlotTop
import Submission.Work.FTS.EllipticEst.remov.EllEstUnif_top_core_of_halves
import Submission.Work.FTS.EllipticEst.remov.HkSq_step_le
import Submission.Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

open Work.FTS.EllipticEst.TT

/-- **The induction step of `prop:Hk`.**  `TT.ESW.StepPieces.EllEstUnif_step_of_pieces` with all
of its inputs supplied by proved declarations. -/
theorem step : ∀ k : ℕ, 3 ≤ k →
    (∃ C : ℝ, 0 < C ∧ EllWeak0 C) →
    (∃ C : ℝ, 0 < C ∧ EllEstUnif (k - 1) C) →
    ∃ C : ℝ, 0 < C ∧ EllEstUnif k C :=
  Work.FTS.EllipticEst.TT.ESW.Pieces.EllEstUnif_step_of_pieces
    (hstep := fun {k} hk α f hcd hmem =>
      Work.FTS.EllipticEst.remov.HkSq_step_le hk α f hcd hmem)
    (hshift := fun {k} hk α f hcd hmem =>
      Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le hk α f hcd hmem)
    (hpos := fun {α} {k} hk {F} {Ψ} h =>
      Work.FTS.EllipticEst.TT.ESW.Shift.EllWeakPos_DzIter_one_shift_of_two_le
        (α := α) (k := k) hk h)
    (hcore := fun D hD k hk =>
      Work.FTS.EllipticEst.remov.EllEstUnif_top_core_of_halves D hD
        (fun k hk => Work.FTS.EllipticEst.remov.A_top_slot_bound D hD k hk)
        (fun k hk => bSlotTop D hD k hk) k hk)
    (hsmF := fun {α} {k} {F} {Ψ} h n =>
      (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1 n)
    (hsmA := fun {α} {k} {F} {Ψ} h n =>
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).2.2.1 n)
    (hsmB := fun {α} {k} {F} {Ψ} h n =>
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).2.2.2 n)
    (hAz := fun {α} {k} {F} {Ψ} h =>
      (Work.FTS.EllipticEst.remov.Dz_slice_identities Ψ h.smoothOpen).1)
    (hBz := fun {α} {k} {F} {Ψ} h =>
      (Work.FTS.EllipticEst.remov.Dz_slice_identities Ψ h.smoothOpen).2)

end Work.FTS.EllipticEst.Prop
