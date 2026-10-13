import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.ESW.StepPieces
import Submission.Work.FTS.EllipticEst.TT.ESW.ShiftWeak
import Submission.Work.FTS.EllipticEst.Prop.Rtilde.BSlot
import Submission.Work.FTS.EllipticEst.Prop.Rtilde.SourceLe
import Submission.Work.FTS.EllipticEst.remov.EllUnifBslot
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.ATopClean
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.DzSliceIdent
import Submission.Work.FTS.EllipticEst.remov.EllEstUnif_top_core_of_halves
import Submission.Work.FTS.EllipticEst.remov.HkSq_step_le
import Submission.Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TT.est_step_weak`: the induction step of Elgindi's `prop:Hk`, in the weak class

## Why the imports are what they are (read this before changing them)

`TT.propHk_core` (hence `remov.propHk_fts`) **imports** this very file: the certificate `prop:Hk`
consumes the induction step proved here.  Consequently nothing on the critical path of
`est_step_weak` may reach `remov.propHk_fts`, or Lean would report an import cycle.  The natural
modules of `Submission/Work/FTS/EllipticEst/remov/` for two of the ingredients

* `remov.EllWeakPos_DzIter_one_shift` (admissibility of the radially differentiated data),
* `remov.A_top_slot_bound` (the top angular slot of `z²∂_zzΨ`),
* `remov.Dz_slice_identities` (the two slice identities),
* `remov.EllEstUnif_step` (the assembly itself),

all have cones that reach `propHk_fts`, so they are replaced here by cone-clean twins:

* `TT.ESW.Pieces.EllEstUnif_step_of_pieces` — a verbatim copy of the assembly (`ESW/StepPieces.lean`);
* `TT.ESW.Shift.EllWeakPos_DzIter_one_shift_of_two_le` — a copy of the second (`ESW/ShiftWeak.lean`)
  with the unused `EllHyp_certificates` import dropped and two structural facts
  (`SmoothOpen.zsq_mul`, `HkMem_of_majorant_ae`) re-proved in `ESW/OpenMem.lean`;
* `remov.TopCoreB.ATopClean` — a cone-clean module declaring `remov.A_top_slot_bound` *under the
  same name* as the original;
* `H2W.Slot01W.DzSliceIdent` — likewise for `remov.Dz_slice_identities`.

The two top angular slots (`hcore`) are supplied by

* `remov.A_top_slot_bound` (from `remov.TopCoreB.ATopClean`, proved, cone-clean);
* `TT.ESW.bSlot_bound` (proved in `Prop/Rtilde/BSlot.lean`): the `B`-slot, assembled from the
  sharp angular chain, the one-dimensional far-region estimate `remov.slice_ang_gen` applied
  slicewise (`TT.ESW.U_le_of_1d`), the source domination (`Prop.Rtilde.SourceLe`, proved) and the
  low-order terms.  `bSlot_bound` takes those two inputs (`hSrc`, `hOneD`) as explicit hypotheses;
  they are instantiated here with `Prop.Rtilde.SourceLe` (proved) and
  `Prop.Rtilde.oneD_of_far` applied to the far-window bound `Prop.Rtilde.VFar` — the single
  unproved input of the whole route (the paper's far-region §"General `ℋ^k` case" analysis on
  `[3π/8, π/2]`, proved from `SliceHyp` by `remov.slice_ang_v_far`).
-/

namespace Work.FTS.EllipticEst.TT

/-- Elgindi's §"General `ℋ^k` Case" (tex 986--1008), the induction step of Proposition
`prop:Hk`, in the weak hypothesis class `EllWeakPos` of `TT.WeakDefs`: for every `k ≥ 3`, the
level-`(k-1)` estimate for all weak data (with an `α`-uniform constant), together with the
level-`0` (`η`-weighted) estimate `EllWeak0`, yields the level-`k` estimate with an `α`-uniform
constant.  (Compare `Work/FTS/EllipticEst/propHk_orth_weak.lean`, whose NOTES record the same
induction in the `EllHyp` class.)

The proof is the assembly `ESW.Pieces.EllEstUnif_step_of_pieces` (the level splitting of `HkSq`,
the `D_z`-shift, the admissibility of the shifted data and the two top angular slots) with the
two top slots supplied by `remov.TopCoreB.ATopClean` (`remov.A_top_slot_bound`) and
`ESW.bSlot_bound`. -/
theorem est_step_weak : ∀ k : ℕ, 3 ≤ k →
    (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) →
    (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif (k - 1) C) →
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif k C :=
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
        (fun k hk => Work.FTS.EllipticEst.TT.ESW.bSlot_bound D hD
          (fun k hk => Work.FTS.EllipticEst.Prop.Rtilde.SourceLe D hD k hk)
          (fun k hk => Work.FTS.EllipticEst.remov.EllUnifBslot.slice_ang_gen_live k (by omega))
          k hk)
        k hk)
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

end Work.FTS.EllipticEst.TT
