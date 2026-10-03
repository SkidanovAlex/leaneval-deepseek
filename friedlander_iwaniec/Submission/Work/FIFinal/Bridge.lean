/-
# `Submission.Work.FIFinal.Bridge` — from the areas through the FIChain endgame to the challenge

This module wires the two halves of the project together:

    `Area4_6c`  ⟹  `Prop41StatementPiBig`   (this directory's `Prop41.lean`)
                ⟹  `Prop41Stmt`             (the `Π`-removal `PiRemoval`, the one input still open)
                ⟹  `PrimeSumBound`          (`Work.FIChain.primeSum_bound_of_prop41'`)
                ⟹  `ChallengeTheorem`       (this directory's `Endgame.lean`)

`Work.FIChain.primeSum_bound_of_prop41'` takes the single binder `h : Prop41Stmt` (the `S₃` binder
`hS3` of the older signature is discharged on disk by `Work.FIChain.S3fixed_signed_Bstar`, see the
module docstring of `Defs.lean`).  Hence **one** input of the challenge is not supplied anywhere in
the workspace:

* `PiRemoval` — the passage from the areas' output (the `Π`-*restricted* Proposition 4.1,
  `Work.FITop4.Prop41StatementPiBig`) to the `Π`-*free* pointwise contract
  `Work.FITop.Prop41Statement` that the endgame consumes.  This is the companion paper's §10
  (Theorem 3), quoted as **(B\*) ⟹ (∫B)**: *integrated*, not pointwise.  See the module docstring of
  `Defs.lean`, `Submission/Work/FITop4/Red5/Vocab.lean:22` and
  `Submission/Work/FIChain/NOTES.md` §38 for the two independent reasons why the pointwise
  implication is not available in this workspace (the inner sums are *signed*, so
  `|Σ_{S₁} f| ≤ |Σ_{S₂} f|` does not follow from `S₁ ⊆ S₂`; and the `B ≤ 2^31` range of the frozen
  contract is stronger than what the paper's numerology grants at small `η`).  The `Π`-removal in
  the form the paper actually proves *is* formalised in this workspace —
  `Work.FIChain.BprimeWindowIntegrated` and `Work.FIChain.RhoWindowIntegrated2`, both fuelled by
  `Prop41StatementPiBig` — but `Work.FIChain/NOTES.md` §43 shows that the position-integrated
  `ρ`-window cannot feed the `S₃` consumer, so the endgame's two inputs
  (`Work.FIChain.windows_at_Bstar` and `Work.FIChain.S3fixed_signed_Bstar`) really do need the
  pointwise contract.

The `PrimeSumBound` interface (`challenge_of_primeSumBound`) is the stable one: whatever form the
FIChain endgame finally takes, closing the challenge needs only a proof of `PrimeSumBound`.
-/
import Mathlib
import Submission.Work.FIFinal.Defs
import Submission.Work.FIFinal.Endgame
import Submission.Work.FIFinal.Prop41
import Submission.Work.FIChain.Target

set_option autoImplicit false

namespace Work.FIFinal

open Finset Filter
open scoped BigOperators

noncomputable section

/-- The prime-sum bound in the FIChain vocabulary is the same statement as in the `Work.FITop`
vocabulary used by this chapter's endgame. -/
theorem primeSumBound_of_fichain (h : PrimeSumBoundFIChain) : PrimeSumBound := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with N hN
  simpa only [primeSumFI, Work.FITop.FIaR, AcountF, AcountTil, Work.FIChain.AcountAtilC,
    Work.FITop.AcountAtil, Work.FIChain.atilc, Work.FITop.atilFIa] using hN

/-- Sanity: `PrimeSumBound` alone already gives the challenge (the last mile, with no input left
open). -/
theorem challenge_of_primeSumBound_apply (hb : PrimeSumBound) : ChallengeTheorem :=
  challenge_of_primeSumBound hb

end

end Work.FIFinal
