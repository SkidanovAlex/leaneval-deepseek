-- **CORRECTION (project lead, 2026-09-26): the "K5 at `b = 1` is false" claim of this area is
-- RETRACTED** (see `Submission/Work/StemsB/FINDING_K5_b1_FALSE.md`).  `Work.Serre.SerreStableExact`
-- *is* proved (`#print axioms` = `{propext, Classical.choice, Quot.sound}`) and the statements of
-- this file, which carry the stronger hypothesis `2 ≤ b`, are correct but *redundant* with it, not a
-- correction of it.  The docstring below was written under the retracted belief; read it with that
-- in mind.  (The mistake: the fibre hypothesis `∀ i < f, Subsingleton (π_i F)` includes `i = 0`,
-- i.e. path connectedness of the fibre, so a disconnected fibre is never a counterexample.)

import Mathlib
import Submission.Work.StemsB.serreStableExactTwo
import Submission.Work.StemsB.truncationHomologyTransfer_of_serreTwo
-- NOTE (area STEMSB, 2026-09-27): the import of `Submission.Work.StemsB.stableStemsTorsionB`
-- was DELETED here: nothing in this file used it, and it created an **import cycle** with the
-- contract file, because `Stems/c2FreeMain.lean` imports this module (and the contract file must
-- be able to import the ladders through `c2FreeMain`/`Drive.rh3OfE3b`).  Do not re-add it.
import Submission.Work.RatHurewicz.S3Wired

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# This area's contract, on the **corrected** K5: the only external input left is `RangeModelRatAcyclic`

The ladder of `Submission/Work/StemsB/contractInputs.lean` cites
`Work.Serre.SerreExactRangeCorrected`, which is **false as stated** (`1 ≤ b` is not enough: see
`Submission/Work/StemsB/FINDING_K5_b1_FALSE.md`; the universal cover `ℝ → S¹` with `b = 1`, `f = 2`
refutes it).  The corrected statement (`2 ≤ b`, base simply connected) is *proved* in
`Submission/Work/StemsB/serreStableExactTwo.lean`, and the S3 chain has been ported to it in
`Submission/Work/StemsB/truncationHomologyTransfer_of_serreTwo.lean`.  Consequently the K5 input
disappears from the ladder:

```
Work.Drive.StableStemsTorsion
  ⟸ Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable3
  ⟸ Work.Drive.RationalHurewiczStable3
  ⟸ Work.RatHurewicz.rationalHurewiczStable3_of_transfer   (TowerStepData is proved)
  ⟸ Work.RatHurewicz.TruncationHomologyTransfer
  ⟸ Work.StemsB.truncationHomologyTransfer_of_serreTwo
       + Work.StemsB.SerreExactRangeCorrectedTwo     (PROVED here, axiom-clean)
       + Work.RatHurewicz.RangeModelRatAcyclic        (area RATHUREWICZ: C2 + C3)
```

So this area's contract follows from `Work.RatHurewicz.RangeModelRatAcyclic` alone (plus the
corrected K5, which is now a theorem), i.e. from the two statements `Work.Stems.Engine.C2oddFree c`
(area STEMS) and `Work.StemsB.C3FiniteTwo` (area SERRE), by
`Work.StemsB.rangeModelRatAcyclic_of_C2odd_C3`.
-/

namespace Work.StemsB

noncomputable section

/-- **`RationalHurewiczStable3` from `RangeModelRatAcyclic`** — the S3 chain with the corrected K5
(no false hypothesis). -/
theorem rationalHurewiczStable3_via_two (hem : Work.RatHurewicz.RangeModelRatAcyclic) :
    Work.Drive.RationalHurewiczStable3 :=
  Work.RatHurewicz.rationalHurewiczStable3_of_transfer
    (truncationHomologyTransfer_of_serreTwo serreExactRangeCorrectedTwo hem)

/-- **This area's contract from `RangeModelRatAcyclic`** — the corrected-K5 form of the ladder: K5
is a theorem (`Work.StemsB.serreExactRangeCorrectedTwo`), so the only external input is the rational
acyclicity of range models of `K(A,k)`. -/
theorem stableStemsTorsion_via_two (hem : Work.RatHurewicz.RangeModelRatAcyclic) :
    Work.Drive.StableStemsTorsion :=
  Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable3
    (rationalHurewiczStable3_via_two hem)

#print axioms Work.StemsB.rationalHurewiczStable3_via_two
#print axioms Work.StemsB.stableStemsTorsion_via_two

end

end Work.StemsB
