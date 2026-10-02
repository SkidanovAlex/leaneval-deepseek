import Mathlib
import Submission.Work.RatHurewicz.S3Wired
import Submission.Work.RatHurewicz.S3Corr
import Submission.Work.RatHurewicz.SerreHurewicz3
import Submission.Work.RatHurewicz.stableStemsTorsion_of_stable3
import Submission.Work.Serre.StableExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The drive's contracts from the two Eilenberg–MacLane/Serre inputs

Area **RATHUREWICZ**.  This is the final wiring of the chapter: the rational Hurewicz theorem in the
stable range — the drive's contract `Work.Drive.RationalHurewiczStable`, its one-degree-short form
`Work.Drive.RationalHurewiczStable3` (area THOM) and the stable-stems contract
`Work.Drive.StableStemsTorsion` (area STEMS) — rests on exactly **two** statements of the
neighbouring chapter (area SERRE's, per `Submission/Work/Drive/SERRE_BLUEPRINT.md`):

* **`Work.RatHurewicz.RangeModelRatAcyclic`** — the rational homology of a range model of `K(A,k)`
  vanishes in degrees `k < j ≤ 2k-1`; this is the blueprint's **C2** (for free `A`: rationally
  `K(A,k)` is a wedge of `k`-spheres below `2k`) and **C3** (for torsion `A`), together with the
  comparison of a range model with the genuine space;

* **`Work.Serre.SerreExactRangeCorrected`** — Serre's exact sequence in the stable range,
  `H_i(E,F) ≅ H_i(B,*)` for `i < b+f` and `1 ≤ b`; this is **K5** of the blueprint, and it follows
  from `Work.Serre.SerreStableExact` by `Work.Serre.serreExactRangeCorrected_of_stableExact`.

  **Caveat, reported by area SERRE.**  The form `Work.StemsB.SerreExactRange` of this statement (the
  one stated without the hypothesis `1 ≤ b`) is *false*: for a discrete base and a fibre with two
  points over a second base component the map `H_0(E,F) → H_0(B,{b₀})` is not an isomorphism.  The
  applications of this chapter all have `b = k ≥ 2`, so the corrected statement — and only the
  corrected statement — is the one used below.  (`truncationHomologyTransfer_of_serre`,
  the form of the transfer stated with `Work.StemsB.SerreExactRange`, is nevertheless a true
  implication, and its proof uses only the instances with large `b`; it is kept in the directory.)

The chain, all of whose links are proved in this area except the two inputs above:

```
RangeModelRatAcyclic, SerreExactRangeCorrected
  ⟹ TruncationHomologyTransfer   (S3Corr.truncationHomologyTransfer_of_serre — delegated, proved)
  ⟹ Work.Drive.RationalHurewiczStable          (rationalHurewiczStable_of_transfer)
  ⟹ Work.Drive.RationalHurewiczStable3         (rationalHurewiczStable3_of_transfer)
  ⟹ Work.Drive.StableStemsTorsion              (stableStemsTorsion_of_transfer)
```

and in between: the stem induction `hurewiczTorsionSucc_of_inputs` (`S3Assembly.lean`), run on the
truncation tower whose data `TowerStepData` is proved here (`towerStepData.lean`), with the
first-degree Hurewicz theorem modulo torsion as the base case.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The range form of the rational Hurewicz theorem** from the two inputs of area SERRE. -/
theorem hurewiczModTorsionRange_of_serre (h : Work.Serre.SerreExactRangeCorrected)
    (hem : RangeModelRatAcyclic) : HurewiczModTorsionRange :=
  hurewiczModTorsionRange_of_transfer (S3Corr.truncationHomologyTransfer_of_serre h hem)

/-- **The drive's contract `Work.Drive.RationalHurewiczStable`** from the two inputs of area
SERRE. -/
theorem rationalHurewiczStable_of_serre (h : Work.Serre.SerreExactRangeCorrected)
    (hem : RangeModelRatAcyclic) : Work.Drive.RationalHurewiczStable :=
  rationalHurewiczStable_of_transfer (S3Corr.truncationHomologyTransfer_of_serre h hem)

/-- **The one-degree-short contract `Work.Drive.RationalHurewiczStable3`** (area THOM) from the two
inputs of area SERRE. -/
theorem rationalHurewiczStable3_of_serre (h : Work.Serre.SerreExactRangeCorrected)
    (hem : RangeModelRatAcyclic) : Work.Drive.RationalHurewiczStable3 :=
  rationalHurewiczStable3_of_transfer (S3Corr.truncationHomologyTransfer_of_serre h hem)

/-- **The contract of area STEMS `Work.Drive.StableStemsTorsion`** from the two inputs of area
SERRE. -/
theorem stableStemsTorsion_of_serre (h : Work.Serre.SerreExactRangeCorrected)
    (hem : RangeModelRatAcyclic) : Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_rationalHurewiczStable3 (rationalHurewiczStable3_of_serre h hem)

/-- **The drive's contract from K5 of the blueprint** (`Work.Serre.SerreStableExact`, the Serre
exact sequence in the stable range for Serre fibrations) together with the rational acyclicity of
the range models. -/
theorem rationalHurewiczStable_of_stableExact (h : Work.Serre.SerreStableExact)
    (hem : RangeModelRatAcyclic) : Work.Drive.RationalHurewiczStable :=
  rationalHurewiczStable_of_serre (Work.Serre.serreExactRangeCorrected_of_stableExact h) hem

/-- **The contract of area STEMS from K5 of the blueprint** together with the rational acyclicity
of the range models. -/
theorem stableStemsTorsion_of_stableExact (h : Work.Serre.SerreStableExact)
    (hem : RangeModelRatAcyclic) : Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_serre (Work.Serre.serreExactRangeCorrected_of_stableExact h) hem

end

end Work.RatHurewicz
