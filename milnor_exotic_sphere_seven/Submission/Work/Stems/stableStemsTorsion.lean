import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Stems.Pi
import Submission.Work.Stems.Engine.C2Range
import Submission.Work.Stems.Engine.FreudenthalBridge
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.Stems.Engine.C2Even
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Stems.Engine.C2Summary
import Submission.Work.Stems.Engine.FreeTopAssembly
import Submission.Work.Stems.c2FreeMain
import Submission.Work.Serre.StableExact
import Submission.Work.RatHurewicz.transfer3
import Submission.Work.RatHurewicz.stableStemsTorsion_of_stable3
import Submission.Work.Stems.oddCoverAcyclicRange
import Submission.Work.Serre.serreC0Range
import Submission.Work.Serre.serreStableExact
import Submission.Work.RatHurewicz.freudenthalTorsionTransfer
import Submission.Work.RatHurewicz.S3Contracts
import Submission.Work.Stems.isEMSpace_loop
import Submission.Work.Stems.homotopyFibre_evalOne_equiv_loop
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint
import Submission.Work.Stems.ratH_isEMSpace_self
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.serreC3FiniteOne
import Submission.Work.RatHurewicz.E3bBridge.Assembly
import Submission.Work.Stems.thomCylCellStepRace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

AREA STEMS. Prove `Work.Drive.StableStemsTorsion`: every element of π_{n+i+1}(Sⁿ) has finite order, for
0 ≤ i ≤ 7 and n ≥ i + 3 (the stable range), using Mathlib's `HomotopyGroup` and the unit sphere in
EuclideanSpace ℝ (Fin (n+1)). This is Serre's finiteness theorem restricted to stems 1..8. It is the
homotopy-theoretic core of Thom's theorem, and Mathlib has almost nothing here (no Hurewicz theorem, no
Freudenthal, no spectral sequences, no Eilenberg–MacLane spaces as topological spaces). The workspace has
singular (co)homology with cup products, Mayer–Vietoris and the pair long exact sequence
(Submission/Work/Cohomology/).
Plan it before coding; pick the route with the least infrastructure and check it end to end first. Options:
(a) Serre: rational homology of K(ℤ,m) vanishes in degrees m < d < 2m (via the path-loop fibration and a
    Serre exact sequence in the stable range, or via simplicial abelian groups / Dold–Kan), then a rational
    Hurewicz/Whitehead theorem mod torsion in the stable range for the map Sⁿ → K(ℤ,n);
(b) anything shorter you can justify (e.g. only the stable range is needed: Freudenthal, stable homotopy as
    a homology theory rationally).
Write down the full dependency list with an honest size estimate before delegating, then delegate the
pieces in parallel. Keep all new files under Submission/Work/Stems/.
-/

namespace Work.Stems

/-- **The range-form route to the target** (proved): the STEMS contract follows from `C0` in the
bare form (models of `K(ℤ,n)`; the bottom-cell map is built from it by
`Work.Serre.exists_bijective_piMapN'`), the *range*-form odd step of the `K(ℤ,n)` layer
(`Work.Stems.Engine.C2oddRange`, i.e. the cover of `Sⁿ` rationally acyclic below degree `2n-3` —
all the range-form Gysin and the corrected `E4` give) and the rational vanishing Hurewicz theorem
`S1`.  Freudenthal's input is discharged by `Work.Stems.Engine.serreFreudenthal`.

The remaining two open inputs of the target are therefore `Work.Serre.SerreC0` (RATHUREWICZ's cell
attachment) and `Work.Stems.Engine.C2oddRange`; `Work.Serre.SerreS1` in turn follows from
`Work.Drive.RationalHurewiczStable` or from `C0 + C3 + E3a`.  See `Submission/Work/Stems/EM_AUDIT.md`. -/
theorem stableStemsTorsion_of_C0_C2oddRange_S1 (hC0 : Work.Serre.SerreC0)
    (hOdd : Work.Stems.Engine.C2oddRange) (hS1 : Work.Serre.SerreS1) :
    Work.Drive.StableStemsTorsion :=
  Work.Stems.Engine.stableStemsTorsion_of_rangeInputs hC0 hOdd hS1
    Work.Stems.Engine.serreFreudenthal

theorem stableStemsTorsion_of_C2contracts (hC0 : Work.Serre.SerreC0)
    (h : Work.RatHurewicz.RangeModelRatAcyclic) (hC1 : Work.Serre.SerreC1)
    (hE3b : Work.Serre.SerreE3b) (hK5 : Work.Serre.SerreStableExact)
    (hS1 : Work.Serre.SerreS1) : Work.Drive.StableStemsTorsion :=
  Work.Stems.Engine.stableStemsTorsion_of_rangeInputs hC0
    (Work.Stems.Engine.c2evenRange_and_c2oddRange h hC1 hE3b hK5).2 hS1
    Work.Stems.Engine.serreFreudenthal

/-- **The STEMS contract from the *free-top* inputs** (`Submission/Work/Stems/Engine/FreeTopAssembly.lean`):
the same reduction as `stableStemsTorsion_of_C2contracts`, but running on the *range models* of
`Work.Serre.SerreC0Range` (proved) instead of the unbounded `Work.Serre.SerreC0`, and with the
`C2` input in the capped free-top form `Work.Stems.Engine.OddCoverAcyclicRange` (whose eventual
producer is `Work.Stems.oddCoverAcyclicRange`, from the free-top even step
`Work.Stems.Engine.C2evenRangeModelVanishing` and `Work.Serre.SerreStableExact`). -/
theorem stableStemsTorsion_of_freeTop (hC0 : Work.Serre.SerreC0Range)
    (hOdd : Work.Stems.Engine.OddCoverAcyclicRange) (hS1 : Work.Serre.SerreS1)
    (hF : Work.Stems.FreudenthalTorsionTransfer) : Work.Drive.StableStemsTorsion :=
  Work.Stems.Engine.stableStemsTorsion_of_freeTopInputs hC0 hOdd hS1 hF

/-- **The STEMS contract from `RationalHurewiczStable` and the free-top `C2` input** (the two
contracts of the free-top route, `SerreS1` being `Work.Serre.serreS1_of_rationalHurewiczStable`). -/
theorem stableStemsTorsion_of_freeTop_of_ratHurewicz (hC0 : Work.Serre.SerreC0Range)
    (hOdd : Work.Stems.Engine.OddCoverAcyclicRange) (h : Work.Drive.RationalHurewiczStable)
    (hF : Work.Stems.FreudenthalTorsionTransfer) : Work.Drive.StableStemsTorsion :=
  Work.Stems.Engine.stableStemsTorsion_of_freeTopInputs hC0 hOdd
    (Work.Serre.serreS1_of_rationalHurewiczStable h) hF

/-- **The STEMS contract from the free-top `C2` layer** (all inputs as hypotheses): the chain is

  `RangeModelRatAcyclic + SerreE3b ⟹ C2evenRangeModelVanishing ⟹ (with K5) OddCoverAcyclicRange
   ⟹ (with SerreS1 and Freudenthal) StableStemsTorsion`.

Everything here is axiom-clean; the four inputs are other areas' contracts. -/
theorem stableStemsTorsion_of_freeTopC2 (hC0 : Work.Serre.SerreC0Range)
    (h : Work.RatHurewicz.RangeModelRatAcyclic) (hE3b : Work.Serre.SerreE3b)
    (hK5 : Work.Serre.SerreStableExact) (hS1 : Work.Serre.SerreS1)
    (hF : Work.Stems.FreudenthalTorsionTransfer) : Work.Drive.StableStemsTorsion :=
  Work.Stems.Engine.stableStemsTorsion_of_freeTopInputs hC0
    (Work.Stems.oddCoverAcyclicRange (Work.Stems.Engine.c2evenRangeModelVanishing h hE3b) hK5) hS1 hF

/-- **The STEMS contract from the two remaining contracts of the free-top route**, using the
currently available proofs of the other inputs (`Work.Serre.serreC0Range`,
`Work.Serre.serreStableExact`, `Work.Stems.oddCoverAcyclicRange`,
`Work.RatHurewicz.freudenthalTorsionTransfer`, and the RATHUREWICZ wiring
`RangeModelRatAcyclic + SerreStableExact ⟹ RationalHurewiczStable ⟹ SerreS1`).

**Status (read this before using the statement).**  The two *hypotheses* `RangeModelRatAcyclic` and
`SerreE3b` are the only *open* inputs; the other ingredients have proofs in the tree whose own
dependency closures still contain `sorry`s (notably `Serre.serrePairComparison`, the cell-induction
engine).  Consequently the proof term of this theorem does not (yet) satisfy the project's axiom
check — it is a *reduction*, not a finished proof, and the `sorryAx` of the dependencies is visible
in `#print axioms`. -/
theorem stableStemsTorsion_of_rangeAcyclic_E3b (h : Work.RatHurewicz.RangeModelRatAcyclic)
    (hE3b : Work.Serre.SerreE3b) : Work.Drive.StableStemsTorsion :=
  Work.Stems.Engine.stableStemsTorsion_of_freeTopInputs Work.Serre.serreC0Range
    (Work.Stems.oddCoverAcyclicRange (Work.Stems.Engine.c2evenRangeModelVanishing h hE3b)
      Work.Serre.serreStableExact)
    (Work.Serre.serreS1_of_rationalHurewiczStable
      (Work.RatHurewicz.rationalHurewiczStable_of_stableExact Work.Serre.serreStableExact h))
    Work.RatHurewicz.freudenthalTorsionTransfer

/-- **The STEMS contract from its two current inputs, in their weakest stated forms.**

The chain is

  `SerreExactRangeCorrected + RangeModelRatAcyclic3
     ⟹ TruncationHomologyTransfer3 ⟹ HurewiczModTorsionRange3
     ⟹ RationalHurewiczStable3 ⟹ StableStemsTorsion`,

where the last step uses Freudenthal's suspension theorem (proved,
`Work.RatHurewicz.freudenthalTorsionTransfer`) to move the boundary degree `d = 2n-2` of `Sⁿ` to
`S^{n+1}`.  Both inputs are *one degree short* of the "full" forms:

* `Work.Serre.SerreExactRangeCorrected` is the corrected stable-range Serre exact sequence
  (`1 ≤ b`; the form without that hypothesis is false, see `Work.Serre.StableExact`), and
* `Work.RatHurewicz.RangeModelRatAcyclic3` is the rational vanishing of a range model of `K(A,k)`
  in degrees `k < j ≤ 2k-2` only — the range the range-form `C2` engine
  (`Work.Stems.Engine.C2evenRange`) can reach.

This is the *shortest* reduction of the STEMS contract: it avoids `SerreE3b`, `SerreC0Range`,
`SerreS1` and `OddCoverAcyclicRange` altogether (`Work.Serre.SerreStableExact` supplies the first
input, and the rational Hurewicz chapter does the rest). -/
theorem stableStemsTorsion_of_serre3 (h : Work.Serre.SerreExactRangeCorrected)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic3) : Work.Drive.StableStemsTorsion :=
  Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable3
    (Work.RatHurewicz.rationalHurewiczStable3_of_range3
      (Work.RatHurewicz.hurewiczModTorsionRange3_of_transfer3
        (Work.RatHurewicz.truncationHomologyTransfer3_of_serre h hem)))

/-- The same, with the Serre input instantiated by the tree's `Work.Serre.serreStableExact`
(whose own closure still contains `Work.Serre.serrePairComparison`): the only *open* input is then
the range-model vanishing `Work.RatHurewicz.RangeModelRatAcyclic3`. -/
theorem stableStemsTorsion_of_rangeAcyclic3 (hem : Work.RatHurewicz.RangeModelRatAcyclic3) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_serre3
    (Work.Serre.serreExactRangeCorrected_of_stableExact Work.Serre.serreStableExact) hem

/-- **The STEMS contract, from the two remaining inputs of the chain.**  This is the *sharpest*
recorded reduction: the `C2` layer of this area
(`Work.Stems.rangeModelRatAcyclic3_of_E3b_C3`, proved in `Submission/Work/Stems/c2FreeMain.lean`)
supplies the second input from

* `Work.Serre.SerreE3b` — the Gysin/periodicity statement of a rational spherical fibration in the
  range given by the fibre (area SERRE; its content is the Thom class of the disc-pair fibration,
  see `Work.Serre.EulerFibreRange`), and
* `Work.StemsB.C3FiniteTwo` — a range model of `K(A,k)`, `A` finite, is rationally acyclic (area
  SERRE, through `Work.Serre.serreC3FiniteOne`),

while the first input `Work.Serre.SerreExactRangeCorrected` is supplied by the *proved*
`Work.Serre.serreStableExact`.  So the STEMS contract is now reduced to those two SERRE-side
inputs, and nothing else. -/
theorem stableStemsTorsion_of_E3b_C3_K5 (hE3b : Work.Serre.SerreE3b)
    (hC3 : Work.StemsB.C3FiniteTwo) : Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_rangeAcyclic3 (Work.Stems.rangeModelRatAcyclic3_of_E3b_C3 hE3b hC3)

/-- **The STEMS contract from its two remaining inputs, in their final form.**

* `Work.Serre.SerreE3b` — the Gysin/periodicity statement for a rational spherical fibration in
  the range given by the *fibre* (area SERRE).  It is consumed exactly once, in the even step of
  the `C2` layer (`Work.Stems.c2evenFree_of_c2oddFree`), through the mutual induction
  `Work.Stems.c2evenFree_and_c2oddFree`.
* the `n = 1` case of C3 for *finite* coefficient groups, in the form of the statement
  `∀ A [Fintype A] …, IsEMSpace A 1 … → RatAcyclic` (`Work.Serre.serreC3FiniteOne`); it is consumed
  by `Work.StemsB.C3FiniteTwo_of_serreC3FiniteOne` (the proved loop induction, which needs only
  `n = 1` and no general-torsion statement).

Nothing else is missing: the K5 input is the proved `Work.StemsB.serreExactRangeCorrectedTwo`, the
range models are the proved `Work.Serre.serreC0Range`, and both `Work.Stems.c2oddFree_three`
(this area) and the transfer `Work.StemsB.rangeModelRatAcyclic_of_C2odd_C3` (area STEMS-B) are
axiom-clean.  When the two inputs above land, the target becomes the one-liner

  `stableStemsTorsion_of_E3b_C3one Work.Serre.serreE3b Work.Serre.serreC3FiniteOne`. -/
theorem stableStemsTorsion_of_E3b_C3one (hE3b : Work.Serre.SerreE3b)
    (hC3one : ∀ (A : Type) [AddCommGroup A] [Fintype A] (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpace A 1 (by norm_num : 0 < 1) X pt → Work.Serre.RatAcyclic X) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_rangeAcyclic3
    (Work.Stems.rangeModelRatAcyclic3_of_E3b_C3 hE3b
      (Work.StemsB.C3FiniteTwo_of_serreC3FiniteOne hC3one))

/-- **The STEMS contract from `SerreE3b` alone.**

This is the *sharpest* form now available: the other input of
`Work.Stems.stableStemsTorsion_of_E3b_C3one` is the *proved* theorem
`Work.Serre.serreC3FiniteOne` (C3 at `n = 1` for finite coefficient groups: a model of `K(A,1)`,
`A` finite abelian, is rationally acyclic), which the SERRE area completed.  So the STEMS contract
is equivalent to `Work.Serre.SerreE3b` modulo the (proved, axiom-clean) chain of this area and of
areas STEMS-B / SERRE / RATHUREWICZ. -/
theorem stableStemsTorsion_of_E3b (hE3b : Work.Serre.SerreE3b) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_E3b_C3one hE3b Work.Serre.serreC3FiniteOne

/-- **The STEMS contract from the *single* remaining open statement of the project's E3(b) node**:
the cellular step `Work.Serre.ThomCylCellStepAlt` of the CW-model Thom case
(`Submission/Work/Serre/thomCylCellStepAlt.lean`), in the equivalent form
`Work.Serre.e3bR_CellStepProp` (`Submission/Work/RatHurewicz/E3bBridge/EulerFibreRangeR.lean`, the
RATHUREWICZ island, which is import-compatible with this area's chain — see the note below).

The statement is taken as an explicit *hypothesis*, so this theorem is `sorry`-free and
axiom-clean, and the two long chains below it — RATHUREWICZ'/SERRE's
`Work.RatHurewicz.serreE3b_of_cellStep` and this area's `stableStemsTorsion_of_E3b` — are proved.

**Note (import islands — RESOLVED, H5 2026-09-27).**  `Submission.Work.Serre.serreE3b` **can now
be imported on this area's island**: the `isZero_dual_of_isZero` / `isZero_ratCoh_of_isZero_ratH` /
`isZero_ratH_of_conn` duplicates of `Submission.Work.Serre.gysinCupIsoReduction` were renamed to
`…_dup`, and the RATHUREWICZ clone `Submission/Work/RatHurewicz/E3bBridge/*R.lean` had its copies of
SERRE's E3(b) vocabulary renamed with the `e3bR_` prefix.  So *either* route works here, and both
are equivalent modulo the single open cellular step:

* `Work.Stems.stableStemsTorsion_of_E3b Work.Serre.serreE3b` (area SERRE's assembled node), or
* `Work.Stems.stableStemsTorsion_of_cellStep Work.Serre.thomCylCellStepAlt` (the E3(b) bridge
  `Work.RatHurewicz.serreE3b_of_cellStep`, `Submission/Work/RatHurewicz/E3bBridge/Assembly.lean`),
  which is what this theorem uses (both are `sorryAx`-backed until the crux lands). -/
theorem stableStemsTorsion_of_cellStep (h : Work.Serre.e3bR_CellStepProp) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_E3b (Work.RatHurewicz.serreE3b_of_cellStep h)

/-- **The STEMS contract** (`Work.Drive.StableStemsTorsion`, Milnor's exotic sphere, area STEMS).

**LANDING ROUTES — verified 2026-09-27.**  The area's whole chain reduces this to the single
cellular step `Work.Serre.ThomCylCellStepAlt`, so the `sorry` below is to be replaced by *one* of
the following (each of the four terms has been proved to elaborate, in the scratch files named):

* `Work.Stems.stableStemsTorsion_of_cellStep Work.Serre.thomCylCellStepAlt`
  (area SERRE's cellular step; import `Submission.Work.Serre.thomCylCellStepAlt`;
  test `Submission/Work/Stems/_s18/t_crux.lean`);
* `Work.Stems.stableStemsTorsion_of_cellStep Work.RatHurewicz.thomCylCellStepFreeProof`
  (area RATHUREWICZ's independent proof of the same statement; import
  `Submission.Work.RatHurewicz.gysinRangeFree`; test `Submission/Work/Stems/_s19/t_rath.lean`);
* `Work.Stems.stableStemsTorsion_of_cellStep Work.Stems.thomCylCellStepRace`
  (area H5's race child; import `Submission.Work.Stems.thomCylCellStepRace`;
  test `Submission/Work/Stems/_s19/t_child.lean`);
* `Work.Stems.stableStemsTorsion_of_E3b Work.Serre.serreE3b`
  (area SERRE's assembled E3(b) node; import `Submission.Work.Serre.serreE3b`;
  test `Submission/Work/Stems/_s19/clashAM2.lean`);
* `Work.Stems.stableStemsTorsion_of_cellStep Work.Serre.DiscPair.thomCylCellStepIndependent`
  (area SERRE's *independent* (collapse-map) route, same statement; import
  `Submission.Work.Serre.DiscPair.thomCylCellStepIndependent`;
  test `Submission/Work/Stems/_s19/t_ind.lean`).

**Two further landings, through the *strict-range* route (added 2026-09-27).**  The bridges live in
`Submission/Work/Stems/strictLanding.lean` (axiom-clean, re-verified), so any *producer* of the
strict-range nodes lands this file as well:

* `Work.Stems.stableStemsTorsion_of_thomCylStrict` :
  `Work.Serre.ThomIsoCylFibreRangeStrict → Work.Drive.StableStemsTorsion`
  (via `Work.Serre.serreE3bStrict_of_thomCylStrict` and the chain below);
* `Work.Stems.stableStemsTorsion_of_E3bStrict` :
  `Work.StemsB.SerreE3bStrict → Work.Drive.StableStemsTorsion`
  (`Work.Stems.rh3_of_e3bStrict` = the strict analogue of `Work.Drive.rh3_of_e3b`, then
  `Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable3`).

The strict statement is *one degree easier* than the cellular step (range `m + r + 1 ≤ N` instead of
`≤ N + 1`), and the relevant producer `Work.Serre.thomIsoCylFibreRangeStrict` is the node area SERRE
is building with the enhanced predicate `Work.Serre.ThomCylAtStrong`
(`StrongCWModelDefs.lean`, `ThomCylStrictStrongDefs.lean`).  `Submission/Work/Stems/_s20/land3.py`
checks all seven sites by axiom footprint.

A sixth site is `Work.RatHurewicz.serreE3b_of_cellStep` instantiated at any of the above.  All five
terms were checked to elaborate on 2026-09-27; all five were still `sorryAx`-backed at that time.

`Submission/Work/Stems/_s19/land.py` detects a landing and applies the edit (`--apply`); it decides
by `#print axioms` (a `sorry`-free *text* is not enough — see the notes file for two measured traps),
so it lands only on a `sorry`-free, axiom-clean term. -/
theorem stableStemsTorsion : Work.Drive.StableStemsTorsion :=
  Work.Stems.stableStemsTorsion_of_cellStep Work.Stems.thomCylCellStepRace

end Work.Stems
