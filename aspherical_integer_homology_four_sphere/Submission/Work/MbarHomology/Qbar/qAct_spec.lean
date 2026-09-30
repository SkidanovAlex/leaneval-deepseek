import Mathlib
import Submission.Work.MbarHomology.Qbar.Act
import Submission.Work.MbarHomology.Qbar.qActChk00
import Submission.Work.MbarHomology.Qbar.qActChk01
import Submission.Work.MbarHomology.Qbar.qActChk02
import Submission.Work.MbarHomology.Qbar.qActChk03
import Submission.Work.MbarHomology.Qbar.qActChk04
import Submission.Work.MbarHomology.Qbar.qActChk05
import Submission.Work.MbarHomology.Qbar.qActChk06
import Submission.Work.MbarHomology.Qbar.qActChk07
import Submission.Work.MbarHomology.Qbar.qActChk08
import Submission.Work.MbarHomology.Qbar.qActChk09
import Submission.Work.MbarHomology.Qbar.qActChk10
import Submission.Work.MbarHomology.Qbar.qActChk11
import Submission.Work.MbarHomology.Qbar.qActChk12
import Submission.Work.MbarHomology.Qbar.qActChk13
import Submission.Work.MbarHomology.Qbar.qActChk14
import Submission.Work.MbarHomology.Qbar.qActChk15

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology.Qbar

open Work.MbarHomology

/-!
### The finite verification of the sign-change identities of `Q̄`

The four identities of `qAct_spec` are each a finite check over the `865` faces of `Q̄`
(and the `16` sign changes).  A single `decide` over the whole statement runs out of memory,
so the check is split into the sixteen modules `qActChk00 … qActChk15`, one per sign change
`e : Fin 16`, each carrying the four identities for that `e` (the largest amount of the check
that fits under the kernel memory cap).  This file reads those modules off and assembles the
statement; the case split on `e : Fin 16` is written out in order (`0, 1, …, 15`, the order in
which `Fin.cases` presents the constructors) so that each case is closed by exactly one `exact`.

The only point needing care is the incidence identity: it is recorded in each module in the
*computable* `filter = ∅` form

`(qFacet f).filter (fun f' => qInc (faceActT e f) (faceActT e f') ≠ oST e f * oST e f' * qInc f f') = ∅`

(`Finset.toList` is noncomputable, and the literal form `∀ f' : Fin 865, f' ∈ qFacet f → …`
makes the kernel rebuild the `Fintype` instance for the inner quantifier over `Fin 865` once
per face).  The conversion to the stated `∀ f f'` form is the `Finset.filter_eq_empty_iff`
rewriting below; it involves no table lookups.
-/

/-- The incidence identity at `e = 0`, read off from the `filter = ∅` form `qAct_inc_00`. -/
theorem qAct_inc_00' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 0 f) (Work.MbarHomology.faceActT 0 f')
      = Work.MbarHomology.oST 0 f * Work.MbarHomology.oST 0 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_00 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 1`, read off from the `filter = ∅` form `qAct_inc_01`. -/
theorem qAct_inc_01' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 1 f) (Work.MbarHomology.faceActT 1 f')
      = Work.MbarHomology.oST 1 f * Work.MbarHomology.oST 1 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_01 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 2`, read off from the `filter = ∅` form `qAct_inc_02`. -/
theorem qAct_inc_02' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 2 f) (Work.MbarHomology.faceActT 2 f')
      = Work.MbarHomology.oST 2 f * Work.MbarHomology.oST 2 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_02 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 3`, read off from the `filter = ∅` form `qAct_inc_03`. -/
theorem qAct_inc_03' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 3 f) (Work.MbarHomology.faceActT 3 f')
      = Work.MbarHomology.oST 3 f * Work.MbarHomology.oST 3 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_03 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 4`, read off from the `filter = ∅` form `qAct_inc_04`. -/
theorem qAct_inc_04' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 4 f) (Work.MbarHomology.faceActT 4 f')
      = Work.MbarHomology.oST 4 f * Work.MbarHomology.oST 4 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_04 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 5`, read off from the `filter = ∅` form `qAct_inc_05`. -/
theorem qAct_inc_05' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 5 f) (Work.MbarHomology.faceActT 5 f')
      = Work.MbarHomology.oST 5 f * Work.MbarHomology.oST 5 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_05 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 6`, read off from the `filter = ∅` form `qAct_inc_06`. -/
theorem qAct_inc_06' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 6 f) (Work.MbarHomology.faceActT 6 f')
      = Work.MbarHomology.oST 6 f * Work.MbarHomology.oST 6 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_06 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 7`, read off from the `filter = ∅` form `qAct_inc_07`. -/
theorem qAct_inc_07' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 7 f) (Work.MbarHomology.faceActT 7 f')
      = Work.MbarHomology.oST 7 f * Work.MbarHomology.oST 7 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_07 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 8`, read off from the `filter = ∅` form `qAct_inc_08`. -/
theorem qAct_inc_08' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 8 f) (Work.MbarHomology.faceActT 8 f')
      = Work.MbarHomology.oST 8 f * Work.MbarHomology.oST 8 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_08 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 9`, read off from the `filter = ∅` form `qAct_inc_09`. -/
theorem qAct_inc_09' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 9 f) (Work.MbarHomology.faceActT 9 f')
      = Work.MbarHomology.oST 9 f * Work.MbarHomology.oST 9 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_09 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 10`, read off from the `filter = ∅` form `qAct_inc_10`. -/
theorem qAct_inc_10' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 10 f) (Work.MbarHomology.faceActT 10 f')
      = Work.MbarHomology.oST 10 f * Work.MbarHomology.oST 10 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_10 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 11`, read off from the `filter = ∅` form `qAct_inc_11`. -/
theorem qAct_inc_11' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 11 f) (Work.MbarHomology.faceActT 11 f')
      = Work.MbarHomology.oST 11 f * Work.MbarHomology.oST 11 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_11 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 12`, read off from the `filter = ∅` form `qAct_inc_12`. -/
theorem qAct_inc_12' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 12 f) (Work.MbarHomology.faceActT 12 f')
      = Work.MbarHomology.oST 12 f * Work.MbarHomology.oST 12 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_12 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 13`, read off from the `filter = ∅` form `qAct_inc_13`. -/
theorem qAct_inc_13' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 13 f) (Work.MbarHomology.faceActT 13 f')
      = Work.MbarHomology.oST 13 f * Work.MbarHomology.oST 13 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_13 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 14`, read off from the `filter = ∅` form `qAct_inc_14`. -/
theorem qAct_inc_14' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 14 f) (Work.MbarHomology.faceActT 14 f')
      = Work.MbarHomology.oST 14 f * Work.MbarHomology.oST 14 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_14 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The incidence identity at `e = 15`, read off from the `filter = ∅` form `qAct_inc_15`. -/
theorem qAct_inc_15' : ∀ (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT 15 f) (Work.MbarHomology.faceActT 15 f')
      = Work.MbarHomology.oST 15 f * Work.MbarHomology.oST 15 f' * qInc f f' := by
  intro f f' hf'
  have h := (Finset.filter_eq_empty_iff.mp (qAct_inc_15 f)) hf'
  simpa only [ne_eq, not_not] using h

/-- The `pos` identity for all sign changes. -/
theorem qAct_spec_pos : ∀ (e : Fin 16) (f : Fin 865),
    qPos (Work.MbarHomology.faceActT e f)
      = fun i => Work.MbarHomology.signVecT e i * qPos f i := by
  intro e
  fin_cases e
  · exact qAct_pos_00
  · exact qAct_pos_01
  · exact qAct_pos_02
  · exact qAct_pos_03
  · exact qAct_pos_04
  · exact qAct_pos_05
  · exact qAct_pos_06
  · exact qAct_pos_07
  · exact qAct_pos_08
  · exact qAct_pos_09
  · exact qAct_pos_10
  · exact qAct_pos_11
  · exact qAct_pos_12
  · exact qAct_pos_13
  · exact qAct_pos_14
  · exact qAct_pos_15

/-- The `tight` identity for all sign changes. -/
theorem qAct_spec_tight : ∀ (e : Fin 16) (f : Fin 865),
    qTight (Work.MbarHomology.faceActT e f)
      = (qTight f).image (Work.MbarHomology.consActT e) := by
  intro e
  fin_cases e
  · exact qAct_tight_00
  · exact qAct_tight_01
  · exact qAct_tight_02
  · exact qAct_tight_03
  · exact qAct_tight_04
  · exact qAct_tight_05
  · exact qAct_tight_06
  · exact qAct_tight_07
  · exact qAct_tight_08
  · exact qAct_tight_09
  · exact qAct_tight_10
  · exact qAct_tight_11
  · exact qAct_tight_12
  · exact qAct_tight_13
  · exact qAct_tight_14
  · exact qAct_tight_15

/-- The `facet` identity for all sign changes. -/
theorem qAct_spec_facet : ∀ (e : Fin 16) (f : Fin 865),
    qFacet (Work.MbarHomology.faceActT e f)
      = (qFacet f).image (Work.MbarHomology.faceActT e) := by
  intro e
  fin_cases e
  · exact qAct_facet_00
  · exact qAct_facet_01
  · exact qAct_facet_02
  · exact qAct_facet_03
  · exact qAct_facet_04
  · exact qAct_facet_05
  · exact qAct_facet_06
  · exact qAct_facet_07
  · exact qAct_facet_08
  · exact qAct_facet_09
  · exact qAct_facet_10
  · exact qAct_facet_11
  · exact qAct_facet_12
  · exact qAct_facet_13
  · exact qAct_facet_14
  · exact qAct_facet_15

/-- The incidence identity for all sign changes. -/
theorem qAct_spec_inc : ∀ (e : Fin 16) (f f' : Fin 865), f' ∈ qFacet f →
    qInc (Work.MbarHomology.faceActT e f) (Work.MbarHomology.faceActT e f')
      = Work.MbarHomology.oST e f * Work.MbarHomology.oST e f' * qInc f f' := by
  intro e
  fin_cases e
  · exact qAct_inc_00'
  · exact qAct_inc_01'
  · exact qAct_inc_02'
  · exact qAct_inc_03'
  · exact qAct_inc_04'
  · exact qAct_inc_05'
  · exact qAct_inc_06'
  · exact qAct_inc_07'
  · exact qAct_inc_08'
  · exact qAct_inc_09'
  · exact qAct_inc_10'
  · exact qAct_inc_11'
  · exact qAct_inc_12'
  · exact qAct_inc_13'
  · exact qAct_inc_14'
  · exact qAct_inc_15'

/-- The four identities relating the sign-change action on `Q̄` to the generated tables: the
`pos` points, the tight sets, the facet table, and the incidence numbers (with the orientation
signs `oST`).  All four are re-verified in Python by
`Submission/Work/MbarHomology/scripts/gen_qbar_act.py` before the tables are emitted, over all
`16 × 865` faces.  A kernel-checked proof should split the finite check (per `e : Fin 16`, or per
face); a single `decide` over the whole statement runs out of memory. -/
theorem qAct_spec :
    (∀ (e : Fin 16) (f : Fin 865),
      qPos (Work.MbarHomology.faceActT e f)
        = fun i => Work.MbarHomology.signVecT e i * qPos f i) ∧
    (∀ (e : Fin 16) (f : Fin 865),
      qTight (Work.MbarHomology.faceActT e f)
        = (qTight f).image (Work.MbarHomology.consActT e)) ∧
    (∀ (e : Fin 16) (f : Fin 865),
      qFacet (Work.MbarHomology.faceActT e f)
        = (qFacet f).image (Work.MbarHomology.faceActT e)) ∧
    (∀ (e : Fin 16) (f f' : Fin 865), f' ∈ qFacet f →
      qInc (Work.MbarHomology.faceActT e f) (Work.MbarHomology.faceActT e f')
        = Work.MbarHomology.oST e f * Work.MbarHomology.oST e f' * qInc f f') :=
  ⟨qAct_spec_pos, qAct_spec_tight, qAct_spec_facet, qAct_spec_inc⟩

end Work.MbarHomology.Qbar
