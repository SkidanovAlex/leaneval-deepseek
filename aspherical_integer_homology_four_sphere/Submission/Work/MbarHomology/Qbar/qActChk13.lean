/-
# The sign-change identities for `Q̄` at the sign change `e = 13`

One of the sixteen modules `qActChk00 … qActChk15` that split the finite verification of
`Work.MbarHomology.Qbar.qAct_spec`.  Each single `decide` runs over the `865` faces of `Q̄`
and the tables `qPos`, `qTight`, `qFacet`, `qIncRow`, `faceActT`, `consActT`, `oST` are long
`if`-chains, so the four identities of a single `e` are the most one module can hold under
the kernel memory cap.

This module handles `e = 13`: the four identities `qPos`, `qTight`, `qFacet` and `qInc`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.Act

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Work.MbarHomology.Qbar

open Work.MbarHomology

/-- The `pos` identity at `e = 13`. -/
theorem qAct_pos_13_c0 : ∀ f : Fin 865, 0 ≤ f.val → f.val < 220 → 
    qPos (Work.MbarHomology.faceActT 13 f) = fun i => Work.MbarHomology.signVecT 13 i * qPos f i := by decide +kernel
theorem qAct_pos_13_c1 : ∀ f : Fin 865, 220 ≤ f.val → f.val < 440 → 
    qPos (Work.MbarHomology.faceActT 13 f) = fun i => Work.MbarHomology.signVecT 13 i * qPos f i := by decide +kernel
theorem qAct_pos_13_c2 : ∀ f : Fin 865, 440 ≤ f.val → f.val < 660 → 
    qPos (Work.MbarHomology.faceActT 13 f) = fun i => Work.MbarHomology.signVecT 13 i * qPos f i := by decide +kernel
theorem qAct_pos_13_c3 : ∀ f : Fin 865, 660 ≤ f.val → 
    qPos (Work.MbarHomology.faceActT 13 f) = fun i => Work.MbarHomology.signVecT 13 i * qPos f i := by decide +kernel
theorem qAct_pos_13 : ∀ f : Fin 865,
    qPos (Work.MbarHomology.faceActT 13 f) = fun i => Work.MbarHomology.signVecT 13 i * qPos f i := by
  intro f
  by_cases h0 : f.val < 220
  · exact qAct_pos_13_c0 f (by omega) h0
  by_cases h1 : f.val < 440
  · exact qAct_pos_13_c1 f (by omega) h1
  by_cases h2 : f.val < 660
  · exact qAct_pos_13_c2 f (by omega) h2
  exact qAct_pos_13_c3 f (by omega)

/-- The `tight` identity at `e = 13`. -/
theorem qAct_tight_13_c0 : ∀ f : Fin 865, 0 ≤ f.val → f.val < 220 → 
    qTight (Work.MbarHomology.faceActT 13 f) = (qTight f).image (Work.MbarHomology.consActT 13) := by decide +kernel
theorem qAct_tight_13_c1 : ∀ f : Fin 865, 220 ≤ f.val → f.val < 440 → 
    qTight (Work.MbarHomology.faceActT 13 f) = (qTight f).image (Work.MbarHomology.consActT 13) := by decide +kernel
theorem qAct_tight_13_c2 : ∀ f : Fin 865, 440 ≤ f.val → f.val < 660 → 
    qTight (Work.MbarHomology.faceActT 13 f) = (qTight f).image (Work.MbarHomology.consActT 13) := by decide +kernel
theorem qAct_tight_13_c3 : ∀ f : Fin 865, 660 ≤ f.val → 
    qTight (Work.MbarHomology.faceActT 13 f) = (qTight f).image (Work.MbarHomology.consActT 13) := by decide +kernel
theorem qAct_tight_13 : ∀ f : Fin 865,
    qTight (Work.MbarHomology.faceActT 13 f) = (qTight f).image (Work.MbarHomology.consActT 13) := by
  intro f
  by_cases h0 : f.val < 220
  · exact qAct_tight_13_c0 f (by omega) h0
  by_cases h1 : f.val < 440
  · exact qAct_tight_13_c1 f (by omega) h1
  by_cases h2 : f.val < 660
  · exact qAct_tight_13_c2 f (by omega) h2
  exact qAct_tight_13_c3 f (by omega)

/-- The `facet` identity at `e = 13`. -/
theorem qAct_facet_13_c0 : ∀ f : Fin 865, 0 ≤ f.val → f.val < 220 → 
    qFacet (Work.MbarHomology.faceActT 13 f) = (qFacet f).image (Work.MbarHomology.faceActT 13) := by decide +kernel
theorem qAct_facet_13_c1 : ∀ f : Fin 865, 220 ≤ f.val → f.val < 440 → 
    qFacet (Work.MbarHomology.faceActT 13 f) = (qFacet f).image (Work.MbarHomology.faceActT 13) := by decide +kernel
theorem qAct_facet_13_c2 : ∀ f : Fin 865, 440 ≤ f.val → f.val < 660 → 
    qFacet (Work.MbarHomology.faceActT 13 f) = (qFacet f).image (Work.MbarHomology.faceActT 13) := by decide +kernel
theorem qAct_facet_13_c3 : ∀ f : Fin 865, 660 ≤ f.val → 
    qFacet (Work.MbarHomology.faceActT 13 f) = (qFacet f).image (Work.MbarHomology.faceActT 13) := by decide +kernel
theorem qAct_facet_13 : ∀ f : Fin 865,
    qFacet (Work.MbarHomology.faceActT 13 f) = (qFacet f).image (Work.MbarHomology.faceActT 13) := by
  intro f
  by_cases h0 : f.val < 220
  · exact qAct_facet_13_c0 f (by omega) h0
  by_cases h1 : f.val < 440
  · exact qAct_facet_13_c1 f (by omega) h1
  by_cases h2 : f.val < 660
  · exact qAct_facet_13_c2 f (by omega) h2
  exact qAct_facet_13_c3 f (by omega)

/-- The incidence identity at `e = 13`, in the computable `filter = ∅` form: no facet `f'` of a
face `f` violates the orientation-sign relation.  (`Finset.toList` is noncomputable and
`∀ f' : Fin 865, f' ∈ qFacet f → …` makes the kernel rebuild the `Fintype` instance for the
inner quantifier `865` times.) -/
theorem qAct_inc_13_c0 : ∀ f : Fin 865, 0 ≤ f.val → f.val < 220 →  (qFacet f).filter (fun f' =>
    qInc (Work.MbarHomology.faceActT 13 f) (Work.MbarHomology.faceActT 13 f')
      ≠ Work.MbarHomology.oST 13 f * Work.MbarHomology.oST 13 f' * qInc f f') = ∅ := by decide +kernel
theorem qAct_inc_13_c1 : ∀ f : Fin 865, 220 ≤ f.val → f.val < 440 →  (qFacet f).filter (fun f' =>
    qInc (Work.MbarHomology.faceActT 13 f) (Work.MbarHomology.faceActT 13 f')
      ≠ Work.MbarHomology.oST 13 f * Work.MbarHomology.oST 13 f' * qInc f f') = ∅ := by decide +kernel
theorem qAct_inc_13_c2 : ∀ f : Fin 865, 440 ≤ f.val → f.val < 660 →  (qFacet f).filter (fun f' =>
    qInc (Work.MbarHomology.faceActT 13 f) (Work.MbarHomology.faceActT 13 f')
      ≠ Work.MbarHomology.oST 13 f * Work.MbarHomology.oST 13 f' * qInc f f') = ∅ := by decide +kernel
theorem qAct_inc_13_c3 : ∀ f : Fin 865, 660 ≤ f.val →  (qFacet f).filter (fun f' =>
    qInc (Work.MbarHomology.faceActT 13 f) (Work.MbarHomology.faceActT 13 f')
      ≠ Work.MbarHomology.oST 13 f * Work.MbarHomology.oST 13 f' * qInc f f') = ∅ := by decide +kernel
theorem qAct_inc_13 : ∀ f : Fin 865, (qFacet f).filter (fun f' =>
    qInc (Work.MbarHomology.faceActT 13 f) (Work.MbarHomology.faceActT 13 f')
      ≠ Work.MbarHomology.oST 13 f * Work.MbarHomology.oST 13 f' * qInc f f') = ∅ := by
  intro f
  by_cases h0 : f.val < 220
  · exact qAct_inc_13_c0 f (by omega) h0
  by_cases h1 : f.val < 440
  · exact qAct_inc_13_c1 f (by omega) h1
  by_cases h2 : f.val < 660
  · exact qAct_inc_13_c2 f (by omega) h2
  exact qAct_inc_13_c3 f (by omega)

end Work.MbarHomology.Qbar
