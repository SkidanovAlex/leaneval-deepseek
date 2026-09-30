/-
# The sign-change identities for `Q̄` at the sign change `e = 9`

One of the sixteen modules `qActChk00 … qActChk15` that split the finite verification of
`Work.MbarHomology.Qbar.qAct_spec`.  Each single `decide` runs over the `865` faces of `Q̄`
and the tables `qPos`, `qTight`, `qFacet`, `qIncRow`, `faceActT`, `consActT`, `oST` are long
`if`-chains, so the four identities of a single `e` are the most one module can hold under
the kernel memory cap.

This module handles `e = 9`: the four identities `qPos`, `qTight`, `qFacet` and `qInc`.
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

/-- The `pos` identity at `e = 9`. -/
theorem qAct_pos_09 : ∀ f : Fin 865,
    qPos (Work.MbarHomology.faceActT 9 f) = fun i => Work.MbarHomology.signVecT 9 i * qPos f i := by
  decide

/-- The `tight` identity at `e = 9`. -/
theorem qAct_tight_09 : ∀ f : Fin 865,
    qTight (Work.MbarHomology.faceActT 9 f) = (qTight f).image (Work.MbarHomology.consActT 9) := by
  decide

/-- The `facet` identity at `e = 9`. -/
theorem qAct_facet_09 : ∀ f : Fin 865,
    qFacet (Work.MbarHomology.faceActT 9 f) = (qFacet f).image (Work.MbarHomology.faceActT 9) := by
  decide

/-- The incidence identity at `e = 9`, in the computable `filter = ∅` form: no facet `f'` of a
face `f` violates the orientation-sign relation.  (`Finset.toList` is noncomputable and
`∀ f' : Fin 865, f' ∈ qFacet f → …` makes the kernel rebuild the `Fintype` instance for the
inner quantifier `865` times.) -/
theorem qAct_inc_09 : ∀ f : Fin 865, (qFacet f).filter (fun f' =>
    qInc (Work.MbarHomology.faceActT 9 f) (Work.MbarHomology.faceActT 9 f')
      ≠ Work.MbarHomology.oST 9 f * Work.MbarHomology.oST 9 f' * qInc f f') = ∅ := by
  decide

end Work.MbarHomology.Qbar
