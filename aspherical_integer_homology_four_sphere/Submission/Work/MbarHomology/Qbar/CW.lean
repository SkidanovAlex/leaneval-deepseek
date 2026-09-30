/-
# The face poset of `Q̄` as a `PolyCW`

**Work package W1** of `Submission/Work/NOTES_LEAD_eA.md`.

`QbarCW` is the face poset of the truncated 24-cell: its cells are the `865` faces of `Q̄`
(`QbarCell`), `f ≤ g` means that `f` is a face of `g` (`tight g ⊆ tight f`), the dimension is
`4 - #(tight f)` (every face of `Q̄` is the intersection of the facets that are tight on it, so
`Q̄` is simple), and the incidence number of a facet is rt_complex's orientation number
(`qInc`).

The face poset of a polytope is a *regular* polyhedral cell complex, so the whole subdivision
machinery of `Work.Subdivision` applies to `QbarCW`; this is what makes the closed cells
`cellLe QbarCW e` (spanned by at most `865` cells) small enough to certify by hand, and what
supplies the regular local models of the cell atlas for `M̄`.
-/
import Mathlib
import Submission.Work.Subdivision.Basic
import Submission.Work.Subdivision.CellChain
import Submission.Work.MbarHomology.Qbar.Basic
import Submission.Work.MbarHomology.Data.QbarFacet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology

open Work.ConvexCells
open Work.Subdivision

noncomputable section

/-- Every face of `Q̄` is tight at most four of the `48` constraints. -/
theorem qCard_le_c0 : ∀ f : Fin 865, 0 ≤ f.val → f.val < 220 →  (qTight f).card ≤ 4 := by decide +kernel
theorem qCard_le_c1 : ∀ f : Fin 865, 220 ≤ f.val → f.val < 440 →  (qTight f).card ≤ 4 := by decide +kernel
theorem qCard_le_c2 : ∀ f : Fin 865, 440 ≤ f.val → f.val < 660 →  (qTight f).card ≤ 4 := by decide +kernel
theorem qCard_le_c3 : ∀ f : Fin 865, 660 ≤ f.val →  (qTight f).card ≤ 4 := by decide +kernel
theorem qCard_le : ∀ f : Fin 865, (qTight f).card ≤ 4 := by
  intro f
  by_cases h0 : f.val < 220
  · exact qCard_le_c0 f (by omega) h0
  by_cases h1 : f.val < 440
  · exact qCard_le_c1 f (by omega) h1
  by_cases h2 : f.val < 660
  · exact qCard_le_c2 f (by omega) h2
  exact qCard_le_c3 f (by omega)

theorem qCard_le' (f : QbarCell) : (qTight f.idx).card ≤ 4 := qCard_le f.idx

/-- **The face poset of `Q̄` as a polyhedral CW complex.** -/
def QbarCW : PolyCW where
  Cell := QbarCell
  dim f := 4 - (qTight f.idx).card
  dim_le := by
    intro a b hab
    have h : (qTight b.idx).card ≤ (qTight a.idx).card := Finset.card_le_card hab
    show 4 - (qTight a.idx).card ≤ 4 - (qTight b.idx).card
    omega
  dim_lt := by
    intro a b hab hne
    have hsub : qTight b.idx ⊆ qTight a.idx := hab
    have hne' : qTight a.idx ≠ qTight b.idx := fun hc => hne (QbarCell.ext (qTight_inj hc))
    have hssub : qTight b.idx ⊂ qTight a.idx := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne'⟩
    have h : (qTight b.idx).card < (qTight a.idx).card := Finset.card_lt_card hssub
    have ha := qCard_le' a
    show 4 - (qTight a.idx).card < 4 - (qTight b.idx).card
    omega
  inc a b := qInc a.idx b.idx

@[simp] theorem QbarCW_dim (f : QbarCell) : QbarCW.dim f = 4 - (qTight f.idx).card := rfl
@[simp] theorem QbarCW_inc (a b : QbarCell) : QbarCW.inc a b = qInc a.idx b.idx := rfl

end

end Work.MbarHomology
