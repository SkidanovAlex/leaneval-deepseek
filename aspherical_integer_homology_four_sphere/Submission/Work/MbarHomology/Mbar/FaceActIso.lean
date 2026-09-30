/-
# The sign-change action on the face poset of `Q̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`: the group of sign changes of the
24-cell acts on the faces of the truncated 24-cell `Q̄` (the table `faceAct`), hence on the cells
of `QbarCW` and on its face lattices.  The action is an order automorphism of the face poset
(`faceActCell_le_iff`), and `faceActIso g F : Set.Iic F ≃o Set.Iic (faceAct γ F)` is the induced
order isomorphism of the face lattice of a cell.

The order-theoretic input is the identity `qTight (faceAct g f) = (qTight f).image (consAct g)` of
`Work.MbarHomology.Qbar.qAct_spec_tight`: the order of the face poset is inclusion of tight sets.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.Act
import Submission.Work.MbarHomology.Qbar.qAct_spec

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology.Mbar

open Work.Subdivision

noncomputable section

/-- The tight set of a sign-changed face is the image of its tight set under `consAct`. -/
theorem qTight_faceAct (g : Fin 4 → ZMod 2) (f : Fin 865) :
    qTight (faceAct g f) = (qTight f).image (consAct g) :=
  Work.MbarHomology.Qbar.qAct_spec_tight (Work.FoldInst.enc g) f

/-- The constraint permutation is involutive. -/
theorem consAct_invol (g : Fin 4 → ZMod 2) (i : Fin 48) : consAct g (consAct g i) = i := by
  decide +revert

/-- The constraint permutation is injective. -/
theorem consAct_injective_q (g : Fin 4 → ZMod 2) : Function.Injective (consAct g) :=
  Function.LeftInverse.injective (fun i => consAct_invol g i)

/-- The constraint permutation respects the side indices. -/
theorem consAct_castAdd (g : Fin 4 → ZMod 2) (S : Fin 24) :
    consAct g (Fin.castAdd 24 S) = Fin.castAdd 24 (Work.FoldInst.sidePerm g S) := by
  decide +revert

/-- The sign change acting on a cell of `QbarCW`. -/
def faceActCell (g : Fin 4 → ZMod 2) (f : QbarCell) : QbarCell := ⟨faceAct g f.idx⟩

@[simp] theorem faceActCell_idx (g : Fin 4 → ZMod 2) (f : QbarCell) :
    (faceActCell g f).idx = faceAct g f.idx := rfl

/-- The order of the face poset, in terms of tight sets. -/
theorem qBarCell_lt_iff {a b : QbarCell} : a < b ↔ qTight b.idx ⊂ qTight a.idx := Iff.rfl

theorem QbarCell_le_iff {a b : QbarCell} : a ≤ b ↔ qTight b.idx ⊆ qTight a.idx := Iff.rfl

/-- The sign change is an order automorphism of the face poset of `Q̄`. -/
theorem faceActCell_lt {g : Fin 4 → ZMod 2} {a b : QbarCell} (h : a < b) :
    faceActCell g a < faceActCell g b := by
  have hsub : qTight b.idx ⊂ qTight a.idx := h
  rw [qBarCell_lt_iff]
  simp only [faceActCell_idx]
  rw [qTight_faceAct, qTight_faceAct]
  exact (Finset.image_ssubset_image (consAct_injective_q g)).mpr hsub

theorem faceActCell_le {g : Fin 4 → ZMod 2} {a b : QbarCell} (h : a ≤ b) :
    faceActCell g a ≤ faceActCell g b := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact le_of_lt (faceActCell_lt hlt)
  · rw [heq]

/-- The sign change on the cells is an involution. -/
theorem faceActCell_invol (g : Fin 4 → ZMod 2) (f : QbarCell) :
    faceActCell g (faceActCell g f) = f := by
  refine QbarCell.ext (qTight_inj ?_)
  show qTight (faceAct g (faceAct g f.idx)) = qTight f.idx
  rw [qTight_faceAct g (faceAct g f.idx), qTight_faceAct g f.idx, Finset.image_image]
  have hc : (consAct g ∘ consAct g) = id := funext fun x => consAct_invol g x
  rw [hc, Finset.image_id]

theorem faceActCell_le_iff {g : Fin 4 → ZMod 2} {a b : QbarCell} :
    faceActCell g a ≤ faceActCell g b ↔ a ≤ b := by
  constructor
  · intro h
    have h' : faceActCell g (faceActCell g a) ≤ faceActCell g (faceActCell g b) := faceActCell_le h
    rwa [faceActCell_invol, faceActCell_invol] at h'
  · exact faceActCell_le

/-- The dimension of a face is invariant under the sign change. -/
theorem QbarCW_dim_faceAct (g : Fin 4 → ZMod 2) (f : QbarCell) :
    QbarCW.dim (faceActCell g f) = QbarCW.dim f := by
  show 4 - (qTight (faceAct g f.idx)).card = 4 - (qTight f.idx).card
  rw [qTight_faceAct, Finset.card_image_of_injective _ (consAct_injective_q g)]

/-- **The order isomorphism of face lattices induced by a sign change.** -/
def faceActIso (g : Fin 4 → ZMod 2) (F : QbarCell) :
    Set.Iic F ≃o Set.Iic (faceActCell g F) where
  toFun f := ⟨faceActCell g f.1, faceActCell_le f.2⟩
  invFun f := ⟨faceActCell g f.1, by
    have h := faceActCell_le (g := g) f.2
    rwa [faceActCell_invol] at h⟩
  left_inv f := Subtype.ext (faceActCell_invol g f.1)
  right_inv f := Subtype.ext (faceActCell_invol g f.1)
  map_rel_iff' := by
    intro a b
    show faceActCell g a.1 ≤ faceActCell g b.1 ↔ a.1 ≤ b.1
    exact faceActCell_le_iff

@[simp] theorem faceActIso_apply (g : Fin 4 → ZMod 2) (F : QbarCell) (f : Set.Iic F) :
    ((faceActIso g F) f).1 = faceActCell g f.1 := rfl

@[simp] theorem faceActIso_top (g : Fin 4 → ZMod 2) (F : QbarCell) :
    ((faceActIso g F) ⟨F, Set.mem_Iic.mpr le_rfl⟩).1 = faceActCell g F := rfl

end

end Work.MbarHomology.Mbar
