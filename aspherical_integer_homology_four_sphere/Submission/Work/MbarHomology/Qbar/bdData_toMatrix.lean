/-
# The abstract boundary matrix `bdData` computes the geometric differential

This file proves `bdData_toMatrix`: for every cell `e` of `Q̄`, every degree `k` and all
indices `i`, `j`, the `(i,j)`-entry of the abstract boundary matrix `bdData e k` (built from the
data tables `qFacet`/`qInc` in `QbarCxEnum.lean`) is the value of the geometric cellular
differential `QbarCW.cellD` on the corresponding basis vector:

`(QbarCW.cellD k (Finsupp.single (cellTop e (k+1) j) 1)) (cellTop e k i) = (bdData e k).toMatrix i j`.

## Structure of the proof

* `PolyCW.cellD_apply_single` (`CellDApply.lean`) evaluates the geometric differential on a
  basis vector: the value at `f` is `QbarCW.inc g f` if `f` is a facet of `g`, and `0`
  otherwise.
* `qFacet_isFacet` (below) is the *soundness* of the facet table: every index listed in
  `qFacet x` is a genuine facet of the cell `x` (`⟨y⟩ ∈ QbarCW.facets ⟨x⟩`).  It is proved
  from the kernel-checked finite verification `qFacet_facet_data` (one `decide` over the
  `865` rows of the table) via `PolyCW.mem_facets`.
* `bdData_toMatrix_apply` unfolds the sparse data `bdData e k` — whose `j`-th column is a
  `filterMap` over `List.finRange` of the non-zero entries `(i, bdEntry e k i j)` — using the
  generic `SVec.toFun_filterMap_finRange`.

Only *soundness* of the facet table is needed, and not completeness: on the entries where
`(dimListLe e k).get i ∉ qFacet ((dimListLe e (k+1)).get j)`, the incidence number
`QbarCW.inc = qInc` vanishes by definition of `qInc`, so both sides of the identity are `0`.

The tables `qFacet`, `qInc` and `bdData` are the literal data on `Fin 865`, so the whole
identity after the reduction above is a statement about them; the geometric objects
(`cellD`, `Finsupp.single`) occur only through `PolyCW.cellD_apply_single`.

`QbarCW.Cell` is definitionally `QbarCell`, but the projection `QbarCW.facets` is elaborated
with argument type `QbarCW.Cell`; the two declarations mentioning it are therefore proved
under `backward.isDefEq.respectTransparency false` (as in `QbarCW_hasAugZero.lean`), which is
the legacy transparency behaviour that identifies the two.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCxEnum
import Submission.Work.MbarHomology.Qbar.CellDApply
import Submission.Work.Certificates.SVec.toFun_filterMap_finRange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology.Qbar

open Work.Subdivision Work.Certificates

/-- **Soundness of the facet table of `Q̄`** (one `decide` over the `865` rows): every index
listed among the facets of `x` is a cell of one dimension less that is a proper face of `x`,
i.e. an honest facet of `x`.

This is stated in the cheap `Finset.filter = ∅` form so that the kernel only inspects the few
indices that are actually listed in `qFacet x`. -/
theorem qFacet_facet_data_c0 : ∀ x : Fin 865, 0 ≤ x.val → x.val < 220 →  (qFacet x).filter
    (fun y => ¬ ((⟨y⟩ : QbarCell) < (⟨x⟩ : QbarCell) ∧
      QbarCW.dim (⟨x⟩ : QbarCell) = QbarCW.dim (⟨y⟩ : QbarCell) + 1)) = ∅ := by decide +kernel
theorem qFacet_facet_data_c1 : ∀ x : Fin 865, 220 ≤ x.val → x.val < 440 →  (qFacet x).filter
    (fun y => ¬ ((⟨y⟩ : QbarCell) < (⟨x⟩ : QbarCell) ∧
      QbarCW.dim (⟨x⟩ : QbarCell) = QbarCW.dim (⟨y⟩ : QbarCell) + 1)) = ∅ := by decide +kernel
theorem qFacet_facet_data_c2 : ∀ x : Fin 865, 440 ≤ x.val → x.val < 660 →  (qFacet x).filter
    (fun y => ¬ ((⟨y⟩ : QbarCell) < (⟨x⟩ : QbarCell) ∧
      QbarCW.dim (⟨x⟩ : QbarCell) = QbarCW.dim (⟨y⟩ : QbarCell) + 1)) = ∅ := by decide +kernel
theorem qFacet_facet_data_c3 : ∀ x : Fin 865, 660 ≤ x.val →  (qFacet x).filter
    (fun y => ¬ ((⟨y⟩ : QbarCell) < (⟨x⟩ : QbarCell) ∧
      QbarCW.dim (⟨x⟩ : QbarCell) = QbarCW.dim (⟨y⟩ : QbarCell) + 1)) = ∅ := by decide +kernel
theorem qFacet_facet_data : ∀ x : Fin 865, (qFacet x).filter
    (fun y => ¬ ((⟨y⟩ : QbarCell) < (⟨x⟩ : QbarCell) ∧
      QbarCW.dim (⟨x⟩ : QbarCell) = QbarCW.dim (⟨y⟩ : QbarCell) + 1)) = ∅ := by
  intro x
  by_cases h0 : x.val < 220
  · exact qFacet_facet_data_c0 x (by omega) h0
  by_cases h1 : x.val < 440
  · exact qFacet_facet_data_c1 x (by omega) h1
  by_cases h2 : x.val < 660
  · exact qFacet_facet_data_c2 x (by omega) h2
  exact qFacet_facet_data_c3 x (by omega)

/-- The `j`-th column of `bdData e k` represents the function `i ↦ bdEntry e k i j`, hence the
`(i,j)`-entry of the abstract boundary matrix is `bdEntry e k i j`. -/
theorem bdData_toMatrix_apply (e : Fin 865) (k : ℕ) (i : Fin (dimListLe e k).length)
    (j : Fin (dimListLe e (k+1)).length) :
    (bdData e k).toMatrix i j = bdEntry e k i j :=
  congrFun (SVec.toFun_filterMap_finRange (dimListLe e k).length (fun i => bdEntry e k i j)) i

section

-- `QbarCW.Cell` is definitionally `QbarCell`, but the projection `QbarCW.facets` is elaborated
-- with argument type `QbarCW.Cell`; the legacy transparency behaviour lets `rw`/`exact` identify
-- the two (as in `QbarCW_hasAugZero.lean`).
set_option backward.isDefEq.respectTransparency false

/-- Every index listed in `qFacet x` is a facet of the cell `x`. -/
theorem qFacet_isFacet (x y : Fin 865) (hy : y ∈ qFacet x) :
    (⟨y⟩ : QbarCell) ∈ QbarCW.facets (⟨x⟩ : QbarCell) := by
  rw [PolyCW.mem_facets]
  exact not_not.mp ((Finset.filter_eq_empty_iff.mp (qFacet_facet_data x)) hy)

/-- `PolyCW.cellD_apply_single` specialised to `QbarCW`, with the cell type written as
`QbarCell` (the statement of the generic lemma uses the projection `QbarCW.Cell`). -/
theorem qbar_cellD_apply_single (k : ℕ) (g : {e : QbarCell // QbarCW.dim e = k + 1})
    (f : {e : QbarCell // QbarCW.dim e = k}) :
    (QbarCW.cellD k (Finsupp.single g 1)) f =
      if (f.1 : QbarCell) ∈ QbarCW.facets (g.1 : QbarCell) then QbarCW.inc g.1 f.1 else 0 :=
  PolyCW.cellD_apply_single QbarCW k g f

/-- **The abstract boundary matrix computes the geometric differential.** -/
theorem bdData_toMatrix (e : Fin 865) (k : ℕ) (i : Fin (dimListLe e k).length)
    (j : Fin (dimListLe e (k+1)).length) :
    (QbarCW.cellD k (Finsupp.single (cellTop e (k+1) j) 1)) (cellTop e k i) =
      (bdData e k).toMatrix i j := by
  rw [qbar_cellD_apply_single, bdData_toMatrix_apply]
  unfold bdEntry
  simp only [cellTop_val]
  rw [QbarCW_inc]
  by_cases h : (dimListLe e k).get i ∈ qFacet ((dimListLe e (k+1)).get j)
  · rw [ite_eq_left h,
      ite_eq_left (qFacet_isFacet ((dimListLe e (k+1)).get j) ((dimListLe e k).get i) h)]
  · rw [ite_eq_right h, qInc, ite_eq_right h]
    by_cases h2 : (⟨(dimListLe e k).get i⟩ : QbarCell) ∈
        QbarCW.facets (⟨(dimListLe e (k+1)).get j⟩ : QbarCell)
    · rw [ite_eq_left h2]
    · rw [ite_eq_right h2]

end

end Work.MbarHomology.Qbar
