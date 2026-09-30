import Mathlib
import Submission.Work.MbarHomology.Mbar.FaceActIso
import Submission.Work.Subdivision.starLM_subdivCell
import Submission.Work.MbarHomology.Qbar.qAct_spec

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option autoImplicit false
-- `QbarCW.Cell` is definitionally `QbarCell` but the two are not syntactically equal;
-- the legacy transparency behaviour lets `rw`/`exact` identify them.
set_option backward.isDefEq.respectTransparency false

namespace Work.Subdivision

namespace PolyCW

variable {P : PolyCW}

/-- Chains supported strictly below `e` are supported below `e`. -/
theorem belowSub_le_leSub (e : P.Cell) (k : ℕ) : belowSub P e k ≤ leSub P e k := by
  rw [belowSub_le_iff]
  intro σ hσ
  exact sdElem_mem_leSub P (fun i => le_of_lt (hσ i))

/-- The cone on a chain supported strictly below `e` is supported below `e`. -/
theorem coneLM_mem_leSub {e : P.Cell} {k : ℕ} {z : chainMod P.Cell k}
    (hz : z ∈ belowSub P e k) : coneLM P e k z ∈ leSub P e (k + 1) := by
  refine Submodule.span_induction (p := fun z _ => coneLM P e k z ∈ leSub P e (k + 1))
    ?_ ?_ ?_ ?_ hz
  · rintro y ⟨σ, hσ, rfl⟩
    rw [coneLM_single P e k σ hσ]
    exact sdElem_mem_leSub P (fun i => by
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Simplex.snoc_apply_castSucc]
        exact le_of_lt (hσ j)
      · rw [Simplex.snoc_apply_last])
  · simp
  · intro a b ha hb iha ihb
    rw [map_add]
    exact Submodule.add_mem _ iha ihb
  · intro c a ha iha
    rw [map_smul]
    exact Submodule.smul_mem _ _ iha

/-- **Agreement of `starLM` for order isomorphisms that agree on a face.** If the
order isomorphisms `φ`, `ψ` have the same underlying map on the faces `≤ x`, then
the induced maps on chains supported below `x` coincide. -/
theorem starLM_congr {e f e' f' : P.Cell}
    (φ : Set.Iic e ≃o Set.Iic f) (ψ : Set.Iic e' ≃o Set.Iic f')
    (x : P.Cell) (hxe : x ≤ e) (hxe' : x ≤ e')
    (hφψ : ∀ (y : P.Cell) (hy : y ≤ x),
      (φ ⟨y, le_trans hy hxe⟩).1 = (ψ ⟨y, le_trans hy hxe'⟩).1) :
    ∀ (k : ℕ) {z : chainMod P.Cell k}, z ∈ leSub P x k → starLM P φ k z = starLM P ψ k z := by
  intro k z hz
  refine Submodule.span_induction (p := fun z _ => starLM P φ k z = starLM P ψ k z) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨σ, hσ, rfl⟩
    rw [starLM_single P φ σ (fun i => le_trans (hσ i) hxe),
      starLM_single P ψ σ (fun i => le_trans (hσ i) hxe')]
    congr 1
    apply Simplex.ext
    intro i
    rw [Simplex.congrIic_apply, Simplex.congrIic_apply]
    exact hφψ (σ i) (hσ i)
  · simp
  · intro a b ha hb iha ihb
    rw [map_add, map_add, iha, ihb]
  · intro c a ha iha
    rw [map_smul, map_smul, iha]

end PolyCW

end Work.Subdivision

namespace Work.Mbar

open Work.MbarHomology
open Work.MbarHomology.Mbar

noncomputable section

/-! ### Elementary facts about the orientation signs -/

/-- The orientation sign of a sign change on a face is `±1`. -/
theorem oST_mul_self (e : Fin 16) (f : Fin 865) : oST e f * oST e f = 1 := by
  decide +revert

/-- The orientation sign of a sign change on a `0`-dimensional face is `1`. -/
theorem oST_eq_one_of_card (e : Fin 16) (f : Fin 865) (h : (qTight f).card = 4) :
    oST e f = 1 := by
  decide +revert

theorem oS_mul_self (g : Fin 4 → ZMod 2) (f : Fin 865) : oS g f * oS g f = 1 :=
  oST_mul_self (Work.FoldInst.enc g) f

theorem oS_eq_one_of_card (g : Fin 4 → ZMod 2) (f : Fin 865) (h : (qTight f).card = 4) :
    oS g f = 1 :=
  oST_eq_one_of_card (Work.FoldInst.enc g) f h

theorem oS_eq_one_of_dim_zero (g : Fin 4 → ZMod 2) (x : QbarCW.Cell) (h : QbarCW.dim x = 0) :
    oS g x.idx = 1 := by
  apply oS_eq_one_of_card
  have hc := qCard_le x.idx
  have h2 : QbarCW.dim x = 4 - (qTight x.idx).card := rfl
  omega

/-! ### The sign change on the facets -/

theorem faceActCell_injective (g : Fin 4 → ZMod 2) :
    Function.Injective (faceActCell g) := by
  intro a b h
  have h2 := congrArg (faceActCell g) h
  rw [faceActCell_invol, faceActCell_invol] at h2
  exact h2

theorem faceActT_injective (g : Fin 4 → ZMod 2) : Function.Injective (faceAct g) := by
  intro a b h
  have h2 : (⟨a⟩ : QbarCell) = ⟨b⟩ := faceActCell_injective g (QbarCell.ext h)
  exact congrArg QbarCell.idx h2

/-- The image of a facet is a facet of the image. -/
theorem mem_facets_faceActCell (g : Fin 4 → ZMod 2) {x y : QbarCW.Cell}
    (hy : y ∈ QbarCW.facets x) : faceActCell g y ∈ QbarCW.facets (faceActCell g x) := by
  have hy' : y < x ∧ QbarCW.dim x = QbarCW.dim y + 1 :=
    (Work.Subdivision.PolyCW.mem_facets (P := QbarCW) x y).mp hy
  refine (Work.Subdivision.PolyCW.mem_facets (P := QbarCW) (faceActCell g x) (faceActCell g y)).mpr
    ⟨faceActCell_lt hy'.1, ?_⟩
  rw [QbarCW_dim_faceAct, QbarCW_dim_faceAct]
  omega

/-- The image cell, as an element of the type of cells of the same dimension. -/
def imgSub (g : Fin 4 → ZMod 2) {k : ℕ}
    (x : {a : QbarCW.Cell // QbarCW.dim a = k}) : {a : QbarCW.Cell // QbarCW.dim a = k} :=
  ⟨faceActCell g x.1, by rw [QbarCW_dim_faceAct]; exact x.2⟩

@[simp] theorem imgSub_val (g : Fin 4 → ZMod 2) {k : ℕ}
    (x : {a : QbarCW.Cell // QbarCW.dim a = k}) : (imgSub g x).1 = faceActCell g x.1 := rfl

/-- The sign change on the facets of a face. -/
def faceActFacetsEquiv (g : Fin 4 → ZMod 2) (x : QbarCW.Cell) :
    {y : QbarCW.Cell // y ∈ QbarCW.facets x} ≃
      {z : QbarCW.Cell // z ∈ QbarCW.facets (faceActCell g x)} where
  toFun y := ⟨faceActCell g y.1, mem_facets_faceActCell g y.2⟩
  invFun z := ⟨faceActCell g z.1, by
    have h := mem_facets_faceActCell g z.2
    rwa [faceActCell_invol] at h⟩
  left_inv y := Subtype.ext (faceActCell_invol g y.1)
  right_inv z := Subtype.ext (faceActCell_invol g z.1)

/-- **The incidence numbers are twisted by the orientation signs.** -/
theorem inc_faceActCell (g : Fin 4 → ZMod 2) {x y : QbarCW.Cell} (hy : y ∈ QbarCW.facets x) :
    QbarCW.inc (faceActCell g x) (faceActCell g y) = oS g x.idx * oS g y.idx * QbarCW.inc x y := by
  show qInc (faceActT (Work.FoldInst.enc g) x.idx) (faceActT (Work.FoldInst.enc g) y.idx)
      = oST (Work.FoldInst.enc g) x.idx * oST (Work.FoldInst.enc g) y.idx * qInc x.idx y.idx
  by_cases hq : y.idx ∈ qFacet x.idx
  · exact Qbar.qAct_spec_inc (Work.FoldInst.enc g) x.idx y.idx hq
  · have hnot : faceActT (Work.FoldInst.enc g) y.idx
        ∉ qFacet (faceActT (Work.FoldInst.enc g) x.idx) := by
      intro hc
      rw [Qbar.qAct_spec_facet] at hc
      obtain ⟨z, hzq, hzy⟩ := Finset.mem_image.mp hc
      exact hq (by rw [← faceActT_injective g hzy]; exact hzq)
    have hz : qInc x.idx y.idx = 0 := by simp [qInc, hq]
    have hz' : qInc (faceActT (Work.FoldInst.enc g) x.idx)
        (faceActT (Work.FoldInst.enc g) y.idx) = 0 := by simp [qInc, hnot]
    rw [hz, hz', mul_zero]

end

end Work.Mbar

namespace Work.Mbar

open Work.MbarHomology
open Work.MbarHomology.Mbar

noncomputable section


/-! ### The signed subdivided boundary -/

/-- **The signed subdivided boundary is natural**: the vertexwise image of the
subdivided boundary of `x` is `oS g x` times the subdivided boundary of the image
of `x`. -/
theorem starLM_facetsSum_signed (g : Fin 4 → ZMod 2) (F : QbarCW.Cell) (m : ℕ)
    (x : {a : QbarCW.Cell // QbarCW.dim a = m + 1}) (hxF : x.1 ≤ F)
    (ih : ∀ (y : {a : QbarCW.Cell // QbarCW.dim a = m}), y.1 ≤ F →
      Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g F) m
          (Work.Subdivision.PolyCW.subdivCell QbarCW m y)
        = oS g y.1.idx • Work.Subdivision.PolyCW.subdivCell QbarCW m (imgSub g y)) :
    Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g F) m
        (∑ y ∈ (QbarCW.facets x.1).attach, QbarCW.inc x.1 y.1 •
          Work.Subdivision.PolyCW.subdivCell QbarCW m
            (Work.Subdivision.PolyCW.facetIndex m x.1 x.2 y))
      = oS g x.1.idx •
          (∑ z ∈ (QbarCW.facets (imgSub g x).1).attach, QbarCW.inc (imgSub g x).1 z.1 •
            Work.Subdivision.PolyCW.subdivCell QbarCW m
              (Work.Subdivision.PolyCW.facetIndex m (imgSub g x).1 (imgSub g x).2 z)) := by
  rw [map_sum]
  have hterm : ∀ y : {y // y ∈ QbarCW.facets x.1},
      Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g F) m
          (QbarCW.inc x.1 y.1 • Work.Subdivision.PolyCW.subdivCell QbarCW m
            (Work.Subdivision.PolyCW.facetIndex m x.1 x.2 y))
        = (QbarCW.inc x.1 y.1 * oS g y.1.idx) •
            Work.Subdivision.PolyCW.subdivCell QbarCW m
              (Work.Subdivision.PolyCW.facetIndex m (imgSub g x).1 (imgSub g x).2
                ⟨faceActCell g y.1, mem_facets_faceActCell g y.2⟩) := by
    intro y
    have hyF : (Work.Subdivision.PolyCW.facetIndex m x.1 x.2 y).1 ≤ F :=
      le_of_lt (lt_of_lt_of_le (Work.Subdivision.PolyCW.facet_lt (P := QbarCW) y.2) hxF)
    rw [map_smul, ih (Work.Subdivision.PolyCW.facetIndex (P := QbarCW) m x.1 x.2 y) hyF, ← mul_smul]
    exact congrArg (fun w => (QbarCW.inc x.1 y.1 * oS g y.1.idx) • w)
      (Work.Subdivision.PolyCW.subdivCell_heq_subtype (P := QbarCW)
        (a := imgSub g (Work.Subdivision.PolyCW.facetIndex m x.1 x.2 y))
        (b := Work.Subdivision.PolyCW.facetIndex m (imgSub g x).1 (imgSub g x).2
                ⟨faceActCell g y.1, mem_facets_faceActCell g y.2⟩) rfl)
  rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.smul_sum]
  refine Finset.sum_bij (fun y _ => ⟨faceActCell g y.1, mem_facets_faceActCell g y.2⟩)
    (fun y _ => Finset.mem_attach _ _) ?_ ?_ ?_
  · intro a₁ _ a₂ _ h
    exact Subtype.ext (faceActCell_injective g (congrArg Subtype.val h))
  · intro b _
    refine ⟨⟨faceActCell g b.1, ?_⟩, Finset.mem_attach _ _, ?_⟩
    · have h := mem_facets_faceActCell g b.2
      simp only [imgSub_val, faceActCell_invol] at h
      exact h
    · exact Subtype.ext (faceActCell_invol g b.1)
  · intro y _
    have hc : QbarCW.inc x.1 y.1 * oS g y.1.idx =
        oS g x.1.idx * QbarCW.inc (faceActCell g x.1) (faceActCell g y.1) := by
      rw [inc_faceActCell g y.2]
      have hs := oS_mul_self g x.1.idx
      calc QbarCW.inc x.1 y.1 * oS g y.1.idx
          = (oS g x.1.idx * oS g x.1.idx) * (QbarCW.inc x.1 y.1 * oS g y.1.idx) := by
            rw [hs, one_mul]
        _ = oS g x.1.idx * (oS g x.1.idx * oS g y.1.idx * QbarCW.inc x.1 y.1) := by ring
    rw [hc, mul_smul]
    simp only [imgSub_val]

/-! ### The signed naturality, by strong induction on the dimension -/

/-- **The signed naturality of the subdivision chain** for the faces of `F`, by
strong induction on the dimension. -/
theorem starLM_subdivCell_signed_aux (g : Fin 4 → ZMod 2) (F : QbarCW.Cell) :
    ∀ (k : ℕ) (x : {a : QbarCW.Cell // QbarCW.dim a = k}), x.1 ≤ F →
      Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g F) k
          (Work.Subdivision.PolyCW.subdivCell QbarCW k x)
        = oS g x.1.idx • Work.Subdivision.PolyCW.subdivCell QbarCW k (imgSub g x) := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih x hxF
  rcases k with _ | m
  · rw [Work.Subdivision.PolyCW.subdivCell_zero QbarCW x,
      Work.Subdivision.PolyCW.subdivCell_zero QbarCW (imgSub g x),
      Work.Subdivision.PolyCW.starLM_single QbarCW (faceActIso g F)
        (Work.Subdivision.Simplex.vertex x.1) (fun _ => hxF)]
    have hv : Work.Subdivision.PolyCW.Simplex.congrIic QbarCW (faceActIso g F)
          (Work.Subdivision.Simplex.vertex x.1) (fun _ => hxF)
        = Work.Subdivision.Simplex.vertex (imgSub g x).1 := by
      apply Work.Subdivision.Simplex.ext
      intro i
      simp only [Work.Subdivision.PolyCW.Simplex.congrIic_apply,
        Work.Subdivision.Simplex.vertex_apply]
      rfl
    rw [hv, oS_eq_one_of_dim_zero g x.1 x.2, one_smul]
  · rw [Work.Subdivision.PolyCW.subdivCell_succ_eq (P := QbarCW) m x, map_smul]
    set zsum : Work.Subdivision.chainMod QbarCW.Cell m :=
      ∑ y ∈ (QbarCW.facets x.1).attach, QbarCW.inc x.1 y.1 •
        Work.Subdivision.PolyCW.subdivCell QbarCW m
          (Work.Subdivision.PolyCW.facetIndex m x.1 x.2 y) with hzsum
    have hzx : zsum ∈ QbarCW.belowSub x.1 m := by
      rw [hzsum]
      exact Work.Subdivision.PolyCW.facetsSum_mem_belowSub (P := QbarCW) m x.1 x.2
    have hzle : zsum ∈ QbarCW.leSub x.1 m :=
      Work.Subdivision.PolyCW.belowSub_le_leSub (P := QbarCW) x.1 m hzx
    have h1 : Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g F) (m + 1)
        (Work.Subdivision.PolyCW.coneLM QbarCW x.1 m zsum)
        = Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g x.1) (m + 1)
            (Work.Subdivision.PolyCW.coneLM QbarCW x.1 m zsum) :=
      Work.Subdivision.PolyCW.starLM_congr (P := QbarCW) (faceActIso g F) (faceActIso g x.1)
        x.1 hxF le_rfl (fun y _ => rfl) (m + 1) (Work.Subdivision.PolyCW.coneLM_mem_leSub (P := QbarCW) hzx)
    have h2 : Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g x.1) (m + 1)
        (Work.Subdivision.PolyCW.coneLM QbarCW x.1 m zsum)
        = Work.Subdivision.PolyCW.coneLM QbarCW (faceActCell g x.1) m
            (Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g x.1) m zsum) :=
      Work.Subdivision.PolyCW.starLM_coneLM QbarCW (faceActIso g x.1) rfl m zsum hzx
    have h3 : Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g x.1) m zsum
        = Work.Subdivision.PolyCW.starLM QbarCW (faceActIso g F) m zsum :=
      (Work.Subdivision.PolyCW.starLM_congr (P := QbarCW) (faceActIso g F) (faceActIso g x.1)
        x.1 hxF le_rfl (fun y _ => rfl) m hzle).symm
    rw [h1, h2, h3]
    have hfacets := starLM_facetsSum_signed g F m x hxF
      (fun y hyF => ih m (by omega) y hyF)
    rw [hfacets, map_smul, Work.Subdivision.PolyCW.subdivCell_succ_eq (P := QbarCW) m (imgSub g x),
      smul_comm]
    simp only [imgSub_val]

/-- **The signed star action of a sign change on the subdivision chain of a face of `Q̄`.**

`faceActIso g F : Set.Iic F ≃o Set.Iic (faceActCell g F)` is the order isomorphism of face lattices
induced by the sign change `g` (`Submission/Work/MbarHomology/Mbar/FaceActIso.lean`), and `starLM`
is the induced vertexwise map on the chains of the order complex.  The subdivision chain
`subdivCell` is natural with respect to an isomorphism of *local structures* (`starLM_subdivCell`),
but the sign change only preserves the incidence numbers up to the orientation signs `oS`
(`qAct_spec_inc`); the correct statement is therefore the *signed* one below: the vertexwise image
of the subdivision chain of `F` is `oS g F` times the subdivision chain of the image face.

The proof should follow the strong induction of `PolyCW.starLM_subdivCell_aux`: the cone step is
`starLM_coneLM`, the facets of `faceActCell g F` are the images of the facets of `F`
(`faceActCell_le_iff`), the incidence numbers are twisted by `oS` (`qAct_spec_inc`), and the base
case uses `oS g f = 1` on the vertices (`0`-dimensional faces). -/
theorem starLM_subdivCell_signed (g : Fin 4 → ZMod 2) (n : ℕ)
    (F : {e : Work.MbarHomology.QbarCell // Work.MbarHomology.QbarCW.dim e = n}) :
    Work.Subdivision.PolyCW.starLM Work.MbarHomology.QbarCW
        (Work.MbarHomology.Mbar.faceActIso g F.1) n
        (Work.Subdivision.PolyCW.subdivCell Work.MbarHomology.QbarCW n F)
      = Work.MbarHomology.oS g F.1.idx •
        Work.Subdivision.PolyCW.subdivCell Work.MbarHomology.QbarCW n
          ⟨Work.MbarHomology.Mbar.faceActCell g F.1,
            by rw [Work.MbarHomology.Mbar.QbarCW_dim_faceAct]; exact F.2⟩ :=
  starLM_subdivCell_signed_aux g F.1 n F le_rfl

end

end Work.Mbar
