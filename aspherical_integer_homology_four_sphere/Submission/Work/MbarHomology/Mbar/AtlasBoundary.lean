/-
# The boundary compatibility of the cell atlas of `M̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`.

`mbarAtlasOf.BoundaryCompat` compares the boundary of the `482`-cell complex `Gen.mbarCx`
(`Gen.mbarBd`) with the boundary of the subdivision chains of `Q̄` read through the atlas.  This
file proves it by reducing both sides, in the free-module model `CellAtlas.kMod`, to the explicit
identity on the columns
`∑_{G ⋖ R} inc(R,G) · oS(c,G) = mbarBd · e`
checked in `MbarHomology/BdFiber/mbarBd_fiber.lean`.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasPush
import Submission.Work.MbarHomology.CellAtlas.Core
import Submission.Work.MbarHomology.CellAtlas.toChainComplex_d_single
import Submission.Work.MbarHomology.BdFiber.mbarBd_fiber
import Submission.Work.MbarHomology.Push.pushNode_comm_D
import Submission.Work.Subdivision.D_subdivCell
import Submission.Work.MbarHomology.Mbar.starLM_subdivCell_signed
import Submission.Work.MbarHomology.Qbar.QbarCW_hasDdZero
import Submission.Work.MbarHomology.Qbar.QbarCW_hasAugZero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option autoImplicit false
-- `QbarCW.Cell` is definitionally `QbarCell`, but the projections of `QbarCW` are elaborated
-- with argument type `QbarCW.Cell`; the legacy transparency behaviour lets `rw` identify them.
set_option backward.isDefEq.respectTransparency false

namespace Work.MbarHomology.Mbar

open Work.Subdivision Work.ConvexCells
open CategoryTheory
open scoped BigOperators

noncomputable section

attribute [local instance 2000] Pi.Function.module Finsupp.module
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

/-! ## 1. The transport of the boundary -/

/-- The boundary `kδCpt` of the free-module model is the image of `chainD` of `mbarSd`. -/
theorem kIso_chainD (k : ℕ) (y : mbarSd.chainX (k + 1)) :
    (CellAtlas.kIso mbarSd k).hom ((mbarSd.chainD k).hom y)
      = CellAtlas.kδCpt mbarSd k ((CellAtlas.kIso mbarSd (k + 1)).hom y) := by
  have h1 : (CellAtlas.kIso mbarSd (k + 1)).inv ((CellAtlas.kIso mbarSd (k + 1)).hom y) = y := by
    rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]
  rw [CellAtlas.kδCpt, ModuleCat.comp_apply, ModuleCat.comp_apply, h1]

/-- The value of the atlas map on the generators of `C`, in the free-module model. -/
theorem kIso_zMapFun (n : ℕ) (x : (Work.HomologyIso.Gen.mbarCx.toChainComplex).X n) :
    (CellAtlas.kIso mbarSd n).hom ((CellAtlas.zMapFun mbarAtlasOf n).hom x)
      = ∑ b : Fin (Work.HomologyIso.Gen.mbarDim n), x b • CellAtlas.kz mbarAtlasOf n b := by
  have hstep : (CellAtlas.zMapFun mbarAtlasOf n).hom x
      = ∑ b : Fin (Work.HomologyIso.Gen.mbarDim n), x b • CellAtlas.z mbarAtlasOf n b := by
    conv_lhs => rw [CellAtlas.cGen_expand Work.HomologyIso.Gen.mbarCx n x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul]
    rw [show (CellAtlas.zMapFun mbarAtlasOf n) (CellAtlas.cGen Work.HomologyIso.Gen.mbarCx n b)
        = CellAtlas.z mbarAtlasOf n b from CellAtlas.zMapFun_piSingle mbarAtlasOf n b]
  rw [hstep, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]
  rfl

/-! ## 2. The cell of a facet -/

/-- The `M̄`-cell of the facet `G` of the root face of a cell of dimension `n`, as an element of
`Fin (mbarDim n)`. -/
def facetCellIdx (c : ZMod 2) (n : ℕ) (G : Fin 865) (hG : QbarCW.dim (⟨G⟩ : QbarCell) = n) :
    Fin (Work.HomologyIso.Gen.mbarDim n) :=
  ⟨moPos (moCell c G), by
    rw [← hG, ← moDim_moCell]
    exact moPos_lt (moCell c G)⟩

/-- The cell of a facet of a face of `Q̄`: the index `facetCellIdx` of a facet node is the cell of
that node. -/
theorem moCid_facetCellIdx (c : ZMod 2) (n : ℕ) (hn : n < 5) (G : Fin 865)
    (hG : QbarCW.dim (⟨G⟩ : QbarCell) = n) :
    moCid ⟨n, hn⟩ (facetCellIdx c n G hG) = moCell c G := by
  interval_cases n <;> decide +revert

theorem facetCellIdx_eq_iff (c : ZMod 2) (n : ℕ) (hn : n < 5) (G : Fin 865)
    (hG : QbarCW.dim (⟨G⟩ : QbarCell) = n) (f : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    (moCell c G = moCid ⟨n, hn⟩ f) ↔ facetCellIdx c n G hG = f := by
  constructor
  · intro h
    have h2 : moPos (moCell c G) = (f : ℕ) := by
      rw [h, (moCid_spec ⟨n, hn⟩ f).2]
    exact Fin.ext h2
  · intro h
    rw [← h]
    exact (moCid_facetCellIdx c n hn G hG).symm

/-! ## 3. The facets of `Q̄` -/

/-- The facet table `qFacet` only lists facets. -/
theorem qFacet_facet_list (x : Fin 865) :
    (qFacet x).filter (fun G => ¬ ((⟨G⟩ : QbarCW.Cell) < (⟨x⟩ : QbarCW.Cell) ∧
      QbarCW.dim (⟨x⟩ : QbarCW.Cell) = QbarCW.dim (⟨G⟩ : QbarCW.Cell) + 1)) = ∅ := by
  decide +revert

theorem qFacet_mem_facets {x G : Fin 865} (hG : G ∈ qFacet x) :
    (⟨G⟩ : QbarCW.Cell) ∈ QbarCW.facets (⟨x⟩ : QbarCW.Cell) := by
  have hfilt := qFacet_facet_list x
  rw [PolyCW.mem_facets]
  have := (Finset.filter_eq_empty_iff.mp hfilt) hG
  simpa only [not_not] using this

/-! ## 4. The atlas chain of a cell is the push of the subdivision chain -/

/-- The identification of the atlas chain with the push of the subdivision chain of the root
face. -/
theorem liftEquiv_symm_val (n : ℕ) (hn : n < 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n))
    (s : Simplex QbarCW.Cell n) (h : s (Fin.last n) = rootCx n e) :
    ((CellAtlas.liftEquiv mbarAtlasOf n n e).symm ⟨s, h⟩).1 = nodeSimplex (rootCopy n e) s := by
  have hcar : carCx (nodeSimplex (rootCopy n e) s) = ⟨n, e⟩ := by
    rw [carCx_nodeSimplex, rootCopy_of_lt hn]
    exact carQ_rootNode n hn e s h
  have h1 : (CellAtlas.liftEquiv mbarAtlasOf n n e)
      ⟨nodeSimplex (rootCopy n e) s, hcar⟩ = ⟨s, h⟩ := by
    apply Subtype.ext
    show liftCx (nodeSimplex (rootCopy n e) s) = s
    rw [liftCx_nodeSimplex, rootCopy_of_lt hn]
    exact liftQ_rootNode n hn e s h
  have h2 : (CellAtlas.liftEquiv mbarAtlasOf n n e).symm ⟨s, h⟩
      = ⟨nodeSimplex (rootCopy n e) s, hcar⟩ :=
    (Equiv.symm_apply_eq (CellAtlas.liftEquiv mbarAtlasOf n n e)).mpr h1.symm
  rw [h2]

/-- A `dite`-sum is the sum over the filtered set. -/
theorem sum_dite_eq_sum_filter {α M : Type*} [AddCommMonoid M] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (f : (a : α) → p a → M) (g : α → M) (hg : ∀ a (h : p a), g a = f a h) :
    (∑ a ∈ s, (if h : p a then f a h else 0)) = ∑ a ∈ s.filter p, g a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.filter_insert, ih]
      by_cases hp : p a
      · rw [dif_pos hp, if_pos hp, Finset.sum_insert (by simp [ha]), hg a hp]
      · rw [dif_neg hp, if_neg hp, zero_add]

/-- The atlas chain of a cell is the push of its subdivision chain. -/
theorem kz_eq_pushNode (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    CellAtlas.kz mbarAtlasOf n e
      = pushNode (rootCopy n e) n
          (PolyCW.subdivCell QbarCW n ⟨rootCx n e, rootCx_dim n e⟩) := by
  by_cases hn : n < 5
  · have hg : ∀ (a : Simplex QbarCW.Cell n) (h : a (Fin.last n) = rootCx n e),
        (PolyCW.subdivCell QbarCW n ⟨rootCx n e, rootCx_dim n e⟩) a
          = (CellAtlas.rootCoeff mbarAtlasOf n e a) := fun a h => rfl
    rw [CellAtlas.kz_eq, pushNode_apply]
    show (∑ s : Simplex QbarCW.Cell n,
        (if h : s (Fin.last n) = rootCx n e then
          (PolyCW.subdivCell QbarCW n ⟨rootCx n e, rootCx_dim n e⟩) s •
            Finsupp.single ((CellAtlas.liftEquiv mbarAtlasOf n n e).symm ⟨s, h⟩).1 (1 : ℤ)
        else 0))
      = ∑ s ∈ (PolyCW.subdivCell QbarCW n ⟨rootCx n e, rootCx_dim n e⟩).support,
          (PolyCW.subdivCell QbarCW n ⟨rootCx n e, rootCx_dim n e⟩) s •
            Finsupp.single (nodeSimplex (rootCopy n e) s) (1 : ℤ)
    rw [sum_dite_eq_sum_filter (s := Finset.univ)
      (p := fun a : Simplex QbarCW.Cell n => a (Fin.last n) = rootCx n e)
      (f := fun a h => (PolyCW.subdivCell QbarCW n ⟨rootCx n e, rootCx_dim n e⟩) a •
        Finsupp.single ((CellAtlas.liftEquiv mbarAtlasOf n n e).symm ⟨a, h⟩).1 (1 : ℤ))
      (g := fun a => (PolyCW.subdivCell QbarCW n ⟨rootCx n e, rootCx_dim n e⟩) a •
        Finsupp.single (nodeSimplex (rootCopy n e) a) (1 : ℤ))
      (fun a h => by rw [liftEquiv_symm_val n hn e a h])]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro a ha
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, subdivCell_apply_last QbarCW n
        ⟨rootCx n e, rootCx_dim n e⟩ a ha⟩
    · intro a _ ha
      have hzero : (PolyCW.subdivCell QbarCW n ⟨rootCx n e, rootCx_dim n e⟩) a = 0 := by
        by_contra hc
        exact ha (Finsupp.mem_support_iff.mpr hc)
      rw [hzero, zero_smul]
  · exact Fin.elim0 (by
      have h0 : Work.HomologyIso.Gen.mbarDim n = 0 :=
        Work.HomologyIso.Gen.mbarDim_eq_zero n (by omega)
      exact h0 ▸ e)


/-- A face of `Q̄` of a given dimension. -/
abbrev FaceCx (n : ℕ) : Type := {e : QbarCell // QbarCW.dim e = n}

/-! ## 5. The push commutes with the star map of a sign change -/

/-- The vertexwise map of the sign change on the flags is the action of the sign change. -/
theorem congrIic_faceActIso (g : Fin 4 → ZMod 2) (n : ℕ) (F : QbarCell)
    (s : Simplex QbarCW.Cell n) (h : ∀ i, s i ≤ F) :
    PolyCW.Simplex.congrIic QbarCW (faceActIso g F) s h = flagAct g s := by
  apply Simplex.ext
  intro i
  exact faceActIso_apply g F ⟨s i, h i⟩

/-- The identification subgroup shrinks when the face grows. -/
theorem KsubAtlas_anti {a b : QbarCell} (h : a ≤ b) :
    KsubAtlas b.idx ≤ KsubAtlas a.idx := by
  refine AddSubgroup.closure_mono ?_
  rintro γ ⟨S, hS, rfl⟩
  exact ⟨S, (mem_tightSidesIdx a.idx S).mpr
    (mem_qTight_of_le h S ((mem_tightSidesIdx b.idx S).mp hS)), rfl⟩

/-- The node `(c,G)` identifies a flag over a face of `G` with its sign-changed representative
over the root face of the cell of the node. -/
theorem flagRel_act_facet (c : ZMod 2) (n : ℕ) (G : QbarCell)
    (s : Simplex QbarCW.Cell n) (h : ∀ i, s i ≤ G) :
    flagRel (c, s) (moRootC (moCell c G.idx), flagAct (sigVec c G.idx) s) := by
  refine ⟨Enode c G.idx, ?_, ?_, ?_⟩
  · rw [Ksub_bary_eq_KsubAtlas]
    exact KsubAtlas_anti (h (Fin.last n)) (Enode_mem_KsubAtlas c G.idx)
  · show moRootC (moCell c G.idx) = c + (c + moRootC (moCell c G.idx))
    rw [← add_assoc, zmod2_add_self', zero_add]
  · show bary (flagAct (sigVec c G.idx) s) = Work.FoldInst.act (sigVec c G.idx) (bary s)
    rw [bary_flagAct]

theorem nodeSimplex_eq_of_flagRel {k : ℕ} {x y : FlagQ k} (h : flagRel x y) :
    nodeSimplex x.1 x.2 = nodeSimplex y.1 y.2 := by
  show (mbarEquiv k).symm (Quotient.mk (flagSetoid k) (x.1, x.2))
      = (mbarEquiv k).symm (Quotient.mk (flagSetoid k) (y.1, y.2))
  exact congrArg (mbarEquiv k).symm (Quotient.sound h)

/-- **The push commutes with the star map.**  On chains supported in the closed cell `G`, pushing
along the node `(c, ·)` is the same as the vertexwise star map of the sign change `sigVec c G`
followed by the push along the root node of the cell of `G`. -/
theorem pushNode_starLM (c : ZMod 2) (n : ℕ) (G : QbarCell) (hG : QbarCW.dim G = n)
    (z : chainMod QbarCW.Cell n) (hz : z ∈ PolyCW.leSub QbarCW G n) :
    pushNode c n z = pushNode (moRootC (moCell c G.idx)) n
      (PolyCW.starLM QbarCW (faceActIso (sigVec c G.idx) G) n z) := by
  refine Submodule.span_induction (p := fun z _ => pushNode c n z
      = pushNode (moRootC (moCell c G.idx)) n
          (PolyCW.starLM QbarCW (faceActIso (sigVec c G.idx) G) n z)) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨σ, hσ, rfl⟩
    rw [PolyCW.starLM_single QbarCW (faceActIso (sigVec c G.idx) G) σ hσ, pushNode_single,
      pushNode_single]
    refine congrArg (fun u => Finsupp.single u (1 : ℤ)) ?_
    rw [congrIic_faceActIso (sigVec c G.idx) n G σ hσ]
    exact nodeSimplex_eq_of_flagRel (flagRel_act_facet c n G σ hσ)
  · simp
  · intro a b ha hb iha ihb
    simp only [map_add, iha, ihb]
  · intro k a ha iha
    simp only [map_smul, iha]

/-! ## 6. The boundary of the subdivision chain of a facet -/

theorem faceActCell_eq_moRoot (c : ZMod 2) (G : QbarCell) :
    faceActCell (sigVec c G.idx) G = (⟨moRoot (moCell c G.idx)⟩ : QbarCW.Cell) :=
  QbarCell.ext (congrArg Prod.snd (Enode_act c G.idx))

theorem moRoot_dim' (i : Fin 482) : QbarCW.dim (⟨moRoot i⟩ : QbarCW.Cell) = moDim i := by
  decide +revert

theorem moRoot_dim_cell (c : ZMod 2) (G : QbarCell) (n : ℕ) (hG : QbarCW.dim G = n) :
    QbarCW.dim (⟨moRoot (moCell c G.idx)⟩ : QbarCW.Cell) = n := by
  rw [moRoot_dim', moDim_moCell, hG]

/-- **The push of the subdivision chain of a facet is the atlas chain of that facet's cell.** -/
theorem pushNode_subdivCell_facet (c : ZMod 2) (n : ℕ) (hn : n < 5) (G : QbarCell)
    (hG : QbarCW.dim G = n) :
    pushNode c n (PolyCW.subdivCell QbarCW n (⟨G, hG⟩ : FaceCx n))
      = oS (sigVec c G.idx) G.idx • CellAtlas.kz mbarAtlasOf n (facetCellIdx c n G.idx hG) := by
  have hmem : PolyCW.subdivCell QbarCW n (⟨G, hG⟩ : FaceCx n) ∈ PolyCW.leSub QbarCW G n :=
    PolyCW.subdivCell_mem_leSub QbarCW n (⟨G, hG⟩ : FaceCx n)
  have hF : (⟨faceActCell (sigVec c G.idx) G, by rw [QbarCW_dim_faceAct]; exact hG⟩ : FaceCx n)
      = (⟨rootCx n (facetCellIdx c n G.idx hG),
          rootCx_dim n (facetCellIdx c n G.idx hG)⟩ : FaceCx n) := by
    apply Subtype.ext
    show faceActCell (sigVec c G.idx) G = rootCx n (facetCellIdx c n G.idx hG)
    rw [faceActCell_eq_moRoot, rootCx_of_lt hn, moCid_facetCellIdx c n hn G.idx hG]
  have hkey : pushNode (moRootC (moCell c G.idx)) n
      (PolyCW.subdivCell QbarCW n
        (⟨faceActCell (sigVec c G.idx) G, by rw [QbarCW_dim_faceAct]; exact hG⟩ : FaceCx n))
      = CellAtlas.kz mbarAtlasOf n (facetCellIdx c n G.idx hG) := by
    rw [kz_eq_pushNode, hF, rootCopy_of_lt hn, moCid_facetCellIdx c n hn G.idx hG]
  calc pushNode c n (PolyCW.subdivCell QbarCW n (⟨G, hG⟩ : FaceCx n))
      = pushNode (moRootC (moCell c G.idx)) n
          (PolyCW.starLM QbarCW (faceActIso (sigVec c G.idx) G) n
            (PolyCW.subdivCell QbarCW n (⟨G, hG⟩ : FaceCx n))) :=
        pushNode_starLM c n G hG _ hmem
    _ = pushNode (moRootC (moCell c G.idx)) n
          (oS (sigVec c G.idx) G.idx • PolyCW.subdivCell QbarCW n
            (⟨faceActCell (sigVec c G.idx) G, by rw [QbarCW_dim_faceAct]; exact hG⟩ : FaceCx n)) := by
        rw [Work.Mbar.starLM_subdivCell_signed (sigVec c G.idx) n
          (⟨G, hG⟩ : FaceCx n)]
    _ = oS (sigVec c G.idx) G.idx • CellAtlas.kz mbarAtlasOf n (facetCellIdx c n G.idx hG) := by
        rw [map_smul, hkey]


/-! ## 7. The cell of a facet as a total function -/

theorem mbarDim_pos {n : ℕ} (hn : n < 5) : 0 < Work.HomologyIso.Gen.mbarDim n := by
  interval_cases n <;> decide +kernel

/-- The cell of the facet node `(c,G)`, as a total function of `G : Fin 865`. -/
def phiFacet (c : ZMod 2) (n : ℕ) (hn : n < 5) (G : Fin 865) :
    Fin (Work.HomologyIso.Gen.mbarDim n) :=
  if h : QbarCW.dim (⟨G⟩ : QbarCell) = n then facetCellIdx c n G h
  else ⟨0, mbarDim_pos hn⟩

theorem phiFacet_eq {c : ZMod 2} {n : ℕ} {hn : n < 5} {G : Fin 865}
    (h : QbarCW.dim (⟨G⟩ : QbarCell) = n) :
    phiFacet c n hn G = facetCellIdx c n G h := dif_pos h

theorem phiFacet_eq_iff {c : ZMod 2} {n : ℕ} {hn : n < 5} {G : Fin 865}
    (hG : QbarCW.dim (⟨G⟩ : QbarCell) = n) (f : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    (moCell c G = moCid ⟨n, hn⟩ f) ↔ phiFacet c n hn G = f := by
  rw [phiFacet_eq hG]
  exact facetCellIdx_eq_iff c n hn G hG f

/-! ## 8. The boundary of the atlas chain of a cell, as a sum over the facets -/

theorem facets_form (n : ℕ) (hn1 : n + 1 < 5)
    (e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))) :
    pushNode (rootCopy (n + 1) e) n
        (D (α := QbarCW.Cell) n
          (PolyCW.subdivCell QbarCW (n + 1) ⟨rootCx (n + 1) e, rootCx_dim (n + 1) e⟩))
      = ∑ y ∈ (QbarCW.facets (rootCx (n + 1) e)).attach,
          (QbarCW.inc (rootCx (n + 1) e) y.1
            * oS (sigVec (rootCopy (n + 1) e) y.1.idx) y.1.idx) •
          CellAtlas.kz mbarAtlasOf n (phiFacet (rootCopy (n + 1) e) n (by omega) y.1.idx) := by
  have hdim : ∀ y ∈ QbarCW.facets (rootCx (n + 1) e), QbarCW.dim y = n := by
    intro y hy
    have h := (PolyCW.mem_facets (P := QbarCW) (rootCx (n + 1) e) y).mp hy
    have hR := rootCx_dim (n + 1) e
    omega
  rw [D_subdivCell QbarCW Work.MbarHomology.Qbar.QbarCW_hasDdZero Work.MbarHomology.Qbar.QbarCW_hasAugZero n
    ⟨rootCx (n + 1) e, rootCx_dim (n + 1) e⟩]
  rw [map_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [map_smul]
  have hy' : QbarCW.dim (⟨y.1.idx⟩ : QbarCell) = n := by
    simpa using hdim y.1 y.2
  have hB3 := pushNode_subdivCell_facet (rootCopy (n + 1) e) n (by omega) y.1 (hdim y.1 y.2)
  show (QbarCW.inc (rootCx (n + 1) e) y.1) • pushNode (rootCopy (n + 1) e) n
      (PolyCW.subdivCell QbarCW n (⟨y.1, hdim y.1 y.2⟩ : FaceCx n))
    = (QbarCW.inc (rootCx (n + 1) e) y.1 * oS (sigVec (rootCopy (n + 1) e) y.1.idx) y.1.idx) •
        CellAtlas.kz mbarAtlasOf n (phiFacet (rootCopy (n + 1) e) n (by omega) y.1.idx)
  rw [hB3, phiFacet_eq hy', mul_smul]


/-! ## 9. The `qFacet` form of the facets sum -/

theorem facets_image_eq_qFacet (c : ZMod 2) (n : ℕ) (hn : n < 5) (x : Fin 865) :
    ∑ G ∈ (QbarCW.facets (⟨x⟩ : QbarCW.Cell)).image (fun y : QbarCW.Cell => y.idx),
        (qInc x G * oS (sigVec c G) G) • CellAtlas.kz mbarAtlasOf n (phiFacet c n hn G)
      = ∑ G ∈ qFacet x,
        (qInc x G * oS (sigVec c G) G) • CellAtlas.kz mbarAtlasOf n (phiFacet c n hn G) := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro G hG
    exact Finset.mem_image.mpr ⟨⟨G⟩, qFacet_mem_facets hG, rfl⟩
  · intro G _ hG
    rw [show qInc x G = 0 from by rw [qInc]; exact ite_eq_right hG, zero_mul, zero_smul]

theorem facets_sum_image_form (n : ℕ) (hn1 : n + 1 < 5)
    (e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))) :
    ∑ y ∈ (QbarCW.facets (rootCx (n + 1) e)).attach,
        (QbarCW.inc (rootCx (n + 1) e) y.1
          * oS (sigVec (rootCopy (n + 1) e) y.1.idx) y.1.idx) •
        CellAtlas.kz mbarAtlasOf n (phiFacet (rootCopy (n + 1) e) n (by omega) y.1.idx)
      = ∑ G ∈ (QbarCW.facets (rootCx (n + 1) e)).image (fun y : QbarCW.Cell => y.idx),
          (qInc (moRoot (moCid ⟨n + 1, hn1⟩ e)) G
            * oS (sigVec (rootCopy (n + 1) e) G) G) •
          CellAtlas.kz mbarAtlasOf n (phiFacet (rootCopy (n + 1) e) n (by omega) G) := by
  refine Finset.sum_bij (fun y _ => y.1.idx) ?_ ?_ ?_ ?_
  · intro y hy
    exact Finset.mem_image.mpr ⟨y.1, y.2, rfl⟩
  · intro y₁ _ y₂ _ h
    apply Subtype.ext
    exact QbarCell.ext h
  · intro G hG
    obtain ⟨y, hy, hyG⟩ := Finset.mem_image.mp hG
    exact ⟨⟨y, hy⟩, Finset.mem_attach _ _, hyG⟩
  · intro y _
    have hidx : (rootCx (n + 1) e).idx = moRoot (moCid ⟨n + 1, hn1⟩ e) := by
      rw [rootCx_of_lt hn1]
    rw [QbarCW_inc, hidx]

/-- The fibre decomposition of a sum of scalar multiples. -/
theorem sum_smul_comp {α β M : Type*} [AddCommMonoid M] [Module ℤ M] [DecidableEq β]
    (s : Finset α) (g : α → β) (A : α → ℤ) (k : β → M) :
    ∑ a ∈ s, A a • k (g a) = ∑ b ∈ s.image g, (∑ a ∈ s.filter (fun a => g a = b), A a) • k b := by
  classical
  have hdisj : ∀ x ∈ s.image g, ∀ y ∈ s.image g, x ≠ y →
      Disjoint (s.filter (fun a => g a = x)) (s.filter (fun a => g a = y)) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro a hax hay
    exact hxy ((Finset.mem_filter.mp hax).2.symm.trans (Finset.mem_filter.mp hay).2)
  have hbi : (s.image g).biUnion (fun b => s.filter (fun a => g a = b)) = s := by
    ext a
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨b, _, hab⟩
      exact (Finset.mem_filter.mp hab).1
    · intro ha
      exact ⟨g a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  refine (show (∑ b ∈ s.image g, (∑ a ∈ s.filter (fun a => g a = b), A a) • k b)
      = ∑ a ∈ s, A a • k (g a) from ?_).symm
  calc ∑ b ∈ s.image g, (∑ a ∈ s.filter (fun a => g a = b), A a) • k b
      = ∑ b ∈ s.image g, ∑ a ∈ s.filter (fun a => g a = b), A a • k b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ b ∈ s.image g, ∑ a ∈ s.filter (fun a => g a = b), A a • k (g a) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
        rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a ∈ (s.image g).biUnion (fun b => s.filter (fun a => g a = b)), A a • k (g a) := by
        rw [Finset.sum_biUnion hdisj]
    _ = ∑ a ∈ s, A a • k (g a) := by rw [hbi]

theorem sum_qFacet_fiber (c : ZMod 2) (n : ℕ) (hn : n < 5) (x : Fin 865) :
    (∑ G ∈ qFacet x,
        (qInc x G * oS (sigVec c G) G) • CellAtlas.kz mbarAtlasOf n (phiFacet c n hn G))
      = ∑ f : Fin (Work.HomologyIso.Gen.mbarDim n),
          (∑ G ∈ (qFacet x).filter (fun G => phiFacet c n hn G = f),
            qInc x G * oS (sigVec c G) G) • CellAtlas.kz mbarAtlasOf n f := by
  have key : (∑ G ∈ qFacet x,
        (qInc x G * oS (sigVec c G) G) • CellAtlas.kz mbarAtlasOf n (phiFacet c n hn G))
      = ∑ b ∈ (qFacet x).image (phiFacet c n hn),
          (∑ G ∈ (qFacet x).filter (fun G => phiFacet c n hn G = b),
            qInc x G * oS (sigVec c G) G) • CellAtlas.kz mbarAtlasOf n b :=
    sum_smul_comp (qFacet x) (phiFacet c n hn)
      (fun G => qInc x G * oS (sigVec c G) G) (fun f => CellAtlas.kz mbarAtlasOf n f)
  have hkey2 : (∑ f : Fin (Work.HomologyIso.Gen.mbarDim n),
        (∑ G ∈ (qFacet x).filter (fun G => phiFacet c n hn G = f),
          qInc x G * oS (sigVec c G) G) • CellAtlas.kz mbarAtlasOf n f)
      = ∑ f ∈ (qFacet x).image (phiFacet c n hn),
          (∑ G ∈ (qFacet x).filter (fun G => phiFacet c n hn G = f),
            qInc x G * oS (sigVec c G) G) • CellAtlas.kz mbarAtlasOf n f :=
    (Finset.sum_subset (Finset.subset_univ _) (fun f _ hf => by
      rw [Finset.filter_eq_empty_iff.mpr (fun G hG h =>
          hf (Finset.mem_image.mpr ⟨G, hG, h⟩)), Finset.sum_empty, zero_smul])).symm
  rw [key, hkey2]


/-! ## 10. The boundary of the atlas chain -/

theorem kδCpt_kz_eq (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))) :
    CellAtlas.kδCpt mbarSd n (CellAtlas.kz mbarAtlasOf (n + 1) e)
      = ∑ f : Fin (Work.HomologyIso.Gen.mbarDim n),
          (Work.HomologyIso.Gen.mbarBd n).toMatrix f e • CellAtlas.kz mbarAtlasOf n f := by
  by_cases hn1 : n + 1 < 5
  · have hn : n < 5 := by omega
    have hfiber : ∀ f : Fin (Work.HomologyIso.Gen.mbarDim n),
        (∑ G ∈ (qFacet (moRoot (moCid ⟨n + 1, hn1⟩ e))).filter
            (fun G => phiFacet (rootCopy (n + 1) e) n hn G = f),
          qInc (moRoot (moCid ⟨n + 1, hn1⟩ e)) G
            * oS (sigVec (rootCopy (n + 1) e) G) G)
          = (Work.HomologyIso.Gen.mbarBd n).toMatrix f e := by
      intro f
      have hfilter : (qFacet (moRoot (moCid ⟨n + 1, hn1⟩ e))).filter
            (fun G => phiFacet (rootCopy (n + 1) e) n hn G = f)
          = (qFacet (moRoot (moCid ⟨n + 1, hn1⟩ e))).filter
            (fun G => moCell (rootCopy (n + 1) e) G
              = moCid ⟨n, by omega⟩ f) := by
        apply Finset.filter_congr
        intro G hG
        have hdim : QbarCW.dim (⟨G⟩ : QbarCell) = n := by
          have h1 := qFacet_mem_facets (x := moRoot (moCid ⟨n + 1, hn1⟩ e)) hG
          have h2 := (PolyCW.mem_facets (P := QbarCW)
            (⟨moRoot (moCid ⟨n + 1, hn1⟩ e)⟩ : QbarCW.Cell) (⟨G⟩ : QbarCell)).mp h1
          have h3 := moRoot_dim' (moCid ⟨n + 1, hn1⟩ e)
          have h4 := (moCid_spec ⟨n + 1, hn1⟩ e).1
          simp only [Fin.val_mk] at h4
          omega
        rw [phiFacet_eq hdim]
        exact (facetCellIdx_eq_iff (rootCopy (n + 1) e) n hn G hdim f).symm
      rw [hfilter, rootCopy_of_lt hn1]
      exact Work.MbarHomology.BdFiber.mbarBd_fiber n hn1 e f
    calc CellAtlas.kδCpt mbarSd n (CellAtlas.kz mbarAtlasOf (n + 1) e)
        = pushNode (rootCopy (n + 1) e) n
            (D (α := QbarCW.Cell) n
              (PolyCW.subdivCell QbarCW (n + 1)
                ⟨rootCx (n + 1) e, rootCx_dim (n + 1) e⟩)) := by
          rw [kz_eq_pushNode, ← Work.MbarHomology.Push.pushNode_comm_D]
      _ = ∑ y ∈ (QbarCW.facets (rootCx (n + 1) e)).attach,
            (QbarCW.inc (rootCx (n + 1) e) y.1
              * oS (sigVec (rootCopy (n + 1) e) y.1.idx) y.1.idx) •
            CellAtlas.kz mbarAtlasOf n (phiFacet (rootCopy (n + 1) e) n hn y.1.idx) :=
          facets_form n hn1 e
      _ = ∑ G ∈ (QbarCW.facets (rootCx (n + 1) e)).image (fun y : QbarCW.Cell => y.idx),
            (qInc (moRoot (moCid ⟨n + 1, hn1⟩ e)) G
              * oS (sigVec (rootCopy (n + 1) e) G) G) •
            CellAtlas.kz mbarAtlasOf n (phiFacet (rootCopy (n + 1) e) n hn G) :=
          facets_sum_image_form n hn1 e
      _ = ∑ G ∈ qFacet (moRoot (moCid ⟨n + 1, hn1⟩ e)),
            (qInc (moRoot (moCid ⟨n + 1, hn1⟩ e)) G
              * oS (sigVec (rootCopy (n + 1) e) G) G) •
            CellAtlas.kz mbarAtlasOf n (phiFacet (rootCopy (n + 1) e) n hn G) := by
          rw [rootCx_of_lt hn1]
          exact facets_image_eq_qFacet (rootCopy (n + 1) e) n hn
            (moRoot (moCid ⟨n + 1, hn1⟩ e))
      _ = ∑ f : Fin (Work.HomologyIso.Gen.mbarDim n),
            (∑ G ∈ (qFacet (moRoot (moCid ⟨n + 1, hn1⟩ e))).filter
              (fun G => phiFacet (rootCopy (n + 1) e) n hn G = f),
              qInc (moRoot (moCid ⟨n + 1, hn1⟩ e)) G
                * oS (sigVec (rootCopy (n + 1) e) G) G) •
            CellAtlas.kz mbarAtlasOf n f :=
          sum_qFacet_fiber (rootCopy (n + 1) e) n hn (moRoot (moCid ⟨n + 1, hn1⟩ e))
      _ = ∑ f : Fin (Work.HomologyIso.Gen.mbarDim n),
            (Work.HomologyIso.Gen.mbarBd n).toMatrix f e • CellAtlas.kz mbarAtlasOf n f := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [hfiber f]
  · exact Fin.elim0 (by
      have h0 : Work.HomologyIso.Gen.mbarDim (n + 1) = 0 :=
        Work.HomologyIso.Gen.mbarDim_eq_zero (n + 1) (by omega)
      exact h0 ▸ e)

/-- **The boundary compatibility of the cell atlas of `M̄`.** -/
theorem mbarBoundaryCompat : mbarAtlasOf.BoundaryCompat := by
  intro n e
  have hsum : ∀ x : (Work.HomologyIso.Gen.mbarCx.toChainComplex).X n,
      (CellAtlas.kIso mbarSd n).hom ((CellAtlas.zMapFun mbarAtlasOf n).hom x)
        = ∑ f : Fin (Work.HomologyIso.Gen.mbarDim n),
            x f • CellAtlas.kz mbarAtlasOf n f := fun x => kIso_zMapFun n x
  have hL : (CellAtlas.kIso mbarSd n).hom
        (CellAtlas.zMapFun mbarAtlasOf n
          ((Work.HomologyIso.Gen.mbarCx.toChainComplex).d (n + 1) n (Pi.single e (1 : ℤ))))
      = ∑ f : Fin (Work.HomologyIso.Gen.mbarDim n),
          (Work.HomologyIso.Gen.mbarBd n).toMatrix f e • CellAtlas.kz mbarAtlasOf n f := by
    rw [hsum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Work.MbarHomology.CellAtlas.toChainComplex_d_single]
    rfl
  have hR : (CellAtlas.kIso mbarSd n).hom
        (mbarSd.chainD n (CellAtlas.zMapFun mbarAtlasOf (n + 1) (Pi.single e (1 : ℤ))))
      = ∑ f : Fin (Work.HomologyIso.Gen.mbarDim n),
          (Work.HomologyIso.Gen.mbarBd n).toMatrix f e • CellAtlas.kz mbarAtlasOf n f := by
    rw [kIso_chainD, CellAtlas.zMapFun_piSingle, ← CellAtlas.kz, kδCpt_kz_eq n e]
  have h := hL.trans hR.symm
  have hbij : Function.Bijective (ConcreteCategory.hom (CellAtlas.kIso mbarSd n).hom) :=
    (ConcreteCategory.isIso_iff_bijective (CellAtlas.kIso mbarSd n).hom).mp inferInstance
  exact hbij.1 h

end

end Work.MbarHomology.Mbar
