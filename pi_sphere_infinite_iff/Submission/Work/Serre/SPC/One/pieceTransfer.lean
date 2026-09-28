import Mathlib
import Submission.Work.Serre.SPC.One.pieceModel
import Submission.Work.Serre.SPC.One.Pieces
import Submission.Work.Serre.SPC.One.OneCellGeom
import Submission.Work.Serre.SPC.discDefs
import Submission.Work.ThomBordism.doubleFC.relFactor

set_option synthInstance.maxHeartbeats 400000


/-!
# The per-piece comparison is the model comparison

For `Z = attachOneCells Y ι f` and a map `q : X → Z`, the `i`-th piece of `q` is
`pieceX Y ι f q i = q⁻¹(cellInteriorOne i)` with relative part `pieceXrel` (the preimage of the
punctured cell `cellPunct i`), and `pieceChainMap` is the induced map of relative chain complexes.

The characteristic map `oneCellMap i : D¹ → Z` is a homeomorphism of the open interval onto the open
cell (`exists_chart`), and the pullback `Pullback q (oneCellMap i)`, restricted to `cellInnerOne`, is
exactly the piece.  This file proves that the pair map of the piece and the *model* pair map
`pmMapOne q (oneCellMap i) punctDisc` are conjugate: for every degree `k`, `pieceChainMap` is an
isomorphism on `H_k` (resp. surjective) exactly when the model map is.

The proof is two commutative squares whose vertical maps are isomorphisms on homology: the
homeomorphism of pairs given by the chart, and the excision of the open cover
`{cellInnerOne, punctDisc}` of `D¹` (`Work.Cohomology.excision_relChainsMap_isIso`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
variable {X : Type} [TopologicalSpace X] {q : C(X, attachOneCells Y ι f)}

/-! ## The chart of the open cell -/

/-- The chart of the `i`-th open cell: a continuous section of the characteristic map, inverse to
`oneCellMap i` on the open model interval. -/
def cellChart (i : ι) : C(↥(cellInteriorOne Y ι f i), ↥cellInnerOne) :=
  Classical.choose (exists_chart f i)

theorem cellChart_spec (i : ι) :
    (∀ y : ↥(cellInteriorOne Y ι f i),
        oneCellMap Y ι f i (cellChart i y) = (y : attachOneCells Y ι f)) ∧
      (∀ t : ↥cellInnerOne, cellChart i ⟨oneCellMap Y ι f i t, t, t.2, rfl⟩ = t) :=
  Classical.choose_spec (exists_chart f i)

theorem cellChart_apply (i : ι) (y : ↥(cellInteriorOne Y ι f i)) :
    oneCellMap Y ι f i (cellChart i y) = (y : attachOneCells Y ι f) :=
  (cellChart_spec (f := f) i).1 y

theorem cellChart_symm_apply (i : ι) (t : ↥cellInnerOne) :
    cellChart i ⟨oneCellMap Y ι f i t, t, t.2, rfl⟩ = t :=
  (cellChart_spec (f := f) i).2 t

/-- The centre lies in the open model interval. -/
theorem cellD1Centre_mem_cellInnerOne_pieceTransfer : cellD1Centre ∈ cellInnerOne := by
  rw [mem_cellInnerOne]
  simp [cellD1Centre]

theorem cellChart_ne_centre_iff (i : ι) {z : attachOneCells Y ι f}
    (hz : z ∈ cellInteriorOne Y ι f i) :
    z ≠ oneCellCentreOne Y ι f i ↔
      ((cellChart i ⟨z, hz⟩ : ↥cellInnerOne) : cellD1) ≠ cellD1Centre := by
  have h1 : oneCellMap Y ι f i (cellChart i ⟨z, hz⟩) = z := cellChart_apply (f := f) i ⟨z, hz⟩
  constructor
  · intro h hc
    refine h ?_
    rw [← h1, hc]
    rfl
  · intro hh hc
    refine hh ?_
    have hz2 : cellD1Centre ∈ cellInnerOne := cellD1Centre_mem_cellInnerOne_pieceTransfer
    have hxy : ((cellChart i ⟨z, hz⟩ : ↥cellInnerOne) : cellD1) = cellD1Centre := by
      refine oneCellMap_injOn_inner f i (cellChart i ⟨z, hz⟩).2 hz2 ?_
      rw [h1]
      exact hc
    exact hxy

/-- The homeomorphism of the open cell with the open model interval. -/
def cellInteriorHomeo (i : ι) : ↥(cellInteriorOne Y ι f i) ≃ₜ ↥cellInnerOne where
  toFun := cellChart i
  invFun t := ⟨oneCellMap Y ι f i t, t, t.2, rfl⟩
  left_inv y := Subtype.ext (cellChart_apply (f := f) i y)
  right_inv t := cellChart_symm_apply (f := f) i t
  continuous_toFun := (cellChart i).continuous
  continuous_invFun :=
    Continuous.subtype_mk ((oneCellMap Y ι f i).continuous.comp continuous_subtype_val) _

@[simp] theorem cellInteriorHomeo_apply (i : ι) (y : ↥(cellInteriorOne Y ι f i)) :
    cellInteriorHomeo (f := f) i y = cellChart i y := rfl

theorem cellInteriorHomeo_symm_coe (i : ι) (t : ↥cellInnerOne) :
    ((cellInteriorHomeo (f := f) i).symm t : attachOneCells Y ι f) = oneCellMap Y ι f i t := rfl

/-! ## The piece and the restricted pullback -/

/-- The total space of the pullback of `q` along the characteristic map of the `i`-th cell. -/
abbrev pbChar (i : ι) : Type := Work.StemsB.Pullback q (oneCellMap Y ι f i)

/-- The part of the pullback lying over the open model interval. -/
abbrev pullCell (i : ι) : Set (pbChar (f := f) (q := q) i) :=
  (Work.StemsB.pullbackSnd q (oneCellMap Y ι f i)) ⁻¹' cellInnerOne

/-- The part of the pullback lying over the punctured model interval. -/
abbrev pullPunct (i : ι) : Set (pbChar (f := f) (q := q) i) :=
  (Work.StemsB.pullbackSnd q (oneCellMap Y ι f i)) ⁻¹' punctDisc

/-- The `i`-th piece of `q`, mapped into the pullback of `q` along the characteristic map by the
chart. -/
def pieceToPbFun (i : ι) (x : pieceX Y ι f q i) : ↥(pullCell (f := f) (q := q) i) :=
  ⟨⟨(x.1, cellChart i ⟨q x.1, x.2⟩),
      ((cellChart_apply (f := f) i ⟨q x.1, x.2⟩)).symm⟩,
    (cellChart i ⟨q x.1, x.2⟩).2⟩

theorem continuous_pieceToPbFun (i : ι) : Continuous (pieceToPbFun (f := f) (q := q) i) := by
  unfold pieceToPbFun
  fun_prop

/-- The inverse direction, from the restricted pullback to the piece. -/
def pbToPieceFun (i : ι) (y : ↥(pullCell (f := f) (q := q) i)) : pieceX Y ι f q i :=
  ⟨y.1.1.1, by
    rw [Set.mem_preimage]
    rw [show q y.1.1.1 = oneCellMap Y ι f i y.1.1.2 from y.1.2]
    exact ⟨y.1.1.2, y.2, rfl⟩⟩

theorem continuous_pbToPieceFun (i : ι) : Continuous (pbToPieceFun (f := f) (q := q) i) := by
  unfold pbToPieceFun
  fun_prop

theorem pbToPiece_pieceToPb (i : ι) (x : pieceX Y ι f q i) :
    pbToPieceFun (f := f) (q := q) i (pieceToPbFun (f := f) (q := q) i x) = x := by
  refine Subtype.ext ?_
  rfl

theorem pieceToPb_pbToPiece (i : ι) (y : ↥(pullCell (f := f) (q := q) i)) :
    pieceToPbFun (f := f) (q := q) i (pbToPieceFun (f := f) (q := q) i y) = y := by
  have hmem : q y.1.1.1 ∈ cellInteriorOne Y ι f i := by
    rw [show q y.1.1.1 = oneCellMap Y ι f i y.1.1.2 from y.1.2]
    exact ⟨y.1.1.2, y.2, rfl⟩
  refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
  · rfl
  · show ((cellChart i ⟨q y.1.1.1, hmem⟩ : ↥cellInnerOne) : cellD1) = y.1.1.2
    have hxy : ((cellChart i ⟨q y.1.1.1, hmem⟩ : ↥cellInnerOne) : cellD1) = y.1.1.2 := by
      refine oneCellMap_injOn_inner f i (cellChart i ⟨q y.1.1.1, hmem⟩).2 y.2 ?_
      rw [cellChart_apply]
      exact y.1.2
    exact hxy

/-- **The piece is the restricted pullback**: a homeomorphism of pairs over the chart. -/
def pieceHomeo (i : ι) :
    (pieceX Y ι f q i) ≃ₜ ↥(pullCell (f := f) (q := q) i) where
  toFun := pieceToPbFun (f := f) (q := q) i
  invFun := pbToPieceFun (f := f) (q := q) i
  left_inv := pbToPiece_pieceToPb (f := f) (q := q) i
  right_inv := pieceToPb_pbToPiece (f := f) (q := q) i
  continuous_toFun := continuous_pieceToPbFun (f := f) (q := q) i
  continuous_invFun := continuous_pbToPieceFun (f := f) (q := q) i

@[simp] theorem pieceHomeo_apply (i : ι) (x : pieceX Y ι f q i) :
    pieceHomeo (f := f) (q := q) i x = pieceToPbFun (f := f) (q := q) i x := rfl

theorem pieceHomeo_snd (i : ι) (x : pieceX Y ι f q i) :
    Work.StemsB.pullbackSnd q (oneCellMap Y ι f i) (pieceHomeo (f := f) (q := q) i x)
      = cellChart i ⟨q x.1, x.2⟩ := rfl

/-- The piece map is the chart composed with the base projection of the pullback. -/
theorem cellInteriorHomeo_pieceMap (i : ι) (x : pieceX Y ι f q i) :
    cellInteriorHomeo (f := f) i (pieceMap Y ι f q i x)
      = ⟨Work.StemsB.pullbackSnd q (oneCellMap Y ι f i) (pieceHomeo (f := f) (q := q) i x),
          (pieceHomeo (f := f) (q := q) i x).2⟩ := rfl

/-! ## The relative parts correspond -/

theorem mem_pieceXrel_iff (i : ι) (x : pieceX Y ι f q i) :
    x ∈ pieceXrel Y ι f q i ↔
      Work.StemsB.pullbackSnd q (oneCellMap Y ι f i) (pieceHomeo (f := f) (q := q) i x)
        ∈ punctDisc := by
  show q x.1 ∈ cellPunct (f := f) i ↔
    Work.StemsB.pullbackSnd q (oneCellMap Y ι f i) (pieceHomeo (f := f) (q := q) i x)
      ∈ punctDisc
  rw [mem_cellPunct, mem_punctDisc, pieceHomeo_snd]
  rw [cellChart_ne_centre_iff (f := f) i x.2]
  exact and_iff_right x.2

theorem mem_pieceYrel_iff (i : ι) (y : pieceY Y ι f i) :
    y ∈ pieceYrel Y ι f i ↔
      ((cellInteriorHomeo (f := f) i y : ↥cellInnerOne) : cellD1) ∈ punctDisc := by
  show (y : attachOneCells Y ι f) ∈ cellPunct (f := f) i ↔
    ((cellInteriorHomeo (f := f) i y : ↥cellInnerOne) : cellD1) ∈ punctDisc
  rw [mem_cellPunct, mem_punctDisc]
  rw [cellChart_ne_centre_iff (f := f) i y.2]
  exact and_iff_right y.2

/-! ## The middle map over the open interval -/

/-- The projection of the restricted pullback to the open interval. -/
def midFun (i : ι) : C(↥(pullCell (f := f) (q := q) i), ↥cellInnerOne) where
  toFun y := ⟨Work.StemsB.pullbackSnd q (oneCellMap Y ι f i) y.1, y.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((Work.StemsB.pullbackSnd q (oneCellMap Y ι f i)).continuous.comp continuous_subtype_val)
    (fun y => y.2)

theorem midFun_mapsTo (i : ι) :
    Set.MapsTo (midFun (f := f) (q := q) i)
      {x : ↥(pullCell (f := f) (q := q) i) | (x : pbChar (f := f) (q := q) i) ∈ pullPunct (f := f) (q := q) i}
      {y : ↥cellInnerOne | (y : cellD1) ∈ punctDisc} :=
  fun x hx => hx

/-- **The middle map**: the pair map over the open interval pair. -/
def midChain (i : ι) :
    Work.Cohomology.relChains (TopCat.of ↥(pullCell (f := f) (q := q) i))
        {x : ↥(pullCell (f := f) (q := q) i) |
          (x : pbChar (f := f) (q := q) i) ∈ pullPunct (f := f) (q := q) i} ⟶
      Work.Cohomology.relChains (TopCat.of ↥cellInnerOne)
        {y : ↥cellInnerOne | (y : cellD1) ∈ punctDisc} :=
  pairMap _ _ (midFun (f := f) (q := q) i) (midFun_mapsTo (f := f) (q := q) i)

/-! ## The two commutative squares -/

/-- The relative part of the restricted pullback. -/
abbrev pullCellRel (i : ι) : Set ↥(pullCell (f := f) (q := q) i) :=
  {x | (x : pbChar (f := f) (q := q) i) ∈ pullPunct (f := f) (q := q) i}

/-- The relative part of the open model interval. -/
abbrev innerPunct : Set ↥cellInnerOne := {y | (y : cellD1) ∈ punctDisc}

theorem pieceHomeo_mapsTo (i : ι) (x : pieceX Y ι f q i) (hx : x ∈ pieceXrel Y ι f q i) :
    (Work.StemsB.sphHomeoHom (X := TopCat.of (pieceX Y ι f q i))
      (Y := TopCat.of ↥(pullCell (f := f) (q := q) i)) (pieceHomeo (f := f) (q := q) i)) x
      ∈ pullCellRel (f := f) (q := q) i :=
  (mem_pieceXrel_iff (f := f) (q := q) i x).mp hx

theorem pieceHomeo_mapsTo_symm (i : ι) (y : ↥(pullCell (f := f) (q := q) i))
    (hy : y ∈ pullCellRel (f := f) (q := q) i) :
    (Work.StemsB.sphHomeoHom
      (X := TopCat.of ↥(pullCell (f := f) (q := q) i)) (Y := TopCat.of (pieceX Y ι f q i))
      (pieceHomeo (f := f) (q := q) i).symm) y ∈ pieceXrel Y ι f q i := by
  refine (mem_pieceXrel_iff (f := f) (q := q) i
    ((pieceHomeo (f := f) (q := q) i).symm y)).mpr ?_
  rw [Homeomorph.apply_symm_apply]
  exact hy

theorem cellInteriorHomeo_mapsTo (i : ι) (y : pieceY Y ι f i) (hy : y ∈ pieceYrel Y ι f i) :
    (Work.StemsB.sphHomeoHom (X := TopCat.of (pieceY Y ι f i))
      (Y := TopCat.of ↥cellInnerOne) (cellInteriorHomeo (f := f) i)) y ∈ innerPunct :=
  (mem_pieceYrel_iff (f := f) i y).mp hy

theorem cellInteriorHomeo_mapsTo_symm (i : ι) (y : ↥cellInnerOne) (hy : y ∈ innerPunct) :
    (Work.StemsB.sphHomeoHom
      (X := TopCat.of ↥cellInnerOne) (Y := TopCat.of (pieceY Y ι f i))
      (cellInteriorHomeo (f := f) i).symm) y ∈ pieceYrel Y ι f i := by
  refine (mem_pieceYrel_iff (f := f) i
    ((cellInteriorHomeo (f := f) i).symm y)).mpr ?_
  rw [Homeomorph.apply_symm_apply]
  exact hy

/-- The chain map induced by the homeomorphism of the piece with the restricted pullback. -/
def uXChain (i : ι) :
    Work.Cohomology.relChains (TopCat.of (pieceX Y ι f q i)) (pieceXrel Y ι f q i) ⟶
      Work.Cohomology.relChains (TopCat.of ↥(pullCell (f := f) (q := q) i))
        (pullCellRel (f := f) (q := q) i) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (pieceX Y ι f q i))
    (TopCat.of ↥(pullCell (f := f) (q := q) i)) (pieceXrel Y ι f q i)
    (pullCellRel (f := f) (q := q) i)
    (Work.StemsB.sphHomeoHom (X := TopCat.of (pieceX Y ι f q i))
      (Y := TopCat.of ↥(pullCell (f := f) (q := q) i)) (pieceHomeo (f := f) (q := q) i))
    (Work.StemsB.pairRestrict (X := TopCat.of (pieceX Y ι f q i))
      (Y := TopCat.of ↥(pullCell (f := f) (q := q) i))
      (Work.StemsB.sphHomeoHom (X := TopCat.of (pieceX Y ι f q i))
        (Y := TopCat.of ↥(pullCell (f := f) (q := q) i)) (pieceHomeo (f := f) (q := q) i))
      (pieceXrel Y ι f q i) (pullCellRel (f := f) (q := q) i)
      (pieceHomeo_mapsTo (f := f) (q := q) i))
    (Work.StemsB.pairRestrict_comp_subtypeIncl _ _ _ _).symm

theorem isIso_uXChain (i : ι) : IsIso (uXChain (f := f) (q := q) i) := by
  rw [uXChain]
  exact isIso_relChainsMapOf_homeo' (X := TopCat.of (pieceX Y ι f q i))
    (Y := TopCat.of ↥(pullCell (f := f) (q := q) i)) (pieceHomeo (f := f) (q := q) i) _ _
    (pieceHomeo_mapsTo (f := f) (q := q) i) (pieceHomeo_mapsTo_symm (f := f) (q := q) i)

/-- The chain map induced by the chart on the base. -/
def uYChain (i : ι) :
    Work.Cohomology.relChains (TopCat.of (pieceY Y ι f i)) (pieceYrel Y ι f i) ⟶
      Work.Cohomology.relChains (TopCat.of ↥cellInnerOne) innerPunct :=
  Work.Cohomology.relChainsMapOf (TopCat.of (pieceY Y ι f i)) (TopCat.of ↥cellInnerOne)
    (pieceYrel Y ι f i) innerPunct
    (Work.StemsB.sphHomeoHom (X := TopCat.of (pieceY Y ι f i)) (Y := TopCat.of ↥cellInnerOne)
      (cellInteriorHomeo (f := f) i))
    (Work.StemsB.pairRestrict (X := TopCat.of (pieceY Y ι f i)) (Y := TopCat.of ↥cellInnerOne)
      (Work.StemsB.sphHomeoHom (X := TopCat.of (pieceY Y ι f i)) (Y := TopCat.of ↥cellInnerOne)
        (cellInteriorHomeo (f := f) i))
      (pieceYrel Y ι f i) innerPunct (cellInteriorHomeo_mapsTo (f := f) i))
    (Work.StemsB.pairRestrict_comp_subtypeIncl _ _ _ _).symm

theorem isIso_uYChain (i : ι) : IsIso (uYChain (f := f) i) := by
  rw [uYChain]
  exact isIso_relChainsMapOf_homeo' (X := TopCat.of (pieceY Y ι f i))
    (Y := TopCat.of ↥cellInnerOne) (cellInteriorHomeo (f := f) i) _ _
    (cellInteriorHomeo_mapsTo (f := f) i) (cellInteriorHomeo_mapsTo_symm (f := f) i)

/-! ## The commutation of the projections with the pair maps -/

/-- Naturality of the projection to the relative chain complex for `relChainsMapOf`. -/
theorem cokernel_π_relChainsMapOf {P Q : TopCat} (A : Set P) (B : Set Q) (f : P ⟶ Q)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl P A ≫ f = g ≫ Work.Cohomology.subtypeIncl Q B) :
    cokernel.π (Work.Cohomology.inclChains P A) ≫ Work.Cohomology.relChainsMapOf P Q A B f g w
      = Work.Cohomology.chainMap ℤ P Q f ≫ cokernel.π (Work.Cohomology.inclChains Q B) := by
  unfold Work.Cohomology.relChainsMapOf
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- **The homeomorphism square**: the piece map is conjugate to the middle map. -/
theorem squareHomeo (i : ι) :
    uXChain (f := f) (q := q) i ≫ midChain (f := f) (q := q) i
      = pieceChainMap Y ι f q i ≫ uYChain (f := f) i := by
  have hmain : Work.StemsB.sphHomeoHom (X := TopCat.of (pieceX Y ι f q i))
        (Y := TopCat.of ↥(pullCell (f := f) (q := q) i)) (pieceHomeo (f := f) (q := q) i)
      ≫ TopCat.ofHom (midFun (f := f) (q := q) i)
      = TopCat.ofHom (pieceMap Y ι f q i)
        ≫ Work.StemsB.sphHomeoHom (X := TopCat.of (pieceY Y ι f i))
            (Y := TopCat.of ↥cellInnerOne) (cellInteriorHomeo (f := f) i) := by
    apply TopCat.hom_ext
    ext x
    rfl
  apply (cancel_epi (cokernel.π
    (Work.Cohomology.inclChains (TopCat.of (pieceX Y ι f q i)) (pieceXrel Y ι f q i)))).mp
  have hL : cokernel.π (Work.Cohomology.inclChains (TopCat.of (pieceX Y ι f q i))
          (pieceXrel Y ι f q i))
        ≫ (uXChain (f := f) (q := q) i ≫ midChain (f := f) (q := q) i)
      = Work.Cohomology.chainMap ℤ (TopCat.of (pieceX Y ι f q i))
          (TopCat.of ↥cellInnerOne)
          (Work.StemsB.sphHomeoHom (X := TopCat.of (pieceX Y ι f q i))
            (Y := TopCat.of ↥(pullCell (f := f) (q := q) i)) (pieceHomeo (f := f) (q := q) i)
            ≫ TopCat.ofHom (midFun (f := f) (q := q) i))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥cellInnerOne) innerPunct) := by
    unfold uXChain midChain Work.Serre.SPC.One.pairMap Work.Cohomology.relChainsMapOf
    rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
      Work.Cohomology.cokernel_π_map]
    rw [← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains]
  have hR : cokernel.π (Work.Cohomology.inclChains (TopCat.of (pieceX Y ι f q i))
          (pieceXrel Y ι f q i))
        ≫ (pieceChainMap Y ι f q i ≫ uYChain (f := f) i)
      = Work.Cohomology.chainMap ℤ (TopCat.of (pieceX Y ι f q i))
          (TopCat.of ↥cellInnerOne)
          (TopCat.ofHom (pieceMap Y ι f q i)
            ≫ Work.StemsB.sphHomeoHom (X := TopCat.of (pieceY Y ι f i))
                (Y := TopCat.of ↥cellInnerOne) (cellInteriorHomeo (f := f) i))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥cellInnerOne) innerPunct) := by
    unfold uYChain pieceChainMap Work.Serre.SPC.One.pairMap Work.Cohomology.relChainsMapOf
    rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
      Work.Cohomology.cokernel_π_map]
    rw [← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains]
  rw [hL, hR, hmain]

/-! ## The excision square -/

/-- The restricted pullback covers the punctured part. -/
theorem isOpen_cellInnerOne : IsOpen (cellInnerOne : Set cellD1) :=
  isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem cellInnerOne_union_punctDisc : (cellInnerOne : Set cellD1) ∪ punctDisc = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases h : x ∈ cellInnerOne
    · exact Or.inl h
    · refine Or.inr ?_
      rw [mem_punctDisc]
      intro hx
      exact h (by rw [hx]; exact cellD1Centre_mem_cellInnerOne_pieceTransfer)

theorem isOpen_pullCell (i : ι) : IsOpen (pullCell (f := f) (q := q) i) :=
  isOpen_cellInnerOne.preimage (Work.StemsB.pullbackSnd q (oneCellMap Y ι f i)).continuous

theorem isOpen_pullPunct (i : ι) : IsOpen (pullPunct (f := f) (q := q) i) :=
  isOpen_punctDisc.preimage (Work.StemsB.pullbackSnd q (oneCellMap Y ι f i)).continuous

theorem pullCell_union_pullPunct (i : ι) :
    pullCell (f := f) (q := q) i ∪ pullPunct (f := f) (q := q) i = Set.univ := by
  rw [← Set.preimage_union, cellInnerOne_union_punctDisc, Set.preimage_univ]

/-- **The excision square**: the middle map and the model map agree up to the excision inclusions
of the open cover `{cellInnerOne, punctDisc}` of `D¹`. -/
theorem squareExcision (i : ι) :
    Work.Cohomology.relChainsMap (TopCat.of (pbChar (f := f) (q := q) i))
        (pullCell (f := f) (q := q) i) (pullPunct (f := f) (q := q) i)
      ≫ pmMapOne q (oneCellMap Y ι f i) punctDisc
    = midChain (f := f) (q := q) i
      ≫ Work.Cohomology.relChainsMap (TopCat.of cellD1) cellInnerOne punctDisc := by
  have hmain : Work.Cohomology.subtypeIncl (TopCat.of (pbChar (f := f) (q := q) i))
        (pullCell (f := f) (q := q) i)
      ≫ TopCat.ofHom (Work.StemsB.pullbackSnd q (oneCellMap Y ι f i))
      = TopCat.ofHom (midFun (f := f) (q := q) i)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of cellD1) cellInnerOne := by
    apply TopCat.hom_ext
    ext x
    rfl
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains
    (TopCat.of ↥(pullCell (f := f) (q := q) i))
    (pullCellRel (f := f) (q := q) i)))).mp
  have hL : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(pullCell (f := f) (q := q) i))
          (pullCellRel (f := f) (q := q) i))
        ≫ (Work.Cohomology.relChainsMap (TopCat.of (pbChar (f := f) (q := q) i))
            (pullCell (f := f) (q := q) i) (pullPunct (f := f) (q := q) i)
          ≫ pmMapOne q (oneCellMap Y ι f i) punctDisc)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(pullCell (f := f) (q := q) i))
          (TopCat.of cellD1)
          (Work.Cohomology.subtypeIncl (TopCat.of (pbChar (f := f) (q := q) i))
              (pullCell (f := f) (q := q) i)
            ≫ TopCat.ofHom (Work.StemsB.pullbackSnd q (oneCellMap Y ι f i)))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of cellD1) punctDisc) := by
    unfold Work.Cohomology.relChainsMap pmMapOne Work.Cohomology.relChainsMapOf
    rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
      Work.Cohomology.cokernel_π_map]
    rw [← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains]
  have hR : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(pullCell (f := f) (q := q) i))
          (pullCellRel (f := f) (q := q) i))
        ≫ (midChain (f := f) (q := q) i
          ≫ Work.Cohomology.relChainsMap (TopCat.of cellD1) cellInnerOne punctDisc)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(pullCell (f := f) (q := q) i))
          (TopCat.of cellD1)
          (TopCat.ofHom (midFun (f := f) (q := q) i)
            ≫ Work.Cohomology.subtypeIncl (TopCat.of cellD1) cellInnerOne)
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of cellD1) punctDisc) := by
    unfold midChain Work.Serre.SPC.One.pairMap Work.Cohomology.relChainsMap
      Work.Cohomology.relChainsMapOf
    rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
      Work.Cohomology.cokernel_π_map]
    rw [← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains]
  rw [hL, hR, hmain]

/-! ## The comparison of the two pair maps -/

/-- The two pair maps are conjugate for the `IsIso`-condition in every degree. -/
theorem pieceChainMap_iso_iff_model (i : ι) (k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (pieceChainMap Y ι f q i) k) ↔
      CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (pmMapOne q (oneCellMap Y ι f i) punctDisc) k) := by
  haveI hux : IsIso (uXChain (f := f) (q := q) i) := isIso_uXChain (f := f) (q := q) i
  haveI huy : IsIso (uYChain (f := f) i) := isIso_uYChain (f := f) i
  haveI hux' : IsIso (HomologicalComplex.homologyMap (uXChain (f := f) (q := q) i) k) :=
    inferInstance
  haveI huy' : IsIso (HomologicalComplex.homologyMap (uYChain (f := f) i) k) := inferInstance
  have h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (midChain (f := f) (q := q) i) k) ↔
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (pieceChainMap Y ι f q i) k) := by
    have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ k)
      (squareHomeo (f := f) (q := q) i)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    exact isIso_iff_of_comm_square _ _ _ _ hsq
  haveI hex : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (pbChar (f := f) (q := q) i))
        (pullCell (f := f) (q := q) i) (pullPunct (f := f) (q := q) i)) k) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (pbChar (f := f) (q := q) i))
      (pullCell (f := f) (q := q) i) (pullPunct (f := f) (q := q) i)
      (isOpen_pullCell (f := f) (q := q) i) (isOpen_pullPunct (f := f) (q := q) i)
      (pullCell_union_pullPunct (f := f) (q := q) i) k
  haveI hey : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of cellD1) cellInnerOne punctDisc) k) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of cellD1) cellInnerOne punctDisc
      isOpen_cellInnerOne isOpen_punctDisc cellInnerOne_union_punctDisc k
  have h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (pmMapOne q (oneCellMap Y ι f i) punctDisc) k) ↔
      CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (midChain (f := f) (q := q) i) k) := by
    have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ k)
      (squareExcision (f := f) (q := q) i)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    exact isIso_iff_of_comm_square _ _ _ _ hsq
  exact h1.symm.trans h2.symm

/-- The two pair maps are conjugate for the surjectivity condition in every degree. -/
theorem pieceChainMap_surjective_iff_model (i : ι) (k : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap (pieceChainMap Y ι f q i) k).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap
        (pmMapOne q (oneCellMap Y ι f i) punctDisc) k).hom := by
  haveI hux : IsIso (uXChain (f := f) (q := q) i) := isIso_uXChain (f := f) (q := q) i
  haveI huy : IsIso (uYChain (f := f) i) := isIso_uYChain (f := f) i
  haveI hux' : IsIso (HomologicalComplex.homologyMap (uXChain (f := f) (q := q) i) k) :=
    inferInstance
  haveI huy' : IsIso (HomologicalComplex.homologyMap (uYChain (f := f) i) k) := inferInstance
  have h1 : Function.Surjective (HomologicalComplex.homologyMap
        (midChain (f := f) (q := q) i) k).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap (pieceChainMap Y ι f q i) k).hom := by
    have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ k)
      (squareHomeo (f := f) (q := q) i)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    exact surjective_iff_of_comm_square _ _ _ _ hsq
  haveI hex : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (pbChar (f := f) (q := q) i))
        (pullCell (f := f) (q := q) i) (pullPunct (f := f) (q := q) i)) k) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (pbChar (f := f) (q := q) i))
      (pullCell (f := f) (q := q) i) (pullPunct (f := f) (q := q) i)
      (isOpen_pullCell (f := f) (q := q) i) (isOpen_pullPunct (f := f) (q := q) i)
      (pullCell_union_pullPunct (f := f) (q := q) i) k
  haveI hey : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of cellD1) cellInnerOne punctDisc) k) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of cellD1) cellInnerOne punctDisc
      isOpen_cellInnerOne isOpen_punctDisc cellInnerOne_union_punctDisc k
  have h2 : Function.Surjective (HomologicalComplex.homologyMap
        (pmMapOne q (oneCellMap Y ι f i) punctDisc) k).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap
        (midChain (f := f) (q := q) i) k).hom := by
    have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ k)
      (squareExcision (f := f) (q := q) i)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    exact surjective_iff_of_comm_square _ _ _ _ hsq
  exact h1.symm.trans h2.symm

end

end Work.Serre.SPC.One
