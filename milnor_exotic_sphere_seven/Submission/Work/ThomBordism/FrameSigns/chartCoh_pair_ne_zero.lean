import Mathlib
import Submission.Work.ThomBordism.FrameSigns.Charts
import Submission.Work.ThomBordism.FrameSigns.relKronH_natural
import Submission.Work.Orient.Bridge
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.Cohomology.hmv_naturality
import Submission.Work.ThomBordism.doubleFC.relFactor
import Submission.Work.Cohomology.relChainsMapOf_isIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory

namespace Work.ThomBordism.FrameSigns

noncomputable section

/-!
## The auxiliary geometry of the translated chart

The map `chartTrans V i x hx : z ↦ eᵢ z − eᵢ x` is an open embedding of the chart source into `ℝ⁸`;
its image `chartImg V i x` is open and contains `0`, so the inclusion of pairs
`(chartImg, chartImg ∖ 0) → (ℝ⁸, ℝ⁸∖0)` is an excision and the corestriction of `chartTrans` to its
image is a homeomorphism of pairs.  Consequently the induced map of *relative chain complexes*
`C_*(Uᵢ, Uᵢ∖{x}) → C_*(ℝ⁸, ℝ⁸∖0)` is a quasi-isomorphism (in fact an isomorphism in every degree),
which is what lets the Kronecker pairing with the model class `τ` be moved to the model pair.
-/

/-- The image of the chart target under the translation `v ↦ v - eᵢ x`, i.e. the image of the
translated chart `chartTrans V i x`. -/
def chartImg (V : Man8) (i : ChartIdx V) (x : V.pt) : Set (EuclideanSpace ℝ (Fin 8)) :=
  (fun v => v - chartMap V i x) '' (chartOf V i).1.target

theorem chartTrans_mem_chartImg (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i)
    (z : ↥(src V i)) : chartTrans V i x hx z ∈ chartImg V i x :=
  ⟨chartMap V i (z : V.pt), (chartOf V i).1.map_source z.2, rfl⟩

theorem chartImg_add_mem_target (V : Man8) (i : ChartIdx V) (x : V.pt)
    {w : EuclideanSpace ℝ (Fin 8)} (hw : w ∈ chartImg V i x) :
    w + chartMap V i x ∈ (chartOf V i).1.target := by
  obtain ⟨v, hv, hvw⟩ := hw
  rw [← hvw, sub_add_cancel]
  exact hv

theorem isOpen_chartImg (V : Man8) (i : ChartIdx V) (x : V.pt) : IsOpen (chartImg V i x) := by
  rw [chartImg]
  exact isOpenMap_sub_right (chartMap V i x) _ (chartOf V i).1.open_target

theorem zero_mem_chartImg (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    (0 : EuclideanSpace ℝ (Fin 8)) ∈ chartImg V i x :=
  ⟨chartMap V i x, (chartOf V i).1.map_source hx, sub_self _⟩

theorem chartImg_union_E8p (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    chartImg V i x ∪ E8p = Set.univ := by
  apply Set.eq_univ_of_forall
  intro w
  by_cases h : w = 0
  · exact Or.inl (h ▸ zero_mem_chartImg V i x hx)
  · exact Or.inr h

theorem isOpen_E8p : IsOpen (E8p : Set (EuclideanSpace ℝ (Fin 8))) :=
  isClosed_singleton.isOpen_compl

/-- **`chartTrans` as a homeomorphism of the chart source onto its image.** -/
def chartTransHomeo (V : Man8) (i : ChartIdx V) {x : V.pt} (hx : x ∈ src V i) :
    ↥(src V i) ≃ₜ ↥(chartImg V i x) where
  toFun z := ⟨chartTrans V i x hx z, chartTrans_mem_chartImg V i x hx z⟩
  invFun w := ⟨(chartOf V i).1.symm ((w : EuclideanSpace ℝ (Fin 8)) + chartMap V i x),
    (chartOf V i).1.map_target (chartImg_add_mem_target V i x w.2)⟩
  left_inv z := by
    apply Subtype.ext
    show (chartOf V i).1.symm (chartTrans V i x hx z + chartMap V i x) = (z : V.pt)
    rw [chartTrans_apply, sub_add_cancel]
    exact (chartOf V i).1.left_inv z.2
  right_inv w := by
    apply Subtype.ext
    have hy := chartImg_add_mem_target V i x w.2
    show chartTrans V i x hx
        ⟨(chartOf V i).1.symm ((w : EuclideanSpace ℝ (Fin 8)) + chartMap V i x),
          (chartOf V i).1.map_target hy⟩ = (w : EuclideanSpace ℝ (Fin 8))
    rw [chartTrans_apply, chartMap_apply, (chartOf V i).1.right_inv hy, add_sub_cancel_right]
  continuous_toFun := Continuous.subtype_mk (chartTrans V i x hx).continuous
    (chartTrans_mem_chartImg V i x hx)
  continuous_invFun := by
    have h1 : ContinuousOn (fun y : EuclideanSpace ℝ (Fin 8) => (chartOf V i).1.symm y)
        (chartOf V i).1.target := (chartOf V i).1.continuousOn_symm
    have h2 : ContinuousOn (fun w : EuclideanSpace ℝ (Fin 8) => w + chartMap V i x)
        (chartImg V i x) := (continuous_id.add continuous_const).continuousOn
    have h3 : Set.MapsTo (fun w : EuclideanSpace ℝ (Fin 8) => w + chartMap V i x)
        (chartImg V i x) (chartOf V i).1.target :=
      fun w hw => chartImg_add_mem_target V i x hw
    exact Continuous.subtype_mk (h1.comp h2 h3).domRestrict
      (fun w => (chartOf V i).1.map_target (chartImg_add_mem_target V i x w.2))

/-- The punctured image: the image of the translated chart minus the origin. -/
def chartImgPunct (V : Man8) (i : ChartIdx V) (x : V.pt) : Set ↥(chartImg V i x) :=
  {w | (w : EuclideanSpace ℝ (Fin 8)) ≠ 0}

theorem chartTransHomeo_symm_ne (V : Man8) (i : ChartIdx V) (x : V.pt)
    {w : EuclideanSpace ℝ (Fin 8)} (hw : w ∈ chartImg V i x) (hw0 : w ≠ 0) :
    (chartOf V i).1.symm (w + chartMap V i x) ≠ x := by
  intro h
  apply hw0
  have hy := chartImg_add_mem_target V i x hw
  have h1 : chartMap V i ((chartOf V i).1.symm (w + chartMap V i x)) = w + chartMap V i x := by
    rw [chartMap_apply, (chartOf V i).1.right_inv hy]
  rw [h] at h1
  have h2 : w + chartMap V i x = 0 + chartMap V i x := by simpa using h1.symm
  exact add_right_cancel h2

/-- **`chartTrans` restricted to the punctured chart source**, a homeomorphism onto the punctured
image. -/
def chartTransHomeoPunct (V : Man8) (i : ChartIdx V) {x : V.pt} (hx : x ∈ src V i) :
    ↥(punctSrc V i x) ≃ₜ ↥(chartImgPunct V i x) where
  toFun a := ⟨⟨chartTrans V i x hx a.1, chartTrans_mem_chartImg V i x hx a.1⟩,
    chartTrans_mem V i x hx a.1 a.2⟩
  invFun w := ⟨⟨(chartOf V i).1.symm ((w.1 : EuclideanSpace ℝ (Fin 8)) + chartMap V i x),
      (chartOf V i).1.map_target (chartImg_add_mem_target V i x w.1.2)⟩,
    chartTransHomeo_symm_ne V i x w.1.2 w.2⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    show (chartOf V i).1.symm (chartTrans V i x hx a.1 + chartMap V i x) = (a.1 : V.pt)
    rw [chartTrans_apply, sub_add_cancel]
    exact (chartOf V i).1.left_inv a.1.2
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    have hy := chartImg_add_mem_target V i x w.1.2
    show chartTrans V i x hx
        ⟨(chartOf V i).1.symm ((w.1 : EuclideanSpace ℝ (Fin 8)) + chartMap V i x),
          (chartOf V i).1.map_target hy⟩ = (w.1 : EuclideanSpace ℝ (Fin 8))
    rw [chartTrans_apply, chartMap_apply, (chartOf V i).1.right_inv hy, add_sub_cancel_right]
  continuous_toFun := by
    have hcomp : Continuous (fun a : ↥(punctSrc V i x) =>
        (chartTrans V i x hx ((a : ↥(src V i))) : EuclideanSpace ℝ (Fin 8))) :=
      (chartTrans V i x hx).continuous.comp continuous_subtype_val
    exact Continuous.subtype_mk (Continuous.subtype_mk hcomp
      (fun a => chartTrans_mem_chartImg V i x hx a.1)) (fun a => chartTrans_mem V i x hx a.1 a.2)
  continuous_invFun := by
    have hsub : Continuous (fun w : ↥(chartImgPunct V i x) => (w : ↥(chartImg V i x))) :=
      continuous_subtype_val
    have hinv : Continuous (fun w : ↥(chartImg V i x) =>
        ((chartOf V i).1.symm ((w : EuclideanSpace ℝ (Fin 8)) + chartMap V i x) : V.pt)) :=
      continuous_subtype_val.comp (chartTransHomeo V i hx).continuous_invFun
    exact Continuous.subtype_mk (Continuous.subtype_mk (hinv.comp hsub)
      (fun w => (chartOf V i).1.map_target (chartImg_add_mem_target V i x w.1.2)))
      (fun w => chartTransHomeo_symm_ne V i x w.1.2 w.2)

/-- The corestriction of `chartTrans` to its image, as a `TopCat`-morphism. -/
def chartTransImgMap (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    TopCat.of ↥(src V i) ⟶ TopCat.of ↥(chartImg V i x) :=
  TopCat.ofHom (chartTransHomeo V i hx).toHomotopyEquiv.toFun

/-- The restriction of `chartTrans` to the punctured chart source, as a `TopCat`-morphism. -/
def chartTransImgMapPunct (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    TopCat.of ↥(punctSrc V i x) ⟶ TopCat.of ↥(chartImgPunct V i x) :=
  TopCat.ofHom (chartTransHomeoPunct V i hx).toHomotopyEquiv.toFun

theorem chartTransImgMap_mem (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    ∀ a ∈ punctSrc V i x, chartTransImgMap V i x hx a ∈ chartImgPunct V i x :=
  fun a ha => chartTrans_mem V i x hx a ha

/-- The relative chain map induced by `chartTrans`, corestricted to its image. -/
def chartImgChain (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    Work.Cohomology.relChains (TopCat.of ↥(src V i)) (punctSrc V i x) ⟶
      Work.Cohomology.relChains (TopCat.of ↥(chartImg V i x)) (chartImgPunct V i x) :=
  Work.Cohomology.hmvPairsChains (X₁ := TopCat.of ↥(src V i)) (X₂ := TopCat.of ↥(chartImg V i x))
    (punctSrc V i x) (chartImgPunct V i x)
    (chartTransImgMap V i x hx) (chartTransImgMap_mem V i x hx)

/-- The relative chain map induced by the translated chart, in the spelling of
`Work.ThomBordism.FrameSigns.relKronH_natural`. -/
def chartTransChain (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    Work.Cohomology.relChains (TopCat.of ↥(src V i)) (punctSrc V i x) ⟶
      Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(src V i))
    (TopCat.of (EuclideanSpace ℝ (Fin 8))) (punctSrc V i x) E8p
    (TopCat.ofHom (chartTrans V i x hx))
    (TopCat.ofHom ⟨fun a => ⟨(chartTrans V i x hx) a.1, chartTrans_mem V i x hx a.1 a.2⟩,
      Continuous.subtype_mk ((chartTrans V i x hx).continuous.comp continuous_subtype_val)
        (fun a => chartTrans_mem V i x hx a.1 a.2)⟩)
    (by apply TopCat.hom_ext; ext a; rfl)

/-- The relative chain map induced by the inclusion of the chart source, in the spelling of
`Work.ThomBordism.FrameSigns.relKronH_natural`. -/
def chartSrcChain (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    Work.Cohomology.relChains (TopCat.of ↥(src V i)) (punctSrc V i x) ⟶
      Work.Cohomology.relChains (TopCat.of V.pt) (punct V x) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(src V i)) (TopCat.of V.pt)
    (punctSrc V i x) (punct V x) (TopCat.ofHom (srcIncl V i))
    (TopCat.ofHom ⟨fun a => ⟨(srcIncl V i) a.1, punctSrc_mem V i x a.1 a.2⟩,
      Continuous.subtype_mk ((srcIncl V i).continuous.comp continuous_subtype_val)
        (fun a => punctSrc_mem V i x a.1 a.2)⟩)
    (by apply TopCat.hom_ext; ext a; rfl)

/-- **The chain map of the corestriction of `chartTrans` is a quasi-isomorphism.** -/
theorem isIso_chartImgChain (V : Man8) (i : ChartIdx V) {x : V.pt} (hi : x ∈ src V i) :
    IsIso (HomologicalComplex.homologyMap (chartImgChain V i x hi) 8) := by
  rw [chartImgChain]
  apply Work.Cohomology.relChainsMapOf_homologyMap_isIso
  · intro k
    exact Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv (X := TopCat.of ↥(src V i))
      (Y := TopCat.of ↥(chartImg V i x)) (chartTransHomeo V i hi).toHomotopyEquiv k
  · intro k
    exact Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
      (X := TopCat.of ↥(punctSrc V i x)) (Y := TopCat.of ↥(chartImgPunct V i x))
      (chartTransHomeoPunct V i hi).toHomotopyEquiv k

/-- **The chain-level factorisation of the translated chart through its image.** -/
theorem chartTransChain_factor (V : Man8) (i : ChartIdx V) {x : V.pt} (hi : x ∈ src V i) :
    chartTransChain V i x hi
      = chartImgChain V i x hi
        ≫ Work.Cohomology.relChainsMapOf (TopCat.of ↥(chartImg V i x))
            (TopCat.of (EuclideanSpace ℝ (Fin 8))) (chartImgPunct V i x) E8p
            (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8)))
              (chartImg V i x))
            (Work.Cohomology.inclInterA (TopCat.of (EuclideanSpace ℝ (Fin 8)))
              (chartImg V i x) E8p)
            (by apply TopCat.hom_ext; ext a; rfl) := by
  have w2 : Work.Cohomology.subtypeIncl (TopCat.of ↥(chartImg V i x)) (chartImgPunct V i x)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8))) (chartImg V i x)
      = Work.Cohomology.inclInterA (TopCat.of (EuclideanSpace ℝ (Fin 8))) (chartImg V i x) E8p
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p := by
    apply TopCat.ext
    intro a
    rfl
  have w'' : Work.Cohomology.subtypeIncl (TopCat.of ↥(src V i)) (punctSrc V i x)
        ≫ (chartTransImgMap V i x hi
          ≫ Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8)))
              (chartImg V i x))
      = (Work.Cohomology.relMapSub (punctSrc V i x) (chartImgPunct V i x)
            (chartTransImgMap V i x hi) (chartTransImgMap_mem V i x hi)
          ≫ Work.Cohomology.inclInterA (TopCat.of (EuclideanSpace ℝ (Fin 8)))
              (chartImg V i x) E8p)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p := by
    apply TopCat.ext
    intro a
    rfl
  have hcomp := Work.Cohomology.relChainsMapOf_comp (X := TopCat.of ↥(src V i))
      (Y := TopCat.of ↥(chartImg V i x)) (Z := TopCat.of (EuclideanSpace ℝ (Fin 8)))
      (punctSrc V i x) (chartImgPunct V i x) E8p
      (chartTransImgMap V i x hi)
      (Work.Cohomology.relMapSub (punctSrc V i x) (chartImgPunct V i x)
        (chartTransImgMap V i x hi) (chartTransImgMap_mem V i x hi))
      (Work.Cohomology.relMapSub_spec (punctSrc V i x) (chartImgPunct V i x)
        (chartTransImgMap V i x hi) (chartTransImgMap_mem V i x hi))
      (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8))) (chartImg V i x))
      (Work.Cohomology.inclInterA (TopCat.of (EuclideanSpace ℝ (Fin 8))) (chartImg V i x) E8p)
      w2 w''
  refine (Work.ThomBordism.doubleFC.relChainsMapOf_congr ?_ ?_ _ _).trans hcomp.symm
  · apply TopCat.ext
    intro a
    rfl
  · apply TopCat.ext
    intro a
    rfl

/-- **The chain map of the translated chart is a quasi-isomorphism.** -/
theorem isIso_chartTransChain (V : Man8) (i : ChartIdx V) {x : V.pt} (hi : x ∈ src V i) :
    IsIso (HomologicalComplex.homologyMap (chartTransChain V i x hi) 8) := by
  have h1 : IsIso (HomologicalComplex.homologyMap (chartImgChain V i x hi) 8) :=
    isIso_chartImgChain V i hi
  have h2 : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf (TopCat.of ↥(chartImg V i x))
        (TopCat.of (EuclideanSpace ℝ (Fin 8))) (chartImgPunct V i x) E8p
        (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin 8))) (chartImg V i x))
        (Work.Cohomology.inclInterA (TopCat.of (EuclideanSpace ℝ (Fin 8))) (chartImg V i x) E8p)
        (by apply TopCat.hom_ext; ext a; rfl)) 8) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (EuclideanSpace ℝ (Fin 8)))
      (chartImg V i x) E8p (isOpen_chartImg V i x) isOpen_E8p (chartImg_union_E8p V i x hi) 8
  rw [chartTransChain_factor V i hi, HomologicalComplex.homologyMap_comp]
  haveI := h1
  haveI := h2
  infer_instance

/-- **The chain map of the inclusion of the chart source is a quasi-isomorphism** (excision). -/
theorem isIso_chartSrcChain (V : Man8) (i : ChartIdx V) {x : V.pt} (hi : x ∈ src V i) :
    IsIso (HomologicalComplex.homologyMap (chartSrcChain V i x hi) 8) := by
  have hcov : src V i ∪ punct V x = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hy : y ∈ src V i
    · exact Or.inl hy
    · exact Or.inr (by simp only [punct, Set.mem_setOf_eq]; intro hyx; exact hy (hyx ▸ hi))
  rw [chartSrcChain]
  exact Work.Cohomology.excision_relChainsMap_isIso (TopCat.of V.pt) (src V i) (punct V x)
    (chartOf V i).1.open_source (isOpen_punct V x) hcov 8

/-- **Naturality of the relative Kronecker pairing for the inclusion of the chart source.** -/
theorem relKronH_natural_srcIncl (V : Man8) (i : ChartIdx V) {x : V.pt} (hi : x ∈ src V i)
    (b : Work.Thom.RelCoh ℤ 8 V.pt (punct V x))
    (z : ↥((Work.Cohomology.relChains (TopCat.of ↥(src V i)) (punctSrc V i x)).homology 8)) :
    (Work.Tubular.relKronH (TopCat.of ↥(src V i)) (punctSrc V i x) 8)
        ((Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
          (punctSrc_mem V i x) ℤ 8).hom b) z
      = (Work.Tubular.relKronH (TopCat.of V.pt) (punct V x) 8) b
          ((HomologicalComplex.homologyMap (chartSrcChain V i x hi) 8).hom z) :=
  relKronH_natural (X := TopCat.of ↥(src V i)) (Y := TopCat.of V.pt)
    (A := punctSrc V i x) (B := punct V x) (srcIncl V i) (punctSrc_mem V i x) 8 b z

/-- **Naturality of the relative Kronecker pairing for the translated chart.** -/
theorem relKronH_natural_chartTrans (V : Man8) (i : ChartIdx V) {x : V.pt} (hi : x ∈ src V i)
    (b : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) E8p)
    (z : ↥((Work.Cohomology.relChains (TopCat.of ↥(src V i)) (punctSrc V i x)).homology 8)) :
    (Work.Tubular.relKronH (TopCat.of ↥(src V i)) (punctSrc V i x) 8)
        ((Work.Thom.relCohMap (chartTrans V i x hi) (punctSrc V i x) E8p
          (chartTrans_mem V i x hi) ℤ 8).hom b) z
      = (Work.Tubular.relKronH (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p 8) b
          ((HomologicalComplex.homologyMap (chartTransChain V i x hi) 8).hom z) :=
  relKronH_natural (X := TopCat.of ↥(src V i))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin 8)))
    (A := punctSrc V i x) (B := E8p) (chartTrans V i x hi) (chartTrans_mem V i x hi) 8 b z

/-- **The local class of the fundamental class of a closed `8`-manifold at a point is nonzero.** -/
theorem locClass_ne_zero (V : Man8) (x : V.pt) :
    Work.Orient.locClass (TopCat.of V.pt) 8 V.c x ≠ 0 := by
  intro hc
  have htop : Submodule.span ℤ
      ({Work.Orient.locClass (TopCat.of V.pt) 8 V.c x} :
        Set (Work.Orient.LocH (TopCat.of V.pt) 8 x)) = ⊤ := V.c_fund x
  have h0 : Submodule.span ℤ
      ({Work.Orient.locClass (TopCat.of V.pt) 8 V.c x} :
        Set (Work.Orient.LocH (TopCat.of V.pt) 8 x)) = ⊥ := by
    rw [hc, Submodule.span_singleton_eq_bot]
  have hbot : (⊥ : Submodule ℤ (Work.Orient.LocH (TopCat.of V.pt) 8 x)) = ⊤ := by
    rw [← h0]; exact htop
  haveI : Subsingleton (Work.Orient.LocH (TopCat.of V.pt) 8 x) := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Submodule ℤ (Work.Orient.LocH (TopCat.of V.pt) 8 x)) := by
      rw [hbot]; exact Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule ℤ (Work.Orient.LocH (TopCat.of V.pt) 8 x)) := by
      rw [hbot]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  obtain ⟨e⟩ := Work.Cohomology.localHomology 8 (by norm_num) V.pt x
  have h2 : (ConcreteCategory.hom e.inv) (1 : ℤ) = 0 := Subsingleton.elim _ _
  have h3 := Iso.inv_hom_id_apply e (1 : ℤ)
  rw [h2, map_zero] at h3
  exact one_ne_zero h3.symm

/-- **The Kronecker pairing of the chart class with the local fundamental class does not vanish.**

This is what makes `frameSign` a genuine sign (`±1` independent of any convention).

Route.  Let `M := TopCat.of V.pt`, `c := Work.Orient.locClass M 8 V.c x`, and
`G := chartCoh V i x hi`.  By `Work.ThomBordism.FrameSigns.relKronH_natural` for the pair map
`srcIncl V i : (↥(src V i), (src V i)∖{x}) → (M, punct V x)`, and the fact that its homology
pushforward is an isomorphism (`Work.Cohomology.excision_relChainsMap_isIso`),

  `⟨G, c⟩ = ⟨(chartTrans V i x hi)^* τ, z⟩`  with `z := (pushforward)⁻¹ c`,

and then `⟨(chartTrans V i x hi)^* τ, z⟩ = ⟨τ, (chartTrans V i x hi)_* z⟩`.  Since `c ≠ 0` (it
generates the local group `LocH M 8 x ≅ ℤ` by `Man8.isFundClass`, and that group is nontrivial, e.g.
by `Work.Cohomology.localHomology`), `z ≠ 0`; and `(chartTrans V i x hi)_*` is injective because
`chartTrans V i x hi` is a homeomorphism of the pair `(↥(src V i), (src V i)∖{x})` onto
`(chartImg V i x, chartImg V i x ∖ {0})` (`Work.Cohomology.relChainsMapOf_homologyMap_isIso` with
the homeomorphism `chartTransHomeo`), so `(chartTrans V i x hi)_* z ≠ 0`.  Finally `⟨τ, −⟩ = dual0`
is injective (`Work.ThomBordism.FrameSigns.tau_pair_ne_zero`). -/
theorem chartCoh_pair_ne_zero (V : Man8) (i : ChartIdx V) {x : V.pt} (hi : x ∈ src V i) :
    (Work.Tubular.relKronH (TopCat.of V.pt) (punct V x) 8) (chartCoh V i x hi)
      (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) ≠ 0 := by
  haveI hExc : IsIso (HomologicalComplex.homologyMap (chartSrcChain V i x hi) 8) :=
    isIso_chartSrcChain V i hi
  haveI hTrans : IsIso (HomologicalComplex.homologyMap (chartTransChain V i x hi) 8) :=
    isIso_chartTransChain V i hi
  let cc : ↥((Work.Cohomology.relChains (TopCat.of V.pt) (punct V x)).homology 8) :=
    Work.Orient.locClass (TopCat.of V.pt) 8 V.c x
  have hcc : cc ≠ 0 := by
    show Work.Orient.locClass (TopCat.of V.pt) 8 V.c x ≠ 0
    exact locClass_ne_zero V x
  let zX : ↥((Work.Cohomology.relChains (TopCat.of ↥(src V i))
      (punctSrc V i x)).homology 8) :=
    ((CategoryTheory.inv (HomologicalComplex.homologyMap (chartSrcChain V i x hi) 8)).hom) cc
  have hzXc : (HomologicalComplex.homologyMap (chartSrcChain V i x hi) 8).hom zX = cc := by
    have h := congrArg (fun (k : (Work.Cohomology.relChains (TopCat.of V.pt)
        (punct V x)).homology 8 ⟶ (Work.Cohomology.relChains (TopCat.of V.pt)
        (punct V x)).homology 8) => k.hom cc)
      (CategoryTheory.IsIso.inv_hom_id (HomologicalComplex.homologyMap (chartSrcChain V i x hi) 8))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h
  have hzX_ne : zX ≠ 0 := by
    intro hz
    exact hcc (by rw [← hzXc, hz, map_zero])
  have hzX2 : (HomologicalComplex.homologyMap (chartTransChain V i x hi) 8).hom zX ≠ 0 := by
    intro h
    have hinj : Function.Injective
        (HomologicalComplex.homologyMap (chartTransChain V i x hi) 8).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact hzX_ne (hinj (by rw [h, map_zero]))
  have hG : (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
        (punctSrc_mem V i x) ℤ 8).hom (chartCoh V i x hi)
      = (Work.Thom.relCohMap (chartTrans V i x hi) (punctSrc V i x) E8p
          (chartTrans_mem V i x hi) ℤ 8).hom tau := by
    haveI : IsIso (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
        (punctSrc_mem V i x) ℤ 8) := isIso_exc V i x hi
    have h := congrArg (fun (k : Work.Thom.RelCoh ℤ 8 (↥(src V i)) (punctSrc V i x) ⟶
        Work.Thom.RelCoh ℤ 8 (↥(src V i)) (punctSrc V i x)) => k.hom
          ((Work.Thom.relCohMap (chartTrans V i x hi) (punctSrc V i x) E8p
            (chartTrans_mem V i x hi) ℤ 8).hom tau))
      (CategoryTheory.IsIso.inv_hom_id (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x)
        (punct V x) (punctSrc_mem V i x) ℤ 8))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at h
    rw [chartCoh]
    exact h
  have hpair1 : (Work.Tubular.relKronH (TopCat.of V.pt) (punct V x) 8) (chartCoh V i x hi) cc
      = (Work.Tubular.relKronH (TopCat.of ↥(src V i)) (punctSrc V i x) 8)
          ((Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
            (punctSrc_mem V i x) ℤ 8).hom (chartCoh V i x hi)) zX := by
    have hnat := relKronH_natural_srcIncl V i hi (chartCoh V i x hi) zX
    rw [hzXc] at hnat
    exact hnat.symm
  have hpair2 : (Work.Tubular.relKronH (TopCat.of ↥(src V i)) (punctSrc V i x) 8)
        ((Work.Thom.relCohMap (chartTrans V i x hi) (punctSrc V i x) E8p
          (chartTrans_mem V i x hi) ℤ 8).hom tau) zX
      = (Work.Tubular.relKronH (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p 8) tau
          ((HomologicalComplex.homologyMap (chartTransChain V i x hi) 8).hom zX) :=
    relKronH_natural_chartTrans V i hi tau zX
  show (Work.Tubular.relKronH (TopCat.of V.pt) (punct V x) 8) (chartCoh V i x hi) cc ≠ 0
  rw [hpair1, hG, hpair2]
  exact tau_pair_ne_zero hzX2

end

end Work.ThomBordism.FrameSigns
