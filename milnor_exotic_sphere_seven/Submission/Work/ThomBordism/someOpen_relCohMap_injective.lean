import Mathlib
import Submission.Work.ThomBordism.collapseM4Defs
import Submission.Work.ThomBordism.ambientBase
import Submission.Work.ThomBordism.eucSliceClass_existsV2
import Submission.Work.Thom.ATools

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The excision step

The first input is the standard excision fact: if `U, A` are open subsets covering `X`, then the
inclusion of pairs `(U, U ∩ A) → (X, A)` induces an *isomorphism* on relative cohomology, hence in
particular an injection.  This is `Work.Cohomology.capRel_excision_isIso`, transported to the
`Work.Thom.relCohMap` spelling of the pullback. -/

theorem relCohMap_subtypeIncl_injective {X : Type} [TopologicalSpace X] (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcov : U ∪ A = Set.univ) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
      ({y : ↥U | (y : X) ∈ A}) A (fun _ hx => hx) ℤ n)) := by
  have hiso : CategoryTheory.IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
      ({y : ↥U | (y : X) ∈ A}) A (fun _ hx => hx) ℤ n) :=
    Work.Cohomology.capRel_excision_isIso (TopCat.of X) U A hU hA hcov n (fun _ hx => hx)
  exact ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hiso).1

/-! ## The open tube inside the one-point compactification -/

/-- The open tube of a tube chart, viewed as a subset of the one-point compactification of the
ambient Euclidean space. -/
def someTubeSet (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : Set (OnePoint (Work.Tubular.Euc (8 + k))) :=
  OnePoint.some '' C.openTube

/-- The punctured open tube inside the one-point compactification. -/
def someTubePtsSet (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) : Set ↥(someTubeSet E C) :=
  {y | (y : OnePoint (Work.Tubular.Euc (8 + k))) ∈
    ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))}

theorem isOpen_someTubeSet (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : IsOpen (someTubeSet E C) :=
  OnePoint.isOpenEmbedding_coe.isOpenMap C.openTube C.openTube_isOpen

/-- The inclusion of the open tube into its image inside the one-point compactification. -/
def someTubeIncl (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    C(↥C.openTube, ↥(someTubeSet E C)) :=
  ⟨fun z => ⟨OnePoint.some z.1, z.1, z.2, rfl⟩,
    Continuous.subtype_mk (OnePoint.continuous_coe.comp continuous_subtype_val) _⟩

theorem someTubeIncl_coe (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (z : ↥C.openTube) :
    ((someTubeIncl E C z : ↥(someTubeSet E C)) : OnePoint (Work.Tubular.Euc (8 + k)))
      = OnePoint.some z.1 := rfl

/-- The inverse of `someTubeIncl`: a point of the image knows the point of the open tube. -/
def someTubeInvFun (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (w : ↥(someTubeSet E C)) : ↥C.openTube :=
  ⟨Classical.choose ((Set.mem_image OnePoint.some C.openTube
      (w : OnePoint (Work.Tubular.Euc (8 + k)))).mp w.2),
   (Classical.choose_spec ((Set.mem_image OnePoint.some C.openTube
      (w : OnePoint (Work.Tubular.Euc (8 + k)))).mp w.2)).1⟩

theorem someTubeInvFun_coe (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (w : ↥(someTubeSet E C)) :
    OnePoint.some ((someTubeInvFun E C w : ↥C.openTube) : Work.Tubular.Euc (8 + k))
      = (w : OnePoint (Work.Tubular.Euc (8 + k))) :=
  (Classical.choose_spec ((Set.mem_image OnePoint.some C.openTube
      (w : OnePoint (Work.Tubular.Euc (8 + k)))).mp w.2)).2

theorem continuous_someTubeInvFun (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : Continuous (someTubeInvFun E C) := by
  have hsome : (fun w : ↥(someTubeSet E C) =>
        OnePoint.some ((someTubeInvFun E C w : ↥C.openTube) : Work.Tubular.Euc (8 + k)))
      = (fun w : ↥(someTubeSet E C) => (w : OnePoint (Work.Tubular.Euc (8 + k)))) := by
    funext w
    exact someTubeInvFun_coe E C w
  have hcont1 : Continuous (fun w : ↥(someTubeSet E C) =>
      OnePoint.some ((someTubeInvFun E C w : ↥C.openTube) : Work.Tubular.Euc (8 + k))) := by
    rw [hsome]
    exact continuous_subtype_val
  have hcont2 : Continuous (fun w : ↥(someTubeSet E C) =>
      ((someTubeInvFun E C w : ↥C.openTube) : Work.Tubular.Euc (8 + k))) :=
    (Topology.IsInducing.continuous_iff
      (f := fun w : ↥(someTubeSet E C) =>
        ((someTubeInvFun E C w : ↥C.openTube) : Work.Tubular.Euc (8 + k)))
      (g := (OnePoint.some : Work.Tubular.Euc (8 + k) → OnePoint (Work.Tubular.Euc (8 + k))))
      OnePoint.isOpenEmbedding_coe.toIsEmbedding.isInducing).mpr hcont1
  exact Continuous.subtype_mk hcont2 _

/-- The canonical bijection between the open tube and its image in the one-point
compactification, as a continuous map. -/
def someTubeInv (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    C(↥(someTubeSet E C), ↥C.openTube) :=
  ⟨someTubeInvFun E C, continuous_someTubeInvFun E C⟩

theorem someTubeInv_apply (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (w : ↥(someTubeSet E C)) :
    someTubeInv E C w = someTubeInvFun E C w := rfl

theorem someTubeIncl_someTubeInv (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (w : ↥(someTubeSet E C)) :
    someTubeIncl E C (someTubeInv E C w) = w := by
  apply Subtype.ext
  rw [someTubeIncl_coe]
  exact someTubeInvFun_coe E C w

theorem someTubeInv_someTubeIncl (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (z : ↥C.openTube) :
    someTubeInv E C (someTubeIncl E C z) = z := by
  have h : OnePoint.some ((someTubeInvFun E C (someTubeIncl E C z) : ↥C.openTube) :
        Work.Tubular.Euc (8 + k))
      = OnePoint.some ((z : ↥C.openTube) : Work.Tubular.Euc (8 + k)) := by
    rw [someTubeInvFun_coe, someTubeIncl_coe]
  exact Subtype.ext (OnePoint.coe_injective h)

theorem someTubeIncl_mem_pts (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ openTubePtset E C x, someTubeIncl E C y ∈ someTubePtsSet E C x :=
  fun y hy hcon => hy (OnePoint.coe_injective (by
    rw [someTubeIncl_coe] at hcon
    exact hcon))

/-! ## Injectivity of the pullback along `someTubeIncl` -/

theorem relCohMap_someTubeIncl_injective (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap (someTubeIncl E C)
      (openTubePtset E C x) (someTubePtsSet E C x) (someTubeIncl_mem_pts E C x) ℤ n)) := by
  have hf : ∀ y ∈ someTubePtsSet E C x, someTubeInv E C y ∈ openTubePtset E C x := by
    intro y hy hcon
    refine hy ?_
    rw [Set.mem_singleton_iff]
    rw [someTubeInv_apply] at hcon
    exact (someTubeInvFun_coe E C y).symm.trans (congrArg OnePoint.some hcon)
  have hg : ∀ y ∈ openTubePtset E C x, someTubeIncl E C y ∈ someTubePtsSet E C x :=
    someTubeIncl_mem_pts E C x
  have hgf : ∀ y ∈ someTubePtsSet E C x, someTubeIncl E C (someTubeInv E C y) ∈
      someTubePtsSet E C x := by
    intro y hy
    rwa [someTubeIncl_someTubeInv E C y]
  have hcomp := Work.Thom.relCohMap_compA (someTubePtsSet E C x) (openTubePtset E C x)
    (someTubePtsSet E C x) (someTubeInv E C) (someTubeIncl E C) hf hg hgf ℤ n
  have hcomp' : CategoryTheory.CategoryStruct.comp
      (Work.Thom.relCohMap (someTubeIncl E C) (openTubePtset E C x) (someTubePtsSet E C x)
        (someTubeIncl_mem_pts E C x) ℤ n)
      (Work.Thom.relCohMap (someTubeInv E C) (someTubePtsSet E C x) (openTubePtset E C x) hf ℤ n)
      = 𝟙 (Work.Thom.RelCoh ℤ n ↥(someTubeSet E C) (someTubePtsSet E C x)) := by
    refine hcomp.trans ?_
    have hcomp_id : (someTubeIncl E C).comp (someTubeInv E C)
        = ContinuousMap.id ↥(someTubeSet E C) :=
      ContinuousMap.ext (fun w => someTubeIncl_someTubeInv E C w)
    refine (Work.Thom.relCohMap_congrA (someTubePtsSet E C x) (someTubePtsSet E C x) hcomp_id hgf
      (fun _ hx => hx) ℤ n).trans ?_
    exact Work.Thom.relCohMap_idA (someTubePtsSet E C x) ℤ n
  have hlin : (Work.Thom.relCohMap (someTubeInv E C) (someTubePtsSet E C x)
        (openTubePtset E C x) hf ℤ n).hom.comp
      (Work.Thom.relCohMap (someTubeIncl E C) (openTubePtset E C x) (someTubePtsSet E C x)
        (someTubeIncl_mem_pts E C x) ℤ n).hom
      = LinearMap.id := by
    have := congrArg (fun φ : Work.Thom.RelCoh ℤ n ↥(someTubeSet E C) (someTubePtsSet E C x) ⟶
        Work.Thom.RelCoh ℤ n ↥(someTubeSet E C) (someTubePtsSet E C x) => φ.hom) hcomp'
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  intro a b hab
  have ha := LinearMap.congr_fun hlin a
  have hb := LinearMap.congr_fun hlin b
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
  rw [hab] at ha
  exact ha.symm.trans hb

/-! ## The main theorem -/

theorem someOpen_relCohMap_injective {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap (Work.ThomBordism.someOpen E C)
      (Work.ThomBordism.openTubePtset E C x)
      ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
      (Work.ThomBordism.someOpen_mem E C x) ℤ n)) := by
  classical
  have hU : IsOpen (someTubeSet E C) := isOpen_someTubeSet E C
  have hA : IsOpen ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))) := by
    rw [show ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        = (OnePoint.some '' ({E.e x} : Set (Work.Tubular.Euc (8 + k))))ᶜ by simp]
    exact (OnePoint.isClosed_image_coe.mpr ⟨isClosed_singleton, isCompact_singleton⟩).isOpen_compl
  have hcov : someTubeSet E C ∪ ({OnePoint.some (E.e x)}ᶜ :
      Set (OnePoint (Work.Tubular.Euc (8 + k)))) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    by_cases hy : y = OnePoint.infty
    · refine Or.inr ?_
      rw [Set.mem_compl_iff, Set.mem_singleton_iff, hy]
      exact (OnePoint.coe_ne_infty (E.e x)).symm
    · have hy' : y ∈ Set.range (OnePoint.some :
          Work.Tubular.Euc (8 + k) → OnePoint (Work.Tubular.Euc (8 + k))) := by
        rw [← OnePoint.compl_infty]
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact hy
      obtain ⟨z, rfl⟩ := Set.mem_range.mp hy'
      by_cases hz : z ∈ C.openTube
      · exact Or.inl ⟨z, hz, rfl⟩
      · refine Or.inr ?_
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact fun h => hz (by rw [OnePoint.coe_injective h]; exact C.mem_openTube x)
  have hinj1 : Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(someTubeSet E C), OnePoint (Work.Tubular.Euc (8 + k))))
      (someTubePtsSet E C x)
      ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
      (fun _ hx => hx) ℤ n)) :=
    relCohMap_subtypeIncl_injective (someTubeSet E C)
      ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))) hU hA hcov n
  have hinj2 : Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap (someTubeIncl E C)
      (openTubePtset E C x) (someTubePtsSet E C x) (someTubeIncl_mem_pts E C x) ℤ n)) :=
    relCohMap_someTubeIncl_injective E C x n
  have hfac : Work.ThomBordism.someOpen E C
      = (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(someTubeSet E C), OnePoint (Work.Tubular.Euc (8 + k)))).comp
        (someTubeIncl E C) := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hkey : Work.Thom.relCohMap (Work.ThomBordism.someOpen E C) (openTubePtset E C x)
      ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
      (Work.ThomBordism.someOpen_mem E C x) ℤ n
      = CategoryTheory.CategoryStruct.comp
        (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(someTubeSet E C), OnePoint (Work.Tubular.Euc (8 + k))))
          (someTubePtsSet E C x)
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
          (fun _ hx => hx) ℤ n)
        (Work.Thom.relCohMap (someTubeIncl E C) (openTubePtset E C x) (someTubePtsSet E C x)
          (someTubeIncl_mem_pts E C x) ℤ n) :=
    (Work.Thom.relCohMap_congrA (openTubePtset E C x)
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))) hfac
        (Work.ThomBordism.someOpen_mem E C x) (someTubeIncl_mem_pts E C x) ℤ n).trans
      (Work.Thom.relCohMap_compA (openTubePtset E C x) (someTubePtsSet E C x)
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        (someTubeIncl E C)
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(someTubeSet E C), OnePoint (Work.Tubular.Euc (8 + k))))
        (someTubeIncl_mem_pts E C x) (fun _ hx => hx) (someTubeIncl_mem_pts E C x) ℤ n).symm
  rw [hkey, ModuleCat.hom_comp]
  exact fun a b hab => hinj1 (hinj2 hab)

end

end Work.ThomBordism
