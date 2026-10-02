import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.Orient.Boundary.LocalClassConstantOnBall
import Submission.Work.Orient.Boundary.HalfCoverGlue
import Submission.Work.Orient.Port.Hatcher
import Submission.Work.Orient.Boundary.IsRelFundClassOfCore
import Submission.Work.Orient.Bridge
import Submission.Work.Orient.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Generating witnesses for a relative class of a compact manifold with boundary

`Work.ThomBordism.piecesBound_generatingWitnesses`: let `W` be a compact `T2` space charted in the
half-space model `EuclideanHalfSpace 9`, `γ` a **half-orientation family** of `W`
(`Work.Orient.IsHalfOrientationFamily 8 W`: local generators of `H₉(W, W∖{x})` at every interior
point, locally coherent over coordinate half-balls of the interior), and let
`w₁ ∈ H₉(W, ∂W)` be *any* relative class.  Then there is a family `Ψ` of local classes, one at each
interior point, given by the **local generation test** on `w₁`:

    Ψ x = the local class of `w₁` at `x`   if that class generates the local group,
    Ψ x = γ x                              otherwise,

and `Ψ` has the two properties that make it usable as the input of the local-to-global gluing lemma
`Work.ThomBordism.piecesBound_relClass_of_witnesses`:

* `Ψ x` generates the local group at every interior point `x`;
* around every interior point `x` the family `Ψ` is the restriction of a **single** class
  `a ∈ H₉(W, W∖U)` over an open neighbourhood `U ⊆ W°` of `x`.

The mathematical content is that the *generation test* for `w₁` is locally constant on interior
coordinate half-balls (`Work.Orient.Boundary.LocalClassConstantOnBall`): on a half-ball `K ⊆ W°`
either the local class of `w₁` generates at every point of `K` or at none, so the class cut out by
`w₁` on a small half-ball is a legitimate witness on the generating locus, and outside it the
coherence class of `γ` is.  This is the first half of the existence proof of the relative
fundamental class of a family of boundary pieces that bound; it is separated here because the same
prescription is reused for every relative class `w₁` (in particular the one produced by the pair
sequence from a null-homologous boundary).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.ThomBordism

noncomputable section

/-- **The localisation of a relative class `w ∈ H₉(W, ∂W)` at an interior point `x`**: the image of
`w` under `C_*(W, ∂W) ⟶ C_*(W, W∖{x})` in homology, i.e. the map of the field
`Work.ThomBordism.NullBordismFamily.w_fund`. -/
abbrev genLocClass {W : Type} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W]
    (w : (Work.Cohomology.relChains (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9)
    (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W) :
    Work.Orient.LocH (TopCat.of W) 9 x :=
  (HomologicalComplex.homologyMap
    (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom w

theorem piecesBound_generatingWitnesses
    {W : Type} [TopologicalSpace W] [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      Work.Orient.LocH (TopCat.of W) 9 x)
    (hγ : Work.Orient.IsHalfOrientationFamily 8 (TopCat.of W) γ)
    (w₁ : (Work.Cohomology.relChains (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9) :
    ∃ Ψ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
        Work.Orient.LocH (TopCat.of W) 9 x,
      (∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
        Ψ x hx = (if Submodule.span ℤ {((HomologicalComplex.homologyMap
              (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
                ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom w₁)} = ⊤
            then (HomologicalComplex.homologyMap
              (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
                ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom w₁
            else γ x hx)) ∧
      (∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
        Submodule.span ℤ {Ψ x hx} = ⊤) ∧
      (∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
        ∃ U : Set W, x ∈ U ∧ U ⊆ {y : W |
            y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W} ∧ IsOpen U ∧
          ∃ a : Work.Orient.RelH (TopCat.of W) 9 U,
            ∀ y (hyU : y ∈ U) (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
              Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hyU) a
                = Ψ y hy) := by
  classical
  -- The boundary is closed, so the interior is an open set.
  have hBclosed : IsClosed ((modelWithCornersEuclideanHalfSpace 9).boundary W) :=
    ModelWithCorners.isClosed_boundary (I := modelWithCornersEuclideanHalfSpace 9)
      (M := W) (n := (1 : WithTop ENat)) one_ne_zero
  -- The prescribed family of local classes.
  let Ψ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      Work.Orient.LocH (TopCat.of W) 9 x :=
    fun x hx => if Submodule.span ℤ ({genLocClass w₁ x hx} :
        Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤ then genLocClass w₁ x hx else γ x hx
  -- Unfolding of `Ψ` on the generating locus.
  have hΨ_eq : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      Submodule.span ℤ ({genLocClass w₁ x hx} :
          Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤ →
      Ψ x hx = genLocClass w₁ x hx := by
    intro x hx hg
    show (if Submodule.span ℤ ({genLocClass w₁ x hx} :
        Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤
      then genLocClass w₁ x hx else γ x hx) = _
    rw [if_pos hg]
  -- `Ψ` generates the local group everywhere.
  have hΨ_gen : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      Submodule.span ℤ {Ψ x hx} = ⊤ := by
    intro x hx
    by_cases hg : Submodule.span ℤ ({genLocClass w₁ x hx} :
        Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤
    · show Submodule.span ℤ ({(if Submodule.span ℤ ({genLocClass w₁ x hx} :
          Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤
        then genLocClass w₁ x hx else γ x hx)} :
          Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤
      rw [if_pos hg]; exact hg
    · show Submodule.span ℤ ({(if Submodule.span ℤ ({genLocClass w₁ x hx} :
          Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤
        then genLocClass w₁ x hx else γ x hx)} :
          Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤
      rw [if_neg hg]; exact hγ.1 x hx
  -- The generation test for `w₁` is constant on an interior coordinate half-ball.
  have hgen_const : ∀ (z : W) (hz : z ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W)
      (r : ℝ) (hr : 0 < r)
      (hgood : Work.Orient.halfBallGood 9 (TopCat.of W) z r)
      (hint : ∀ y ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) z r,
        y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      ∀ y ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) z r,
        ∀ (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
        (Submodule.span ℤ {genLocClass w₁ y hy} = ⊤ ↔
          Submodule.span ℤ {genLocClass w₁ z hz} = ⊤) := by
    intro z hz r hr hgood hint y hyK hy
    have h1 := Work.Orient.Boundary.LocalClassConstantOnBall 8 (TopCat.of W) z r hr hgood
      hint w₁ z y (Work.Orient.mem_halfBallPiece_center (W := TopCat.of W) (z := z)
        (r := r) hr) hyK
    have h2 : (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) z hz) 9).hom w₁
        = genLocClass w₁ z hz := by
      show (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) z hz) 9).hom w₁
        = (HomologicalComplex.homologyMap
          (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W) z hz) 9).hom w₁
      rw [Work.Orient.relPunct_eq_relChainsInclPunct]
    have h3 : (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) y hy) 9).hom w₁
        = genLocClass w₁ y hy := by
      show (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) y hy) 9).hom w₁
        = (HomologicalComplex.homologyMap
          (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W) y hy) 9).hom w₁
      rw [Work.Orient.relPunct_eq_relChainsInclPunct]
    rw [h2, h3] at h1
    exact h1.symm
  -- The local witnesses for `Ψ`.
  have hwit : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      ∃ U : Set W, x ∈ U ∧ U ⊆ {y : W |
          y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W} ∧ IsOpen U ∧
        ∃ a : Work.Orient.RelH (TopCat.of W) 9 U,
          ∀ y (hyU : y ∈ U) (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
            Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hyU) a = Ψ y hy := by
    intro x hx
    have hUopen : IsOpen (((modelWithCornersEuclideanHalfSpace 9).boundary W))ᶜ :=
      hBclosed.isOpen_compl
    obtain ⟨r, hr, hgood, hsub⟩ := Work.Orient.Boundary.exists_halfBall_subset 8
      (W := TopCat.of W) hUopen hx
    obtain ⟨U, hUK, hUopen', hxU⟩ :=
      mem_nhds_iff.mp (Work.Orient.Boundary.halfBallPiece_mem_nhds (n := 8) (W := TopCat.of W)
        (z := x) (r := r) hr)
    have hKint : ∀ y ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) x r,
        y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W := fun y hy => hsub hy
    by_cases hg : Submodule.span ℤ ({genLocClass w₁ x hx} :
        Set (Work.Orient.LocH (TopCat.of W) 9 x)) = ⊤
    · -- generating case: the witness is the localisation of `w₁`
      have hBle : (modelWithCornersEuclideanHalfSpace 9).boundary W ⊆ Uᶜ := by
        intro z hz hzU
        exact (hKint z (hUK hzU)) hz
      refine ⟨U, hxU, fun z hz => hsub (hUK hz), hUopen', ?_⟩
      refine ⟨(HomologicalComplex.homologyMap
        (Work.Orient.relChainsIncl (TopCat.of W) hBle) 9).hom w₁, ?_⟩
      intro y hyU hy
      have hyK : y ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) x r := hUK hyU
      have hΨy : Ψ y hy = genLocClass w₁ y hy :=
        hΨ_eq y hy ((hgen_const x hx r hr hgood hKint y hyK hy).mpr hg)
      rw [hΨy]
      have hpt : ({y} : Set W) ⊆ U := Set.singleton_subset_iff.mpr hyU
      have hp : (modelWithCornersEuclideanHalfSpace 9).boundary W ⊆ ({t : W | t ≠ y}) :=
        fun z hz hzy => hy (hzy ▸ hz)
      have e1 : Work.Orient.resRelH (TopCat.of W) 9 hpt
          = (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of W)
              (Set.compl_subset_compl.mpr hpt)) 9).hom :=
        Work.Orient.resRelH_eq_homologyMap_relChainsIncl (TopCat.of W) 9 hpt
      have e2 : (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of W)
              (Set.compl_subset_compl.mpr hpt)) 9).hom
            ((HomologicalComplex.homologyMap
              (Work.Orient.relChainsIncl (TopCat.of W) hBle) 9).hom w₁)
          = (HomologicalComplex.homologyMap
              (Work.Orient.relChainsIncl (TopCat.of W) hBle
                ≫ Work.Orient.relChainsIncl (TopCat.of W)
                  (Set.compl_subset_compl.mpr hpt)) 9).hom w₁ := by
        rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
      have e3 : Work.Orient.relChainsIncl (TopCat.of W) hBle
              ≫ Work.Orient.relChainsIncl (TopCat.of W) (Set.compl_subset_compl.mpr hpt)
            = Work.Orient.relChainsIncl (TopCat.of W) (hBle.trans (Set.compl_subset_compl.mpr hpt)) :=
        Work.Orient.relChainsIncl_trans (TopCat.of W) hBle (Set.compl_subset_compl.mpr hpt)
      have e4 : Work.Orient.relChainsIncl (TopCat.of W) (hBle.trans (Set.compl_subset_compl.mpr hpt))
            = Work.Orient.relChainsIncl (TopCat.of W) hp :=
        Work.Orient.relChainsIncl_congr (TopCat.of W)
          (hBle.trans (Set.compl_subset_compl.mpr hpt)) hp
      have e5 : Work.Orient.relChainsIncl (TopCat.of W) hp
            = Work.ThomBordism.relChainsInclPunct (TopCat.of W)
                ((modelWithCornersEuclideanHalfSpace 9).boundary W) y hy := rfl
      rw [e1, e2, e3, e4, e5]
      rfl
    · -- non-generating case: the witness is the coherence class of `γ`
      have hKcoord : Work.Orient.IsCoordHalfBall 9 (TopCat.of W)
          (Work.Orient.halfBallPiece 9 (TopCat.of W) x r) := ⟨x, r, hr, hgood, rfl⟩
      obtain ⟨aK, haK⟩ := hγ.2 (Work.Orient.halfBallPiece 9 (TopCat.of W) x r) hKcoord hKint
      refine ⟨U, hxU, fun z hz => hsub (hUK hz), hUopen', ?_⟩
      refine ⟨Work.Orient.resRelH (TopCat.of W) 9 hUK aK, ?_⟩
      intro y hyU hy
      have hyK : y ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) x r := hUK hyU
      have hΨy : Ψ y hy = γ y hy := by
        show (if Submodule.span ℤ ({genLocClass w₁ y hy} :
            Set (Work.Orient.LocH (TopCat.of W) 9 y)) = ⊤
          then genLocClass w₁ y hy else γ y hy) = γ y hy
        rw [if_neg]
        exact fun h => hg ((hgen_const x hx r hr hgood hKint y hyK hy).mp h)
      rw [hΨy]
      have h1 := Work.Orient.Port.RelHmap_comp' (TopCat.of W) 9
        (Set.singleton_subset_iff.mpr hyU) hUK (Set.singleton_subset_iff.mpr hyK)
      change (Work.ThomBordism.RelHmap (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hyU))
        ((Work.ThomBordism.RelHmap (TopCat.of W) 9 hUK) aK) = γ y hy
      rw [← LinearMap.comp_apply, h1]
      exact haK y hy hyK
  refine ⟨Ψ, ?_, hΨ_gen, hwit⟩
  · intro x hx
    rfl

end

end Work.ThomBordism
