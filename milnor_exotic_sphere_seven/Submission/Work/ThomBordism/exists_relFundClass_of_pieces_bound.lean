import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Orient.Preimage
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Surgery.Collar
import Submission.Work.ThomBordism.orientOfCollar
import Submission.Work.Orient.Boundary.IsRelFundClassOfCore
import Submission.Work.Orient.Boundary.LocalClassConstantOnBall
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.Orient.Closed
import Submission.Work.ThomBordism.bdryCapBdryBijective
import Submission.Work.ThomBordism.piecesBound_sum_isFundClass
import Submission.Work.ThomBordism.piecesBound_relClass_of_witnesses
import Submission.Work.ThomBordism.piecesBound_locClass_eq_of_core
import Submission.Work.ThomBordism.piecesBound_locGen_iff
import Submission.Work.ThomBordism.piecesBound_generatingWitnesses

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative fundamental class of a family of boundary pieces that bound

`Work.ThomBordism.exists_relFundClass_of_pieces_bound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.ThomBordism

noncomputable section

theorem exists_relFundClass_of_pieces_bound
    {W : Type} [TopologicalSpace W] [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
    [Nonempty W]
    (hcol : Nonempty (Work.Surgery.Collar 8 W))
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (e : ↥((modelWithCornersEuclideanHalfSpace 9).boundary W) ≃ₜ (Σ i : ι, (Fam i).pt))
    {γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      Work.Orient.LocH (TopCat.of W) 9 x}
    (hγ : Work.Orient.IsHalfOrientationFamily 8 (TopCat.of W) γ)
    (h : (HomologicalComplex.homologyMap
          (Work.Cohomology.inclChains (TopCat.of W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8)
          (∑ i : ι, HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (Fam i).X
              (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary W))
              (TopCat.ofHom ⟨fun y => e.symm ⟨i, y⟩,
                e.continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c) = 0) :
    ∃ w : (Work.Cohomology.relChains (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9,
      (∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
        Submodule.span ℤ {(HomologicalComplex.homologyMap
          (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9 w)} = ⊤) ∧
      (Work.Cohomology.hPairδ (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8 w
        = ∑ i : ι, HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (Fam i).X
              (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary W))
              (TopCat.ofHom ⟨fun y => e.symm ⟨i, y⟩,
                e.continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c) := by
  classical
  -- ### 0. The boundary is compact, and charted over `ℝ⁸` by transport along `e`
  have hBclosed : IsClosed ((modelWithCornersEuclideanHalfSpace 9).boundary W) :=
    Work.Orient.Boundary.isClosed_boundary_halfSpace 8 (TopCat.of W)
  haveI hBcpt : CompactSpace ↥((modelWithCornersEuclideanHalfSpace 9).boundary W) :=
    isCompact_iff_compactSpace.mp hBclosed.isCompact
  haveI hσ : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (Σ i : ι, (Fam i).pt) :=
    Work.ThomBordism.sigmaChartedSpace (ι := ι) (fun i => (Fam i).pt)
  haveI hBchart : ChartedSpace (EuclideanSpace ℝ (Fin 8))
      ↥((modelWithCornersEuclideanHalfSpace 9).boundary W) :=
    e.symm.chartedSpace
  -- ### 1. The boundary sum `s`
  set s : (Work.Cohomology.singularChains ℤ
      (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary W))).homology 8 :=
    ∑ i : ι, HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (Fam i).X
        (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary W))
        (TopCat.ofHom ⟨fun y => e.symm ⟨i, y⟩,
          e.continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c with hsdef
  have hh : (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8).hom s = 0 := by
    rw [hsdef]; exact h
  -- ### 2. `s` is a fundamental class of the boundary
  have hD1 : Work.Orient.IsFundClass
      (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8 s :=
    piecesBound_sum_isFundClass e
  -- ### 3. A class `w₁` with `hPairδ w₁ = s`
  have hex := (Work.Cohomology.hPair_exact₁ (TopCat.of W)
    ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8).moduleCat_range_eq_ker
  have hs_ker : s ∈ (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8)).ker := by
    rw [LinearMap.mem_ker]; exact hh
  have hs_rng : s ∈ (ModuleCat.Hom.hom (Work.Cohomology.hPairδ (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8)).range := by
    rw [hex]; exact hs_ker
  obtain ⟨w₁, hw₁⟩ := hs_rng
  -- ### 4. The collar, its core, and a relative fundamental class `w₀`
  obtain ⟨w₀, hw₀rel, -, -⟩ := Work.ThomBordism.exists_relFundClass_of_collar'
    (n := 8) (M := W) (Classical.choice hcol) γ hγ
  obtain ⟨C₀, hC₀cpt, hC₀int, hC₀conn, hC₀iso⟩ :=
    Work.ThomBordism.coreIso_of_collar (n := 8) (Classical.choice hcol)
  -- ### 5. The local comparison at a boundary point (pending delegated input)
  have hD2 := piecesBound_locGen_iff (W := W) w₀ hw₀rel
  -- ### 6. The prescription `Ψ` and its local witnesses (pending delegated input)
  have hD7 := piecesBound_generatingWitnesses (W := W) γ hγ w₁
  obtain ⟨Ψ, hΨdef, hΨ_gen, hwit_all⟩ := hD7
  have hΨ_eq : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      Submodule.span ℤ {((HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom w₁)} = ⊤ →
      Ψ x hx = (HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom w₁ := by
    intro x hx hg
    rw [hΨdef x hx, if_pos hg]
  -- ### 7. Local generation of `w₁` near every boundary point
  have hgen_near : ∀ (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace 9).boundary W)
      (r : ℝ) (hr : 0 < r)
      (hgood : Work.Orient.halfBallGood 9 (TopCat.of W) y r)
      (x : W) (hxK : x ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) y r)
      (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      Submodule.span ℤ {((HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom w₁)} = ⊤ := by
    intro y hy r hr hgood x hxK hx
    have h1 := (hD2 y hy r hr hgood x hxK hx w₁).1
    rw [h1, hw₁]
    exact hD1 ⟨y, hy⟩
  -- ### 8. The prescribed local classes over the core
  obtain ⟨u, hu⟩ := piecesBound_relClass_of_witnesses hC₀cpt hC₀int Ψ
    (fun x hx => hwit_all x (hC₀int x hx))
  -- ### 9. Transport along the core isomorphism
  have hbc : (modelWithCornersEuclideanHalfSpace 9).boundary W ⊆ C₀ᶜ :=
    fun z hz hzC => hC₀int z hzC hz
  set φ : (Work.Cohomology.relChains (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9 ⟶
      (Work.Cohomology.relChains (TopCat.of W) C₀ᶜ).homology 9 :=
    HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of W)
      (A := (modelWithCornersEuclideanHalfSpace 9).boundary W) (B := C₀ᶜ) hbc) 9 with hφdef
  haveI : IsIso φ := hC₀iso
  obtain ⟨z, hz⟩ := ((ConcreteCategory.isIso_iff_bijective φ).mp inferInstance).2 u
  have hloc_z : ∀ (x : W) (hx : x ∈ C₀),
      (HomologicalComplex.homologyMap (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W) x (hC₀int x hx)) 9).hom z
        = Ψ x (hC₀int x hx) := by
    intro x hx
    have hfac : Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hx) (φ.hom z)
        = (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W) x (hC₀int x hx)) 9).hom z := by
      have hsubx : C₀ᶜ ⊆ ({x} : Set W)ᶜ :=
        Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
      have hfac' : Work.Orient.relPunct (TopCat.of W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W) x (hC₀int x hx)
          = Work.Orient.relChainsIncl (TopCat.of W)
              (A := (modelWithCornersEuclideanHalfSpace 9).boundary W) (B := C₀ᶜ) hbc
            ≫ Work.Cohomology.relCokerMap (TopCat.of W) C₀ᶜ ({x} : Set W)ᶜ hsubx := by
        rw [Work.Orient.relPunct_eq_relChainsIncl]
        rw [← Work.Orient.relChainsIncl_eq_relCokerMap (TopCat.of W) hsubx]
        rw [Work.Orient.relChainsIncl_trans (TopCat.of W) hbc hsubx]
      have hcomp := HomologicalComplex.homologyMap_comp
        (Work.Orient.relChainsIncl (TopCat.of W)
          (A := (modelWithCornersEuclideanHalfSpace 9).boundary W) (B := C₀ᶜ) hbc)
        (Work.Cohomology.relCokerMap (TopCat.of W) C₀ᶜ ({x} : Set W)ᶜ hsubx) 9
      rw [hfac', hcomp, ModuleCat.comp_apply]
      rfl
    rw [hz] at hfac
    have h5 : (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x (hC₀int x hx)) 9).hom z
        = Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hx) u :=
      hfac.symm
    rw [← Work.Orient.relPunct_eq_relChainsInclPunct]
    exact h5.trans (hu x hx)
  -- ### 10. `z` is a relative fundamental class
  have hfund : Work.Orient.IsRelFundClass (TopCat.of W) 9
      ((modelWithCornersEuclideanHalfSpace 9).boundary W) z := by
    refine Work.Orient.Boundary.IsRelFundClassOfCore 8 (TopCat.of W) C₀ hC₀cpt hC₀int hC₀conn z ?_
    intro x hx
    rw [Work.Orient.relPunct_eq_relChainsInclPunct]
    rw [hloc_z x hx]
    exact hΨ_gen x (hC₀int x hx)
  -- ### 11. The identity `loc_z = Ψ` on the whole interior
  have hz_eq : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      (HomologicalComplex.homologyMap (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom z = Ψ x hx :=
    piecesBound_locClass_eq_of_core hC₀int hC₀conn z Ψ hwit_all hloc_z
  -- ### 12. `hPairδ z = s`
  have hdel : Work.Cohomology.hPairδ (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8 z = s := by
    have hdiff : Work.Cohomology.hPairδ (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8 (z - w₁) = 0 := by
      have hvan : ∀ y : ↥((modelWithCornersEuclideanHalfSpace 9).boundary W),
          Work.Orient.locClass
            (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8
            ((Work.Cohomology.hPairδ (TopCat.of W)
              ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8).hom (z - w₁)) y = 0 := by
        intro y
        obtain ⟨r, hr, hgood, -⟩ := Work.Orient.Boundary.exists_halfBall_subset 8
          (W := TopCat.of W) (U := Set.univ) isOpen_univ (Set.mem_univ y.1)
        obtain ⟨x, hxK, hxbdry⟩ :=
          Work.Orient.Boundary.exists_mem_halfBallPiece_and_notMem_boundary 8 (TopCat.of W)
            y.1 y.2 r hr hgood
        have hzero : (HomologicalComplex.homologyMap
            (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
              ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hxbdry) 9).hom (z - w₁) = 0 := by
          rw [map_sub]
          rw [hz_eq x hxbdry]
          rw [hΨ_eq x hxbdry (hgen_near y.1 y.2 r hr hgood x hxK hxbdry)]
          rw [sub_self]
        exact (hD2 y.1 y.2 r hr hgood x hxK hxbdry (z - w₁)).2.mp hzero
      exact Work.Orient.eq_zero_of_locClass_eq_zero 8 (by norm_num)
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary W))
        ((Work.Cohomology.hPairδ (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8).hom (z - w₁)) hvan
    have h1 : Work.Cohomology.hPairδ (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8 z
        - Work.Cohomology.hPairδ (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8 w₁ = 0 := by
      rw [← map_sub]
      exact hdiff
    rw [sub_eq_zero.mp h1, hw₁]
  -- ### 13. Assembly
  refine ⟨z, ?_, hdel.trans hsdef⟩
  intro x hx
  rw [← Work.Orient.relPunct_eq_relChainsInclPunct (TopCat.of W)
    ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx]
  exact hfund x hx

end

end Work.ThomBordism
