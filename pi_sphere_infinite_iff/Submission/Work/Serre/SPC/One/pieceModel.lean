import Mathlib
import Submission.Work.Serre.SPC.One.ModelCompress
import Submission.Work.Serre.SPC.One.discPairStrong
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.CellStep.ModelReduction
import Submission.Work.StemsB.hasHLP_pullback
import Submission.Work.Cohomology.pd_plumbing

set_option synthInstance.maxHeartbeats 400000


/-!
# The model pair map for a relative part of the model interval

For a continuous map `p : E → B`, a map `χ : D¹ → B` and a set `W ⊆ D¹`, `pmMapOne p χ W` is the
map of relative chain complexes

  `(χ^*E, χ^*E|_{(pullbackSnd)⁻¹ W}) ⟶ (D¹, W)`

induced by the projection `pullbackSnd p χ` of the pullback.

The main result is `pmMapOne_punctDisc_strong`: for a Serre fibration `p` whose fibres over the
points `χ y` are homologically `φ`-connected, the map with relative part the *punctured* interval
`punctDisc = D¹ ∖ {0}` is an isomorphism on integral homology in degrees `< 1 + φ` and surjective
in degree `1 + φ`.  It follows from `discPairStrong` (relative part `S⁰ = {±1}`) by the
`relCokerMap` step enlarging the relative part from `S⁰` to `punctDisc`, whose acyclicity is
`Work.Serre.SPC.One.compressRel_punctDisc`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

/-- **The model pair map** `(χ^*E, χ^*E|_{(pullbackSnd)⁻¹ W}) ⟶ (D¹, W)` induced by the projection
of the pullback, on relative singular chains. -/
noncomputable def pmMapOne {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (χ : C(cellD1, B)) (W : Set cellD1) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p χ))
        ((Work.StemsB.pullbackSnd p χ) ⁻¹' W) ⟶
      Work.Cohomology.relChains (TopCat.of cellD1) W :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback p χ)) (TopCat.of cellD1)
    ((Work.StemsB.pullbackSnd p χ) ⁻¹' W) W
    (TopCat.ofHom (Work.StemsB.pullbackSnd p χ))
    (TopCat.ofHom ⟨fun x => ⟨(Work.StemsB.pullbackSnd p χ) x.1, x.2⟩, by
      exact Continuous.subtype_mk
        ((Work.StemsB.pullbackSnd p χ).continuous.comp continuous_subtype_val) (fun x => x.2)⟩)
    (by ext x; rfl)

/-- At the boundary sphere the model map is `discPairMap`. -/
theorem pmMapOne_cellS0Set {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (χ : C(cellD1, B)) :
    pmMapOne p χ cellS0Set = discPairMap p χ := rfl

/-- **The `relCokerMap` square of the model maps**: enlarging the relative part commutes with the
model maps. -/
theorem pmMapOne_square {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (χ : C(cellD1, B)) {W₀ W₁ : Set cellD1} (h : W₀ ⊆ W₁) :
    Work.Cohomology.relCokerMap (TopCat.of (Work.StemsB.Pullback p χ))
        ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₀) ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₁)
        (fun x hx => h hx)
      ≫ pmMapOne p χ W₁
    = pmMapOne p χ W₀
      ≫ Work.Cohomology.relCokerMap (TopCat.of cellD1) W₀ W₁ h := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains
    (TopCat.of (Work.StemsB.Pullback p χ)) ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₀)))).mp
  show cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p χ))
        ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₀))
      ≫ (Work.Cohomology.relCokerMap (TopCat.of (Work.StemsB.Pullback p χ))
          ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₀) ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₁)
          (fun x hx => h hx)
        ≫ pmMapOne p χ W₁)
    = cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p χ))
        ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₀))
      ≫ (pmMapOne p χ W₀ ≫ Work.Cohomology.relCokerMap (TopCat.of cellD1) W₀ W₁ h)
  have hpm (W : Set cellD1) :
      cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p χ))
          ((Work.StemsB.pullbackSnd p χ) ⁻¹' W)) ≫ pmMapOne p χ W
        = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p χ))
            (TopCat.of cellD1) (TopCat.ofHom (Work.StemsB.pullbackSnd p χ))
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of cellD1) W) := by
    unfold pmMapOne Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  rw [← Category.assoc, Work.Cohomology.relCokerMap_comp_π]
  calc cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p χ))
        ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₁)) ≫ pmMapOne p χ W₁
      = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p χ))
          (TopCat.of cellD1) (TopCat.ofHom (Work.StemsB.pullbackSnd p χ))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of cellD1) W₁) := hpm W₁
    _ = Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p χ))
          (TopCat.of cellD1) (TopCat.ofHom (Work.StemsB.pullbackSnd p χ))
        ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of cellD1) W₀)
          ≫ Work.Cohomology.relCokerMap (TopCat.of cellD1) W₀ W₁ h) := by
        rw [Work.Cohomology.relCokerMap_comp_π]
    _ = (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p χ))
          (TopCat.of cellD1) (TopCat.ofHom (Work.StemsB.pullbackSnd p χ))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of cellD1) W₀))
          ≫ Work.Cohomology.relCokerMap (TopCat.of cellD1) W₀ W₁ h := by
        rw [Category.assoc]
    _ = (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p χ))
          ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₀)) ≫ pmMapOne p χ W₀)
          ≫ Work.Cohomology.relCokerMap (TopCat.of cellD1) W₀ W₁ h := by rw [hpm W₀]
    _ = cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p χ))
          ((Work.StemsB.pullbackSnd p χ) ⁻¹' W₀))
        ≫ (pmMapOne p χ W₀
          ≫ Work.Cohomology.relCokerMap (TopCat.of cellD1) W₀ W₁ h) := by
        rw [Category.assoc]

/-- The boundary `S⁰` of the model interval lies in the punctured interval. -/
theorem cellS0Set_subset_punctDisc : cellS0Set ⊆ punctDisc := by
  rintro x ⟨z, rfl⟩
  rw [mem_punctDisc]
  intro h
  have h1 : ((cellS0ToD1 z : cellD1) : ℝ) = 0 := by
    have := congrArg (fun p : cellD1 => (p : ℝ)) h
    simpa [cellD1Centre] using this
  have h2 := norm_cellS0ToD1 z
  rw [h1] at h2
  norm_num at h2

/-- **The punctured model statement**: for a Serre fibration `p` with homologically
`φ`-connected fibres over the points `χ y`, the model pair map with relative part the punctured
interval is an isomorphism on integral homology in degrees `< 1 + φ` and surjective in degree
`1 + φ`. -/
theorem pmMapOne_punctDisc_strong {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (χ : C(cellD1, B)) (φ : ℕ)
    (hfib : ∀ y : cellD1, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p (χ y)))).homology j))
    (h0 : ∀ y : cellD1,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre p (χ y)))
        (ModuleCat.of ℤ ℤ))) :
    (∀ k : ℕ, k < 1 + φ → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (pmMapOne p χ punctDisc) k)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (pmMapOne p χ punctDisc) (1 + φ)).hom := by
  have hIncl : cellS0Set ⊆ punctDisc := cellS0Set_subset_punctDisc
  have hq : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p χ) :=
    fun n => Work.StemsB.hasHLP_pullback p χ (hp n)
  have hDisc := discPairStrong p hp χ φ hfib h0
  rw [← pmMapOne_cellS0Set p χ] at hDisc
  have key (k : ℕ) :
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (pmMapOne p χ cellS0Set) k) ↔
        CategoryTheory.IsIso (HomologicalComplex.homologyMap (pmMapOne p χ punctDisc) k) := by
    haveI htot : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of (Work.StemsB.Pullback p χ))
          ((Work.StemsB.pullbackSnd p χ) ⁻¹' cellS0Set)
          ((Work.StemsB.pullbackSnd p χ) ⁻¹' punctDisc) (fun x hx => hIncl hx)) k) :=
      Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of (Work.StemsB.Pullback p χ))
        (fun x hx => hIncl hx)
        (fun j => Work.Serre.isZero_relChains_preimage_of_compress (Work.StemsB.pullbackSnd p χ)
          hq hIncl (fun d => compressRel_punctDisc d) j) k
    haveI hbase : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of cellD1) cellS0Set punctDisc hIncl) k) :=
      Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of cellD1) hIncl
        (fun j => isZero_relChains_punctDisc j) k
    have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ k)
      (pmMapOne_square p χ hIncl)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
    exact (isIso_iff_of_comm_square
      (h := HomologicalComplex.homologyMap (pmMapOne p χ punctDisc) k)
      (f := HomologicalComplex.homologyMap (pmMapOne p χ cellS0Set) k)
      (u := HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
        (TopCat.of (Work.StemsB.Pullback p χ)) ((Work.StemsB.pullbackSnd p χ) ⁻¹' cellS0Set)
        ((Work.StemsB.pullbackSnd p χ) ⁻¹' punctDisc) (fun x hx => hIncl hx)) k)
      (v := HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of cellD1) cellS0Set punctDisc hIncl) k) hsq).symm
  refine ⟨fun k hk => (key k).mp (hDisc.1 k hk), ?_⟩
  have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ (1 + φ))
    (pmMapOne_square p χ hIncl)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
  haveI htot : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of (Work.StemsB.Pullback p χ))
        ((Work.StemsB.pullbackSnd p χ) ⁻¹' cellS0Set)
        ((Work.StemsB.pullbackSnd p χ) ⁻¹' punctDisc) (fun x hx => hIncl hx)) (1 + φ)) :=
    Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of (Work.StemsB.Pullback p χ))
      (fun x hx => hIncl hx)
      (fun j => Work.Serre.isZero_relChains_preimage_of_compress (Work.StemsB.pullbackSnd p χ)
        hq hIncl (fun d => compressRel_punctDisc d) j) (1 + φ)
  haveI hbase : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of cellD1) cellS0Set punctDisc hIncl) (1 + φ)) :=
    Work.Serre.CellStep.isIso_relCokerMap_of_acyclic (TopCat.of cellD1) hIncl
      (fun j => isZero_relChains_punctDisc j) (1 + φ)
  exact (surjective_iff_of_comm_square
    (h := HomologicalComplex.homologyMap (pmMapOne p χ punctDisc) (1 + φ))
    (f := HomologicalComplex.homologyMap (pmMapOne p χ cellS0Set) (1 + φ))
    (u := HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
      (TopCat.of (Work.StemsB.Pullback p χ)) ((Work.StemsB.pullbackSnd p χ) ⁻¹' cellS0Set)
      ((Work.StemsB.pullbackSnd p χ) ⁻¹' punctDisc) (fun x hx => hIncl hx)) (1 + φ))
    (v := HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of cellD1) cellS0Set punctDisc hIncl) (1 + φ))
    hsq).mpr hDisc.2

end

end Work.Serre.SPC.One
