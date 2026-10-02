import Mathlib
import Submission.Work.Orient.Boundary.injective_localisation_of_halfBallInterior
import Submission.Work.Orient.Boundary.tripleConnectingMap_surjective_of_isRelFundClass
import Submission.Work.Orient.Boundary.RelChainsBridge
import Submission.Work.ThomBordism.locClass_hPairDelta_eq_tripleDelta
import Submission.Work.ThomBordism.halfBallLocalisation_hPairDelta_eq

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism

theorem locClass_hPairDelta_eq_of_localClass_eq {n : ℕ}
    (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {B : Set W} (hB : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W = B)
    {y : W} (hy : y ∈ B) {r : ℝ} (hr : 0 < r)
    (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.halfBallPiece (n + 1) W y r) (hx₀int : x₀ ∉ B)
    {w w' : (Work.Cohomology.relChains W B).homology (n + 1)}
    (h : (HomologicalComplex.homologyMap (Work.Orient.relPunct W B x₀ hx₀int) (n + 1)).hom w
       = (HomologicalComplex.homologyMap (Work.Orient.relPunct W B x₀ hx₀int) (n + 1)).hom w') :
    Work.Orient.locClass (TopCat.of ↥B) n ((Work.Cohomology.hPairδ W B n).hom w) ⟨y, hy⟩
      = Work.Orient.locClass (TopCat.of ↥B) n ((Work.Cohomology.hPairδ W B n).hom w') ⟨y, hy⟩ := by
  subst hB
  -- the point `x₀` lies in the interior part of the half-ball piece
  have hKint : x₀ ∈ Work.Orient.Boundary.halfBallK n W y r ∩
      (Work.Orient.Boundary.bdrySetW n W)ᶜ := ⟨hx₀, hx₀int⟩
  -- the four inclusions of the two triples `(∂W∖{y} ⊆ ∂W ⊆ W)` and `(A ⊆ B' ⊆ W)`
  have hBB : Work.Orient.Boundary.bdrySetW n W ⊆ Work.Orient.Boundary.bigB n W y r :=
    Work.Orient.Boundary.bdrySetW_sub_bigB n W y r
  have hAB : Work.Orient.Boundary.bdryMinus n W y ⊆ Work.Orient.Boundary.bigA n W y r :=
    Work.Orient.Boundary.bdryMinus_sub_bigA n W y r
  have h11 : Work.Orient.Boundary.bdryMinus n W y ⊆ Work.Orient.Boundary.bdrySetW n W :=
    Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y
  have h22 : Work.Orient.Boundary.bigA n W y r ⊆ Work.Orient.Boundary.bigB n W y r :=
    Work.Orient.Boundary.bigA_sub_bigB n W y r
  -- `B'` avoids `x₀`
  have hj : Work.Orient.Boundary.bigB n W y r ⊆ ({x₀} : Set W)ᶜ := by
    intro z hz hzx
    rw [Set.mem_singleton_iff] at hzx
    subst hzx
    exact hz hKint
  -- the map of the hypothesis is the localisation to the piece followed by `hj`
  have hcomp : Work.Orient.relPunct W (Work.Orient.Boundary.bdrySetW n W) x₀ hx₀int
      = Work.Orient.relChainsIncl W hBB ≫ Work.Orient.relChainsIncl W hj := by
    rw [Work.Orient.relPunct_eq_relChainsIncl W (Work.Orient.Boundary.bdrySetW n W) x₀ hx₀int,
      Work.Orient.relChainsIncl_trans W hBB hj]
  -- `hj` induces an injective map on homology
  have hinjL : Function.Injective (Work.Orient.resRelH W (n + 1)
      (Set.singleton_subset_iff.mpr hKint)) :=
    Work.Orient.Boundary.injective_localisation_of_halfBallInterior n W y hy r hr hgood x₀ hKint
  have hres : (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W hj) (n + 1)).hom
      = Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hKint) := by
    rw [Work.Orient.resRelH_eq_homologyMap_relChainsIncl W (n + 1)
      (Set.singleton_subset_iff.mpr hKint)]
  have hinj2 : Function.Injective
      (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W hj) (n + 1)).hom := by
    rw [hres]
    exact hinjL
  -- the localisations of `w` and `w'` to the piece `P` agree
  have hmain : (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W hBB) (n + 1)).hom w
      = (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W hBB) (n + 1)).hom w' := by
    apply hinj2
    have h1 := h
    rw [hcomp, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp] at h1
    simp only [LinearMap.comp_apply] at h1
    exact h1
  -- the same statement for the map `ρ` of the triple `(A ⊆ B' ⊆ W)`
  have hmainρ : (HomologicalComplex.homologyMap (Work.Orient.Boundary.tripleMap W h11 h22 hAB hBB).τ₃
        (n + 1)).hom w
      = (HomologicalComplex.homologyMap (Work.Orient.Boundary.tripleMap W h11 h22 hAB hBB).τ₃
        (n + 1)).hom w' := by
    show (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W
        (Work.Orient.Boundary.bdrySetW n W) (Work.Orient.Boundary.bigB n W y r) hBB) (n + 1)).hom w
      = (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W
        (Work.Orient.Boundary.bdrySetW n W) (Work.Orient.Boundary.bigB n W y r) hBB) (n + 1)).hom w'
    rw [← Work.Orient.relChainsIncl_eq_relCokerMap W hBB]
    exact hmain
  -- the naturality square of the map of triples
  have hsq : ∀ a : (Work.Cohomology.relChains W (Work.Orient.Boundary.bdrySetW n W)).homology (n + 1),
      (HomologicalComplex.homologyMap (Work.Orient.Boundary.tripleMap W h11 h22 hAB hBB).τ₁ n).hom
        (((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
          (Work.Orient.Boundary.bdrySetW n W) h11).δ (n + 1) n (by simp [ComplexShape.down])).hom a)
      = (((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bigA n W y r)
          (Work.Orient.Boundary.bigB n W y r) h22).δ (n + 1) n (by simp [ComplexShape.down])).hom
          ((HomologicalComplex.homologyMap
            (Work.Orient.Boundary.tripleMap W h11 h22 hAB hBB).τ₃ (n + 1)).hom a)) := by
    intro a
    have hnat := Work.Orient.Boundary.tripleMap_delta_naturality W h11 h22 hAB hBB n
    have h1 := congrArg (fun φ => (ModuleCat.Hom.hom φ) a) hnat
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h1
    simp only [LinearMap.comp_apply] at h1
    exact h1
  have hinje : Function.Injective
      (HomologicalComplex.homologyMap (Work.Orient.Boundary.tripleMap W h11 h22 hAB hBB).τ₁ n).hom :=
    Work.Orient.Boundary.tripleConnecting_input₁ n W y hy r hr hgood
  -- the two triple connecting maps agree
  have htriple : ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
        (Work.Orient.Boundary.bdrySetW n W) h11).δ (n + 1) n (by simp [ComplexShape.down])).hom w
      = ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
        (Work.Orient.Boundary.bdrySetW n W) h11).δ (n + 1) n (by simp [ComplexShape.down])).hom w' := by
    apply hinje
    rw [hsq w, hsq w', hmainρ]
  -- the local class of `hPairδ` is the triple connecting map, so we are done
  rw [Work.ThomBordism.locClass_hPairDelta_eq_tripleDelta n W w y hy,
    Work.ThomBordism.locClass_hPairDelta_eq_tripleDelta n W w' y hy]
  exact congrArg (fun u => (HomologicalComplex.homologyMap (Work.Orient.Boundary.diffCokerMap W
      (Work.Orient.Boundary.bdrySetW n W) y hy
      (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)) n).hom u) htriple

end Work.ThomBordism
