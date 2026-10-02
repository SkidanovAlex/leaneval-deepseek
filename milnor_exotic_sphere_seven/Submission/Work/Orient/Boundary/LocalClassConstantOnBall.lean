import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfRestrictIso
import Submission.Work.Orient.Boundary.HalfRestrictIsoAtPoint
import Submission.Work.Orient.Boundary.RelChainsBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local class of a relative class is constant on a coordinate half-ball of the interior

`Work.Orient.Boundary.LocalClassConstantOnBall`: if `K = halfBallPiece (n+1) W z r` is a coordinate
half-ball whose points are all interior, then for **any** `w ∈ H_{n+1}(W, W∖∂W) = H_{n+1}(W,∂W)`
the property "the local class of `w` at `t` generates `H_{n+1}(W, W∖{t})`" is *independent of* the
point `t ∈ K`.

The proof is the factorisation through `H_{n+1}(W, W∖K)`:
for `t ∈ K` the map `relPunct W ∂W t` (the localisation of `Defs.lean`) is
`relChainsIncl W (∂W ⊆ Kᶜ) ≫ relCokerMap W Kᶜ {t}ᶜ` (functoriality of `relChainsIncl` plus the
chain-level bridge `relChainsIncl_eq_relCokerMap`), and the second factor is an isomorphism by
`Work.Orient.Boundary.HalfRestrictIsoAtPoint`.  Hence both sides are equivalent to
"`(relChainsIncl W (∂W ⊆ Kᶜ))_* w` generates `H_{n+1}(W, W∖K)`".

This is the local constancy of the *local degree*, which is what transports the relative fundamental
class out of a compact core (see `Work.Orient.Boundary.IsRelFundClassOfCore`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-- **An isomorphism of `ℤ`-modules preserves the property of an element of generating.** -/
theorem span_singleton_eq_top_iff_of_isIso {M N : ModuleCat ℤ} (φ : M ⟶ N) (hφ : IsIso φ)
    (a : M) :
    Submodule.span ℤ (Set.singleton (φ.hom a)) = ⊤ ↔
      Submodule.span ℤ (Set.singleton a) = ⊤ := by
  have hb : Function.Bijective φ.hom := (ConcreteCategory.isIso_iff_bijective φ).mp hφ
  have hspan : Submodule.span ℤ (Set.singleton (φ.hom a))
      = Submodule.map φ.hom (Submodule.span ℤ (Set.singleton a)) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨a, Set.mem_singleton_iff.mpr rfl, (Set.mem_singleton_iff.mp hx).symm⟩
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_singleton_iff.mp hy]
      exact Set.mem_singleton_iff.mpr rfl
  rw [hspan]
  constructor
  · intro h
    rw [Submodule.eq_top_iff']
    intro b
    have hmem : φ.hom b ∈ Submodule.map φ.hom (Submodule.span ℤ (Set.singleton a)) := by
      rw [h]; exact Submodule.mem_top
    obtain ⟨b', hb', heq⟩ := Submodule.mem_map.mp hmem
    rw [hb.1 heq] at hb'
    exact hb'
  · intro h
    rw [h, Submodule.map_top, LinearMap.range_eq_top]
    exact hb.2

/-- **The local class of a relative class is constant on an interior coordinate half-ball.** -/
theorem LocalClassConstantOnBall (n : ℕ) (W : TopCat.{0}) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (z : W) (r : ℝ) (hr : 0 < r)
    (hball : Work.Orient.halfBallGood (n + 1) W z r)
    (hint : ∀ y ∈ Work.Orient.halfBallPiece (n + 1) W z r,
      y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (w : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
    (x y : W) (hx : x ∈ Work.Orient.halfBallPiece (n + 1) W z r)
    (hy : y ∈ Work.Orient.halfBallPiece (n + 1) W z r) :
    (Submodule.span ℤ (Set.singleton ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x
          (hint x hx)) (n + 1)).hom w)) = ⊤)
      ↔ (Submodule.span ℤ (Set.singleton ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) y
          (hint y hy)) (n + 1)).hom w)) = ⊤) := by
  classical
  let K : Set W := Work.Orient.halfBallPiece (n + 1) W z r
  let B : Set W := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W
  have h1 : B ⊆ Kᶜ := fun t ht hK => hint t hK ht
  have hsubx : Kᶜ ⊆ ({x} : Set W)ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
  have hsuby : Kᶜ ⊆ ({y} : Set W)ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)
  let u : (Work.Cohomology.relChains W Kᶜ).homology (n + 1) :=
    (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W (A := B) (B := Kᶜ) h1)
      (n + 1)).hom w
  have hfac : ∀ (t : W) (ht : t ∈ K) (hsub : Kᶜ ⊆ ({t} : Set W)ᶜ),
      Work.Orient.relPunct W B t (hint t ht)
        = Work.Orient.relChainsIncl W (A := B) (B := Kᶜ) h1
          ≫ Work.Cohomology.relCokerMap W Kᶜ ({t} : Set W)ᶜ hsub := by
    intro t ht hsub
    rw [Work.Orient.relPunct_eq_relChainsIncl]
    rw [← Work.Orient.relChainsIncl_eq_relCokerMap W hsub]
    rw [Work.Orient.relChainsIncl_trans W h1 hsub]
  have hcomp : ∀ (t : W) (ht : t ∈ K) (hsub : Kᶜ ⊆ ({t} : Set W)ᶜ),
      HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := B) (B := Kᶜ) h1
            ≫ Work.Cohomology.relCokerMap W Kᶜ ({t} : Set W)ᶜ hsub) (n + 1)
        = HomologicalComplex.homologyMap
              (Work.Orient.relChainsIncl W (A := B) (B := Kᶜ) h1) (n + 1)
          ≫ HomologicalComplex.homologyMap
              (Work.Cohomology.relCokerMap W Kᶜ ({t} : Set W)ᶜ hsub) (n + 1) :=
    fun t ht hsub => HomologicalComplex.homologyMap_comp _ _ _
  have hx_eq : (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W B x (hint x hx)) (n + 1)).hom w
      = (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap W Kᶜ ({x} : Set W)ᶜ hsubx) (n + 1)).hom u := by
    rw [hfac x hx hsubx, hcomp x hx hsubx, ModuleCat.comp_apply]
    rfl
  have hy_eq : (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W B y (hint y hy)) (n + 1)).hom w
      = (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap W Kᶜ ({y} : Set W)ᶜ hsuby) (n + 1)).hom u := by
    rw [hfac y hy hsuby, hcomp y hy hsuby, ModuleCat.comp_apply]
    rfl
  have hspanx : (Submodule.span ℤ (Set.singleton ((HomologicalComplex.homologyMap
      (Work.Orient.relPunct W B x (hint x hx)) (n + 1)).hom w)) = ⊤)
      ↔ Submodule.span ℤ (Set.singleton u) = ⊤ := by
    rw [hx_eq]
    exact span_singleton_eq_top_iff_of_isIso _
      (HalfRestrictIsoAtPoint n W z r hr hball hint x hx) u
  have hspany : (Submodule.span ℤ (Set.singleton ((HomologicalComplex.homologyMap
      (Work.Orient.relPunct W B y (hint y hy)) (n + 1)).hom w)) = ⊤)
      ↔ Submodule.span ℤ (Set.singleton u) = ⊤ := by
    rw [hy_eq]
    exact span_singleton_eq_top_iff_of_isIso _
      (HalfRestrictIsoAtPoint n W z r hr hball hint y hy) u
  exact hspanx.trans hspany.symm

end

end Work.Orient.Boundary
