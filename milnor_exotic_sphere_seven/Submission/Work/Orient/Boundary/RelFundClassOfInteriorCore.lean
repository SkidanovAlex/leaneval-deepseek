import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.CoreClass
import Submission.Work.Orient.Boundary.BoundaryOrientation
import Submission.Work.Orient.Boundary.IsRelFundClassOfCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Existence of the relative fundamental class from the collar input

`Work.Orient.Boundary.RelativeFundamentalClassExists_of_coreIso`:
`Work.Orient.CoreIsoProp n` (the homological shadow of the collar neighbourhood theorem, proved from
`Work.Surgery.HasCollar` in `…/Boundary/CoreIsoOfCollar.lean`) implies
`Work.Orient.RelativeFundamentalClassExists n`, i.e. ORIENT's item 2.

The construction:

* `CoreIsoProp n` supplies a compact core `C₀ ⊆ W°` meeting every path-component of `W°` for which
  `φ : H_{n+1}(W,∂W) → H_{n+1}(W, W∖C₀)` is an isomorphism;
* `Work.Orient.Boundary.exists_coreClass` glues the local generators of the orientation over `C₀`
  into a class `u₀ ∈ H_{n+1}(W, W∖C₀)` with `u₀|_{{x}} = γ x` for every `x ∈ C₀`;
* `φ` being surjective, `u₀ = φ w` for some `w ∈ H_{n+1}(W,∂W)`;
* for `x ∈ C₀` the localisation of `w` at `x` factors through `φ` and the localisation of `u₀`,
  giving `loc_x w = γ x`, i.e. the local generator property on the core;
* `Work.Orient.Boundary.IsRelFundClassOfCore` spreads that property to every interior point;
* the boundary formula is `Work.Orient.Boundary.BoundaryOrientation`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

theorem RelativeFundamentalClassExists_of_coreIso (n : ℕ) (h : Work.Orient.CoreIsoProp n) :
    Work.Orient.RelativeFundamentalClassExists n := by
  classical
  intro W _ _ _ _ _ γ hγ
  obtain ⟨C₀, hCp, hint, hconn, hiso⟩ := h W
  obtain ⟨u₀, hu₀⟩ := exists_coreClass n W hCp hint γ hγ
  let φ : (Work.Cohomology.relChains W
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1) ⟶
      (Work.Cohomology.relChains W C₀ᶜ).homology (n + 1) :=
    HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W
      (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (B := C₀ᶜ)
      (fun y hy hyc => hint y hyc hy)) (n + 1)
  obtain ⟨w, hw⟩ := ((ConcreteCategory.isIso_iff_bijective φ).mp hiso).2 u₀
  have hwfund : Work.Orient.IsRelFundClass W (n + 1)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) w := by
    apply IsRelFundClassOfCore n W C₀ hCp hint hconn w
    intro x hx
    have h1 : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ⊆ C₀ᶜ :=
      fun t ht htC => hint t htC ht
    have hsubx : C₀ᶜ ⊆ ({x} : Set W)ᶜ :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
    have hfac : Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          x (hint x hx)
        = Work.Orient.relChainsIncl W
            (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (B := C₀ᶜ) h1
          ≫ Work.Cohomology.relCokerMap W C₀ᶜ ({x} : Set W)ᶜ hsubx := by
      rw [Work.Orient.relPunct_eq_relChainsIncl]
      rw [← Work.Orient.relChainsIncl_eq_relCokerMap W hsubx]
      rw [Work.Orient.relChainsIncl_trans W h1 hsubx]
    have hcomp := HomologicalComplex.homologyMap_comp
      (Work.Orient.relChainsIncl W
        (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (B := C₀ᶜ) h1)
      (Work.Cohomology.relCokerMap W C₀ᶜ ({x} : Set W)ᶜ hsubx) (n + 1)
    have hloc : (HomologicalComplex.homologyMap (Work.Orient.relPunct W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x (hint x hx))
          (n + 1)).hom w
        = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) u₀ := by
      rw [hfac, hcomp, ModuleCat.comp_apply, show
        (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W
          (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (B := C₀ᶜ) h1)
          (n + 1)).hom w = u₀ from hw]
      rfl
    rw [hloc, hu₀ x hx]
    exact hγ.1 x (hint x hx)
  exact ⟨w, hwfund, BoundaryOrientation n W w hwfund⟩

end

end Work.Orient.Boundary
