import Mathlib
import Submission.Work.Orient.Boundary.CoreIsoOfCollar
import Submission.Work.Orient.Boundary.RelFundClassOfInteriorCore
import Submission.Work.Orient.Boundary.BoundaryOrientation
import Submission.Work.Orient.Boundary.CoreClass
import Submission.Work.Orient.Boundary.IsRelFundClassOfCore
import Submission.Work.Orient.Bridge
import Submission.Work.ThomBordism.Interface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT item 2, **pointwise**: a collar of *this* manifold suffices

## Why this file exists (area THOM, critical-path analysis of 2026-09-25)

The ORIENT area's item 2 — "a compact `C^∞` `(n+1)`-manifold with boundary and an orientation has a
relative fundamental class `w ∈ H_{n+1}(W,∂W)` which is a local generator at every interior point
and whose `hPairδ` is a fundamental class of `∂W`" — is currently available only in the *global*
form

```
Work.Orient.Boundary.RelativeFundamentalClassExists_of_hasCollar (n)
    (h : ∀ M, IsManifold … 1 M → Work.Surgery.HasCollar n M) :
    Work.Orient.RelativeFundamentalClassExists n
```

i.e. it consumes the **general collar neighbourhood theorem** (a collar for *every* compact
`(n+1)`-manifold with boundary).  `Work.Orient.RelativeFundamentalClassExists 8` is one of the eight
inputs of the Pontryagin–Thom deliverable `Work.PTGeometric.transversalityCoreFamily` (the hypothesis
`hOrient`), which in turn is the only remaining input of this area's target
`Work.ThomBordism.thomRational` besides `Work.ThomBordism.BoundarySigma` (proved) and
`Work.ThomBordism.Smooth8Fundamental` (proved).  So *as long as the global form is the only form,
the general collar neighbourhood theorem sits on the critical path of `thomRational`*.

That is not how the geometry is used.  In the Pontryagin–Thom construction the manifold `W` at hand
comes with a collar *by construction* — `Work.PTGeometric.GenuineNullBordismData.collar` is a field
of the geometric data, produced by the fact that the null-homotopy is stationary near the collapse
end — and PTGEOMETRIC's own docstrings say so ("whose input, the collar, is produced by construction
in `GenuineNullBordismData.collar`").  What is needed is therefore the **pointwise** form: a collar
*of the given `W`* is enough.

That is what this file provides, with the same proof as ORIENT's global one: the core is the
complement `(collarRegion c 1)ᶜ` of the collar region of `c` (`CoreIsoOfCollar.collarRegion`), the
relative chain inclusion over that core is a quasi-isomorphism
(`CoreIsoOfCollar.isIso_relChainsIncl_of_collar`, the five-lemma step), it meets every path component
of the interior (`CoreIsoOfCollar.exists_path_to_compl_collarRegion`), and the rest of the argument is
`RelFundClassOfInteriorCore`'s (exported) one: `exists_coreClass` glues the local generators,
`IsRelFundClassOfCore` spreads the local-generator property over the interior and
`BoundaryOrientation` is the boundary formula.

## Main results

* `Work.ThomBordism.coreIso_of_collar` — the geometric core datum of `CoreIsoProp`, from a collar of
  the given manifold (the pointwise form of `Work.Orient.Boundary.CoreIsoOfCollar`);
* `Work.ThomBordism.exists_relFundClass_of_collar` — **ORIENT item 2 for a manifold with a collar**;
* `Work.ThomBordism.exists_relFundClass_of_collar'` — the same in the "consumer form" of
  `Work.Orient.exists_relFundClass_of_halfOrientation` (the local-generator property through
  `Work.ThomBordism.relChainsInclPunct`, i.e. the exact shape of the field
  `Work.ThomBordism.NullBordismFamily.w_fund`).

## Consequence for the wiring (for the project lead)

`Work.PTGeometric.Orientation.genuinePullbackOrientationData_of_orientation` (and the definitions
`BoundarySign`, `GenuineNullBordismDataRefined`, `GenuineRealisationRefined`) thread the *global*
`hOrient : Work.Orient.RelativeFundamentalClassExists 8`.  Replacing that parameter by the collar
datum they already carry (`GenuineNullBordismData.collar`, of shape
`∀ (W) [..] (hW) (_hbdry), Work.Surgery.HasCollar 8 W`) and calling
`Work.ThomBordism.exists_relFundClass_of_collar` at the manifold `W` at hand removes `hOrient` from
the interface of `Work.PTGeometric.transversalityCoreFamily` — and with it the general collar
neighbourhood theorem from the critical path of `Work.Drive.ThomRational`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism

noncomputable section

open Work.Orient.Boundary

variable {n : ℕ}

/-- **The core datum of `Work.Orient.CoreIsoProp`, from a collar of the given manifold.**

This is the body of `Work.Orient.Boundary.CoreIsoOfCollar` with the collar of the manifold *at hand*
instead of a function supplying a collar of every manifold: the core is `(collarRegion c 1)ᶜ`, the
relative chain inclusion over it is an isomorphism (the five-lemma step
`isIso_relChainsIncl_of_collar`), and it meets every path component of the interior
(`exists_path_to_compl_collarRegion`). -/
theorem coreIso_of_collar {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (c : Work.Surgery.Collar n M) :
    ∃ (C₀ : Set M) (_hCp : IsCompact C₀)
      (_hint : ∀ x ∈ C₀, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
      (_hconn : ∀ (x : M) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
        ∃ (y : M) (hy : y ∈ C₀)
          (hy' : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
          Nonempty (Path (⟨x, hx⟩ : {z : M //
              z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) ⟨y, hy'⟩)),
      IsIso (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of M)
        (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ)
        (fun y hy hyc => _hint y hyc hy)) (n + 1)) := by
  refine ⟨(collarRegion c 1)ᶜ,
    (isOpen_collarRegion c 1).isClosed_compl.isCompact, ?_, ?_, ?_⟩
  · intro x hx hxb
    exact hx (boundary_subset_collarRegion c one_pos hxb)
  · intro x hx
    exact exists_path_to_compl_collarRegion c one_pos x hx
  · have hb : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M ⊆
        (((collarRegion c 1)ᶜ)ᶜ) :=
      fun y hy hyc => hyc (boundary_subset_collarRegion c one_pos hy)
    exact isIso_relChainsIncl_of_collar c one_pos (((collarRegion c 1)ᶜ)ᶜ)
      (compl_compl _) hb (n + 1)

/-- **ORIENT item 2 for a compact manifold with a collar.**

For a compact `T2` `C^∞` `(n+1)`-manifold `M` with boundary, an orientation family `γ` and **a
collar `c` of `M`** (`Work.Surgery.Collar n M`, e.g. the collar produced by the Pontryagin–Thom
construction), there is a relative fundamental class `w ∈ H_{n+1}(M, ∂M; ℤ)` which is a local
generator at every interior point and whose `hPairδ` is a fundamental class of `∂M`.

This is `Work.Orient.Boundary.RelativeFundamentalClassExists` *at the given manifold*, so it does not
need the general collar neighbourhood theorem. -/
theorem exists_relFundClass_of_collar {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (c : Work.Surgery.Collar n M)
    (γ : ∀ x : M, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
      Work.Orient.LocH (TopCat.of M) (n + 1) x)
    (hγ : Work.Orient.IsHalfOrientationFamily n (TopCat.of M) γ) :
    ∃ w : (Work.Cohomology.relChains (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)).homology (n + 1),
      Work.Orient.IsRelFundClass (TopCat.of M) (n + 1)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) w ∧
      Work.Orient.IsFundClass
        (TopCat.of ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)) n
        (Work.Cohomology.hPairδ (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) n w) := by
  classical
  obtain ⟨C₀, hCp, hint, hconn, hiso⟩ := coreIso_of_collar (n := n) c
  obtain ⟨u₀, hu₀⟩ := exists_coreClass n (TopCat.of M) hCp hint γ hγ
  let φ : (Work.Cohomology.relChains (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)).homology (n + 1) ⟶
      (Work.Cohomology.relChains (TopCat.of M) C₀ᶜ).homology (n + 1) :=
    HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of M)
      (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ)
      (fun y hy hyc => hint y hyc hy)) (n + 1)
  obtain ⟨w, hw⟩ := ((ConcreteCategory.isIso_iff_bijective φ).mp hiso).2 u₀
  have hwfund : Work.Orient.IsRelFundClass (TopCat.of M) (n + 1)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) w := by
    apply IsRelFundClassOfCore n (TopCat.of M) C₀ hCp hint hconn w
    intro x hx
    have h1 : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M ⊆ C₀ᶜ :=
      fun t ht htC => hint t htC ht
    have hsubx : C₀ᶜ ⊆ ({x} : Set M)ᶜ :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
    have hfac : Work.Orient.relPunct (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x (hint x hx)
        = Work.Orient.relChainsIncl (TopCat.of M)
            (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ) h1
          ≫ Work.Cohomology.relCokerMap (TopCat.of M) C₀ᶜ ({x} : Set M)ᶜ hsubx := by
      rw [Work.Orient.relPunct_eq_relChainsIncl]
      rw [← Work.Orient.relChainsIncl_eq_relCokerMap (TopCat.of M) hsubx]
      rw [Work.Orient.relChainsIncl_trans (TopCat.of M) h1 hsubx]
    have hcomp := HomologicalComplex.homologyMap_comp
      (Work.Orient.relChainsIncl (TopCat.of M)
        (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ) h1)
      (Work.Cohomology.relCokerMap (TopCat.of M) C₀ᶜ ({x} : Set M)ᶜ hsubx) (n + 1)
    have hloc : (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x (hint x hx))
          (n + 1)).hom w
        = Work.Orient.resRelH (TopCat.of M) (n + 1)
            (Set.singleton_subset_iff.mpr hx) u₀ := by
      rw [hfac, hcomp, ModuleCat.comp_apply, show
        (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of M)
          (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ) h1)
          (n + 1)).hom w = u₀ from hw]
      rfl
    rw [hloc, hu₀ x hx]
    exact hγ.1 x (hint x hx)
  exact ⟨w, hwfund, BoundaryOrientation n (TopCat.of M) w hwfund⟩

/-- **The consumer form of `exists_relFundClass_of_collar`**: the local-generator property written
with `Work.ThomBordism.relChainsInclPunct`, i.e. exactly the shape of the field
`Work.ThomBordism.NullBordismFamily.w_fund` (compare
`Work.Orient.exists_relFundClass_of_halfOrientation`). -/
theorem exists_relFundClass_of_collar' {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (c : Work.Surgery.Collar n M)
    (γ : ∀ x : M, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
      Work.Orient.LocH (TopCat.of M) (n + 1) x)
    (hγ : Work.Orient.IsHalfOrientationFamily n (TopCat.of M) γ) :
    ∃ w : (Work.Cohomology.relChains (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)).homology (n + 1),
      Work.Orient.IsRelFundClass (TopCat.of M) (n + 1)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) w ∧
      (∀ (x : M) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
        Submodule.span ℤ {((HomologicalComplex.homologyMap
          (Work.ThomBordism.relChainsInclPunct (TopCat.of M)
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x hx) (n + 1)).hom w)} = ⊤) ∧
      Work.Orient.IsFundClass
        (TopCat.of ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)) n
        (Work.Cohomology.hPairδ (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) n w) := by
  obtain ⟨w, hw1, hw2⟩ := exists_relFundClass_of_collar (n := n) c γ hγ
  refine ⟨w, hw1, ?_, hw2⟩
  intro x hx
  rw [← Work.Orient.relPunct_eq_relChainsInclPunct (TopCat.of M)
    ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x hx]
  exact hw1 x hx

end

end Work.ThomBordism
