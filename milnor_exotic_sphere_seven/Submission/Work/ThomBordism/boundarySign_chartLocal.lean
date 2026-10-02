import Mathlib
import Submission.Work.ThomBordism.locClass_hPairDelta_eq_of_localClass_eq
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.PTGeometric.HOFEuclid
import Submission.Work.PTGeometric.isOrientFamily_eq_smul_of_connected
import Submission.Work.Orient.Boundary.BoundaryOrientation
import Submission.Work.ThomBordism.modelHalfOrientation
import Submission.Work.ThomBordism.boundarySign_span_locClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Manifold

namespace Work.ThomBordism

/-- The chart-local boundary sign: the local class at `y` of the boundary class of a relative class
whose local class at the interior point `x₀` in the half-ball piece around `y` is the chart
generator, expressed in the boundary chart `eb`, is `±` the chart generator. -/
theorem boundarySign_chartLocal
    (n : ℕ) (hn : 1 ≤ n)
    (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (e : OpenPartialHomeomorph W (Work.PTGeometric.HOF.Euc (n + 1)))
    (eb : OpenPartialHomeomorph ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      (Work.PTGeometric.HOF.Euc n))
    {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hyeb : (⟨y, hy⟩ : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) ∈ eb.source)
    {r : ℝ} (hr : 0 < r)
    (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.halfBallPiece (n + 1) W y r)
    (hx₀int : x₀ ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hx₀e : x₀ ∈ e.source)
    (w : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
    (hw : (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
            x₀ hx₀int) (n + 1)).hom w
        = Work.PTGeometric.HOF.chartTr e x₀ hx₀e
            (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (e x₀))) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
        ((Work.Cohomology.hPairδ W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n).hom w) ⟨y, hy⟩
      = c • Work.PTGeometric.HOF.chartTr (W := TopCat.of
            ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) eb ⟨y, hy⟩ hyeb
          (Work.PTGeometric.HOF.eucFam n hn (eb ⟨y, hy⟩)) := by
  classical
  have hgen : Submodule.span ℤ (Set.singleton ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          x₀ hx₀int) (n + 1)).hom w)) = ⊤ := by
    rw [hw]
    exact span_chartTr_eucFam (W := W) (N := n + 1) (by omega) e x₀ hx₀e
  have hspanL : Submodule.span ℤ (Set.singleton (Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
        ((Work.Cohomology.hPairδ W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n).hom w) ⟨y, hy⟩)) = ⊤ :=
    boundarySign_span_locClass n hn W hy hr hgood hx₀ hx₀int w hgen
  have hspanG : Submodule.span ℤ (Set.singleton (Work.PTGeometric.HOF.chartTr (W := TopCat.of
        ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) eb ⟨y, hy⟩ hyeb
        (Work.PTGeometric.HOF.eucFam n hn (eb ⟨y, hy⟩)))) = ⊤ :=
    span_chartTr_eucFam (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
      hn eb ⟨y, hy⟩ hyeb
  have hsurjU : Function.Surjective (Work.PTGeometric.HOF.chartInvCore (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
      eb ⟨y, hy⟩ hyeb) :=
    fun v => Exists.intro (Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) eb ⟨y, hy⟩ hyeb v)
      (Work.PTGeometric.HOF.chartInvCore_chartTr (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) eb ⟨y, hy⟩ hyeb v)
  have hspanU : Submodule.span ℤ (Set.singleton (Work.PTGeometric.HOF.chartInvCore (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
      eb ⟨y, hy⟩ hyeb
      (Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
        ((Work.Cohomology.hPairδ W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n).hom w) ⟨y, hy⟩))) = ⊤ :=
    Work.Orient.Boundary.span_eq_top_of_surjective _ hsurjU hspanL
  obtain ⟨eiso⟩ := Work.PTGeometric.nonempty_locH_iso_int n hn
    (TopCat.of (Work.PTGeometric.HOF.Euc n)) (eb ⟨y, hy⟩)
  obtain ⟨c, hc, heq⟩ := Work.PTGeometric.exists_pm_one_smul_eq_of_span_eq_top eiso.toLinearEquiv
    (Work.PTGeometric.HOF.eucFam_gen n hn (eb ⟨y, hy⟩)) hspanU
  refine ⟨c, hc, ?_⟩
  have h := congrArg (fun z => Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) eb ⟨y, hy⟩ hyeb z) heq
  simp only [map_zsmul] at h
  rwa [Work.PTGeometric.HOF.chartTr_chartInvCore (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) eb ⟨y, hy⟩ hyeb] at h

end Work.ThomBordism
