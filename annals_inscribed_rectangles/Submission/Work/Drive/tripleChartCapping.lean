import Mathlib
import Submission.Work.Drive.tripleChartBridge
import Submission.Work.Drive.fderiv_chartAt_cappingCharted
import Submission.Work.Drive.fderiv_chartAt_halfLineProjective
import Submission.Work.Drive.planeChain

/-!
# The genericity data of the triple engine, in the coordinates `(0,∞) × ℝP³` of the capping space

`Work.Drive.Meet3Generic` asks, at a triple point of three chains
`D k : ℝ³ → Y` with `Y = Work.Drive.CappingSpace`, for the manifold transversality
`TripleTransverse (mfderiv D k (x k))` and for the common-direction (face) condition.

This file chains the two bridges

* `Work.Drive.tripleTransverse_mfderiv_iff_fderiv_chartAt_self` /
  `Work.Drive.tripleCommonDir_mfderiv_iff_fderiv_chartAt_self` — the condition may be checked in any
  chart, and conveniently in the chart at the triple point itself;
* `Work.Drive.fderiv_chartAt_cappingCharted` — the chart of `Y` is the chart of `(0,∞) × ℝP³` read
  through `cappingSpaceHomeoProj`,

into the statement that **the genericity data of the concrete chains of the counting chapter may be
verified in the coordinates `(0,∞) × ℝP³`**, namely as the transversality of
`fderiv (chartAt (cappingSpaceHomeoProj ·) ∘ cappingSpaceHomeoProj ∘ D k)`, which
`Work.Drive.fderiv_chartAt_halfLineProjective` reduces further to the explicit chart coordinates
`(log ∘ levelOf, projChartMap i ∘ cls)`.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

attribute [local instance] Work.Drive.cappingCharted Work.Drive.halfLineProjectiveCharted
  Work.Drive.isManifold_cappingCharted Work.Drive.t2Space_cappingSpace

/-- **Triple transversality in the `(0,∞) × ℝP³` coordinates of the capping space.** -/
theorem tripleTransverse_mfderiv_iff_fderiv_halfLineProjective
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → Work.Drive.CappingSpace)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hcont : ∀ k, ContinuousAt (D k) (x k))
    (heq1 : D 0 (x 0) = D 1 (x 1)) (heq2 : D 0 (x 0) = D 2 (x 2)) :
    TripleTransverse (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0))
        (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1)) (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2))
      ↔ TripleTransverse
          (fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
              (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
              Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj (D 0 (x 0)))
              (Work.Drive.cappingSpaceHomeoProj (D 0 u))) (x 0))
          (fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
              (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
              Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj (D 0 (x 0)))
              (Work.Drive.cappingSpaceHomeoProj (D 1 u))) (x 1))
          (fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
              (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
              Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj (D 0 (x 0)))
              (Work.Drive.cappingSpaceHomeoProj (D 2 u))) (x 2)) := by
  have hsrc : ∀ k : Fin 3, D k (x k) ∈
      (chartAt (EuclideanSpace ℝ (Fin 4)) (D 0 (x 0))).source := by
    intro k
    have hk : D k (x k) = D 0 (x 0) := by
      fin_cases k
      · rfl
      · exact heq1.symm
      · exact heq2.symm
    rw [hk]
    exact mem_chart_source _ _
  have h0 := fderiv_chartAt_cappingCharted (D 0) (x 0) (D 0 (x 0)) (hcont 0) (hsrc 0)
  have h1 := fderiv_chartAt_cappingCharted (D 1) (x 1) (D 0 (x 0)) (hcont 1) (hsrc 1)
  have h2 := fderiv_chartAt_cappingCharted (D 2) (x 2) (D 0 (x 0)) (hcont 2) (hsrc 2)
  rw [tripleTransverse_mfderiv_iff_fderiv_chartAt_self D hD x heq1 heq2, h0, h1, h2]

/-- **The common-direction (face) condition in the `(0,∞) × ℝP³` coordinates.** -/
theorem tripleCommonDir_mfderiv_iff_fderiv_halfLineProjective
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → Work.Drive.CappingSpace)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hcont : ∀ k, ContinuousAt (D k) (x k))
    (heq1 : D 0 (x 0) = D 1 (x 1)) (heq2 : D 0 (x 0) = D 2 (x 2))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDir (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0))
        (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1)) (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2)) v
      ↔ TripleCommonDir
          (fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
              (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
              Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj (D 0 (x 0)))
              (Work.Drive.cappingSpaceHomeoProj (D 0 u))) (x 0))
          (fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
              (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
              Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj (D 0 (x 0)))
              (Work.Drive.cappingSpaceHomeoProj (D 1 u))) (x 1))
          (fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
              (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
              Work.Drive.halfLineProjectiveCharted (Work.Drive.cappingSpaceHomeoProj (D 0 (x 0)))
              (Work.Drive.cappingSpaceHomeoProj (D 2 u))) (x 2)) v := by
  have hsrc : ∀ k : Fin 3, D k (x k) ∈
      (chartAt (EuclideanSpace ℝ (Fin 4)) (D 0 (x 0))).source := by
    intro k
    have hk : D k (x k) = D 0 (x 0) := by
      fin_cases k
      · rfl
      · exact heq1.symm
      · exact heq2.symm
    rw [hk]
    exact mem_chart_source _ _
  have h0 := fderiv_chartAt_cappingCharted (D 0) (x 0) (D 0 (x 0)) (hcont 0) (hsrc 0)
  have h1 := fderiv_chartAt_cappingCharted (D 1) (x 1) (D 0 (x 0)) (hcont 1) (hsrc 1)
  have h2 := fderiv_chartAt_cappingCharted (D 2) (x 2) (D 0 (x 0)) (hcont 2) (hsrc 2)
  rw [tripleCommonDir_mfderiv_iff_fderiv_chartAt_self D hD x heq1 heq2 v, h0, h1, h2]

end

end Work.Drive
