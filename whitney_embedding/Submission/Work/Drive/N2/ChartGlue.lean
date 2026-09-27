import Mathlib
import Submission.Work.Drive.N2.HeightBasics
import Submission.Work.Drive.N2.ChartSplit
import Submission.Work.Embedding.exists_unique_closest_point

/-!
# Glue between chart representations and the `(a,b)`-minor regions

For an immersion `e : M → ℝ⁵` and a chart at `p`, the *minor region* of the coordinate pair
`(a,b)` is the open set of points of the chart target where the `(a,b)`-minor of the chart
representation is invertible.  On it the chart representation is a submersion and its derivative is
injective (because `e` is an immersion).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace
open MeasureTheory
open Work.Drive.Morse
open Work.Projection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-- The region of a chart on which the `(a,b)`-minor of the chart representation is invertible. -/
def minorRegion (e : M → EuclideanSpace ℝ (Fin 5)) (p : M) (a b : Fin 5) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {y | y ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target ∧
    (minor (chartRep e p) a b y).det ≠ 0}

lemma minorRegion_subset_target (e : M → EuclideanSpace ℝ (Fin 5)) (p : M) (a b : Fin 5) :
    minorRegion e p a b ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target := fun _ hy => hy.1

/-- The chart representation is `C^∞` on the minor region. -/
lemma contDiffOn_minorRegion (e : M → EuclideanSpace ℝ (Fin 5))
    (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) (p : M) (a b : Fin 5) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chartRep e p) (minorRegion e p a b) :=
  (Work.Embedding.contMDiffOn_chartRepN e he p).contDiffOn.mono (minorRegion_subset_target e p a b)

/-- The chart representation is differentiable at every point of the minor region. -/
lemma differentiableAt_minorRegion (e : M → EuclideanSpace ℝ (Fin 5))
    (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) (p : M) (a b : Fin 5)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ minorRegion e p a b) :
    DifferentiableAt ℝ (chartRep e p) y :=
  ((Work.Embedding.contDiffAt_chartRepN e he p hy.1).differentiableAt (by simp))

/-- The derivative of the chart representation is injective on the minor region. -/
lemma injective_fderiv_minorRegion (e : M → EuclideanSpace ℝ (Fin 5))
    (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) (himm : ∀ x, Function.Injective (mfderiv (𝓡 2) (𝓡 5) e x))
    (p : M) (a b : Fin 5) {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ minorRegion e p a b) :
    Function.Injective (fderiv ℝ (chartRep e p) y) :=
  Work.Embedding.injective_fderiv_chartRep_infty e he himm p hy.1

/-- Invertibility of the `(a,b)`-minor is equivalent to the non-vanishing of its determinant. -/
lemma bijective_minor_iff_det_ne_zero (e : M → EuclideanSpace ℝ (Fin 5)) (p : M) (a b : Fin 5)
    (y : EuclideanSpace ℝ (Fin 2)) :
    Function.Bijective (minor (chartRep e p) a b y) ↔
      (minor (chartRep e p) a b y).det ≠ 0 := by
  rw [← ContinuousLinearMap.isUnit_iff_bijective, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap,
    LinearMap.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero

end Work.Drive.N2
