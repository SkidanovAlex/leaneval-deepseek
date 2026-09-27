import Mathlib
import Submission.Work.Whitney.exists_sheet_model
import Submission.Work.Whitney.localPushNTrans_aux

/-!
# Sheet-model consequences used by the cut form of the local Whitney push

For a sheet parametrisation `σ : ℝⁿ → M` of a branch of an immersion `f : M → ℝ^{2n}` presented
by `Φ (f (σ u) - f p) = (u, h u)`, we derive

* `IsOpen (σ '' ball 0 ρ)` for every `ρ ≤ R₀` (from the identity, by the "section" trick), and
* `frontier (σ '' closedBall 0 ρ) ⊆ σ '' sphere 0 ρ`.
-/

open scoped Manifold ContDiff
open Topology Metric Set

namespace Work.Whitney

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- A sheet parametrisation is a right section of the first `Φ`-coordinate of `f`, so the image of
every smaller ball is open. -/
theorem isOpen_sheet_ball (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : Continuous f)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (σ : EuclideanSpace ℝ (Fin n) → M)
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (p : M) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hsheet : ∀ u, ‖u‖ ≤ R₀ → Φ (f (σ u) - f p) = (u, h u))
    (hinj : Set.InjOn σ (Metric.closedBall 0 R₀))
    (hopen : IsOpen (σ '' Metric.ball 0 R₀))
    (ρ : ℝ) (hρ : ρ ≤ R₀) :
    IsOpen (σ '' Metric.ball 0 ρ) := by
  refine isOpen_image_ball_of_section σ (fun x => (Φ (f x - f p)).1) R₀ ?_ ?_ hinj hopen ρ hρ
  · exact (Φ.continuous.comp (hf.sub continuous_const)).fst
  · intro u hu
    rw [hsheet u hu]

/-- The frontier of the image of a closed ball of a sheet consists of images of sphere points. -/
theorem frontier_sheet_closedBall (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : Continuous f)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (σ : EuclideanSpace ℝ (Fin n) → M)
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (p : M) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hsheet : ∀ u, ‖u‖ ≤ R₀ → Φ (f (σ u) - f p) = (u, h u))
    (hσcont : Continuous σ)
    (hinj : Set.InjOn σ (Metric.closedBall 0 R₀))
    (hopen : IsOpen (σ '' Metric.ball 0 R₀))
    (ρ : ℝ) (hρ : ρ ≤ R₀) :
    frontier (σ '' Metric.closedBall 0 ρ) ⊆ σ '' Metric.sphere 0 ρ := by
  refine frontier_image_closedBall_subset σ ρ (isOpen_sheet_ball f hf Φ σ h p R₀ hR₀ hsheet hinj hopen ρ hρ) ?_ ?_
  · exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ).image hσcont |>.isClosed
  · exact hinj.mono (fun y hy => by
      rw [mem_closedBall_zero_iff] at hy ⊢; linarith)

end Work.Whitney
