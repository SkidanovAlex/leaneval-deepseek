import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseKinLoc.NeuFrac.lamBox_subset_ball
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.exists_box_bump`

For every side `ℓ` and every translation `u` there is a radius `R` containing the moving box
`Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` (FS `eq:Theta`, the corpus's `lamBox`/`bsBox`) and a `C^∞`
compactly supported bump `η` which is identically `1` in a whole neighbourhood of the closed
ball `B(0,R)`.

This is the elementary "cut off the localisation ball" input: `Λ(u)` is a bounded set, so it
sits in `B(0,R)`, and any smooth compactly supported function that equals `1` near `B(0,R)`
can be multiplied into a trial function without changing it on the box while gaining compact
support.

The radius is `R = ‖ℓ·u‖ + 2(|ℓ|+1)`: the box lies in the closed ball of radius `2(|ℓ|+1)`
about its centre `ℓ·u` (`Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall`), and `ℓ·u` lies
within `‖ℓ·u‖` of the origin.  The bump is then the `ContDiffBump` centred at `0` with inner
radius `R+1` and outer radius `R+2`; it is `1` on the closed ball of radius `R+1 ⊇ B(0,R)`,
hence a neighbourhood of every point of `B(0,R)`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology ContDiff ENNReal

namespace Work.BoseKinLoc.NeuFrac

set_option linter.unusedVariables false

/-- For every `R ≥ 0` there is a smooth compactly supported `η` which is eventually (hence on a
neighbourhood of each point) equal to `1` on the closed ball of radius `R`. -/
private lemma exists_bump_of_le {R : ℝ} (hR : 0 ≤ R) :
    ∃ η : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiff ℝ (⊤ : ENat) η ∧ HasCompactSupport η ∧
        ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R → η =ᶠ[nhds z] 1 := by
  refine ⟨(fun z => (⟨R + 1, R + 2, by linarith, by linarith⟩ :
      ContDiffBump (0 : EuclideanSpace ℝ (Fin 3))) z), ?_, ?_, ?_⟩
  · exact ContDiffBump.contDiff _
  · exact ContDiffBump.hasCompactSupport _
  · intro z hz
    refine ContDiffBump.eventuallyEq_one_of_mem_ball _ ?_
    rw [Metric.mem_ball, dist_zero_right]
    linarith

lemma exists_box_bump (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ (R : ℝ) (η : EuclideanSpace ℝ (Fin 3) → ℝ),
      Work.BoseKinLoc.lamBox ℓ u ⊆ Metric.closedBall 0 R ∧
        ContDiff ℝ (⊤ : ENat) η ∧ HasCompactSupport η ∧
          ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R → η =ᶠ[nhds z] 1 := by
  obtain ⟨η, hcd, hcs, hη⟩ :=
    exists_bump_of_le (R := ‖ℓ • u‖ + 2 * (|ℓ| + 1)) (by positivity)
  refine ⟨‖ℓ • u‖ + 2 * (|ℓ| + 1), η, ?_, hcd, hcs, ?_⟩
  · intro x hx
    have h1 : dist x (ℓ • u) ≤ 2 * (|ℓ| + 1) :=
      Metric.mem_closedBall.mp (lamBox_subset_closedBall ℓ u hx)
    rw [Metric.mem_closedBall]
    have h2 : dist x 0 ≤ dist x (ℓ • u) + ‖ℓ • u‖ := by
      rw [← dist_zero_right (ℓ • u)]
      exact dist_triangle x (ℓ • u) 0
    linarith
  · intro z hz
    exact hη z hz

end Work.BoseKinLoc.NeuFrac
