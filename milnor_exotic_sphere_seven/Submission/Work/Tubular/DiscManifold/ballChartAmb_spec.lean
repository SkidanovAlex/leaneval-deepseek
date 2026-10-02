import Mathlib
import Submission.Work.Tubular.DiscManifold.BallChartAmb
import Submission.Work.Tubular.DiscManifold.Defs
import Submission.Work.SignatureBordism.BallBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Tubular.DiscManifold

open scoped Manifold ContDiff Topology

open Work.SignatureBordism

theorem ballChartAmb_spec (n : ℕ) (b : Work.SignatureBordism.Ball n) :
    IsOpen (Work.Tubular.DiscManifold.ballChartAmb n b) ∧
      ∀ v ∈ Work.SignatureBordism.Ball n,
        (Work.Tubular.discPt n v ∈ (chartAt (Work.SignatureBordism.Half n) b).source ↔
          v ∈ Work.Tubular.DiscManifold.ballChartAmb n b) := by
  classical
  by_cases hb : b ∈ interiorSource n
  · -- the point `b` lies in the source of the centre chart
    have hdef : ballChartAmb n b
        = {v : EuclideanSpace ℝ (Fin (n + 1)) | -(1 / 2 : ℝ) < v 0 ∧ ‖v‖ < 1} := by
      rw [ballChartAmb, dif_pos hb]
    rw [hdef]
    refine ⟨?_, fun v hv => ?_⟩
    · exact (isOpen_lt continuous_const
          (by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin (n + 1)) => v 0)).inter
        (isOpen_lt (by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin (n + 1)) => ‖v‖)
          continuous_const)
    · have hc : chartAt (Half n) b = ballChartAt n b := rfl
      rw [discPt_of_mem n hv, hc, ballChartAt_of_mem n hb, interiorChart_source]
      simp only [interiorSource, Set.mem_ofPred_eq]
  · -- the point `b` is on a side of the ball: a half-ball chart
    have hdef : ballChartAmb n b
        = {v : EuclideanSpace ℝ (Fin (n + 1)) |
            0 < bsign (decide (0 < (b : EuclideanSpace ℝ (Fin (n + 1)))
              (ballCoord n b (ball_ne_zero_of_not_mem n hb))))
              * v (ballCoord n b (ball_ne_zero_of_not_mem n hb))} := by
      rw [ballChartAmb, dif_neg hb]
    rw [hdef]
    refine ⟨?_, fun v hv => ?_⟩
    · exact isOpen_lt continuous_const (by fun_prop)
    · have hc : chartAt (Half n) b
          = halfChart n (ballCoord n b (ball_ne_zero_of_not_mem n hb))
              (decide (0 < (b : EuclideanSpace ℝ (Fin (n + 1)))
                (ballCoord n b (ball_ne_zero_of_not_mem n hb)))) := by
        have hc' : chartAt (Half n) b = ballChartAt n b := rfl
        rw [hc', ballChartAt_of_not_mem n hb]
        rfl
      rw [discPt_of_mem n hv, hc, halfChart_source]
      simp only [halfSource, Set.mem_ofPred_eq]

end Work.Tubular.DiscManifold
