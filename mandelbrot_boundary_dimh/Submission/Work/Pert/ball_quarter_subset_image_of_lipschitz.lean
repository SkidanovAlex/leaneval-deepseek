import Mathlib
import Submission.Work.Pert.RoucheBridge

namespace Work.Pert

/-- A map of the disc which is `O(R/2)`-close to the identity on the boundary circle covers a
quarter-disc around the origin.  Proof by Rouché
(`Commons.Analysis.Complex.rouche_simple_zero`, re-exported by `Work.Pert.RoucheBridge`): for
`‖w‖ < R/4` apply it with `f = id`, `a = 0` and `g u = F u - w` on the disc `ball 0 R`.  On the
sphere `‖g u‖ ≤ ‖F u‖ + ‖w‖ ≤ R/2 + R/4 < R = ‖u‖`, and `id + g = fun u => u + F u - w` vanishes
at `u` iff `u + F u = w`. -/
theorem ball_quarter_subset_image_of_lipschitz {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.closedBall (0 : ℂ) R))
    (hlip : ∀ u ∈ Metric.sphere (0 : ℂ) R, ‖F u‖ ≤ R / 2) :
    Metric.ball (0 : ℂ) (R / 4) ⊆ (fun u : ℂ => u + F u) '' Metric.ball (0 : ℂ) R := by
  intro w hw
  have hwlt : ‖w‖ < R / 4 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  -- Rouché's hypothesis on the boundary sphere
  have hlt : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖F z - w‖ < ‖(fun u : ℂ => u) z‖ := by
    intro z hz
    show ‖F z - w‖ < ‖z‖
    have hzR : ‖z‖ = R := by simpa using hz
    calc ‖F z - w‖ ≤ ‖F z‖ + ‖w‖ := norm_sub_le _ _
      _ < R / 2 + R / 4 := by linarith [hlip z hz]
      _ < R := by linarith
      _ = ‖z‖ := hzR.symm
  -- Rouché with `f = id`, `g = F - w`, `a = 0`: `id + g = fun u => u + F u - w` has a unique
  -- zero `z` in the disc, i.e. `z + F z = w`.
  obtain ⟨z, hz, hz0, -⟩ :=
    Commons.Analysis.Complex.rouche_simple_zero (R := R) hR (f := fun u : ℂ => u)
      (g := fun u : ℂ => F u - w) (a := 0)
      (by simpa using hR) differentiableOn_id continuousOn_id
      (hF.sub (differentiableOn_const w))
      (hF.continuousOn.sub continuousOn_const)
      hlt (by simp) (by simp) (fun z _ h0 => h0)
  exact ⟨z, hz, by linear_combination hz0⟩

end Work.Pert
