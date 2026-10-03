import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.dirichlet_circle_boundary
import Submission.Lib.Unif2.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Dirichlet

theorem dirichlet_ball {c : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℝ}
    (hF : ContinuousOn F (sphere c R)) :
    ∃ u : ℂ → ℝ,
      (∀ z : ℂ, ‖z - c‖ < R → HarmonicAt u z) ∧
      ContinuousOn (fun z : ℂ => if ‖z - c‖ < R then u z else F z) (closedBall c R) := by
  classical
  -- Reduce to the Dirichlet problem for the ball of radius R centered at 0
  -- (already available in the shared commons) by translating the data:
  -- boundary data g(w) = F (c + w) on the circle sphere 0 R.
  let g : ℂ → ℝ := fun w => F (c + w)
  have hg : ContinuousOn g (sphere (0 : ℂ) R) := by
    dsimp [g]
    refine ContinuousOn.comp hF ?_ ?_
    · fun_prop
    · intro w hw
      have hwn : ‖w‖ = R := by simpa [Metric.sphere, dist_eq_norm] using hw
      simpa [Metric.sphere, dist_eq_norm] using hwn
  rcases Commons.Analysis.Complex.Harmonic.dirichlet_circle_boundary (g := g) (r := R) hR hg
    with ⟨P, hP, hPg⟩
  refine ⟨fun z : ℂ => P (z - c), ?_, ?_⟩
  · -- harmonicity: translation preserves harmonicity (composition with an
    -- analytic affine map), and P is harmonic on ball 0 R
    intro z hz
    have hw : z - c ∈ ball (0 : ℂ) R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hPw : HarmonicAt P (z - c) := hP.harmonicOnNhd (z - c) hw
    have hf : AnalyticAt ℂ (fun y : ℂ => y - c) z := by
      exact AnalyticAt.sub (𝕜 := ℂ) (f := fun y : ℂ => y) (g := fun _ : ℂ => c) (x := z)
        analyticAt_id (analyticAt_const (v := c) (x := z))
    exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (u := P) (f := fun y : ℂ => y - c) (x := z) hf hPw
  · -- continuity of the glued map on the closed ball
    have hPcont : ContinuousOn P (closedBall (0 : ℂ) R) :=
      InnerProductSpace.HarmonicContOnCl.continuousOn_ball hP
    let T : ℂ → ℂ := fun z => z - c
    let glued0 : ℂ → ℝ := fun w => if ‖w‖ < R then P w else F (c + w)
    have hEqOn0 : Set.EqOn glued0 P (closedBall (0 : ℂ) R) := by
      intro w hw
      have hwle : ‖w‖ ≤ R := by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hw)
      by_cases hwlt : ‖w‖ < R
      · simp [glued0, hwlt]
      · have hwR : ‖w‖ = R := le_antisymm hwle (le_of_not_gt hwlt)
        have hwP : P w = g w := hPg w hwR
        simp [glued0, hwlt, ← hwP, g]
    have hglued0_cont : ContinuousOn glued0 (closedBall (0 : ℂ) R) := by
      exact hPcont.congr hEqOn0
    have hTmap : MapsTo T (closedBall c R) (closedBall (0 : ℂ) R) := by
      intro z hz
      have hle : ‖z - c‖ ≤ R := by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hz)
      simpa [T, dist_eq_norm] using hle
    have hcomp : ContinuousOn (glued0 ∘ T) (closedBall c R) :=
      ContinuousOn.comp hglued0_cont (by fun_prop : ContinuousOn T (closedBall c R)) hTmap
    refine hcomp.congr ?_
    intro z hz
    by_cases hlt : ‖z - c‖ < R
    · simp [hlt, T, glued0]
    · simp [hlt, T, glued0]

end Commons.Analysis.Complex.Dirichlet
