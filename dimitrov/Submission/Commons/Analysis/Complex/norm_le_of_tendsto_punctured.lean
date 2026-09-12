import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.RingTheory.PicardGroup

namespace Commons.Analysis.Complex

open Filter Metric Set
open scoped Topology

theorem norm_le_of_tendsto_punctured {f : ℂ → ℂ} {L : ℂ}
    (hf : ∀ u : ℂ, 0 < ‖u‖ → ‖u‖ < 1 → DifferentiableAt ℂ f u)
    (hL : Filter.Tendsto f (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds L))
    {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) :
    ∃ u ∈ Metric.sphere (0 : ℂ) R, ‖L‖ ≤ ‖f u‖ := by
  classical
  set g : ℂ → ℂ := Function.update f 0 L with hg
  -- `g` is continuous at `0` by construction.
  have hg_cont : ContinuousAt g 0 := by
    rw [hg]
    exact continuousAt_update_same.2 hL
  -- `g` agrees with `f` away from `0`.
  have hg_ne : ∀ z : ℂ, z ≠ 0 → g z = f z := by
    intro z hz
    rw [hg]
    exact Function.update_of_ne hz L f
  -- `g` is differentiable on the punctured unit disk.
  have hdiff_g : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → DifferentiableAt ℂ g z := by
    intro z hz0 hz1
    have hzne : z ≠ 0 := by rwa [norm_pos_iff] at hz0
    have heq : g =ᶠ[𝓝 z] f := by
      filter_upwards [(isOpen_compl_singleton (x := (0 : ℂ))).mem_nhds (by simpa using hzne)]
        with w hw
      exact hg_ne w (by simpa using hw)
    exact (hf z hz0 hz1).congr_of_eventuallyEq heq
  -- hence `g` is differentiable in a punctured neighbourhood of `0`
  have hd_g : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ g z := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1)] with z hz hzne
    exact hdiff_g z (by rw [norm_pos_iff]; simpa using hzne)
      (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  -- removable singularity: `g` is analytic, hence differentiable, at `0`
  have hg_analytic : AnalyticAt ℂ g 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd_g hg_cont
  -- `g` is differentiable on the unit ball
  have hg_diffOn : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rcases eq_or_ne z 0 with rfl | hzne
    · exact hg_analytic.differentiableAt.differentiableWithinAt
    · exact (hdiff_g z (by rw [norm_pos_iff]; exact hzne) hz).differentiableWithinAt
  -- so it satisfies the hypotheses of the maximum modulus principle on the disk of radius `R`
  have hgDiffCont : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) :=
    DiffContOnCl.mk_ball
      (hg_diffOn.mono (Metric.ball_subset_ball (le_of_lt hR1)))
      (hg_diffOn.continuousOn.mono (Metric.closedBall_subset_ball hR1))
  obtain ⟨z, hzfront, hzmax⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm (f := g) (U := Metric.ball (0 : ℂ) R)
      Metric.isBounded_ball ⟨0, Metric.mem_ball_self hR0⟩ hgDiffCont
  have hzsphere : z ∈ Metric.sphere (0 : ℂ) R := by
    rw [← frontier_ball (0 : ℂ) hR0.ne']
    exact hzfront
  refine ⟨z, hzsphere, ?_⟩
  have h0clos : (0 : ℂ) ∈ closure (Metric.ball (0 : ℂ) R) :=
    subset_closure (Metric.mem_ball_self hR0)
  have hle : ‖g 0‖ ≤ ‖g z‖ := hzmax h0clos
  have hg0 : g 0 = L := by
    rw [hg]; exact Function.update_self 0 L f
  have hzne : z ≠ 0 := by
    intro h
    rw [h, Metric.mem_sphere, dist_self] at hzsphere
    linarith [hzsphere.symm]
  rw [hg0] at hle
  rw [hg_ne z hzne] at hle
  exact hle

end Commons.Analysis.Complex