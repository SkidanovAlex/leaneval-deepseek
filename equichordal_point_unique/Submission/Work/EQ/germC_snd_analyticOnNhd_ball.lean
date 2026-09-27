import Mathlib
import Submission.Work.EQ.analyticAt_local_inverse
import Submission.Work.EQ.DefsCore

namespace Work.EQ

/-- The `y`-coordinate `v ↦ (germC a h v).2` of the stable germ curve is analytic at every point
of `Metric.ball 0 ρY`, given that `Yinv` is analytic on that ball and is both a left and a right
inverse of that `y`-coordinate there (`hY1`, `hY3`), and that the `y`-coordinate maps the closed
ball of radius `ρY` into the open one (`hstrict`). Route: per point `u₀` in the ball, apply
`Work.EQ.analyticAt_local_inverse` to `g := Yinv` on `U := Metric.ball 0 ρY` at
`υ := (germC a h u₀).2` (in `U` by `hstrict`, with `Yinv υ = u₀` by `hY3`; `Yinv` is injective on
`U` by `hY1`), and identify the analytic local inverse with the `y`-coordinate using `hY1`. -/
theorem germC_snd_analyticOnNhd_ball {a : ℝ} {h : ℂ → ℂ} {ρY : ℝ} (hρY : 0 < ρY)
    {Yinv : ℂ → ℂ} (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0:ℂ) ρY))
    (hY1 : ∀ y ∈ Metric.ball (0:ℂ) ρY, (Work.EQ.germC a h (Yinv y)).2 = y)
    (hY3 : ∀ w, w ∈ Metric.ball (0:ℂ) ρY → Yinv ((Work.EQ.germC a h w).2) = w)
    (hstrict : ∀ w : ℂ, ‖w‖ ≤ ρY → ‖(Work.EQ.germC a h w).2‖ < ρY) :
    AnalyticOnNhd ℂ (fun v : ℂ => (Work.EQ.germC a h v).2) (Metric.ball (0:ℂ) ρY) := by
  intro u₀ hu₀
  -- `u₀` lies in the closed ball, so its image `υ` lies in the open ball
  have hu₀le : ‖u₀‖ ≤ ρY := by
    exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hu₀)
  have hυ : (germC a h u₀).2 ∈ Metric.ball (0 : ℂ) ρY := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hstrict u₀ hu₀le
  have hYinvυ : Yinv ((germC a h u₀).2) = u₀ := hY3 u₀ hu₀
  -- `Yinv` is injective on the ball, being a left inverse of the `y`-coordinate
  have hinj : Set.InjOn Yinv (Metric.ball (0 : ℂ) ρY) := by
    intro y hy y' hy' h
    have h1 := hY1 y hy
    have h2 := hY1 y' hy'
    rw [h] at h1
    rw [h1] at h2
    exact h2
  -- the holomorphic local inverse of `Yinv` at `υ`
  obtain ⟨ε, hε, ψ, hψan, hψ0, hψinv, hψU⟩ :=
    analyticAt_local_inverse Metric.isOpen_ball hYan hinj hυ
  rw [hYinvυ] at hψan hψinv hψU
  have hψat : AnalyticAt ℂ ψ u₀ := by
    refine hψan u₀ ?_
    rw [Metric.mem_ball, dist_self]
    exact hε
  -- on a neighbourhood of `u₀` the local inverse agrees with the `y`-coordinate
  refine hψat.congr ?_
  filter_upwards [Metric.ball_mem_nhds u₀ hε] with w hw
  have h1 := hY1 (ψ w) (hψU w hw)
  rw [hψinv w hw] at h1
  exact h1.symm

end Work.EQ
