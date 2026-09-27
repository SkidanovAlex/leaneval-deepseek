import Mathlib
import Submission.Work.CriticalSet.Defs

open scoped Topology

namespace Work.CriticalSet

/-- **A regular value of a holomorphic function has finitely many preimages in a compact disc**
(the "transverse crossings" half of the disc-filling argument, in the holomorphic setting).

Let `f : ℂ → ℂ` be complex analytic on the ball of radius `ρ` around `0`, let `0 < r < ρ`, and let `y`
be a value not attained at any critical point of `f` inside that ball.  Then `{z | ‖z‖ ≤ r, f z = y}` is
finite.

Proof strategy.  For `z` with `dist z 0 ≤ r < ρ` and `f z = y`, the analytic function `f - y` has a zero
at `z` with `deriv (f - y) z = deriv f z ≠ 0`; hence
(`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` applied to `f - y`, the first alternative being
excluded because it would force `deriv f z = 0`) the zero is isolated: there is an open neighbourhood
`u` of `z` with `u ∩ {w | f w = y} = {z}`.  So the preimage set `P := {z | dist z 0 ≤ r ∧ f z = y}` is
discrete (`isDiscrete_iff_forall_mem_exists_isOpen`), and it is closed in the compact set
`Metric.closedBall 0 r` because `f` is continuous on the ball of radius `ρ` (analytic functions are
continuous, `AnalyticOnNhd.continuousOn`).  Closed in a compact set it is compact, and a compact
discrete set is finite (`IsCompact.finite` with `isCompact_closedBall`). -/
theorem analytic_finite_preimage_of_regularValue {f : ℂ → ℂ} {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 ρ)) {y : ℂ}
    (hy : ∀ z, dist z 0 < ρ → f z = y → deriv f z ≠ 0) :
    ({z : ℂ | dist z 0 ≤ r ∧ f z = y}).Finite := by
  -- The set of preimages of `y` inside the closed disc of radius `r`.
  set P : Set ℂ := {z : ℂ | dist z 0 ≤ r ∧ f z = y} with hP
  -- `P` sits inside the closed disc, which in turn sits in the ball on which `f` is analytic.
  have hP_closedBall : P ⊆ Metric.closedBall (0 : ℂ) r := by
    intro z hz
    rw [hP] at hz
    simpa [Metric.mem_closedBall] using hz.1
  have hCB : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) ρ := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    exact lt_of_le_of_lt hz hrρ
  have hPsub : P ⊆ Metric.ball (0 : ℂ) ρ := hP_closedBall.trans hCB
  -- `P` is closed: it is the intersection of the closed disc with the preimage of `{y}`, and `f` is
  -- continuous on the closed disc (which is contained in the ball of analyticity and compact).
  have hclosed : IsClosed P := by
    have hcont : ContinuousOn f (Metric.closedBall (0 : ℂ) r) := hf.continuousOn.mono hCB
    have h := hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall
      (t := {y}) isClosed_singleton
    have heq : Metric.closedBall (0 : ℂ) r ∩ f ⁻¹' {y} = P := by
      rw [hP]
      ext z
      simp [Metric.mem_closedBall]
    rwa [heq] at h
  have hcompact : IsCompact P :=
    (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset hclosed hP_closedBall
  -- `P` is discrete: the preimages of a regular value are isolated zeros of `f - y`.
  have hdiscrete : IsDiscrete P := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro z hz
    have hzP : dist z 0 ≤ r ∧ f z = y := by simpa [hP] using hz
    have hzball : z ∈ Metric.ball (0 : ℂ) ρ := hPsub hz
    have hzan : AnalyticAt ℂ (fun w => f w - y) z := (hf z hzball).sub analyticAt_const
    rcases hzan.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · -- First alternative: `f - y` vanishes near `z`, so `f` is locally constant `y` there and
      -- `deriv f z = 0`, contradicting that `y` is a regular value.
      exfalso
      have hfe : f =ᶠ[𝓝 z] (fun _ => y) := by
        filter_upwards [hzero] with w hw
        simpa using sub_eq_zero.mp hw
      have hd : deriv f z = 0 := by
        have h' := hfe.deriv_eq
        rwa [deriv_const] at h'
      exact hy z hzball hzP.2 hd
    · -- Second alternative: `f - y` is nonzero on a punctured neighbourhood of `z`; the ball of
      -- that neighbourhood meets `P` only in `z`.
      rw [eventually_nhdsWithin_iff] at hne
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hne
      refine ⟨Metric.ball z ε, Metric.isOpen_ball, ?_⟩
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hw, hwP⟩
        have hfwy : f w = y := (by simpa [hP] using hwP : dist w 0 ≤ r ∧ f w = y).2
        by_contra hwz
        exact (hεsub hw hwz) (sub_eq_zero.mpr hfwy)
      · intro hw
        rw [hw]
        exact ⟨Metric.mem_ball_self hε, hz⟩
  exact hcompact.finite hdiscrete

end Work.CriticalSet
