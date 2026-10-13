import Mathlib

namespace Work.WilE3.Frame

/-- **The identity principle along real lines.**  Let `G` be complex-analytic on the ball
`B (u₀, ρ)` of the Banach space `ι → ℂ` (`ι` a finite type), and suppose that for every *real*
direction `w : ι → ℝ` the one-variable function `t ↦ G (u₀ + t • w_ℂ)` vanishes in a whole
neighbourhood of `t = 0` (here `w_ℂ = fun i => (w i : ℂ)`).  If in addition `G u₀ = 0`, then
`G (u₀ + w_ℂ) = 0` for **every** real direction `w` with `‖w_ℂ‖ < ρ`.

This is the one-variable identity-principle step of `Work.WilE3.Frame.vanish_of_real_points`: the
disc `{t : ‖t‖ < ρ / ‖w_ℂ‖}` is preconnected, the function `t ↦ G (u₀ + t • w_ℂ)` is analytic on
it (it is the composition of the affine line with `G`, whose image stays in `B (u₀, ρ)`), and it
vanishes identically there because it vanishes near `0`; evaluating at `t = 1` (which lies in the
disc since `‖w_ℂ‖ < ρ`) gives the claim.  The degenerate case `w_ℂ = 0` is exactly `G u₀ = 0`.

A very close template (for *complex* directions, and concluding an eventual statement) is the
already proved `Work.WilE3.Frame.eq_zero_of_all_lines` in
`Submission/Work/WilE3/Frame/eq_zero_of_all_lines.lean`; its norm bookkeeping can be reused
verbatim with `S := fun t => G (u₀ + t • w)` and `r := ρ / ‖w_ℂ‖`. -/
lemma eq_zero_of_eventually_zero_on_real_directions {ι : Type*} [Fintype ι]
    (G : (ι → ℂ) → ℂ) (u₀ : ι → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hG : AnalyticOnNhd ℂ G (Metric.ball u₀ ρ)) (hG₀ : G u₀ = 0)
    (hdir : ∀ w : ι → ℝ, ∀ᶠ t in nhds (0 : ℂ),
      G (u₀ + t • (fun i => (w i : ℂ))) = 0)
    (w : ι → ℝ) (hw : ‖(fun i => (w i : ℂ))‖ < ρ) :
    G (u₀ + (fun i => (w i : ℂ))) = 0 := by
  -- We prove the statement for an arbitrary *complex* direction `W`; the real direction of the
  -- claim is then `W = fun i => (w i : ℂ)`.
  have key : ∀ W : ι → ℂ, ‖W‖ < ρ → (∀ᶠ t in nhds (0 : ℂ), G (u₀ + t • W) = 0) →
      G (u₀ + W) = 0 := by
    intro W hW hv
    rcases eq_or_ne W 0 with hW0 | hWne
    · -- degenerate case: the direction is zero and the claim is the hypothesis `G u₀ = 0`
      rw [hW0, add_zero]
      exact hG₀
    · have hWpos : 0 < ‖W‖ := norm_pos_iff.mpr hWne
      have hRpos : 0 < ρ / ‖W‖ := div_pos hρ hWpos
      -- `0` and `1` both lie in the disc of radius `ρ / ‖W‖`
      have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (ρ / ‖W‖) := by
        rw [Metric.mem_ball, dist_self]
        exact hRpos
      have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (ρ / ‖W‖) := by
        rw [Metric.mem_ball, dist_zero_right, norm_one, lt_div_iff₀ hWpos]
        simpa using hW
      -- the parametrized line is analytic and maps the disc into the ball of analyticity of `G`
      have hφ : AnalyticOnNhd ℂ (fun t : ℂ => u₀ + t • W) (Metric.ball (0 : ℂ) (ρ / ‖W‖)) :=
        fun t _ => (analyticAt_const (v := u₀)).add
          ((ContinuousLinearMap.toSpanSingleton ℂ W).analyticAt t)
      have hmaps : Set.MapsTo (fun t : ℂ => u₀ + t • W) (Metric.ball (0 : ℂ) (ρ / ‖W‖))
          (Metric.ball u₀ ρ) := by
        intro t ht
        rw [Metric.mem_ball, dist_eq_norm] at ht ⊢
        rw [sub_zero, lt_div_iff₀ hWpos] at ht
        simpa only [add_sub_cancel_left, norm_smul] using ht
      have hcomp : AnalyticOnNhd ℂ (fun t : ℂ => G (u₀ + t • W))
          (Metric.ball (0 : ℂ) (ρ / ‖W‖)) :=
        AnalyticOnNhd.comp hG hφ hmaps
      -- the restriction vanishes near `t = 0`, so by the identity principle it is zero on the disc
      have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hcomp
        Metric.isPreconnected_ball h0mem hv
      have h1e : G (u₀ + (1 : ℂ) • W) = 0 := hzero h1mem
      simpa only [one_smul] using h1e
  exact key (fun i => (w i : ℂ)) hw (hdir w)

end Work.WilE3.Frame
