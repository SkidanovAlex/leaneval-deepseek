import Mathlib

namespace Work.EQ

/-- If a function `E : ℂ → ℂ` is analytic on the ball of radius `ε > 0` around `0`, and it
vanishes in a punctured neighborhood of every nonzero point of that ball, then it vanishes
in a whole neighborhood of `0`. This is the principle of isolated zeros (identity theorem):
the point `ε/2` is a zero of `E` with accumulation points arbitrarily close to it, so `E`
vanishes identically on the (preconnected) ball, hence eventually at `0`. -/
theorem eventually_zero_of_analyticOn_ball {E : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hE : AnalyticOnNhd ℂ E (Metric.ball 0 ε))
    (h0 : ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε →
      Filter.Eventually (fun z => E z = 0) (nhdsWithin x {x}ᶜ)) :
    Filter.Eventually (fun z => E z = 0) (nhds (0 : ℂ)) := by
  -- A convenient nonzero point of the ball.
  have hz₀ne : (((ε / 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  have hz₀lt : ‖(((ε / 2 : ℝ)) : ℂ)‖ < ε := by
    have h : ‖(((ε / 2 : ℝ)) : ℂ)‖ = |ε| / 2 := by simp
    rw [h, abs_of_pos hε]; linarith
  have hz₀mem : (((ε / 2 : ℝ)) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hz₀lt
  -- `E` vanishes frequently near this point (in fact eventually in a punctured neighborhood).
  have hfreq : ∃ᶠ z in nhdsWithin (((ε / 2 : ℝ)) : ℂ) {(((ε / 2 : ℝ)) : ℂ)}ᶜ, E z = 0 :=
    (h0 _ hz₀ne hz₀lt).frequently
  -- the identity theorem: `E` vanishes on the whole (preconnected) ball.
  have heq : Set.EqOn E 0 (Metric.ball (0 : ℂ) ε) :=
    hE.eqOn_zero_of_preconnected_of_frequently_eq_zero Metric.isPreconnected_ball hz₀mem hfreq
  -- the ball is a neighborhood of `0`, so `E` vanishes eventually at `0`.
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
  exact heq hz

end Work.EQ
