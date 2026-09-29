import Mathlib

namespace Work.A14D

/-- **Identity theorem for a ball in `ℂ` fed by a real interval.**

If `f : ℂ → ℂ` is holomorphic on the ball `Metric.ball 1 δ` and vanishes on the
real interval `(1, 1 + ε)`, then `f` vanishes on the whole ball.  Indeed the
interval meets the ball in a set accumulating at the centre `1`, which lies in
the (preconnected) ball, so the principle of isolated zeros applies. -/
theorem eqOn_zero_of_ball_of_Ioo {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (1 : ℂ) δ))
    (h : ∀ t : ℝ, t ∈ Set.Ioo 1 (1 + ε) → f (t : ℂ) = 0) :
    ∀ z ∈ Metric.ball (1 : ℂ) δ, f z = 0 := by
  -- Differentiability on an open set upgrades to analyticity.
  have hf_an : AnalyticOnNhd ℂ f (Metric.ball (1 : ℂ) δ) :=
    (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 hf
  -- The ball is convex, hence preconnected.
  have hpre : IsPreconnected (Metric.ball (1 : ℂ) δ) := (convex_ball (1 : ℂ) δ).isPreconnected
  -- The centre belongs to the ball.
  have h1 : (1 : ℂ) ∈ Metric.ball (1 : ℂ) δ := by
    rw [Metric.mem_ball, dist_self]; exact hδ
  -- The zero set accumulates at the centre `1`.
  have hclos : (1 : ℂ) ∈ closure ({z | f z = 0} \ {1}) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    -- real point `1 + c` with `0 < c < min η ε`
    set c : ℝ := min η ε / 2 with hcd
    have hcpos : 0 < c := by rw [hcd]; exact div_pos (lt_min hη hε) (by norm_num)
    have hcη : c < η := by rw [hcd]; linarith [lt_min hη hε, min_le_left η ε]
    have hcε : c < ε := by rw [hcd]; linarith [lt_min hη hε, min_le_right η ε]
    refine ⟨((1 + c : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · -- it is a zero of `f`
      exact h (1 + c) ⟨by linarith, by linarith⟩
    · -- and it is not the centre
      intro hcontra
      have : (1 + c : ℝ) = 1 := by
        apply Complex.ofReal_inj.mp
        simpa using hcontra
      linarith
    · -- and it is within distance `η` of the centre
      have hdist : dist (1 : ℂ) ((1 + c : ℝ) : ℂ) = c := by
        rw [dist_eq_norm]
        have hsub : (1 : ℂ) - ((1 + c : ℝ) : ℂ) = (((1 - (1 + c) : ℝ)) : ℂ) := by
          push_cast; ring
        rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
      rw [hdist]; exact hcη
  intro z hz
  exact hf_an.eqOn_zero_of_preconnected_of_mem_closure hpre h1 hclos hz

end Work.A14D
