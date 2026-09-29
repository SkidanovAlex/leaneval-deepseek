import Mathlib
import Submission.Work.A14.defs

namespace Work.A14D

/-- **Identity theorem for a ball in `ℂ` fed by a real interval (centre `ninth`).**

If `X : ℂ → ℂ` is holomorphic on the ball `Metric.ball ninth δ` and vanishes on the
real interval `(x₀ - η, x₀ + η)` with `x₀` inside the ball, then `X` vanishes on the
whole ball: the real interval accumulates at `x₀`, which lies in the (preconnected)
ball, so the principle of isolated zeros applies. -/
theorem eqOn_zero_of_ball_ninth_of_realInterval {δ : ℝ} (hδ : 0 < δ) {X : ℂ → ℂ}
    (hX : DifferentiableOn ℂ X (Metric.ball ninth δ)) {x₀ η : ℝ} (hη : 0 < η)
    (hx₀ : (x₀ : ℂ) ∈ Metric.ball ninth δ)
    (h : ∀ y : ℝ, |y - x₀| < η → X (y : ℂ) = 0) :
    ∀ z ∈ Metric.ball ninth δ, X z = 0 := by
  -- Differentiability on the open ball upgrades to analyticity.
  have hX_an : AnalyticOnNhd ℂ X (Metric.ball ninth δ) :=
    (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 hX
  -- The ball is convex, hence preconnected.
  have hpre : IsPreconnected (Metric.ball ninth δ) := (convex_ball ninth δ).isPreconnected
  -- The zero set of `X` accumulates at `x₀`.
  have hclos : (x₀ : ℂ) ∈ closure ({z | X z = 0} \ {(x₀ : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set c : ℝ := min ε η / 2 with hcd
    have hcpos : 0 < c := by rw [hcd]; exact div_pos (lt_min hε hη) (by norm_num)
    have hcε : c < ε := by
      rw [hcd]; linarith [lt_min hε hη, min_le_left ε η]
    have hcη : c < η := by
      rw [hcd]; linarith [lt_min hε hη, min_le_right ε η]
    refine ⟨((x₀ + c : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · -- it is a zero of `X`
      exact h (x₀ + c) (by rw [show x₀ + c - x₀ = c by ring, abs_of_pos hcpos]; exact hcη)
    · -- and it is not the centre `x₀`
      intro hcontra
      have : x₀ + c = x₀ := Complex.ofReal_inj.mp hcontra
      linarith
    · -- and it is within distance `ε` of the centre `x₀`
      have hdist : dist (x₀ : ℂ) (((x₀ + c : ℝ)) : ℂ) = c := by
        rw [dist_eq_norm]
        have hsub : (x₀ : ℂ) - (((x₀ + c : ℝ)) : ℂ)
            = (((x₀ - (x₀ + c) : ℝ)) : ℂ) := by push_cast; ring
        rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
      rw [hdist]; exact hcε
  intro z hz
  exact hX_an.eqOn_zero_of_preconnected_of_mem_closure hpre hx₀ hclos hz

end Work.A14D
