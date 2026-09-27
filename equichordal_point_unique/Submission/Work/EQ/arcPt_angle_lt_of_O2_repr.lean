import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.arc_iterate_aux

namespace Work.EQ

open Complex

/-- Strict increase of the angle: if the arc point at `O₁`-angle `θ ∈ (0,π)` also has the
`O₂`-representation `polarPt (a/2) (ρ₂ ψ) ψ` with `ψ ∈ (0,π)` and `ρ₂ ψ > 0`, then `ψ > θ`.
Subtracting the centres gives `ρ₁ θ * sin θ = ρ₂ ψ * sin ψ` and
`ρ₁ θ * cos θ - ρ₂ ψ * cos ψ = a` (via `arcPt_re`, `arcPt_im`, `polarPt_re`, `polarPt_im_eq` of
`arc_iterate_aux`), whence `ρ₂ ψ * Real.sin (ψ - θ) = a * sin θ > 0` using `Real.sin_sub`.
As `-π < ψ - θ < π`, `Real.sin_nonpos_of_nonpos_of_neg_pi_le` gives `ψ - θ > 0`. -/
theorem arcPt_angle_lt_of_O2_repr {a : ℝ} (ha0 : 0 < a) {ρ₁ ρ₂ : ℝ → ℝ} {θ ψ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hψ0 : 0 < ψ) (hψπ : ψ < Real.pi) (hρ₂ : 0 < ρ₂ ψ)
    (h : arcPt a ρ₁ θ = polarPt (a / 2) (ρ₂ ψ) ψ) : θ < ψ := by
  -- Imaginary parts of the equality of points: `ρ₁ θ * sin θ = ρ₂ ψ * sin ψ`.
  have him : ρ₁ θ * Real.sin θ = ρ₂ ψ * Real.sin ψ := by
    have hc := congrArg Complex.im h
    rw [arcPt_im, polarPt_im_eq] at hc
    linarith
  -- Real parts: `ρ₁ θ * cos θ - ρ₂ ψ * cos ψ = a`.
  have hre : ρ₁ θ * Real.cos θ - ρ₂ ψ * Real.cos ψ = a := by
    have hc := congrArg Complex.re h
    rw [arcPt_re, polarPt_re] at hc
    linarith
  -- The combination `cos θ * him - sin θ * hre` is `ρ₂ ψ * sin (ψ - θ) = a * sin θ`.
  have key : ρ₂ ψ * Real.sin (ψ - θ) = a * Real.sin θ := by
    rw [Real.sin_sub]
    linear_combination -Real.cos θ * him + Real.sin θ * hre
  -- Since `ρ₂ ψ > 0` and `a > 0`, `sin θ > 0`, this makes `sin (ψ - θ) > 0`.
  have hsin : 0 < Real.sin (ψ - θ) := by
    have hpos : 0 < ρ₂ ψ * Real.sin (ψ - θ) := by
      rw [key]
      exact mul_pos ha0 (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
    exact pos_of_mul_pos_right hpos hρ₂.le
  -- As `-π < ψ - θ < π`, `sin (ψ - θ) > 0` forces `ψ - θ > 0`.
  by_contra hle
  have hle' : ψ - θ ≤ 0 := by linarith [not_lt.mp hle]
  exact absurd hsin (not_lt.mpr (Real.sin_nonpos_of_nonpos_of_neg_pi_le hle' (by linarith)))

end Work.EQ
