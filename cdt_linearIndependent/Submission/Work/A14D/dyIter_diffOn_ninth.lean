import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.chainZDefs

namespace Work.A14D

open Complex Metric
open scoped Topology

/-- The factor `(z-1)²/(z²-2z)` of `Dy` is holomorphic on `Metric.ball ninth δ` for `δ ≤ 1/20`:
the denominator `z² - 2z = z(z-2)` does not vanish there. -/
lemma dy_factor_diffOn_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) :
    DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ 2 / (z ^ 2 - 2 * z)) (Metric.ball ninth δ) := by
  refine DifferentiableOn.div ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    ((differentiableOn_id.pow 2).sub ((differentiableOn_const 2).mul differentiableOn_id))
    ?_
  intro z hz
  rw [show z ^ 2 - 2 * z = z * (z - 2) by ring]
  exact mul_ne_zero (ne_zero_of_mem_ball_ninth hδ hz)
    (sub_ne_zero.mpr (ne_two_of_mem_ball_ninth hδ hz))

/-- `DyIter (k+1) f = Dy (DyIter k f)`. -/
lemma DyIter_succ' (k : ℕ) (f : ℂ → ℂ) :
    DyIter (k + 1) f = Dy (DyIter k f) := by
  have := Function.iterate_succ_apply' Dy k f
  simp only [DyIter] at this ⊢
  exact this

/-- `Dy` preserves holomorphy on `Metric.ball ninth δ` for `δ ≤ 1/20`. -/
lemma dy_diffOn_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) {A : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (Metric.ball ninth δ)) :
    ∀ k : ℕ, DifferentiableOn ℂ (DyIter k A) (Metric.ball ninth δ) := by
  intro k
  induction k with
  | zero =>
      rw [DyIter, Function.iterate_zero]
      simpa using hA
  | succ k ih =>
      rw [DyIter_succ']
      have hfun : Dy (DyIter k A)
          = fun z : ℂ => deriv (DyIter k A) z * ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) := by
        funext z
        simp only [Dy]
        rw [mul_div_assoc]
      rw [hfun]
      exact (ih.deriv Metric.isOpen_ball).mul (dy_factor_diffOn_ninth hδ)

/-- `∂_y`-iterates of a function holomorphic on the disc `Metric.ball ninth δ` (`ninth = 1/9`) are
holomorphic on that disc, for `δ ≤ 1/20`.

`Dy f z = deriv f z * (z-1)^2/(z^2-2z)`: the factor `(z-1)^2/(z^2-2z)` is holomorphic on the disc
because `0, 2 ∉ Metric.ball ninth δ` when `δ ≤ 1/20` (indeed `‖z - 1/9‖ < 1/20` forces
`z ≠ 0` and `z ≠ 2`), and the derivative of a function holomorphic on the open disc is holomorphic
there (`DifferentiableOn.deriv`).  Induction on `k`, using

`DyIter (k+1) f = fun z => deriv (DyIter k f) z * (z - 1)^2 / (z^2 - 2*z)`
(`Function.iterate_succ_apply'` and `DyIter = (Dy)^[k]`). -/
theorem dyIter_diffOn_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) {A : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (Metric.ball ninth δ)) :
    ∀ k : ℕ, DifferentiableOn ℂ (DyIter k A) (Metric.ball ninth δ) :=
  dy_diffOn_ninth hδ hA

end Work.A14D
