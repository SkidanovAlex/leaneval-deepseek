import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.FTS.StrongEps.LocUnif.tendsto_backward_diffQuot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- `ENNReal.ofReal` of the square of the derivative is dominated by the
`liminf` of `ENNReal.ofReal` of the squares of the backward difference quotients
with step `1/(j+1)`.

When `f` is differentiable at `x` the backward difference quotients converge to
`deriv f x`, hence so do their (squares and) `ofReal`s, and the `liminf` of a
convergent sequence is its limit.  When `f` is not differentiable at `x`,
`deriv f x = 0` by definition, so the left-hand side is `0` and the claim is
trivial. -/
theorem ofReal_deriv_sq_le_liminf_backwardDiffQuot (f : ℝ → ℝ) (x ρ : ℝ) :
    ENNReal.ofReal ((deriv f x * ρ) ^ 2)
      ≤ Filter.liminf (fun j : ℕ => ENNReal.ofReal
          (((f x - f (x - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1) * ρ) ^ 2)) Filter.atTop := by
  by_cases hx : DifferentiableAt ℝ f x
  · -- Differentiable case: the backward difference quotients converge to `deriv f x`.
    have hs : Filter.Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hspos : ∀ j : ℕ, 0 < (1 : ℝ) / ((j : ℝ) + 1) := fun j => by positivity
    have hT : Filter.Tendsto
        (fun j : ℕ => (f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1)))
        Filter.atTop (nhds (deriv f x)) :=
      tendsto_backward_diffQuot hx hs hspos
    have hw : Filter.Tendsto
        (fun j : ℕ => ((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1))) * ρ)
        Filter.atTop (nhds (deriv f x * ρ)) :=
      hT.mul tendsto_const_nhds
    have h2 : Filter.Tendsto
        (fun j : ℕ => (((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1))) * ρ) ^ 2)
        Filter.atTop (nhds ((deriv f x * ρ) ^ 2)) :=
      hw.pow 2
    have h3 : Filter.Tendsto
        (fun j : ℕ => ENNReal.ofReal
          ((((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1))) * ρ) ^ 2))
        Filter.atTop (nhds (ENNReal.ofReal ((deriv f x * ρ) ^ 2))) :=
      ENNReal.tendsto_ofReal h2
    -- `(j+1) = 1/(1/(j+1))`, so the two sequences agree.
    have heq : (fun j : ℕ => ENNReal.ofReal
          ((((f x - f (x - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1) * ρ) ^ 2)))
        = fun j : ℕ => ENNReal.ofReal
          ((((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1))) * ρ) ^ 2) := by
      funext j
      congr 1
      have h : ((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1)))
          = ((f x - f (x - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)) := by
        field_simp
      rw [h]
    rw [heq, Filter.Tendsto.liminf_eq h3]
  · -- Non-differentiable case: `deriv f x = 0`, so the left-hand side vanishes.
    have hd : deriv f x = 0 := deriv_zero_of_not_differentiableAt hx
    simp [hd]

end Work.FTS.StrongEps.LocUnif
