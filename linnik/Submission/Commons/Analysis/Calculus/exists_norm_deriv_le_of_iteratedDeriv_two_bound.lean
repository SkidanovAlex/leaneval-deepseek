import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

namespace Commons.Analysis.Calculus

/-- If `f : ℝ → ℂ` is `C²` on the open interval `(0, x₀)` and its second derivative
is bounded there by `B`, then its first derivative is bounded there as well.

This is because the mean value theorem applied to `deriv f` on the (convex) interval
`(0, x₀)` shows that `deriv f` is Lipschitz with constant `B`, and the interval has
finite length `x₀`. -/
theorem exists_norm_deriv_le_of_iteratedDeriv_two_bound {f : ℝ → ℂ} {x₀ B : ℝ} (hx₀ : 0 < x₀)
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hbound : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∃ M : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖deriv f t‖ ≤ M := by
  -- midpoint of the interval
  have hx₁ : (x₀ / 2) ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
  -- `B` is nonnegative
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hbound (x₀ / 2) hx₁)
  -- second derivative expressed as the derivative of `deriv f`
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- `deriv f` is differentiable on the interval
  have hdiff : ∀ x ∈ Set.Ioo (0:ℝ) x₀, DifferentiableAt ℝ (deriv f) x := by
    intro x hx
    have hcx : ContDiffAt ℝ 2 f x := hf2.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hcx1 : ContDiffAt ℝ 1 (deriv f) x := hcx.derivWithin (by norm_num)
    exact hcx1.differentiableAt_one
  refine ⟨B * x₀ + ‖deriv f (x₀ / 2)‖, fun t ht => ?_⟩
  -- mean value inequality for `deriv f`
  have hmvt : ‖deriv f t - deriv f (x₀ / 2)‖ ≤ B * ‖t - x₀ / 2‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (C := B) hdiff
      (fun x hx => by rw [← h2]; exact hbound x hx) (convex_Ioo 0 x₀) hx₁ ht
  have hdist : ‖t - x₀ / 2‖ ≤ x₀ := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2, hx₁.1, hx₁.2]
  calc ‖deriv f t‖
      ≤ ‖deriv f t - deriv f (x₀ / 2)‖ + ‖deriv f (x₀ / 2)‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (deriv f t - deriv f (x₀ / 2)) (deriv f (x₀ / 2))
    _ ≤ B * ‖t - x₀ / 2‖ + ‖deriv f (x₀ / 2)‖ := by linarith
    _ ≤ B * x₀ + ‖deriv f (x₀ / 2)‖ := by
        have := mul_le_mul_of_nonneg_left hdist hB
        linarith

end Commons.Analysis.Calculus