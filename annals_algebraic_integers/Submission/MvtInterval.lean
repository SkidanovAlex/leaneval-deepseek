import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.DivLinear

/-!
# Mean-value / derivative Lipschitz bounds for real polynomials on an interval

For the separation arguments of the complementary polynomial (paper
`adjust.tex`, proof of `prop:early_ints_better`) we need the elementary fact
that a real polynomial `P` whose derivative is bounded by `M` on `[a,b]` is
`M`-Lipschitz there:

    |P.eval x - P.eval y| ≤ M · |x − y|   (x,y ∈ [a,b]).

Proof: `Convex.norm_image_sub_le_of_norm_deriv_le` applied to the restriction
of the polynomial (continuously differentiable on the interval).
-/

noncomputable section

open scoped Real BigOperators
open Submission.DivLinear
open Submission.SerreExample
open Polynomial

namespace Submission.MvtInterval

/-- A polynomial with derivative bounded by `M` on `[a,b]` is `M`-Lipschitz
there. -/
lemma abs_eval_sub_le_of_deriv_bound {P : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ x : ℝ, x ∈ Set.Icc a b → |P.derivative.eval x| ≤ M) :
    ∀ x : ℝ, x ∈ Set.Icc a b → ∀ y : ℝ, y ∈ Set.Icc a b →
      |P.eval x - P.eval y| ≤ M * |x - y| := by
  intro x hx y hy
  have _ := hab
  have _ := hM
  let f : ℝ → ℝ := fun z => P.eval z
  have hs : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hf : ∀ z : ℝ, z ∈ Set.Icc a b →
      HasDerivWithinAt f (P.derivative.eval z) (Set.Icc a b) z := by
    intro z hz
    simpa [f] using (P.hasDerivAt z).hasDerivWithinAt
  have hbound : ∀ z : ℝ, z ∈ Set.Icc a b → ‖P.derivative.eval z‖ ≤ M := by
    intro z hz
    simpa [Real.norm_eq_abs] using hderiv z hz
  have h : |P.eval y - P.eval x| ≤ M * |y - x| := by
    simpa [f] using (hs.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound hx hy)
  rwa [abs_sub_comm (P.eval y) (P.eval x), abs_sub_comm y x] at h

/-- Polynomial Lipschitz on the Serre interval with the sup-norm of the
derivative as the constant: `|P(x) − P(y)| ≤ supNorm P.derivative · |x − y|`. -/
lemma abs_eval_sub_le_supNorm_deriv (P : Polynomial ℝ) :
    ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → ∀ y : ℝ, y ∈ Set.Icc aSerre bSerre →
      |P.eval x - P.eval y| ≤ DivLinear.supNorm P.derivative * |x - y| := by
  intro x hx y hy
  exact abs_eval_sub_le_of_deriv_bound a_le_b (DivLinear.supNorm_nonneg P.derivative)
    (fun z hz => DivLinear.abs_eval_le_supNorm (P := P.derivative) z hz) x hx y hy

end Submission.MvtInterval
