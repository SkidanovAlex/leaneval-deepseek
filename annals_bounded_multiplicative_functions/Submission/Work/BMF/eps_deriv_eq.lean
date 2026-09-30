import Mathlib
import Submission.Work.BMF.adi_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- The derivative of the "error" polynomial-minus-log-minus-lattice function, rewritten as the
sum of the Taylor-derivative corrections. -/
theorem eps_deriv_eq (k : ℕ) {x c0 : ℝ} {T mu : ℕ → ℝ} {P G : ℝ[X]}
    (hP : P = C c0 + ∑ m ∈ Finset.Icc 1 k,
      (C (T m / (2 * Real.pi)) * Tay m x + C (mu m) * X ^ m))
    (hG : G = ∑ m ∈ Finset.Icc 1 k, C (mu m) * X ^ m) :
    ∀ t : ℝ, t ≠ 0 → deriv (fun s => P.eval s - ((∑ m ∈ Finset.Icc 1 k, T m) / (2 * Real.pi)) *
      Real.log s - G.eval s) t =
      ∑ m ∈ Finset.Icc 1 k, T m / (2 * Real.pi) * ((Tay m x).derivative.eval t - 1 / t) := by
  intro t ht
  -- First compute the derivative via `HasDerivAt`: polynomial parts plus `A · log`.
  have hF : HasDerivAt (fun s => P.eval s - ((∑ m ∈ Finset.Icc 1 k, T m) / (2 * Real.pi)) *
      Real.log s - G.eval s)
      (P.derivative.eval t - ((∑ m ∈ Finset.Icc 1 k, T m) / (2 * Real.pi)) * t⁻¹ -
        G.derivative.eval t) t := by
    refine ((P.hasDerivAt t).sub ?_).sub (G.hasDerivAt t)
    exact (Real.hasDerivAt_log ht).const_mul _
  -- Differentiate `P`, whose `μ`-part will cancel against `G`.
  have hPd : derivative P = ∑ m ∈ Icc 1 k,
      (C (T m / (2 * Real.pi)) * derivative (Tay m x) + C (mu m) * derivative (X ^ m)) := by
    rw [hP, derivative_add, derivative_C, zero_add, derivative_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [derivative_add, derivative_C_mul, derivative_C_mul]
  have hPde : eval t (derivative P) = ∑ m ∈ Icc 1 k,
      ((T m / (2 * Real.pi)) * eval t (derivative (Tay m x)) +
        mu m * eval t (derivative (X ^ m))) := by
    rw [hPd, eval_finsetSum]
    exact Finset.sum_congr rfl fun m _ => by rw [eval_add, eval_mul, eval_C, eval_mul, eval_C]
  have hGd : derivative G = ∑ m ∈ Icc 1 k, (C (mu m) * derivative (X ^ m)) := by
    rw [hG, derivative_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [derivative_C_mul]
  have hGde : eval t (derivative G) = ∑ m ∈ Icc 1 k, mu m * eval t (derivative (X ^ m)) := by
    rw [hGd, eval_finsetSum]
    exact Finset.sum_congr rfl fun m _ => by rw [eval_mul, eval_C]
  -- Distribute the constant `A` over the sum.
  have hA : (∑ m ∈ Icc 1 k, T m) / (2 * Real.pi) * t⁻¹ =
      ∑ m ∈ Icc 1 k, T m / (2 * Real.pi) * t⁻¹ := by
    rw [Finset.sum_div, Finset.sum_mul]
  rw [hF.deriv, hPde, hGde, hA]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

end Work.BMF
