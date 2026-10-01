/-
# ZeroFreeTables — tf72Phi_upper

`tf72PhiUB x` is an upper bound for `tf72Phi (-x)` on `0 ≤ x ≤ 2`.

Both quantities are Laplace transforms of the polynomial body
`tf72Body s = (2-s)³(4+6s+s²)`:

  `tf72Phi (-x) = (1/30) ∫₀² e^{xs} tf72Body s ds`,
  `tf72PhiUB x  = (1/30) ∫₀² (Σ_{m<9} (xs)^m/m! + 2(xs)^9/9!) tf72Body s ds`

(the second identity is `tf72PhiUB_eq_integral`).  The integrand comparison is
pointwise on `[0,2]`: for `t = xs ∈ [0,4]`,

  `e^t ≤ Σ_{m<9} t^m/m! + 2 t^9/9!`   (`tf72_exp_taylor_upper`),

since the Taylor tail `Σ_{m≥10} t^m/m!` is at most `t^9/9!` for `t ≤ 4`.  As
`tf72Body ≥ 0` on `[0,2]`, multiplying by `tf72Body s` and integrating gives the
claim.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.tf72Phi_defs
import Submission.Work.ZeroFreeTables.tf72_exp_taylor_upper
import Submission.Work.ZeroFreeTables.tf72PhiUB_eq_integral

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.ZeroFreeTables

/-- `tf72Body` is non-negative on `[0,2]`. -/
private theorem tf72Body_nonneg_of_mem (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    0 ≤ tf72Body s := by
  rw [tf72Body]
  have h1 : 0 ≤ (2 - s) ^ 3 := by
    have : 0 ≤ 2 - s := by linarith
    positivity
  have h2 : 0 ≤ 4 + 6 * s + s ^ 2 := by nlinarith [sq_nonneg (s + 3)]
  positivity

theorem tf72Phi_upper (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    tf72Phi (-x) ≤ tf72PhiUB x := by
  have hcont_exp : Continuous (fun s : ℝ => Real.exp (x * s) * tf72Body s) := by
    unfold tf72Body
    fun_prop
  have hcont_poly : Continuous (fun s : ℝ =>
      ((∑ m ∈ Finset.range 9, (x * s) ^ m / (m.factorial : ℝ))
        + 2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s) := by
    unfold tf72Body
    fun_prop
  rw [tf72Phi, tf72PhiUB_eq_integral x]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/30)
  have hcongr : (∫ s in (0:ℝ)..2, Real.exp (-((-x) * s)) * tf72Body s)
      = ∫ s in (0:ℝ)..2, Real.exp (x * s) * tf72Body s := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show -((-x) * s) = x * s by ring]
  rw [hcongr]
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
  · exact hcont_exp.intervalIntegrable 0 2
  · exact hcont_poly.intervalIntegrable 0 2
  · intro s hs
    rw [Set.mem_Icc] at hs
    have ht0 : 0 ≤ x * s := mul_nonneg hx0 hs.1
    have ht4 : x * s ≤ 4 := by
      have h4 : x * s ≤ 2 * 2 := mul_le_mul hx2 hs.2 hs.1 (by norm_num)
      linarith
    exact mul_le_mul_of_nonneg_right (tf72_exp_taylor_upper (x * s) ht0 ht4)
      (tf72Body_nonneg_of_mem s hs.1 hs.2)

end Work.ZeroFreeTables
