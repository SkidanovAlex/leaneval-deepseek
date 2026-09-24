import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.support_lt

/-!
# The `λ⁺` remainder bound

`Work.ChenPlan.LinearSieve.Assembly.rem_bound_plus`:

`Σ_{d ∣ P} |λ⁺(d)| · |r_d| ≤ Σ_{d ∣ P, d < D} 3^{ω(d)} |r_d|`.

The Rosser–Iwaniec upper weight `λ⁺(d)` is supported on the *upper admissible* divisors of `P`,
and every upper admissible **squarefree** `d` satisfies `d < D` (`RI.rdPlus_lt`).  Divisors of `P`
are squarefree (`A.squarefree_of_mem_divisors_prodPrimes`), so the support of `λ⁺` lies below the
level `D`, exactly as in the `λ⁻` bound (`RI.lamMinus_error_le`).  On the support, `|λ⁺(d)| = |μ(d)| ≤ 1 ≤ 3^{ω(d)}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.Assembly

open Classical
open Work.ChenPlan.LinearSieve
open Work.ChenPlan.LinearSieve.RI

/-- The weight `|λ⁺(d)|` is dominated by `3^{ω(d)}`: on the upper-admissible divisors it equals
`|μ(d)| ≤ 1`, and it vanishes elsewhere. -/
lemma abs_lamPlus_le_card (P : ℕ) (D : ℝ) (d : ℕ) :
    |lamPlus P D d| ≤ (3 : ℝ) ^ d.primeFactors.card := by
  by_cases h : d ∣ P ∧ rdPlus D d
  · have hlm : lamPlus P D d = ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
      unfold lamPlus; rw [if_pos h]
    rw [hlm]
    have h1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
    linarith
  · have hlm : lamPlus P D d = 0 := by unfold lamPlus; rw [if_neg h]
    rw [hlm, abs_zero]
    positivity

/-- **The `λ⁺` remainder bound.**  The `3^{ω(d)}`-weighted remainder `remSum A D` dominates the
`λ⁺` error term for `D > 1`. -/
theorem rem_bound_plus (A : BoundingSieve) {D : ℝ} (hD : 1 < D) :
    ∑ d ∈ A.prodPrimes.divisors, |lamPlus A.prodPrimes D d| * |A.rem d|
      ≤ Submission.ChenPlan.remSum A D := by
  classical
  rw [Submission.ChenPlan.remSum, Finset.sum_filter]
  refine Finset.sum_le_sum fun d hd => ?_
  by_cases hlt : (d : ℝ) < D
  · rw [if_pos hlt]
    exact mul_le_mul_of_nonneg_right (abs_lamPlus_le_card _ _ _) (abs_nonneg _)
  · rw [if_neg hlt]
    have hlam : lamPlus A.prodPrimes D d = 0 := by
      unfold lamPlus
      by_cases hc : d ∣ A.prodPrimes ∧ rdPlus D d
      · exact absurd (RI.rdPlus_lt hD (A.squarefree_of_mem_divisors_prodPrimes hd) hc.2) hlt
      · rw [if_neg hc]
    rw [hlam]
    simp

end Work.ChenPlan.LinearSieve.Assembly
