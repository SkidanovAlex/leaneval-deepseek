import Mathlib
import Submission.Work.A3.Circle

/-!
# Splitting the polynomial exponential sum `expSum` at a rational shift

`Work.A3.expSum Q N θ = ∑_{n=1}^{N} e(-2πi θ Q(n))` is summed over the integer interval
`Finset.Icc 1 N`; this module rewrites it as the sum over `Finset.range N` of the shifted index
`n + 1` and, for `θ = a/q + β`, splits each exponential into its rational (`a/q`) and archimedean
(`β`) factors:

`expSum Q N (a/q + β) = ∑_{n<N} e(-2πi a Q(n+1)/q) · e(-2πi β Q(n+1))`.

The first factor `e(-2πi a Q(n+1)/q)` is the `q`-periodic (complete-sum) part and the second
`e(-2πi β Q(n+1))` the archimedean (singular-integral) part, so this identity is the first step
of the major-arc decomposition of Area A3.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

/-- **Reindexing**: the sum over the interval `Icc 1 N` is the sum over `Finset.range N` of the
shift `n ↦ n + 1`. -/
lemma sum_Icc_one_eq_sum_range_nat (N : ℕ) (g : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 N, g m) = ∑ n ∈ Finset.range N, g (n + 1) := by
  refine (Finset.sum_bij (fun (n : ℕ) (_ : n ∈ Finset.range N) => n + 1) ?_ ?_ ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc]
    omega
  · intro n₁ _ n₂ _ heq
    omega
  · intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
    exact ⟨b - 1, by rw [Finset.mem_range]; omega, by omega⟩
  · intro n _
    rfl

/-- **Splitting the exponential** of a sum `a/q + β` of a rational and an archimedean part:
`e(-2πi X (a/q + β)) = e(-2πi a X / q) · e(-2πi β X)` for real `X`, `a`, `q`, `β`. -/
lemma exp_neg_mul_add_split (X a q β : ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (X * (a / q + β)))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (a * X / q))) *
        Complex.exp (-(2 * Real.pi * Complex.I * (β * X))) := by
  rw [← Complex.exp_add]
  congr 1
  ring

theorem expSum_range_split (Q : Polynomial ℤ) (N : ℕ) (a q : ℤ) (β : ℝ) :
    Work.A3.expSum Q N ((a : ℝ) / (q : ℝ) + β) =
      ∑ n ∈ Finset.range N,
        (Complex.exp (-(2 * Real.pi * Complex.I * ((a : ℝ) * (((Q.eval ((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ) / (q : ℝ))))
        * Complex.exp (-(2 * Real.pi * Complex.I * (β * (((Q.eval ((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ))))) := by
  rw [expSum, sum_Icc_one_eq_sum_range_nat]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end

end Work.A3
