import Mathlib.RingTheory.Trace.Defs

namespace Commons.Algebra.MvPolynomial

/-- Expand the evaluation of the multinomial generating polynomial: the value of
`∑_f X_f · C(trace (∏_j x (f j)))` at `μ` is `∑_f (∏_j μ (f j)) · trace (∏_j x (f j))`,
which by symmetry equals the trace of the `k`-th power of `∑_i μ i • x i`. -/
theorem eval_sum_trace_pow {L : Type*} [Field L] [Algebra ℚ L]
    {ι : Type*} [Fintype ι] (x : ι → L) (k : ℕ) (μ : ι → ℚ) :
    MvPolynomial.eval μ (∑ f : Fin k → ι, (∏ j : Fin k, MvPolynomial.X (f j)) *
        MvPolynomial.C (Algebra.trace ℚ L (∏ j : Fin k, x (f j))))
      = Algebra.trace ℚ L ((∑ i, μ i • x i) ^ k) := by
  have hL : MvPolynomial.eval μ (∑ f : Fin k → ι, (∏ j : Fin k, MvPolynomial.X (f j)) *
        MvPolynomial.C (Algebra.trace ℚ L (∏ j : Fin k, x (f j))))
      = ∑ f : Fin k → ι, (∏ j : Fin k, μ (f j)) *
          (Algebra.trace ℚ L (∏ j : Fin k, x (f j))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_mul, map_prod]
    simp only [MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [hL]
  rw [Fintype.sum_pow (fun i => μ i • x i) k]
  rw [map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_smul, map_smul, smul_eq_mul]

end Commons.Algebra.MvPolynomial