import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAtT_mul
import Submission.Commons.FieldTheory.RatFunc.ordAtT_algebraMap
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_ge
import Submission.Commons.FieldTheory.RatFunc.ordAt_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_algebraMap
import Submission.Commons.Algebra.Polynomial.dnum_def

set_option linter.unusedVariables false

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.Algebra.Polynomial
open Commons.FieldTheory.RatFunc

/-- `ordAtT` of the `n`-th power of the linear factor `X − C α` equals `n`: the factor
`X − C α` is a simple root of itself, so the only contribution to the order comes from the
exponent `n`. -/
theorem ordAtT_X_sub_C_pow {K : Type*} [Field K] (α : K) (n : ℕ) :
    ordAtT α (algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ n))
      = ((n : ℤ) : WithTop ℤ) := by
  have hz : (((Polynomial.X - Polynomial.C α) ^ n) : Polynomial K) ≠ 0 :=
    pow_ne_zero n (Polynomial.X_sub_C_ne_zero α)
  rw [ordAtT_algebraMap hz, Polynomial.rootMultiplicity_X_sub_C_pow]

/-- **The derivative lowers the order by at most `j`**: if `f ∈ K(X)` is nonzero of order `N` at
`α` and the Frobenius residue `z^j f^{(j)} − (N)_j f` has order at least `N + 1`, then the `j`-th
derivative of `f` has order at least `N − j`. -/
theorem ordAtT_iterate_deriv_ge {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {α : K} {f : RatFunc K} (hf : f ≠ 0) {N : ℤ} (hN : ordAt α f = N) {j : ℕ}
    (hres : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j)
          * ((D : RatFunc K → RatFunc K)^[j] f)
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((fallFact N j : ℤ) : K)) * f)) :
    ((N - j : ℤ) : WithTop ℤ) ≤ ordAtT α (((D : RatFunc K → RatFunc K)^[j] f)) := by
  -- Split off the case where the iterated derivative vanishes identically.
  rcases eq_or_ne ((D : RatFunc K → RatFunc K)^[j] f) 0 with h0 | h0
  · rw [h0]; simp [ordAtT]
  -- The linear factor `z = X − C α`, raised to the `j`-th power, is nonzero in `K(X)`.
  have hz : algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero j (Polynomial.X_sub_C_ne_zero α))
  -- Rewrite `z^j f^{(j)}` as the Frobenius residue plus `(N)_j f`.
  have hsplit : algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j)
        * ((D : RatFunc K → RatFunc K)^[j] f)
      = (algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j)
            * ((D : RatFunc K → RatFunc K)^[j] f)
          - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((fallFact N j : ℤ) : K)) * f)
        + algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((fallFact N j : ℤ) : K)) * f := by
    ring
  -- The second summand has order exactly `N` (or vanishes).
  have hCf : (N : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((fallFact N j : ℤ) : K)) * f) := by
    rcases eq_or_ne ((fallFact N j : ℤ) : K) 0 with h0' | h0'
    · rw [h0', Polynomial.C_0, map_zero, zero_mul]; simp [ordAtT]
    · have hC0 : (Polynomial.C ((fallFact N j : ℤ) : K) : Polynomial K) ≠ 0 := by
        rwa [Polynomial.C_ne_zero]
      have hC0' : algebraMap (Polynomial K) (RatFunc K)
          (Polynomial.C ((fallFact N j : ℤ) : K)) ≠ 0 := RatFunc.algebraMap_ne_zero hC0
      rw [ordAtT_mul α hC0' hf, ordAtT_algebraMap hC0, Polynomial.rootMultiplicity_C]
      simp [ordAtT_def α hf, hN]
  -- Hence `z^j f^{(j)}` itself has order at least `N`.
  have hNle : (N : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K)
      ((Polynomial.X - Polynomial.C α) ^ j) * ((D : RatFunc K → RatFunc K)^[j] f)) := by
    rw [hsplit]
    refine le_trans (le_min ?_ hCf) (ordAtT_add_ge α _ _)
    exact le_trans (by rw [WithTop.coe_le_coe]; omega) hres
  -- Cancel the order `j` of the factor `z^j`.
  rw [ordAtT_mul α hz h0, ordAtT_X_sub_C_pow, ordAtT_def α h0, ← WithTop.coe_add,
    WithTop.coe_le_coe] at hNle
  rw [ordAtT_def α h0, WithTop.coe_le_coe]
  omega

end Commons.FieldTheory.RatFunc
