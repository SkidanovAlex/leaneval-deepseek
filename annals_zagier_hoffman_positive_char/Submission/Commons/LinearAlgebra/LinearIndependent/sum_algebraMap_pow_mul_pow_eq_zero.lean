import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.LinearIndependent

/-- **Frobenius ("freshman's dream") rigidity of a linear relation.**  Let `L` be a field of
characteristic `p` and `K` a subfield.  If `v : ι → L` is `K`-linearly independent and a
`K`-linear combination of the `p^j`-th powers `(v i)^(p^j)` with coefficients that are themselves
`p^j`-th powers of elements of `K` vanishes, then all the coefficients vanish.  (The point is that
`∑ i, d i^(p^j)·v i^(p^j) = (∑ i, d i • v i)^(p^j)` in characteristic `p`.) -/
theorem sum_algebraMap_pow_mul_pow_eq_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [ExpChar L p] {ι : Type*} [Fintype ι] {v : ι → L}
    (hv : LinearIndependent K v) (j : ℕ) (d : ι → K)
    (h : ∑ i, algebraMap K L (d i) ^ (p ^ j) * v i ^ (p ^ j) = 0) : ∀ i, d i = 0 := by
  have hpj : p ^ j ≠ 0 := pow_ne_zero j (Fact.out : p.Prime).ne_zero
  have key : (∑ i, algebraMap K L (d i) * v i) ^ p ^ j = 0 := by
    rw [show (∑ i, algebraMap K L (d i) * v i) ^ p ^ j
        = ∑ i, (algebraMap K L (d i) * v i) ^ p ^ j from
      sum_pow_char_pow p j Finset.univ (fun i => algebraMap K L (d i) * v i)]
    simpa [mul_pow] using h
  have hsum : ∑ i, algebraMap K L (d i) * v i = 0 := (pow_eq_zero_iff hpj).mp key
  refine (Fintype.linearIndependent_iff.mp hv) (fun i => d i) ?_
  simpa [Algebra.smul_def] using hsum

end Commons.LinearAlgebra.LinearIndependent