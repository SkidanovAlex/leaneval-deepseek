import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Algebra.Polynomial.le_rootMultiplicity_derivative

namespace Commons.Algebra.Polynomial

/-- **Coprimality with the derivative implies squarefreeness.**  If `p` is coprime to its derivative `p'`, then every root of `p` is simple: `rootMultiplicity β p ≤ 1`.  Indeed a double root `β` would give `(X − C β) ∣ p` and `(X − C β) ∣ p'` (since `p = (X−Cβ)²q` implies `p' = 2(X−Cβ)q + (X−Cβ)²q'`), contradicting `IsCoprime p p'`.

This is the standard certificate for the *squarefreeness* hypothesis of the divisor bounds of arXiv:2408.15403 (the paper's Lemma `(res)`: "`R₄(y)` is irreducible", hence squarefree): an explicit Bézout identity `A·p + B·p' = C c` with `c ≠ 0` (coefficients in the base field) exhibits `IsCoprime p p'` and hence `rootMultiplicity β p ≤ 1`. -/
theorem rootMultiplicity_le_one_of_isCoprime_derivative {K : Type*} [Field K]
    {p : Polynomial K} (h : IsCoprime p p.derivative) (β : K) :
    Polynomial.rootMultiplicity β p ≤ 1 := by
  -- Suppose `β` is a multiple root, i.e. `(X - C β) ^ 2 ∣ p`.
  by_contra hle
  rw [not_le] at hle
  have h2 : 2 ≤ p.rootMultiplicity β := by omega
  have hsq : (Polynomial.X - Polynomial.C β) ^ 2 ∣ p :=
    (pow_dvd_pow _ h2).trans (Polynomial.pow_rootMultiplicity_dvd p β)
  -- Then `(X - C β) ∣ p`, and — differentiating `(X - C β) ^ 2 * q` — also `(X - C β) ∣ p'`.
  have hlin : (Polynomial.X - Polynomial.C β) ∣ p :=
    dvd_trans ⟨Polynomial.X - Polynomial.C β, by ring⟩ hsq
  have hder : (Polynomial.X - Polynomial.C β) ∣ p.derivative := by
    simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hsq
  -- A common divisor of `p` and `p'` must be a unit, but `X - C β` is prime, hence not a unit.
  exact (Polynomial.prime_X_sub_C β).not_isUnit (h.isUnit_of_dvd' hlin hder)

end Commons.Algebra.Polynomial