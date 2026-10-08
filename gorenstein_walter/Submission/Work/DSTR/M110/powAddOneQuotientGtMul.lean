import Mathlib
import Submission.Work.DSTR.M110.powAddOneArithCore

namespace Work.DSTR.M110

/-- For odd `q`, `A + 1` divides `A ^ q + 1`. -/
private lemma dvd_pow_add_one_of_odd (A q : ℕ) (hq : Odd q) : (A + 1) ∣ A ^ q + 1 := by
  simpa using hq.nat_add_dvd_pow_add_pow A 1

/-- Gorenstein–Walter, the arithmetic estimate behind the cohomology computation: if `A` is odd,
`3 ≤ A`, `q` is an odd prime dividing `A + 1`, then `(A ^ q + 1) / (A + 1) > q * (A + 1)`.

Equivalently `(A + 1) * (q * (A + 1)) < A ^ q + 1`: the cofactor of `A + 1` in `A ^ q + 1` is
strictly larger than `q * (A + 1)`.  Here `q ∣ A + 1` forces `2 * q ≤ A + 1` (as `A + 1` is even
and `q` is odd), which pins down the worst case `q = 3`; the polynomial estimate
`q * (A + 1) ^ 2 < A ^ q + 1` (delegated as `powAddOneArithCore`) then gives the result. -/
theorem powAddOneQuotientGtMul (A q : ℕ) (hA : Odd A) (hA3 : 3 ≤ A) (hq : q.Prime) (hqo : Odd q) (hdvd : q ∣ A + 1) : (A ^ q + 1) / (A + 1) > q * (A + 1) := by
  -- `q ≥ 3` since `q` is an odd prime.
  have hq3 : 3 ≤ q := by
    obtain ⟨m, hm⟩ := hqo
    have := hq.two_le
    omega
  -- `A + 1` is even, and `q` is odd, so `2 * q ∣ A + 1`.
  have h2dvd : 2 ∣ A + 1 := by
    obtain ⟨k, hk⟩ := hA
    exact ⟨k + 1, by omega⟩
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hqo
  have h2qdvd : 2 * q ∣ A + 1 := hcop.mul_dvd_of_dvd_of_dvd h2dvd hdvd
  have hApos : 0 < A + 1 := by omega
  have h2q : 2 * q ≤ A + 1 := Nat.le_of_dvd hApos h2qdvd
  -- consequently `5 ≤ A`, in particular `5 ≤ A` and `3 ≤ q`.
  have hA5 : 5 ≤ A := by omega
  -- `A + 1 ∣ A ^ q + 1` because `q` is odd.
  have hdvd' : (A + 1) ∣ A ^ q + 1 := dvd_pow_add_one_of_odd A q hqo
  -- the polynomial estimate `q * (A + 1) ^ 2 < A ^ q + 1`.
  have hcore : q * (A + 1) ^ 2 < A ^ q + 1 := powAddOneArithCore A q hA5 hqo hq3 h2q
  -- division is exact, so it suffices to compare after multiplying by `A + 1`.
  have hQ : (A ^ q + 1) / (A + 1) * (A + 1) = A ^ q + 1 := Nat.div_mul_cancel hdvd'
  have hstep : (q * (A + 1)) * (A + 1) < (A ^ q + 1) / (A + 1) * (A + 1) := by
    rw [hQ]
    calc (q * (A + 1)) * (A + 1) = q * (A + 1) ^ 2 := by ring
      _ < A ^ q + 1 := hcore
  exact (Nat.mul_lt_mul_right hApos).mp hstep

end Work.DSTR.M110
