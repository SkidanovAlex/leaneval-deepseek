import Mathlib
import Submission.Work.A3.completeSum_mul_eq

/-!
# Splitting the complete exponential sum along a factorisation `q = m * n`

For `(m,n) = 1` and `a` coprime to `m * n`, the complete sum `completeSum Q a (m*n)` factors
through the Chinese remainder theorem as a *product* of complete sums at the two moduli, with
multipliers `a*u` (mod `m`) and `a*v` (mod `n`) that are again coprime to the respective moduli.

This is the base case of the induction over the prime factorisation of the modulus: the two
factors produced are coprime to `m` resp. `n`, so the inductive hypothesis (a bound at the prime
powers) applies to each of them.  The pair `(u,v)` is a Bézout pair for `(m,n)`, and the
coprimality of `a*u` with `m` (resp. `a*v` with `n`) is proved by an explicit Bézout
combination: multiplying the two "`= 1`" identities
`(x*a + y*(m*n)) * (u*n + v*m) = 1` and rearranging exhibits `a*u` (resp. `a*v`) as the
coefficient of `1`.
-/

namespace Work.A3

theorem coprime_factor_exists (Q : Polynomial ℤ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hco : m.Coprime n) (a : ℤ) (ha : IsCoprime a (((m * n : ℕ) : ℤ))) :
    ∃ u v : ℤ, IsCoprime (a * u) ((m : ℕ) : ℤ) ∧ IsCoprime (a * v) ((n : ℕ) : ℤ) ∧
      Work.A3.completeSum Q a (m * n) = Work.A3.completeSum Q (a * u) m *
        Work.A3.completeSum Q (a * v) n := by
  -- Bézout data: `x*a + y*(m*n) = 1` from `ha`, and `p*m + q*n = 1` from `hco`.
  obtain ⟨x, y, hxy⟩ := ha
  obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr hco
  have h1 : x * a + y * ((m : ℤ) * (n : ℤ)) = 1 := by
    simpa [Nat.cast_mul] using hxy
  -- `u = q`, `v = p`, so that `u*n + v*m = 1` (which is `h2`).
  have h2 : q * (n : ℤ) + p * (m : ℤ) = 1 := by linarith [hpq]
  refine ⟨q, p, ?_, ?_, ?_⟩
  · -- `a*q` is coprime to `m`: the product of the two "`= 1`" identities, rearranged.
    refine ⟨x * (n : ℤ),
      x * a * p + y * (n : ℤ) * q * (n : ℤ) + y * (n : ℤ) * p * (m : ℤ), ?_⟩
    have hkey : (x * (n : ℤ)) * (a * q) +
        (x * a * p + y * (n : ℤ) * q * (n : ℤ) + y * (n : ℤ) * p * (m : ℤ)) * (m : ℤ)
        = (x * a + y * ((m : ℤ) * (n : ℤ))) * (q * (n : ℤ) + p * (m : ℤ)) := by ring
    rw [hkey, h1, h2, mul_one]
  · -- `a*p` is coprime to `n`: same identity, the other way round.
    refine ⟨x * (m : ℤ),
      x * a * q + y * (m : ℤ) * q * (n : ℤ) + y * (m : ℤ) * p * (m : ℤ), ?_⟩
    have hkey : (x * (m : ℤ)) * (a * p) +
        (x * a * q + y * (m : ℤ) * q * (n : ℤ) + y * (m : ℤ) * p * (m : ℤ)) * (n : ℤ)
        = (x * a + y * ((m : ℤ) * (n : ℤ))) * (q * (n : ℤ) + p * (m : ℤ)) := by ring
    rw [hkey, h1, h2, mul_one]
  · -- The Chinese remainder factorisation of the complete sum.
    exact Work.A3.completeSum_mul_eq Q a q p m n hm hn h2

end Work.A3
