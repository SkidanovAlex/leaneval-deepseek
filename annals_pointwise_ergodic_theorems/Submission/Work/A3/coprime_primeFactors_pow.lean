import Mathlib
import Submission.Work.A3.Circle

namespace Work.A3

/-- Distinct prime divisors of `q` give coprime prime powers. -/
theorem coprime_primeFactors_pow (q p p' : ℕ) (hp : p ∈ q.primeFactors)
    (hp' : p' ∈ q.primeFactors) (hne : p ≠ p') :
    (p ^ q.factorization p).Coprime (p' ^ q.factorization p') := by
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpp' : Nat.Prime p' := Nat.prime_of_mem_primeFactors hp'
  have hcop : Nat.Coprime p p' := by
    rw [hpp.coprime_iff_not_dvd]
    intro hd
    rcases (Nat.dvd_prime hpp').mp hd with h | h
    · exact hpp.ne_one h
    · exact hne h
  exact hcop.pow _ _

end Work.A3
