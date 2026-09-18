import Mathlib.Data.Nat.PrimeFin

namespace Commons.NumberTheory.Nat

/-- `x` is coprime to `q ≠ 0` iff no prime factor of `q` divides `x`. -/
theorem coprime_iff_forall_primeFactors_not_dvd {x q : ℕ} (hq : q ≠ 0) :
    x.Coprime q ↔ ∀ p ∈ q.primeFactors, ¬ p ∣ x := by
  constructor
  · intro hx p hp pdvd
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hpp, pdvd, hpq⟩) hx
  · intro h
    by_contra hx
    rcases Nat.Prime.not_coprime_iff_dvd.mp hx with ⟨p, hpp, hpdvd, hqdvd⟩
    have hp : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hqdvd, hq⟩
    exact h p hp hpdvd

end Commons.NumberTheory.Nat