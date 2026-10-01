import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Choose.Lucas

set_option linter.style.haveILetI false

namespace Commons.Algebra.Polynomial

/-- For a prime `p`, if `p ^ n ∣ m` and `0 < h < p ^ n`, then `p ∣ choose m h`.
This is the arithmetic core of the statement that the `k`-th Hasse derivative
(`k < p ^ n`) commutes with right multiplication by `X ^ (j * p ^ n)`: all the
"lower" binomial coefficients `choose (j * p ^ n) h` (`0 < h < p ^ n`) are
divisible by `p`, hence vanish in characteristic `p`.  Proved by induction on `n`
using the Lucas-type recursion `choose n k ≡ choose (n%p) (k%p) * choose (n/p) (k/p)`. -/
theorem prime_dvd_choose_of_pow_dvd {p m h n : ℕ} (hp : p.Prime) (hm : p ^ n ∣ m)
    (h1 : 0 < h) (h2 : h < p ^ n) : p ∣ m.choose h := by
  induction n generalizing m h with
  | zero =>
      rw [pow_zero] at h2
      omega
  | succ n ih =>
      haveI : Fact p.Prime := ⟨hp⟩
      have hpdvdm : p ∣ m := by
        have : p ∣ p ^ (n + 1) := by rw [pow_succ]; exact dvd_mul_left p (p ^ n)
        exact this.trans hm
      have hm0 : m % p = 0 := Nat.mod_eq_zero_of_dvd hpdvdm
      have hrec := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := m) (k := h) (p := p)
      rw [hm0] at hrec
      by_cases hph : p ∣ h
      · have hh0 : 0 < h / p := Nat.div_pos (Nat.le_of_dvd h1 hph) hp.pos
        have hh2 : h / p < p ^ n := by
          have : h < p * p ^ n := by rw [← pow_succ']; exact h2
          exact Nat.div_lt_of_lt_mul this
        have hdiv : p ^ n ∣ m / p := by
          have hmp : m / p * p = m := Nat.div_mul_cancel hpdvdm
          have key : p ^ n * p ∣ m / p * p := by rw [hmp, ← pow_succ]; exact hm
          exact (mul_dvd_mul_iff_right hp.ne_zero).mp key
        have hB : p ∣ (m / p).choose (h / p) := ih hdiv hh0 hh2
        have hBmod : (m / p).choose (h / p) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hB
        have hAmod : (0).choose (h % p) ≡ 1 [MOD p] := by
          rw [Nat.mod_eq_zero_of_dvd hph, Nat.choose_zero_right]
        exact Nat.modEq_zero_iff_dvd.mp (hrec.trans (by simpa using hAmod.mul hBmod))
      · have hne : h % p ≠ 0 := fun hh => hph (Nat.dvd_of_mod_eq_zero hh)
        have hAzero : (0).choose (h % p) = 0 :=
          Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hne)
        rw [hAzero, zero_mul] at hrec
        exact Nat.modEq_zero_iff_dvd.mp hrec

theorem hasseDeriv_mul_X_pow_prime_pow {F : Type*} [Field F] (p n : ℕ) [CharP F p] (hp : p.Prime) (k j : ℕ) (hk : k < p ^ n) (c : Polynomial F) :
    Polynomial.hasseDeriv k (c * Polynomial.X ^ (j * p ^ n)) = (Polynomial.hasseDeriv k c) * Polynomial.X ^ (j * p ^ n) := by
  rw [Polynomial.hasseDeriv_mul]
  trans Polynomial.hasseDeriv k c * Polynomial.hasseDeriv 0 (Polynomial.X ^ (j * p ^ n))
  · refine Finset.sum_eq_single (k, 0) ?_ ?_
    · intro b hb hbne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
      have h2pos : 0 < b.2 := by
        rcases Nat.eq_zero_or_pos b.2 with h | h
        · exfalso
          have hb1 : b.1 = k := by omega
          exact hbne (Prod.ext hb1 h)
        · exact h
      have h2lt : b.2 < p ^ n := by omega
      have hcast : (((j * p ^ n).choose b.2 : ℕ) : F) = 0 := by
        rw [CharP.cast_eq_zero_iff F p]
        exact prime_dvd_choose_of_pow_dvd hp (dvd_mul_left (p ^ n) j) h2pos h2lt
      rw [Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial, hcast, zero_mul,
        Polynomial.monomial_zero_right, mul_zero]
    · intro hnot
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hnot
  · simp

end Commons.Algebra.Polynomial