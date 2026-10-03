import Mathlib
import Submission.Work.FIArea7.MSmoothDefs

namespace Work.FIArea7

/-- For coprime `a`, `b`, at most one of them is divisible by a given prime `p`, hence at most
one of the two `factorization` exponents is nonzero. -/
lemma factorization_eq_zero_or_of_coprime {a b p : ℕ} (h : a.Coprime b) :
    a.factorization p = 0 ∨ b.factorization p = 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨ha, hb⟩ := hc
  have hpa : p ∣ a := Nat.dvd_of_factorization_pos ha
  have hpb : p ∣ b := Nat.dvd_of_factorization_pos hb
  have hp1 : p = 1 :=
    Nat.dvd_one.mp (h.gcd_eq_one ▸ Nat.dvd_gcd hpa hpb)
  exact ha (by rw [hp1]; exact Nat.factorization_eq_zero_of_not_prime a Nat.not_prime_one)

/-- The per-prime factor `hterm m p ·` is multiplicative in the exponent under coprimality. -/
lemma hterm_mul_factorization_of_coprime (m a b p : ℕ) (h : a.Coprime b) :
    hterm m p ((a * b).factorization p)
      = hterm m p (a.factorization p) * hterm m p (b.factorization p) := by
  rw [Nat.factorization_mul_apply_of_coprime h]
  rcases factorization_eq_zero_or_of_coprime h with ha | hb
  · rw [ha, Nat.zero_add, hterm_zero, one_mul]
  · rw [hb, Nat.add_zero, hterm_zero, mul_one]

lemma hfac_mul_of_coprime (m a b : ℕ) (h : a.Coprime b) :
    hfac m (a * b) = hfac m a * hfac m b := by
  simp only [hfac]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => hterm_mul_factorization_of_coprime m a b p h

end Work.FIArea7
