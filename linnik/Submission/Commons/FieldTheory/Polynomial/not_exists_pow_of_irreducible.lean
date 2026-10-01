import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial

namespace Commons.FieldTheory.Polynomial

/-- `X^n - C a` is reducible over a field when `a = b^p` with `p ∣ n`: the geometric-sum
factorization `X^{p·m} - b^p = (X^m - b)·(X^{m(p-1)} + X^{m(p-2)}b + … + b^{p-1})`. -/
theorem not_irreducible_X_pow_sub_C_of_exists_pow {F : Type*} [Field F] {n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn : n ≠ 0) {a b : F} (_hb : b ≠ 0) (hab : a = b ^ p) :
    ¬ Irreducible (X ^ n - C a : Polynomial F) := by
  intro hirr
  have hmp : n = (n / p) * p := (Nat.div_mul_cancel hpn).symm
  have hfac : X ^ n - C a = (X ^ (n / p)) ^ p - (C b) ^ p := by
    have h1 : (X : Polynomial F) ^ n = (X ^ (n / p)) ^ p := by
      conv_lhs => rw [hmp]
      rw [pow_mul]
    have h2 : (C a : Polynomial F) = (C b) ^ p := by rw [hab, map_pow]
    rw [h1, h2]
  have hdvd : (X ^ (n / p) - C b : Polynomial F) ∣ (X ^ n - C a) := by
    rw [hfac]
    exact sub_dvd_pow_sub_pow _ _ p
  obtain ⟨q, hq⟩ := hdvd
  have hd0 : (X ^ (n / p) - C b : Polynomial F) ≠ 0 := by
    intro h
    have h2 := congrArg Polynomial.natDegree h
    rw [natDegree_X_pow_sub_C, natDegree_zero] at h2
    exact hn (by rw [hmp, h2, zero_mul])
  rcases hirr.isUnit_or_isUnit hq with h1 | h1
  · have h2 := natDegree_eq_zero_of_isUnit h1
    rw [natDegree_X_pow_sub_C] at h2
    exact hn (by rw [hmp, h2, zero_mul])
  · have hq0 : q ≠ 0 := h1.ne_zero
    have hmul := congrArg Polynomial.natDegree hq
    rw [natDegree_mul hd0 hq0, natDegree_X_pow_sub_C, natDegree_X_pow_sub_C,
      natDegree_eq_zero_of_isUnit h1, add_zero] at hmul
    have hp0 : 0 < n / p :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos
    have h3 : n / p * p = n / p * 1 := by
      rw [mul_one]
      exact hmp.symm.trans hmul
    exact hp.ne_one (Nat.eq_of_mul_eq_mul_left hp0 h3)

/-- **The Kummer condition is automatic.**  If `X^n - C a` is irreducible over a field `F` and
`a ≠ 0`, then `a` is not a `p`-th power for any prime `p ∣ n`. -/
theorem not_exists_pow_of_irreducible {F : Type*} [Field F] {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn : n ≠ 0) {a : F} (ha : a ≠ 0) (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C a)) :
    ¬ ∃ b : F, b ^ p = a := by
  rintro ⟨b, hb⟩
  have hb0 : b ≠ 0 := by
    intro h
    exact ha (by rw [← hb, h, zero_pow hp.pos.ne'])
  exact not_irreducible_X_pow_sub_C_of_exists_pow hp hpn hn hb0 hb.symm hirr

end Commons.FieldTheory.Polynomial
