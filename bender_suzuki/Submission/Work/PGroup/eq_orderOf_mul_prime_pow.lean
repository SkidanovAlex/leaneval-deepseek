import Mathlib
import Submission.Work.PGroup.Cyc2Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `q`-part of an index `n` with `q ∣ Φ_n(2)`

If a prime `q ≠ 2` divides the cyclotomic value `Φ_n(2) = PhiZ n`, then the multiplicative
order `d = orderOf (2 : ZMod q)` divides `n`, and the remaining factor `n / d` is a power of
`q`:

`n = orderOf (2 : ZMod q) * q ^ j`.

This is the standard "primitive prime divisor" bookkeeping for the base `2`; it is the
combinatorial input for the Bang–Zsigmondy argument (`bang_zsigmondy_two`).

The proof is a strong induction on `n` using the cyclotomic `expand` recursion
`Φ_m(X ^ q) = Φ_{m·q}(X) · Φ_m(X)` for `q ∤ m` (and `Φ_m(X ^ q) = Φ_{m·q}(X)` for `q ∣ m`):
writing `m = n / q`, the divisor `q` of `Φ_n(2)` forces `q ∣ Φ_m(2 ^ q)`, and since
`2 ^ q ≡ 2 (mod q)` this gives `q ∣ Φ_m(2)`.  If `q ∤ m`, the order is exactly `m`; if
`q ∣ m`, the induction hypothesis applies to `m < n`.
-/

namespace Work.PGroup

/-- Evaluation of `cyclotomic m` over `ZMod q` at the image of `a : ℤ` equals the image of
the value of `cyclotomic m` over `ℤ` at `a`. -/
lemma eval_cyclotomic_eq_intCast (q m : ℕ) (a : ℤ) :
    Polynomial.eval ((a : ℤ) : ZMod q) (Polynomial.cyclotomic m (ZMod q))
      = ((Polynomial.eval a (Polynomial.cyclotomic m ℤ) : ℤ) : ZMod q) := by
  rw [← Polynomial.map_cyclotomic_int m (ZMod q)]
  exact Polynomial.eval_map_apply (Int.castRingHom (ZMod q)) a

/-- If `q ∣ Φ_m(2 ^ q)` then `q ∣ Φ_m(2)`, because `2 ^ q ≡ 2 (mod q)`. -/
lemma dvd_PhiZ_of_dvd_eval_pow {q m : ℕ} (hq : q.Prime)
    (hA : (q : ℤ) ∣ (Polynomial.cyclotomic m ℤ).eval ((2 : ℤ) ^ q)) :
    (q : ℤ) ∣ PhiZ m := by
  have : Fact q.Prime := ⟨hq⟩
  have hzero : (((Polynomial.cyclotomic m ℤ).eval ((2 : ℤ) ^ q) : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hA
  have heq : (((Polynomial.cyclotomic m ℤ).eval (2 : ℤ) : ℤ) : ZMod q) = 0 := by
    rw [← eval_cyclotomic_eq_intCast]
    rw [show ((2 : ℤ) : ZMod q) = (((2 : ℤ) ^ q : ℤ) : ZMod q) by
      push_cast; rw [ZMod.pow_card]]
    rw [← hzero]
    rw [← eval_cyclotomic_eq_intCast]
  rw [PhiZ]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp heq

theorem eq_orderOf_mul_prime_pow {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : (q : ℤ) ∣ PhiZ n) : ∃ j : ℕ, n = orderOf (2 : ZMod q) * q ^ j := by
  revert hdvd
  refine Nat.strong_induction_on n ?_
  intro n ih hdvd
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exfalso
    have h1 : PhiZ 0 = 1 := by rw [PhiZ, Polynomial.cyclotomic_zero, Polynomial.eval_one]
    rw [h1] at hdvd
    have h2 : (q : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
    have h3 : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.two_le
    omega
  by_cases hqn : q ∣ n
  · set m := n / q with hm
    have hn_eq : n = m * q := by
      rw [hm]
      exact (Nat.div_mul_cancel hqn).symm
    have hm_pos : 0 < m := by
      rw [hm]
      exact Nat.div_pos (Nat.le_of_dvd hn hqn) hq.pos
    have hm_lt : m < n := by
      rw [hn_eq]
      have := Nat.mul_lt_mul_of_pos_left hq.one_lt hm_pos
      simpa using this
    have hPhiZ_m : (q : ℤ) ∣ PhiZ m := by
      apply dvd_PhiZ_of_dvd_eval_pow hq
      rw [← Polynomial.expand_eval]
      by_cases hqm : q ∣ m
      · rw [Polynomial.cyclotomic_expand_eq_cyclotomic hq hqm ℤ]
        rw [← hn_eq]
        exact hdvd
      · rw [Polynomial.cyclotomic_expand_eq_cyclotomic_mul hq hqm ℤ, Polynomial.eval_mul]
        refine dvd_mul_of_dvd_left ?_ _
        rw [← hn_eq]
        exact hdvd
    by_cases hqm : q ∣ m
    · obtain ⟨j, hj⟩ := ih m hm_lt hPhiZ_m
      exact ⟨j + 1, by rw [hn_eq, hj, pow_succ]; ring⟩
    · have hd := orderOf_two_eq_of_dvd_PhiZ q m hq hqm hPhiZ_m
      exact ⟨1, by rw [hn_eq, hd, pow_one]⟩
  · have hd := orderOf_two_eq_of_dvd_PhiZ q n hq hqn hdvd
    exact ⟨0, by rw [pow_zero, mul_one, hd]⟩

end Work.PGroup
