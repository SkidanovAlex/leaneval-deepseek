import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ulcm k = lcm(1,…,k)` is at most `4 ^ k`

The least common multiple of `1, 2, …, k` satisfies `lcm(1,…,k) ≤ 4^k`.
The proof is the classical one: one shows the two divisibilities
* `lcm(1,…,2m) ∣ centralBinom m · lcm(1,…,m)`
* `lcm(1,…,2m+1) ∣ (2m+1 choose m) · lcm(1,…,m+1)`,
which follow from the usual lower bound on the `p`-adic valuation of a binomial
coefficient, and then runs a strong induction using `choose (2m) m ≤ 4^m` and
`choose (2m+1) m ≤ 2^{2m} = 4^m`.
-/

namespace Work.BW

open Finset

/-- `ulcm n` is `Nat.lcmUpto n` (`lcm` of `{1,…,n}`). -/
lemma ulcm_eq_lcmUpto (n : ℕ) : ulcm n = Nat.lcmUpto n := by
  rw [ulcm, Nat.lcmUpto, Finset.lcm_eq_lcm_image]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩

lemma ulcm_ne_zero (n : ℕ) : ulcm n ≠ 0 := by
  rw [ulcm_eq_lcmUpto]; exact Nat.lcmUpto_ne_zero n

lemma ulcm_pos (n : ℕ) : 0 < ulcm n := Nat.pos_of_ne_zero (ulcm_ne_zero n)

/-- The `p`-adic valuation of `ulcm n` is `⌊log_p n⌋` for a prime `p`. -/
lemma ulcm_factorization (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (ulcm n).factorization p = Nat.log p n := by
  rw [ulcm_eq_lcmUpto]; exact Nat.factorization_lcmUpto n hp

/-- The `p`-adic valuation of `choose (2m) m` is at least `⌊log_p (2m)⌋ - ⌊log_p m⌋`. -/
lemma factorization_choose_two_mul_ge {p : ℕ} (hp : p.Prime) (m : ℕ) :
    Nat.log p (2 * m) ≤ (Nat.choose (2 * m) m).factorization p + Nat.log p m := by
  by_cases hm : m = 0
  · subst hm; simp
  have hp1 : 1 < p := hp.one_lt
  set c := Nat.log p m with hc
  have hm_lt : m < p ^ (c + 1) := by rw [hc]; exact Nat.lt_pow_succ_log_self hp1 m
  have hpow : p ^ (c + 2) = p ^ (c + 1) * p := by
    have : c + 2 = (c + 1) + 1 := by omega
    rw [this, pow_succ]
  have h2mlt : 2 * m < p ^ (c + 2) := by
    rw [hpow]
    have : 2 * p ^ (c + 1) ≤ p ^ (c + 1) * p := by
      calc 2 * p ^ (c + 1) = p ^ (c + 1) * 2 := by rw [mul_comm]
        _ ≤ p ^ (c + 1) * p := Nat.mul_le_mul_left _ hp.two_le
    omega
  have hlog_le : Nat.log p (2 * m) ≤ c + 1 := by
    have := Nat.log_lt_of_lt_pow (b := p) (x := c + 2) (y := 2 * m) (by omega) h2mlt
    omega
  rcases lt_or_eq_of_le hlog_le with h | h
  · omega
  · have hge : 0 < (Nat.choose (2 * m) m).factorization p := by
      have hb : Nat.log p (2 * m) < c + 2 := by omega
      rw [Nat.factorization_choose hp (by omega) hb, Finset.card_pos]
      refine ⟨c + 1, ?_⟩
      rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hm2 : m % p ^ (c + 1) = m := Nat.mod_eq_of_lt hm_lt
      have hsub : 2 * m - m = m := by omega
      rw [hsub, hm2]
      have hp_le : p ^ (c + 1) ≤ 2 * m := by
        have := Nat.pow_log_le_self p (by omega : 2 * m ≠ 0)
        rw [h] at this; exact this
      omega
    omega

/-- The `p`-adic valuation of `choose (2m+1) m` is at least
`⌊log_p (2m+1)⌋ - ⌊log_p (m+1)⌋`. -/
lemma factorization_choose_two_mul_add_one_ge {p : ℕ} (hp : p.Prime) (m : ℕ) :
    Nat.log p (2 * m + 1) ≤
      (Nat.choose (2 * m + 1) m).factorization p + Nat.log p (m + 1) := by
  have hp1 : 1 < p := hp.one_lt
  set c := Nat.log p (m + 1) with hc
  have hm_lt : m + 1 < p ^ (c + 1) := by rw [hc]; exact Nat.lt_pow_succ_log_self hp1 (m + 1)
  have hpow : p ^ (c + 2) = p ^ (c + 1) * p := by
    have : c + 2 = (c + 1) + 1 := by omega
    rw [this, pow_succ]
  have h2mlt : 2 * m + 1 < p ^ (c + 2) := by
    rw [hpow]
    have : 2 * p ^ (c + 1) ≤ p ^ (c + 1) * p := by
      calc 2 * p ^ (c + 1) = p ^ (c + 1) * 2 := by rw [mul_comm]
        _ ≤ p ^ (c + 1) * p := Nat.mul_le_mul_left _ hp.two_le
    omega
  have hlog_le : Nat.log p (2 * m + 1) ≤ c + 1 := by
    have := Nat.log_lt_of_lt_pow (b := p) (x := c + 2) (y := 2 * m + 1) (by omega) h2mlt
    omega
  rcases lt_or_eq_of_le hlog_le with h | h
  · omega
  · have hge : 0 < (Nat.choose (2 * m + 1) m).factorization p := by
      have hb : Nat.log p (2 * m + 1) < c + 2 := by omega
      rw [Nat.factorization_choose hp (by omega) hb, Finset.card_pos]
      refine ⟨c + 1, ?_⟩
      rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hm2 : m % p ^ (c + 1) = m := Nat.mod_eq_of_lt (by omega)
      have hm2' : (m + 1) % p ^ (c + 1) = m + 1 := Nat.mod_eq_of_lt hm_lt
      have hsub : 2 * m + 1 - m = m + 1 := by omega
      rw [hsub, hm2, hm2']
      have hp_le : p ^ (c + 1) ≤ 2 * m + 1 := by
        have := Nat.pow_log_le_self p (by omega : 2 * m + 1 ≠ 0)
        rw [h] at this; exact this
      omega
    omega

/-- `lcm(1,…,2m)` divides `centralBinom m · lcm(1,…,m)`. -/
lemma ulcm_two_mul_dvd (m : ℕ) : ulcm (2 * m) ∣ Nat.choose (2 * m) m * ulcm m := by
  rw [← Nat.factorization_prime_le_iff_dvd (ulcm_ne_zero (2 * m))
    (Nat.mul_ne_zero (Nat.choose_ne_zero (by omega)) (ulcm_ne_zero m))]
  intro p hp
  rw [ulcm_factorization (2 * m) hp,
    Nat.factorization_mul (Nat.choose_ne_zero (by omega)) (ulcm_ne_zero m),
    Finsupp.add_apply, ulcm_factorization m hp]
  exact factorization_choose_two_mul_ge hp m

/-- `lcm(1,…,2m+1)` divides `(2m+1 choose m) · lcm(1,…,m+1)`. -/
lemma ulcm_two_mul_add_one_dvd (m : ℕ) :
    ulcm (2 * m + 1) ∣ Nat.choose (2 * m + 1) m * ulcm (m + 1) := by
  rw [← Nat.factorization_prime_le_iff_dvd (ulcm_ne_zero (2 * m + 1))
    (Nat.mul_ne_zero (Nat.choose_ne_zero (by omega)) (ulcm_ne_zero (m + 1)))]
  intro p hp
  rw [ulcm_factorization (2 * m + 1) hp,
    Nat.factorization_mul (Nat.choose_ne_zero (by omega)) (ulcm_ne_zero (m + 1)),
    Finsupp.add_apply, ulcm_factorization (m + 1) hp]
  exact factorization_choose_two_mul_add_one_ge hp m

/-- `(2m).choose m ≤ 4 ^ m`. -/
lemma choose_two_mul_le_four_pow (m : ℕ) : Nat.choose (2 * m) m ≤ 4 ^ m := by
  have h : Nat.choose (2 * m) m ≤ 2 ^ (2 * m) := Nat.choose_le_two_pow _ _
  calc Nat.choose (2 * m) m ≤ 2 ^ (2 * m) := h
    _ = 4 ^ m := by rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, pow_mul]

/-- `(2m+1).choose m ≤ 4 ^ m`. -/
lemma choose_two_mul_add_one_le_four_pow (m : ℕ) : Nat.choose (2 * m + 1) m ≤ 4 ^ m := by
  have h : Nat.choose (2 * m + 1) m ≤ 2 ^ (2 * m) := Nat.choose_succ_le_two_pow (2 * m) m
  calc Nat.choose (2 * m + 1) m ≤ 2 ^ (2 * m) := h
    _ = 4 ^ m := by rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, pow_mul]

/-- `4 ^ m * 4 ^ n = 4 ^ (m + n)`. -/
lemma four_pow_mul (m n : ℕ) : 4 ^ m * 4 ^ n = 4 ^ (m + n) := by rw [pow_add]

theorem ulcm_le_four_pow (k : ℕ) : (ulcm k : ℝ) ≤ 4 ^ k := by
  have key : ulcm k ≤ 4 ^ k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases Nat.even_or_odd k with hk | hk
      · obtain ⟨m, hm⟩ := hk
        rw [hm, ← two_mul m] at ih ⊢
        rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · simp [ulcm]
        · have hmk : m < 2 * m := by omega
          have hpos : 0 < Nat.choose (2 * m) m * ulcm m :=
            Nat.mul_pos (Nat.choose_pos (by omega)) (ulcm_pos m)
          calc ulcm (2 * m)
              ≤ Nat.choose (2 * m) m * ulcm m := Nat.le_of_dvd hpos (ulcm_two_mul_dvd m)
            _ ≤ 4 ^ m * ulcm m := by
                gcongr; exact choose_two_mul_le_four_pow m
            _ ≤ 4 ^ m * 4 ^ m := by gcongr; exact ih m hmk
            _ = 4 ^ (2 * m) := by rw [four_pow_mul]; congr 1; omega
      · obtain ⟨m, rfl⟩ := hk
        rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · simp [ulcm]
        · have hmk : m + 1 < 2 * m + 1 := by omega
          have hpos : 0 < Nat.choose (2 * m + 1) m * ulcm (m + 1) :=
            Nat.mul_pos (Nat.choose_pos (by omega)) (ulcm_pos (m + 1))
          calc ulcm (2 * m + 1)
              ≤ Nat.choose (2 * m + 1) m * ulcm (m + 1) :=
                Nat.le_of_dvd hpos (ulcm_two_mul_add_one_dvd m)
            _ ≤ 4 ^ m * ulcm (m + 1) := by
                gcongr; exact choose_two_mul_add_one_le_four_pow m
            _ ≤ 4 ^ m * 4 ^ (m + 1) := by gcongr; exact ih (m + 1) hmk
            _ = 4 ^ (2 * m + 1) := by rw [four_pow_mul]; congr 1; omega
  exact_mod_cast key

end Work.BW
