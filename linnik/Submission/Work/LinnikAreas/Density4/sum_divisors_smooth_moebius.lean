import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

/-!
# The Möbius sum over `k`-smooth divisors

For `SmoothOf d k ↔ d ∣ k ^ d` (i.e. every prime factor of `d` divides `k`, see the
docstring of `SmoothOf`) we prove

`∑_{d ∣ n, d k-smooth} μ (n / d) = if (n,k) = 1 then μ n else 0`.

The proof identifies the sum with the Dirichlet convolution `f_k * μ` where `f_k` is the
indicator of the smooth numbers (an arithmetic function).  Both `f_k * μ` and the
right hand side `n ↦ [n ⊥ k] · μ n` are multiplicative, so by
`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers` it suffices to check
prime powers, where the smooth divisors of `p ^ i` are `{1}` if `p ∤ k` and all of
`(p ^ i).divisors` if `p ∣ k`.
-/

namespace Work.LinnikAreas.Density4

open Finset

/-! ### The predicate `SmoothOf` -/

/-- `d` is `0`-smooth iff it is nonzero (every `d ≠ 0` divides `0 ^ d = 0`). -/
lemma smoothOf_zero_iff (d : ℕ) : SmoothOf d 0 ↔ d ≠ 0 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [SmoothOf]
  · rw [SmoothOf, zero_pow hd]
    exact iff_of_true (dvd_zero d) hd

/-- `d` is `k`-smooth iff every prime divisor of `d` divides `k`. -/
lemma smoothOf_iff_prime_dvd {d k : ℕ} (hd : d ≠ 0) :
    SmoothOf d k ↔ ∀ p : ℕ, p.Prime → p ∣ d → p ∣ k := by
  rw [SmoothOf]
  constructor
  · intro h p hp hpd
    exact hp.dvd_of_dvd_pow (hpd.trans h)
  · intro h
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro q a hq hqad
    rcases eq_or_ne a 0 with rfl | ha
    · exact one_dvd _
    have hqd : q ∣ d := (dvd_pow_self q ha).trans hqad
    have hqk : q ∣ k := h q hq hqd
    have hle : a ≤ d := by
      have h1 : a ≤ q ^ a := le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hq.two_le a)
      have h2 : q ^ a ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hqad
      omega
    exact (pow_dvd_pow q hle).trans (pow_dvd_pow_of_dvd hqk d)

/-- Smoothness is multiplicative on nonzero coprime (indeed arbitrary nonzero) factors. -/
lemma smoothOf_mul_iff {m n k : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    SmoothOf (m * n) k ↔ SmoothOf m k ∧ SmoothOf n k := by
  rw [smoothOf_iff_prime_dvd (Nat.mul_ne_zero hm hn),
      smoothOf_iff_prime_dvd hm, smoothOf_iff_prime_dvd hn]
  constructor
  · intro h
    exact ⟨fun p hp hpd => h p hp (dvd_mul_of_dvd_left hpd n),
           fun p hp hpd => h p hp (dvd_mul_of_dvd_right hpd m)⟩
  · rintro ⟨h1, h2⟩ p hp hpd
    rcases hp.dvd_mul.mp hpd with h | h
    · exact h1 p hp h
    · exact h2 p hp h

/-- For a prime `p`, `p ^ i = 1` only for `i = 0`. -/
lemma prime_pow_eq_one {p i : ℕ} (hp : p.Prime) : p ^ i = 1 ↔ i = 0 := by
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · refine iff_of_false ?_ hi
    intro h
    exact hp.not_dvd_one (h ▸ dvd_pow_self p hi)

/-- The prime powers that are `k`-smooth are exactly `1` and the ones whose prime divides `k`. -/
lemma smoothOf_prime_pow {p j k : ℕ} (hp : p.Prime) : SmoothOf (p ^ j) k ↔ j = 0 ∨ p ∣ k := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  constructor
  · intro h
    right
    exact hp.dvd_of_dvd_pow ((dvd_pow_self p hj).trans h)
  · rintro (rfl | hpk)
    · exact absurd rfl hj
    have h1 : p ^ j ∣ k ^ j := pow_dvd_pow_of_dvd hpk j
    have h2 : k ^ j ∣ k ^ (p ^ j) :=
      pow_dvd_pow k (le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hp.two_le j))
    exact h1.trans h2

/-- The Möbius inversion identity `∑_{d ∣ n} μ d = [n = 1]`, over `ℝ`. -/
lemma sum_moebius_divisors_eq (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ)
  have h2 := DFunLike.congr_fun h n
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h2
  simpa using h2

/-! ### The two arithmetic functions -/

/-- Indicator of the `k`-smooth numbers, as an arithmetic function. -/
noncomputable def smoothInd (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if SmoothOf d k then 1 else 0, by simp [SmoothOf]⟩

/-- The Möbius function, viewed as an arithmetic function with values in `ℝ`. -/
abbrev moebiusR : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

/-- The function `n ↦ [n ⊥ k] · μ n`. -/
def topFun (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n k then ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0, by simp⟩

lemma isMultiplicative_smoothInd (k : ℕ) : (smoothInd k).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [smoothInd, SmoothOf], ?_⟩
  intro m n hm hn hmn
  rcases eq_or_ne k 0 with rfl | hk
  · show (if SmoothOf (m * n) 0 then (1 : ℝ) else 0) =
      (if SmoothOf m 0 then 1 else 0) * (if SmoothOf n 0 then 1 else 0)
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    simp [smoothOf_zero_iff, hm, hn, hmn0]
  · have hiff := smoothOf_mul_iff hm hn (k := k)
    by_cases h1 : SmoothOf m k <;> by_cases h2 : SmoothOf n k
    · have h3 : SmoothOf (m * n) k := hiff.mpr ⟨h1, h2⟩
      simp [smoothInd, h3, h1, h2]
    · have h3 : ¬ SmoothOf (m * n) k := fun hh => h2 (hiff.mp hh).2
      simp [smoothInd, h3, h1, h2]
    · have h3 : ¬ SmoothOf (m * n) k := fun hh => h1 (hiff.mp hh).1
      simp [smoothInd, h3, h1, h2]
    · have h3 : ¬ SmoothOf (m * n) k := fun hh => h1 (hiff.mp hh).1
      simp [smoothInd, h3, h1, h2]

/-- `n ↦ [n ⊥ k] · μ n` is multiplicative. -/
lemma coprime_moebius_mul_eq (k m n : ℕ) (hmn : m.Coprime n) :
    (if Nat.Coprime (m * n) k then (ArithmeticFunction.moebius (m * n) : ℝ) else 0)
      = (if Nat.Coprime m k then (ArithmeticFunction.moebius m : ℝ) else 0)
        * (if Nat.Coprime n k then (ArithmeticFunction.moebius n : ℝ) else 0) := by
  by_cases h : Nat.Coprime (m * n) k
  · have hmk : Nat.Coprime m k := h.coprime_mul_right
    have hnk : Nat.Coprime n k := h.coprime_mul_left
    rw [if_pos h, if_pos hmk, if_pos hnk,
      ArithmeticFunction.IsMultiplicative.map_mul_of_coprime ArithmeticFunction.isMultiplicative_moebius hmn]
    push_cast
    ring
  · rw [if_neg h]
    have : ¬ (Nat.Coprime m k ∧ Nat.Coprime n k) := fun ⟨h1, h2⟩ => h (h1.mul_left h2)
    rcases not_and_or.mp this with h1 | h1
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h1, mul_zero]

lemma isMultiplicative_topFun (k : ℕ) : (topFun k).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [topFun], ?_⟩
  intro m n hm hn hmn
  show (if Nat.Coprime (m * n) k then ((ArithmeticFunction.moebius (m * n) : ℤ) : ℝ) else 0)
      = (if Nat.Coprime m k then ((ArithmeticFunction.moebius m : ℤ) : ℝ) else 0)
        * (if Nat.Coprime n k then ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0)
  exact coprime_moebius_mul_eq k m n hmn

/-! ### The two functions agree, checked on prime powers -/

private lemma sum_range_indicator (p i k : ℕ) (hp : p.Prime) :
    (∑ x ∈ Finset.range (i + 1),
        (if x = 0 ∨ p ∣ k then (1 : ℝ) else 0) * (ArithmeticFunction.moebius (p ^ (i - x)) : ℝ))
      = if p ∣ k then (if i = 0 then 1 else 0) else (ArithmeticFunction.moebius (p ^ i) : ℝ) := by
  by_cases hpk : p ∣ k
  · rw [if_pos hpk]
    have h1 : ∀ x ∈ Finset.range (i + 1),
        (if x = 0 ∨ p ∣ k then (1 : ℝ) else 0) * (ArithmeticFunction.moebius (p ^ (i - x)) : ℝ)
          = (ArithmeticFunction.moebius (p ^ (i - x)) : ℝ) := by
      intro x hx
      rw [if_pos (Or.inr hpk), one_mul]
    rw [Finset.sum_congr rfl h1]
    have h2 : (∑ x ∈ Finset.range (i + 1), (ArithmeticFunction.moebius (p ^ (i - x)) : ℝ))
        = ∑ x ∈ (p ^ i).divisors, (ArithmeticFunction.moebius x : ℝ) := by
      rw [Nat.sum_divisors_prime_pow hp]
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun e => (ArithmeticFunction.moebius (p ^ e) : ℝ)) (i + 1))
    rw [h2, sum_moebius_divisors_eq]
    by_cases hi : i = 0
    · rw [if_pos ((prime_pow_eq_one hp).mpr hi), if_pos hi]
    · rw [if_neg (fun h => hi ((prime_pow_eq_one hp).mp h)), if_neg hi]
  · rw [if_neg hpk]
    have h1 : ∀ x : ℕ, (if x = 0 ∨ p ∣ k then (1 : ℝ) else 0) = (if x = 0 then 1 else 0) := by
      intro x
      by_cases hx : x = 0 <;> simp [hx, hpk]
    simp only [h1]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro x hx hx0
      simp [hx0]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos i)) h0

lemma smoothInd_mul_moebiusR_prime_pow {p i k : ℕ} (hp : p.Prime) :
    (smoothInd k * moebiusR) (p ^ i) = topFun k (p ^ i) := by
  rw [ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ (p ^ i).divisorsAntidiagonal, (smoothInd k) x.1 * moebiusR x.2)
      = ∑ d ∈ (p ^ i).divisors, (smoothInd k) d * moebiusR (p ^ i / d) from
      Nat.sum_divisorsAntidiagonal (fun a b => (smoothInd k) a * moebiusR b)]
  rw [Nat.sum_divisors_prime_pow hp]
  have hterm : ∀ x ∈ Finset.range (i + 1),
      (smoothInd k) (p ^ x) * moebiusR (p ^ i / p ^ x)
        = (if x = 0 ∨ p ∣ k then (1 : ℝ) else 0)
          * (ArithmeticFunction.moebius (p ^ (i - x)) : ℝ) := by
    intro x hx
    have hxi : x ≤ i := by
      have : x < i + 1 := Finset.mem_range.mp hx
      omega
    rw [Nat.pow_div hxi hp.pos, moebiusR, ArithmeticFunction.intCoe_apply]
    by_cases h : x = 0 ∨ p ∣ k
    · rw [if_pos h]
      have hs : SmoothOf (p ^ x) k := (smoothOf_prime_pow hp).mpr h
      simp [smoothInd, hs]
    · rw [if_neg h]
      have hs : ¬ SmoothOf (p ^ x) k := fun hh => h ((smoothOf_prime_pow hp).mp hh)
      simp [smoothInd, hs]
  rw [Finset.sum_congr rfl hterm, sum_range_indicator p i k hp]
  change (if p ∣ k then (if i = 0 then 1 else 0) else (ArithmeticFunction.moebius (p ^ i) : ℝ))
      = (if Nat.Coprime (p ^ i) k then (ArithmeticFunction.moebius (p ^ i) : ℝ) else 0)
  by_cases hpk : p ∣ k
  · rw [if_pos hpk]
    by_cases hi : i = 0
    · subst hi
      simp
    · have hnc : ¬ Nat.Coprime (p ^ i) k := by
        rw [Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hi)]
        exact (Nat.Prime.dvd_iff_not_coprime hp).mp hpk
      rw [if_neg hnc, if_neg hi]
  · rw [if_neg hpk]
    have hc : Nat.Coprime (p ^ i) k := (hp.coprime_iff_not_dvd.mpr hpk).pow_left i
    rw [if_pos hc]

/-- `f_k * μ = n ↦ [n ⊥ k] · μ n`. -/
lemma smoothInd_mul_moebiusR_eq (k : ℕ) : smoothInd k * moebiusR = topFun k := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      (smoothInd k * moebiusR) ?_ (topFun k) ?_).mpr ?_
  · exact (isMultiplicative_smoothInd k).mul (ArithmeticFunction.isMultiplicative_moebius.intCast (R := ℝ))
  · exact isMultiplicative_topFun k
  · intro p i hp
    exact smoothInd_mul_moebiusR_prime_pow (k := k) hp

/-! ### The divisor-sum form of the statement -/

/-- The filtered divisor sum is the value of the Dirichlet convolution `f_k * μ`. -/
lemma sum_filter_eq_conv (n k : ℕ) :
    (∑ d ∈ n.divisors.filter (fun d => SmoothOf d k),
        (ArithmeticFunction.moebius (n / d) : ℝ))
      = (smoothInd k * moebiusR) n := by
  rw [ArithmeticFunction.mul_apply, Finset.sum_filter]
  rw [show (∑ x ∈ n.divisorsAntidiagonal, (smoothInd k) x.1 * moebiusR x.2)
      = ∑ d ∈ n.divisors, (smoothInd k) d * moebiusR (n / d) from
      Nat.sum_divisorsAntidiagonal (fun a b => (smoothInd k) a * moebiusR b)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [moebiusR, ArithmeticFunction.intCoe_apply]
  by_cases h : SmoothOf d k <;> simp [smoothInd, h]

theorem sum_divisors_smooth_moebius (n k : ℕ) :
    (∑ d ∈ n.divisors.filter (fun d => Work.LinnikAreas.Density4.SmoothOf d k),
        (ArithmeticFunction.moebius (n / d) : ℝ))
      = if Nat.Coprime n k then (ArithmeticFunction.moebius n : ℝ) else 0 := by
  rw [sum_filter_eq_conv, smoothInd_mul_moebiusR_eq]
  rfl

end Work.LinnikAreas.Density4
