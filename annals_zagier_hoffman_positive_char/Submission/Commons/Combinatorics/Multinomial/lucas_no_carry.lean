import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Multinomial
import Submission.Commons.Data.Nat.choose_add_ne_zero_iff_noCarry
import Submission.Commons.Data.Nat.sum_digits_decomp

namespace Commons.Combinatorics.Multinomial

open Finset

/-- The base-`p` expansion of `n` truncated at length `L`: for `n < p ^ L`,
`n` is the sum of its base-`p` digits weighted by the powers of `p`. -/
theorem sum_digits_range_eq (p : ℕ) (n : ℕ) :
    ∀ L : ℕ, n < p ^ L → ∑ j ∈ Finset.range L, (n / p ^ j % p) * p ^ j = n := by
  intro L
  induction L generalizing n with
  | zero =>
    intro hn
    rw [pow_zero, Nat.lt_one_iff] at hn
    subst hn
    simp
  | succ L ih =>
    intro hn
    rw [Finset.sum_range_succ']
    have hg : ∀ j, (n / p ^ (j + 1) % p) * p ^ (j + 1) =
        ((n / p) / p ^ j % p) * p ^ j * p := by
      intro j
      have h1 : n / p ^ (j + 1) = (n / p) / p ^ j := by
        rw [pow_succ', Nat.div_div_eq_div_mul]
      have h2 : p ^ (j + 1) = p ^ j * p := pow_succ p j
      rw [h1, h2]; ring
    rw [Finset.sum_congr rfl (fun j _ => hg j)]
    rw [← Finset.sum_mul]
    have hdiv : n / p < p ^ L := by
      have hmul : n < p * p ^ L := by
        rw [mul_comm]; rwa [pow_succ] at hn
      exact Nat.div_lt_of_lt_mul hmul
    rw [ih (n / p) hdiv]
    rw [pow_zero, Nat.div_one, mul_one]
    exact Nat.div_add_mod' n p

/-- If the base-`p` "column sums" of the values `f i` (`i ∈ s`) are all `< p`, then the
`k`-th base-`p` digit of `∑ i ∈ s, f i` is the sum of the `k`-th base-`p` digits of the
`f i`: adding the numbers in base `p` produces no carries. -/
theorem sum_div_pow_mod_eq_of_column_lt {p : ℕ} (hp : 1 < p) {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) (h : ∀ j, ∑ i ∈ s, f i / p ^ j % p < p) (k : ℕ) :
    (∑ i ∈ s, f i) / p ^ k % p = ∑ i ∈ s, f i / p ^ k % p := by
  set S := ∑ i ∈ s, f i with hS
  set c : ℕ → ℕ := fun j => ∑ i ∈ s, f i / p ^ j % p with hc
  have hSpos : S < p ^ (S + 1) := by
    calc S < 2 ^ S := Nat.lt_two_pow_self
      _ ≤ 2 ^ (S + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ S)
      _ ≤ p ^ (S + 1) := Nat.pow_le_pow_left (by omega) (S + 1)
  have hdec : S = ∑ j ∈ Finset.range (S + 1), c j * p ^ j := by
    have hterm : ∀ i ∈ s, f i = ∑ j ∈ Finset.range (S + 1), (f i / p ^ j % p) * p ^ j := by
      intro i hi
      exact (sum_digits_range_eq p (f i) (S + 1)
        (lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi) hSpos)).symm
    calc S = ∑ i ∈ s, f i := hS
      _ = ∑ i ∈ s, ∑ j ∈ Finset.range (S + 1), (f i / p ^ j % p) * p ^ j :=
          Finset.sum_congr rfl hterm
      _ = ∑ j ∈ Finset.range (S + 1), ∑ i ∈ s, (f i / p ^ j % p) * p ^ j := Finset.sum_comm
      _ = ∑ j ∈ Finset.range (S + 1), c j * p ^ j := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [hc]
          rw [Finset.sum_mul]
  have hcol : ∀ j < S + 1, c j < p := by
    intro j _
    simp only [hc]
    exact h j
  have hczero : ∀ j, S + 1 ≤ j → c j = 0 := by
    intro j hj
    simp only [hc]
    apply Finset.sum_eq_zero
    intro i hi
    have hfi : f i < p ^ j := by
      calc f i ≤ S := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        _ < p ^ (S + 1) := hSpos
        _ ≤ p ^ j := Nat.pow_le_pow_right (by omega) hj
    rw [Nat.div_eq_of_lt hfi, Nat.zero_mod]
  have key := Commons.Data.Nat.sum_digits_decomp c hcol k
  rw [← hdec] at key
  rcases lt_or_ge k (S + 1) with hk | hk
  · rw [if_pos hk] at key
    exact key
  · rw [if_neg (not_lt.mpr hk)] at key
    rw [key]
    exact (hczero k hk).symm


/-- Dickson's (Lucas-type) theorem for multinomial coefficients mod `p`: the multinomial
coefficient `Nat.multinomial univ a` is not divisible by the prime `p` if and only if the
base-`p` digits of the numbers `a i` sum, at every position, to a value `< p` (equivalently,
adding the `a i` in base `p` produces no carries). -/
theorem lucas_no_carry {p : ℕ} (hp : p.Prime) {ι : Type*} [Fintype ι]
    (a : ι → ℕ) :
    ¬ p ∣ Nat.multinomial Finset.univ a ↔ ∀ j : ℕ, (∑ i, a i / p ^ j % p) < p := by
  classical
  have hp1 : 1 < p := hp.one_lt
  suffices key : ∀ s : Finset ι, ¬ p ∣ Nat.multinomial s a ↔
      ∀ j, (∑ i ∈ s, a i / p ^ j % p) < p by
    exact key Finset.univ
  intro s
  induction s using Finset.induction with
  | empty =>
    rw [Nat.multinomial_empty]
    simp only [Finset.sum_empty]
    exact ⟨fun _ _ => hp.pos, fun _ => hp.not_dvd_one⟩
  | insert b s hb ih =>
    rw [Nat.multinomial_insert hb a]
    rw [hp.dvd_mul, not_or]
    have hcho : ¬ p ∣ (a b + ∑ i ∈ s, a i).choose (a b) ↔
        ∀ j, a b / p ^ j % p + (∑ i ∈ s, a i) / p ^ j % p < p := by
      rw [Commons.Data.Nat.ChooseNoCarry.prime_dvd_choose_iff hp (a b) (∑ i ∈ s, a i),
        not_exists]
      simp only [not_le]
    rw [ih, hcho]
    simp_rw [Finset.sum_insert hb]
    constructor
    · rintro ⟨h1, h2⟩ j
      have h1j := h1 j
      rw [sum_div_pow_mod_eq_of_column_lt hp1 s a h2 j] at h1j
      exact h1j
    · intro h
      have h2 : ∀ j, ∑ i ∈ s, a i / p ^ j % p < p := by
        intro j
        have := h j
        omega
      refine ⟨fun j => ?_, h2⟩
      rw [sum_div_pow_mod_eq_of_column_lt hp1 s a h2 j]
      exact h j

end Commons.Combinatorics.Multinomial