import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace Commons.NumberTheory.Moebius

open Finset
open scoped ArithmeticFunction.Moebius

/-- The sum of the Möbius function over the divisors of `k` is `1` for `k = 1` and `0` otherwise. -/
lemma divisors_sum_moebius (k : ℕ) :
    ∑ n ∈ k.divisors, (ArithmeticFunction.moebius n : ℤ) = if k = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply
        (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ)) (x := k)]
  rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.one_apply]

/-- For `1 ≤ k ≤ x`, the positive divisors of `k` are exactly the elements of `[1, x]` dividing `k`. -/
lemma filter_Icc_dvd_eq_divisors {x k : ℕ} (hk1 : 1 ≤ k) (hkx : k ≤ x) :
    (Finset.Icc 1 x).filter (fun n => n ∣ k) = k.divisors := by
  ext n
  rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, by omega⟩
  · rintro ⟨h3, hk0⟩
    have hn0 : n ≠ 0 := by rintro rfl; exact hk0 (zero_dvd_iff.mp h3)
    exact ⟨⟨by omega, le_trans (Nat.le_of_dvd (by omega) h3) hkx⟩, h3⟩

/-- Double counting identity: `∑_{n ≤ x} μ(n) ⌊x/n⌋ = 1`. -/
lemma sum_moebius_mul_div_eq_one (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℤ) * ((x / n : ℕ) : ℤ) = 1 := by
  have hcard : ∀ n : ℕ, ((x / n : ℕ) : ℤ) =
      ((#{k ∈ Finset.range (x+1) | k ≠ 0 ∧ n ∣ k}) : ℤ) := by
    intro n; rw [Nat.card_multiples']
  calc
    ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℤ) * ((x / n : ℕ) : ℤ)
      = ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℤ) *
          (∑ k ∈ Finset.range (x+1), if k ≠ 0 ∧ n ∣ k then (1:ℤ) else 0) := by
        apply Finset.sum_congr rfl; intro n hn
        rw [hcard n, Finset.card_filter]
        push_cast
        rfl
    _ = ∑ n ∈ Finset.Icc 1 x, ∑ k ∈ Finset.range (x+1),
          (ArithmeticFunction.moebius n : ℤ) * (if k ≠ 0 ∧ n ∣ k then (1:ℤ) else 0) := by
        apply Finset.sum_congr rfl; intro n hn
        rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (x+1), ∑ n ∈ Finset.Icc 1 x,
          (ArithmeticFunction.moebius n : ℤ) * (if k ≠ 0 ∧ n ∣ k then (1:ℤ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (x+1), (if k = 1 then (1:ℤ) else 0) := by
        apply Finset.sum_congr rfl; intro k hk
        rw [Finset.mem_range] at hk
        simp only [mul_ite, mul_one, mul_zero]
        by_cases hk0 : k = 0
        · subst hk0
          simp
        · have hk1 : 1 ≤ k := by omega
          have hkx : k ≤ x := by omega
          simp only [show (k ≠ 0) = True from eq_true hk0, true_and]
          rw [← Finset.sum_filter, filter_Icc_dvd_eq_divisors hk1 hkx, divisors_sum_moebius k]
    _ = 1 := by
        have : (1:ℕ) ∈ Finset.range (x+1) := by rw [Finset.mem_range]; omega
        rw [Finset.sum_ite_eq' (Finset.range (x+1)) 1 (fun _ => (1:ℤ)), if_pos this]

/-- Real version of the double counting identity. -/
lemma sum_moebius_mul_div_eq_one_real (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ) * ((x / n : ℕ) : ℝ) = 1 := by
  have h := sum_moebius_mul_div_eq_one x hx
  rw [show (∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ) * ((x / n : ℕ) : ℝ))
        = ((∑ n ∈ Finset.Icc 1 x,
              (ArithmeticFunction.moebius n : ℤ) * ((x / n : ℕ) : ℤ) : ℤ) : ℝ) from by
        push_cast; rfl]
  rw [h]
  norm_num

/-- The basic termwise identity `μ n / n = (1/x) (μ n ⌊x/n⌋ + μ n (x mod n)/n)`. -/
lemma moebius_term_eq (x n : ℕ) (hx : 1 ≤ x) (hn : 1 ≤ n) :
    (ArithmeticFunction.moebius n : ℝ)/(n:ℝ)
      = (1/(x:ℝ))*((ArithmeticFunction.moebius n : ℝ)*((x/n:ℕ):ℝ)
          + (ArithmeticFunction.moebius n : ℝ)*((x%n:ℕ):ℝ)/(n:ℝ)) := by
  have key : (n:ℝ) * ((x/n:ℕ):ℝ) + ((x%n:ℕ):ℝ) = (x:ℝ) := by
    exact_mod_cast (Nat.div_add_mod x n)
  have hn0 : (n:ℝ) ≠ 0 := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    linarith
  have hx0 : (x:ℝ) ≠ 0 := by
    have : (0:ℝ) < x := by exact_mod_cast hx
    linarith
  have hdiv : ((x/n:ℕ):ℝ) + ((x%n:ℕ):ℝ)/(n:ℝ) = (x:ℝ)/(n:ℝ) := by
    rw [eq_div_iff hn0, add_mul, div_mul_cancel₀ _ hn0]
    linarith [key]
  have h2 : (1/(x:ℝ))*((ArithmeticFunction.moebius n : ℝ)*((x/n:ℕ):ℝ)
          + (ArithmeticFunction.moebius n : ℝ)*((x%n:ℕ):ℝ)/(n:ℝ))
        = (ArithmeticFunction.moebius n : ℝ) *
            (((x/n:ℕ):ℝ) + ((x%n:ℕ):ℝ)/(n:ℝ)) * (1/(x:ℝ)) := by
    ring
  rw [h2, hdiv]
  field_simp

theorem sum_moebius_div_abs_le : ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
    |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ C := by
  refine ⟨2, by norm_num, ?_⟩
  intro x hx
  have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxne : (x:ℝ) ≠ 0 := ne_of_gt hxpos
  have h1xpos : (0:ℝ) < 1/(x:ℝ) := by positivity
  set S1 : ℝ := ∑ n ∈ Finset.Icc 1 x,
      (ArithmeticFunction.moebius n : ℝ) * ((x/n:ℕ):ℝ) with hS1def
  set S2 : ℝ := ∑ n ∈ Finset.Icc 1 x,
      (ArithmeticFunction.moebius n : ℝ) * ((x%n:ℕ):ℝ) / (n:ℝ) with hS2def
  have hS1 : S1 = 1 := by
    rw [hS1def]; exact sum_moebius_mul_div_eq_one_real x hx
  have hS2 : |S2| ≤ (x:ℝ) := by
    rw [hS2def]
    calc |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ) * ((x%n:ℕ):ℝ) / (n:ℝ)|
        ≤ ∑ n ∈ Finset.Icc 1 x,
            |(ArithmeticFunction.moebius n : ℝ) * ((x%n:ℕ):ℝ) / (n:ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 x, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
          have hmod : ((x%n:ℕ):ℝ) < (n:ℝ) := by
            exact_mod_cast (Nat.mod_lt x (by omega : 0 < n))
          have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
            rw [← Int.cast_abs]
            exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
          rw [abs_div, abs_mul,
            abs_of_nonneg (show (0:ℝ) ≤ ((x%n:ℕ):ℝ) from Nat.cast_nonneg _),
            abs_of_pos hnpos, div_le_one hnpos]
          nlinarith [hmu, hmod, abs_nonneg (ArithmeticFunction.moebius n : ℝ),
            show (0:ℝ) ≤ ((x%n:ℕ):ℝ) from Nat.cast_nonneg _]
      _ = (x:ℝ) := by
          rw [Finset.sum_const]
          simp [Nat.card_Icc]
  have hA : ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ)/(n:ℝ)
      = (1/(x:ℝ)) * (S1 + S2) := by
    rw [hS1def, hS2def]
    rw [Finset.sum_congr rfl (fun n hn => moebius_term_eq x n hx (Finset.mem_Icc.mp hn).1),
        ← Finset.mul_sum, Finset.sum_add_distrib]
  calc |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ)/(n:ℝ)|
      = |(1/(x:ℝ)) * (S1 + S2)| := by rw [hA]
    _ = (1/(x:ℝ)) * |S1 + S2| := by rw [abs_mul, abs_of_pos h1xpos]
    _ ≤ (1/(x:ℝ)) * (1 + (x:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt h1xpos)
        calc |S1 + S2| ≤ |S1| + |S2| := abs_add_le _ _
          _ = 1 + |S2| := by rw [hS1, abs_one]
          _ ≤ 1 + (x:ℝ) := by linarith [hS2]
    _ = 1/(x:ℝ) + 1 := by
        rw [mul_add, mul_one, one_div, inv_mul_cancel₀ hxne]
    _ ≤ 2 := by
        have h1x : (1:ℝ)/(x:ℝ) ≤ 1 := by
          rw [div_le_one hxpos]; exact_mod_cast hx
        linarith

end Commons.NumberTheory.Moebius