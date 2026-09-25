import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Goldbach

/-- If the Chebyshev `θ` function strictly increases from `a` to `b`, then the
interval `(a, b]` contains a prime.

Indeed `θ` is the sum of `log p` over primes `p ≤ x`, and `θ x = θ ⌊x⌋₊`; since
all the summands are nonnegative, `θ b > θ a` forces a prime contribution in
the range `(⌊a⌋₊, ⌊b⌋₊]`, i.e. a prime `p` with `a < p ≤ b`. -/
theorem exists_prime_of_theta_lt {a b : ℝ} (h : Chebyshev.theta a < Chebyshev.theta b) :
    ∃ p : ℕ, Nat.Prime p ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  by_contra hno
  rw [Chebyshev.theta_eq_theta_coe_floor a, Chebyshev.theta_eq_theta_coe_floor b] at h
  have hNM : ⌊a⌋₊ < ⌊b⌋₊ := by
    by_contra hle
    push_neg at hle
    exact absurd h (not_lt.mpr (Chebyshev.theta_mono (by exact_mod_cast hle)))
  have hb0 : 0 ≤ b := by
    by_contra hbneg
    push_neg at hbneg
    have hz : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have haθ : 0 ≤ Chebyshev.theta (((⌊a⌋₊ : ℕ)) : ℝ) := Chebyshev.theta_nonneg _
    have hbθ : 0 < Chebyshev.theta (((⌊b⌋₊ : ℕ)) : ℝ) := lt_of_le_of_lt haθ h
    rw [hz] at hbθ
    simp at hbθ
  have hset : (Finset.Ioc 0 ⌊b⌋₊).filter Nat.Prime
      = (Finset.Ioc 0 ⌊a⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp0, hpM⟩, hpp⟩
      refine ⟨⟨hp0, ?_⟩, hpp⟩
      by_contra hgt
      push_neg at hgt
      have hpa : a < (p : ℝ) := by
        have h2 : a < (((⌊a⌋₊ : ℕ)) : ℝ) + 1 := Nat.lt_floor_add_one a
        have h3 : (((⌊a⌋₊ : ℕ)) : ℝ) + 1 ≤ (p : ℝ) := by
          have : ⌊a⌋₊ + 1 ≤ p := by omega
          exact_mod_cast this
        linarith
      have hpb : (p : ℝ) ≤ b := by
        have h1 : (((⌊b⌋₊ : ℕ)) : ℝ) ≤ b := Nat.floor_le hb0
        have h2 : (p : ℝ) ≤ ((⌊b⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpM
        linarith
      exact hno ⟨p, hpp, hpa, hpb⟩
    · rintro ⟨⟨hp0, hpN⟩, hpp⟩
      exact ⟨⟨hp0, by omega⟩, hpp⟩
  have hthetaeq : Chebyshev.theta (((⌊b⌋₊ : ℕ)) : ℝ)
      = Chebyshev.theta (((⌊a⌋₊ : ℕ)) : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
    rw [hset]
  linarith

/-- The elementary window estimate behind the short-interval argument: for
`x ≥ 1` with `log x ≥ 4` and `A > 0`, the "gain" of the interval
`[x, x + x/(log x)^A]` over the two error terms of `θ` at level `A + 1` is
positive. -/
theorem short_interval_gain_pos (A : ℝ) (hA : 0 < A) {x : ℝ} (hx : 1 ≤ x)
    (hL : 4 ≤ Real.log x) :
    0 < x / (Real.log x) ^ A
      - (x + x / (Real.log x) ^ A) / (Real.log (x + x / (Real.log x) ^ A)) ^ (A + 1)
      - x / (Real.log x) ^ (A + 1) := by
  have hx0 : 0 < x := by linarith
  have hLpos : 0 < Real.log x := by linarith
  have hLpow_pos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hLpos A
  have h1Lpow : 1 < (Real.log x) ^ A := Real.one_lt_rpow (by linarith) hA
  have hden_pos : 0 < (Real.log x) ^ (A + 1) := Real.rpow_pos_of_pos hLpos (A + 1)
  have hLh_ge : Real.log x ≤ Real.log (x + x / (Real.log x) ^ A) :=
    Real.log_le_log hx0 (by
      have : 0 < x / (Real.log x) ^ A := div_pos hx0 hLpow_pos
      linarith)
  have hpow_le : (Real.log x) ^ (A + 1)
      ≤ (Real.log (x + x / (Real.log x) ^ A)) ^ (A + 1) :=
    Real.rpow_le_rpow (le_of_lt hLpos) hLh_ge (by linarith)
  have hnum_nn : 0 ≤ x + x / (Real.log x) ^ A := by
    have : 0 < x / (Real.log x) ^ A := div_pos hx0 hLpow_pos
    linarith
  have hle1 : (x + x / (Real.log x) ^ A) / (Real.log (x + x / (Real.log x) ^ A)) ^ (A + 1)
      ≤ (x + x / (Real.log x) ^ A) / (Real.log x) ^ (A + 1) :=
    div_le_div_of_nonneg_left hnum_nn hden_pos hpow_le
  have hle_x : x / (Real.log x) ^ A ≤ x := by
    rw [div_le_iff₀ hLpow_pos]
    calc x ≤ x * 1 := (mul_one x).ge
      _ ≤ x * (Real.log x) ^ A := mul_le_mul_of_nonneg_left (le_of_lt h1Lpow) (le_of_lt hx0)
  have hle2 : (x + x / (Real.log x) ^ A) / (Real.log x) ^ (A + 1)
      ≤ 2 * x / (Real.log x) ^ (A + 1) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hden_pos)
    linarith
  have hLpow_add : (Real.log x) ^ (A + 1) = (Real.log x) ^ A * Real.log x := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  have hkey : 3 * x / (Real.log x) ^ (A + 1) < x / (Real.log x) ^ A := by
    rw [hLpow_add, div_lt_iff₀ (by positivity)]
    rw [← mul_assoc, div_mul_cancel₀ x (ne_of_gt hLpow_pos)]
    nlinarith [hx0, hL]
  have hB : (x + x / (Real.log x) ^ A) / (Real.log (x + x / (Real.log x) ^ A)) ^ (A + 1)
      ≤ 2 * x / (Real.log x) ^ (A + 1) := le_trans hle1 hle2
  have h3eq : 2 * x / (Real.log x) ^ (A + 1) + x / (Real.log x) ^ (A + 1)
      = 3 * x / (Real.log x) ^ (A + 1) := by ring
  have hfinal : 0 < x / (Real.log x) ^ A - 2 * x / (Real.log x) ^ (A + 1)
      - x / (Real.log x) ^ (A + 1) := by
    rw [sub_sub, h3eq]
    exact sub_pos.mpr hkey
  linarith

/-- **Primes in short intervals.**

For every `A > 0` there is `x₀` such that for all `x ≥ x₀` the interval
`[x, x + x/(log x)^A]` contains a prime.  This is the short-interval input of
the circle-method proof of the weak Goldbach theorem.

The proof is a soft consequence of the prime number theorem with a
power-of-logarithm error term at level `A + 1`
(`Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog`): over a window
`[x, x + h]` of length `h = x/(log x)^A` the `θ`-increment exceeds
`h` minus the two error terms, and for `x` large this is positive, so `θ`
strictly increases and hence (by `exists_prime_of_theta_lt`) a prime lies in the
window. -/
theorem prime_in_short_interval (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x ≤ (p : ℝ) ∧ (p : ℝ) ≤ x + x / (Real.log x) ^ A := by
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  obtain ⟨x₁, hx₁⟩ :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog (A + 1) hA1
  refine ⟨max x₁ (max 4 (Real.exp 4)), ?_⟩
  intro x hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : 4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxexp : Real.exp 4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hL4 : 4 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 4) hxexp
    rwa [Real.log_exp] at h
  have hLpos : 0 < Real.log x := by linarith
  have hLpow_pos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hLpos A
  set h : ℝ := x / (Real.log x) ^ A with hh
  have hhpos : 0 < h := by rw [hh]; exact div_pos hx0 hLpow_pos
  have hxh₁ : x₁ ≤ x + h := by linarith
  have hbx : |Chebyshev.theta x - x| ≤ x / (Real.log x) ^ (A + 1) := hx₁ x hxx₁
  have hbxh : |Chebyshev.theta (x + h) - (x + h)|
      ≤ (x + h) / (Real.log (x + h)) ^ (A + 1) := hx₁ (x + h) hxh₁
  have hgain : Chebyshev.theta x < Chebyshev.theta (x + h) := by
    have he1 : (x + h) - (x + h) / (Real.log (x + h)) ^ (A + 1) ≤ Chebyshev.theta (x + h) := by
      have := neg_abs_le (Chebyshev.theta (x + h) - (x + h))
      linarith
    have he2 : Chebyshev.theta x ≤ x + x / (Real.log x) ^ (A + 1) := by
      have := le_abs_self (Chebyshev.theta x - x)
      linarith
    have hwindow : 0 < x / (Real.log x) ^ A
        - (x + x / (Real.log x) ^ A) / (Real.log (x + x / (Real.log x) ^ A)) ^ (A + 1)
        - x / (Real.log x) ^ (A + 1) := short_interval_gain_pos A hA (by linarith) hL4
    rw [← hh] at hwindow
    linarith
  obtain ⟨p, hpp, hxp, hpb⟩ := exists_prime_of_theta_lt hgain
  exact ⟨p, hpp, le_of_lt hxp, by rw [hh] at hpb; exact hpb⟩

end Commons.NumberTheory.Goldbach
