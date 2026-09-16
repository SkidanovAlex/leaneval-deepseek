import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.Analysis.ExpLog.sum_inv_Icc_le_log

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.ArithmeticFunction

noncomputable section

/-- `T k x = ∑_{1 ≤ n ≤ x} τ(n)^k / n`. -/
private def T (k x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ k / (n : ℝ)

private lemma T_nonneg (k x : ℕ) : 0 ≤ T k x := by
  unfold T
  exact Finset.sum_nonneg fun n _ => div_nonneg (by positivity) (Nat.cast_nonneg n)

/-- Base case: `T 0 x = ∑_{1 ≤ n ≤ x} 1/n ≤ 1 + log x`. -/
private lemma T_zero_le (x : ℕ) : T 0 x ≤ 1 + Real.log (x : ℝ) := by
  have h : T 0 x = ∑ n ∈ Finset.Icc 1 x, ((n : ℝ))⁻¹ := by
    unfold T
    apply Finset.sum_congr rfl
    intro n _
    rw [pow_zero, one_div]
  rw [h]
  exact Commons.Analysis.ExpLog.sum_inv_Icc_le_log x

/-- `τ(d·e) ≤ τ(d)·τ(e)` propagated to the weighted quotients. -/
private lemma tau_pow_div_mul_le (k d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) :
    ((d * e).divisors.card : ℝ) ^ k / ((d * e : ℕ) : ℝ)
      ≤ (((d.divisors.card : ℝ)) ^ k / (d : ℝ)) *
        (((e.divisors.card : ℝ)) ^ k / (e : ℝ)) := by
  have hdm : (d * e).divisors.card ≤ d.divisors.card * e.divisors.card :=
    Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le d e
  have hdmR : ((d * e).divisors.card : ℝ) ≤ (d.divisors.card : ℝ) * (e.divisors.card : ℝ) := by
    exact_mod_cast hdm
  have hpow : ((d * e).divisors.card : ℝ) ^ k
      ≤ ((d.divisors.card : ℝ)) ^ k * ((e.divisors.card : ℝ)) ^ k := by
    calc ((d * e).divisors.card : ℝ) ^ k
        ≤ (((d.divisors.card : ℝ) * (e.divisors.card : ℝ))) ^ k :=
          pow_le_pow_left₀ (by positivity) hdmR k
      _ = ((d.divisors.card : ℝ)) ^ k * ((e.divisors.card : ℝ)) ^ k := by rw [mul_pow]
  have hde : (0 : ℝ) < ((d * e : ℕ) : ℝ) := by
    have : 0 < d * e := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  calc ((d * e).divisors.card : ℝ) ^ k / ((d * e : ℕ) : ℝ)
      ≤ (((d.divisors.card : ℝ)) ^ k * ((e.divisors.card : ℝ)) ^ k) / ((d * e : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hpow (le_of_lt hde)
    _ = (((d.divisors.card : ℝ)) ^ k / (d : ℝ)) *
          (((e.divisors.card : ℝ)) ^ k / (e : ℝ)) := by
        rw [Nat.cast_mul]
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
        have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
        field_simp

/-- The recursion `T (k+1) x ≤ T k x * T k x`. -/
private lemma T_succ_le (k x : ℕ) : T (k+1) x ≤ T k x * T k x := by
  set f : ℕ → ℕ → ℝ := fun a b => ((a * b).divisors.card : ℝ) ^ k / ((a * b : ℕ) : ℝ)
    with hf
  have hA : T (k+1) x = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d) := by
    unfold T
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hinner : (∑ d ∈ n.divisors, f d (n / d))
        = ((n.divisors.card : ℝ)) * (((n.divisors.card : ℝ)) ^ k / (n : ℝ)) := by
      have hpt : ∀ d ∈ n.divisors, f d (n / d) = ((n.divisors.card : ℝ)) ^ k / (n : ℝ) := by
        intro d hd
        have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
        have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
        simp only [hf]
        rw [hmul]
      rw [Finset.sum_congr rfl hpt, Finset.sum_const]
      simp only [nsmul_eq_mul]
    rw [hinner, pow_succ]
    ring
  have hB : (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d))
      = ∑ n ∈ Finset.range (x + 1), ∑ d ∈ n.divisors, f d (n / d) := by
    have hrange : Finset.range (x + 1) = insert 0 (Finset.Icc 1 x) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hrange, Finset.sum_insert (by simp [Finset.mem_Icc]), Nat.divisors_zero]
    simp
  have hC := Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola f x
  have hD : (∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e)
      ≤ (∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ)) ^ k / (d : ℝ))
        * (∑ e ∈ Finset.Icc 1 x, ((e.divisors.card : ℝ)) ^ k / (e : ℝ)) := by
    calc (∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e)
        ≤ ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 x,
            (((d.divisors.card : ℝ)) ^ k / (d : ℝ)) *
              (((e.divisors.card : ℝ)) ^ k / (e : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          calc ∑ e ∈ Finset.Icc 1 (x / d), f d e
              ≤ ∑ e ∈ Finset.Icc 1 (x / d),
                  (((d.divisors.card : ℝ)) ^ k / (d : ℝ)) *
                    (((e.divisors.card : ℝ)) ^ k / (e : ℝ)) := by
                apply Finset.sum_le_sum
                intro e he
                simp only [hf]
                exact tau_pow_div_mul_le k d e hd1 (Finset.mem_Icc.mp he).1
            _ ≤ ∑ e ∈ Finset.Icc 1 x,
                  (((d.divisors.card : ℝ)) ^ k / (d : ℝ)) *
                    (((e.divisors.card : ℝ)) ^ k / (e : ℝ)) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro e he
                  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
                  have hex : e ≤ x / d := (Finset.mem_Icc.mp he).2
                  exact Finset.mem_Icc.mpr ⟨he1, le_trans hex (Nat.div_le_self x d)⟩
                · intro e _ _
                  positivity
      _ = (∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ)) ^ k / (d : ℝ))
            * (∑ e ∈ Finset.Icc 1 x, ((e.divisors.card : ℝ)) ^ k / (e : ℝ)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.mul_sum]
  calc T (k+1) x
      = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d) := hA
    _ = ∑ n ∈ Finset.range (x + 1), ∑ d ∈ n.divisors, f d (n / d) := hB
    _ = ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e := hC
    _ ≤ (∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ)) ^ k / (d : ℝ))
          * (∑ e ∈ Finset.Icc 1 x, ((e.divisors.card : ℝ)) ^ k / (e : ℝ)) := hD
    _ = T k x * T k x := by unfold T; rfl

/-- `T k x ≤ (1 + log x)^{2^k}`. -/
private lemma T_bound : ∀ k x, T k x ≤ (1 + Real.log (x : ℝ)) ^ (2^k) := by
  intro k
  induction k with
  | zero => intro x; simpa using T_zero_le x
  | succ k ih =>
      intro x
      have h1 : T (k+1) x ≤ T k x * T k x := T_succ_le k x
      have h2 : T k x ≤ (1 + Real.log (x : ℝ)) ^ (2^k) := ih x
      have hnn : 0 ≤ T k x := T_nonneg k x
      have hlog : 0 ≤ 1 + Real.log (x : ℝ) := by
        rcases Nat.eq_zero_or_pos x with hx | hx
        · subst hx; simp
        · have : 0 ≤ Real.log (x : ℝ) :=
            Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
          linarith
      have hsq : T k x * T k x
          ≤ ((1 + Real.log (x : ℝ)) ^ (2^k)) * ((1 + Real.log (x : ℝ)) ^ (2^k)) :=
        mul_le_mul h2 h2 hnn (le_trans hnn h2)
      calc T (k+1) x ≤ T k x * T k x := h1
        _ ≤ ((1 + Real.log (x : ℝ)) ^ (2^k)) * ((1 + Real.log (x : ℝ)) ^ (2^k)) := hsq
        _ = (1 + Real.log (x : ℝ)) ^ (2^(k+1)) := by
              rw [← pow_two, ← pow_mul, pow_succ]

/-- `Σ_{n ≤ y} τ(n)^k / n ≪ (log y)^{2^k}` — the divisor-power weighted sum bound
used in the Friedlander–Iwaniec theorem, with the exponent `2^k` made explicit. -/
theorem sum_tau_pow_div_le_logpow_explicit (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      (∑ n ∈ Finset.Icc 1 y, ((Nat.divisors n).card : ℝ) ^ k / (n : ℝ))
        ≤ C * (Real.log y) ^ ((2 : ℝ) ^ k) := by
  refine ⟨(1 + 1 / Real.log 2) ^ (2 ^ k), ?_, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 0 < 1 + 1 / Real.log 2 := by positivity
    exact pow_pos this (2^k)
  · intro y hy
    have hy1 : 1 < y := by omega
    have hlogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy1)
    have hlog2y : Real.log 2 ≤ Real.log (y : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hy)
    have hle : 1 + Real.log (y : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log (y : ℝ) := by
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hone : (1 : ℝ) ≤ (Real.log 2)⁻¹ * Real.log (y : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hlog2y
          (by positivity : (0 : ℝ) ≤ (Real.log 2)⁻¹)
        rwa [inv_mul_cancel₀ (ne_of_gt hlog2pos)] at h
      rw [one_div]
      nlinarith [hone]
    have hbase : 0 ≤ 1 + Real.log (y : ℝ) := by linarith
    have hT : T k y ≤ (1 + Real.log (y : ℝ)) ^ (2^k) := T_bound k y
    have hpow : (1 + Real.log (y : ℝ)) ^ (2^k)
        ≤ ((1 + 1 / Real.log 2) * Real.log (y : ℝ)) ^ (2^k) :=
      pow_le_pow_left₀ hbase hle (2^k)
    calc (∑ n ∈ Finset.Icc 1 y, ((Nat.divisors n).card : ℝ) ^ k / (n : ℝ))
        = T k y := rfl
      _ ≤ (1 + Real.log (y : ℝ)) ^ (2^k) := hT
      _ ≤ ((1 + 1 / Real.log 2) * Real.log (y : ℝ)) ^ (2^k) := hpow
      _ = (1 + 1 / Real.log 2) ^ (2 ^ k) * (Real.log (y : ℝ)) ^ ((2 : ℝ) ^ k) := by
            rw [mul_pow]
            congr 1
            rw [show ((2 : ℝ) ^ k) = ((2 ^ k : ℕ) : ℝ) by push_cast; ring]
            exact (Real.rpow_natCast (Real.log (y : ℝ)) (2 ^ k)).symm

end

end Commons.NumberTheory.ArithmeticFunction
