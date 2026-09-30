import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog
import Submission.Work.BMF.PIC_theta_eq_sum_Ioc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Primes in short intervals, quantitatively

Proof of `Work.BMF.prime_interval_count`.

Route: from the Prime Number Theorem with power-of-`log` error (the workspace module
`Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog`) one gets
`θ(2x) - θ(x) ≥ (11/12) x` for `x` large, and `θ(2x) - θ(x) = Σ_{x<p≤2x} log p`,
while `Σ_{x<p≤2x} log p ≤ (π(2x)-π(x)) · log(2x)`, so `π(2x) - π(x) ≳ x / log(2x)`;
the threshold `C k³ log k` is chosen so that `x / log(2x) ≥ k³/2`.
-/

namespace Work.BMF

open Finset

/-- For `k ≥ 2`, `Real.log k ≥ 1/2`. -/
lemma BMF_log_nat_ge_half {k : ℕ} (hk : 2 ≤ k) : (1 / 2 : ℝ) ≤ Real.log k := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk2
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  linarith

/-- `8 ≤ k³` for `k ≥ 2`. -/
lemma BMF_eight_le_cube {k : ℕ} (hk : 2 ≤ k) : (8 : ℝ) ≤ (k : ℝ) ^ 3 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk2 3
  norm_num at h
  exact h

/-- The sum of `log p` over the primes in `(n, 2n]` is at most `#(primes) * log (2n)`. -/
lemma BMF_sum_log_le_card (n : ℕ) :
    (∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ)) ≤
      (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) * Real.log (2 * (n : ℝ)) := by
  have hterm : ∀ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime,
      Real.log (p : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hp'⟩ := hp
    have hp2 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp'.pos
    have h3 : (p : ℝ) ≤ 2 * (n : ℝ) := by
      calc (p : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast h2
        _ = 2 * (n : ℝ) := by push_cast; ring
    exact Real.log_le_log hp2 h3
  calc (∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ))
      ≤ ∑ _p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log (2 * (n : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) * Real.log (2 * (n : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- PNT with a power-of-`log` error implies: for all large `x`, `θ(2x) - θ(x) ≥ (11/12) x`. -/
lemma BMF_theta_increment_lower :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 6 ≤ Real.log x →
      (11 / 12) * x ≤ Chebyshev.theta (2 * x) - Chebyshev.theta x := by
  obtain ⟨x₀, hx₀⟩ :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog 2 (by norm_num)
  refine ⟨max x₀ (Real.exp 6), ?_⟩
  intro x hx hlog
  have hx₀' : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 6 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 6) hxe
  have h2x₀ : x₀ ≤ 2 * x := by linarith
  have h1 : |Chebyshev.theta x - x| ≤ x / (Real.log x) ^ 2 := by
    simpa only [Real.rpow_two] using hx₀ x hx₀'
  have h2 : |Chebyshev.theta (2 * x) - 2 * x| ≤ 2 * x / (Real.log (2 * x)) ^ 2 := by
    simpa only [Real.rpow_two] using hx₀ (2 * x) h2x₀
  have hlog2x : (6 : ℝ) ≤ Real.log (2 * x) := by
    have h : Real.log x ≤ Real.log (2 * x) := Real.log_le_log hxpos (by linarith)
    linarith
  have hsq : (36 : ℝ) ≤ (Real.log x) ^ 2 := by nlinarith
  have hsq2 : (36 : ℝ) ≤ (Real.log (2 * x)) ^ 2 := by nlinarith
  have e1 : x / (Real.log x) ^ 2 ≤ x / 36 :=
    div_le_div_of_nonneg_left hxpos.le (by norm_num) hsq
  have e2 : 2 * x / (Real.log (2 * x)) ^ 2 ≤ 2 * x / 36 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hsq2
  have t1 : Chebyshev.theta x ≤ x + x / (Real.log x) ^ 2 := by
    have := (abs_le.mp h1).2; linarith
  have t2 : 2 * x - 2 * x / (Real.log (2 * x)) ^ 2 ≤ Chebyshev.theta (2 * x) := by
    have := (abs_le.mp h2).1; linarith
  linarith

/-- Numerical core: for `x ≥ 1000 * k³ * log k` and `k ≥ 2`, `k³ · log(2x) ≤ (11/6) x`. -/
lemma BMF_key_log_ineq (k : ℕ) (hk : 2 ≤ k) (x : ℝ)
    (hx : 1000 * (k : ℝ) ^ 3 * Real.log k ≤ x) :
    (k : ℝ) ^ 3 * Real.log (2 * x) ≤ (11 / 6) * x := by
  have hKpos : 0 < (k : ℝ) ^ 3 := by positivity
  have hLhalf : (1 / 2 : ℝ) ≤ Real.log k := BMF_log_nat_ge_half hk
  have hLpos : 0 < Real.log k := by linarith
  set t : ℝ := 1000 * (k : ℝ) ^ 3 * Real.log k with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hxt : t ≤ x := by rw [ht]; exact hx
  have hxpos : 0 < x := lt_of_lt_of_le htpos hxt
  -- step (I): `f x ≥ f t` where `f y = (11/6) y - k³ log (2y)`
  have hstep : (11 / 6) * t - (k : ℝ) ^ 3 * Real.log (2 * t) ≤
      (11 / 6) * x - (k : ℝ) ^ 3 * Real.log (2 * x) := by
    have hlogsplit : Real.log (2 * x) = Real.log (2 * t) + Real.log (x / t) := by
      have h : 2 * t * (x / t) = 2 * x := by field_simp
      rw [← h, Real.log_mul (by positivity) (by positivity)]
    have hKt : (k : ℝ) ^ 3 / t ≤ 11 / 6 := by
      have htpos' : 0 < 1000 * (k : ℝ) ^ 3 * Real.log k := by positivity
      rw [ht, div_le_iff₀ htpos']
      nlinarith [hKpos, hLhalf]
    have hxsub : x / t - 1 = (x - t) / t := by
      rw [sub_div, div_self (ne_of_gt htpos)]
    have hlogle : Real.log (x / t) ≤ x / t - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h1 : (k : ℝ) ^ 3 * Real.log (x / t) ≤ (k : ℝ) ^ 3 * (x / t - 1) :=
      mul_le_mul_of_nonneg_left hlogle hKpos.le
    have h2 : (k : ℝ) ^ 3 * (x / t - 1) ≤ (11 / 6) * (x - t) := by
      rw [hxsub, mul_div_assoc', div_le_iff₀ htpos]
      have hK3 : (k : ℝ) ^ 3 ≤ (11 / 6) * t := (div_le_iff₀ htpos).mp hKt
      have hxt0 : 0 ≤ x - t := sub_nonneg.mpr hxt
      nlinarith [hK3, hxt0]
    have hle : (k : ℝ) ^ 3 * Real.log (x / t) ≤ (11 / 6) * (x - t) := by linarith
    rw [hlogsplit]
    nlinarith [hle]
  -- step (II): `f t ≥ 0`
  have hft : 0 ≤ (11 / 6) * t - (k : ℝ) ^ 3 * Real.log (2 * t) := by
    have h2t : 2 * t = 2000 * (k : ℝ) ^ 3 * Real.log k := by rw [ht]; ring
    have hlog2t : Real.log (2 * t) =
        Real.log 2000 + 3 * Real.log k + Real.log (Real.log k) := by
      rw [h2t, Real.log_mul (by positivity) (ne_of_gt hLpos),
        Real.log_mul (by norm_num) (ne_of_gt hKpos), Real.log_pow]
      ring
    have hLlog : Real.log (Real.log k) ≤ Real.log k - 1 := Real.log_le_sub_one_of_pos hLpos
    have hlog2000 : Real.log 2000 ≤ 10 := by
      have h1 : Real.log 2000 ≤ Real.log ((2 : ℝ) ^ 11) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at h1
      norm_num at h1
      have h2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
      linarith
    have hle : Real.log (2 * t) ≤ 9 + 4 * Real.log k := by
      rw [hlog2t]; linarith
    have hneed : Real.log (2 * t) ≤ (11 / 6) * (1000 * Real.log k) := by
      nlinarith [hle, hLhalf]
    have hmain : (k : ℝ) ^ 3 * Real.log (2 * t) ≤
        (k : ℝ) ^ 3 * ((11 / 6) * (1000 * Real.log k)) :=
      mul_le_mul_of_nonneg_left hneed hKpos.le
    rw [ht]
    nlinarith [hmain]
  have hfx : 0 ≤ (11 / 6) * x - (k : ℝ) ^ 3 * Real.log (2 * x) := le_trans hft hstep
  linarith

/-- The main counting step: if `x = n ≥ 1000 k³ log k` and `k ≥ 2`, the interval `(n, 2n]`
contains at least `k³/2` primes. -/
lemma BMF_core (X a : ℝ)
    (hX : ∀ y : ℝ, X ≤ y → 6 ≤ Real.log y →
      (11 / 12) * y ≤ Chebyshev.theta (2 * y) - Chebyshev.theta y)
    (ha1000 : 1000 ≤ a) (haX : X ≤ a)
    (k n : ℕ) (hk : 2 ≤ k)
    (hn : a * (k : ℝ) ^ 3 * Real.log k ≤ (n : ℝ)) :
    (k : ℝ) ^ 3 ≤ 2 * (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) := by
  have hKpos : 0 < (k : ℝ) ^ 3 := by positivity
  have hKlL : (4 : ℝ) ≤ (k : ℝ) ^ 3 * Real.log k := by
    have h8 := BMF_eight_le_cube hk
    have hLhalf : (1 / 2 : ℝ) ≤ Real.log k := BMF_log_nat_ge_half hk
    have h := mul_le_mul h8 hLhalf (by norm_num) (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 3)
    norm_num at h
    exact h
  have hn' : a * ((k : ℝ) ^ 3 * Real.log k) ≤ (n : ℝ) := by nlinarith only [hn]
  have hxX : X ≤ (n : ℝ) := by
    have h1 : a ≤ a * ((k : ℝ) ^ 3 * Real.log k) := by
      have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 3 * Real.log k := by linarith
      nlinarith [h2, ha1000]
    linarith [haX, hn']
  have hxpos : 0 < (n : ℝ) := by nlinarith [hn', ha1000, hKlL]
  have hlog6 : 6 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hxpos]
    have hexp6 : Real.exp 6 ≤ (4000 : ℝ) := by
      have h : Real.exp 6 = (Real.exp 1) ^ 6 := by
        simpa using Real.exp_nat_mul (1 : ℝ) 6
      rw [h]
      have h4 : (Real.exp 1) ^ 6 ≤ (3 : ℝ) ^ 6 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 6
      have h729 : (3 : ℝ) ^ 6 = 729 := by norm_num
      linarith
    nlinarith [hn', ha1000, hKlL, hexp6]
  have htheta : (11 / 12) * (n : ℝ) ≤
      Chebyshev.theta (2 * (n : ℝ)) - Chebyshev.theta (n : ℝ) := hX (n : ℝ) hxX hlog6
  have hsum : (11 / 12) * (n : ℝ) ≤
      ∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [← PIC_theta_eq_sum_Ioc n]
    exact htheta
  have hcard : (∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ)) ≤
      (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) * Real.log (2 * (n : ℝ)) :=
    BMF_sum_log_le_card n
  have h1 : (11 / 12) * (n : ℝ) ≤
      (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) * Real.log (2 * (n : ℝ)) :=
    le_trans hsum hcard
  have h2 : (11 / 6) * (n : ℝ) ≤
      (2 * (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ)) * Real.log (2 * (n : ℝ)) := by
    nlinarith [h1]
  have hkey : (k : ℝ) ^ 3 * Real.log (2 * (n : ℝ)) ≤ (11 / 6) * (n : ℝ) :=
    BMF_key_log_ineq k hk (n : ℝ) (by nlinarith [hn', ha1000, hKlL])
  have hlog2xpos : 0 < Real.log (2 * (n : ℝ)) := by
    have h : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hxpos (by linarith)
    linarith
  have h4 : (k : ℝ) ^ 3 * Real.log (2 * (n : ℝ)) ≤
      (2 * (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ)) * Real.log (2 * (n : ℝ)) :=
    le_trans hkey h2
  exact le_of_mul_le_mul_right h4 hlog2xpos

/-- **Primes in short intervals, quantitatively.** There is an absolute constant `C` such that for every `k ≥ 2` and every `M ≥ 1` the interval `(M, max (2*M) ⌈C·k³·log k⌉]` contains at least `k³/2` primes. -/
theorem prime_interval_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (k M : ℕ), 2 ≤ k → 1 ≤ M →
      k^3 ≤ 2 * ((Finset.Ioc M (max (2*M) ⌈C * (k:ℝ)^3 * Real.log k⌉₊)).filter Nat.Prime).card := by
  obtain ⟨X, hX⟩ := BMF_theta_increment_lower
  refine ⟨2 * max 1000 (X + 10) + 1, ?_, ?_⟩
  · have : (0 : ℝ) < max 1000 (X + 10) :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    linarith
  · intro k M hk hM
    set a : ℝ := max 1000 (X + 10) with hadef
    have ha1000 : 1000 ≤ a := le_max_left _ _
    have haX : X ≤ a := by
      have h1 : X ≤ X + 10 := by linarith
      have h2 : X + 10 ≤ a := le_max_right _ _
      linarith
    have hKlL : (4 : ℝ) ≤ (k : ℝ) ^ 3 * Real.log k := by
      have h8 := BMF_eight_le_cube hk
      have hLhalf : (1 / 2 : ℝ) ≤ Real.log k := BMF_log_nat_ge_half hk
      have h := mul_le_mul h8 hLhalf (by norm_num) (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 3)
      norm_num at h
      exact h
    set N : ℕ := ⌈(2 * a + 1) * (k : ℝ) ^ 3 * Real.log k⌉₊ with hNdef
    have hNge : (2 * a + 1) * (k : ℝ) ^ 3 * Real.log k ≤ (N : ℝ) := Nat.le_ceil _
    by_cases hNM : N ≤ 2 * M
    · have hmax : max (2 * M) N = 2 * M := max_eq_left hNM
      rw [hmax]
      have hMge : a * (k : ℝ) ^ 3 * Real.log k ≤ (M : ℝ) := by
        have h1 : (N : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hNM
        nlinarith [hNge, h1, hKlL]
      have hc := BMF_core X a hX ha1000 haX k M hk hMge
      exact_mod_cast hc
    · have hNMg : 2 * M < N := Nat.lt_of_not_le hNM
      have hNM' : 2 * M ≤ N := le_of_lt hNMg
      have hmax : max (2 * M) N = N := max_eq_right hNM'
      rw [hmax]
      set T : ℕ := N / 2 with hTdef
      have hMT : M ≤ T := by
        rw [hTdef]
        omega
      have h2T : 2 * T ≤ N := by rw [hTdef]; omega
      have hsubset : (Finset.Ioc T (2 * T)).filter Nat.Prime ⊆
          (Finset.Ioc M N).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
        exact ⟨⟨by omega, by omega⟩, hp.2⟩
      have hTge : a * (k : ℝ) ^ 3 * Real.log k ≤ (T : ℝ) := by
        have h1 : (N : ℝ) ≤ 2 * (T : ℝ) + 1 := by
          have h : N ≤ 2 * T + 1 := by rw [hTdef]; omega
          exact_mod_cast h
        nlinarith [hNge, h1, hKlL]
      have hc := BMF_core X a hX ha1000 haX k T hk hTge
      have hle : (((Finset.Ioc T (2 * T)).filter Nat.Prime).card : ℝ) ≤
          (((Finset.Ioc M N).filter Nat.Prime).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hc' : (k : ℝ) ^ 3 ≤ 2 * (((Finset.Ioc M N).filter Nat.Prime).card : ℝ) := by
        nlinarith [hc, hle]
      exact_mod_cast hc'

end Work.BMF
