import Mathlib
import Submission.Commons.NumberTheory.Mertens.first_mertens_bounded
import Submission.Commons.NumberTheory.Mertens.second_mertens_converges
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.chi4_log_recip_sum_bounded
import Submission.Commons.NumberTheory.FriedlanderIwaniec.chi4_recip_sum_tail
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_div_log_abel_identity
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Filter Finset

namespace Commons.NumberTheory.FriedlanderIwaniec

noncomputable section

/-! ### The character `χ₄` on `ℕ`, real-valued -/

/-- `χ₄` evaluated at a natural number, as a real number. -/
private def c4 (n : ℕ) : ℝ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

private lemma c4_one_mod {n : ℕ} (h : n % 4 = 1) : c4 n = 1 := by
  unfold c4; rw [ZMod.χ₄_nat_one_mod_four h]; norm_num

private lemma c4_three_mod {n : ℕ} (h : n % 4 = 3) : c4 n = -1 := by
  unfold c4; rw [ZMod.χ₄_nat_three_mod_four h]; norm_num

private lemma c4_zero_mod {n : ℕ} (h : n % 2 = 0) : c4 n = 0 := by
  unfold c4; rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos h]; norm_num

private lemma abs_c4_le_one (n : ℕ) : |c4 n| ≤ 1 := by
  have hc : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hc with h | h | h | h
  · have : n % 2 = 0 := by omega
    rw [c4_zero_mod this]; norm_num
  · rw [c4_one_mod h]; norm_num
  · have : n % 2 = 0 := by omega
    rw [c4_zero_mod this]; norm_num
  · rw [c4_three_mod h]; norm_num

private lemma c4_mul (m n : ℕ) : c4 (m * n) = c4 m * c4 n := by
  simp only [c4, Nat.cast_mul, map_mul, Int.cast_mul]

/-! ### The χ₄-twisted harmonic sum and its limit -/

/-- The χ₄-twisted harmonic sum `Σ_{n ≤ N} χ₄(n)/n`. -/
private def S (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), c4 n / n

private lemma S_eq (N : ℕ) :
    S N = ∑ n ∈ range (N + 1), (((ZMod.χ₄ (n : ZMod 4) : ℤ)) : ℝ) / n := rfl

/-- The limit `c₀ = Σ χ₄(n)/n` of the χ₄-twisted harmonic sum, with its polynomial tail bound. -/
private lemma S_tail : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, |S N - c| ≤ 4 / ((N : ℝ) + 1) := by
  obtain ⟨c, hc, h⟩ := chi4_recip_sum_tail
  refine ⟨c, hc, fun N => ?_⟩
  rw [S_eq]
  have := h N
  simpa only [Nat.cast_add, Nat.cast_one] using this

private lemma S_eq_Icc (M : ℕ) : S M = ∑ n ∈ Icc 1 M, c4 n / n := by
  rw [S]
  rw [show range (M+1) = insert 0 (Icc 1 M) from by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega]
  rw [Finset.sum_insert (by simp)]
  norm_num

/-! ### The primes-below set -/

private lemma primesLE_eq (n : ℕ) : n.primesLE = (range (n + 1)).filter Nat.Prime := by
  ext p
  simp [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_range]

/-! ### Chebyshev's ψ bound -/

private lemma psi_bound (N : ℕ) : (∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ))
    ≤ Real.log 3 * ((N : ℝ) + 1) := by
  have h : (∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ))
      = Chebyshev.psi ((N : ℕ) : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    rw [show Finset.range (N+1) = Finset.Icc 0 N from by
      ext n; simp only [Finset.mem_range, Finset.mem_Icc]; omega]
  rw [h]
  have h2 := Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real (N : ℝ) (Nat.cast_nonneg N)
  have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  nlinarith

/-! ### The log-divisor identity -/

/-- The key identity:
`Σ_{n ≤ N} χ₄(n) log n / n = Σ_{d ≤ N} (χ₄ d Λ d / d) (Σ_{e ≤ N/d} χ₄ e / e)`. -/
private lemma log_div_identity (N : ℕ) :
    (∑ n ∈ range (N + 1), c4 n * Real.log n / n)
      = ∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
          * (∑ e ∈ Icc 1 (N / d), c4 e / e) := by
  have h1 : (∑ n ∈ range (N + 1), c4 n * Real.log n / n)
      = ∑ n ∈ range (N + 1), ∑ d ∈ n.divisors,
          (c4 n / (n : ℝ)) * (ArithmeticFunction.vonMangoldt d : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
    ring
  have h2 : (∑ n ∈ range (N + 1), ∑ d ∈ n.divisors,
        (c4 n / (n : ℝ)) * (ArithmeticFunction.vonMangoldt d : ℝ))
      = ∑ n ∈ range (N + 1), ∑ d ∈ n.divisors,
          (c4 (d * (n / d)) / ((d : ℝ) * ((n / d : ℕ) : ℝ)))
            * (ArithmeticFunction.vonMangoldt d : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    have hreal : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, hmul]
    rw [hmul, hreal]
  rw [h1, h2, Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola
      (fun d e => (c4 (d * e) / ((d : ℝ) * (e : ℝ)))
        * (ArithmeticFunction.vonMangoldt d : ℝ)) N]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    positivity
  have he0 : (e : ℝ) ≠ 0 := by
    have : 1 ≤ e := (Finset.mem_Icc.mp he).1
    positivity
  rw [c4_mul]
  field_simp

/-! ### `Σ χ₄(n)Λ(n)/n` is bounded -/

private lemma W_eq (N : ℕ) :
    (∑ n ∈ range (N + 1), c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n)
      = ∑ n ∈ Icc 1 N, c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
  rw [show range (N+1) = insert 0 (Icc 1 N) from by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega]
  rw [Finset.sum_insert (by simp)]
  simp

private lemma W_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      |(∑ n ∈ range (N + 1), c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n)| ≤ C := by
  obtain ⟨c₀, hc₀pos, hS⟩ := S_tail
  obtain ⟨C₁, hC₁pos, hlog⟩ := chi4_log_recip_sum_bounded
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine ⟨(C₁ + 8 * Real.log 3) / c₀, by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
    positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- rewrite the identity with `S` on the right
  have hid : (∑ n ∈ range (N + 1), c4 n * Real.log n / n)
      = ∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d) * S (N / d) := by
    rw [log_div_identity N]
    apply Finset.sum_congr rfl
    intro d _
    rw [S_eq_Icc]
  -- decompose
  have hsplit : (∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d) * S (N / d))
      = c₀ * (∑ d ∈ Icc 1 N, c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
        + ∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
            * (S (N / d) - c₀) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  -- bound the error term
  have herr : |∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
        * (S (N / d) - c₀)| ≤ 8 * Real.log 3 := by
    have hterm : ∀ d ∈ Icc 1 N,
        |(c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d) * (S (N / d) - c₀)|
          ≤ 4 * (ArithmeticFunction.vonMangoldt d : ℝ) / (N : ℝ) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have htail : |S (N / d) - c₀| ≤ 4 * (d : ℝ) / (N : ℝ) := by
        have h1 := hS (N / d)
        have h2 : 4 / (((N / d : ℕ) : ℝ) + 1) ≤ 4 * (d : ℝ) / (N : ℝ) := by
          have hlt : (N : ℝ) ≤ (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
            have hnat : N ≤ d * (N / d + 1) := by
              have h := Nat.div_add_mod N d
              have hmod : N % d ≤ d := le_of_lt (Nat.mod_lt N (by omega))
              nlinarith
            exact_mod_cast hnat
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hlt]
        linarith
      have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt d : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      calc |(c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d) * (S (N / d) - c₀)|
          = |c4 d| * ((ArithmeticFunction.vonMangoldt d : ℝ) / (d : ℝ))
              * |S (N / d) - c₀| := by
            rw [abs_mul, abs_div, abs_of_pos hd0, abs_mul, abs_of_nonneg hΛ]
            ring
        _ ≤ 1 * ((ArithmeticFunction.vonMangoldt d : ℝ) / (d : ℝ)) * (4 * (d : ℝ) / (N : ℝ)) := by
            apply mul_le_mul
            · exact mul_le_mul (abs_c4_le_one d) (le_refl _) (div_nonneg hΛ (le_of_lt hd0))
                (by norm_num)
            · exact htail
            · exact abs_nonneg _
            · positivity
        _ = 4 * (ArithmeticFunction.vonMangoldt d : ℝ) / (N : ℝ) := by
            field_simp
    calc |∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
            * (S (N / d) - c₀)|
        ≤ ∑ d ∈ Icc 1 N, 4 * (ArithmeticFunction.vonMangoldt d : ℝ) / (N : ℝ) :=
          le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
      _ = (4 / (N : ℝ)) * ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
      _ ≤ (4 / (N : ℝ)) * (Real.log 3 * ((N : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hsum : (∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d : ℝ))
              ≤ (∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) := by
            rw [show range (N+1) = insert 0 (Icc 1 N) from by
              ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega]
            rw [Finset.sum_insert (by simp)]
            have := ArithmeticFunction.vonMangoldt_nonneg (n := 0)
            linarith
          linarith [psi_bound N, hsum]
      _ ≤ 8 * Real.log 3 := by
          have h2 : ((N : ℝ) + 1) / (N : ℝ) ≤ 2 := by
            rw [div_le_iff₀ (by linarith)]
            linarith
          have h3 : (4 / (N : ℝ)) * (Real.log 3 * ((N : ℝ) + 1))
              = 4 * Real.log 3 * (((N : ℝ) + 1) / (N : ℝ)) := by ring
          rw [h3]
          nlinarith [hlog3, h2]
  -- conclude
  have hkey : c₀ * |∑ d ∈ Icc 1 N, c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d|
      ≤ |(∑ n ∈ range (N + 1), c4 n * Real.log n / n)| + 8 * Real.log 3 := by
    have hdecomp : (∑ n ∈ range (N + 1), c4 n * Real.log n / n)
        = c₀ * (∑ d ∈ Icc 1 N, c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
          + ∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
            * (S (N / d) - c₀) := hid.trans hsplit
    have : c₀ * (∑ d ∈ Icc 1 N, c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
        = (∑ n ∈ range (N + 1), c4 n * Real.log n / n)
          - ∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
            * (S (N / d) - c₀) := by
      linarith [hdecomp]
    calc c₀ * |∑ d ∈ Icc 1 N, c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d|
        = |c₀ * (∑ d ∈ Icc 1 N, c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)| := by
          rw [abs_mul, abs_of_pos hc₀pos]
      _ = |(∑ n ∈ range (N + 1), c4 n * Real.log n / n)
            - ∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
              * (S (N / d) - c₀)| := by rw [this]
      _ ≤ _ := by
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
        · linarith [le_abs_self (∑ n ∈ range (N + 1), c4 n * Real.log n / n),
            neg_abs_le (∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
              * (S (N / d) - c₀))]
        · linarith [le_abs_self (∑ d ∈ Icc 1 N, (c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d)
              * (S (N / d) - c₀)),
            neg_abs_le (∑ n ∈ range (N + 1), c4 n * Real.log n / n)]
  have hsum_abs : |∑ d ∈ Icc 1 N, c4 d * (ArithmeticFunction.vonMangoldt d : ℝ) / d|
      ≤ (C₁ + 8 * Real.log 3) / c₀ := by
    have hlogc : |∑ n ∈ range (N + 1), c4 n * Real.log n / n| ≤ C₁ := by
      simpa only [c4] using hlog N
    rw [le_div_iff₀ hc₀pos, mul_comm]
    linarith [hkey, hlogc]
  rw [W_eq N]
  exact hsum_abs

/-! ### The elementary first Mertens theorem for `Λ` -/

private lemma V_eq_Icc (N : ℕ) :
    (∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n)
      = ∑ n ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
  rw [show range (N+1) = insert 0 (Icc 1 N) from by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega]
  rw [Finset.sum_insert (by simp)]
  simp

private lemma sum_log_hyperbola (N : ℕ) :
    (∑ n ∈ range (N + 1), Real.log (n : ℝ))
      = ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d : ℝ) * ((N / d : ℕ) : ℝ) := by
  have h1 : (∑ n ∈ range (N + 1), Real.log (n : ℝ))
      = ∑ n ∈ range (N + 1), ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [ArithmeticFunction.vonMangoldt_sum]
  rw [h1, Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola
      (fun d _ => (ArithmeticFunction.vonMangoldt d : ℝ)) N]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  rw [Nat.add_sub_cancel]
  ring

private lemma sum_log_range_shift (N : ℕ) :
    (∑ i ∈ range N, Real.log ((i : ℝ) + 1)) = ∑ n ∈ range (N + 1), Real.log (n : ℝ) := by
  rw [Finset.sum_range_succ']
  simp

private lemma sum_log_upper (N : ℕ) :
    (∑ n ∈ range (N + 1), Real.log (n : ℝ))
      ≤ ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N := by
  have h := MonotoneOn.sum_le_integral (f := fun x : ℝ => Real.log x) (x₀ := (1 : ℝ)) (a := N)
    (fun x hx y hy hxy => Real.log_le_log (by linarith [hx.1]) hxy)
  rw [integral_log] at h
  rw [Real.log_one] at h
  have hconv : (∑ i ∈ range N, Real.log ((1 : ℝ) + ↑i))
      = ∑ n ∈ range (N + 1), Real.log (n : ℝ) := by
    rw [← sum_log_range_shift N]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [hconv] at h
  have h' : (1 + (N : ℝ)) * Real.log (1 + (N : ℝ)) - 1 * 0 - (1 + (N : ℝ)) + 1
      = ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N := by
    rw [show (1 + (N : ℝ)) = ((N : ℝ) + 1) by ring]
    ring
  linarith [h, h']

private lemma sum_log_lower (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ ∑ n ∈ range (N + 1), Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have h := MonotoneOn.integral_le_sum (f := fun x : ℝ => Real.log x) (x₀ := (1 : ℝ)) (a := N)
    (fun x hx y hy hxy => Real.log_le_log (by linarith [hx.1]) hxy)
  rw [integral_log] at h
  rw [Real.log_one] at h
  have h2 : (∑ i ∈ range N, Real.log ((1 : ℝ) + ↑(i + 1)))
      = ∑ n ∈ range (N + 2), Real.log (n : ℝ) := by
    have e1 : (∑ i ∈ range N, Real.log ((1 : ℝ) + ↑(i + 1)))
        = ∑ i ∈ range (N + 1), Real.log ((1 : ℝ) + ↑i) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, add_zero, Real.log_one, zero_add]
    rw [e1]
    have e2 : (∑ i ∈ range (N + 1), Real.log ((1 : ℝ) + ↑i))
        = ∑ i ∈ range (N + 1), Real.log ((i : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    rw [e2, sum_log_range_shift (N + 1)]
  rw [h2, Finset.sum_range_succ] at h
  have h' : ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N
      ≤ (∑ n ∈ range (N + 1), Real.log (n : ℝ)) + Real.log ((N : ℝ) + 1) := by
    have hh := h
    rw [show (1 + (N : ℝ)) = ((N : ℝ) + 1) by ring] at hh
    rw [show Real.log (((N + 1 : ℕ)) : ℝ) = Real.log ((N : ℝ) + 1) from by
      push_cast; ring_nf] at hh
    linarith [hh]
  have h5 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
    apply sub_nonneg.mpr
    exact Real.log_le_log (by exact_mod_cast hN) (by linarith)
  have h6 : (N : ℝ) * Real.log N ≤ (N : ℝ) * Real.log ((N : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [h5]) (by positivity)
  linarith [h', h6]

private lemma V_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    |(∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n) - Real.log N| ≤ C := by
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine ⟨2 * Real.log 3 + 2, by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- ### Step 1
  have hmain : |(N : ℝ) * (∑ n ∈ range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) / n)
      - (∑ n ∈ range (N + 1), Real.log (n : ℝ))| ≤ Real.log 3 * ((N : ℝ) + 1) := by
    have hsplit : (N : ℝ) * (∑ n ∈ range (N + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) / n)
        - (∑ n ∈ range (N + 1), Real.log (n : ℝ))
        = ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d : ℝ)
            * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)) := by
      rw [V_eq_Icc, sum_log_hyperbola, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    rw [hsplit]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hbd : ∀ d ∈ Icc 1 N,
        |(ArithmeticFunction.vonMangoldt d : ℝ) * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))|
          ≤ (ArithmeticFunction.vonMangoldt d : ℝ) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt d : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hle1 : (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) ≤ 1 := by
        have h1 : (N : ℝ) < ((N / d : ℕ) : ℝ) * (d : ℝ) + d := by
          have hnat : N < (N / d) * d + d := by
            have h := Nat.div_add_mod N d
            have hmod : N % d < d := Nat.mod_lt N (by omega)
            nlinarith
          have h2 : ((N / d : ℕ) : ℝ) * (d : ℝ) = (((N / d) * d : ℕ) : ℝ) := by push_cast; ring
          rw [h2]
          exact_mod_cast hnat
        have : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
          rw [div_lt_iff₀ hd0]; linarith
        linarith
      have hge0 : (0 : ℝ) ≤ (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) := by
        have : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
          rw [le_div_iff₀ hd0]
          exact_mod_cast Nat.div_mul_le_self N d
        linarith
      rw [abs_mul, abs_of_nonneg hΛ, abs_of_nonneg (by linarith)]
      calc (ArithmeticFunction.vonMangoldt d : ℝ)
            * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))
          ≤ (ArithmeticFunction.vonMangoldt d : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hle1 hΛ
        _ = (ArithmeticFunction.vonMangoldt d : ℝ) := mul_one _
    calc ∑ d ∈ Icc 1 N, |(ArithmeticFunction.vonMangoldt d : ℝ)
          * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d : ℝ) := Finset.sum_le_sum hbd
      _ ≤ ∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) := by
          rw [show range (N+1) = insert 0 (Icc 1 N) from by
            ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega]
          rw [Finset.sum_insert (by simp)]
          have := ArithmeticFunction.vonMangoldt_nonneg (n := 0)
          linarith
      _ ≤ Real.log 3 * ((N : ℝ) + 1) := psi_bound N
  -- ### Step 2
  have hlogbound : |(∑ n ∈ range (N + 1), Real.log (n : ℝ)) - (N : ℝ) * Real.log N|
      ≤ N + Real.log ((N : ℝ) + 1) := by
    have hupper := sum_log_upper N
    have hlower := sum_log_lower N
    have h1 : (∑ n ∈ range (N + 1), Real.log (n : ℝ)) - (N : ℝ) * Real.log N
        ≤ Real.log ((N : ℝ) + 1) := by
      have h4 : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
        have hdiv : ((N : ℝ) + 1) / N = 1 + 1 / N := by field_simp
        have hpos : (0 : ℝ) < ((N : ℝ) + 1) / N := by positivity
        have h5 := Real.log_le_sub_one_of_pos hpos
        have hd : ((N : ℝ) + 1) / N - 1 = 1 / N := by
          rw [add_div, div_self (ne_of_gt hNpos)]
          ring
        have hlog : Real.log ((N : ℝ) + 1) - Real.log N = Real.log (((N : ℝ) + 1) / N) := by
          rw [Real.log_div (by positivity) (ne_of_gt hNpos)]
        rw [hlog]
        linarith [h5, hd]
      have h6 : N * (Real.log ((N : ℝ) + 1) - Real.log N) ≤ 1 := by
        calc N * (Real.log ((N : ℝ) + 1) - Real.log N) ≤ N * (1 / N) :=
              mul_le_mul_of_nonneg_left h4 (by linarith)
          _ = 1 := by field_simp
      have h7 : ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1)
          = Real.log ((N : ℝ) + 1) + N * Real.log ((N : ℝ) + 1) := by ring
      linarith
    have h2 : -((N : ℝ)) ≤ (∑ n ∈ range (N + 1), Real.log (n : ℝ)) - (N : ℝ) * Real.log N := by
      linarith
    have h3 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  -- ### Step 3
  have hkey : (N : ℝ) * |(∑ n ∈ range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) / n) - Real.log N|
      ≤ Real.log 3 * ((N : ℝ) + 1) + (N + Real.log ((N : ℝ) + 1)) := by
    set V : ℝ := ∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n with hV
    set S : ℝ := ∑ n ∈ range (N + 1), Real.log (n : ℝ) with hS
    have h2 : |(N : ℝ) * V - (N : ℝ) * Real.log N|
        ≤ |(N : ℝ) * V - S| + |S - (N : ℝ) * Real.log N| := by
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · linarith [le_abs_self ((N : ℝ) * V - S), le_abs_self (S - (N : ℝ) * Real.log N)]
      · linarith [neg_abs_le ((N : ℝ) * V - S), neg_abs_le (S - (N : ℝ) * Real.log N)]
    have h3 : (N : ℝ) * V - (N : ℝ) * Real.log N = (N : ℝ) * (V - Real.log N) := by ring
    rw [h3, abs_mul, abs_of_pos hNpos] at h2
    linarith [h2, hmain, hlogbound]
  -- ### Step 4
  have hfinal : |(∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n) - Real.log N|
      ≤ (Real.log 3 * ((N : ℝ) + 1) + 2 * N) / N := by
    rw [le_div_iff₀ hNpos, mul_comm]
    have h2 : N + Real.log ((N : ℝ) + 1) ≤ 2 * N := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (N : ℝ) + 1 by positivity)
      linarith
    linarith [hkey, h2]
  refine hfinal.trans ?_
  have h1 : Real.log 3 * ((N : ℝ) + 1) ≤ 2 * Real.log 3 * N := by
    have : ((N : ℝ) + 1) ≤ 2 * N := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hlog3]
  have h5 : (Real.log 3 * ((N : ℝ) + 1) + 2 * N) / N ≤ 2 * Real.log 3 + 2 := by
    rw [div_le_iff₀ hNpos]
    nlinarith [h1, hlog3]
  linarith [h5]

/-! ### The weighted prime log-divisor sum `Θ` -/

/-- `Θ(N) = Σ_{p ≤ N} (1 + χ₄(p)) log p / p`. -/
private def Theta (N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 1)).filter Nat.Prime, (1 + c4 p) * Real.log p / p

private lemma logDiv_eq (N : ℕ) :
    Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ)
      = ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p := by
  rw [Commons.NumberTheory.Mertens.logDiv, Nat.floor_natCast, primesLE_eq]

private lemma Theta_eq (N : ℕ) :
    Theta N = Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ)
      + ∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p := by
  rw [Theta, logDiv_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

private lemma vonMangoldt_split (N : ℕ) :
    (∑ n ∈ range (N + 1), c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n)
      = (∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p)
        + ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
            c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := range (N + 1)) (p := Nat.Prime)
    (f := fun n => c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]

private lemma lambda_split (N : ℕ) :
    (∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n)
      = (∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p)
        + ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
            (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := range (N + 1)) (p := Nat.Prime)
    (f := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) / n)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]

private lemma nonprime_lambda_eq (N : ℕ) :
    (∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℝ) / n)
      = (∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n)
        - Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ) := by
  rw [lambda_split N, logDiv_eq N]
  ring

private lemma Theta_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, |Theta N - Real.log N| ≤ C := by
  obtain ⟨CV, hCV, hV⟩ := V_bound
  obtain ⟨CD, hCD, hD⟩ := Commons.NumberTheory.Mertens.first_mertens_bounded
  obtain ⟨CW, hCW, hW⟩ := W_bounded
  refine ⟨CD + CW + 2 * (CV + CD), by positivity, fun N => ?_⟩
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hN01 : N = 0 ∨ N = 1 := by omega
    rcases hN01 with rfl | rfl
    · have h0 : Theta 0 = 0 := by
        rw [Theta]
        apply Finset.sum_eq_zero
        intro p hp
        rw [Finset.mem_filter, Finset.mem_range] at hp
        have hp0 : p = 0 := by omega
        rw [hp0] at hp
        exact absurd hp.2 Nat.not_prime_zero
      rw [h0]
      simp only [Nat.cast_zero, Real.log_zero, sub_zero, abs_zero]
      linarith [hCD, hCW, hCV]
    · have h1 : Theta 1 = 0 := by
        rw [Theta]
        apply Finset.sum_eq_zero
        intro p hp
        rw [Finset.mem_filter, Finset.mem_range] at hp
        have hp01 : p = 0 ∨ p = 1 := by omega
        rcases hp01 with hp0 | hp1
        · rw [hp0] at hp; exact absurd hp.2 Nat.not_prime_zero
        · rw [hp1] at hp; exact absurd hp.2 Nat.not_prime_one
      rw [h1]
      simp only [Nat.cast_one, Real.log_one, sub_zero, abs_zero]
      linarith [hCD, hCW, hCV]
  have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hVN : |(∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n) - Real.log N|
      ≤ CV := hV N
  have hDN : |Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ) - Real.log N| ≤ CD :=
    hD ((N : ℕ) : ℝ) h2N
  have hWN : |(∑ n ∈ range (N + 1), c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n)|
      ≤ CW := hW N
  -- bound the non-prime part
  have hnonneg : |∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
        c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n|
      ≤ 2 * ((∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n)
        - Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ)) := by
    have h1 : ∀ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
        |c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n|
          ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
      intro n _
      have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [abs_div, abs_mul, abs_of_nonneg hn, abs_of_nonneg hΛ]
      calc |c4 n| * (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)
          ≤ 1 * (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (abs_c4_le_one n) hΛ) hn
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) := by ring
        _ ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)) := by
            have := div_nonneg hΛ hn
            linarith
    calc |∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
          c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n|
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
            |c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
            2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) := Finset.sum_le_sum h1
      _ = 2 * ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
            (ArithmeticFunction.vonMangoldt n : ℝ) / n := by rw [Finset.mul_sum]
      _ = 2 * ((∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n)
            - Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ)) := by
          rw [nonprime_lambda_eq N]
  -- bound the χ₄-weighted prime sum
  have hkey : (∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p)
      = (∑ n ∈ range (N + 1), c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n)
        - ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
            c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
    rw [vonMangoldt_split N]; ring
  have hchi : |(∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p)|
      ≤ CW + 2 * (CV + CD) := by
    have hVl : (∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n)
        - Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ) ≤ CV + CD := by
      have h1 : (∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n) - Real.log N
          ≤ CV := by linarith [abs_le.mp hVN]
      have h2 : Real.log N - Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ) ≤ CD := by
        linarith [abs_le.mp hDN]
      linarith
    have hnp := le_trans hnonneg (by linarith [hVl] :
      2 * ((∑ n ∈ range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / n)
        - Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ)) ≤ 2 * (CV + CD))
    rw [hkey, abs_sub_le_iff]
    constructor
    · linarith [le_abs_self (∑ n ∈ range (N + 1), c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n),
        neg_abs_le (∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
          c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n), hWN, hnp]
    · linarith [neg_abs_le (∑ n ∈ range (N + 1), c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n),
        le_abs_self (∑ n ∈ (range (N + 1)).filter (fun n => ¬ n.Prime),
          c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) / n), hWN, hnp]
  rw [Theta_eq N]
  have habs : |Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ)
        + (∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p) - Real.log N|
      ≤ |Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ) - Real.log N|
        + |∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p| := by
    have e : Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ)
          + (∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p) - Real.log N
        = (Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ) - Real.log N)
          + (∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p) := by ring
    rw [e]
    exact abs_add_le _ _
  calc |Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ)
          + (∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p) - Real.log N|
      ≤ |Commons.NumberTheory.Mertens.logDiv ((N : ℕ) : ℝ) - Real.log N|
        + |∑ p ∈ (range (N + 1)).filter Nat.Prime, c4 p * Real.log p / p| := habs
    _ ≤ CD + (CW + 2 * (CV + CD)) := add_le_add hDN hchi
    _ = CD + CW + 2 * (CV + CD) := by ring

/-! ### Abel summation for `Σ_{p ≤ x} (1 + χ₄(p)) log p / p` -/

/-- The weight `b n = (1 + χ₄(n)) log n / n` supported on the primes. -/
private def bAb (n : ℕ) : ℝ := (1 + c4 n) * Real.log n / n * (if n.Prime then (1 : ℝ) else 0)

private lemma bAb_zero : bAb 0 = 0 := by simp [bAb]

private lemma bAb_one : bAb 1 = 0 := by simp [bAb]

private lemma Icc_filter_prime_eq (N : ℕ) :
    (Finset.Icc 0 N).filter Nat.Prime = (Finset.range (N + 1)).filter Nat.Prime := by
  ext p
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hpr⟩
    rw [Finset.mem_Icc] at hp
    exact ⟨by rw [Finset.mem_range]; omega, hpr⟩
  · rintro ⟨hp, hpr⟩
    rw [Finset.mem_range] at hp
    exact ⟨by rw [Finset.mem_Icc]; omega, hpr⟩

private lemma sum_bAb (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, bAb n) = Theta ⌊x⌋₊ := by
  rw [Theta, ← Icc_filter_prime_eq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  unfold bAb
  rw [mul_ite, mul_one, mul_zero]

private lemma sum_bAb_div_log (x : ℝ) (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, bAb n / Real.log n)
      = ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + c4 p) / (p : ℝ) := by
  have hterm : ∀ n ∈ Finset.Icc 0 ⌊x⌋₊,
      n ∉ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime → bAb n / Real.log n = 0 := by
    intro n hnmem hnf
    have hnp : ¬ n.Prime := fun h => hnf (Finset.mem_filter.mpr ⟨hnmem, h⟩)
    rw [bAb, if_neg hnp, mul_zero, zero_div]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hterm, Icc_filter_prime_eq]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [bAb, if_pos hp.2, mul_one]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
  have hlogp : Real.log (p : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · linarith
    · intro h; rw [h] at hp2; norm_num at hp2
  have hp0 : (p : ℝ) ≠ 0 := by
    have h2le : 2 ≤ p := hp.2.two_le
    have hne : p ≠ 0 := by omega
    exact_mod_cast hne
  field_simp

/-- **Abel summation** for the logarithmic weight `(1 + χ₄(p)) log p / p`. -/
private lemma Abel_identity (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + c4 p) / (p : ℝ))
      = Theta ⌊x⌋₊ / Real.log x
        + ∫ t in (2 : ℝ)..x, Theta ⌊t⌋₊ / (t * (Real.log t) ^ 2) := by
  rw [← sum_bAb_div_log x hx,
    sum_div_log_abel_identity bAb bAb_zero bAb_one hx, sum_bAb x]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [sum_bAb t]

section GeneralAnalysis

open MeasureTheory

/-- For `t ≥ 1` the logarithm of `t` and of its floor differ by at most `log 2`. -/
private lemma abs_log_sub_log_floor_le {t : ℝ} (ht : 1 ≤ t) :
    |Real.log t - Real.log ((⌊t⌋₊ : ℕ) : ℝ)| ≤ Real.log 2 := by
  have htpos : (0 : ℝ) < t := by linarith
  have hfl : (1 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by
    have h : ((1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    exact_mod_cast Nat.le_floor h
  have hflpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by linarith
  have hle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hlt : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hsplit : Real.log t - Real.log ((⌊t⌋₊ : ℕ) : ℝ)
      = Real.log (t / ((⌊t⌋₊ : ℕ) : ℝ)) :=
    (Real.log_div (ne_of_gt htpos) (ne_of_gt hflpos)).symm
  have hratio_ge : 1 ≤ t / ((⌊t⌋₊ : ℕ) : ℝ) := (one_le_div hflpos).mpr hle
  have hratio_le : t / ((⌊t⌋₊ : ℕ) : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hflpos]
    nlinarith [hlt, hfl]
  rw [hsplit, abs_of_nonneg (Real.log_nonneg hratio_ge)]
  exact Real.log_le_log (div_pos htpos hflpos) hratio_le

/-- A measurable function bounded on `[2, ∞)` is integrable against `(t (log t)^2)⁻¹`. -/
private lemma integrableOn_g_div_id_log_sq {g : ℝ → ℝ} {M : ℝ}
    (hg : Measurable g) (hb : ∀ t : ℝ, 2 ≤ t → |g t| ≤ M) :
    IntegrableOn (fun t : ℝ => g t / (t * (Real.log t) ^ 2)) (Set.Ioi 2) volume := by
  have hmc : Measurable (fun t : ℝ => t * (Real.log t) ^ 2) := by
    have h1 : Measurable (fun t : ℝ => Real.log t * Real.log t) :=
      Real.measurable_log.mul Real.measurable_log
    have h2 : Measurable (fun t : ℝ => (Real.log t) ^ 2) := by simpa [pow_two] using h1
    exact measurable_id.mul h2
  have hfm : Measurable (fun t : ℝ => g t / (t * (Real.log t) ^ 2)) := hg.div hmc
  have hdom : Integrable (fun t : ℝ => M * (t⁻¹ / (Real.log t) ^ 2))
      (volume.restrict (Set.Ioi 2)) :=
    (integrableOn_inv_div_log_sq_Ioi (c := 2) (by norm_num)).const_mul M
  refine hdom.mono' hfm.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have ht2 : (2 : ℝ) ≤ t := le_of_lt ht
  have hden : (0 : ℝ) < t * (Real.log t) ^ 2 := by
    have hl : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
    positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
  calc |g t| / (t * (Real.log t) ^ 2) ≤ M / (t * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right (hb t ht2) (le_of_lt hden)
    _ = M * (t⁻¹ / (Real.log t) ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]

/-- The improper integral `∫_2^x g t/(t (log t)^2) dt` converges for `g` measurable and
bounded on `[2, ∞)`. -/
private lemma bounded_div_id_log_sq_tendsto {g : ℝ → ℝ} {M : ℝ}
    (hg : Measurable g) (hb : ∀ t : ℝ, 2 ≤ t → |g t| ≤ M) :
    ∃ L : ℝ, Tendsto (fun x : ℝ => ∫ t in (2 : ℝ)..x, g t / (t * (Real.log t) ^ 2))
      atTop (nhds L) :=
  ⟨_, intervalIntegral_tendsto_integral_Ioi (μ := volume)
      (b := fun x : ℝ => x) (l := atTop) (2 : ℝ)
      (integrableOn_g_div_id_log_sq hg hb) tendsto_id⟩

/-- Splitting off the main term of the integral: for `x ≥ 2`,
`∫_2^x (log t + g t)/(t (log t)^2) dt = log log x - log log 2 + ∫_2^x g t/(t (log t)^2) dt`. -/
private lemma integral_log_add_div_id_log_sq {g : ℝ → ℝ} {M x : ℝ}
    (hx : 2 ≤ x) (hg : Measurable g) (hb : ∀ t : ℝ, 2 ≤ t → |g t| ≤ M) :
    ∫ t in (2 : ℝ)..x, (Real.log t + g t) / (t * (Real.log t) ^ 2)
      = Real.log (Real.log x) - Real.log (Real.log 2)
        + ∫ t in (2 : ℝ)..x, g t / (t * (Real.log t) ^ 2) := by
  have hInt2 : IntervalIntegrable (fun t : ℝ => g t / (t * (Real.log t) ^ 2)) volume
      (2 : ℝ) x := by
    rw [intervalIntegrable_iff]
    refine (integrableOn_g_div_id_log_sq hg hb).mono_set ?_
    rw [Set.uIoc_of_le hx]
    exact fun t ht => ht.1
  have hInt1 : IntervalIntegrable (fun t : ℝ => (t * Real.log t)⁻¹) volume (2 : ℝ) x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.inv₀ (continuousOn_id.mul ?_) ?_
    · exact Real.continuousOn_log.mono (fun t ht => by
        have ht2 : (2 : ℝ) ≤ t := ht.1
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith)
    · intro t ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      refine mul_ne_zero (by linarith) ?_
      exact Real.log_ne_zero_of_pos_of_ne_one (by linarith)
        (by intro h; rw [h] at ht2; norm_num at ht2)
  have hpt : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      (Real.log t + g t) / (t * (Real.log t) ^ 2)
        = (t * Real.log t)⁻¹ + g t / (t * (Real.log t) ^ 2) := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have hlogt : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · linarith
      · intro h; rw [h] at ht2; norm_num at ht2
    have ht0 : t ≠ 0 := by linarith
    have h1 : Real.log t / (t * (Real.log t) ^ 2) = (t * Real.log t)⁻¹ := by
      field_simp
    rw [add_div, h1]
  have hmain : ∫ t in (2 : ℝ)..x, (t * Real.log t)⁻¹
      = Real.log (Real.log x) - Real.log (Real.log 2) := by
    rw [show (fun t : ℝ => (t * Real.log t)⁻¹) = (fun t : ℝ => t⁻¹ / Real.log t) from by
      funext t; rw [div_eq_mul_inv, mul_inv]]
    exact integral_inv_div_log (by norm_num) (by linarith)
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hInt1 hInt2, hmain]

end GeneralAnalysis

/-! ### The bounded remainder `Efun t = Θ(⌊t⌋) - log t` -/

private noncomputable def Efun (t : ℝ) : ℝ := Theta ⌊t⌋₊ - Real.log t

private lemma Efun_measurable : Measurable Efun := by
  have h1 : Measurable (fun n : ℕ => Theta n) := measurable_of_countable _
  have h2 : Measurable (fun t : ℝ => Theta ⌊t⌋₊) := h1.comp Nat.measurable_floor
  exact h2.sub Real.measurable_log

private lemma Efun_abs_le (C : ℝ) (hC : ∀ N : ℕ, |Theta N - Real.log N| ≤ C) :
    ∀ t : ℝ, 2 ≤ t → |Efun t| ≤ C + Real.log 2 := by
  intro t ht
  have h1 : |Theta ⌊t⌋₊ - Real.log ((⌊t⌋₊ : ℕ) : ℝ)| ≤ C := hC ⌊t⌋₊
  have h2 : |Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t| ≤ Real.log 2 := by
    rw [abs_sub_comm]
    exact abs_log_sub_log_floor_le (by linarith)
  have hsplit : Efun t = (Theta ⌊t⌋₊ - Real.log ((⌊t⌋₊ : ℕ) : ℝ))
      + (Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t) := by unfold Efun; ring
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)



/-- The explicit convergent expression for `Σ_{p ≤ x} (1 + χ₄(p))/p - log log x`. -/
private lemma F_eq (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + c4 p) / (p : ℝ))
        - Real.log (Real.log x)
      = (1 - Real.log (Real.log 2)) + Efun x / Real.log x
        + ∫ t in (2 : ℝ)..x, Efun t / (t * (Real.log t) ^ 2) := by
  obtain ⟨C, hCpos, hCb⟩ := Theta_bound
  have hEb : ∀ t : ℝ, 2 ≤ t → |Efun t| ≤ C + Real.log 2 := Efun_abs_le C hCb
  have hint_eq : ∫ t in (2 : ℝ)..x, Theta ⌊t⌋₊ / (t * (Real.log t) ^ 2)
      = ∫ t in (2 : ℝ)..x, (Real.log t + Efun t) / (t * (Real.log t) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t _
    unfold Efun; ring
  have hlogx : Real.log x ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one (by linarith)
    intro h; linarith [hx, h]
  have hΘ : Theta ⌊x⌋₊ / Real.log x = 1 + Efun x / Real.log x := by
    rw [Efun, sub_div, div_self hlogx]
    ring
  rw [Abel_identity x hx, hint_eq,
    integral_log_add_div_id_log_sq hx Efun_measurable hEb, hΘ]
  ring

/-- `Σ_{p ≤ x} (1 + χ₄(p))/p - log log x` converges. -/
private lemma one_add_recip_tendsto :
    ∃ c : ℝ, Tendsto (fun x : ℝ =>
      (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + c4 p) / (p : ℝ))
        - Real.log (Real.log x)) atTop (nhds c) := by
  obtain ⟨C, hCpos, hCb⟩ := Theta_bound
  have hEb : ∀ t : ℝ, 2 ≤ t → |Efun t| ≤ C + Real.log 2 := Efun_abs_le C hCb
  obtain ⟨L, hL⟩ := bounded_div_id_log_sq_tendsto (g := Efun) (M := C + Real.log 2)
    Efun_measurable hEb
  have hEdiv : Tendsto (fun x : ℝ => Efun x / Real.log x) atTop (nhds 0) := by
    have hlim : Tendsto (fun x : ℝ => (C + Real.log 2) / Real.log x) atTop (nhds 0) :=
      Tendsto.const_div_atTop Real.tendsto_log_atTop (C + Real.log 2)
    have hlimneg : Tendsto (fun x : ℝ => -((C + Real.log 2) / Real.log x)) atTop (nhds 0) := by
      simpa using hlim.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimneg hlim ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
      have h1 : -(C + Real.log 2) ≤ Efun x := by
        have := (abs_le.mp (hEb x hx)).1
        linarith
      have h2 : -((C + Real.log 2) / Real.log x) = (-(C + Real.log 2)) / Real.log x := by
        rw [neg_div]
      rw [h2]
      exact div_le_div_of_nonneg_right h1 (le_of_lt hlogx)
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
      have h1 : Efun x ≤ C + Real.log 2 := (abs_le.mp (hEb x hx)).2
      exact div_le_div_of_nonneg_right h1 (le_of_lt hlogx)
  refine ⟨1 - Real.log (Real.log 2) + L, ?_⟩
  have hmain : Tendsto (fun x : ℝ => (1 - Real.log (Real.log 2)) + Efun x / Real.log x
      + ∫ t in (2 : ℝ)..x, Efun t / (t * (Real.log t) ^ 2)) atTop
      (nhds ((1 - Real.log (Real.log 2)) + L)) := by
    simpa using (((tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 - Real.log (Real.log 2))) atTop
        (nhds (1 - Real.log (Real.log 2)))).add hEdiv).add hL)
  have hev : (fun x : ℝ => (1 - Real.log (Real.log 2)) + Efun x / Real.log x
      + ∫ t in (2 : ℝ)..x, Efun t / (t * (Real.log t) ^ 2))
      =ᶠ[atTop] (fun x : ℝ =>
        (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + c4 p) / (p : ℝ))
          - Real.log (Real.log x)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    exact (F_eq x hx).symm
  exact hmain.congr' hev

/-- `Mertens.primeRecips` agrees with the explicit prime-reciprocal sum. -/
private lemma primeRecips_eq_sum (x : ℝ) :
    Commons.NumberTheory.Mertens.primeRecips x
      = ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  simp only [Commons.NumberTheory.Mertens.primeRecips]
  rw [primesLE_eq]

/-- Convergence of `Σ_{p ≤ x} χ₄(p)/p` over the reals. -/
private lemma chi4_prime_recip_tendsto_real :
    ∃ c : ℝ, Tendsto (fun y : ℝ =>
      ∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, c4 p / (p : ℝ)) atTop (nhds c) := by
  obtain ⟨c1, h1⟩ := one_add_recip_tendsto
  obtain ⟨M, hM⟩ := Commons.NumberTheory.Mertens.second_mertens_converges
  have h2 : Tendsto (fun x : ℝ =>
      (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        - Real.log (Real.log x)) atTop (nhds M) :=
    hM.congr' (Eventually.of_forall (fun x => by rw [primeRecips_eq_sum x]))
  refine ⟨c1 - M, ?_⟩
  have h3 : Tendsto (fun x : ℝ =>
      (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + c4 p) / (p : ℝ))
        - Real.log (Real.log x)) atTop (nhds c1) := h1
  have hev : (fun x : ℝ =>
        ((∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + c4 p) / (p : ℝ))
            - Real.log (Real.log x))
          - ((∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
            - Real.log (Real.log x)))
      =ᶠ[atTop] (fun y : ℝ => ∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, c4 p / (p : ℝ)) := by
    refine Eventually.of_forall (fun x => ?_)
    dsimp only
    have hsplit : (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + c4 p) / (p : ℝ))
        = (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          + ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, c4 p / (p : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [add_div]
    rw [hsplit]
    ring
  exact (h3.sub h2).congr' hev

theorem chi4_prime_recip_converges :
    ∃ c : ℂ, Filter.Tendsto (fun y : ℝ =>
        ∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
          (((ZMod.χ₄ (p : ZMod 4) : ℤ)) : ℂ) / (p : ℂ)) Filter.atTop (nhds c) := by
  obtain ⟨c, hc⟩ := chi4_prime_recip_tendsto_real
  refine ⟨(c : ℂ), ?_⟩
  have hsum : ∀ y : ℝ, (∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
        (((ZMod.χ₄ (p : ZMod 4) : ℤ)) : ℂ) / (p : ℂ))
      = ((∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, c4 p / (p : ℝ) : ℝ) : ℂ) := by
    intro y
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    simp only [c4, Complex.ofReal_intCast]
  have hcont : Filter.Tendsto (fun y : ℝ =>
      ((∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, c4 p / (p : ℝ) : ℝ) : ℂ))
      Filter.atTop (nhds ((c : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto c).comp hc
  exact hcont.congr' (Filter.Eventually.of_forall (fun y => (hsum y).symm))

end

end Commons.NumberTheory.FriedlanderIwaniec
