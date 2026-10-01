import Mathlib.NumberTheory.Chebyshev
import Submission.Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds

open Finset
open scoped ArithmeticFunction

namespace Commons.NumberTheory.ArithmeticFunction

/-!
# Mertens' first theorem in the von Mangoldt form

We prove that there is a constant `C` with
`|∑_{n ≤ x} Λ(n)/n − log x| ≤ C` for every `x ≥ 1`.

The proof is the classical elementary one.  For an integer `N ≥ 2` we use
`∑_{n ≤ N} log n = log (N!)` (Stirling, in the form of
`Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds`) together with
the divisor sum identity `log n = ∑_{d ∣ n} Λ(d)`, which after exchanging the
order of summation becomes `∑_{d ≤ N} Λ(d) ⌊N/d⌋`.  Comparing with
`N · ∑_{d ≤ N} Λ(d)/d` and using Chebyshev's bound `∑_{d ≤ N} Λ(d) ≤ C N`
(`Chebyshev.psi_le_const_mul_self`) yields `∑_{d ≤ N} Λ(d)/d = log N + O(1)`.
-/

/-! ## Double counting over divisors -/

/-- Summing over divisors and then over `n ≤ N` is the same as summing `f d`
weighted by the number `⌊N/d⌋` of multiples of `d` up to `N`. -/
lemma sum_Icc_divisors_eq_sum_mul_div (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, f d = ∑ d ∈ Icc 1 N, f d * ((N / d : ℕ) : ℝ) := by
  have hIcc : Icc 1 N = Ioc 0 N := by
    ext n; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdiv : ∀ n ∈ Icc 1 N, n.divisors = (Icc 1 N).filter (fun d => d ∣ n) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
        le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, hdvd⟩
    · rintro ⟨⟨hd1, _⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  calc ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, f d
      = ∑ n ∈ Icc 1 N, ∑ d ∈ (Icc 1 N).filter (fun d => d ∣ n), f d := by
        apply sum_congr rfl; intro n hn; rw [hdiv n hn]
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, (if d ∣ n then f d else 0) := by
        apply sum_congr rfl; intro n _; rw [sum_filter]
    _ = ∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if d ∣ n then f d else 0) := sum_comm
    _ = ∑ d ∈ Icc 1 N, f d * (((Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) := by
        apply sum_congr rfl; intro d _
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ d ∈ Icc 1 N, f d * ((N / d : ℕ) : ℝ) := by
        apply sum_congr rfl; intro d _
        have hc : (((Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) = ((N / d : ℕ) : ℝ) := by
          rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
        rw [hc]

/-! ## The identity `∑ log n = ∑ Λ(d) ⌊N/d⌋ = log (N!)` -/

/-- `∑_{n ≤ N} log n = log (N!)`. -/
lemma sum_log_Icc_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Icc 1 N, Real.log (n : ℝ) = Real.log (N.factorial : ℝ) := by
  have hprod : (∏ n ∈ Icc 1 N, (n : ℝ)) = (N.factorial : ℝ) := by
    rw [← Finset.prod_natCast]
    congr 1
    rw [show Icc 1 N = Ico 1 (N + 1) by
      ext n; simp [Finset.mem_Icc, Finset.mem_Ico]]
    exact Finset.prod_Ico_id_eq_factorial N
  have hne : ∀ n ∈ Icc 1 N, (n : ℝ) ≠ 0 := by
    intro n hn; rw [Finset.mem_Icc] at hn; exact_mod_cast (by omega : n ≠ 0)
  rw [← Real.log_prod hne, hprod]

/-- The identity `∑_{d ≤ N} Λ(d) · ⌊N/d⌋ = log (N!)`. -/
lemma sum_vonMangoldt_mul_div_eq_log_factorial (N : ℕ) :
    ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
      = Real.log (N.factorial : ℝ) := by
  rw [← sum_Icc_divisors_eq_sum_mul_div ArithmeticFunction.vonMangoldt N]
  calc ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d
      = ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
        apply sum_congr rfl; intro n _
        rw [ArithmeticFunction.vonMangoldt_sum]
    _ = Real.log (N.factorial : ℝ) := sum_log_Icc_eq_log_factorial N

/-! ## The two termwise estimates -/

/-- `Λ d · ⌊N/d⌋ ≤ N · (Λ d / d)`, termwise. -/
lemma vonMangoldt_mul_div_le (N d : ℕ) :
    ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
      ≤ (N : ℝ) * (ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
  calc ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
      ≤ ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le hΛ
    _ = (N : ℝ) * (ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by ring

/-- `N/d < ⌊N/d⌋ + 1` as real numbers. -/
lemma div_lt_nat_div_add_one (N d : ℕ) (hd : 0 < d) :
    (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
  have hnat : N < (N / d + 1) * d := by
    have h := Nat.div_add_mod N d
    have hm := Nat.mod_lt N hd
    calc N = d * (N / d) + N % d := h.symm
      _ < d * (N / d) + d := by omega
      _ = (N / d + 1) * d := by ring
  have hreal : (N : ℝ) < (((N / d : ℕ) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast hnat
  rw [div_lt_iff₀ (by exact_mod_cast hd)]
  linarith [hreal]

/-- `N · (Λ d / d) ≤ Λ d · ⌊N/d⌋ + Λ d`, termwise. -/
lemma nat_mul_vonMangoldt_div_le (N d : ℕ) (hd : 0 < d) :
    (N : ℝ) * (ArithmeticFunction.vonMangoldt d / (d : ℝ))
      ≤ ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) + ArithmeticFunction.vonMangoldt d := by
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
  have hNdd : (N : ℝ) / (d : ℝ) ≤ ((N / d : ℕ) : ℝ) + 1 :=
    le_of_lt (div_lt_nat_div_add_one N d hd)
  calc (N : ℝ) * (ArithmeticFunction.vonMangoldt d / (d : ℝ))
      = ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)) := by ring
    _ ≤ ArithmeticFunction.vonMangoldt d * (((N / d : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hNdd hΛ
    _ = ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) + ArithmeticFunction.vonMangoldt d := by
        ring

/-! ## Chebyshev's bound and Stirling bounds -/

/-- Chebyshev's bound for the sum of `Λ` over `Icc 1 N`. -/
lemma sum_vonMangoldt_Icc_le (N : ℕ) :
    ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d ≤ (Real.log 4 + 4) * (N : ℝ) := by
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at h
  have hIoc : Ioc 0 N = Icc 1 N := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]
    constructor <;> intro hbar <;> exact ⟨by omega, hbar.2⟩
  rwa [hIoc] at h

/-- `∑_{n ≤ N} log n ≤ N log N`. -/
lemma sum_log_Icc_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by
  have hNN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc ∑ n ∈ Icc 1 N, Real.log (n : ℝ)
      ≤ ∑ _n ∈ Icc 1 N, Real.log (N : ℝ) := by
        apply sum_le_sum; intro n hn
        rw [Finset.mem_Icc] at hn
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hn.2)
    _ = (Icc 1 N).card • Real.log (N : ℝ) := sum_const _
    _ = (N : ℝ) * Real.log (N : ℝ) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- `N log N - N ≤ ∑_{n ≤ N} log n` (the Stirling lower bound). -/
lemma log_factorial_le_sum_log_Icc (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
  have hE := Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds (n := N) hN
  rw [sum_log_Icc_eq_log_factorial N]
  linarith [hE.1]

/-! ## The main integer estimate -/

/-- For integers `N ≥ 2`: `|∑_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 4`. -/
theorem sum_vonMangoldt_div_sub_log_nat_bound (N : ℕ) (hN : 2 ≤ N) :
    |∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) - Real.log (N : ℝ)|
      ≤ Real.log 4 + 4 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : 1 ≤ N := by omega
  have hkey : ∑ n ∈ Icc 1 N, Real.log (n : ℝ)
      = ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
    rw [sum_log_Icc_eq_log_factorial, sum_vonMangoldt_mul_div_eq_log_factorial]
  -- lower bound on `N * A`
  have hchain_low : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ)
      ≤ (N : ℝ) * (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
    calc (N : ℝ) * Real.log (N : ℝ) - (N : ℝ)
        ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := log_factorial_le_sum_log_Icc N hN
      _ = ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := hkey
      _ ≤ (N : ℝ) * ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
          rw [Finset.mul_sum]
          exact sum_le_sum (fun d _ => vonMangoldt_mul_div_le N d)
  -- upper bound on `N * A`
  have hchain_high : (N : ℝ) * (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ))
      ≤ (N : ℝ) * (Real.log (N : ℝ) + (Real.log 4 + 4)) := by
    have h3 : (N : ℝ) * ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d / (d : ℝ)
        ≤ (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ))
          + ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact sum_le_sum (fun d hd => by
        rw [Finset.mem_Icc] at hd
        exact nat_mul_vonMangoldt_div_le N d (by omega))
    calc (N : ℝ) * (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ))
        ≤ (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ))
          + ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d := h3
      _ ≤ (N : ℝ) * Real.log (N : ℝ) + (Real.log 4 + 4) * (N : ℝ) := by
          rw [← hkey]
          exact add_le_add (sum_log_Icc_le N hN1) (sum_vonMangoldt_Icc_le N)
      _ = (N : ℝ) * (Real.log (N : ℝ) + (Real.log 4 + 4)) := by ring
  -- divide by `N > 0`
  have hlow : Real.log (N : ℝ) - 1
      ≤ ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    have h := hchain_low
    have hrw : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) = (N : ℝ) * (Real.log (N : ℝ) - 1) := by ring
    rw [hrw] at h
    exact le_of_mul_le_mul_left h hNpos
  have hhigh : ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)
      ≤ Real.log (N : ℝ) + (Real.log 4 + 4) :=
    le_of_mul_le_mul_left hchain_high hNpos
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_sub_le_iff]
  exact ⟨by linarith [hhigh], by linarith [hlow]⟩

/-! ## The theorem for real `x` -/

theorem sum_vonMangoldt_div_sub_log_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
        - Real.log x‖ ≤ C := by
  refine ⟨Real.log 4 + 4 + Real.log 2, ?_, ?_⟩
  · have h1 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · intro x hx
    have hN1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
    have hxpos : 0 < x := by linarith
    have hNle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hxlt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    rcases eq_or_lt_of_le hN1 with h | h
    · -- case `⌊x⌋₊ = 1`
      have h1 : ⌊x⌋₊ = 1 := h.symm
      have hx2 : x < 2 := by
        have := hxlt
        rw [h1] at this
        norm_num at this
        linarith
      have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
      have hlogx_le : Real.log x ≤ Real.log 2 := Real.log_le_log hxpos (le_of_lt hx2)
      have hsum : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) = 0 := by
        rw [h1]; simp
      rw [hsum, Real.norm_eq_abs]
      simp only [zero_sub, abs_neg, abs_of_nonneg hlogx_nonneg]
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      linarith
    · -- case `⌊x⌋₊ ≥ 2`
      have hN2 : 2 ≤ ⌊x⌋₊ := h
      have hNposR : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < ⌊x⌋₊)
      have hb := sum_vonMangoldt_div_sub_log_nat_bound ⌊x⌋₊ hN2
      have hNge1R : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ ⌊x⌋₊)
      have hxd_lt : x / ((⌊x⌋₊ : ℕ) : ℝ) < 2 := by
        rw [div_lt_iff₀ hNposR]; linarith
      have hlogdiff : |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| ≤ Real.log 2 := by
        have hpos : 0 ≤ Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
          sub_nonneg.mpr (Real.log_le_log hNposR hNle)
        have hle : Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log 2 := by
          rw [← Real.log_div hxpos.ne' hNposR.ne']
          exact Real.log_le_log (div_pos hxpos hNposR) (le_of_lt hxd_lt)
        rw [abs_sub_comm, abs_of_nonneg hpos]
        exact hle
      rw [Real.norm_eq_abs]
      calc |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) - Real.log x|
          ≤ |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
                - Real.log ((⌊x⌋₊ : ℕ) : ℝ)|
              + |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| := by
            rw [show ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
                  - Real.log x
                = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
                    - Real.log ((⌊x⌋₊ : ℕ) : ℝ))
                  + (Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x) by ring]
            exact abs_add_le _ _
        _ ≤ (Real.log 4 + 4) + Real.log 2 := add_le_add hb hlogdiff

end Commons.NumberTheory.ArithmeticFunction