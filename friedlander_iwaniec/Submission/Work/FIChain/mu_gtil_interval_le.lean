/-
# `Work.FIChain.mu_gtil_interval_le`

The `(2.4)`-type sieve estimate for `g̃ = FIgtil` on an **interval** `[y₁, y₂]`, uniform in the
coprimality parameter `ℓ`:

`|Σ_{y₁ ≤ d ≤ y₂, d squarefree, (d,ℓ)=1} μ(d)·g̃(d)| ≤ C·σ̃_ℓ·(log (max y₁ 2))^{-6}`.

The log is taken at the **lower** endpoint (the upper-endpoint form is false: a single large
squarefree `d` contributes `≈ 1/d`).  The estimate is deduced from the prefix form
`Work.FIChain.mu_gtil_coprime_le` by writing the interval sum as the difference of two prefix sums
and comparing the two logarithms; the small cases `y₁ ≤ 2` are absorbed into the constant.
-/
import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.mu_gtil_coprime_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `1 ≤ (log 2)^{-6}` (since `log 2 ≤ 1`). -/
lemma mgil_log_two_rpow_neg_six_ge_one : (1 : ℝ) ≤ (Real.log 2) ^ (-6 : ℝ) := by
  have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have h2 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  have := Real.rpow_le_rpow_of_nonpos h1 h2 (by norm_num : (-6 : ℝ) ≤ 0)
  simpa using this

/-- For `y ≥ 3`: `(log (y-1))^{-6} ≤ 64·(log y)^{-6}`; equivalent to `y ≤ (y-1)²` under `log`,
which lifts the factor `2^6 = 64`. -/
lemma mgil_log_sub_one_rpow_neg_le (y : ℕ) (hy : 3 ≤ y) :
    (Real.log (((y - 1 : ℕ)) : ℝ)) ^ (-6 : ℝ) ≤ 64 * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
  have hy2 : 2 ≤ y - 1 := by omega
  have hcast : (((y - 1 : ℕ)) : ℝ) = (y : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ y)]; norm_num
  have hy3 : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hv0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hvsq : (y : ℝ) ≤ (((y - 1 : ℕ)) : ℝ) ^ 2 := by
    rw [hcast]; nlinarith [hy3]
  have hlog : (Real.log (y : ℝ)) ≤ 2 * Real.log (((y - 1 : ℕ)) : ℝ) := by
    calc Real.log (y : ℝ) ≤ Real.log ((((y - 1 : ℕ)) : ℝ) ^ 2) := Real.log_le_log hv0 hvsq
      _ = 2 * Real.log (((y - 1 : ℕ)) : ℝ) := by rw [Real.log_pow]; ring
  have hhalf : Real.log (y : ℝ) / 2 ≤ Real.log (((y - 1 : ℕ)) : ℝ) := by linarith
  have hpos : 0 < Real.log (y : ℝ) / 2 := by
    have h : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith [hy3])
    linarith
  have hmono := Real.rpow_le_rpow_of_nonpos hpos hhalf (by norm_num : (-6 : ℝ) ≤ 0)
  have hkey : (Real.log (y : ℝ) / 2) ^ (-6 : ℝ) = 64 * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
    have h3 : Real.log (y : ℝ) / 2 = (1 / 2) * Real.log (y : ℝ) := by ring
    rw [h3, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (Real.log_nonneg (by linarith [hy3]))]
    rw [show ((1 : ℝ) / 2) ^ (-6 : ℝ) = (64 : ℝ) by norm_num [Real.rpow_neg, Real.rpow_natCast]]
  linarith [hmono, hkey]

/-- The comparison of the two endpoint logarithms: for `y ≥ 1`,
`(log (max (y-1) 2))^{-6} ≤ 64·(log (max y 2))^{-6}`. -/
lemma mgil_log_max_sub_one_rpow_neg_le (y : ℕ) (hy : 1 ≤ y) :
    (Real.log (((max (y - 1) 2 : ℕ)) : ℝ)) ^ (-6 : ℝ)
      ≤ 64 * (Real.log (((max y 2 : ℕ)) : ℝ)) ^ (-6 : ℝ) := by
  by_cases hy2 : y ≤ 2
  · have e1 : (max (y - 1) 2 : ℕ) = 2 := by omega
    have e2 : (max y 2 : ℕ) = 2 := by omega
    rw [e1, e2]; push_cast
    nlinarith [Real.rpow_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (-6)]
  · have hy3 : 3 ≤ y := by omega
    have e1 : (max (y - 1) 2 : ℕ) = y - 1 := by omega
    have e2 : (max y 2 : ℕ) = y := by omega
    rw [e1, e2]
    exact mgil_log_sub_one_rpow_neg_le y hy3

/-- Interval splitting: `Σ_{a..b} = Σ_{1..b} − Σ_{1..a−1}` for `1 ≤ a ≤ b+1`. -/
lemma mgil_sum_Icc_eq_sub (g : ℕ → ℝ) (a b : ℕ) (h : 1 ≤ a) (h2 : a ≤ b + 1) :
    ∑ d ∈ Finset.Icc a b, g d
      = (∑ d ∈ Finset.Icc 1 b, g d) - (∑ d ∈ Finset.Icc 1 (a - 1), g d) := by
  have hsub : Finset.Icc 1 (a - 1) ⊆ Finset.Icc 1 b := by
    intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, by omega⟩
  have hsdiff : Finset.Icc 1 b \ Finset.Icc 1 (a - 1) = Finset.Icc a b := by
    ext d
    rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    omega
  have hsum := Finset.sum_sdiff (f := g) hsub
  rw [hsdiff] at hsum
  linarith [hsum]

/-- **`(2.4)` on an interval** (`g̃ = FIgtil`, coprimality parameter `ℓ`), with the log at the
*lower* endpoint (the upper-endpoint form is FALSE — a single large squarefree `d` contributes
`≈ 1/d`).  For `y₁ ≤ 2` the `max y₁ 2` keeps the statement usable. -/
theorem mu_gtil_interval_le : ∃ C : ℝ, 0 < C ∧ ∀ (ℓ y₁ y₂ : ℕ), 1 ≤ ℓ → 1 ≤ y₁ → y₁ ≤ y₂ →
    |∑ d ∈ (Finset.Icc y₁ y₂).filter (fun d => Squarefree d ∧ Nat.Coprime d ℓ),
        (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil d|
      ≤ C * Work.FIChain.sigmaTilde ℓ * (Real.log (((max y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FIChain.mu_gtil_coprime_le
  refine ⟨65 * max C₀ 1, by positivity, ?_⟩
  intro ℓ y₁ y₂ hℓ hy₁ hy₁₂
  set P : ℕ → Prop := fun d => Squarefree d ∧ Nat.Coprime d ℓ with hP
  set f : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil d with hf
  set A : ℕ → ℝ := fun n => ∑ d ∈ (Finset.Icc 1 n).filter P, f d with hA
  have hAval : ∀ n : ℕ, A n = ∑ d ∈ (Finset.Icc 1 n).filter P, f d := fun n => by simp only [hA]
  have hσ1 : (1 : ℝ) ≤ Work.FIChain.sigmaTilde ℓ := by
    rw [Work.FIChain.sigmaTilde]
    calc (1 : ℝ) = ∏ _p ∈ ℓ.primeFactors, (1 : ℝ) := by simp
      _ ≤ ∏ p ∈ ℓ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
          Finset.prod_le_prod₀ (fun p _ => by norm_num) (fun p _ => by
            have : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by positivity
            linarith)
  have hσ0 : (0 : ℝ) < Work.FIChain.sigmaTilde ℓ := lt_of_lt_of_le zero_lt_one hσ1
  have hbound : ∀ n : ℕ, |A n| ≤ max C₀ 1 * Work.FIChain.sigmaTilde ℓ
      * (Real.log (((max n 2 : ℕ)) : ℝ)) ^ (-6 : ℝ) := by
    intro n
    by_cases hn : 2 ≤ n
    · have h := hC₀ ℓ (n : ℝ) hℓ (by exact_mod_cast hn)
      rw [Nat.floor_natCast] at h
      have hmax : (max n 2 : ℕ) = n := by omega
      rw [hmax]
      have hL : (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ (-6 : ℝ) :=
        Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) _
      have hh : |A n| ≤ C₀ * Work.FIChain.sigmaTilde ℓ * (Real.log (n : ℝ)) ^ (-6 : ℝ) := by
        rw [hAval n]; simpa only [hP, hf] using h
      calc |A n| ≤ C₀ * Work.FIChain.sigmaTilde ℓ * (Real.log (n : ℝ)) ^ (-6 : ℝ) := hh
        _ ≤ max C₀ 1 * Work.FIChain.sigmaTilde ℓ * (Real.log (n : ℝ)) ^ (-6 : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (le_of_lt hσ0)) hL
    · have hn1 : n ≤ 1 := by omega
      have hmax : (max n 2 : ℕ) = 2 := by omega
      rw [hmax]; push_cast
      have hsmall : |A n| ≤ 1 := by
        interval_cases n
        · have h0 : A 0 = 0 := by rw [hAval]; simp
          rw [h0]; norm_num
        · have hP1 : P 1 := by rw [hP]; exact ⟨squarefree_one, Nat.coprime_one_left ℓ⟩
          have h1 : A 1 = 1 := by
            rw [hAval]
            rw [Finset.Icc_self, Finset.filter_singleton, if_pos hP1, Finset.sum_singleton, hf]
            simp [Submission.ASP.FIgtil_one]
          rw [h1]; norm_num
      have hlog2 : (1 : ℝ) ≤ (Real.log 2) ^ (-6 : ℝ) := mgil_log_two_rpow_neg_six_ge_one
      have hRHS : (1 : ℝ) ≤ max C₀ 1 * Work.FIChain.sigmaTilde ℓ * (Real.log 2) ^ (-6 : ℝ) := by
        have hK : (1 : ℝ) ≤ max C₀ 1 := le_max_right _ _
        have h1 : (1 : ℝ) ≤ max C₀ 1 * Work.FIChain.sigmaTilde ℓ := by nlinarith [hK, hσ1]
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (max C₀ 1 * Work.FIChain.sigmaTilde ℓ) * (Real.log 2) ^ (-6 : ℝ) :=
              mul_le_mul h1 hlog2 (by norm_num) (by positivity)
      linarith [hsmall, hRHS]
  have hsplit : ∑ d ∈ (Finset.Icc y₁ y₂).filter P, f d = A y₂ - A (y₁ - 1) := by
    rw [hAval y₂, hAval (y₁ - 1)]
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    exact mgil_sum_Icc_eq_sub (fun d => if P d then f d else 0) y₁ y₂ hy₁ (by omega)
  rw [hsplit]
  have hb2 : |A y₂| ≤ max C₀ 1 * Work.FIChain.sigmaTilde ℓ
      * (Real.log (((max y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ) := by
    refine le_trans (hbound y₂) (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_nonpos
      (Real.log_pos (by exact_mod_cast (by omega : 1 < max y₁ 2)))
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < max y₁ 2))
        (by exact_mod_cast (by omega : max y₁ 2 ≤ max y₂ 2)))
      (by norm_num)
  have hb1 : |A (y₁ - 1)| ≤ max C₀ 1 * Work.FIChain.sigmaTilde ℓ
      * (64 * (Real.log (((max y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ)) := by
    refine le_trans (hbound (y₁ - 1)) (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mgil_log_max_sub_one_rpow_neg_le y₁ hy₁
  calc |A y₂ - A (y₁ - 1)| ≤ |A y₂| + |A (y₁ - 1)| := abs_sub _ _
    _ ≤ max C₀ 1 * Work.FIChain.sigmaTilde ℓ * (Real.log (((max y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ)
        + max C₀ 1 * Work.FIChain.sigmaTilde ℓ
          * (64 * (Real.log (((max y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ)) := add_le_add hb2 hb1
    _ = 65 * max C₀ 1 * Work.FIChain.sigmaTilde ℓ
          * (Real.log (((max y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ) := by ring

end

end Work.FIChain
