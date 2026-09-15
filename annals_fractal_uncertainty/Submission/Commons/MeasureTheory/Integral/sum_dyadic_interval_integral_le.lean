import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
open scoped Interval BigOperators

namespace Commons.MeasureTheory.Integral

/-- For a nonnegative function `f` integrable on the positive half-line, the integral of `f`
over any `Ioc a b` with `0 < a` is at most the integral over the whole half-line. -/
lemma setIntegral_Ioc_le_setIntegral_Ioi {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hint : IntegrableOn f (Set.Ioi (0 : ℝ)) volume)
    {a b : ℝ} (ha : 0 < a) :
    ∫ r in Set.Ioc a b, f r ≤ ∫ r in Set.Ioi (0 : ℝ), f r := by
  refine setIntegral_mono_set hint (Filter.Eventually.of_forall hf) ?_
  exact Filter.Eventually.of_forall (fun x hx => lt_trans ha hx.1)

/-- Same bound as `setIntegral_Ioc_le_setIntegral_Ioi`, phrased for an interval integral. -/
lemma intervalIntegral_le_integral_Ioi {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hint : IntegrableOn f (Set.Ioi (0 : ℝ)) volume)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ r in a..b, f r ≤ ∫ r in Set.Ioi (0 : ℝ), f r := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_Ioc_le_setIntegral_Ioi hf hint ha

/-- Interval-integrability on `[a,b]` with `0 < a`, inherited from integrability on `(0,∞)`. -/
lemma intervalIntegrable_of_integrableOn_Ioi {f : ℝ → ℝ}
    (hint : IntegrableOn f (Set.Ioi (0 : ℝ)) volume)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact hint.mono_set (fun x hx => lt_trans ha hx.1)

/-- The dyadic intervals `[2^{k-1}, 2^{k+1}]`, `k = 1, …, K`, split into the two disjoint
dyadic families `[2^{k-1}, 2^k]` and `[2^k, 2^{k+1}]`, telescoping to
`[1, 2^K]` and `[2, 2^{K+1}]` respectively. -/
lemma dyadic_sum_intervalIntegral_eq (f : ℝ → ℝ)
    (hint : IntegrableOn f (Set.Ioi (0 : ℝ)) volume) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), f r)
      = (∫ r in (1 : ℝ)..(2 : ℝ) ^ K, f r)
        + ∫ r in (2 : ℝ)..(2 : ℝ) ^ (K + 1), f r := by
  induction K with
  | zero => simp [intervalIntegral.integral_same]
  | succ K IH =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), IH]
    simp only [Nat.add_sub_cancel]
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have hpow1 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hmono : (2 : ℝ) ^ K ≤ 2 ^ (K + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ K)
    have hmono2 : (2 : ℝ) ^ (K + 1) ≤ 2 ^ ((K + 1) + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ (K + 1))
    have h2le : (2 : ℝ) ≤ 2 ^ (K + 1) := by
      have hK : (1 : ℕ) ≤ K + 1 := by omega
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hK
      simpa using this
    have h1 : (∫ r in (1 : ℝ)..(2 : ℝ) ^ K, f r)
        + (∫ r in (2 : ℝ) ^ K..(2 : ℝ) ^ (K + 1), f r)
        = ∫ r in (1 : ℝ)..(2 : ℝ) ^ (K + 1), f r :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_integrableOn_Ioi hint (a := 1) (b := 2 ^ K) (by norm_num) hpow1)
        (intervalIntegrable_of_integrableOn_Ioi hint (a := 2 ^ K) (b := 2 ^ (K + 1))
          (pow_pos h2pos K) hmono)
    have h2 : (∫ r in (2 : ℝ)..(2 : ℝ) ^ (K + 1), f r)
        + (∫ r in (2 : ℝ) ^ (K + 1)..(2 : ℝ) ^ ((K + 1) + 1), f r)
        = ∫ r in (2 : ℝ)..(2 : ℝ) ^ ((K + 1) + 1), f r :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_integrableOn_Ioi hint (a := 2) (b := 2 ^ (K + 1)) h2pos h2le)
        (intervalIntegrable_of_integrableOn_Ioi hint (a := 2 ^ (K + 1)) (b := 2 ^ ((K + 1) + 1))
          (pow_pos h2pos (K + 1)) hmono2)
    have h3 : (∫ r in (2 : ℝ) ^ K..(2 : ℝ) ^ ((K + 1) + 1), f r)
        = (∫ r in (2 : ℝ) ^ K..(2 : ℝ) ^ (K + 1), f r)
          + (∫ r in (2 : ℝ) ^ (K + 1)..(2 : ℝ) ^ ((K + 1) + 1), f r) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_integrableOn_Ioi hint (a := 2 ^ K) (b := 2 ^ (K + 1))
          (pow_pos h2pos K) hmono)
        (intervalIntegrable_of_integrableOn_Ioi hint (a := 2 ^ (K + 1)) (b := 2 ^ ((K + 1) + 1))
          (pow_pos h2pos (K + 1)) hmono2)).symm
    calc ((∫ r in (1 : ℝ)..(2 : ℝ) ^ K, f r)
            + (∫ r in (2 : ℝ)..(2 : ℝ) ^ (K + 1), f r))
          + (∫ r in (2 : ℝ) ^ K..(2 : ℝ) ^ ((K + 1) + 1), f r)
        = ((∫ r in (1 : ℝ)..(2 : ℝ) ^ K, f r)
            + (∫ r in (2 : ℝ)..(2 : ℝ) ^ (K + 1), f r))
          + ((∫ r in (2 : ℝ) ^ K..(2 : ℝ) ^ (K + 1), f r)
            + (∫ r in (2 : ℝ) ^ (K + 1)..(2 : ℝ) ^ ((K + 1) + 1), f r)) := by rw [h3]
      _ = ((∫ r in (1 : ℝ)..(2 : ℝ) ^ K, f r)
            + (∫ r in (2 : ℝ) ^ K..(2 : ℝ) ^ (K + 1), f r))
          + ((∫ r in (2 : ℝ)..(2 : ℝ) ^ (K + 1), f r)
            + (∫ r in (2 : ℝ) ^ (K + 1)..(2 : ℝ) ^ ((K + 1) + 1), f r)) := by ring
      _ = (∫ r in (1 : ℝ)..(2 : ℝ) ^ (K + 1), f r)
          + (∫ r in (2 : ℝ)..(2 : ℝ) ^ ((K + 1) + 1), f r) := by rw [h1, h2]

theorem sum_dyadic_interval_integral_le (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) MeasureTheory.volume) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), f r)
      ≤ 2 * ∫ r in Set.Ioi (0 : ℝ), f r := by
  rw [dyadic_sum_intervalIntegral_eq f hint K]
  have h1 : (∫ r in (1 : ℝ)..(2 : ℝ) ^ K, f r) ≤ ∫ r in Set.Ioi (0 : ℝ), f r :=
    intervalIntegral_le_integral_Ioi hf hint (by norm_num)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have h2 : (∫ r in (2 : ℝ)..(2 : ℝ) ^ (K + 1), f r) ≤ ∫ r in Set.Ioi (0 : ℝ), f r := by
    refine intervalIntegral_le_integral_Ioi hf hint (by norm_num) ?_
    have hK : (1 : ℕ) ≤ K + 1 := by omega
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hK
    simpa using this
  calc (∫ r in (1 : ℝ)..(2 : ℝ) ^ K, f r) + (∫ r in (2 : ℝ)..(2 : ℝ) ^ (K + 1), f r)
      ≤ (∫ r in Set.Ioi (0 : ℝ), f r) + (∫ r in Set.Ioi (0 : ℝ), f r) := add_le_add h1 h2
    _ = 2 * ∫ r in Set.Ioi (0 : ℝ), f r := by ring

end Commons.MeasureTheory.Integral