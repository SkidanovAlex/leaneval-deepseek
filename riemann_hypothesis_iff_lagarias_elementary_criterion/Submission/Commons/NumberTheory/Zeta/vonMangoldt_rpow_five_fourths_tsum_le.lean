import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped BigOperators
open MeasureTheory

namespace Commons.NumberTheory.Zeta

/-!
# The von Mangoldt series at `5/4`

We prove the explicit bound `∑' n, Λ n / n ^ (5/4) ≤ 27`.

The argument is elementary.  Using the sharp form of the logarithmic
inequality `log x ≤ x ^ a / (a * e)` (with `a = 1/8`) together with
Mathlib's `Λ n ≤ log n`, each term is bounded by

`Λ n / n ^ (5/4) = Λ n · n ^ (-(5/4)) ≤ 8/e · n ^ (-(9/8))`.

The `p`-series `∑ n ^ (-(9/8))` is bounded by `9` via the integral test, and
`(8/e)·9 = 72/e ≤ 27` since `e ≥ 8/3`.
-/

/-- The sharp logarithmic inequality: for `x > 0` and `a > 0`,
`log x ≤ x ^ a / (a * exp 1)`.

It is equivalent to `log (x ^ a / e) ≤ x ^ a / e - 1`, i.e. Mathlib's
`Real.log_le_sub_one_of_pos`. -/
private lemma log_le_rpow_div_mul_exp {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ x ^ a / (a * Real.exp 1) := by
  have hxpow : 0 < x ^ a := Real.rpow_pos_of_pos hx a
  have hu : 0 < x ^ a / Real.exp 1 := div_pos hxpow (Real.exp_pos 1)
  have h := Real.log_le_sub_one_of_pos hu
  rw [Real.log_div hxpow.ne' (Real.exp_ne_zero 1), Real.log_rpow hx a, Real.log_exp] at h
  have h2 : Real.log x * a ≤ x ^ a / Real.exp 1 := by linarith
  calc Real.log x ≤ x ^ a / Real.exp 1 / a := (le_div_iff₀ ha).mpr h2
    _ = x ^ a / (a * Real.exp 1) := by rw [div_div, mul_comm (Real.exp 1) a]

/-- The real `p`-series `∑_{n ≥ 0} n ^ (-(9/8))` is at most `9`.

The integral test bounds the tail `∑_{n ≥ 2} n ^ (-(9/8))` by
`∫_{[1,∞)} x ^ (-(9/8)) dx = 8`, and the remaining terms `n = 0, 1` contribute `0 + 1 = 1`. -/
private lemma psum_neg_nine_eighths_le : (∑' n : ℕ, (n : ℝ) ^ (-((9 : ℝ) / 8))) ≤ 9 := by
  have hS : Summable (fun n : ℕ => (n : ℝ) ^ (-((9 : ℝ) / 8))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-((9 : ℝ) / 8))) (Set.Ici ((1 : ℕ) : ℝ)) := by
    intro a ha b _ hab
    have ha1 : (1 : ℝ) ≤ a := by simpa using Set.mem_Ici.mp ha
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by norm_num)
  have hint : IntegrableOn (fun x : ℝ => x ^ (-((9 : ℝ) / 8))) (Set.Ioi ((1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-((9 : ℝ) / 8)) < -1)
      (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))
  have hnonneg : ∀ t ∈ Set.Ioi (((1 : ℕ)) : ℝ), 0 ≤ t ^ (-((9 : ℝ) / 8)) :=
    fun t ht => Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) _
  have hb := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ => x ^ (-((9 : ℝ) / 8))) 1 hanti hint hnonneg
  have hiv : ∫ x in Set.Ioi (((1 : ℕ)) : ℝ), x ^ (-((9 : ℝ) / 8)) = 8 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-((9 : ℝ) / 8)) < -1)
      (by norm_num : (0 : ℝ) < ((1 : ℕ)))]
    norm_num
  rw [hiv] at hb
  have hfin : ∑ i ∈ Finset.range 2, (i : ℝ) ^ (-((9 : ℝ) / 8)) = 1 := by
    simp [Finset.sum_range_succ]
  have hshift := hS.sum_add_tsum_nat_add 2
  have htail : ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-((9 : ℝ) / 8)) ≤ 8 := hb
  calc ∑' n : ℕ, (n : ℝ) ^ (-((9 : ℝ) / 8))
      = (∑ i ∈ Finset.range 2, (i : ℝ) ^ (-((9 : ℝ) / 8)))
          + ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-((9 : ℝ) / 8)) := hshift.symm
    _ = 1 + ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-((9 : ℝ) / 8)) := by rw [hfin]
    _ ≤ 1 + 8 := by linarith [htail]
    _ = 9 := by norm_num

/-- Pointwise bound: `Λ n · n ^ (-(5/4)) ≤ 8/e · n ^ (-(9/8))`. -/
private lemma vm_term_le_five_fourths (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((5 : ℝ) / 4))
      ≤ (8 / Real.exp 1) * (n : ℝ) ^ (-((9 : ℝ) / 8)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by simp
    rw [h0, Nat.cast_zero, Real.zero_rpow (by norm_num : (-((5 : ℝ) / 4)) ≠ 0),
      Real.zero_rpow (by norm_num : (-((9 : ℝ) / 8)) ≠ 0)]
    simp
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlog : Real.log (n : ℝ) ≤ (8 / Real.exp 1) * (n : ℝ) ^ ((1 : ℝ) / 8) := by
      have h := log_le_rpow_div_mul_exp (x := (n : ℝ)) (a := (1 : ℝ) / 8)
        hnpos (by norm_num)
      have heq : (n : ℝ) ^ ((1 : ℝ) / 8) / (((1 : ℝ) / 8) * Real.exp 1)
          = (8 / Real.exp 1) * (n : ℝ) ^ ((1 : ℝ) / 8) := by
        have h8 : (((1 : ℝ) / 8))⁻¹ = 8 := by norm_num
        rw [div_eq_mul_inv, mul_inv_rev, h8, div_eq_mul_inv]
        ring
      rwa [heq] at h
    have hlog2 : (ArithmeticFunction.vonMangoldt n : ℝ)
        ≤ (8 / Real.exp 1) * (n : ℝ) ^ ((1 : ℝ) / 8) :=
      le_trans ArithmeticFunction.vonMangoldt_le_log hlog
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((5 : ℝ) / 4))
        ≤ ((8 / Real.exp 1) * (n : ℝ) ^ ((1 : ℝ) / 8)) * (n : ℝ) ^ (-((5 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_right hlog2 (Real.rpow_nonneg hnpos.le _)
      _ = (8 / Real.exp 1) * ((n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ (-((5 : ℝ) / 4))) := by
          ring
      _ = (8 / Real.exp 1) * (n : ℝ) ^ ((1 : ℝ) / 8 + -((5 : ℝ) / 4)) := by
          rw [← Real.rpow_add hnpos]
      _ = (8 / Real.exp 1) * (n : ℝ) ^ (-((9 : ℝ) / 8)) := by
          have : (1 : ℝ) / 8 + -((5 : ℝ) / 4) = -((9 : ℝ) / 8) := by norm_num
          rw [this]

theorem vonMangoldt_rpow_five_fourths_tsum_le :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ ((5 : ℝ) / 4)) ≤ 27 := by
  have hconv : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ ((5 : ℝ) / 4))
      = fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((5 : ℝ) / 4)) := by
    funext n
    rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n) ((5 : ℝ) / 4)]
  rw [hconv]
  have hle : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((5 : ℝ) / 4))
      ≤ (8 / Real.exp 1) * (n : ℝ) ^ (-((9 : ℝ) / 8)) := vm_term_le_five_fourths
  have hgsum : Summable (fun n : ℕ => (8 / Real.exp 1) * (n : ℝ) ^ (-((9 : ℝ) / 8))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-((9 : ℝ) / 8)) < -1)).mul_left _
  have hfsum : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((5 : ℝ) / 4))) :=
    Summable.of_nonneg_of_le
      (f := fun n : ℕ => (8 / Real.exp 1) * (n : ℝ) ^ (-((9 : ℝ) / 8)))
      (g := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((5 : ℝ) / 4)))
      (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      hle hgsum
  calc (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((5 : ℝ) / 4)))
      ≤ ∑' n : ℕ, (8 / Real.exp 1) * (n : ℝ) ^ (-((9 : ℝ) / 8)) :=
        Summable.tsum_le_tsum hle hfsum hgsum
    _ = (8 / Real.exp 1) * (∑' n : ℕ, (n : ℝ) ^ (-((9 : ℝ) / 8))) := by rw [tsum_mul_left]
    _ ≤ (8 / Real.exp 1) * 9 := by
        exact mul_le_mul_of_nonneg_left psum_neg_nine_eighths_le (by positivity)
    _ ≤ 27 := by
        have he : (8 : ℝ) / 3 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have hpos : 0 < Real.exp 1 := Real.exp_pos 1
        rw [div_mul_eq_mul_div]
        rw [div_le_iff₀ hpos]
        nlinarith

end Commons.NumberTheory.Zeta
