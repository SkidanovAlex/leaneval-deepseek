import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped BigOperators
open MeasureTheory

namespace Commons.NumberTheory.ArithmeticFunction

/-!
# The von Mangoldt series at real part `≥ 3/2`

We prove the explicit bound
`∑' n, Λ n · n ^ (-σ) ≤ 20` for every real `σ ≥ 3/2`.

The proof is completely elementary.  Since `Λ n ≤ log n` and `log n ≤ 4 n ^ (1/4)`
(Mathlib's `Real.log_le_rpow_div` with `ε = 1/4`), each term is bounded by

`Λ n · n ^ (-σ) ≤ 4 n ^ (1/4 - σ) ≤ 4 n ^ (-5/4)`  (`σ ≥ 3/2`, `n ≥ 1`),

and the `p`-series `∑ n ^ (-5/4)` is bounded by `5` using the integral test
(`AntitoneOn.tsum_comp_add_le_integral` applied to `x ↦ x ^ (-5/4)` on `[1, ∞)`).
Hence the sum is at most `4 · 5 = 20`.
-/

/-- The real `p`-series `∑_{n ≥ 0} n ^ (-5/4)` is at most `5`.

The integral test bounds the tail `∑_{n ≥ 2} n ^ (-5/4)` by
`∫_{[1,∞)} x ^ (-5/4) dx = 4`, and the remaining terms `n = 0, 1` contribute `0 + 1 = 1`. -/
private lemma psum_le_five : (∑' n : ℕ, (n : ℝ) ^ (-(5 : ℝ) / 4)) ≤ 5 := by
  have hS : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 : ℝ) / 4)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(5 : ℝ) / 4)) (Set.Ici ((1 : ℕ) : ℝ)) := by
    intro a ha b _ hab
    have ha1 : (1 : ℝ) ≤ a := by simpa using Set.mem_Ici.mp ha
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by norm_num)
  have hint : IntegrableOn (fun x : ℝ => x ^ (-(5 : ℝ) / 4)) (Set.Ioi ((1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-(5 : ℝ) / 4) < -1)
      (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))
  have hnonneg : ∀ t ∈ Set.Ioi (((1 : ℕ)) : ℝ), 0 ≤ t ^ (-(5 : ℝ) / 4) :=
    fun t ht => Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) _
  have hb := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ => x ^ (-(5 : ℝ) / 4)) 1 hanti hint hnonneg
  have hiv : ∫ x in Set.Ioi (((1 : ℕ)) : ℝ), x ^ (-(5 : ℝ) / 4) = 4 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-(5 : ℝ) / 4) < -1)
      (by norm_num : (0 : ℝ) < ((1 : ℕ)))]
    norm_num
  rw [hiv] at hb
  have hfin : ∑ i ∈ Finset.range 2, (i : ℝ) ^ (-(5 : ℝ) / 4) = 1 := by
    simp [Finset.sum_range_succ]
  have hshift := hS.sum_add_tsum_nat_add 2
  have htail : ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-(5 : ℝ) / 4) ≤ 4 := hb
  calc ∑' n : ℕ, (n : ℝ) ^ (-(5 : ℝ) / 4)
      = (∑ i ∈ Finset.range 2, (i : ℝ) ^ (-(5 : ℝ) / 4))
          + ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-(5 : ℝ) / 4) := hshift.symm
    _ = 1 + ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-(5 : ℝ) / 4) := by rw [hfin]
    _ ≤ 1 + 4 := by linarith [htail]
    _ = 5 := by norm_num

/-- Pointwise bound: for `σ ≥ 3/2`, `Λ n · n ^ (-σ) ≤ 4 n ^ (-5/4)`. -/
private lemma vm_term_le {σ : ℝ} (hσ : (3 : ℝ) / 2 ≤ σ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
      ≤ 4 * (n : ℝ) ^ (-(5 : ℝ) / 4) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0Λ : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
      rw [ArithmeticFunction.vonMangoldt_apply]
      split_ifs with h
      · exact absurd h not_isPrimePow_zero
      · rfl
    rw [h0Λ, Nat.cast_zero, Real.zero_rpow (by linarith : (-σ) ≠ 0),
        Real.zero_rpow (by norm_num : (-(5 : ℝ) / 4) ≠ 0)]
    norm_num
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have h := Real.log_le_rpow_div (x := (n : ℝ)) (ε := (1 : ℝ) / 4)
        (Nat.cast_nonneg n) (by norm_num)
      rw [div_eq_mul_inv, show (((1 : ℝ) / 4 : ℝ)⁻¹) = 4 by norm_num, mul_comm] at h
      exact h
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = 4 * (n : ℝ) ^ ((1 : ℝ) / 4 - σ) := by
          rw [mul_assoc, ← Real.rpow_add hnpos]
          rw [show (1 : ℝ) / 4 + (-σ) = (1 : ℝ) / 4 - σ by ring]
      _ ≤ 4 * (n : ℝ) ^ (-(5 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by norm_num)

theorem tsum_vonMangoldt_rpow_neg_le {σ : ℝ} (hσ : (3 : ℝ) / 2 ≤ σ) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) ≤ 20 := by
  have hle : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        ≤ 4 * (n : ℝ) ^ (-(5 : ℝ) / 4) := fun n => vm_term_le hσ n
  have hg : Summable (fun n : ℕ => 4 * (n : ℝ) ^ (-(5 : ℝ) / 4)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(5 : ℝ) / 4) < -1)).mul_left 4
  have hf : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hle hg
  calc ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
      ≤ ∑' n : ℕ, 4 * (n : ℝ) ^ (-(5 : ℝ) / 4) :=
        Summable.tsum_le_tsum hle hf hg
    _ = 4 * ∑' n : ℕ, (n : ℝ) ^ (-(5 : ℝ) / 4) := by rw [tsum_mul_left]
    _ ≤ 4 * 5 := by linarith [psum_le_five]
    _ = 20 := by norm_num

end Commons.NumberTheory.ArithmeticFunction