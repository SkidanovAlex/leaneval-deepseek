import Mathlib
import Submission.Commons.Analysis.Series.tail_inv_sq_le
import Submission.Commons.Analysis.Series.tail_inv_sq_summable

namespace Commons.Analysis.Hilbert

theorem tsum_int_ofReal_natAbs_inv_sq_le (a : ℕ) (ha : 1 ≤ a) :
    (∑' x : ℤ, (if 2 * a ≤ x.natAbs then
        ENNReal.ofReal (2 * (a : ℝ) / ((x.natAbs : ℝ)) ^ 2) else 0))
      ≤ ENNReal.ofReal 4 := by
  set h : ℤ → ℝ :=
    fun x => if 2 * a ≤ x.natAbs then 2 * (a : ℝ) / ((x.natAbs : ℝ)) ^ 2 else 0 with hh
  -- Summability building blocks.
  have hf0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hfl : Summable (fun n : ℕ => 2 * (a : ℝ) * (1 / (n : ℝ) ^ 2)) :=
    hf0.mul_left (2 * (a : ℝ))
  have hf1 : Summable (fun n : ℕ => 2 * (a : ℝ) * (1 / (((n + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h2 := (summable_nat_add_iff 1).mpr hfl
    simpa using h2
  -- Nonnegativity.
  have hnn : ∀ x, 0 ≤ h x := by
    intro x; simp only [hh]
    by_cases hx : 2 * a ≤ x.natAbs
    · rw [if_pos hx]; positivity
    · rw [if_neg hx]
  -- Pointwise bounds by summable functions.
  have hpos_le : ∀ i : ℕ, h (i : ℤ) ≤ 2 * (a : ℝ) * (1 / (i : ℝ) ^ 2) := by
    intro i; simp only [hh, Int.natAbs_natCast]
    by_cases hi : 2 * a ≤ i
    · rw [if_pos hi, div_eq_mul_one_div]
    · rw [if_neg hi]; positivity
  have hneg_na : ∀ i : ℕ, ((-(i + 1 : ℤ))).natAbs = i + 1 := by
    intro i
    rw [show (-(i + 1 : ℤ)) = -(↑i + 1) from by ring]
    rw [show (-(↑i + 1 : ℤ)) = Int.negSucc i from (Int.negSucc_eq i).symm]
    exact Int.natAbs_negSucc i
  have hneg_le : ∀ i : ℕ, h (-(i + 1 : ℤ)) ≤ 2 * (a : ℝ) * (1 / (((i + 1 : ℕ)) : ℝ) ^ 2) := by
    intro i; simp only [hh]; rw [hneg_na i]
    by_cases hi : 2 * a ≤ i + 1
    · rw [if_pos hi, div_eq_mul_one_div]
    · rw [if_neg hi]; positivity
  have hpos_summ : Summable (fun i : ℕ => h (i : ℤ)) :=
    Summable.of_nonneg_of_le (fun i => hnn _) hpos_le hfl
  have hneg_summ : Summable (fun i : ℕ => h (-(i + 1 : ℤ))) :=
    Summable.of_nonneg_of_le (fun i => hnn _) hneg_le hf1
  -- The `ℤ ≃ ℕ ⊕ ℕ` identification.
  have hcomp : ∀ c : ℕ ⊕ ℕ, h (Equiv.intEquivNatSumNat.symm c)
      = Sum.elim (fun i : ℕ => h (i : ℤ)) (fun i : ℕ => h (-(i + 1 : ℤ))) c := by
    intro c; rcases c with i | i
    · rfl
    · show h (Int.negSucc i) = h (-(↑i + 1))
      rw [Int.negSucc_eq]
  have hsumm_h : Summable h := by
    rw [← Equiv.summable_iff Equiv.intEquivNatSumNat.symm]
    have hs := Summable.sum
      (Sum.elim (fun i : ℕ => h (i : ℤ)) (fun i : ℕ => h (-(i + 1 : ℤ)))) hpos_summ hneg_summ
    have heq : (h ∘ ⇑Equiv.intEquivNatSumNat.symm)
        = Sum.elim (fun i : ℕ => h (i : ℤ)) (fun i : ℕ => h (-(i + 1 : ℤ))) := by
      funext c; exact hcomp c
    rw [heq]; exact hs
  -- Split the `ℤ`-sum into two `ℕ`-sums.
  have hdecomp : (∑' x : ℤ, h x)
      = (∑' i : ℕ, h (i : ℤ)) + (∑' i : ℕ, h (-(i + 1 : ℤ))) := by
    rw [← Equiv.tsum_eq Equiv.intEquivNatSumNat.symm h]
    rw [tsum_congr (fun c => hcomp c)]
    exact Summable.tsum_sum hpos_summ hneg_summ
  -- Value of the two half-line sums.
  have hψ_summ : Summable (fun i : ℕ => (if 2 * a ≤ i then (1 : ℝ) / (i : ℝ) ^ 2 else 0)) :=
    Commons.Analysis.Series.tail_inv_sq_summable (2 * a)
  have hS : (∑' i : ℕ, (if 2 * a ≤ i then (1 : ℝ) / (i : ℝ) ^ 2 else 0))
      ≤ 2 / (2 * (2 * (a : ℝ)) - 1) := by
    have h0 := Commons.Analysis.Series.tail_inv_sq_le (2 * a) (by omega)
    have hcast : ((2 * a : ℕ) : ℝ) = 2 * (a : ℝ) := by push_cast; ring
    rwa [hcast] at h0
  have hpos_val : (∑' i : ℕ, h (i : ℤ))
      = 2 * (a : ℝ) * (∑' i : ℕ, (if 2 * a ≤ i then (1 : ℝ) / (i : ℝ) ^ 2 else 0)) := by
    rw [show (∑' i : ℕ, h (i : ℤ))
        = ∑' i : ℕ, 2 * (a : ℝ) * (if 2 * a ≤ i then (1 : ℝ) / (i : ℝ) ^ 2 else 0) from by
      apply tsum_congr; intro i
      simp only [hh, Int.natAbs_natCast]
      by_cases hi : 2 * a ≤ i
      · rw [if_pos hi, if_pos hi, div_eq_mul_one_div]
      · rw [if_neg hi, if_neg hi, mul_zero]]
    rw [tsum_mul_left]
  have hneg_val : (∑' i : ℕ, h (-(i + 1 : ℤ)))
      = 2 * (a : ℝ)
        * (∑' i : ℕ, (if 2 * a ≤ i + 1 then (1 : ℝ) / (((i + 1 : ℕ)) : ℝ) ^ 2 else 0)) := by
    rw [show (∑' i : ℕ, h (-(i + 1 : ℤ)))
        = ∑' i : ℕ, 2 * (a : ℝ)
            * (if 2 * a ≤ i + 1 then (1 : ℝ) / (((i + 1 : ℕ)) : ℝ) ^ 2 else 0) from by
      apply tsum_congr; intro i
      simp only [hh]; rw [hneg_na i]
      by_cases hi : 2 * a ≤ i + 1
      · rw [if_pos hi, if_pos hi, div_eq_mul_one_div]
      · rw [if_neg hi, if_neg hi, mul_zero]]
    rw [tsum_mul_left]
  have hshift : (∑' i : ℕ, (if 2 * a ≤ i + 1 then (1 : ℝ) / (((i + 1 : ℕ)) : ℝ) ^ 2 else 0))
      = (∑' i : ℕ, (if 2 * a ≤ i then (1 : ℝ) / (i : ℝ) ^ 2 else 0)) := by
    have hz := Summable.tsum_eq_zero_add hψ_summ
    have h0 : (if 2 * a ≤ 0 then (1 : ℝ) / (((0 : ℕ)) : ℝ) ^ 2 else 0) = 0 := by
      have : ¬ (2 * a ≤ 0) := by omega
      rw [if_neg this]
    rw [h0, zero_add] at hz
    exact hz.symm
  -- Assemble the bound.
  have hbound : (∑' x : ℤ, h x) ≤ 4 := by
    rw [hdecomp, hpos_val, hneg_val, hshift]
    have hA : (0 : ℝ) ≤ 2 * (a : ℝ) := by positivity
    have hmul : 2 * (a : ℝ) * (∑' i : ℕ, (if 2 * a ≤ i then (1 : ℝ) / (i : ℝ) ^ 2 else 0))
        ≤ 2 * (a : ℝ) * (2 / (2 * (2 * (a : ℝ)) - 1)) :=
      mul_le_mul_of_nonneg_left hS hA
    have harith : 2 * (a : ℝ) * (2 / (2 * (2 * (a : ℝ)) - 1)) ≤ 2 := by
      have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have hd : (0 : ℝ) < 2 * (2 * (a : ℝ)) - 1 := by linarith
      rw [show 2 * (2 * (a : ℝ)) - 1 = 4 * (a : ℝ) - 1 by ring] at hd ⊢
      rw [← mul_div_assoc, div_le_iff₀ hd]
      nlinarith [h1]
    nlinarith [hmul, harith]
  -- Bridge to `ENNReal`.
  have hbridge : (∑' x : ℤ, (if 2 * a ≤ x.natAbs then
        ENNReal.ofReal (2 * (a : ℝ) / ((x.natAbs : ℝ)) ^ 2) else 0))
      = ENNReal.ofReal (∑' x : ℤ, h x) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun x => hnn x) hsumm_h]
    apply tsum_congr; intro x
    simp only [hh]
    by_cases hx : 2 * a ≤ x.natAbs
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx, ENNReal.ofReal_zero]
  rw [hbridge]
  exact ENNReal.ofReal_le_ofReal hbound

end Commons.Analysis.Hilbert
