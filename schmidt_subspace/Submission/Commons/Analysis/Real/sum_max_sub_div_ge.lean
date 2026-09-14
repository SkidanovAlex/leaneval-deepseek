import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

private lemma sum_range_cast_nat (n : ℕ) :
    ∑ j ∈ Finset.range n, (j : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sum_max_sub_div_ge {I m D : ℝ} {k : ℕ} (hI : 0 ≤ I) (hIm : I ≤ m) (hm : 2 ≤ m)
    (hD : 1 ≤ D) (hk : (k : ℝ) ≤ D + 1) :
    (k : ℝ) * I ^ 2 / (2 * m) ≤ ∑ j ∈ Finset.range k, max (I - (j : ℝ) / D) 0 := by
  have hDpos : 0 < D := by linarith
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  rcases le_or_gt ((k : ℝ) - 1) (I * D) with hle | hlt
  · -- Case 1: every term of the sum is nonnegative.
    have hterm : ∀ j ∈ Finset.range k, max (I - (j : ℝ) / D) 0 = I - (j : ℝ) / D := by
      intro j hj
      have hjk : (j : ℝ) ≤ (k : ℝ) - 1 := by
        have hjlt : j < k := Finset.mem_range.mp hj
        have : j + 1 ≤ k := hjlt
        have hcast : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
        push_cast at hcast
        linarith
      have hdiv : (j : ℝ) / D ≤ I := by
        rw [div_le_iff₀ hDpos]
        nlinarith
      rw [max_eq_left (sub_nonneg.mpr hdiv)]
    rw [Finset.sum_congr rfl hterm]
    have hsum : ∑ j ∈ Finset.range k, (I - (j : ℝ) / D)
        = (k : ℝ) * I - ((k : ℝ) * ((k : ℝ) - 1) / 2) / D := by
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_div]
      rw [Finset.sum_const, Finset.card_range]
      rw [sum_range_cast_nat]
      simp only [nsmul_eq_mul]
    rw [hsum]
    have hA : (k : ℝ) * I ^ 2 / (2 * m) ≤ (k : ℝ) * I / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * m)]
      have h2 : (k : ℝ) * I / 2 * (2 * m) = (k : ℝ) * I * m := by ring
      rw [h2]
      have hImul : I * I ≤ I * m := mul_le_mul_of_nonneg_left hIm hI
      have := mul_le_mul_of_nonneg_left hImul hk0
      nlinarith
    have hB : (k : ℝ) * I / 2
        ≤ (k : ℝ) * I - ((k : ℝ) * ((k : ℝ) - 1) / 2) / D := by
      have hX : ((k : ℝ) * ((k : ℝ) - 1) / 2) / D ≤ (k : ℝ) * I / 2 := by
        rw [div_le_iff₀ hDpos]
        have h2 : (k : ℝ) * I / 2 * D = (k : ℝ) * I * D / 2 := by ring
        rw [h2]
        have := mul_le_mul_of_nonneg_left hle hk0
        nlinarith
      linarith
    exact le_trans hA hB
  · -- Case 2: the last term is negative; use the first ⌊I*D⌋+1 terms.
    have ht0 : 0 ≤ I * D := mul_nonneg hI (by linarith)
    have hq_le : ((Nat.floor (I * D) : ℕ) : ℝ) ≤ I * D := Nat.floor_le ht0
    have hq_lt : I * D < ((Nat.floor (I * D) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (I * D)
    have hqk : Nat.floor (I * D) + 1 ≤ k := by
      have h1 : ((Nat.floor (I * D) : ℕ) : ℝ) < (k : ℝ) - 1 := lt_of_le_of_lt hq_le hlt
      have h2 : (((Nat.floor (I * D) + 1 : ℕ)) : ℝ) ≤ (k : ℝ) := by push_cast; linarith
      exact_mod_cast h2
    have hsub : Finset.range (Nat.floor (I * D) + 1) ⊆ Finset.range k :=
      Finset.range_subset_range.mpr hqk
    have hsplit : ∑ j ∈ Finset.range (Nat.floor (I * D) + 1), max (I - (j : ℝ) / D) 0
        ≤ ∑ j ∈ Finset.range k, max (I - (j : ℝ) / D) 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x _ _; exact le_max_right _ _)
    have hterm2 : ∀ j ∈ Finset.range (Nat.floor (I * D) + 1),
        max (I - (j : ℝ) / D) 0 = I - (j : ℝ) / D := by
      intro j hj
      have hjq : j ≤ Nat.floor (I * D) := by
        have := Finset.mem_range.mp hj
        omega
      have hjc : (j : ℝ) ≤ (Nat.floor (I * D) : ℝ) := by exact_mod_cast hjq
      have hdiv : (j : ℝ) / D ≤ I := by
        rw [div_le_iff₀ hDpos]
        nlinarith [hjc, hq_le]
      rw [max_eq_left (sub_nonneg.mpr hdiv)]
    have hsum2 : ∑ j ∈ Finset.range (Nat.floor (I * D) + 1), (I - (j : ℝ) / D)
        = ((Nat.floor (I * D) : ℝ) + 1) * I
            - (((Nat.floor (I * D) : ℝ) + 1) * (Nat.floor (I * D) : ℝ) / 2) / D := by
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_div]
      rw [Finset.sum_const, Finset.card_range]
      rw [sum_range_cast_nat]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have hT1 : I ^ 2 * D / 2 ≤ ((Nat.floor (I * D) : ℝ) + 1) * I
        - (((Nat.floor (I * D) : ℝ) + 1) * (Nat.floor (I * D) : ℝ) / 2) / D := by
      have hkey : (I * D) ^ 2
          ≤ ((Nat.floor (I * D) : ℝ) + 1) * (2 * (I * D) - (Nat.floor (I * D) : ℝ)) := by
        have hu0 : 0 ≤ I * D - (Nat.floor (I * D) : ℝ) := by linarith
        have hu1 : I * D - (Nat.floor (I * D) : ℝ) ≤ 1 := by linarith
        have hfac : ((Nat.floor (I * D) : ℝ) + 1) * (2 * (I * D) - (Nat.floor (I * D) : ℝ))
              - (I * D) ^ 2
            = (Nat.floor (I * D) : ℝ)
              + (I * D - (Nat.floor (I * D) : ℝ)) * (2 - (I * D - (Nat.floor (I * D) : ℝ))) := by
          ring
        have hnn : 0 ≤ (Nat.floor (I * D) : ℝ)
              + (I * D - (Nat.floor (I * D) : ℝ)) * (2 - (I * D - (Nat.floor (I * D) : ℝ))) := by
          apply add_nonneg (Nat.cast_nonneg _)
          apply mul_nonneg hu0
          linarith
        nlinarith [hfac, hnn]
      have hRHS : ((Nat.floor (I * D) : ℝ) + 1) * I
            - (((Nat.floor (I * D) : ℝ) + 1) * (Nat.floor (I * D) : ℝ) / 2) / D
          = ((Nat.floor (I * D) : ℝ) + 1) * (2 * (I * D) - (Nat.floor (I * D) : ℝ)) / (2 * D) := by
        field_simp
      rw [hRHS]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * D)]
      nlinarith
    have hT2 : (k : ℝ) * I ^ 2 / (2 * m) ≤ I ^ 2 * D / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * m)]
      have h2 : (I ^ 2 * D / 2) * (2 * m) = I ^ 2 * D * m := by ring
      rw [h2]
      have hkm : (k : ℝ) ≤ D * m := by nlinarith [hk, hm, hD]
      nlinarith [mul_le_mul_of_nonneg_left hkm (sq_nonneg I)]
    have hTle : ((Nat.floor (I * D) : ℝ) + 1) * I
          - (((Nat.floor (I * D) : ℝ) + 1) * (Nat.floor (I * D) : ℝ) / 2) / D
        ≤ ∑ j ∈ Finset.range k, max (I - (j : ℝ) / D) 0 := by
      rw [← hsum2]
      calc ∑ j ∈ Finset.range (Nat.floor (I * D) + 1), (I - (j : ℝ) / D)
          = ∑ j ∈ Finset.range (Nat.floor (I * D) + 1), max (I - (j : ℝ) / D) 0 := by
            rw [Finset.sum_congr rfl hterm2]
        _ ≤ ∑ j ∈ Finset.range k, max (I - (j : ℝ) / D) 0 := hsplit
    exact le_trans hT2 (le_trans hT1 hTle)

end Commons.Analysis.Real