import Mathlib
import Submission.Commons.Combinatorics.QBinomial.alt_sum_eq_one
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow

namespace Commons.Combinatorics.QBinomial

open Finset

/-- The Gaussian binomial coefficient `gb r i` (the number of `i`-dimensional subspaces of
`𝔽₂^r`) is bounded by `2 ^ (i * (r - i) + i)`. -/
lemma gb_le_two_pow (r i : ℕ) : gb r i ≤ 2 ^ (i * (r - i) + i) := by
  have h := Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow
      (K := ZMod 2) (V := Fin r → ZMod 2) i
  rw [Module.finrank_pi, Fintype.card_fin] at h
  have hcard : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  rw [hcard] at h
  exact h

theorem gb_pow_sum_le (d r : ℕ) (hr : r ≤ d) :
    (∑ i ∈ Finset.range (r + 1), (Commons.Combinatorics.QBinomial.gb r i : ℝ) *
      ((2 : ℝ) ^ (7 * d * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)) ≤ 4 / 3 := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
    subst hr0
    have hone : (∑ i ∈ Finset.range (0 + 1), (gb 0 i : ℝ) *
        ((2 : ℝ) ^ (7 * 0 * i))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2)) = 1 := by
      rw [Finset.sum_range_one, gb_zero]
      norm_num
    rw [hone]
    norm_num
  · have h2ne : (2:ℝ) ≠ 0 := by norm_num
    have hpow : ∀ i : ℕ, (2:ℝ)^(-(2*(i:ℤ))) = (1/4:ℝ)^i := by
      intro i
      rw [show (1/4:ℝ) = (2:ℝ)^(-(2:ℤ)) by norm_num [zpow_neg, zpow_natCast]]
      rw [← zpow_natCast ((2:ℝ)^(-(2:ℤ))) i, ← zpow_mul]
      rw [show -(2*(i:ℤ)) = (-(2:ℤ))*(i:ℤ) by ring]
    have hgeom : (∑ i ∈ Finset.range (r+1), (1/4:ℝ)^i) ≤ 4/3 := by
      rw [geom_sum_eq (by norm_num : (1/4:ℝ) ≠ 1)]
      rw [div_le_iff_of_neg (by norm_num : (1/4:ℝ) - 1 < 0)]
      norm_num
    have hterm : ∀ i, i ≤ r → (gb r i : ℝ) * ((2:ℝ)^(7*d*i))⁻¹ * (2:ℝ)^(4*i^2)
        ≤ (2:ℝ)^(-(2*(i:ℤ))) := by
      intro i hir
      have hA : (gb r i : ℝ) ≤ (2:ℝ)^(((i*(r-i)+i : ℕ)):ℤ) := by
        have h := gb_le_two_pow r i
        have hR : (gb r i : ℝ) ≤ (2:ℝ)^(i*(r-i)+i) := by exact_mod_cast h
        simpa only [zpow_natCast] using hR
      have hB : ((2:ℝ)^(7*d*i))⁻¹ = (2:ℝ)^(-(((7*d*i : ℕ)):ℤ)) := by
        rw [← zpow_natCast (2:ℝ) (7*d*i), ← zpow_neg]
      have hBpos : (0:ℝ) ≤ (2:ℝ)^(-(((7*d*i : ℕ)):ℤ)) := by positivity
      have hCpos : (0:ℝ) ≤ (2:ℝ)^(((4*i^2 : ℕ)):ℤ) := by positivity
      have hC : (2:ℝ)^(4*i^2) = (2:ℝ)^(((4*i^2 : ℕ)):ℤ) := by rw [zpow_natCast]
      have hexp : ((i*(r-i)+i : ℕ):ℤ) + (-(((7*d*i:ℕ)):ℤ)) + ((4*i^2:ℕ):ℤ)
          ≤ -(2*(i:ℤ)) := by
        have hirZ : ((r-i:ℕ):ℤ) = (r:ℤ) - (i:ℤ) := by omega
        have hR : (r:ℤ) - 7*(d:ℤ) + 3*(i:ℤ) + 3 ≤ 0 := by omega
        have hnn : (0:ℤ) ≤ (i:ℤ) := by positivity
        have key : ((i*(r-i)+i:ℕ):ℤ) + (-(((7*d*i:ℕ)):ℤ)) + ((4*i^2:ℕ):ℤ)
            = (i:ℤ) * ((r:ℤ) - 7*(d:ℤ) + 3*(i:ℤ) + 3) - 2*(i:ℤ) := by
          push_cast
          rw [hirZ]
          ring
        rw [key]
        have hmul := mul_nonpos_of_nonneg_of_nonpos hnn hR
        linarith
      calc (gb r i : ℝ) * ((2:ℝ)^(7*d*i))⁻¹ * (2:ℝ)^(4*i^2)
          ≤ (2:ℝ)^(((i*(r-i)+i : ℕ)):ℤ) * (2:ℝ)^(-(((7*d*i : ℕ)):ℤ))
              * (2:ℝ)^(((4*i^2 : ℕ)):ℤ) := by
            rw [hB, hC]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hBpos) hCpos
        _ = (2:ℝ)^((((i*(r-i)+i : ℕ)):ℤ) + (-(((7*d*i : ℕ)):ℤ)) + ((4*i^2 : ℕ)):ℤ) := by
            rw [← zpow_add₀ h2ne, ← zpow_add₀ h2ne]
        _ ≤ (2:ℝ)^(-(2*(i:ℤ))) := zpow_le_zpow_right₀ (by norm_num) hexp
    calc (∑ i ∈ Finset.range (r + 1), (gb r i : ℝ) * ((2 : ℝ) ^ (7 * d * i))⁻¹
            * (2 : ℝ) ^ (4 * i ^ 2))
        ≤ ∑ i ∈ Finset.range (r + 1), (2:ℝ)^(-(2*(i:ℤ))) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hterm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = ∑ i ∈ Finset.range (r + 1), (1/4:ℝ)^i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hpow i
      _ ≤ 4 / 3 := hgeom

end Commons.Combinatorics.QBinomial
