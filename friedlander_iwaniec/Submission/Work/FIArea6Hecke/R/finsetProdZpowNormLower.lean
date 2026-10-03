import Mathlib

namespace Work.FIArea6Hecke.R

/-- Norm of the product of complex `zpow`s over a finset, with non-negative exponents. -/
theorem finsetProdZpowNorm_eq (S : Finset ℂ) (w : ℂ → ℤ)
    (hw : ∀ u ∈ S, 0 ≤ w u) (ζ : ℂ) :
    ‖∏ u ∈ S, (ζ - u) ^ (w u)‖ = ∏ u ∈ S, ‖ζ - u‖ ^ (w u).toNat := by
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro u hu
  rw [Complex.norm_zpow, ← zpow_natCast, Int.toNat_of_nonneg (hw u hu)]

theorem finsetProdZpowNormLower (S : Finset ℂ) (c : ℝ) (hc : 0 < c) (w : ℂ → ℤ)
    (hw : ∀ u ∈ S, 0 ≤ w u) (ζ : ℂ) (hζ : ∀ u ∈ S, c ≤ ‖ζ - u‖) :
    -Real.log ‖∏ u ∈ S, (ζ - u) ^ (w u)‖ ≤
      -(∑ u ∈ S, ((w u).toNat : ℝ)) * Real.log c := by
  have hnorm := finsetProdZpowNorm_eq S w hw ζ
  have hpos : ∀ u ∈ S, 0 < ‖ζ - u‖ := fun u hu => lt_of_lt_of_le hc (hζ u hu)
  have hfpos : ∀ u ∈ S, 0 < ‖ζ - u‖ ^ (w u).toNat := fun u hu => pow_pos (hpos u hu) _
  -- logarithm of the norm of the product
  have hlog : Real.log ‖∏ u ∈ S, (ζ - u) ^ (w u)‖
      = ∑ u ∈ S, ((w u).toNat : ℝ) * Real.log ‖ζ - u‖ := by
    rw [hnorm, Real.log_prod (fun u hu => ne_of_gt (hfpos u hu))]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Real.log_pow]
  -- termwise comparison
  have hle : ∑ u ∈ S, ((w u).toNat : ℝ) * Real.log c
      ≤ ∑ u ∈ S, ((w u).toNat : ℝ) * Real.log ‖ζ - u‖ := by
    apply Finset.sum_le_sum
    intro u hu
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hc (hζ u hu)) (Nat.cast_nonneg _)
  have hsum : (∑ u ∈ S, ((w u).toNat : ℝ)) * Real.log c
      = ∑ u ∈ S, ((w u).toNat : ℝ) * Real.log c := Finset.sum_mul S _ (Real.log c)
  have key : (∑ u ∈ S, ((w u).toNat : ℝ)) * Real.log c
      ≤ ∑ u ∈ S, ((w u).toNat : ℝ) * Real.log ‖ζ - u‖ := by
    rw [hsum]; exact hle
  rw [hlog]
  calc -(∑ u ∈ S, ((w u).toNat : ℝ) * Real.log ‖ζ - u‖)
      ≤ -((∑ u ∈ S, ((w u).toNat : ℝ)) * Real.log c) := neg_le_neg key
    _ = -(∑ u ∈ S, ((w u).toNat : ℝ)) * Real.log c := by ring

end Work.FIArea6Hecke.R
