import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.CorrAux

open Work.BoseBox

/-- The product term of the correction is dominated by `8 * C₀ * C₁ * A⁻⁵ * (μa³)^{797/323}`
times the logarithmic factor.  Since `ℓ = A (μa³)^{-163/323}` and `d = (μa³)^{6/323}`,
the `A`- and `μa³`-powers cancel exactly:
`(ℓ⁻¹)² ((ℓd)³)⁻¹ = A⁻⁵ (μa³)^{797/323}`, and the hypothesis `A⁻¹(μa³)^{157/323} ≤ 1`
turns `L = 1 + (ℓd)⁻¹ + |log d|` into `L ≤ 2(1 + |log t|)`. -/
theorem prodTermBound {C₀ C₁ A t : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (hA : 0 < A) (ht : 0 < t)
    (hu : A⁻¹ * Work.BoseBox.fsXp t 157 ≤ 1) :
    (let ℓ : ℝ := A * Work.BoseBox.fsXp t (-163)
     let d : ℝ := Work.BoseBox.fsXp t 6
     let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
     C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
       ≤ 8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * Work.BoseBox.fsXp t 797 * (1 + |Real.log t|) ^ 3) := by
  simp only []
  set ℓ : ℝ := A * fsXp t (-163) with hℓ
  set d : ℝ := fsXp t 6 with hd
  set L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d| with hL
  have htnn : (0 : ℝ) ≤ t := ht.le
  -- `(ℓd)⁻¹ = A⁻¹ (μa³)^{157/323}` is nonnegative and `≤ 1`.
  have hLdInv : (ℓ * d)⁻¹ = A⁻¹ * fsXp t 157 := by
    have hmul : ℓ * d = A * fsXp t (-157) := by
      rw [hℓ, hd, mul_assoc, fsXp_mul ht]; norm_num
    rw [hmul, mul_inv, fsXp_inv ht]; norm_num
  have hLdInv_nonneg : 0 ≤ (ℓ * d)⁻¹ := by
    rw [hLdInv]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hA)) (fsXp_nonneg (t := t) (c := 157) htnn)
  -- the two `A`/`t` power identities
  have hLsq : (ℓ⁻¹) ^ 2 = (A⁻¹) ^ 2 * fsXp t 326 := by
    have hLinv : ℓ⁻¹ = A⁻¹ * fsXp t 163 := by
      rw [hℓ, mul_inv, fsXp_inv ht]; norm_num
    rw [hLinv, mul_pow, fsXp_pow htnn]; norm_num
  have hLd3 : ((ℓ * d) ^ 3)⁻¹ = (A⁻¹) ^ 3 * fsXp t 471 := by
    rw [← inv_pow, hLdInv, mul_pow, fsXp_pow htnn]; norm_num
  have hA5 : (A⁻¹) ^ 2 * (A⁻¹) ^ 3 = A ^ (-(5 : ℝ)) := by
    rw [← pow_add, inv_pow, Real.rpow_neg hA.le 5]; norm_num
  have hx : fsXp t 326 * fsXp t 471 = fsXp t 797 := by
    rw [fsXp_mul ht]; norm_num
  -- the exact evaluation of the product of the two inverse factors
  have hkey : C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
      = C₀ * C₁ * A ^ (-(5 : ℝ)) * fsXp t 797 * L ^ 3 := by
    rw [hLsq, hLd3]
    calc C₀ * ((A⁻¹) ^ 2 * fsXp t 326) * C₁ * L ^ 3 * ((A⁻¹) ^ 3 * fsXp t 471)
        = C₀ * C₁ * ((A⁻¹) ^ 2 * (A⁻¹) ^ 3) * (fsXp t 326 * fsXp t 471) * L ^ 3 := by
          ring
      _ = C₀ * C₁ * A ^ (-(5 : ℝ)) * fsXp t 797 * L ^ 3 := by rw [hA5, hx]
  -- the bound on `L`
  have hLbound : L ≤ 2 * (1 + |Real.log t|) := by
    have hu' : (ℓ * d)⁻¹ ≤ 1 := by rw [hLdInv]; exact hu
    have hdlog : |Real.log d| ≤ |Real.log t| := by
      rw [hd, fsXp, Real.log_rpow ht, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 323)]
      nlinarith [abs_nonneg (Real.log t)]
    rw [hL]
    have := abs_nonneg (Real.log t)
    linarith
  have hLnn : 0 ≤ L := by
    rw [hL]
    have := abs_nonneg (Real.log d)
    linarith
  have hL3 : L ^ 3 ≤ 8 * (1 + |Real.log t|) ^ 3 := by
    calc L ^ 3 ≤ (2 * (1 + |Real.log t|)) ^ 3 := pow_le_pow_left₀ hLnn hLbound 3
      _ = 8 * (1 + |Real.log t|) ^ 3 := by ring
  have hK : 0 ≤ C₀ * C₁ * A ^ (-(5 : ℝ)) * fsXp t 797 := by
    have hA5pos : 0 < A ^ (-(5 : ℝ)) := Real.rpow_pos_of_pos hA _
    exact mul_nonneg (mul_nonneg (mul_nonneg h₀ h₁) (le_of_lt hA5pos))
      (fsXp_nonneg (t := t) (c := 797) htnn)
  calc C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
      = C₀ * C₁ * A ^ (-(5 : ℝ)) * fsXp t 797 * L ^ 3 := hkey
    _ ≤ C₀ * C₁ * A ^ (-(5 : ℝ)) * fsXp t 797 * (8 * (1 + |Real.log t|) ^ 3) :=
        mul_le_mul_of_nonneg_left hL3 hK
    _ = 8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3 := by ring

end Work.BoseFixB1S.CorrAux
