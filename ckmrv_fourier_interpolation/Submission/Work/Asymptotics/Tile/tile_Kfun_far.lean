import Mathlib
import Submission.Work.Asymptotics.Tile.tile_dev_aux
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.KClear_mg2

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

set_option maxHeartbeats 1000000

private lemma DeltaFun_vadd_int' (n : ℤ) (hn : n = 1 ∨ n = -1) (w : UpperHalfPlane) :
    Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w) = Work.Kernels.DeltaFun w := by
  rcases hn with h | h
  · subst h
    push_cast
    exact Work.Kernels.KernelFacts.DeltaFun_vadd_one w
  · subst h
    push_cast
    show Work.Kernels.DeltaFun (((-1 : ℝ)) +ᵥ w) = Work.Kernels.DeltaFun w
    have h1 := Work.Kernels.KernelFacts.DeltaFun_vadd_one ((-1 : ℝ) +ᵥ w)
    rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w by rw [← add_vadd]; norm_num] at h1
    exact h1.symm

/-- The divisor identity `Δ(w) (j w - j z) = σ^12 (E₄(σ)^3 - Δ(σ) j z)` for `σ = S • w`. -/
private lemma delta_mul_jdiff_eq (w z : UpperHalfPlane) :
    Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z)
      = (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 12 *
        (Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3
          - Work.Kernels.DeltaFun (ModularGroup.S • w) * Work.Kernels.jInvariantFun z) := by
  have h1 : Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z)
      = Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun z := by
    rw [mul_sub, Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
  rw [h1, Work.Asymptotics.E4Fun_S_smul' w, Work.Asymptotics.DeltaFun_S_smul' w]
  ring

/-! ## Numeric facts -/

private lemma two_seven_le_exp_one : (2.7:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]

private lemma exp_nat_ge (n : ℕ) : (2.7:ℝ)^n ≤ Real.exp ((n:ℝ)) := by
  have h : (2.7:ℝ) ≤ Real.exp 1 := two_seven_le_exp_one
  rw [show ((n:ℝ)) = ((n:ℕ):ℝ) * 1 by simp, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) h n

private lemma exp_neg_two_pi_le : Real.exp (-(2*Real.pi)) ≤ 1/100 := by
  have h1 : Real.exp (-(2*Real.pi)) ≤ Real.exp (-(6:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have h2 : (100:ℝ) ≤ Real.exp (6:ℝ) := by
    have h := exp_nat_ge 6
    have h3 : (100:ℝ) ≤ (2.7:ℝ)^6 := by norm_num
    linarith
  calc Real.exp (-(2*Real.pi)) ≤ Real.exp (-(6:ℝ)) := h1
    _ = 1/(Real.exp (6:ℝ)) := by rw [Real.exp_neg, inv_eq_one_div]
    _ ≤ 1/((100:ℝ)) := one_div_le_one_div_of_le (by norm_num) h2

private lemma exp_neg_six_pi_le : Real.exp (-(6*Real.pi)) ≤ 1/1000 := by
  have h1 : Real.exp (-(6*Real.pi)) ≤ Real.exp (-(18:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have h2 : (1000:ℝ) ≤ Real.exp (18:ℝ) := by
    have h := exp_nat_ge 18
    have h3 : (1000:ℝ) ≤ (2.7:ℝ)^18 := by norm_num
    linarith
  calc Real.exp (-(6*Real.pi)) ≤ Real.exp (-(18:ℝ)) := h1
    _ = 1/(Real.exp (18:ℝ)) := by rw [Real.exp_neg, inv_eq_one_div]
    _ ≤ 1/((1000:ℝ)) := one_div_le_one_div_of_le (by norm_num) h2

private lemma exp_neg_eight_pi_le : Real.exp (-(8*Real.pi)) ≤ 1/(10:ℝ)^9 := by
  have h1 : Real.exp (-(8*Real.pi)) ≤ Real.exp (-(24:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have h2 : (10:ℝ)^9 ≤ Real.exp (24:ℝ) := by
    have h := exp_nat_ge 24
    have h3 : (10:ℝ)^9 ≤ (2.7:ℝ)^24 := by norm_num
    linarith
  calc Real.exp (-(8*Real.pi)) ≤ Real.exp (-(24:ℝ)) := h1
    _ = 1/(Real.exp (24:ℝ)) := by rw [Real.exp_neg, inv_eq_one_div]
    _ ≤ 1/((10:ℝ)^9) := one_div_le_one_div_of_le (by norm_num) h2

/-! ## Scale comparisons -/

private lemma scale_vadd_le (a : ℝ) (w : UpperHalfPlane) :
    Work.Kernels.scale (a +ᵥ w) ≤ (1 + |a|) * Work.Kernels.scale w := by
  have h1 : (a +ᵥ w).im = w.im := UpperHalfPlane.vadd_im a w
  have h2 : ‖((a +ᵥ w : UpperHalfPlane) : ℂ)‖ ≤ |a| + ‖(w : ℂ)‖ := by
    calc ‖((a +ᵥ w : UpperHalfPlane) : ℂ)‖ = ‖(a : ℂ) + (w : ℂ)‖ := by rw [UpperHalfPlane.coe_vadd]
      _ ≤ ‖(a : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
      _ = |a| + ‖(w : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  have h3 : (0:ℝ) < w.im := w.im_pos
  have h4 : (0:ℝ) ≤ (w.im)⁻¹ := inv_nonneg.mpr h3.le
  have h5 : (0:ℝ) ≤ ‖(w:ℂ)‖ := norm_nonneg _
  have h6 : (0:ℝ) ≤ |a| := abs_nonneg a
  unfold Work.Kernels.scale
  rw [h1]
  nlinarith [h2, h4, h5, h6]

private lemma scale_imagAxis_le (t : ℝ) (ht : 0 < t) (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    Work.Kernels.scale (Work.Kernels.imagAxis t ht) ≤ 5 := by
  have him : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  have hn : ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t :=
    Work.Asymptotics.Tile.norm_imagAxis_coe t ht
  have hinv : (Work.Kernels.imagAxis t ht).im⁻¹ ≤ 1 := by
    rw [him]
    exact inv_le_one_of_one_le₀ h1
  rw [him] at hinv
  unfold Work.Kernels.scale
  rw [him, hn]
  linarith

/-! ## Bounds for `E₄` and `Δ ∘ j` on the imaginary axis -/

private lemma norm_E4_imagAxis_le_201 (t : ℝ) (ht : 0 < t) (h1 : 1 ≤ t) :
    ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ≤ 201 := by
  have him : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  have hb := Work.Asymptotics.E4Fun_sub_one_explicit (w := Work.Kernels.imagAxis t ht)
    (by rw [him]; exact h1)
  rw [Work.Asymptotics.norm_qParamFun] at hb
  rw [him] at hb
  have he : Real.exp (-(2*Real.pi*t)) ≤ 1/100 := by
    calc Real.exp (-(2*Real.pi*t)) ≤ Real.exp (-(2*Real.pi*1)) := by
          apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      _ = Real.exp (-(2*Real.pi)) := by ring_nf
      _ ≤ 1/100 := exp_neg_two_pi_le
  have hsub : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) - 1‖ + 1 := by
    have h := norm_add_le (Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) - 1) (1:ℂ)
    rw [sub_add_cancel, norm_one] at h
    exact h
  calc ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) - 1‖ + 1 := hsub
    _ ≤ 20000 * (1/100) + 1 := by linarith [hb, he]
    _ ≤ 201 := by norm_num

private lemma norm_E4_imagAxis_le_three_halves (t : ℝ) (ht : 0 < t) (h2 : 2 ≤ t) :
    ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ≤ 3/2 := by
  have him : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  have hb := Work.FunnelNumerics.E4_sub_one_le (Work.Kernels.imagAxis t ht) (by rw [him]; exact h2)
  have hsub : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) - 1‖ + 1 := by
    have h := norm_add_le (Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) - 1) (1:ℂ)
    rw [sub_add_cancel, norm_one] at h
    exact h
  linarith

private lemma norm_cube_E4_lower (σ : UpperHalfPlane) (h2 : 2 ≤ σ.im) :
    (1:ℝ)/8 ≤ ‖Work.Kernels.E4Fun σ ^ 3‖ := by
  have h1 := Work.FunnelNumerics.E4_sub_one_le σ h2
  have h2' : (1:ℝ)/2 ≤ ‖Work.Kernels.E4Fun σ‖ := by
    have h := abs_norm_sub_norm_le (Work.Kernels.E4Fun σ) (1:ℂ)
    rw [norm_one] at h
    have h3 := (abs_le.mp (le_trans h h1)).1
    linarith
  calc (1:ℝ)/8 = (1/2:ℝ)^3 := by norm_num
    _ ≤ ‖Work.Kernels.E4Fun σ‖^3 := pow_le_pow_left₀ (by norm_num) h2' 3
    _ = ‖Work.Kernels.E4Fun σ ^ 3‖ := by rw [norm_pow]

/-- `‖Δ(σ) · j(i t)‖ ≤ 1/16` for `Im σ ≥ 6` and `1 ≤ t ≤ 3`. -/
private lemma delta_mul_j_imagAxis_small (σ : UpperHalfPlane) (h6 : 6 ≤ σ.im)
    (t : ℝ) (ht : 0 < t) (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    ‖Work.Kernels.DeltaFun σ * Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ ≤ 1/16 := by
  have hΔσ : ‖Work.Kernels.DeltaFun σ‖ ≤ 2 * Real.exp (-(2 * Real.pi * σ.im)) :=
    Work.Asymptotics.DeltaFun_upper_sharp σ (by linarith)
  have hΔzlow : (1:ℝ)/2 * Real.exp (-(2 * Real.pi * t))
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
    Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht h1
  have hm := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun (Work.Kernels.imagAxis t ht)
  have hprod : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
        * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
      = ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ := by
    rw [← norm_mul, hm]
  have hle : (1:ℝ)/2 * Real.exp (-(2 * Real.pi * t))
        * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3 := by
    calc (1:ℝ)/2 * Real.exp (-(2 * Real.pi * t))
          * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
        ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
          * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ :=
          mul_le_mul_of_nonneg_right hΔzlow (norm_nonneg _)
      _ = ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ := hprod
      _ = ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3 := by rw [norm_pow]
  have hone : (1:ℝ)/2 * Real.exp (-(2 * Real.pi * t)) * (2 * Real.exp (2 * Real.pi * t)) = 1 := by
    rw [show (1:ℝ)/2 * Real.exp (-(2 * Real.pi * t)) * (2 * Real.exp (2 * Real.pi * t))
        = (Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * t)) by ring,
      ← Real.exp_add]
    simp
  have hj : ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3 * (2 * Real.exp (2 * Real.pi * t)) := by
    have h2 : (0:ℝ) < 2 * Real.exp (2 * Real.pi * t) := by positivity
    calc ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
        = (1:ℝ)/2 * Real.exp (-(2 * Real.pi * t)) * (2 * Real.exp (2 * Real.pi * t))
            * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by rw [hone, one_mul]
      _ = (2 * Real.exp (2 * Real.pi * t))
            * ((1:ℝ)/2 * Real.exp (-(2 * Real.pi * t))
                * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖) := by ring
      _ ≤ (2 * Real.exp (2 * Real.pi * t))
            * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3 :=
            mul_le_mul_of_nonneg_left hle h2.le
      _ = ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
            * (2 * Real.exp (2 * Real.pi * t)) := by ring
  rw [norm_mul]
  rcases le_or_gt t 2 with h2 | h2
  · have hE4 := norm_E4_imagAxis_le_201 t ht h1
    have hcube : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3 ≤ (201:ℝ)^3 :=
      pow_le_pow_left₀ (norm_nonneg _) hE4 3
    have hexp : Real.exp (-(2 * Real.pi * σ.im) + 2 * Real.pi * t) ≤ 1/(10:ℝ)^9 := by
      have h := Real.exp_le_exp.mpr (show -(2 * Real.pi * σ.im) + 2 * Real.pi * t ≤ -(8*Real.pi) by
        nlinarith [Real.pi_pos])
      exact le_trans h exp_neg_eight_pi_le
    have h5 : (0:ℝ) < Real.exp (-(2*Real.pi*σ.im) + 2*Real.pi*t) := Real.exp_pos _
    calc ‖Work.Kernels.DeltaFun σ‖
          * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
        ≤ (2 * Real.exp (-(2 * Real.pi * σ.im)))
            * (‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
                * (2 * Real.exp (2 * Real.pi * t))) :=
          mul_le_mul hΔσ hj (norm_nonneg _) (by positivity)
      _ = 4 * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
            * (Real.exp (-(2*Real.pi*σ.im)) * Real.exp (2*Real.pi*t)) := by ring
      _ = 4 * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
            * Real.exp (-(2*Real.pi*σ.im) + 2*Real.pi*t) := by rw [← Real.exp_add]
      _ ≤ 4 * (201:ℝ)^3 * (1/(10:ℝ)^9) := by
          calc 4 * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
                * Real.exp (-(2*Real.pi*σ.im) + 2*Real.pi*t)
              ≤ 4 * (201:ℝ)^3 * Real.exp (-(2*Real.pi*σ.im) + 2*Real.pi*t) := by
                apply mul_le_mul_of_nonneg_right _ h5.le
                exact mul_le_mul_of_nonneg_left hcube (by norm_num)
            _ ≤ 4 * (201:ℝ)^3 * (1/(10:ℝ)^9) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 1/16 := by norm_num
  · have h2' : 2 ≤ t := le_of_lt h2
    have hE4 := norm_E4_imagAxis_le_three_halves t ht h2'
    have hcube : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3 ≤ ((3:ℝ)/2)^3 :=
      pow_le_pow_left₀ (norm_nonneg _) hE4 3
    have hexp : Real.exp (-(2 * Real.pi * σ.im) + 2 * Real.pi * t) ≤ 1/1000 := by
      have h := Real.exp_le_exp.mpr (show -(2 * Real.pi * σ.im) + 2 * Real.pi * t ≤ -(6*Real.pi) by
        nlinarith [Real.pi_pos])
      exact le_trans h exp_neg_six_pi_le
    have h5 : (0:ℝ) < Real.exp (-(2*Real.pi*σ.im) + 2*Real.pi*t) := Real.exp_pos _
    calc ‖Work.Kernels.DeltaFun σ‖
          * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
        ≤ (2 * Real.exp (-(2 * Real.pi * σ.im)))
            * (‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
                * (2 * Real.exp (2 * Real.pi * t))) :=
          mul_le_mul hΔσ hj (norm_nonneg _) (by positivity)
      _ = 4 * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
            * (Real.exp (-(2*Real.pi*σ.im)) * Real.exp (2*Real.pi*t)) := by ring
      _ = 4 * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
            * Real.exp (-(2*Real.pi*σ.im) + 2*Real.pi*t) := by rw [← Real.exp_add]
      _ ≤ 4 * ((3:ℝ)/2)^3 * (1/1000) := by
          calc 4 * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖^3
                * Real.exp (-(2*Real.pi*σ.im) + 2*Real.pi*t)
              ≤ 4 * ((3:ℝ)/2)^3 * Real.exp (-(2*Real.pi*σ.im) + 2*Real.pi*t) := by
                apply mul_le_mul_of_nonneg_right _ h5.le
                exact mul_le_mul_of_nonneg_left hcube (by norm_num)
            _ ≤ 4 * ((3:ℝ)/2)^3 * (1/1000) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 1/16 := by norm_num

/-! ## The clearing identity for `K` -/

private lemma Kfun_mul_growthPrefactor (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ z : UpperHalfPlane)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.Kfun ℓ d τ z * Work.Kernels.growthPrefactor d τ z
      = Work.Kernels.KfunClear ℓ d τ z := by
  simp only [Work.Kernels.Kfun, Work.Kernels.KfunClear]
  rw [Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z h,
    Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z h]
  ring

end Work.Asymptotics.Tile

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

private theorem tile_Kfun_far_aux (ℓ : Work.Kernels.LogLambdaData) (d e : ℕ)
    (hd : d = 8 ∨ d = 24) (he : e = (if d = 8 then 1 else 2)) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → 6 ≤ (ModularGroup.S • w).im →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t → t ≤ 3 →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨α, N, M, hα, hN, hM, hb⟩ := (Work.Asymptotics.KClear_mg2 ℓ d hd).1
  let c0 : ℝ := (6:ℝ)^12/16 * (Real.exp (-(6*Real.pi))/2)^e
  have hc0 : 0 < c0 := by
    dsimp only [c0]
    positivity
  refine ⟨(α + 1) * 2 ^ N * 5 ^ M / c0, N, ?_, hN, ?_⟩
  · have hα1 : 0 < α + 1 := by linarith
    positivity
  · intro w hw h6 n hn t ht h1 h3
    have hne : Work.Kernels.jInvariantFun ((n:ℝ) +ᵥ w)
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      intro hjj
      have hw1 : w = Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) :=
        tileCoincidence w hw n hn t ht h1 h3 hjj
      have him2 : (ModularGroup.S • (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))).im = t := by
        rw [Work.Asymptotics.imagAxis_smul_S t⁻¹ (inv_pos.mpr ht)]
        simp [Work.Kernels.imagAxis, inv_inv]
      rw [hw1] at h6
      rw [him2] at h6
      linarith
    have hgp : Work.Kernels.Kfun ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)
          * Work.Kernels.growthPrefactor d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)
        = Work.Kernels.KfunClear ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht) :=
      Kfun_mul_growthPrefactor ℓ d hd _ _ hne
    have hgp_eq : ‖Work.Kernels.growthPrefactor d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖
        = ‖Work.Kernels.DeltaFun w * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) ^ e
            * (Work.Kernels.jInvariantFun w
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := by
      rw [Work.Kernels.growthPrefactor, DeltaFun_vadd_int' n hn w,
        jInvariantFun_vadd_int' n hn w, ← he]
    have hna : |((n:ℝ))| ≤ 1 := by
      rcases hn with h | h
      · subst h; push_cast; norm_num
      · subst h; push_cast; norm_num
    have hsτ : Work.Kernels.scale ((n:ℝ) +ᵥ w) ≤ 2 * Work.Kernels.scale w := by
      calc Work.Kernels.scale ((n:ℝ) +ᵥ w)
          ≤ (1 + |((n:ℝ))|) * Work.Kernels.scale w := scale_vadd_le _ _
        _ ≤ 2 * Work.Kernels.scale w := by
            apply mul_le_mul_of_nonneg_right _ (Work.Kernels.scale_pos w).le
            linarith
    have hsz : Work.Kernels.scale (Work.Kernels.imagAxis t ht) ≤ 5 :=
      scale_imagAxis_le t ht h1 h3
    have hnum : ‖Work.Kernels.KfunClear ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖
        ≤ α * 2^N * 5^M * (Work.Kernels.scale w)^N := by
      have hb' := hb ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)
      have hτ : (Work.Kernels.scale ((n:ℝ)+ᵥ w))^N ≤ (2 * Work.Kernels.scale w)^N :=
        Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hsτ hN
      have hz : (Work.Kernels.scale (Work.Kernels.imagAxis t ht))^M ≤ 5^M :=
        Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hsz hM
      calc ‖Work.Kernels.KfunClear ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖
          ≤ α * (Work.Kernels.scale ((n:ℝ)+ᵥ w))^N
              * (Work.Kernels.scale (Work.Kernels.imagAxis t ht))^M := hb'
        _ ≤ α * (2 * Work.Kernels.scale w)^N * 5^M := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hτ hα) hz ?_ ?_
            · exact Real.rpow_nonneg (Work.Kernels.scale_pos _).le M
            · exact mul_nonneg hα
                (Real.rpow_nonneg (mul_nonneg (by norm_num)
                  (le_of_lt (Work.Kernels.scale_pos w))) N)
        _ = α * 2^N * 5^M * (Work.Kernels.scale w)^N := by
            rw [Real.mul_rpow (by norm_num) (Work.Kernels.scale_pos w).le]
            ring
    have hden : c0 ≤ ‖Work.Kernels.growthPrefactor d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖ := by
      rw [hgp_eq]
      have hid := delta_mul_jdiff_eq w (Work.Kernels.imagAxis t ht)
      have hcore : (1:ℝ)/16 ≤ ‖Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3
          - Work.Kernels.DeltaFun (ModularGroup.S • w)
              * Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
        have hE4 : (1:ℝ)/8 ≤ ‖Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3‖ :=
          norm_cube_E4_lower (ModularGroup.S • w) (by linarith)
        have hs : ‖Work.Kernels.DeltaFun (ModularGroup.S • w)
            * Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ ≤ 1/16 :=
          delta_mul_j_imagAxis_small (ModularGroup.S • w) h6 t ht h1 h3
        have h2 : ‖Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3‖
            - ‖Work.Kernels.DeltaFun (ModularGroup.S • w)
                * Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
            ≤ ‖Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3
                - Work.Kernels.DeltaFun (ModularGroup.S • w)
                    * Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ :=
          (abs_le.mp (abs_norm_sub_norm_le
            (Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3)
            (Work.Kernels.DeltaFun (ModularGroup.S • w)
              * Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)))).2
        linarith
      have hnorm12 : (6:ℝ)^12 ≤ ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖^12 := by
        have h1' : (6:ℝ) ≤ ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ := by
          have h := Complex.abs_im_le_norm ((ModularGroup.S • w : UpperHalfPlane) : ℂ)
          rw [UpperHalfPlane.coe_im, abs_of_pos (ModularGroup.S • w).im_pos] at h
          linarith
        exact pow_le_pow_left₀ (by norm_num) h1' 12
      have hd1 : (6:ℝ)^12/16 ≤ ‖Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun w
          - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := by
        rw [hid, norm_mul, norm_pow]
        calc (6:ℝ)^12/16 = (6:ℝ)^12 * (1/16) := by ring
          _ ≤ ‖(((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖^12
                * ‖Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3
                  - Work.Kernels.DeltaFun (ModularGroup.S • w)
                      * Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ :=
              mul_le_mul hnorm12 hcore (by norm_num) (by positivity)
      have hd2 : (Real.exp (-(6*Real.pi))/2)^e
          ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖^e := by
        have hlb : Real.exp (-(6*Real.pi))/2
            ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
          have h := Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht h1
          have he' : Real.exp (-(6*Real.pi)) ≤ Real.exp (-(2*Real.pi*t)) :=
            Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
          linarith
        exact pow_le_pow_left₀ (by positivity) hlb e
      have hsplit : ‖Work.Kernels.DeltaFun w * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) ^ e
            * (Work.Kernels.jInvariantFun w
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖
          = ‖Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun w
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖^e := by
        calc ‖Work.Kernels.DeltaFun w * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) ^ e
              * (Work.Kernels.jInvariantFun w
                  - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖
            = ‖Work.Kernels.DeltaFun w * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) ^ e‖
              * ‖Work.Kernels.jInvariantFun w
                  - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := norm_mul _ _
          _ = (‖Work.Kernels.DeltaFun w‖
                * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) ^ e‖)
              * ‖Work.Kernels.jInvariantFun w
                  - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by rw [norm_mul]
          _ = (‖Work.Kernels.DeltaFun w‖
                * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖^e)
              * ‖Work.Kernels.jInvariantFun w
                  - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by rw [norm_pow]
          _ = (‖Work.Kernels.DeltaFun w‖
                * ‖Work.Kernels.jInvariantFun w
                  - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖)
              * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖^e := by ring
          _ = ‖Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun w
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖
              * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖^e := by rw [norm_mul]
      dsimp only [c0]
      rw [hsplit]
      exact mul_le_mul hd1 hd2 (by positivity) (norm_nonneg _)
    have hgpnorm : ‖Work.Kernels.Kfun ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖
          * ‖Work.Kernels.growthPrefactor d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖
        = ‖Work.Kernels.KfunClear ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖ := by
      rw [← norm_mul, hgp]
    have hKc : ‖Work.Kernels.Kfun ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖ * c0
        ≤ α * 2^N * 5^M * (Work.Kernels.scale w)^N := by
      calc ‖Work.Kernels.Kfun ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖ * c0
          ≤ ‖Work.Kernels.Kfun ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖
            * ‖Work.Kernels.growthPrefactor d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖ :=
            mul_le_mul_of_nonneg_left hden (norm_nonneg _)
        _ = ‖Work.Kernels.KfunClear ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖ := hgpnorm
        _ ≤ α * 2^N * 5^M * (Work.Kernels.scale w)^N := hnum
    have hK : ‖Work.Kernels.Kfun ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖
        ≤ (α * 2^N * 5^M * (Work.Kernels.scale w)^N) / c0 := by
      rw [le_div_iff₀ hc0]
      exact hKc
    calc ‖Work.Kernels.Kfun ℓ d ((n:ℝ)+ᵥ w) (Work.Kernels.imagAxis t ht)‖
        ≤ (α * 2^N * 5^M * (Work.Kernels.scale w)^N) / c0 := hK
      _ = (α * 2^N * 5^M / c0) * (Work.Kernels.scale w)^N := by rw [div_mul_eq_mul_div]
      _ ≤ ((α + 1) * 2^N * 5^M / c0) * (Work.Kernels.scale w)^N := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N)
          apply div_le_div_of_nonneg_right _ hc0.le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **The kernel `Kfun` at the cusp-`±1` tiles, far side.**  For `w ∈ E = KEpsilon` with
`6 ≤ (S • w).im`, `n = ±1` and `t ∈ [1,3]`, `Kfun ℓ d (n +ᵥ w) (i t)` is polynomially bounded in
`scale w`.

Suggested route, all ingredients already proved in the workspace.
Write `τ = n +ᵥ w`, `z = i t`.  On the region there is no coincidence: `j τ = j z` would force
`w = i/t` by `Work.Asymptotics.Tile.tileCoincidence` in `tile_dev_low.lean`, hence
`(S • w).im = t ≤ 3 < 6`.  So `Kfun τ z = KfunClear τ z / growthPrefactor d τ z`
(`Work.Kernels.ClearLink.KPlusClear_eq_smul`, `...KMinusClear_eq_smul`,
`Work.Kernels.ClassicalFacts.DeltaFun_ne_zero`).
Numerator: `Work.Asymptotics.KClear_mg2` (ModerateGrowth2 of `KfunClear`), together with
`Work.Asymptotics.scale_le_scale_vadd` (in
`Submission/Work/Asymptotics/Tile/layerSeminormCuspTile.lean`; the version stated there has
`scale w ≤ scale (n +ᵥ w)`) and `scale (i t) ≤ 4`.
Denominator: with `σ := S • w` (so `w = S • σ`, `Im σ ≥ 6`, `‖σ‖ ≥ 6`), the algebra
`Δ(τ) * (j τ - j (i t)) = σ ^ 12 * (E4(σ) ^ 3 - Δ(σ) * j (i t))` from
`Work.Asymptotics.DeltaFun_S_smul'` / `E4Fun_S_smul'` (public copies in
`Submission/Work/Asymptotics/Xi8_bound_E.lean`),
`Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun`, and the `vadd` invariances
`KernelFacts.DeltaFun_vadd_one`, `E4Fun_vadd_one`, `jInvariantFun_vadd_one`; then
`‖E4(σ)^3 - Δ(σ) * j (i t)‖ ≥ 1/4` using `Work.Asymptotics.E4Fun_sub_one_explicit`,
`Work.Asymptotics.DeltaFun_upper_sharp`, and `‖j (i t)‖ ≤ 8 * Real.exp (2 * π * t)` (from
`j = E4^3/Δ`, `DeltaFun_imagAxis_lower_sharp`, `E4Fun_sub_one_explicit`), while
`‖Δ(i t)‖ ≥ Real.exp (-6π)/2` (`Work.Asymptotics.DeltaFun_imagAxis_lower_sharp`).
This gives `‖growthPrefactor‖ ≥ 6^12/4 * (Real.exp (-6π)/2)^e`, a positive constant; together
with the numerator bound this yields an explicit pair `(C, N)` (any `N ≥ 0` works). -/
theorem tile_Kfun_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → 6 ≤ (ModularGroup.S • w).im →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t → t ≤ 3 →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N :=
  tile_Kfun_far_aux ℓ d (if d = 8 then 1 else 2) hd rfl


end Work.Asymptotics.Tile
