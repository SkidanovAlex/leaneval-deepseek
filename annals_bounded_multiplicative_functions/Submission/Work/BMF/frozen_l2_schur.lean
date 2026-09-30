import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open MeasureTheory intervalIntegral

namespace Work.BMF

noncomputable section

/-! ## The frozen `L²`/Schur bound for the kernel `1/(1+(t-s)^2)`

We prove: for a continuous (nonnegative) `φ` and `c ≤ d`,
`∫_c^d ∫_c^d φ t φ s /(1+(t-s)^2) ≤ π ∫_c^d φ^2`.

The proof follows the elementary Schur/AM–GM argument: pointwise
`φ t φ s ≤ (φ t^2 + φ s^2)/2`, and the row sums of the kernel are bounded by `π`.
-/

private lemma cont_sq (c : ℝ) : Continuous (fun x : ℝ => 1 + (c - x)^2) := by fun_prop

private lemma cont_sq2 : Continuous (fun p : ℝ × ℝ => 1 + (p.1 - p.2)^2) := by fun_prop

private lemma cont_inv_sq (c : ℝ) : Continuous (fun x : ℝ => (1 + (c - x)^2)⁻¹) :=
  (cont_sq c).inv₀ (fun x => by positivity)

private lemma cont_inv_sq2 : Continuous (fun p : ℝ × ℝ => (1 + (p.1 - p.2)^2)⁻¹) :=
  cont_sq2.inv₀ (fun p => by positivity)

/-- The row-sum bound for the Hilbert kernel `1/(1+s^2)`: a single row has mass at most `π`. -/
private lemma row_integral_le_pi (t lo hi : ℝ) (_hlo : lo ≤ hi) :
    (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹) ≤ Real.pi := by
  have hsub : (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹)
      = ∫ s in lo - t..hi - t, (1 + s^2)⁻¹ := by
    have hfun : (fun t' : ℝ => (1 + (t - t')^2)⁻¹)
        = (fun t' : ℝ => (fun s : ℝ => (1 + s^2)⁻¹) (t' - t)) := by
      funext t'
      simp only []
      rw [show (t - t')^2 = (t' - t)^2 by ring]
    rw [hfun]
    exact intervalIntegral.integral_comp_sub_right (fun s : ℝ => (1 + s^2)⁻¹) t
  rw [hsub, integral_inv_one_add_sq]
  have h1 := Real.arctan_lt_pi_div_two (hi - t)
  have h2 := Real.neg_pi_div_two_lt_arctan (lo - t)
  linarith

/-- **The Hilbert/Schur bound** for the kernel `1/(1+(t-t')^2)`. -/
private theorem hilbert_kernel_bound (f : ℝ → ℝ) (hf : Continuous f)
    (lo hi : ℝ) (hlo : lo ≤ hi) :
    (∫ t in lo..hi, ∫ t' in lo..hi, f t * f t' * (1 + (t - t')^2)⁻¹)
      ≤ Real.pi * ∫ t in lo..hi, f t^2 := by
  set S : ℝ := ∫ t in lo..hi, f t^2 with hS
  have hAmgm : ∀ t t' : ℝ, f t * f t' ≤ f t^2/2 + f t'^2/2 := by
    intro t t'; nlinarith [sq_nonneg (f t - f t')]
  have hpt : ∀ t t' : ℝ,
      f t * f t' * (1 + (t - t')^2)⁻¹
        ≤ (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹ := by
    intro t t'
    exact mul_le_mul_of_nonneg_right (hAmgm t t') (by positivity)
  have cA : Continuous (Function.uncurry (fun t t' : ℝ => f t * f t' * (1 + (t - t')^2)⁻¹)) := by
    have hun : Function.uncurry (fun t t' : ℝ => f t * f t' * (1 + (t - t')^2)⁻¹)
        = (fun p : ℝ × ℝ => f p.1 * f p.2 * (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
    rw [hun]
    exact ((hf.comp continuous_fst).mul (hf.comp continuous_snd)).mul cont_inv_sq2
  have cB : Continuous
      (Function.uncurry (fun t t' : ℝ => (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹)) := by
    have hun : Function.uncurry (fun t t' : ℝ => (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹)
        = (fun p : ℝ × ℝ => (f p.1^2/2 + f p.2^2/2) * (1 + (p.1 - p.2)^2)⁻¹) := by
      funext p; rfl
    rw [hun]
    exact (((hf.comp continuous_fst).pow 2).div_const 2 |>.add
      (((hf.comp continuous_snd).pow 2).div_const 2)).mul cont_inv_sq2
  have cA1 : ∀ t : ℝ, Continuous (fun t' : ℝ => f t * f t' * (1 + (t - t')^2)⁻¹) := fun t =>
    (continuous_const.mul hf).mul (cont_inv_sq t)
  have cB1 : ∀ t : ℝ, Continuous (fun t' : ℝ => (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹) :=
    fun t => (continuous_const.add ((hf.pow 2).div_const 2)).mul (cont_inv_sq t)
  have Aint : IntervalIntegrable
      (fun t : ℝ => ∫ t' in lo..hi, f t * f t' * (1 + (t - t')^2)⁻¹) volume lo hi :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' cA lo hi).intervalIntegrable lo hi
  have Bint : IntervalIntegrable
      (fun t : ℝ => ∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹) volume lo hi :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' cB lo hi).intervalIntegrable lo hi
  have hmono : (∫ t in lo..hi, ∫ t' in lo..hi, f t * f t' * (1 + (t - t')^2)⁻¹)
      ≤ (∫ t in lo..hi, ∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹) := by
    refine intervalIntegral.integral_mono_on hlo Aint Bint ?_
    intro t _
    refine intervalIntegral.integral_mono_on hlo ((cA1 t).intervalIntegrable lo hi)
      ((cB1 t).intervalIntegrable lo hi) ?_
    intro t' _; exact hpt t t'
  have hsplit1 : ∀ t : ℝ,
      (∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹)
        = (∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
          + (∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹) := by
    intro t
    trans (∫ t' in lo..hi, (f t^2/2 * (1 + (t - t')^2)⁻¹ + f t'^2/2 * (1 + (t - t')^2)⁻¹))
    · apply intervalIntegral.integral_congr
      intro t' _; ring
    · exact intervalIntegral.integral_add
        ((continuous_const.mul (cont_inv_sq t)).intervalIntegrable lo hi)
        ((((hf.pow 2).div_const 2).mul (cont_inv_sq t)).intervalIntegrable lo hi)
  have cT1 : Continuous (fun t : ℝ => ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t t' : ℝ => f t^2/2 * (1 + (t - t')^2)⁻¹) (by
        have hun : Function.uncurry (fun t t' : ℝ => f t^2/2 * (1 + (t - t')^2)⁻¹)
            = (fun p : ℝ × ℝ => f p.1^2/2 * (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
        rw [hun]
        exact (((hf.comp continuous_fst).pow 2).div_const 2).mul cont_inv_sq2) lo hi
  have cT2 : Continuous (fun t : ℝ => ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t t' : ℝ => f t'^2/2 * (1 + (t - t')^2)⁻¹) (by
        have hun : Function.uncurry (fun t t' : ℝ => f t'^2/2 * (1 + (t - t')^2)⁻¹)
            = (fun p : ℝ × ℝ => f p.2^2/2 * (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
        rw [hun]
        exact (((hf.comp continuous_snd).pow 2).div_const 2).mul cont_inv_sq2) lo hi
  have hsplit : (∫ t in lo..hi, ∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹)
      = (∫ t in lo..hi, ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
        + (∫ t in lo..hi, ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹) := by
    trans (∫ t in lo..hi, ((∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
        + (∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)))
    · apply intervalIntegral.integral_congr
      intro t _; exact hsplit1 t
    · exact intervalIntegral.integral_add (cT1.intervalIntegrable lo hi) (cT2.intervalIntegrable lo hi)
  have hT1 : (∫ t in lo..hi, ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
      ≤ Real.pi/2 * S := by
    rw [hS]
    have hsimp : (∫ t in lo..hi, ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
        = ∫ t in lo..hi, f t^2/2 * (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t _
      show (∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
          = f t^2/2 * (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹)
      rw [intervalIntegral.integral_const_mul]
    rw [hsimp]
    have hcont1 : Continuous (fun t : ℝ => f t^2/2 * (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹)) :=
      ((hf.pow 2).div_const 2).mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun t t' : ℝ => (1 + (t - t')^2)⁻¹) (by
            have hun : Function.uncurry (fun t t' : ℝ => (1 + (t - t')^2)⁻¹)
                = (fun p : ℝ × ℝ => (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
            rw [hun]; exact cont_inv_sq2) lo hi)
    calc (∫ t in lo..hi, f t^2/2 * (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹))
        ≤ ∫ t in lo..hi, f t^2/2 * Real.pi := by
          refine intervalIntegral.integral_mono_on hlo (hcont1.intervalIntegrable lo hi)
            ((((hf.pow 2).div_const 2).mul continuous_const).intervalIntegrable lo hi) ?_
          intro t _
          exact mul_le_mul_of_nonneg_left (row_integral_le_pi t lo hi hlo) (by positivity)
      _ = Real.pi/2 * (∫ t in lo..hi, f t^2) := by
          rw [show (∫ t in lo..hi, f t^2/2 * Real.pi)
              = ∫ t in lo..hi, (Real.pi/2) * f t^2 by
            apply intervalIntegral.integral_congr
            intro t _; ring]
          rw [intervalIntegral.integral_const_mul]
  have hT2 : (∫ t in lo..hi, ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)
      ≤ Real.pi/2 * S := by
    rw [hS]
    have cBT : Continuous (Function.uncurry (fun t t' : ℝ => f t'^2/2 * (1 + (t - t')^2)⁻¹)) := by
      have hun : Function.uncurry (fun t t' : ℝ => f t'^2/2 * (1 + (t - t')^2)⁻¹)
          = (fun p : ℝ × ℝ => f p.2^2/2 * (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
      rw [hun]
      exact (((hf.comp continuous_snd).pow 2).div_const 2).mul cont_inv_sq2
    have hswap : (∫ t in lo..hi, ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)
        = ∫ t' in lo..hi, ∫ t in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹ := by
      apply MeasureTheory.intervalIntegral_intervalIntegral_swap
      refine (ContinuousOn.integrableOn_compact
        ((isCompact_uIcc (a := lo) (b := hi)).prod (isCompact_uIcc (a := lo) (b := hi)))
        cBT.continuousOn).mono_set ?_
      exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
    rw [hswap]
    have hsimp : (∫ t' in lo..hi, ∫ t in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)
        = ∫ t' in lo..hi, f t'^2/2 * (∫ t in lo..hi, (1 + (t - t')^2)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t' _
      show (∫ t in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)
          = f t'^2/2 * (∫ t in lo..hi, (1 + (t - t')^2)⁻¹)
      rw [intervalIntegral.integral_const_mul]
    rw [hsimp]
    have hcont2 : Continuous (fun t' : ℝ => f t'^2/2 * (∫ t in lo..hi, (1 + (t - t')^2)⁻¹)) :=
      ((hf.pow 2).div_const 2).mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun t' t : ℝ => (1 + (t - t')^2)⁻¹) (by
            have hun : Function.uncurry (fun t' t : ℝ => (1 + (t - t')^2)⁻¹)
                = (fun p : ℝ × ℝ => (1 + (p.2 - p.1)^2)⁻¹) := by funext p; rfl
            rw [hun]
            exact ((by fun_prop : Continuous (fun p : ℝ × ℝ => 1 + (p.2 - p.1)^2))).inv₀
              (fun p => by positivity)) lo hi)
    calc (∫ t' in lo..hi, f t'^2/2 * (∫ t in lo..hi, (1 + (t - t')^2)⁻¹))
        ≤ ∫ t' in lo..hi, f t'^2/2 * Real.pi := by
          refine intervalIntegral.integral_mono_on hlo (hcont2.intervalIntegrable lo hi)
            ((((hf.pow 2).div_const 2).mul continuous_const).intervalIntegrable lo hi) ?_
          intro t' _
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hcongr : (∫ t in lo..hi, (1 + (t - t')^2)⁻¹)
              = ∫ t in lo..hi, (1 + (t' - t)^2)⁻¹ := by
            apply intervalIntegral.integral_congr
            intro t _
            simp only []
            rw [show (t - t')^2 = (t' - t)^2 by ring]
          rw [hcongr]
          exact row_integral_le_pi t' lo hi hlo
      _ = Real.pi/2 * (∫ t in lo..hi, f t^2) := by
          rw [show (∫ t' in lo..hi, f t'^2/2 * Real.pi)
              = ∫ t' in lo..hi, (Real.pi/2) * f t'^2 by
            apply intervalIntegral.integral_congr
            intro t' _; ring]
          rw [intervalIntegral.integral_const_mul]
  calc (∫ t in lo..hi, ∫ t' in lo..hi, f t * f t' * (1 + (t - t')^2)⁻¹)
      ≤ (∫ t in lo..hi, ∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹) := hmono
    _ = (∫ t in lo..hi, ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
        + (∫ t in lo..hi, ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹) := hsplit
    _ ≤ Real.pi/2 * S + Real.pi/2 * S := add_le_add hT1 hT2
    _ = Real.pi * S := by ring

theorem frozen_l2_schur (φ : ℝ → ℝ) (hφ : Continuous φ) (hφ0 : ∀ t, 0 ≤ φ t) (c d : ℝ)
    (hcd : c ≤ d) :
    ∫ t in c..d, ∫ s in c..d, φ t * φ s * (1 + (t - s)^2)⁻¹
      ≤ Real.pi * ∫ t in c..d, φ t^2 :=
  hilbert_kernel_bound φ hφ c d hcd

end

end Work.BMF
