import Mathlib.Analysis.Fourier.AddCircle
import Submission.Work.SmallBoxA0.SinParsevalDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `n`-th Fourier coefficient of the odd extension `oddExt F`

This file proves `Work.SmallBoxA0.fourierCoeff_oddExt`: the `n`-th complex
Fourier coefficient of the odd extension `oddExt F` of `F` (period `2` on
`[-1,1]`) equals `-I` times the `n`-th sine coefficient of `F` on
`[-1/2, 1/2]`.

The computation is the standard odd-function Fourier computation: split the
integral over `[-1,1]` at `0`, use the oddness `oddExt F (-v) = -oddExt F v`
(for `v > 0`, which suffices since `{0}` is null) to fold the two halves
together, recognise `e^{-inπv} - e^{inπv} = -2i sin(nπv)`, and finally shift
`v = x + 1/2` on `(0,1)`.

Note `oddExt F` is *not* continuous at `0` in general (it has a jump unless
`F (-1/2) = 0`), so all "pointwise" identifications on `(0,1)` are performed
with `integral_congr_ae` / with the `v > 0` hypothesis, never with
`integral_congr` on `[0,1]`.
-/

namespace Work.SmallBoxA0

open MeasureTheory intervalIntegral

noncomputable section

set_option linter.unusedVariables false

/-! ### Elementary facts about `fourier m` on `AddCircle 2` -/

lemma fourier_int_two (m : ℤ) (v : ℝ) :
    fourier m (↑v : AddCircle (2:ℝ)) = Complex.exp (↑m * ↑Real.pi * Complex.I * ↑v) := by
  rw [fourier_coe_apply]; congr 1; push_cast; ring

lemma norm_fourier_int_two (m : ℤ) (v : ℝ) :
    ‖fourier m (↑v : AddCircle (2:ℝ))‖ ≤ 1 := by
  rw [fourier_int_two]
  rw [show (↑m * ↑Real.pi * Complex.I * ↑v) = ↑((m:ℝ) * Real.pi * v) * Complex.I by
    push_cast; ring]
  rw [Complex.norm_exp_ofReal_mul_I]

lemma fourier_int_two_neg (m : ℤ) (v : ℝ) :
    fourier m (↑(-v) : AddCircle (2:ℝ)) = fourier (-m) (↑v : AddCircle (2:ℝ)) := by
  rw [fourier_int_two, fourier_int_two]; congr 1; push_cast; ring

lemma fourier_neg_sub_pos (n : ℤ) (v : ℝ) :
    fourier (-n) (↑v : AddCircle (2:ℝ)) - fourier n (↑v : AddCircle (2:ℝ))
      = -2 * Complex.I * ((Real.sin ((n:ℝ) * Real.pi * v) : ℝ) : ℂ) := by
  rw [fourier_int_two, fourier_int_two]
  set x : ℝ := (n:ℝ) * Real.pi * v with hx
  have h1 : (↑(-n) * ↑Real.pi * Complex.I * ↑v) = ↑(-x) * Complex.I := by
    rw [hx]; push_cast; ring
  have h2 : (↑n * ↑Real.pi * Complex.I * ↑v) = ↑x * Complex.I := by
    rw [hx]; push_cast; ring
  rw [h1, h2, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

lemma measurable_fourier_two (m : ℤ) :
    Measurable (fun v : ℝ => fourier m (↑v : AddCircle (2:ℝ))) := by
  rw [show (fun v : ℝ => fourier m (↑v : AddCircle (2:ℝ)))
      = fun v : ℝ => Complex.exp (↑m * ↑Real.pi * Complex.I * ↑v) from
        funext (fourier_int_two m)]
  fun_prop

/-! ### Elementary facts about `oddExt` -/

/-- `oddExt F` is odd at every *positive* argument.  (At `0` it is not, in
general: `oddExt F 0 = -F (-1/2)` while `-oddExt F 0 = F (-1/2)`.) -/
lemma oddExt_neg_of_pos (F : ℝ → ℝ) {v : ℝ} (hv : 0 < v) :
    oddExt F (-v) = - oddExt F v := by
  unfold oddExt
  rw [if_pos (by linarith : -v ≤ 0), if_neg (by linarith : ¬ v ≤ 0)]
  simp only [neg_neg]

lemma oddExt_eq_of_pos (F : ℝ → ℝ) {v : ℝ} (hv : 0 < v) :
    oddExt F v = F (v - 1/2) := by
  unfold oddExt
  rw [if_neg (by linarith : ¬ v ≤ 0)]

lemma measurable_oddExt {F : ℝ → ℝ} (hF : Continuous F) : Measurable (oddExt F) := by
  unfold oddExt
  exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)

/-! ### Integrability of the integrands

`oddExt F` is measurable and bounded on compact intervals, so every integrand
`fourier m (·) * oddExt F` is interval integrable. -/

lemma intervalIntegrable_oddExt_mul_fourier {F : ℝ → ℝ} (hF : Continuous F) (m : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => fourier m (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
      volume a b := by
  set Q : ℝ := 2 * (|a| + |b| + 1) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hF.continuousOn : ContinuousOn F (Set.Icc (-Q) Q))
  have hmeas : Measurable (fun v : ℝ => fourier m (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)) :=
    (measurable_fourier_two m).mul (Complex.measurable_ofReal.comp (measurable_oddExt hF))
  have harg : ∀ w : ℝ, |w| ≤ Q → ‖F w‖ ≤ M := fun w hw =>
    hM w (Set.mem_Icc.mpr ⟨by linarith [neg_abs_le w, hw], by linarith [le_abs_self w, hw]⟩)
  have hbound : ∀ v : ℝ, min a b ≤ v → v ≤ max a b → ‖(oddExt F v : ℂ)‖ ≤ M := by
    intro v hv1 hv2
    have hvabs : |v| ≤ |a| + |b| := by
      have hmax_le : max |a| |b| ≤ |a| + |b| := by
        apply max_le <;> linarith [abs_nonneg a, abs_nonneg b]
      have hmin_low : -(max |a| |b|) ≤ min a b :=
        le_min (by linarith [neg_abs_le a, le_max_left |a| |b|])
               (by linarith [neg_abs_le b, le_max_right |a| |b|])
      have hmax_ab : max a b ≤ max |a| |b| :=
        max_le (le_trans (le_abs_self a) (le_max_left _ _))
               (le_trans (le_abs_self b) (le_max_right _ _))
      rw [abs_le]
      exact ⟨by linarith [neg_le_neg hv1, neg_le_neg hmin_low, hmax_le],
             by linarith [hv2, hmax_ab, hmax_le]⟩
    have h1 : |v - 1/2| ≤ Q := by
      have h := abs_add_le v (-(1/2))
      rw [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
      have : v - 1/2 = v + -(1/2) := by ring
      rw [this]; linarith [abs_nonneg a, abs_nonneg b]
    have h2 : |-v - 1/2| ≤ Q := by
      have h := abs_add_le v (1/2)
      have : -v - 1/2 = -(v + 1/2) := by ring
      rw [this, abs_neg]; linarith [abs_nonneg a, abs_nonneg b]
    rw [show ‖(oddExt F v : ℂ)‖ = |oddExt F v| by simp]
    by_cases hv0 : v ≤ 0
    · rw [oddExt, if_pos hv0, abs_neg]; exact harg _ h2
    · rw [oddExt, if_neg hv0]; exact harg _ h1
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.IntegrableOn.of_bound ?_ hmeas.aestronglyMeasurable M ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with v hv
      have hv1 : min a b ≤ v := le_trans (min_le_left a b) (le_of_lt hv.1)
      have hv2 : v ≤ max a b := le_trans hv.2 (le_max_right a b)
      calc ‖fourier m (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)‖
          = ‖fourier m (↑v : AddCircle (2:ℝ))‖ * ‖(oddExt F v : ℂ)‖ := norm_mul _ _
        _ ≤ 1 * M := by gcongr; exact norm_fourier_int_two m v; exact hbound v hv1 hv2
        _ = M := one_mul M
  · refine MeasureTheory.IntegrableOn.of_bound ?_ hmeas.aestronglyMeasurable M ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with v hv
      have hv1 : min a b ≤ v := le_trans (min_le_right a b) (le_of_lt hv.1)
      have hv2 : v ≤ max a b := le_trans hv.2 (le_max_left a b)
      calc ‖fourier m (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)‖
          = ‖fourier m (↑v : AddCircle (2:ℝ))‖ * ‖(oddExt F v : ℂ)‖ := norm_mul _ _
        _ ≤ 1 * M := by gcongr; exact norm_fourier_int_two m v; exact hbound v hv1 hv2
        _ = M := one_mul M

/-! ### The main integral identity on `[-1,1]` -/

lemma fourierCoeff_oddExt_keyA {F : ℝ → ℝ} (hF : Continuous F) (n : ℤ) :
    (∫ v in (-1)..1, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
      = -2 * Complex.I
          * (((∫ v in (0:ℝ)..1, oddExt F v * Real.sin ((n:ℝ) * Real.pi * v) : ℝ)) : ℂ) := by
  have hΦint : ∀ a b : ℝ, IntervalIntegrable
      (fun v : ℝ => fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)) volume a b :=
    fun a b => intervalIntegrable_oddExt_mul_fourier hF (-n) a b
  have hΨint : ∀ a b : ℝ, IntervalIntegrable
      (fun v : ℝ => fourier n (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)) volume a b :=
    fun a b => intervalIntegrable_oddExt_mul_fourier hF n a b
  have hsplit : (∫ v in (-1)..1, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
      = (∫ v in (-1)..0, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
        + (∫ v in (0:ℝ)..1, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)) :=
    (integral_add_adjacent_intervals (hΦint (-1) 0) (hΦint 0 1)).symm
  have hcomp : (∫ v in (-1)..0, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
      = ∫ v in (0:ℝ)..1, fourier (-n) (↑(-v) : AddCircle (2:ℝ)) * (oddExt F (-v) : ℂ) := by
    have := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1)
      (fun v : ℝ => fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
    simpa using this.symm
  have hneg : (∫ v in (0:ℝ)..1, fourier (-n) (↑(-v) : AddCircle (2:ℝ)) * (oddExt F (-v) : ℂ))
      = -∫ v in (0:ℝ)..1, fourier n (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with v hv
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hv0 : 0 < v := hv.1
    rw [oddExt_neg_of_pos F hv0, fourier_int_two_neg (-n) v, neg_neg, Complex.ofReal_neg]
    ring
  have hsub : (∫ v in (0:ℝ)..1, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
        - (∫ v in (0:ℝ)..1, fourier n (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
      = ∫ v in (0:ℝ)..1, (fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)
          - fourier n (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)) :=
    (integral_sub (hΦint 0 1) (hΨint 0 1)).symm
  have hpt : ∀ v : ℝ, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)
        - fourier n (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)
      = -2 * Complex.I * ((oddExt F v * Real.sin ((n:ℝ) * Real.pi * v) : ℝ) : ℂ) := by
    intro v
    rw [← sub_mul, fourier_neg_sub_pos, Complex.ofReal_mul]
    ring
  have hreal : (∫ v in (0:ℝ)..1, (-2 * Complex.I)
        * ((oddExt F v * Real.sin ((n:ℝ) * Real.pi * v) : ℝ) : ℂ))
      = -2 * Complex.I
          * (((∫ v in (0:ℝ)..1, oddExt F v * Real.sin ((n:ℝ) * Real.pi * v) : ℝ)) : ℂ) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rw [hsplit, hcomp, hneg]
  rw [show -(∫ v in (0:ℝ)..1, fourier n (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
        + (∫ v in (0:ℝ)..1, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
      = (∫ v in (0:ℝ)..1, fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ))
        - (∫ v in (0:ℝ)..1, fourier n (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)) by ring]
  rw [hsub]
  rw [show (∫ v in (0:ℝ)..1, (fourier (-n) (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)
          - fourier n (↑v : AddCircle (2:ℝ)) * (oddExt F v : ℂ)))
      = ∫ v in (0:ℝ)..1, (-2 * Complex.I)
          * ((oddExt F v * Real.sin ((n:ℝ) * Real.pi * v) : ℝ) : ℂ) from by
        apply intervalIntegral.integral_congr
        intro v _; exact hpt v]
  exact hreal

/-! ### The shift `v = x + 1/2` -/

lemma oddExt_sin_integral_eq {F : ℝ → ℝ} (hF : Continuous F) (n : ℤ) :
    (∫ v in (0:ℝ)..1, oddExt F v * Real.sin ((n:ℝ)*Real.pi*v))
      = ∫ x in (-(1/2))..(1/2), F x * Real.sin ((n:ℝ)*Real.pi*(x + 1/2)) := by
  have h1 : (∫ v in (0:ℝ)..1, oddExt F v * Real.sin ((n:ℝ)*Real.pi*v))
      = ∫ v in (0:ℝ)..1, F (v - 1/2) * Real.sin ((n:ℝ)*Real.pi*v) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with v hv
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    rw [oddExt_eq_of_pos F hv.1]
  rw [h1]
  have h2 : (∫ x in (-(1/2))..(1/2), F (x + 1/2 - 1/2) * Real.sin ((n:ℝ)*Real.pi*(x + 1/2)))
      = ∫ v in (0:ℝ)..1, F (v - 1/2) * Real.sin ((n:ℝ)*Real.pi*v) := by
    have h := intervalIntegral.integral_comp_add_right (a := (-(1/2) : ℝ)) (b := (1/2))
      (fun v : ℝ => F (v - 1/2) * Real.sin ((n:ℝ)*Real.pi*v)) (1/2)
    rw [show (-(1/2) : ℝ) + 1/2 = 0 by norm_num,
        show (1/2 : ℝ) + 1/2 = 1 by norm_num] at h
    exact h
  rw [← h2]
  apply intervalIntegral.integral_congr
  intro x _
  simp only []
  rw [show x + 1/2 - 1/2 = x by ring]

/-- Casting the real sine integral over `[-1/2,1/2]` to `ℂ` (the form in which
the target statement asks for it). -/
lemma cast_oddExt_sin_integral {F : ℝ → ℝ} (n : ℤ) :
    (((∫ x in (-(1/2))..(1/2), F x * Real.sin ((n:ℝ)*Real.pi*(x+1/2))) : ℝ) : ℂ)
      = ∫ x in (-(1/2))..(1/2),
          (F x : ℂ) * ((Real.sin ((n:ℝ)*Real.pi*(x+1/2)) : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _
  push_cast
  ring

lemma fourierCoeff_oddExt {F : ℝ → ℝ} (hF : Continuous F) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1)
        (fun v : ℝ => ((Work.SmallBoxA0.oddExt F v : ℝ) : ℂ)) n
      = -Complex.I * ((∫ x in (-(1 / 2))..(1 / 2),
            F x * Real.sin ((n : ℝ) * Real.pi * (x + 1 / 2))) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  rw [show (1 : ℝ) - (-1) = 2 by norm_num]
  simp only [smul_eq_mul]
  rw [Complex.real_smul]
  rw [fourierCoeff_oddExt_keyA hF n]
  have hSC : (((∫ v in (0:ℝ)..1, oddExt F v * Real.sin ((n:ℝ)*Real.pi*v) : ℝ)) : ℂ)
      = (∫ x in (-(1/2))..(1/2),
          (F x : ℂ) * ((Real.sin ((n:ℝ)*Real.pi*(x+1/2)) : ℝ) : ℂ)) := by
    rw [oddExt_sin_integral_eq hF n]
    exact cast_oddExt_sin_integral n
  rw [hSC]
  rw [show ((1/2 : ℝ) : ℂ) = 1/2 by norm_num]
  ring

end

end Work.SmallBoxA0
