import Mathlib
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop
import Submission.Work.Asymptotics.KPlusXiDefs

/-!
# The axis bound for `(kpre)⁻¹`

This file proves `Work.Residues.kpre_inv_axis_bound`.  Recall
`kpre z τ = 2·1728·π·Δ(z)·(j τ − j z)`
(`Work.Residues.kpre`), so on the contour `z = it` (`1 ≤ t ≤ Im τ − 1`)

`‖(kpre (it) τ)⁻¹‖ = 1/(2·1728·π·‖Δ(it)‖·‖j τ − j(it)‖)`.

Two estimates control the two factors in the denominator:

* `‖Δ(it)‖ ≥ (1/2)e^{−2πt}` is the given hypothesis `hΔl`;
* `‖j τ − j(it)‖ ≥ (1/16 − (27/4)e^{−2π}) e^{2π Im τ}` is proved here from
  `‖E₄ τ‖ ≥ 1/2` near the cusp (`Work.Asymptotics.exists_bound_norm_E4Fun_atImInfty`),
  `‖Δ τ‖ ≤ 2e^{−2π Im τ}` (`hΔu`) and `‖j(it)‖ ≤ (27/4)e^{2πt}`
  (from `hΔl` and the upper bound `hE4u`).

The only place where the numerical constant `1/16 − (27/4)e^{−2π} > 0` really enters
is `kpre_axis_const_pos`, proved by the crude bound `e^{2π} > e^6 > 343 > 108`.
-/

namespace Work.Residues

open UpperHalfPlane
open Work.Kernels

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Elementary numerical and norm identities -/

/-- The numerical constant `1/16 - (27/4)e^{-2π}` is positive. -/
lemma kpre_axis_const_pos : (0:ℝ) < 1/16 - 27/4 * Real.exp (-(2*Real.pi)) := by
  have h1 : Real.exp 1 > 2.7182818283 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    have h := Real.exp_nat_mul (x := (1:ℝ)) 2
    rw [show (↑(2:ℕ) : ℝ) * 1 = 2 by norm_num] at h
    exact h
  have h2gt : (7:ℝ) < Real.exp 2 := by
    rw [h2]
    calc (7:ℝ) < (2.7182818283)^2 := by norm_num
      _ < (Real.exp 1)^2 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h6 : Real.exp 6 = Real.exp 2 ^ 3 := by
    have h := Real.exp_nat_mul (x := (2:ℝ)) 3
    rw [show (↑(3:ℕ) : ℝ) * 2 = 6 by norm_num] at h
    exact h
  have h6gt : (108:ℝ) < Real.exp 6 := by
    rw [h6]
    calc (108:ℝ) < 7^3 := by norm_num
      _ < (Real.exp 2)^3 := pow_lt_pow_left₀ h2gt (by norm_num) (by norm_num)
  have h2pi : (6:ℝ) < 2*Real.pi := by nlinarith [Real.pi_gt_three]
  have hexp2pi_gt : (108:ℝ) < Real.exp (2*Real.pi) := lt_trans h6gt (Real.exp_lt_exp.mpr h2pi)
  have hinv : Real.exp (-(2 * Real.pi)) < 1/108 := by
    rw [Real.exp_neg]
    rw [show (Real.exp (2*Real.pi))⁻¹ = 1/Real.exp (2*Real.pi) by rw [one_div]]
    exact one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 108) hexp2pi_gt
  have hlt : 27/4 * Real.exp (-(2 * Real.pi)) < 1/16 := by
    calc 27/4 * Real.exp (-(2 * Real.pi)) < 27/4 * (1/108) :=
          mul_lt_mul_of_pos_left hinv (by norm_num)
      _ = 1/16 := by norm_num
  linarith

/-- The modulus of the prefactor: `‖kpre z τ‖ = 2·1728·π·‖Δ z‖·‖j τ - j z‖`. -/
lemma kpre_axis_norm (z τ : UpperHalfPlane) : ‖Work.Residues.kpre z τ‖ =
    3456 * Real.pi * ‖DeltaFun z‖ * ‖jInvariantFun τ - jInvariantFun z‖ := by
  rw [Work.Residues.kpre, show Work.Kernels.c1728 = (1728 : ℂ) from rfl]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num

/-- The elementary identity `1/(A·x⁻¹·z) = (1/A)·x·z⁻¹`. -/
lemma inv_mul_axis_identity (A : ℝ) (hA : A ≠ 0) (x z : ℝ) (hx : x ≠ 0) (hz : z ≠ 0) :
    1/(A * x⁻¹ * z) = (1/A) * x * z⁻¹ := by
  field_simp

/-! ## The three estimates on `j` -/

/-- Lower bound for `‖j τ‖` away from the cusp: from `‖E₄ τ‖ ≥ 1/2` and
`‖Δ τ‖ ≤ 2e^{-2π Im τ}` one gets `‖j τ‖ ≥ e^{2π Im τ}/16`. -/
lemma jInvariant_axis_lower
    (hΔu : ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)))
    {A : ℝ} (hA : ∀ τ : UpperHalfPlane, A ≤ τ.im → (1/2:ℝ) ≤ ‖E4Fun τ‖) :
    ∀ τ : UpperHalfPlane, max A 1 ≤ τ.im →
      (1/16 : ℝ) * Real.exp (2 * Real.pi * τ.im) ≤ ‖jInvariantFun τ‖ := by
  intro τ hτ
  have hE4τ : (1/2:ℝ) ≤ ‖E4Fun τ‖ := hA τ (le_trans (le_max_left _ _) hτ)
  have hDτ : ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2*Real.pi*τ.im)) :=
    hΔu τ (le_trans (le_max_right _ _) hτ)
  have hDτpos : 0 < ‖DeltaFun τ‖ := norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  have hj : ‖jInvariantFun τ‖ = ‖E4Fun τ‖^3 / ‖DeltaFun τ‖ := by
    simp only [jInvariantFun, norm_div, norm_pow]
  rw [hj]
  have hnum : (1/2:ℝ)^3 ≤ ‖E4Fun τ‖^3 := pow_le_pow_left₀ (by norm_num) hE4τ 3
  have step1 : (1/2:ℝ)^3 / ‖DeltaFun τ‖ ≤ ‖E4Fun τ‖^3 / ‖DeltaFun τ‖ :=
    div_le_div_of_nonneg_right hnum hDτpos.le
  have step2 : (1/2:ℝ)^3 / (2 * Real.exp (-(2*Real.pi*τ.im))) ≤ (1/2:ℝ)^3 / ‖DeltaFun τ‖ :=
    div_le_div_of_nonneg_left (by norm_num) hDτpos hDτ
  have heq : (1/16 : ℝ) * Real.exp (2 * Real.pi * τ.im)
      = (1/2:ℝ)^3 / (2 * Real.exp (-(2*Real.pi*τ.im))) := by
    rw [Real.exp_neg]
    have h : Real.exp (2 * Real.pi * τ.im) ≠ 0 := Real.exp_ne_zero _
    field_simp
    ring
  rw [heq]
  linarith [step1, step2]

/-- Upper bound for `‖j (it)‖` on the imaginary axis: from `‖Δ(it)‖ ≥ (1/2)e^{-2πt}`
and `‖E₄(it)‖ ≤ 3/2` one gets `‖j(it)‖ ≤ (27/4)e^{2πt}`. -/
lemma jInvariant_imagAxis_upper
    (hΔl : ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤ ‖DeltaFun (imagAxis t ht)‖)
    (hE4u : ∀ τ : UpperHalfPlane, 1 ≤ τ.im → ‖E4Fun τ‖ ≤ 3 / 2) :
    ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖jInvariantFun (imagAxis t ht)‖ ≤ 27/4 * Real.exp (2*Real.pi*t) := by
  intro t ht ht1
  have hz : (imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  have hE4z : ‖E4Fun (imagAxis t ht)‖ ≤ 3/2 := hE4u _ (by rw [hz]; exact ht1)
  have hDzl : (1/2:ℝ) * Real.exp (-(2*Real.pi*t)) ≤ ‖DeltaFun (imagAxis t ht)‖ := hΔl t ht ht1
  have hDzpos : 0 < ‖DeltaFun (imagAxis t ht)‖ :=
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
  have hj : ‖jInvariantFun (imagAxis t ht)‖
      = ‖E4Fun (imagAxis t ht)‖^3 / ‖DeltaFun (imagAxis t ht)‖ := by
    simp only [jInvariantFun, norm_div, norm_pow]
  rw [hj]
  have hnum : ‖E4Fun (imagAxis t ht)‖^3 ≤ (3/2:ℝ)^3 :=
    pow_le_pow_left₀ (norm_nonneg _) hE4z 3
  have step1 : ‖E4Fun (imagAxis t ht)‖^3 / ‖DeltaFun (imagAxis t ht)‖
      ≤ (3/2:ℝ)^3 / ‖DeltaFun (imagAxis t ht)‖ :=
    div_le_div_of_nonneg_right hnum hDzpos.le
  have hdenpos : 0 < (1/2:ℝ) * Real.exp (-(2*Real.pi*t)) := by positivity
  have step2 : (3/2:ℝ)^3 / ‖DeltaFun (imagAxis t ht)‖
      ≤ (3/2:ℝ)^3 / ((1/2:ℝ) * Real.exp (-(2*Real.pi*t))) :=
    div_le_div_of_nonneg_left (by norm_num) hdenpos hDzl
  have heq : (3/2:ℝ)^3 / ((1/2:ℝ) * Real.exp (-(2*Real.pi*t)))
      = 27/4 * Real.exp (2*Real.pi*t) := by
    rw [Real.exp_neg]
    have h : Real.exp (2 * Real.pi * t) ≠ 0 := Real.exp_ne_zero _
    field_simp
    ring
  linarith [step1, step2, heq.le, heq.ge]

/-- Lower bound for the difference `‖j τ - j(it)‖` in the strip `t ≤ Im τ - 1`, where
`j τ` dominates `j(it)` by a factor `e^{2π}`. -/
lemma jInvariant_axis_diff_lower
    (hΔu : ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)))
    (hΔl : ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤ ‖DeltaFun (imagAxis t ht)‖)
    (hE4u : ∀ τ : UpperHalfPlane, 1 ≤ τ.im → ‖E4Fun τ‖ ≤ 3 / 2)
    {A : ℝ} (hA : ∀ τ : UpperHalfPlane, A ≤ τ.im → (1/2:ℝ) ≤ ‖E4Fun τ‖) :
    ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), max A 1 ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      (1/16 - 27/4 * Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im)
        ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := by
  intro τ t ht hτ ht1 htle
  have hjτ := jInvariant_axis_lower hΔu hA τ hτ
  have hjz := jInvariant_imagAxis_upper hΔl hE4u t ht ht1
  have hsub : ‖jInvariantFun τ‖ - ‖jInvariantFun (imagAxis t ht)‖
      ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := norm_sub_norm_le _ _
  have hexp_le : Real.exp (2*Real.pi*t) ≤ Real.exp (-(2*Real.pi)) * Real.exp (2*Real.pi*τ.im) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h : -(2*Real.pi) + 2*Real.pi*τ.im = 2*Real.pi*(τ.im - 1) := by ring
    rw [h]
    nlinarith [Real.pi_pos, htle]
  have h2 : (27/4) * Real.exp (2*Real.pi*t)
      ≤ (27/4) * (Real.exp (-(2*Real.pi)) * Real.exp (2*Real.pi*τ.im)) :=
    mul_le_mul_of_nonneg_left hexp_le (by norm_num)
  linarith [hsub, hjτ, hjz, h2]

/-! ## The main bound -/

theorem kpre_inv_axis_bound
    (hΔu : ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)))
    (hΔl : ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤
        ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖)
    (hE4u : ∀ τ : UpperHalfPlane, 1 ≤ τ.im → ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2) :
    ∃ H K : ℝ, 0 < K ∧ 0 ≤ H ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
        ‖(Work.Residues.kpre (Work.Kernels.imagAxis t ht) τ)⁻¹‖
          ≤ K * Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨A, hA⟩ := Work.Asymptotics.exists_bound_norm_E4Fun_atImInfty
  have hc : (0:ℝ) < 1/16 - 27/4 * Real.exp (-(2*Real.pi)) := kpre_axis_const_pos
  refine ⟨max A 1, 1/(1728*Real.pi*(1/16 - 27/4*Real.exp (-(2*Real.pi)))), ?_, ?_, ?_⟩
  · exact one_div_pos.mpr (by positivity)
  · exact le_trans zero_le_one (le_max_right _ _)
  · intro τ t ht hτ ht1 htle
    have hjd := jInvariant_axis_diff_lower hΔu hΔl hE4u hA τ t ht hτ ht1 htle
    have hDzl : (1/2:ℝ) * Real.exp (-(2*Real.pi*t)) ≤ ‖DeltaFun (imagAxis t ht)‖ := hΔl t ht ht1
    have hkn := kpre_axis_norm (imagAxis t ht) τ
    have hpos : 0 < 1728*Real.pi*(1/16 - 27/4*Real.exp (-(2*Real.pi))) * Real.exp (-(2*Real.pi*t)) * Real.exp (2*Real.pi*τ.im) := by positivity
    have hchain : 1728*Real.pi*(1/16 - 27/4*Real.exp (-(2*Real.pi))) * Real.exp (-(2*Real.pi*t)) * Real.exp (2*Real.pi*τ.im)
        ≤ ‖Work.Residues.kpre (imagAxis t ht) τ‖ := by
      rw [hkn]
      have h1 : (3456*Real.pi) * ((1/2) * Real.exp (-(2*Real.pi*t)))
          ≤ (3456*Real.pi) * ‖DeltaFun (imagAxis t ht)‖ :=
        mul_le_mul_of_nonneg_left hDzl (by positivity)
      calc 1728*Real.pi*(1/16 - 27/4*Real.exp (-(2*Real.pi))) * Real.exp (-(2*Real.pi*t)) * Real.exp (2*Real.pi*τ.im)
          = (3456*Real.pi) * ((1/2) * Real.exp (-(2*Real.pi*t)))
              * ((1/16 - 27/4*Real.exp (-(2*Real.pi))) * Real.exp (2*Real.pi*τ.im)) := by ring
        _ ≤ (3456*Real.pi) * ‖DeltaFun (imagAxis t ht)‖
              * ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ :=
            mul_le_mul h1 hjd (by positivity) (by positivity)
    calc ‖(Work.Residues.kpre (imagAxis t ht) τ)⁻¹‖
        = 1/‖Work.Residues.kpre (imagAxis t ht) τ‖ := by rw [norm_inv, one_div]
      _ ≤ 1/(1728*Real.pi*(1/16 - 27/4*Real.exp (-(2*Real.pi))) * Real.exp (-(2*Real.pi*t)) * Real.exp (2*Real.pi*τ.im)) :=
          one_div_le_one_div_of_le hpos hchain
      _ = 1/(1728*Real.pi*(1/16 - 27/4*Real.exp (-(2*Real.pi)))) * Real.exp (2*Real.pi*t) * Real.exp (-(2*Real.pi*τ.im)) := by
          have h1 : Real.exp (-(2*Real.pi*t)) = (Real.exp (2*Real.pi*t))⁻¹ := Real.exp_neg _
          have h2 : Real.exp (-(2*Real.pi*τ.im)) = (Real.exp (2*Real.pi*τ.im))⁻¹ := Real.exp_neg _
          rw [h1, h2]
          exact inv_mul_axis_identity _ (by positivity) _ _ (Real.exp_ne_zero _) (Real.exp_ne_zero _)

end

end Work.Residues
