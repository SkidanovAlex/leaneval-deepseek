import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

open MeasureTheory

/-- Subadditivity of `x ↦ x ^ p` for `0 < p ≤ 1`: for `0 ≤ x ≤ y` we have
`y ^ p - x ^ p ≤ (y - x) ^ p`. -/
lemma rpow_sub_le_rpow_sub {p x y : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ p - x ^ p ≤ (y - x) ^ p := by
  have h := Real.rpow_add_le_add_rpow hx (sub_nonneg.mpr hxy) hp.le hp1
  have hx' : x + (y - x) = y := by ring
  rw [hx'] at h
  linarith

/-- `(4 / π) ^ (p - 1) = (π / 4) ^ (1 - p)`. -/
lemma four_div_pi_rpow (p : ℝ) : (4 / Real.pi) ^ (p - 1) = (Real.pi / 4) ^ (1 - p) := by
  have hc : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h1 : (Real.pi / 4)⁻¹ = 4 / Real.pi := inv_div _ _
  calc (4 / Real.pi) ^ (p - 1) = ((Real.pi / 4)⁻¹) ^ (p - 1) := by rw [h1]
    _ = ((Real.pi / 4) ^ (p - 1))⁻¹ := by rw [Real.inv_rpow hc]
    _ = (Real.pi / 4) ^ (-(p - 1)) := (Real.rpow_neg hc (p - 1)).symm
    _ = (Real.pi / 4) ^ (1 - p) := by rw [show -(p - 1) = 1 - p by ring]

theorem integral_sin_two_rpow_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {θ θ' : ℝ}
    (h0 : 0 < θ) (hle : θ ≤ θ') (h1 : θ' < Real.pi / 2) :
    ∫ σ in θ..θ', Real.sin (2 * σ) ^ (p - 1) ≤ 2 * (Real.pi / 4) ^ (1 - p) / p * (θ' - θ) ^ p := by
  have hpm1 : p - 1 ≤ 0 := by linarith
  have h4pi : (0 : ℝ) < 4 / Real.pi := by positivity
  have hc4 : (0 : ℝ) < Real.pi / 4 := by positivity
  -- `sin (2σ) > 0` on the whole interval
  have hsin_pos : ∀ σ ∈ Set.Icc θ θ', 0 < Real.sin (2 * σ) := by
    intro σ hσ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1, h0]) (by linarith [hσ.2, h1])
  -- the pointwise comparison
  have hpt : ∀ σ ∈ Set.Icc θ θ', Real.sin (2 * σ) ^ (p - 1) ≤
      (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) := by
    intro σ hσ
    have hσ0 : 0 < σ := lt_of_lt_of_le h0 hσ.1
    have hσL : σ < Real.pi / 2 := lt_of_le_of_lt hσ.2 h1
    have hc_nn : 0 ≤ (Real.pi / 4) ^ (1 - p) := Real.rpow_nonneg hc4.le _
    rcases le_or_gt σ (Real.pi / 4) with hs | hs
    · -- `σ ≤ π/4`: use `sin (2σ) ≥ (4/π) σ`
      have hmul : 2 / Real.pi * (2 * σ) ≤ Real.sin (2 * σ) :=
        Real.mul_le_sin (by linarith) (by linarith)
      have hge : 4 / Real.pi * σ ≤ Real.sin (2 * σ) := by
        rw [show (4 : ℝ) / Real.pi * σ = 2 / Real.pi * (2 * σ) by ring]
        exact hmul
      have hbase : 0 < 4 / Real.pi * σ := mul_pos h4pi hσ0
      have hrw : (4 / Real.pi * σ) ^ (p - 1) = (Real.pi / 4) ^ (1 - p) * σ ^ (p - 1) := by
        rw [Real.mul_rpow h4pi.le hσ0.le, four_div_pi_rpow]
      calc Real.sin (2 * σ) ^ (p - 1) ≤ (4 / Real.pi * σ) ^ (p - 1) :=
            Real.rpow_le_rpow_of_nonpos hbase hge hpm1
        _ = (Real.pi / 4) ^ (1 - p) * σ ^ (p - 1) := hrw
        _ ≤ (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)) hc_nn
    · -- `σ > π/4`: use `sin (2σ) = sin (π - 2σ) ≥ (4/π) (π/2 - σ)`
      have hmul : 2 / Real.pi * (Real.pi - 2 * σ) ≤ Real.sin (Real.pi - 2 * σ) :=
        Real.mul_le_sin (by linarith) (by linarith)
      rw [Real.sin_pi_sub] at hmul
      have hge : 4 / Real.pi * (Real.pi / 2 - σ) ≤ Real.sin (2 * σ) := by
        rw [show (4 : ℝ) / Real.pi * (Real.pi / 2 - σ)
              = 2 / Real.pi * (Real.pi - 2 * σ) by ring]
        exact hmul
      have hbase : 0 < 4 / Real.pi * (Real.pi / 2 - σ) := mul_pos h4pi (by linarith)
      have hrw : (4 / Real.pi * (Real.pi / 2 - σ)) ^ (p - 1)
          = (Real.pi / 4) ^ (1 - p) * (Real.pi / 2 - σ) ^ (p - 1) := by
        rw [Real.mul_rpow h4pi.le (by linarith), four_div_pi_rpow]
      calc Real.sin (2 * σ) ^ (p - 1) ≤ (4 / Real.pi * (Real.pi / 2 - σ)) ^ (p - 1) :=
            Real.rpow_le_rpow_of_nonpos hbase hge hpm1
        _ = (Real.pi / 4) ^ (1 - p) * (Real.pi / 2 - σ) ^ (p - 1) := hrw
        _ ≤ (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left (Real.rpow_nonneg hσ0.le _)) hc_nn
  -- continuity of the two integrands
  have hui : Set.uIcc θ θ' = Set.Icc θ θ' := Set.uIcc_of_le hle
  have hid : ContinuousOn (fun σ : ℝ => σ ^ (p - 1)) (Set.uIcc θ θ') := by
    refine continuous_id.continuousOn.rpow_const ?_
    intro σ hσ
    left
    rw [hui] at hσ
    exact ne_of_gt (lt_of_lt_of_le h0 hσ.1)
  have hsub_c : ContinuousOn (fun σ : ℝ => Real.pi / 2 - σ) (Set.uIcc θ θ') :=
    continuous_const.continuousOn.sub continuous_id.continuousOn
  have h2c : ContinuousOn (fun σ : ℝ => (Real.pi / 2 - σ) ^ (p - 1)) (Set.uIcc θ θ') := by
    refine hsub_c.rpow_const ?_
    intro σ hσ
    left
    rw [hui] at hσ
    exact ne_of_gt (by linarith [hσ.2, h1])
  have hcontf : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ) ^ (p - 1)) (Set.uIcc θ θ') := by
    have hsin : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ)) (Set.uIcc θ θ') :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    refine hsin.rpow_const ?_
    intro σ hσ
    left
    rw [hui] at hσ
    exact ne_of_gt (hsin_pos σ hσ)
  have hcontg : ContinuousOn (fun σ : ℝ =>
      (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)))
      (Set.uIcc θ θ') :=
    continuousOn_const.mul (hid.add h2c)
  -- monotonicity of the interval integral
  have hmono : ∫ σ in θ..θ', Real.sin (2 * σ) ^ (p - 1) ≤
      ∫ σ in θ..θ', (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
    intervalIntegral.integral_mono_on hle (ContinuousOn.intervalIntegrable hcontf)
      (ContinuousOn.intervalIntegrable hcontg) hpt
  -- explicit evaluation of the comparison integral
  have hint1 : ∫ σ in θ..θ', σ ^ (p - 1) = (θ' ^ p - θ ^ p) / p := by
    rw [integral_rpow (Or.inl (show (-1 : ℝ) < p - 1 by linarith))]
    rw [show p - 1 + 1 = p by ring]
  have hint2 : ∫ σ in θ..θ', (Real.pi / 2 - σ) ^ (p - 1)
      = ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p) / p := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (p - 1)) (Real.pi / 2)]
    rw [integral_rpow (Or.inl (show (-1 : ℝ) < p - 1 by linarith))]
    rw [show p - 1 + 1 = p by ring]
  have hint_add : ∫ σ in θ..θ', (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1))
      = (∫ σ in θ..θ', σ ^ (p - 1)) + ∫ σ in θ..θ', (Real.pi / 2 - σ) ^ (p - 1) :=
    intervalIntegral.integral_add (ContinuousOn.intervalIntegrable hid)
      (ContinuousOn.intervalIntegrable h2c)
  have hInt : ∫ σ in θ..θ', (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1))
      = (θ' ^ p - θ ^ p) / p + ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p) / p := by
    rw [hint_add, hint1, hint2]
  have hb1 : θ' ^ p - θ ^ p ≤ (θ' - θ) ^ p := rpow_sub_le_rpow_sub hp hp1 h0.le hle
  have hb2 : (Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p ≤ (θ' - θ) ^ p := by
    have h := rpow_sub_le_rpow_sub (p := p) hp hp1 (x := Real.pi / 2 - θ') (y := Real.pi / 2 - θ)
      (by linarith) (by linarith)
    rwa [show Real.pi / 2 - θ - (Real.pi / 2 - θ') = θ' - θ by ring] at h
  have hsum_bound : ∫ σ in θ..θ', (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1))
      ≤ 2 * (θ' - θ) ^ p / p := by
    rw [hInt]
    have hkey : θ' ^ p - θ ^ p + ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p)
        ≤ 2 * (θ' - θ) ^ p := by linarith
    calc (θ' ^ p - θ ^ p) / p + ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p) / p
        = (θ' ^ p - θ ^ p + ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p)) / p := by ring
      _ ≤ (2 * (θ' - θ) ^ p) / p := div_le_div_of_nonneg_right hkey hp.le
      _ = 2 * (θ' - θ) ^ p / p := rfl
  have hc_nn : 0 ≤ (Real.pi / 4) ^ (1 - p) := Real.rpow_nonneg hc4.le _
  calc ∫ σ in θ..θ', Real.sin (2 * σ) ^ (p - 1)
      ≤ ∫ σ in θ..θ', (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
        hmono
    _ = (Real.pi / 4) ^ (1 - p)
          * ∫ σ in θ..θ', (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (Real.pi / 4) ^ (1 - p) * (2 * (θ' - θ) ^ p / p) :=
        mul_le_mul_of_nonneg_left hsum_bound hc_nn
    _ = 2 * (Real.pi / 4) ^ (1 - p) / p * (θ' - θ) ^ p := by ring

end Work.FTS_RegExport.THL
