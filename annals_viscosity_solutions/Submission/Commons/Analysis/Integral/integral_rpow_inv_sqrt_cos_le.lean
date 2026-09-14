import Mathlib
import Submission.Commons.Analysis.Integral.integral_inv_sqrt_sq_add_le
import Submission.Commons.Analysis.Integral.pi_sqrt_log_bound

open MeasureTheory intervalIntegral Real

set_option autoImplicit false

namespace Commons.Analysis.Integral

/-- For `|u| ≤ π`, one has `(u/π)^2 ≤ sin(u/2)^2`. -/
lemma sq_div_pi_le_sin_sq_half {u : ℝ} (hu : |u| ≤ Real.pi) :
    (u / Real.pi)^2 ≤ Real.sin (u / 2)^2 := by
  have hkey : |u| / Real.pi ≤ Real.sin (|u| / 2) := by
    have h0 : 0 ≤ |u| / 2 := by positivity
    have h1 : |u| / 2 ≤ Real.pi / 2 := by linarith [abs_nonneg u, hu]
    have h := Real.mul_le_sin h0 h1
    have hh : 2 / Real.pi * (|u| / 2) = |u| / Real.pi := by ring
    rwa [hh] at h
  have h1 : 0 ≤ |u| / Real.pi := by positivity
  have h2 : 0 ≤ Real.sin (|u| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by linarith [abs_nonneg u, Real.pi_pos, hu])
  have hle : (|u| / Real.pi)^2 ≤ Real.sin (|u| / 2)^2 := by nlinarith [hkey, h1, h2]
  have e1 : (|u| / Real.pi)^2 = (u / Real.pi)^2 := by rw [div_pow, div_pow, sq_abs]
  have e2 : Real.sin (|u| / 2)^2 = Real.sin (u / 2)^2 := by
    rcases lt_or_ge 0 u with h | h
    · rw [abs_of_pos h]
    · rw [abs_of_nonpos h, neg_div, Real.sin_neg, neg_sq]
  rwa [e1, e2] at hle

/-- The identity `1 + cos θ = 2 sin((π - θ)/2)^2`. -/
lemma one_add_cos_eq_two_mul_sin_sq_half (θ : ℝ) :
    1 + Real.cos θ = 2 * Real.sin ((Real.pi - θ) / 2)^2 := by
  have hc : Real.cos θ = - Real.cos (Real.pi - θ) := by
    have := Real.cos_pi_sub θ; linarith
  have hgen (φ : ℝ) : 1 - Real.cos φ = 2 * Real.sin (φ / 2)^2 := by
    have hcs : Real.cos (φ / 2)^2 = 1 / 2 + Real.cos φ / 2 := by
      have h := Real.cos_sq (φ / 2)
      rwa [show (2 : ℝ) * (φ / 2) = φ by ring] at h
    have hss : Real.sin (φ / 2)^2 = 1 - Real.cos (φ / 2)^2 := Real.sin_sq (φ / 2)
    linarith [hcs, hss]
  rw [hc, show 1 + -Real.cos (Real.pi - θ) = 1 - Real.cos (Real.pi - θ) by ring]
  exact hgen (Real.pi - θ)

/-- For `θ ∈ [0, 2π]`, `2 ((π - θ)/π)^2 ≤ 1 + cos θ`. -/
lemma two_mul_div_pi_sq_le_one_add_cos (θ : ℝ) (h0 : 0 ≤ θ) (h2 : θ ≤ 2 * Real.pi) :
    2 * ((Real.pi - θ) / Real.pi)^2 ≤ 1 + Real.cos θ := by
  have hφ : |Real.pi - θ| ≤ Real.pi := by
    rw [abs_le]; constructor <;> linarith [Real.pi_pos]
  have hs := sq_div_pi_le_sin_sq_half hφ
  rw [one_add_cos_eq_two_mul_sin_sq_half θ]
  linarith [hs]

/-- Pointwise lower bound for the base `1 + v^2 + 2 v cos θ`. -/
lemma cos_int_base_le {v θ : ℝ} (hv : 0 < v) (h0 : 0 ≤ θ) (h2 : θ ≤ 2 * Real.pi) :
    (v - 1)^2 + (4 * v / Real.pi^2) * (Real.pi - θ)^2 ≤ 1 + v^2 + 2 * v * Real.cos θ := by
  have hge := two_mul_div_pi_sq_le_one_add_cos θ h0 h2
  have hπ2 : 0 < Real.pi^2 := by positivity
  have heq : 2 * ((Real.pi - θ) / Real.pi)^2 * Real.pi^2 = 2 * (Real.pi - θ)^2 := by
    rw [div_pow]; field_simp
  have hcleared : (2 : ℝ) * (Real.pi - θ)^2 ≤ (1 + Real.cos θ) * Real.pi^2 := by
    have h := mul_le_mul_of_nonneg_right hge (le_of_lt hπ2)
    rwa [heq] at h
  have hkey : 4 * v * (Real.pi - θ)^2 ≤ 2 * v * (1 + Real.cos θ) * Real.pi^2 := by
    nlinarith [hcleared, hv]
  have h2' : (4 * v / Real.pi^2) * (Real.pi - θ)^2 ≤ 2 * v * (1 + Real.cos θ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hπ2]
    nlinarith [hkey]
  nlinarith [h2']

theorem integral_rpow_inv_sqrt_cos_le {v : ℝ} (hv1 : (1 : ℝ) / 2 ≤ v) (hv2 : v ≤ 2)
    (hne : v ≠ 1) :
    ∫ θ in (0)..(2 * Real.pi), (1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2)
      ≤ 100 * |v - 1| ^ (-(1 : ℝ) / 2) := by
  have hvpos : 0 < v := by linarith
  set k : ℝ := 2 * Real.sqrt v / Real.pi with hk
  set σ : ℝ := (v - 1)^2 with hσ
  have hσpos : 0 < σ := by rw [hσ]; exact sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hkpos : 0 < k := by rw [hk]; positivity
  have hk2 : k^2 = 4 * v / Real.pi^2 := by
    rw [hk, div_pow, mul_pow, Real.sq_sqrt hvpos.le]; ring
  have hsqrtσ : Real.sqrt σ = |v - 1| := by rw [hσ, Real.sqrt_sq_eq_abs]
  have hb1 : ∀ θ : ℝ, (v - 1)^2 ≤ 1 + v^2 + 2 * v * Real.cos θ := by
    intro θ; nlinarith [Real.neg_one_le_cos θ, hvpos]
  have hv1sq : 0 < (v - 1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have habs1 : |v - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h2sv : 1 ≤ 2 * Real.sqrt v := by
    have h : (1 : ℝ) / 2 ≤ Real.sqrt v := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      nlinarith [hv1]
    linarith
  have hs4 : Real.sqrt σ / k ≤ Real.pi := by
    have hkey : |v - 1| ≤ 2 * Real.sqrt v := le_trans habs1 h2sv
    rw [hsqrtσ, hk, div_div_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt v)]
    nlinarith [hkey, Real.pi_pos]
  -- Step 1: pointwise comparison of the integrands.
  have step1 : (∫ θ in (0)..(2 * Real.pi), (1 + v^2 + 2 * v * Real.cos θ)^(-(1 : ℝ)/2))
      ≤ ∫ θ in (0)..(2 * Real.pi), (σ + k^2 * (Real.pi - θ)^2)^(-(1 : ℝ)/2) := by
    apply integral_mono_on (by linarith [Real.pi_pos])
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.rpow_const
        (f := fun θ : ℝ => 1 + v^2 + 2 * v * Real.cos θ) (s := Set.uIcc 0 (2 * Real.pi))
        (by fun_prop)
      intro x _
      left
      exact ne_of_gt (lt_of_lt_of_le hv1sq (hb1 x))
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.rpow_const
        (f := fun θ : ℝ => σ + k^2 * (Real.pi - θ)^2) (s := Set.uIcc 0 (2 * Real.pi))
        (by fun_prop)
      intro x _
      left
      positivity
    · intro θ hθ
      have hle : σ + k^2 * (Real.pi - θ)^2 ≤ 1 + v^2 + 2 * v * Real.cos θ := by
        rw [hσ, hk2]; exact cos_int_base_le hvpos hθ.1 hθ.2
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
  -- Step 2: translate the integration variable.
  have step2 : (∫ θ in (0)..(2 * Real.pi), (σ + k^2 * (Real.pi - θ)^2)^(-(1 : ℝ)/2))
      = ∫ s in (-Real.pi)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2) := by
    have h := integral_comp_sub_left (fun s : ℝ => (σ + k^2 * s^2)^(-(1 : ℝ)/2)) Real.pi
      (a := 0) (b := 2 * Real.pi)
    rw [show Real.pi - 2 * Real.pi = -Real.pi by ring, show Real.pi - (0 : ℝ) = Real.pi by ring]
      at h
    exact h
  have hHcont : Continuous (fun s : ℝ => (σ + k^2 * s^2)^(-(1 : ℝ)/2)) := by
    rw [continuous_iff_continuousAt]
    intro s
    have hb : Continuous fun s : ℝ => σ + k^2 * s^2 := by fun_prop
    exact (continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (by positivity)))).comp hb.continuousAt
  -- Step 3: exploit evenness.
  have step3 : (∫ s in (-Real.pi)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2))
      = 2 * ∫ s in (0)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2) := by
    have hsplit : (∫ s in (-Real.pi)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2))
        = (∫ s in (-Real.pi)..0, (σ + k^2 * s^2)^(-(1 : ℝ)/2))
          + (∫ s in (0)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2)) :=
      (integral_add_adjacent_intervals (hHcont.intervalIntegrable (-Real.pi) 0)
        (hHcont.intervalIntegrable 0 Real.pi)).symm
    have hneg : (∫ s in (-Real.pi)..0, (σ + k^2 * s^2)^(-(1 : ℝ)/2))
        = ∫ s in (0)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2) := by
      have hcomp := integral_comp_neg (fun s : ℝ => (σ + k^2 * s^2)^(-(1 : ℝ)/2))
        (a := -Real.pi) (b := 0)
      have hcongr : (∫ x in (-Real.pi)..0, (σ + k^2 * (-x)^2)^(-(1 : ℝ)/2))
          = ∫ x in (-Real.pi)..0, (σ + k^2 * x^2)^(-(1 : ℝ)/2) := by
        apply integral_congr
        intro x _
        simp only [neg_sq]
      rw [hcongr] at hcomp
      simpa using hcomp
    rw [hsplit, hneg]; ring
  -- Step 4: the elementary integral estimate.
  have step4 : (∫ s in (0)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2))
      ≤ (1/k) * (1 + Real.log (Real.pi * k / Real.sqrt σ)) :=
    integral_inv_sqrt_sq_add_le hσpos hkpos Real.pi_pos hs4
  -- Step 5: numeric endgame.
  have step5 : (2/k) * (1 + Real.log (Real.pi * k / Real.sqrt σ))
      ≤ 100 * |v - 1| ^ (-(1 : ℝ)/2) := by
    have hk2' : 2/k = Real.pi / Real.sqrt v := by rw [hk]; field_simp
    have harg : Real.pi * k / Real.sqrt σ = 2 * Real.sqrt v / |v - 1| := by
      rw [hk, hsqrtσ]; field_simp
    rw [hk2', harg]
    exact pi_sqrt_log_bound hv1 hv2 hne
  calc (∫ θ in (0)..(2 * Real.pi), (1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ)/2))
      ≤ ∫ θ in (0)..(2 * Real.pi), (σ + k^2 * (Real.pi - θ)^2)^(-(1 : ℝ)/2) := step1
    _ = ∫ s in (-Real.pi)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2) := step2
    _ = 2 * ∫ s in (0)..Real.pi, (σ + k^2 * s^2)^(-(1 : ℝ)/2) := step3
    _ ≤ 2 * ((1/k) * (1 + Real.log (Real.pi * k / Real.sqrt σ))) :=
        mul_le_mul_of_nonneg_left step4 (by norm_num)
    _ = (2/k) * (1 + Real.log (Real.pi * k / Real.sqrt σ)) := by ring
    _ ≤ 100 * |v - 1| ^ (-(1 : ℝ)/2) := step5

end Commons.Analysis.Integral
