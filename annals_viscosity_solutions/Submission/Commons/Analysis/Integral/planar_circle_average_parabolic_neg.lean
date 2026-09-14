import Mathlib
import Submission.Commons.Analysis.Integral.sup_circle_mean_eq_large_s
import Submission.Commons.Analysis.Integral.integral_sqrt_sq_sub_one_le
import Submission.Commons.Analysis.Integral.integral_sqrt_sq_sub_one_le_quarter
import Submission.Commons.Analysis.Integral.circle_l2_mean_le_rpow_eighth
import Submission.Commons.Analysis.Integral.integrableOn_l2_rpow_eighth_bound_zero_one
import Submission.Commons.Analysis.Integral.integral_l2_rpow_eighth_bound_zero_one
import Submission.Commons.Analysis.Integral.integrableOn_l2_rpow_eighth_bound_half
import Submission.Commons.Analysis.Integral.integral_l2_rpow_eighth_bound_half
import Submission.Commons.Analysis.Integral.integrableOn_sqrt_sq_sub_one_Ioi_sqrt_two

namespace Commons.Analysis.Integral

open MeasureTheory Real Set

/-- Sup-norm (Chebyshev) circle mean: the average over the unit circle of the reciprocal
of the sup-distance from `(s,0)` to the circle point `(cos θ, sin θ)`. -/
noncomputable def supCircleMean (s : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), (max |s - Real.cos θ| |Real.sin θ|)⁻¹

/-- Euclidean (l2) circle mean of `1/dist`. -/
noncomputable def l2CircleMean (s : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in (0)..Real.pi, (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹

/-- Upper bound for the l2-circle mean valid on `(0,1)` (from two AGM steps). -/
private noncomputable def l2Bound (x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ (-(1 / 8 : ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - x ^ 2)))

private lemma norm_pair_eq (r ρ θ : ℝ) (hρ : 0 < ρ) :
    ‖(r, (0:ℝ)) - ρ • (Real.cos θ, Real.sin θ)‖
      = ρ * max |r/ρ - Real.cos θ| |Real.sin θ| := by
  have hs : (r, (0:ℝ)) - ρ • (Real.cos θ, Real.sin θ) = (r - ρ * Real.cos θ, -(ρ * Real.sin θ)) := by
    ext <;> simp
  rw [hs, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_mul,
    abs_of_nonneg hρ.le]
  have h1 : |r - ρ * Real.cos θ| = ρ * |r/ρ - Real.cos θ| := by
    rw [show ρ * |r/ρ - Real.cos θ| = |ρ| * |r/ρ - Real.cos θ| by rw [abs_of_nonneg hρ.le],
        ← abs_mul]
    congr 1
    field_simp
  rw [h1, mul_max_of_nonneg _ _ hρ.le]

private lemma inner_recip (r ρ θ : ℝ) (hρ : 0 < ρ) :
    (‖(r, (0:ℝ)) - ρ • (Real.cos θ, Real.sin θ)‖)⁻¹
      = (1/ρ) * (max |r/ρ - Real.cos θ| |Real.sin θ|)⁻¹ := by
  rw [norm_pair_eq r ρ θ hρ, mul_inv, one_div]

private lemma inner_integral_eq (c ρ t : ℝ) (hρ : 0 < ρ) :
    (∫ θ in (0)..(2 * Real.pi),
        (‖(c * t ^ (2 / 3 : ℝ)) • (1, 0) - ρ • (Real.cos θ, Real.sin θ)‖)⁻¹)
      = (1/ρ) * ∫ θ in (0)..(2 * Real.pi),
          (max |(c * t ^ (2 / 3 : ℝ))/ρ - Real.cos θ| |Real.sin θ|)⁻¹ := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  have h : (c * t ^ (2 / 3 : ℝ)) • ((1,0):ℝ×ℝ) = (c * t ^ (2 / 3 : ℝ), 0) := by ext <;> simp
  rw [h]
  exact inner_recip _ _ _ hρ

private lemma continuous_max_inv {s : ℝ} (hs1 : s ≠ 1) (hs2 : s ≠ -1) :
    Continuous fun θ : ℝ => (max |s - Real.cos θ| |Real.sin θ|)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) ?_
  intro θ
  by_contra hc
  have hzero : max |s - Real.cos θ| |Real.sin θ| = 0 := hc
  have h1 : |s - Real.cos θ| = 0 :=
    le_antisymm (hzero ▸ le_max_left _ _) (abs_nonneg _)
  have h2 : |Real.sin θ| = 0 :=
    le_antisymm (hzero ▸ le_max_right _ _) (abs_nonneg _)
  have hcos : Real.cos θ = s := by
    have := abs_eq_zero.mp h1
    linarith
  have hsin : Real.sin θ = 0 := abs_eq_zero.mp h2
  have hsq : s ^ 2 = 1 := by
    rw [← hcos]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact hs1 h
  · exact hs2 h

private lemma supCircleMean_eq_pi {s : ℝ} (hs1 : s ≠ 1) (hs2 : s ≠ -1) :
    supCircleMean s
      = (1 / Real.pi) * ∫ θ in (0)..Real.pi, (max |s - Real.cos θ| |Real.sin θ|)⁻¹ := by
  have hcont : Continuous fun θ : ℝ => (max |s - Real.cos θ| |Real.sin θ|)⁻¹ :=
    continuous_max_inv hs1 hs2
  have hsym : ∀ θ : ℝ,
      (max |s - Real.cos (2 * Real.pi - θ)| |Real.sin (2 * Real.pi - θ)|)⁻¹
        = (max |s - Real.cos θ| |Real.sin θ|)⁻¹ := by
    intro θ
    rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub, abs_neg]
  have hsplit : (∫ θ in (0)..Real.pi, (max |s - Real.cos θ| |Real.sin θ|)⁻¹)
        + (∫ θ in Real.pi..(2 * Real.pi), (max |s - Real.cos θ| |Real.sin θ|)⁻¹)
      = (∫ θ in (0)..(2 * Real.pi), (max |s - Real.cos θ| |Real.sin θ|)⁻¹) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hreflect : (∫ θ in Real.pi..(2 * Real.pi), (max |s - Real.cos θ| |Real.sin θ|)⁻¹)
      = (∫ θ in (0)..Real.pi, (max |s - Real.cos θ| |Real.sin θ|)⁻¹) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := Real.pi)
      (fun θ : ℝ => (max |s - Real.cos θ| |Real.sin θ|)⁻¹) (2 * Real.pi)
    rw [show (2:ℝ) * Real.pi - Real.pi = Real.pi by ring,
        show (2:ℝ) * Real.pi - 0 = 2 * Real.pi by ring] at h
    rw [← h]
    exact intervalIntegral.integral_congr (fun x _ => hsym x)
  have hfin : supCircleMean s
      = (1 / (2 * Real.pi)) * (∫ θ in (0)..(2 * Real.pi), (max |s - Real.cos θ| |Real.sin θ|)⁻¹) :=
    rfl
  rw [hfin, ← hsplit, hreflect]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

private lemma one_add_sq_sub_pos {s : ℝ} (hs1 : s ≠ 1) (hs2 : s ≠ -1) (θ : ℝ) :
    0 < 1 + s ^ 2 - 2 * s * Real.cos θ := by
  have h : 1 + s ^ 2 - 2 * s * Real.cos θ = (s - Real.cos θ) ^ 2 + Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h]
  by_contra hc
  have h0 : (s - Real.cos θ) ^ 2 + Real.sin θ ^ 2 = 0 := le_antisymm (not_lt.mp hc) (by positivity)
  have hA : (s - Real.cos θ) ^ 2 = 0 := by nlinarith [sq_nonneg (s - Real.cos θ), sq_nonneg (Real.sin θ)]
  have hB : Real.sin θ ^ 2 = 0 := by nlinarith [sq_nonneg (s - Real.cos θ), sq_nonneg (Real.sin θ)]
  have hcos : Real.cos θ = s := by
    have := sq_eq_zero_iff.mp hA; linarith
  have hsin : Real.sin θ = 0 := sq_eq_zero_iff.mp hB
  have hsq : s ^ 2 = 1 := by rw [← hcos]; nlinarith [Real.sin_sq_add_cos_sq θ]
  rcases sq_eq_one_iff.mp hsq with hh | hh
  · exact hs1 hh
  · exact hs2 hh

private lemma supCircleMean_le_sqrt_two_mul_l2 {s : ℝ} (hs0 : 0 < s) (hs1 : s ≠ 1) :
    supCircleMean s ≤ Real.sqrt 2 * l2CircleMean s := by
  have hs2 : s ≠ -1 := by linarith
  have hpt : ∀ θ : ℝ, (max |s - Real.cos θ| |Real.sin θ|)⁻¹
      ≤ Real.sqrt 2 * (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹ := by
    intro θ
    have hX : 1 + s ^ 2 - 2 * s * Real.cos θ
        = |s - Real.cos θ| ^ 2 + |Real.sin θ| ^ 2 := by
      rw [sq_abs, sq_abs]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hmax0 : 0 ≤ max |s - Real.cos θ| |Real.sin θ| :=
      le_max_iff.mpr (Or.inr (abs_nonneg _))
    have hle : Real.sqrt ((|s - Real.cos θ| ^ 2 + |Real.sin θ| ^ 2) / 2)
        ≤ max |s - Real.cos θ| |Real.sin θ| := by
      rw [Real.sqrt_le_left hmax0]
      have h1 : |s - Real.cos θ| ^ 2 ≤ (max |s - Real.cos θ| |Real.sin θ|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
      have h2 : |Real.sin θ| ^ 2 ≤ (max |s - Real.cos θ| |Real.sin θ|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
      linarith
    have hXpos : 0 < 1 + s ^ 2 - 2 * s * Real.cos θ := one_add_sq_sub_pos hs1 hs2 θ
    have hYpos : 0 < (|s - Real.cos θ| ^ 2 + |Real.sin θ| ^ 2) / 2 := by
      rw [← hX]; positivity
    have hA : (0:ℝ) ≤ |s - Real.cos θ| ^ 2 + |Real.sin θ| ^ 2 := by positivity
    have hstep : (Real.sqrt ((|s - Real.cos θ| ^ 2 + |Real.sin θ| ^ 2) / 2))⁻¹
        = Real.sqrt 2 * (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹ := by
      rw [Real.sqrt_div hA 2, inv_div, div_eq_mul_inv]
      rw [← hX]
    calc (max |s - Real.cos θ| |Real.sin θ|)⁻¹
        ≤ (Real.sqrt ((|s - Real.cos θ| ^ 2 + |Real.sin θ| ^ 2) / 2))⁻¹ :=
          inv_anti₀ (Real.sqrt_pos.mpr hYpos) hle
      _ = Real.sqrt 2 * (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹ := hstep
  have hcont2 : Continuous fun θ : ℝ =>
      Real.sqrt 2 * (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹ := by
    refine Continuous.const_mul ?_ _
    refine Continuous.inv₀ (by fun_prop) ?_
    intro θ
    exact ne_of_gt (Real.sqrt_pos.mpr (one_add_sq_sub_pos hs1 hs2 θ))
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := (0:ℝ)) (b := Real.pi)
    Real.pi_pos.le ((continuous_max_inv hs1 hs2).intervalIntegrable _ _)
    (hcont2.intervalIntegrable _ _) (fun x _ => hpt x)
  have h2 := mul_le_mul_of_nonneg_left hmono (by positivity : (0:ℝ) ≤ 1 / Real.pi)
  rw [intervalIntegral.integral_const_mul] at h2
  have h3 : (1 / Real.pi) * (Real.sqrt 2 * ∫ θ in (0)..Real.pi,
        (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹)
      = Real.sqrt 2 * l2CircleMean s := by
    rw [l2CircleMean]
    ring
  calc supCircleMean s = (1 / Real.pi) * ∫ θ in (0)..Real.pi,
        (max |s - Real.cos θ| |Real.sin θ|)⁻¹ := supCircleMean_eq_pi hs1 hs2
    _ ≤ (1 / Real.pi) * (Real.sqrt 2 * ∫ θ in (0)..Real.pi,
        (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹) := h2
    _ = Real.sqrt 2 * l2CircleMean s := h3

/-- The l2-circle mean is invariant under `s ↦ 1/s` up to the Jacobian factor `1/s`. -/
private lemma l2CircleMean_inv {x : ℝ} (hx : 0 < x) :
    l2CircleMean x = (1 / x) * l2CircleMean (1 / x) := by
  have hpt : ∀ θ : ℝ, (Real.sqrt (1 + x ^ 2 - 2 * x * Real.cos θ))⁻¹
      = (1 / x) * (Real.sqrt (1 + (1 / x) ^ 2 - 2 * (1 / x) * Real.cos θ))⁻¹ := by
    intro θ
    have hX : 1 + x ^ 2 - 2 * x * Real.cos θ
        = x ^ 2 * (1 + (1 / x) ^ 2 - 2 * (1 / x) * Real.cos θ) := by
      field_simp
      ring
    have hY : 0 ≤ 1 + (1 / x) ^ 2 - 2 * (1 / x) * Real.cos θ := by
      have hYeq : 1 + (1 / x) ^ 2 - 2 * (1 / x) * Real.cos θ
          = ((1 / x) - Real.cos θ) ^ 2 + Real.sin θ ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      rw [hYeq]; positivity
    rw [hX, Real.sqrt_mul (by positivity : (0:ℝ) ≤ x ^ 2) _, Real.sqrt_sq hx.le, mul_inv, one_div]
  rw [l2CircleMean, l2CircleMean]
  have hAB : (∫ θ in (0)..Real.pi, (Real.sqrt (1 + x ^ 2 - 2 * x * Real.cos θ))⁻¹)
      = (1 / x) * ∫ θ in (0)..Real.pi,
          (Real.sqrt (1 + (1 / x) ^ 2 - 2 * (1 / x) * Real.cos θ))⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
  rw [hAB]
  ring

private lemma inv_mul_sqrt {x : ℝ} (hx : 0 < x) : x⁻¹ * Real.sqrt x = (Real.sqrt x)⁻¹ := by
  have h1 : x⁻¹ * Real.sqrt x = x ^ (-(1/2:ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hx]
    norm_num
  have h2 : (Real.sqrt x)⁻¹ = x ^ (-(1/2:ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hx)]
  rw [h1, h2]

/-- Pointwise bound on `(0,1)`. -/
private lemma supCircleMean_le_l2Bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    supCircleMean x ≤ Real.sqrt 2 * l2Bound x := by
  have hl2 : l2CircleMean x ≤ l2Bound x := by
    simpa only [l2CircleMean, l2Bound] using circle_l2_mean_le_rpow_eighth hx0.le hx1
  exact (supCircleMean_le_sqrt_two_mul_l2 hx0 (ne_of_lt hx1)).trans
    (mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg 2))

/-- Pointwise bound on `(1,√2)`. -/
private lemma supCircleMean_le_l2Bound_inv {x : ℝ} (hx0 : 1 < x) :
    supCircleMean x ≤ Real.sqrt 2 * l2Bound (1 / x) * x⁻¹ := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx0
  have hxlt : 1 / x < 1 := by rw [div_lt_one hxpos]; exact hx0
  have hxnn : (0:ℝ) ≤ 1 / x := by positivity
  have hl2 : l2CircleMean (1 / x) ≤ l2Bound (1 / x) := by
    simpa only [l2CircleMean, l2Bound] using circle_l2_mean_le_rpow_eighth hxnn hxlt
  calc supCircleMean x ≤ Real.sqrt 2 * l2CircleMean x :=
        supCircleMean_le_sqrt_two_mul_l2 hxpos (ne_of_gt hx0)
    _ = Real.sqrt 2 * ((1 / x) * l2CircleMean (1 / x)) := by rw [l2CircleMean_inv hxpos]
    _ = Real.sqrt 2 * l2CircleMean (1 / x) * x⁻¹ := by ring
    _ ≤ Real.sqrt 2 * l2Bound (1 / x) * x⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg 2)

/-- Pointwise bound on `(1,√2)` using the sharp single-step l2 bound. -/
private lemma supCircleMean_le_rpow_quarter_inv {x : ℝ} (hx0 : 1 < x) :
    supCircleMean x ≤ Real.sqrt 2 * ((1 : ℝ) - (1 / x) ^ 2) ^ (-(1/4:ℝ)) * x⁻¹ := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx0
  have hu0 : (0:ℝ) ≤ 1 / x := by positivity
  have hu1 : 1 / x < 1 := by rw [div_lt_one hxpos]; exact hx0
  have hl2 : l2CircleMean (1 / x) ≤ ((1 : ℝ) - (1 / x) ^ 2) ^ (-(1/4:ℝ)) := by
    simpa only [l2CircleMean] using circle_l2_mean_le_rpow_quarter hu0 hu1
  calc supCircleMean x ≤ Real.sqrt 2 * l2CircleMean x :=
        supCircleMean_le_sqrt_two_mul_l2 hxpos (ne_of_gt hx0)
    _ = Real.sqrt 2 * ((1 / x) * l2CircleMean (1 / x)) := by rw [l2CircleMean_inv hxpos]
    _ = Real.sqrt 2 * l2CircleMean (1 / x) * x⁻¹ := by ring
    _ ≤ Real.sqrt 2 * ((1 : ℝ) - (1 / x) ^ 2) ^ (-(1/4:ℝ)) * x⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg 2)

/-- The integrand of the target. -/
private noncomputable def F (c ρ : ℝ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
      ((‖(c * t ^ (2 / 3 : ℝ)) • (1, 0) - ρ • (Real.cos θ, Real.sin θ)‖)⁻¹
        - (c * t ^ (2 / 3 : ℝ))⁻¹)

private lemma F_eq (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (t : ℝ) (ht0 : 0 < t)
    (ht : c * t ^ (2 / 3 : ℝ) / ρ ≠ 1) :
    F c ρ t = (1/ρ) * (supCircleMean (c * t ^ (2 / 3 : ℝ)/ρ) - (c * t ^ (2 / 3 : ℝ)/ρ)⁻¹) := by
  set s : ℝ := c * t ^ (2 / 3 : ℝ) / ρ with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hsne : s ≠ -1 := by linarith
  set M : ℝ → ℝ := fun θ => (max |s - Real.cos θ| |Real.sin θ|)⁻¹ with hM
  have hcontM : Continuous M := by rw [hM]; exact continuous_max_inv ht hsne
  have hpt : ∀ θ : ℝ,
      (‖(c * t ^ (2 / 3 : ℝ)) • (1, 0) - ρ • (Real.cos θ, Real.sin θ)‖)⁻¹
        - (c * t ^ (2 / 3 : ℝ))⁻¹ = (1/ρ) * M θ - (c * t ^ (2 / 3 : ℝ))⁻¹ := by
    intro θ
    have hpair : (c * t ^ (2 / 3 : ℝ)) • ((1,0):ℝ×ℝ) = (c * t ^ (2 / 3 : ℝ), 0) := by
      ext <;> simp
    have h1 : (‖(c * t ^ (2 / 3 : ℝ)) • (1, 0) - ρ • (Real.cos θ, Real.sin θ)‖)⁻¹
        = (1/ρ) * M θ := by
      rw [hM, hs, hpair]
      exact inner_recip (c * t ^ (2 / 3 : ℝ)) ρ θ hρ
    rw [h1]
  have hstep : (∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ (2 / 3 : ℝ)) • (1, 0) - ρ • (Real.cos θ, Real.sin θ)‖)⁻¹
          - (c * t ^ (2 / 3 : ℝ))⁻¹))
      = (1/ρ) * (∫ θ in (0)..(2 * Real.pi), M θ)
        - (2 * Real.pi) * (c * t ^ (2 / 3 : ℝ))⁻¹ := by
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
    rw [intervalIntegral.integral_sub ((hcontM.const_mul (1/ρ)).intervalIntegrable _ _)
        intervalIntegrable_const]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    ring
  have hsup : supCircleMean s = (1 / (2 * Real.pi)) * (∫ θ in (0)..(2 * Real.pi), M θ) := by
    rw [supCircleMean, hM]
  have hcn : c * t ^ (2 / 3 : ℝ) ≠ 0 := by positivity
  have hs_inv : s⁻¹ = ρ * (c * t ^ (2 / 3 : ℝ))⁻¹ := by
    rw [hs]
    field_simp
  show (1 / (2 * Real.pi)) * (∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ (2 / 3 : ℝ)) • (1, 0) - ρ • (Real.cos θ, Real.sin θ)‖)⁻¹
          - (c * t ^ (2 / 3 : ℝ))⁻¹)) = _
  rw [hstep, hsup, hs_inv]
  field_simp

private noncomputable def phi (c ρ : ℝ) (x : ℝ) : ℝ := (ρ/c) ^ (3/2:ℝ) * x ^ (3/2:ℝ)

private lemma phi_pos (c ρ x : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hx : 0 < x) :
    0 < phi c ρ x :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hx _)

private lemma phi_pow (c ρ x : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hx : 0 < x) :
    (phi c ρ x) ^ (2/3:ℝ) = (ρ/c) * x := by
  rw [phi, Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hx.le _),
    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ρ/c), ← Real.rpow_mul hx.le]
  rw [show (3/2:ℝ)*(2/3:ℝ) = 1 by norm_num, Real.rpow_one, Real.rpow_one]

private lemma r_comp (c ρ x : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hx : 0 < x) :
    c * (phi c ρ x) ^ (2/3:ℝ) / ρ = x := by
  rw [phi_pow c ρ x hc hρ hx]
  field_simp

private lemma phi_deriv (c ρ x : ℝ) (hx : 0 < x) :
    HasDerivAt (phi c ρ) ((ρ/c) ^ (3/2:ℝ) * ((3/2:ℝ) * x ^ (1/2:ℝ))) x := by
  have h : HasDerivAt (fun x : ℝ => x ^ (3/2:ℝ)) ((3/2:ℝ) * x ^ (1/2:ℝ)) x := by
    have h0 := Real.hasDerivAt_rpow_const (x := x) (p := (3/2:ℝ)) (Or.inl (ne_of_gt hx))
    convert h0 using 1
    norm_num
  exact h.const_mul ((ρ/c) ^ (3/2:ℝ))

private lemma phi_strictMonoOn (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    StrictMonoOn (phi c ρ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [phi, phi]
  have hK : 0 < (ρ/c) ^ (3/2:ℝ) := Real.rpow_pos_of_pos (by positivity) _
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx.le hxy (by norm_num)) hK

private lemma phi_mul (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    (ρ/c) ^ (3/2:ℝ) * (c/ρ) ^ (3/2:ℝ) = 1 := by
  rw [← Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm]
  rw [show ρ * c / (c * ρ) = 1 by field_simp, Real.one_rpow]

private lemma phi_image (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    phi c ρ '' Set.Ioi 0 = Set.Ioi 0 := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact phi_pos c ρ x hc hρ hx
  · intro y hy
    refine ⟨(c/ρ) * y ^ (2/3:ℝ), mul_pos (div_pos hc hρ) (Real.rpow_pos_of_pos hy _), ?_⟩
    rw [phi, Real.mul_rpow (div_nonneg hc.le hρ.le) (Real.rpow_nonneg hy.le _), ← Real.rpow_mul hy.le]
    rw [show (2/3:ℝ)*(3/2:ℝ) = 1 by norm_num, Real.rpow_one]
    rw [← mul_assoc, phi_mul c ρ hc hρ, one_mul]

private lemma F_comp (c ρ x : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hx : 0 < x) (hx1 : x ≠ 1) :
    F c ρ (phi c ρ x) = (1/ρ) * (supCircleMean x - x⁻¹) := by
  rw [F_eq c ρ hc hρ (phi c ρ x) (phi_pos c ρ x hc hρ hx)
      (by rw [r_comp c ρ x hc hρ hx]; exact hx1),
    r_comp c ρ x hc hρ hx]

private lemma phi_injOn (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    Set.InjOn (phi c ρ) (Set.Ioi 0) := (phi_strictMonoOn c ρ hc hρ).injOn

private lemma coef_id (c ρ x : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    (ρ/c)^(3/2:ℝ) * ((3/2:ℝ) * x^(1/2:ℝ)) * (1/ρ)
    = (3*Real.sqrt ρ/(2*c^(3/2:ℝ))) * Real.sqrt x := by
  rw [Real.div_rpow hρ.le hc.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [show ρ^(3/2:ℝ) = ρ * ρ^(1/2:ℝ) by
        rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hρ, Real.rpow_one]]
  field_simp

set_option maxHeartbeats 800000 in
private lemma target_eq_J (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ t in Set.Ioi (0:ℝ), F c ρ t)
      = (3 * Real.sqrt ρ/(2*c^(3/2:ℝ))) * ∫ x in Set.Ioi (0:ℝ),
          (supCircleMean x - x⁻¹) * Real.sqrt x := by
  have himg := integral_image_eq_integral_abs_deriv_smul (f := phi c ρ)
      (f' := fun x => (ρ/c)^(3/2:ℝ) * ((3/2:ℝ) * x^(1/2:ℝ)))
      (s := Set.Ioi (0:ℝ)) measurableSet_Ioi
      (fun x hx => (phi_deriv c ρ x hx).hasDerivWithinAt)
      (phi_injOn c ρ hc hρ) (F c ρ)
  rw [phi_image c ρ hc hρ] at himg
  rw [himg]
  have hpt : ∀ x ∈ Set.Ioi (0:ℝ), x ≠ 1 →
      (|(ρ/c)^(3/2:ℝ) * ((3/2:ℝ) * x^(1/2:ℝ))| • F c ρ (phi c ρ x))
        = (3 * Real.sqrt ρ/(2*c^(3/2:ℝ))) * ((supCircleMean x - x⁻¹) * Real.sqrt x) := by
    intro x hx hx1
    rw [F_comp c ρ x hc hρ hx hx1, smul_eq_mul]
    have habs : |(ρ/c)^(3/2:ℝ) * ((3/2:ℝ) * x^(1/2:ℝ))|
        = (ρ/c)^(3/2:ℝ) * ((3/2:ℝ) * x^(1/2:ℝ)) :=
      abs_of_pos (mul_pos (Real.rpow_pos_of_pos (div_pos hρ hc) _)
        (mul_pos (by norm_num) (Real.rpow_pos_of_pos hx _)))
    rw [habs]
    calc (ρ/c)^(3/2:ℝ) * ((3/2:ℝ) * x^(1/2:ℝ)) * ((1/ρ) * (supCircleMean x - x⁻¹))
        = ((ρ/c)^(3/2:ℝ) * ((3/2:ℝ) * x^(1/2:ℝ)) * (1/ρ)) * (supCircleMean x - x⁻¹) := by ring
      _ = ((3*Real.sqrt ρ/(2*c^(3/2:ℝ))) * Real.sqrt x) * (supCircleMean x - x⁻¹) := by
            rw [coef_id c ρ x hc hρ]
      _ = (3*Real.sqrt ρ/(2*c^(3/2:ℝ))) * ((supCircleMean x - x⁻¹) * Real.sqrt x) := by ring
  have hae1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1:ℝ) := by
    rw [ae_iff]; simp
  rw [setIntegral_congr_ae measurableSet_Ioi (by
    filter_upwards [hae1] with x hx1 hmem
    exact hpt x hmem hx1)]
  rw [← integral_const_mul]

/-- `supCircleMean` is continuous away from `±1`. -/
private lemma supCircleMean_continuousOn (s : Set ℝ) (hs : ∀ x ∈ s, x ≠ 1 ∧ x ≠ -1) :
    ContinuousOn supCircleMean s := by
  have hcont : Continuous fun p : ↥s × ℝ =>
      (max |(p.1:ℝ) - Real.cos p.2| |Real.sin p.2|)⁻¹ := by
    apply Continuous.inv₀
    · fun_prop
    · intro p
      apply ne_of_gt
      rw [lt_max_iff]
      by_cases h : Real.sin p.2 = 0
      · left
        have h2 : Real.cos p.2 ^ 2 = 1 := by
          have := Real.sin_sq_add_cos_sq p.2; rw [h] at this; nlinarith
        have hcos : Real.cos p.2 = 1 ∨ Real.cos p.2 = -1 := by
          have h3 : (Real.cos p.2 - 1)*(Real.cos p.2 + 1) = 0 := by nlinarith
          rcases mul_eq_zero.mp h3 with h4 | h4
          · left; linarith
          · right; linarith
        rcases hcos with hc | hc
        · rw [hc]; exact abs_pos.mpr (sub_ne_zero.mpr (hs _ p.1.2).1)
        · rw [hc]; exact abs_pos.mpr (sub_ne_zero.mpr (fun hh => (hs _ p.1.2).2 (by linarith)))
      · right; exact abs_pos.mpr h
  have hc2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x:↥s) (θ:ℝ) =>
        (max |(x:ℝ) - Real.cos θ| |Real.sin θ|)⁻¹) hcont 0 (2*Real.pi) (μ := volume)
  rw [continuousOn_iff_continuous_domRestrict]
  have h2 : (Set.domRestrict s supCircleMean) = fun x : ↥s =>
      (1/(2*Real.pi)) * ∫ t in (0)..(2*Real.pi), (max |(x:ℝ) - Real.cos t| |Real.sin t|)⁻¹ := by
    funext x; rfl
  rw [h2]
  exact continuous_const.mul hc2


/-! ## Elementary integrals and the final estimate -/

private lemma inv_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ = x ^ (-(1/2:ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx]

private lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

private lemma integrableOn_Ioo_inv_sqrt :
    IntegrableOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Ioo (0:ℝ) 2) := by
  have h : IntegrableOn (fun x : ℝ => x ^ (-(1/2:ℝ))) (Set.Ioo (0:ℝ) 2) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 2)]; norm_num
  refine h.congr_fun ?_ measurableSet_Ioo
  intro x hx
  exact (inv_sqrt_eq_rpow hx.1.le).symm

private lemma integrableOn_Ioc_inv_sqrt_zero_one :
    IntegrableOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Ioc (0:ℝ) 1) :=
  (integrableOn_Ioo_inv_sqrt).mono_set (by
    intro x hx; exact ⟨hx.1, lt_of_le_of_lt hx.2 (by norm_num)⟩)

private lemma integrableOn_Ioc_inv_sqrt_one_sqrt_two :
    IntegrableOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Ioc (1:ℝ) (Real.sqrt 2)) :=
  (integrableOn_Ioo_inv_sqrt).mono_set (by
    intro x hx; exact ⟨lt_trans zero_lt_one hx.1, lt_of_le_of_lt hx.2 sqrt_two_lt_two⟩)

private lemma integral_Ioc_zero_one_inv_sqrt :
    ∫ x in Set.Ioc (0:ℝ) 1, (Real.sqrt x)⁻¹ = 2 := by
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  rw [show (∫ x in (0:ℝ)..1, (Real.sqrt x)⁻¹) = ∫ x in (0:ℝ)..1, x ^ (-(1/2:ℝ)) from
    intervalIntegral.integral_congr (fun x hx => by
      have h := Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)
      rw [h] at hx
      exact inv_sqrt_eq_rpow hx.1)]
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
  rw [show (-(1/2:ℝ)) + 1 = 1/2 by norm_num]
  rw [Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0), Real.one_rpow]
  norm_num

private lemma integral_Ioc_one_sqrt_two_inv_sqrt :
    ∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2), (Real.sqrt x)⁻¹
      = 2 * ((2:ℝ) ^ (1/4:ℝ) - 1) := by
  rw [← intervalIntegral.integral_of_le Real.one_lt_sqrt_two.le]
  rw [show (∫ x in (1:ℝ)..Real.sqrt 2, (Real.sqrt x)⁻¹)
      = ∫ x in (1:ℝ)..Real.sqrt 2, x ^ (-(1/2:ℝ)) from
    intervalIntegral.integral_congr (fun x hx => by
      have h := Set.uIcc_of_le Real.one_lt_sqrt_two.le
      rw [h] at hx
      exact inv_sqrt_eq_rpow (by linarith [hx.1]))]
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
  rw [show (-(1/2:ℝ)) + 1 = 1/2 by norm_num]
  rw [Real.one_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (1/2:ℝ) * (1/2) = 1/4 by norm_num]
  ring

/-- The pointwise description of the target integrand beyond `√2`. -/
private lemma supCircleMean_eq_large_s' {x : ℝ} (hx : Real.sqrt 2 ≤ x) :
    supCircleMean x = (Real.sqrt (x ^ 2 - 1))⁻¹ := by
  simpa only [supCircleMean] using sup_circle_mean_eq_large_s (s := x) hx

/-- The sup-circle mean is nonnegative (it is the mean of a nonnegative integrand). -/
private lemma supCircleMean_nonneg (s : ℝ) : 0 ≤ supCircleMean s := by
  rw [supCircleMean]
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by positivity) ?_)
  intro u _
  exact inv_nonneg.mpr (le_max_iff.mpr (Or.inr (abs_nonneg _)))

private lemma J_neg :
    (∫ x in Set.Ioi (0:ℝ), (supCircleMean x - x⁻¹) * Real.sqrt x) < 0 := by
  set f : ℝ → ℝ := fun x => (supCircleMean x - x⁻¹) * Real.sqrt x with hf
  have hae1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1:ℝ) := by
    rw [ae_iff]; simp
  -- pointwise upper bounds on the three pieces
  have hb1 : ∀ x ∈ Set.Ioc (0:ℝ) 1, x ≠ 1 →
      f x ≤ Real.sqrt 2 * (l2Bound x * Real.sqrt x) - (Real.sqrt x)⁻¹ := by
    intro x hx hx1
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hle : supCircleMean x ≤ Real.sqrt 2 * l2Bound x := supCircleMean_le_l2Bound hx.1 hxlt
    rw [hf]
    calc (supCircleMean x - x⁻¹) * Real.sqrt x
        ≤ (Real.sqrt 2 * l2Bound x - x⁻¹) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right (sub_le_sub_right hle _) (Real.sqrt_nonneg x)
      _ = Real.sqrt 2 * (l2Bound x * Real.sqrt x) - (Real.sqrt x)⁻¹ := by
          rw [sub_mul, inv_mul_sqrt hx.1]
          ring
  have hb2 : ∀ x ∈ Set.Ioc (1:ℝ) (Real.sqrt 2),
      f x ≤ Real.sqrt 2 * (l2Bound (1 / x) * (Real.sqrt x)⁻¹) - (Real.sqrt x)⁻¹ := by
    intro x hx
    have hx1 : 1 < x := hx.1
    have hle : supCircleMean x ≤ Real.sqrt 2 * l2Bound (1 / x) * x⁻¹ :=
      supCircleMean_le_l2Bound_inv hx1
    rw [hf]
    calc (supCircleMean x - x⁻¹) * Real.sqrt x
        ≤ (Real.sqrt 2 * l2Bound (1 / x) * x⁻¹ - x⁻¹) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right (sub_le_sub_right hle _) (Real.sqrt_nonneg x)
      _ = Real.sqrt 2 * (l2Bound (1 / x) * (Real.sqrt x)⁻¹) - (Real.sqrt x)⁻¹ := by
          have key : x⁻¹ * Real.sqrt x = (Real.sqrt x)⁻¹ := inv_mul_sqrt (lt_trans zero_lt_one hx1)
          rw [sub_mul]
          rw [show (Real.sqrt 2 * l2Bound (1 / x) * x⁻¹) * Real.sqrt x
              = Real.sqrt 2 * (l2Bound (1 / x) * (x⁻¹ * Real.sqrt x)) by ring]
          rw [key]
  have hb3 : ∀ x ∈ Set.Ioi (Real.sqrt 2),
      f x = ((Real.sqrt (x^2-1))⁻¹ - x⁻¹) * Real.sqrt x := by
    intro x hx
    show (supCircleMean x - x⁻¹) * Real.sqrt x = _
    rw [supCircleMean_eq_large_s' hx.le]
  -- integrability of the majorants
  have hD2 : IntegrableOn (fun x : ℝ => l2Bound x * Real.sqrt x) (Set.Ioc (0:ℝ) 1) := by
    simpa only [l2Bound] using integrableOn_l2_rpow_eighth_bound_zero_one
  have hD3 : IntegrableOn (fun x : ℝ => l2Bound (1 / x) * (Real.sqrt x)⁻¹)
      (Set.Ioc (1:ℝ) (Real.sqrt 2)) := by
    simpa only [l2Bound] using integrableOn_l2_rpow_eighth_bound_half
  have hmaj1 : IntegrableOn
      (fun x : ℝ => Real.sqrt 2 * (l2Bound x * Real.sqrt x) - (Real.sqrt x)⁻¹)
      (Set.Ioc (0:ℝ) 1) :=
    (hD2.const_mul (Real.sqrt 2)).sub integrableOn_Ioc_inv_sqrt_zero_one
  have hmaj2 : IntegrableOn
      (fun x : ℝ => Real.sqrt 2 * (l2Bound (1 / x) * (Real.sqrt x)⁻¹) - (Real.sqrt x)⁻¹)
      (Set.Ioc (1:ℝ) (Real.sqrt 2)) :=
    (hD3.const_mul (Real.sqrt 2)).sub integrableOn_Ioc_inv_sqrt_one_sqrt_two
  have hmajn1 : IntegrableOn
      (fun x : ℝ => Real.sqrt 2 * (l2Bound x * Real.sqrt x) + (Real.sqrt x)⁻¹)
      (Set.Ioc (0:ℝ) 1) :=
    (hD2.const_mul (Real.sqrt 2)).add integrableOn_Ioc_inv_sqrt_zero_one
  have hmajn2 : IntegrableOn
      (fun x : ℝ => Real.sqrt 2 * (l2Bound (1 / x) * (Real.sqrt x)⁻¹) + (Real.sqrt x)⁻¹)
      (Set.Ioc (1:ℝ) (Real.sqrt 2)) :=
    (hD3.const_mul (Real.sqrt 2)).add integrableOn_Ioc_inv_sqrt_one_sqrt_two
  -- (a.e.) strong measurability of `f`
  have hcont1 : ContinuousOn f (Set.Ioo (0:ℝ) 1) := by
    rw [hf]
    exact ((supCircleMean_continuousOn _
        (fun x hx => ⟨ne_of_lt hx.2, ne_of_gt (by linarith [hx.1])⟩)).sub
      (continuousOn_id.inv₀ (fun x hx => ne_of_gt hx.1))).mul Real.continuous_sqrt.continuousOn
  have hcont2 : ContinuousOn f (Set.Ioo (1:ℝ) (Real.sqrt 2)) := by
    rw [hf]
    exact ((supCircleMean_continuousOn _
        (fun x hx => ⟨ne_of_gt hx.1, ne_of_gt (by linarith [hx.1])⟩)).sub
      (continuousOn_id.inv₀ (fun x hx => ne_of_gt (lt_trans zero_lt_one hx.1)))).mul
      Real.continuous_sqrt.continuousOn
  have hmeas1 : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    rw [show volume.restrict (Set.Ioc (0:ℝ) 1) = volume.restrict (Set.Ioo (0:ℝ) 1) from
      (Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := 1))).symm]
    exact hcont1.aestronglyMeasurable measurableSet_Ioo
  have hmeas2 : AEStronglyMeasurable f (volume.restrict (Set.Ioc (1:ℝ) (Real.sqrt 2))) := by
    rw [show volume.restrict (Set.Ioc (1:ℝ) (Real.sqrt 2))
          = volume.restrict (Set.Ioo (1:ℝ) (Real.sqrt 2)) from
      (Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Ioc (a := (1:ℝ)) (b := Real.sqrt 2))).symm]
    exact hcont2.aestronglyMeasurable measurableSet_Ioo
  -- integrability of `f` on the three pieces
  have hfint1 : IntegrableOn f (Set.Ioc (0:ℝ) 1) := by
    refine Integrable.mono' hmajn1 hmeas1 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_mono Measure.restrict_le_self hae1] with x hx hx1
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hle : supCircleMean x ≤ Real.sqrt 2 * l2Bound x := supCircleMean_le_l2Bound hx.1 hxlt
    have h0 : 0 ≤ supCircleMean x := supCircleMean_nonneg x
    have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hxinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.1.le
    have habs : |supCircleMean x - x⁻¹| ≤ supCircleMean x + x⁻¹ := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have h2b : supCircleMean x * Real.sqrt x ≤ Real.sqrt 2 * (l2Bound x * Real.sqrt x) := by
      calc supCircleMean x * Real.sqrt x
          ≤ (Real.sqrt 2 * l2Bound x) * Real.sqrt x := mul_le_mul_of_nonneg_right hle hsqrt
        _ = Real.sqrt 2 * (l2Bound x * Real.sqrt x) := by ring
    rw [Real.norm_eq_abs, hf, abs_mul, abs_of_nonneg hsqrt]
    calc |supCircleMean x - x⁻¹| * Real.sqrt x
        ≤ (supCircleMean x + x⁻¹) * Real.sqrt x := mul_le_mul_of_nonneg_right habs hsqrt
      _ = supCircleMean x * Real.sqrt x + (Real.sqrt x)⁻¹ := by
          rw [add_mul, inv_mul_sqrt hx.1]
      _ ≤ Real.sqrt 2 * (l2Bound x * Real.sqrt x) + (Real.sqrt x)⁻¹ := by linarith
  have hfint2 : IntegrableOn f (Set.Ioc (1:ℝ) (Real.sqrt 2)) := by
    refine Integrable.mono' hmajn2 hmeas2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : 1 < x := hx.1
    have hxpos : 0 < x := lt_trans zero_lt_one hx1
    have hle : supCircleMean x ≤ Real.sqrt 2 * l2Bound (1 / x) * x⁻¹ :=
      supCircleMean_le_l2Bound_inv hx1
    have h0 : 0 ≤ supCircleMean x := supCircleMean_nonneg x
    have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hxinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hxpos.le
    have habs : |supCircleMean x - x⁻¹| ≤ supCircleMean x + x⁻¹ := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have h2b : supCircleMean x * Real.sqrt x
        ≤ Real.sqrt 2 * (l2Bound (1 / x) * (Real.sqrt x)⁻¹) := by
      calc supCircleMean x * Real.sqrt x
          ≤ (Real.sqrt 2 * l2Bound (1 / x) * x⁻¹) * Real.sqrt x :=
            mul_le_mul_of_nonneg_right hle hsqrt
        _ = Real.sqrt 2 * (l2Bound (1 / x) * (Real.sqrt x)⁻¹) := by
            have key : x⁻¹ * Real.sqrt x = (Real.sqrt x)⁻¹ := inv_mul_sqrt hxpos
            rw [show (Real.sqrt 2 * l2Bound (1 / x) * x⁻¹) * Real.sqrt x
                = Real.sqrt 2 * (l2Bound (1 / x) * (x⁻¹ * Real.sqrt x)) by ring, key]
    rw [Real.norm_eq_abs, hf, abs_mul, abs_of_nonneg hsqrt]
    calc |supCircleMean x - x⁻¹| * Real.sqrt x
        ≤ (supCircleMean x + x⁻¹) * Real.sqrt x := mul_le_mul_of_nonneg_right habs hsqrt
      _ = supCircleMean x * Real.sqrt x + (Real.sqrt x)⁻¹ := by
          rw [add_mul, inv_mul_sqrt hxpos]
      _ ≤ Real.sqrt 2 * (l2Bound (1 / x) * (Real.sqrt x)⁻¹) + (Real.sqrt x)⁻¹ := by linarith
  have hfint3 : IntegrableOn f (Set.Ioi (Real.sqrt 2)) :=
    IntegrableOn.congr_fun integrableOn_sqrt_sq_sub_one_Ioi_sqrt_two
      (fun x hx => (hb3 x hx).symm) measurableSet_Ioi
  -- the two splits
  have hset1 : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h1)
      · exact h1
      · linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (not_le.mp h)
  have hset2 : Set.Ioc (1:ℝ) (Real.sqrt 2) ∪ Set.Ioi (Real.sqrt 2) = Set.Ioi (1:ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h1)
      · exact h1
      · exact lt_trans Real.one_lt_sqrt_two h1
    · intro hx
      by_cases h : x ≤ Real.sqrt 2
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (not_le.mp h)
  have hfintIoi1 : IntegrableOn f (Set.Ioi (1:ℝ)) := by
    rw [← hset2]
    exact hfint2.union hfint3
  have hsplit2 : (∫ x in Set.Ioi (1:ℝ), f x)
      = (∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2), f x) + (∫ x in Set.Ioi (Real.sqrt 2), f x) := by
    rw [← hset2]
    exact setIntegral_union (Set.disjoint_left.mpr (fun x hx1 hx2 => (not_lt.mpr hx1.2) hx2))
      measurableSet_Ioi hfint2 hfint3
  have hsplit1 : (∫ x in Set.Ioi (0:ℝ), f x)
      = (∫ x in Set.Ioc (0:ℝ) 1, f x) + (∫ x in Set.Ioi (1:ℝ), f x) := by
    rw [← hset1]
    exact setIntegral_union (Set.disjoint_left.mpr (fun x hx1 hx2 => (not_lt.mpr hx1.2) hx2))
      measurableSet_Ioi hfint1 hfintIoi1
  -- bounds on each piece
  have hbound1 : (∫ x in Set.Ioc (0:ℝ) 1, f x) ≤ Real.sqrt 2 * 0.87 - 2 := by
    have hmono := setIntegral_mono_on_ae hfint1 hmaj1 measurableSet_Ioc (by
      filter_upwards [hae1] with x hx1 hmem
      exact hb1 x hmem hx1)
    have heq : (∫ x in Set.Ioc (0:ℝ) 1,
          (Real.sqrt 2 * (l2Bound x * Real.sqrt x) - (Real.sqrt x)⁻¹))
        = Real.sqrt 2 * (∫ x in Set.Ioc (0:ℝ) 1, l2Bound x * Real.sqrt x)
          - (∫ x in Set.Ioc (0:ℝ) 1, (Real.sqrt x)⁻¹) := by
      rw [integral_sub (hD2.const_mul (Real.sqrt 2)) integrableOn_Ioc_inv_sqrt_zero_one,
        integral_const_mul]
    rw [heq] at hmono
    have h2 := integral_Ioc_zero_one_inv_sqrt
    have h1 : (∫ x in Set.Ioc (0:ℝ) 1, l2Bound x * Real.sqrt x) ≤ 0.87 := by
      simpa only [l2Bound] using integral_l2_rpow_eighth_bound_zero_one
    have hmul : Real.sqrt 2 * (∫ x in Set.Ioc (0:ℝ) 1, l2Bound x * Real.sqrt x)
        ≤ Real.sqrt 2 * 0.87 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)
    linarith [hmono, hmul, h2]
  have hbound2 : (∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2), f x)
      ≤ Real.sqrt 2 * 0.6 - 2 * ((2:ℝ) ^ (1/4:ℝ) - 1) := by
    have hmono := setIntegral_mono_on_ae hfint2 hmaj2 measurableSet_Ioc (by
      filter_upwards with x hmem
      exact hb2 x hmem)
    have heq : (∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2),
          (Real.sqrt 2 * (l2Bound (1 / x) * (Real.sqrt x)⁻¹) - (Real.sqrt x)⁻¹))
        = Real.sqrt 2 * (∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2), l2Bound (1 / x) * (Real.sqrt x)⁻¹)
          - (∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2), (Real.sqrt x)⁻¹) := by
      rw [integral_sub (hD3.const_mul (Real.sqrt 2)) integrableOn_Ioc_inv_sqrt_one_sqrt_two,
        integral_const_mul]
    rw [heq] at hmono
    have h2 := integral_Ioc_one_sqrt_two_inv_sqrt
    have h1 : (∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2), l2Bound (1 / x) * (Real.sqrt x)⁻¹) ≤ 0.6 := by
      simpa only [l2Bound] using integral_l2_rpow_eighth_bound_half
    have hmul : Real.sqrt 2 * (∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2),
          l2Bound (1 / x) * (Real.sqrt x)⁻¹) ≤ Real.sqrt 2 * 0.6 :=
      mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)
    linarith [hmono, hmul, h2]
  have hbound3 : (∫ x in Set.Ioi (Real.sqrt 2), f x) ≤ 1/4 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hb3 x hx)]
    exact integral_sqrt_sq_sub_one_le_quarter
  -- assembly
  have htotal : (∫ x in Set.Ioi (0:ℝ), f x)
      ≤ (Real.sqrt 2 * 0.87 - 2) + (Real.sqrt 2 * 0.6 - 2 * ((2:ℝ) ^ (1/4:ℝ) - 1)) + 1/4 := by
    rw [hsplit1, hsplit2]
    linarith [hbound1, hbound2, hbound3]
  have hneg : (Real.sqrt 2 * 0.87 - 2) + (Real.sqrt 2 * 0.6 - 2 * ((2:ℝ) ^ (1/4:ℝ) - 1)) + 1/4 < 0 := by
    have h2 : Real.sqrt 2 ≤ 1.4143 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h4 : (1.189:ℝ) ≤ (2:ℝ) ^ (1/4:ℝ) := by
      rw [show (2:ℝ) ^ (1/4:ℝ) = Real.sqrt (Real.sqrt 2) by
        rw [show (1/4:ℝ) = (1/2:ℝ) * (1/2) by norm_num,
          Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
          ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]]
      rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg 2),
        Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    nlinarith [h2, h4]
  linarith

theorem planar_circle_average_parabolic_neg {c rho : ℝ} (hc : 0 < c) (hrho : 0 < rho) :
    ∫ t in Set.Ioi (0 : ℝ),
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
            (‖(c * t ^ (2 / 3 : ℝ)) • (1, 0) - rho • (Real.cos theta, Real.sin theta)‖)⁻¹
          - (c * t ^ (2 / 3 : ℝ))⁻¹)
      < 0 := by
  change (∫ t in Set.Ioi (0:ℝ), F c rho t) < 0
  rw [target_eq_J c rho hc hrho]
  refine mul_neg_of_pos_of_neg ?_ J_neg
  exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hrho))
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hc _))



end Commons.Analysis.Integral
