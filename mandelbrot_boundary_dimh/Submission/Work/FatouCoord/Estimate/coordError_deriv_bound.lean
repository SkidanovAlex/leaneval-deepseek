/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup

/-!
# Derivative bound for the defect `coordError`

Continuing the quantitative set-up of `FatouCoord/Setup`, we bound the derivative of the
defect `coordError f (1 - a)` of the approximate Abel coordinate `w - (1-a) log w`.

On the region `Re w > 1/r + 9` (so that `-1/w` lies in the disc of the quantitative
hypotheses) the defect is differentiable and its derivative decays like `1/|w|^2`:

`‖deriv (coordError f (1 - a)) w‖ ≤ B / ‖w‖^2`,

with a constant `B` depending only on `A'` (the derivative bound for `h`) and on `‖1 - a‖`.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Estimate

open Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {w z : ℂ}

/-! ## Derivative of the chart and of the denominator -/

/-- `z ↦ -1/z` has derivative `1/z ^ 2` away from the origin. -/
lemma hasDerivAt_neg_one_div (w : ℂ) (hw : w ≠ 0) :
    HasDerivAt (fun z : ℂ => -1 / z) ((w ^ 2)⁻¹) w := by
  have h := (hasDerivAt_inv hw).neg
  have h2 : (-fun y : ℂ => y⁻¹) = fun z : ℂ => -1 / z := by funext z; simp [neg_div]
  rw [h2] at h
  simpa using h

/-- Derivative of the denominator `w ↦ 1 + (-1/w) h (-1/w)`. -/
lemma hasDerivAt_den {h : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hd : DifferentiableAt ℂ h (-1 / w)) :
    HasDerivAt (fun z : ℂ => 1 + (-1 / z) * h (-1 / z))
      ((1 / w ^ 2) * (h (-1 / w) + (-1 / w) * deriv h (-1 / w))) w := by
  have hu : HasDerivAt (fun z : ℂ => -1 / z) ((w ^ 2)⁻¹) w := hasDerivAt_neg_one_div w hw
  have hhu : HasDerivAt (fun z : ℂ => h (-1 / z)) (deriv h (-1 / w) * (w ^ 2)⁻¹) w := by
    have hh := hd.hasDerivAt.comp w hu
    have heq : (h ∘ (fun z : ℂ => -1 / z)) = fun z : ℂ => h (-1 / z) := by funext z; rfl
    rw [heq] at hh
    exact hh
  have hmul : HasDerivAt ((fun z : ℂ => -1 / z) * (fun z : ℂ => h (-1 / z)))
      (((w ^ 2)⁻¹) * h (-1 / w) + (-1 / w) * (deriv h (-1 / w) * (w ^ 2)⁻¹)) w :=
    hu.mul hhu
  have hres := hmul.const_add 1
  have key1 : (fun x : ℂ => 1 + (((fun z : ℂ => -1 / z) * (fun z : ℂ => h (-1 / z))) x))
      = (fun z : ℂ => 1 + (-1 / z) * h (-1 / z)) := by
    funext z; simp [Pi.mul_apply]
  have key2 : ((w ^ 2)⁻¹ * h (-1 / w) + (-1 / w) * (deriv h (-1 / w) * (w ^ 2)⁻¹))
      = (1 / w ^ 2) * (h (-1 / w) + (-1 / w) * deriv h (-1 / w)) := by
    field_simp
  rw [key1, key2] at hres
  exact hres

/-! ## The region `Re w > 1/r + 9` -/

/-- In the region `Re w > 1/r + 9` the modulus of `w` exceeds `9`. -/
lemma nine_lt_norm {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : 1 / r + 9 < w.re) :
    (9 : ℝ) < ‖w‖ := by
  have h1 : (0 : ℝ) < 1 / r := one_div_pos.mpr hr
  calc (9 : ℝ) < w.re := by linarith
    _ ≤ ‖w‖ := Complex.re_le_norm w

/-- `-1/w` lies in the disc of the quantitative hypotheses. -/
lemma neg_one_div_mem_ball (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) : -1 / w ∈ ball 0 r := by
  have hr := hb.hr
  have h1r : (0 : ℝ) < 1 / r := one_div_pos.mpr hr
  have hwr : (0 : ℝ) < w.re := by linarith
  have hnw : 1 / r < ‖w‖ := by
    have : 1 / r < w.re := by linarith
    linarith [Complex.re_le_norm w]
  have hw0 : w ≠ 0 := by intro hh; rw [hh] at hwr; simp at hwr
  rw [mem_ball_zero_iff]; exact norm_neg_one_div_lt hr hw0 hnw

/-- `-1/w` is a point of differentiability of `h`. -/
lemma differentiableAt_h_neg_one_div (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) : DifferentiableAt ℂ h (-1 / w) :=
  hb.h_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (neg_one_div_mem_ball hb hw))

/-- The size of the correction `(-1/w) h (-1/w)` in the denominator. -/
lemma den_correction_le (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) : ‖(-1 / w) * h (-1 / w)‖ ≤ 2 / ‖w‖ := by
  have h9 : (9 : ℝ) < ‖w‖ := nine_lt_norm hb.hr hw
  have hh : ‖h (-1 / w)‖ ≤ 2 := hb.h_bound _ (neg_one_div_mem_ball hb hw)
  have h1 : ‖-1 / w‖ = 1 / ‖w‖ := by rw [norm_div, norm_neg, norm_one]
  calc ‖(-1 / w) * h (-1 / w)‖ = ‖-1 / w‖ * ‖h (-1 / w)‖ := norm_mul _ _
    _ = (1 / ‖w‖) * ‖h (-1 / w)‖ := by rw [h1]
    _ ≤ (1 / ‖w‖) * 2 :=
        mul_le_mul_of_nonneg_left hh (div_nonneg zero_le_one (norm_nonneg w))
    _ = 2 / ‖w‖ := by ring

/-- The denominator `1 + (-1/w) h (-1/w)` is a point of the slit plane. -/
lemma den_mem_slitPlane (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) : (1 + (-1 / w) * h (-1 / w)) ∈ Complex.slitPlane := by
  have h9 : (9 : ℝ) < ‖w‖ := nine_lt_norm hb.hr hw
  refine Complex.mem_slitPlane_of_norm_lt_one ?_
  have hle := den_correction_le hb hw
  have hlt : 2 / ‖w‖ < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < ‖w‖)]; linarith
  linarith

/-- The denominator is nonzero. -/
lemma den_ne_zero (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) : (1 + (-1 / w) * h (-1 / w)) ≠ 0 :=
  Complex.slitPlane_ne_zero (den_mem_slitPlane hb hw)

/-- The denominator is bounded below by `1/2`. -/
lemma den_low (hb : ParabolicBounds f h a r A A') {w : ℂ} (hw : 1 / r + 9 < w.re) :
    (1 : ℝ) / 2 ≤ ‖1 + (-1 / w) * h (-1 / w)‖ := by
  have h9 : (9 : ℝ) < ‖w‖ := nine_lt_norm hb.hr hw
  have hle := den_correction_le hb hw
  have hge : (1 : ℝ) - ‖(-1 / w) * h (-1 / w)‖ ≤ ‖1 + (-1 / w) * h (-1 / w)‖ := by
    have hsub := norm_sub_le ((1 : ℂ) + (-1 / w) * h (-1 / w)) ((-1 / w) * h (-1 / w))
    have he : ((1 : ℂ) + (-1 / w) * h (-1 / w)) - ((-1 / w) * h (-1 / w)) = 1 := by ring
    rw [he, norm_one] at hsub
    linarith
  have hlt : 2 / ‖w‖ < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < ‖w‖)]; linarith
  linarith

/-! ## Derivative of `wMap` -/

/-- Derivative of `wMap f` in the region `Re w > 1/r + 9`. -/
lemma wMap_hasDerivAt (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) :
    HasDerivAt (wMap f)
      (((1 + (-1 / w) * h (-1 / w))
          - w * ((1 / w ^ 2) * (h (-1 / w) + (-1 / w) * deriv h (-1 / w))))
        / (1 + (-1 / w) * h (-1 / w)) ^ 2) w := by
  have hr := hb.hr
  have h1r : (0 : ℝ) < 1 / r := one_div_pos.mpr hr
  have hwr : (0 : ℝ) < w.re := by linarith
  have hnw : 1 / r < ‖w‖ := by
    have : 1 / r < w.re := by linarith
    linarith [Complex.re_le_norm w]
  have hw0 : w ≠ 0 := by intro hh; rw [hh] at hwr; simp at hwr
  have hd := differentiableAt_h_neg_one_div hb hw
  have hDne := den_ne_zero hb hw
  have hden := hasDerivAt_den hw0 hd
  have hev : wMap f =ᶠ[𝓝 w] (fun z : ℂ => z / (1 + (-1 / z) * h (-1 / z))) := by
    have hVopen : IsOpen ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 1 / r < ‖z‖}) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const continuous_norm)
    have hwV : w ∈ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 1 / r < ‖z‖}) := ⟨hwr, hnw⟩
    filter_upwards [hVopen.mem_nhds hwV] with z hz
    exact wMap_eq hr hb.f_eq hz.1 hz.2
  have hid : HasDerivAt (fun z : ℂ => z) (1 : ℂ) w := hasDerivAt_id w
  have hquot := hid.div hden hDne
  have hres := hquot.congr_of_eventuallyEq hev
  have key : (1 * (1 + (-1 / w) * h (-1 / w))
        - w * ((1 / w ^ 2) * (h (-1 / w) + (-1 / w) * deriv h (-1 / w))))
      = ((1 + (-1 / w) * h (-1 / w))
          - w * ((1 / w ^ 2) * (h (-1 / w) + (-1 / w) * deriv h (-1 / w)))) := by ring
  rw [key] at hres
  exact hres

/-- Explicit form of `deriv (wMap f) w` in the region. -/
lemma wMap_deriv_sub_one (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) :
    deriv (wMap f) w - 1
      = (deriv h (-1 / w) - h (-1 / w) ^ 2)
          / (w ^ 2 * (1 + (-1 / w) * h (-1 / w)) ^ 2) := by
  have hDne := den_ne_zero hb hw
  have hderiv := (wMap_hasDerivAt hb hw).deriv
  rw [hderiv]
  have hD2 : (1 + (-1 / w) * h (-1 / w)) ^ 2 ≠ 0 := pow_ne_zero 2 hDne
  rw [div_sub' hD2]
  rw [show (1 + -1 / w * h (-1 / w)
        - w * ((1 / w ^ 2) * (h (-1 / w) + (-1 / w) * deriv h (-1 / w)))
        - (1 + -1 / w * h (-1 / w)) ^ 2 * 1)
      = (deriv h (-1 / w) - h (-1 / w) ^ 2) / w ^ 2 from by
        field_simp; ring]
  rw [div_div]

/-- The derivative of `wMap f` differs from `1` by `O(1/w^2)`. -/
lemma wMap_deriv_bound_aux (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) :
    ‖deriv (wMap f) w - 1‖ ≤ 4 * (A' + 4) / ‖w‖ ^ 2 := by
  have h9 : (9 : ℝ) < ‖w‖ := nine_lt_norm hb.hr hw
  have hDlow := den_low hb hw
  have hnum : ‖deriv h (-1 / w) - h (-1 / w) ^ 2‖ ≤ A' + 4 := by
    have h2 : ‖h (-1 / w) ^ 2‖ ≤ 4 := by
      rw [norm_pow]
      nlinarith [norm_nonneg (h (-1 / w)), hb.h_bound _ (neg_one_div_mem_ball hb hw)]
    calc ‖deriv h (-1 / w) - h (-1 / w) ^ 2‖
          ≤ ‖deriv h (-1 / w)‖ + ‖h (-1 / w) ^ 2‖ := norm_sub_le _ _
      _ ≤ A' + 4 := by
          have := hb.h_deriv_bound _ (neg_one_div_mem_ball hb hw)
          linarith
  rw [wMap_deriv_sub_one hb hw]
  simp only [norm_div, norm_mul, norm_pow]
  have hD2 : (1 / 4 : ℝ) ≤ ‖1 + (-1 / w) * h (-1 / w)‖ ^ 2 :=
    by nlinarith [hDlow, norm_nonneg (1 + (-1 / w) * h (-1 / w))]
  have hcle : ‖w‖ ^ 2 * (1 / 4) ≤ ‖w‖ ^ 2 * ‖1 + (-1 / w) * h (-1 / w)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hD2 (by positivity)
  have hmain : ‖deriv h (-1 / w) - h (-1 / w) ^ 2‖
        / (‖w‖ ^ 2 * ‖1 + (-1 / w) * h (-1 / w)‖ ^ 2)
      ≤ (A' + 4) / (‖w‖ ^ 2 * (1 / 4)) :=
    div_le_div₀ (by linarith [hb.hA']) hnum (by positivity) hcle
  have heq : (A' + 4) / (‖w‖ ^ 2 * (1 / 4)) = 4 * (A' + 4) / ‖w‖ ^ 2 := by
    have h0 : ‖w‖ ≠ 0 := ne_of_gt (by linarith)
    field_simp
  rw [heq] at hmain
  exact hmain

/-- The position of `wMap f w` relative to `w` in the region. -/
lemma wMap_sub_aux (hb : ParabolicBounds f h a r A A') {w : ℂ} (hw : 1 / r + 9 < w.re) :
    ‖wMap f w - w‖ ≤ 4 ∧ (0 : ℝ) < (wMap f w).re := by
  have hr := hb.hr
  have h1r : (0 : ℝ) < 1 / r := one_div_pos.mpr hr
  have hwr : (0 : ℝ) < w.re := by linarith
  have hnw : 1 / r < ‖w‖ := by
    have : 1 / r < w.re := by linarith
    linarith [Complex.re_le_norm w]
  have hDne := den_ne_zero hb hw
  have hDlow := den_low hb hw
  have hsub := wMap_sub_eq hr hb.f_eq hwr hnw hDne
  have hnorm : ‖wMap f w - w‖ ≤ 4 := by
    rw [hsub, norm_div]
    have hh : ‖h (-1 / w)‖ ≤ 2 := hb.h_bound _ (neg_one_div_mem_ball hb hw)
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖1 + (-1 / w) * h (-1 / w)‖)]
    nlinarith
  refine ⟨hnorm, ?_⟩
  have habs := Complex.abs_re_le_norm (wMap f w - w)
  rw [abs_le] at habs
  have hge : -(4 : ℝ) ≤ (wMap f w - w).re := by linarith [habs.1]
  have hre : (wMap f w).re = w.re + (wMap f w - w).re := by
    rw [Complex.sub_re]; ring
  rw [hre]; linarith

/-- The logarithmic part `deriv (wMap f) w / wMap f w - 1/w` is `O(1/w^2)`. -/
lemma wMap_deriv_ratio_aux (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) :
    ‖deriv (wMap f) w / (wMap f w) - 1 / w‖ ≤ 2 * (4 * (A' + 4) + 4) / ‖w‖ ^ 2 := by
  have h9 : (9 : ℝ) < ‖w‖ := nine_lt_norm hb.hr hw
  have hwn : (0 : ℝ) < ‖w‖ := by linarith
  have hw0 : w ≠ 0 := by intro hh; rw [hh] at hwn; simp at hwn
  have hW' := wMap_deriv_bound_aux hb hw
  obtain ⟨hWsub, hWre⟩ := wMap_sub_aux hb hw
  have hWne : wMap f w ≠ 0 := by intro hh; rw [hh] at hWre; simp at hWre
  have hkey : deriv (wMap f) w / (wMap f w) - 1 / w
      = (w * (deriv (wMap f) w - 1) - (wMap f w - w)) / (w * wMap f w) := by
    field_simp
    ring
  have hnum1 : ‖w * (deriv (wMap f) w - 1)‖ ≤ 4 * (A' + 4) / ‖w‖ := by
    rw [norm_mul]
    calc ‖w‖ * ‖deriv (wMap f) w - 1‖ ≤ ‖w‖ * (4 * (A' + 4) / ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hW' (norm_nonneg w)
      _ = 4 * (A' + 4) / ‖w‖ := by
          have h0 : ‖w‖ ≠ 0 := ne_of_gt hwn
          field_simp
  have hnum : ‖w * (deriv (wMap f) w - 1) - (wMap f w - w)‖ ≤ 4 * (A' + 4) + 4 := by
    calc ‖w * (deriv (wMap f) w - 1) - (wMap f w - w)‖
          ≤ ‖w * (deriv (wMap f) w - 1)‖ + ‖wMap f w - w‖ := norm_sub_le _ _
      _ ≤ 4 * (A' + 4) / ‖w‖ + 4 := add_le_add hnum1 hWsub
      _ ≤ 4 * (A' + 4) + 4 := by
          have hle : 4 * (A' + 4) / ‖w‖ ≤ 4 * (A' + 4) := by
            rw [div_le_iff₀ hwn]
            nlinarith [hb.hA', norm_nonneg w]
          linarith
  have hWnorm : ‖w‖ - 4 ≤ ‖wMap f w‖ := by
    have h := norm_add_le (wMap f w) (w - wMap f w)
    have he : wMap f w + (w - wMap f w) = w := by ring
    rw [he] at h
    have h2 : ‖w - wMap f w‖ = ‖wMap f w - w‖ := norm_sub_rev _ _
    rw [h2] at h
    linarith
  have hdenlow : ‖w‖ ^ 2 / 2 ≤ ‖w * wMap f w‖ := by
    rw [norm_mul]
    have h1 : ‖w‖ ^ 2 / 2 ≤ ‖w‖ * (‖w‖ - 4) := by nlinarith
    have h2 : ‖w‖ * (‖w‖ - 4) ≤ ‖w‖ * ‖wMap f w‖ :=
      mul_le_mul_of_nonneg_left hWnorm (norm_nonneg w)
    linarith
  calc ‖deriv (wMap f) w / (wMap f w) - 1 / w‖
      = ‖(w * (deriv (wMap f) w - 1) - (wMap f w - w)) / (w * wMap f w)‖ := by rw [hkey]
    _ = ‖w * (deriv (wMap f) w - 1) - (wMap f w - w)‖ / ‖w * wMap f w‖ := norm_div _ _
    _ ≤ (4 * (A' + 4) + 4) / (‖w‖ ^ 2 / 2) :=
        div_le_div₀ (by linarith [hb.hA']) hnum (by positivity) hdenlow
    _ = 2 * (4 * (A' + 4) + 4) / ‖w‖ ^ 2 := by
        have h0 : ‖w‖ ≠ 0 := ne_of_gt hwn
        field_simp

/-! ## Derivative of the approximate coordinate and of the defect -/

/-- Derivative of `approxCoord c` on the slit plane. -/
lemma hasDerivAt_approxCoord {c : ℂ} {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (approxCoord c) (1 - c / z) z := by
  have hlog : HasDerivAt Complex.log z⁻¹ z := Complex.hasDerivAt_log hz
  have h3 : HasDerivAt (fun w : ℂ => w - c * Complex.log w) (1 - c * z⁻¹) z :=
    (hasDerivAt_id z).sub (hlog.const_mul c)
  have he : (fun w : ℂ => w - c * Complex.log w) = approxCoord c := by funext w; rfl
  rw [he] at h3
  have h4 : 1 - c * z⁻¹ = 1 - c / z := by rw [div_eq_mul_inv]
  rw [h4] at h3
  exact h3

/-- Derivative of the defect `coordError f (1 - a)` in the region. -/
lemma hasDerivAt_coordError (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : 1 / r + 9 < w.re) (hWslit : wMap f w ∈ Complex.slitPlane) :
    HasDerivAt (coordError f (1 - a))
      ((1 - (1 - a) / (wMap f w)) * deriv (wMap f) w - (1 - (1 - a) / w)) w := by
  have hwr : (0 : ℝ) < w.re := by
    have := one_div_pos.mpr hb.hr; linarith
  have hWmap : HasDerivAt (wMap f) (deriv (wMap f) w) w :=
    (wMap_hasDerivAt hb hw).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (approxCoord (1 - a) ∘ wMap f)
      ((1 - (1 - a) / (wMap f w)) * deriv (wMap f) w) w :=
    (hasDerivAt_approxCoord hWslit).comp w hWmap
  have hwapprox : HasDerivAt (approxCoord (1 - a)) (1 - (1 - a) / w) w :=
    hasDerivAt_approxCoord (Or.inl hwr)
  have hsub := hcomp.sub hwapprox
  have hres := hsub.sub_const 1
  have hfun : (fun x : ℂ => ((approxCoord (1 - a) ∘ wMap f) - approxCoord (1 - a)) x - 1)
      = coordError f (1 - a) := by
    funext z
    simp only [Pi.sub_apply, Function.comp_apply, coordError, approxCoord]
  rw [hfun] at hres
  exact hres

/-! ## The main estimate -/

theorem coordError_deriv_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ N B : ℝ, 0 < N ∧ 0 ≤ B ∧ 1 / r < N ∧
      ∀ w : ℂ, N < w.re → ‖deriv (coordError f (1 - a)) w‖ ≤ B / ‖w‖ ^ 2 := by
  refine ⟨1 / r + 9, 4 * (A' + 4) + 2 * ‖(1 : ℂ) - a‖ * (4 * (A' + 4) + 4), ?_, ?_, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 / r := one_div_pos.mpr hb.hr
    linarith
  · have h1 : (0 : ℝ) ≤ 4 * (A' + 4) := by linarith [hb.hA']
    have h2 : (0 : ℝ) ≤ 4 * (A' + 4) + 4 := by linarith
    have h3 : (0 : ℝ) ≤ ‖(1 : ℂ) - a‖ := norm_nonneg _
    nlinarith
  · linarith [one_div_pos.mpr hb.hr]
  · intro w hw
    have h9 : (9 : ℝ) < ‖w‖ := nine_lt_norm hb.hr hw
    obtain ⟨hWsub, hWre⟩ := wMap_sub_aux hb hw
    have hWslit : wMap f w ∈ Complex.slitPlane := Or.inl hWre
    have hhas := hasDerivAt_coordError hb hw hWslit
    have hderiv : deriv (coordError f (1 - a)) w
        = (1 - (1 - a) / (wMap f w)) * deriv (wMap f) w - (1 - (1 - a) / w) := hhas.deriv
    rw [hderiv]
    have hW' := wMap_deriv_bound_aux hb hw
    have hratio := wMap_deriv_ratio_aux hb hw
    have hkey : (1 - (1 - a) / (wMap f w)) * deriv (wMap f) w - (1 - (1 - a) / w)
        = (deriv (wMap f) w - 1)
            - (1 - a) * (deriv (wMap f) w / (wMap f w) - 1 / w) := by
      simp only [div_eq_mul_inv]; ring
    rw [hkey, sub_eq_add_neg]
    have h1 : ‖deriv (wMap f) w - 1‖ ≤ 4 * (A' + 4) / ‖w‖ ^ 2 := hW'
    have h2 : ‖-((1 - a) * (deriv (wMap f) w / (wMap f w) - 1 / w))‖
        ≤ ‖1 - a‖ * (2 * (4 * (A' + 4) + 4) / ‖w‖ ^ 2) := by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
    calc ‖(deriv (wMap f) w - 1)
            + -((1 - a) * (deriv (wMap f) w / (wMap f w) - 1 / w))‖
        ≤ ‖deriv (wMap f) w - 1‖
            + ‖-((1 - a) * (deriv (wMap f) w / (wMap f w) - 1 / w))‖ := norm_add_le _ _
      _ ≤ 4 * (A' + 4) / ‖w‖ ^ 2 + ‖1 - a‖ * (2 * (4 * (A' + 4) + 4) / ‖w‖ ^ 2) :=
          add_le_add h1 h2
      _ = (4 * (A' + 4) + 2 * ‖(1 : ℂ) - a‖ * (4 * (A' + 4) + 4)) / ‖w‖ ^ 2 := by ring

end

end Work.FatouCoord.Estimate
