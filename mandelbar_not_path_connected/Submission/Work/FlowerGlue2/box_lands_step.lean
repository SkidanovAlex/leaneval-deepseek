/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.L0

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.box_lands_step` — the chart one-step estimates of the landing argument

The *proved* elementary pieces of the landing lemma `Work.FlowerGlue2.box_lands_attr`, which is
**false as stated** in the abstract generality of `AttrCompare` (see `NOTES_FALSE_box_deep_attr2.md`
and the header of `box_lands_attr.lean`; the missing hypothesis is that the petal contains the deep
tail `{Re (w0 P ·) > M₀}`).  They are independent of that missing uniform transient bound:

* `Work.FlowerGlue2.zt` — the `c₀`-chart coordinate `zt P z = (z - z₁)/s c₀`, with
  `w0 P z = -1/zt P z`, `zt P z = -1/w0 P z`, and `z = m c₀ + s c₀ · zt P z` (`z_eq_chart`);
* `Ft_chart`, `w0_Ft_chart`, `w0_incr_chart` — the **exact** one-step formula of the chart:
  `w0 P (Ft c₀ z) = w0 P z / (1 + ζ h ζ)` and `w0 P (Ft c₀ z) - w0 P z = h ζ/(1 + ζ h ζ)`
  (`ζ = zt P z`); the increment expansion `O(‖ζ‖²)` around `1 - κ₀ ζ` is
  `Work.FlowerGlue2.incr_expansion_aux`;
* `h_close'` — `‖h ζ - 1‖ ≤ A‖ζ‖² + ‖h₁‖‖ζ‖` (with `h c₀ 0 = 1`, `tau_c₀`); the norm bounds on `h`
  are `Work.FlowerGlue2.h_norm_bounds'` (in `incr_defs`);
* `phi_iterate_loc` — the Abel equation along a whole orbit: `φa (F^j y) = φa y + j`;
* `z₁_not_mem_loc` — the parabolic point is not in the petal;
* `re_mul_log_le'`, `neg_re_mul_log_le'`, `log_le_abs'` — the real `log` estimates bounding
  `Re(κ₀ log (w0 ·))` and `Im(κ₀ log (w0 ·))` (via `(log w).re = log ‖w‖` and `|arg w| ≤ π/2` for
  `Re w > 0`).
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Filter Set Metric
open scoped Topology
open Work.PARIMPL (ParNormal Ft gtc)

namespace Work.FlowerGlue2

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

def zt (P : ParNormal d) (z : ℂ) : ℂ := (z - d.z₁) / P.s c₀

theorem s_ne' (P : ParNormal d) : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)

theorem a_eq_zero' (P : ParNormal d) : P.a c₀ = 0 := by
  have h := P.a_sq c₀ (mem_ball_self P.hρ₀)
  rw [P.a2₀] at h
  have h' : P.a c₀ * P.a c₀ = 0 := by simpa [pow_two] using h
  exact mul_self_eq_zero.mp h'

theorem w0_eq_neg_inv_zt' (P : ParNormal d) (z : ℂ) : w0 P z = -1 / zt P z := by
  have h1 : (1 : ℂ) / zt P z = P.s c₀ / (z - d.z₁) := by
    simp only [zt]; rw [one_div_div]
  simp only [w0_apply, neg_div, h1]

theorem neg_inv_w0_eq_zt' (P : ParNormal d) (z : ℂ) : -1 / w0 P z = zt P z := by
  rw [w0_eq_neg_inv_zt']
  by_cases h : zt P z = 0
  · simp [h]
  · field_simp

theorem zt_ne_zero' (P : ParNormal d) {z : ℂ} (hz : z ≠ d.z₁) : zt P z ≠ 0 := by
  rw [← neg_inv_w0_eq_zt' P z]
  exact div_ne_zero (show (-1 : ℂ) ≠ 0 by norm_num) (w0_ne_zero hz)

theorem z_eq_chart (P : ParNormal d) {z : ℂ} (hz : z ≠ d.z₁) :
    z = P.m c₀ + P.s c₀ * zt P z := by
  have hrec : z = d.z₁ - P.s c₀ / w0 P z := chart_recovery (P := P) hz
  have key : P.s c₀ * zt P z = -(P.s c₀ / w0 P z) := by
    rw [w0_eq_neg_inv_zt' P z]
    simp only [zt]
    field_simp
  conv_lhs => rw [hrec]
  rw [P.m₀, key, sub_eq_add_neg]

/-- The normal form in the chart: `Ft c₀ (m c₀ + s c₀ ζ) - z₁ = s c₀ (ζ + ζ² h c₀ ζ)`. -/
theorem Ft_chart (P : ParNormal d) {ζ : ℂ} (hζ : ‖ζ‖ < P.r) :
    Ft c₀ (P.m c₀ + P.s c₀ * ζ) - d.z₁ = P.s c₀ * (ζ + ζ ^ 2 * P.h c₀ ζ) := by
  have hmem : c₀ ∈ ball c₀ P.ρ₀ := mem_ball_self P.hρ₀
  have hconj := P.conj c₀ hmem ζ (by simpa [mem_ball_zero_iff] using hζ)
  rw [P.m₀, a_eq_zero' P] at hconj
  rw [show Work.Implosion.normalForm (0 : ℂ) (P.h c₀) ζ = ζ + ζ ^ 2 * P.h c₀ ζ by
        simp [Work.Implosion.normalForm]] at hconj
  rw [P.m₀]
  rw [hconj]
  ring

/-- **The exact one-step formula of the chart, in chart coordinates.** -/
theorem w0_Ft_chart (P : ParNormal d) {ζ : ℂ} (hζ : ‖ζ‖ < P.r) (hne : ζ ≠ 0)
    (hB : 1 + ζ * P.h c₀ ζ ≠ 0) :
    w0 P (Ft c₀ (P.m c₀ + P.s c₀ * ζ)) = -1 / ζ / (1 + ζ * P.h c₀ ζ) := by
  have hs : P.s c₀ ≠ 0 := s_ne' P
  have hsub := Ft_chart P hζ
  have hfac : ζ + ζ ^ 2 * P.h c₀ ζ = ζ * (1 + ζ * P.h c₀ ζ) := by ring
  rw [w0_apply, hsub, hfac]
  field_simp

/-- The per-step increment in chart coordinates. -/
theorem w0_incr_chart (P : ParNormal d) {ζ : ℂ} (hζ : ‖ζ‖ < P.r) (hne : ζ ≠ 0)
    (hB : 1 + ζ * P.h c₀ ζ ≠ 0) :
    w0 P (Ft c₀ (P.m c₀ + P.s c₀ * ζ)) - (-1 / ζ) = P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) := by
  rw [w0_Ft_chart P hζ hne hB]
  field_simp
  ring

theorem h_close' (P : ParNormal d) {ζ : ℂ} (hζ : ‖ζ‖ < P.r) :
    ‖P.h c₀ ζ - 1‖ ≤ P.A * ‖ζ‖ ^ 2 + ‖P.h1 c₀‖ * ‖ζ‖ := by
  have hb := P.bounds c₀ (mem_ball_self P.hρ₀)
  have h1 := hb.2.2.1 ζ hζ
  rw [tau_c₀ P] at h1
  calc ‖P.h c₀ ζ - 1‖
      = ‖(P.h c₀ ζ - 1 - P.h1 c₀ * ζ) + P.h1 c₀ * ζ‖ := by congr 1; ring
    _ ≤ ‖P.h c₀ ζ - 1 - P.h1 c₀ * ζ‖ + ‖P.h1 c₀ * ζ‖ := norm_add_le _ _
    _ ≤ P.A * ‖ζ‖ ^ 2 + ‖P.h1 c₀‖ * ‖ζ‖ := by
        rw [norm_mul]
        linarith


theorem phi_iterate_loc {Pa : Set ℂ} {φa : ℂ → ℂ}
    (P : ParNormal d) (A : AttrCompare P Pa φa) {y : ℂ} (hy : y ∈ Pa) (j : ℕ) :
    φa ((Ft c₀)^[j] y) = φa y + j := by
  induction j with
  | zero => simp
  | succ k ih =>
      have hmk : (Ft c₀)^[k] y ∈ Pa := by
        clear ih
        induction k with
        | zero => simpa using hy
        | succ n hh => simpa [Function.iterate_succ_apply'] using A.mapsTo_Pa hh
      rw [Function.iterate_succ_apply', A.φa_shift _ hmk, ih]
      push_cast
      ring

theorem z₁_not_mem_loc {Pa : Set ℂ} {φa : ℂ → ℂ}
    (P : ParNormal d) (A : AttrCompare P Pa φa) : d.z₁ ∉ Pa := by
  intro h
  have hfix : Ft c₀ d.z₁ = d.z₁ := by
    have h1 : (Ft c₀) d.z₁ = Work.PARIMPL.gtc c₀ (Work.PARIMPL.gtc c₀ d.z₁) := by
      rw [Work.PARIMPL.Ft_eq_g_comp]; rfl
    rw [h1]
    have h2 : Work.PARIMPL.gtc c₀ d.z₁ = d.z₁ := d.per_half
    simp only [h2]
  have h2 := A.φa_shift d.z₁ h
  rw [hfix] at h2
  have h3 : (1 : ℂ) = 0 := by linear_combination -h2
  exact one_ne_zero h3

theorem re_mul_log_le' {κ w : ℂ} (hw : 0 < w.re) (hw1 : 1 ≤ ‖w‖) :
    (κ * Complex.log w).re ≤ ‖κ‖ * (Real.log ‖w‖ + Real.pi / 2) := by
  have hre : (Complex.log w).re = Real.log ‖w‖ := Complex.log_re w
  have hlog0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw1
  have him : |(Complex.log w).im| ≤ Real.pi / 2 := by
    have h2 := (Complex.arg_le_pi_div_two_iff (z := w)).mpr (Or.inl (le_of_lt hw))
    have h3 := (Complex.neg_pi_div_two_le_arg_iff (z := w)).mpr (Or.inl (le_of_lt hw))
    rw [Complex.log_im]
    exact abs_le.mpr ⟨h3, h2⟩
  have hmul : (κ * Complex.log w).re = κ.re * (Complex.log w).re - κ.im * (Complex.log w).im := by
    simp [Complex.mul_re]
  rw [hmul, hre]
  have h4 : κ.re * Real.log ‖w‖ ≤ ‖κ‖ * Real.log ‖w‖ :=
    mul_le_mul_of_nonneg_right (Complex.re_le_norm κ) hlog0
  have h7 : -κ.im * (Complex.log w).im ≤ ‖κ‖ * (Real.pi / 2) := by
    have hni : -κ.im ≤ ‖κ‖ := by
      have h5 := Complex.abs_im_le_norm κ
      have h6 := neg_le_abs κ.im
      linarith
    by_cases hx : 0 ≤ (Complex.log w).im
    · refine le_trans (mul_le_mul_of_nonneg_right hni hx) ?_
      exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self (Complex.log w).im]) (norm_nonneg κ)
    · have hx2 : (Complex.log w).im ≤ 0 := le_of_not_ge hx
      rw [show -κ.im * (Complex.log w).im = κ.im * (-(Complex.log w).im) by ring]
      refine le_trans (mul_le_mul_of_nonneg_right (Complex.im_le_norm κ) (by linarith)) ?_
      exact mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (Complex.log w).im]) (norm_nonneg κ)
  linarith

theorem neg_re_mul_log_le' {κ w : ℂ} (hw : 0 < w.re) (hw1 : 1 ≤ ‖w‖) :
    -(κ * Complex.log w).re ≤ ‖κ‖ * (Real.log ‖w‖ + Real.pi / 2) := by
  have h := re_mul_log_le' (κ := -κ) hw hw1
  rw [neg_mul] at h
  simpa using h



theorem log_le_abs' (t : ℝ) : Real.log t ≤ |t| := by
  rw [← Real.log_abs t]
  exact Real.log_le_self (abs_nonneg t)


end
