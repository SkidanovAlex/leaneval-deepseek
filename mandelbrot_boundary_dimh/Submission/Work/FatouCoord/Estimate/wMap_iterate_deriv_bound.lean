import Mathlib
import Submission.Work.FatouCoord.Setup

namespace Work.FatouCoord.Estimate

open Work.FatouCoord

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {z w : ℂ}

/-! ## Basic calculus facts -/

/-- The derivative of the chart `w ↦ -1/w`. -/
lemma hasDerivAt_chart {w : ℂ} (hw : w ≠ 0) : HasDerivAt chart (1 / w^2) w := by
  have h := (hasDerivAt_inv hw).const_mul (-1)
  have e : (fun y : ℂ => (-1) * y⁻¹) = chart := by funext y; simp [chart, div_eq_mul_inv]
  rw [e] at h
  convert h using 1
  ring

lemma deriv_chart {w : ℂ} (hw : w ≠ 0) : deriv chart w = 1 / w^2 :=
  (hasDerivAt_chart hw).deriv

lemma norm_neg_one_div (w : ℂ) : ‖-1 / w‖ = 1 / ‖w‖ := by simp

/-- `f` is complex differentiable on the ball of radius `r`. -/
lemma differentiableAt_f (hb : ParabolicBounds f h a r A A') {z : ℂ} (hz : z ∈ ball 0 r) :
    DifferentiableAt ℂ f z := by
  have hdiff : DifferentiableAt ℂ (fun z : ℂ => z + z^2 * h z) z := by
    have hh : DifferentiableAt ℂ h z :=
      hb.h_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    exact (differentiableAt_id.add ((differentiableAt_id.pow 2).mul hh))
  have heq : f =ᶠ[𝓝 z] (fun z : ℂ => z + z^2 * h z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with u hu
    exact hb.f_eq u hu
  exact hdiff.congr_of_eventuallyEq heq

/-- On the ball of radius `r`, `deriv f` is given by the expansion of `h`. -/
lemma deriv_f (hb : ParabolicBounds f h a r A A') {z : ℂ} (hz : z ∈ ball 0 r) :
    deriv f z = 1 + 2*z*h z + z^2 * deriv h z := by
  have heq : f =ᶠ[𝓝 z] (fun z : ℂ => z + z^2 * h z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with u hu
    exact hb.f_eq u hu
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hh : HasDerivAt h (deriv h z) z :=
    (hb.h_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ => z^2 * h z) (2*z*h z + z^2 * deriv h z) z := by
    have key := (hasDerivAt_pow 2 z).mul hh
    have hfun : ((fun x : ℂ => x^2) * h) = fun z : ℂ => z^2 * h z := by funext x; rfl
    rw [hfun] at key
    convert key using 1
    ring
  have h3 : HasDerivAt (fun z : ℂ => z + z^2 * h z) (1 + (2*z*h z + z^2 * deriv h z)) z := by
    have key := (hasDerivAt_id z).add h2
    have hfun : (id + fun z : ℂ => z^2 * h z) = fun z : ℂ => z + z^2 * h z := by funext x; rfl
    rwa [hfun] at key
  rw [h3.deriv]; ring

/-! ## Constants and the quantitative bounds -/

/-- Constant in the near-translation estimate for `wMap`. -/
def Ksub (A : ℝ) (a : ℂ) : ℝ := 2 * (2*A + ‖a‖ + ‖a - 1‖)

/-- Constant in the estimate `deriv (wMap f) = 1 + O(w⁻²)`. -/
def Kderiv (A' : ℝ) : ℝ := 4 * (A' + 4)

lemma Ksub_nonneg {A : ℝ} (hA : 0 ≤ A) (a : ℂ) : 0 ≤ Ksub A a := by
  rw [Ksub]; positivity

lemma Kderiv_nonneg {A' : ℝ} (hA' : 0 ≤ A') : 0 ≤ Kderiv A' := by
  rw [Kderiv]; positivity

/-- Bound for the numerator appearing in the near-translation estimate. -/
lemma norm_sub_identity_bound (hb : ParabolicBounds f h a r A A') {z : ℂ} (hz : z ∈ ball 0 r)
    (hzn : ‖z‖ ≤ 1) :
    ‖(h z - 1 - a*z)*(1 - z) + (a-1)*z - a*z^2‖ ≤ (Ksub A a / 2) * ‖z‖ := by
  have hA0 : 0 ≤ A := hb.hA
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have ht2 : ‖z‖^2 ≤ ‖z‖ := by nlinarith [hz0, hzn]
  have hclose : ‖h z - 1 - a*z‖ ≤ A*‖z‖^2 := hb.h_close z hz
  have h1z : ‖(1:ℂ) - z‖ ≤ 1 + ‖z‖ := by
    calc ‖(1:ℂ) - z‖ ≤ ‖(1:ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one]
  have hsplit : ‖(h z - 1 - a*z)*(1 - z) + (a-1)*z - a*z^2‖
      ≤ ‖h z - 1 - a*z‖ * ‖(1:ℂ) - z‖ + ‖a-1‖ * ‖z‖ + ‖a‖ * ‖z‖^2 := by
    calc ‖(h z - 1 - a*z)*(1 - z) + (a-1)*z - a*z^2‖
        ≤ ‖(h z - 1 - a*z)*(1 - z) + (a-1)*z‖ + ‖a*z^2‖ := norm_sub_le _ _
      _ ≤ (‖(h z - 1 - a*z)*(1 - z)‖ + ‖(a-1)*z‖) + ‖a*z^2‖ := by
          linarith [norm_add_le ((h z - 1 - a*z)*(1 - z)) ((a-1)*z)]
      _ = ‖h z - 1 - a*z‖ * ‖(1:ℂ) - z‖ + ‖a-1‖ * ‖z‖ + ‖a‖ * ‖z‖^2 := by
          rw [norm_mul, norm_mul, norm_mul, norm_pow]
  have hb1 : ‖h z - 1 - a*z‖ * ‖(1:ℂ) - z‖ ≤ (A*‖z‖^2) * (1 + ‖z‖) :=
    mul_le_mul hclose h1z (by positivity) (mul_nonneg hA0 (sq_nonneg _))
  have hb1b : (A*‖z‖^2) * (1 + ‖z‖) ≤ 2*A*‖z‖ := by
    have h1 : A*‖z‖^2 ≤ A*‖z‖ := mul_le_mul_of_nonneg_left ht2 hA0
    have h2 : 1 + ‖z‖ ≤ 2 := by linarith
    calc (A*‖z‖^2) * (1 + ‖z‖) ≤ (A*‖z‖) * 2 :=
          mul_le_mul h1 h2 (by positivity) (mul_nonneg hA0 hz0)
      _ = 2*A*‖z‖ := by ring
  have hb4 : ‖a‖ * ‖z‖^2 ≤ ‖a‖ * ‖z‖ := mul_le_mul_of_nonneg_left ht2 (norm_nonneg a)
  calc ‖(h z - 1 - a*z)*(1 - z) + (a-1)*z - a*z^2‖
      ≤ ‖h z - 1 - a*z‖ * ‖(1:ℂ) - z‖ + ‖a-1‖ * ‖z‖ + ‖a‖ * ‖z‖^2 := hsplit
    _ ≤ 2*A*‖z‖ + ‖a-1‖ * ‖z‖ + ‖a‖ * ‖z‖ := by linarith [hb1, hb1b, hb4]
    _ = (Ksub A a / 2) * ‖z‖ := by rw [Ksub]; ring

/-- The pull-back `wMap` is a translation by `1` up to `O(1/w)`. -/
lemma wMap_sub_bound_aux (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hre : 0 < w.re) (hrw : 1/r < ‖w‖) (h4 : 4 ≤ ‖w‖) :
    ‖wMap f w - w - 1‖ ≤ Ksub A a / ‖w‖ := by
  have hnw : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) h4
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hnw)
  have hz : -1/w ∈ ball 0 r := by
    rw [mem_ball_zero_iff]; exact norm_neg_one_div_lt hb.hr hw0 hrw
  have hz1 : ‖(-1/w : ℂ)‖ = 1/‖w‖ := norm_neg_one_div w
  have hzn : ‖(-1/w : ℂ)‖ ≤ 1 := by
    rw [hz1]; rw [div_le_one hnw]; linarith
  have hzh : ‖(-1/w) * h (-1/w)‖ ≤ 1/2 := by
    have hbnd : ‖(-1/w) * h (-1/w)‖ ≤ 2/‖w‖ := by
      calc ‖(-1/w) * h (-1/w)‖ ≤ ‖(-1/w : ℂ)‖ * ‖h (-1/w)‖ := norm_mul_le _ _
        _ = (1/‖w‖) * ‖h (-1/w)‖ := by rw [hz1]
        _ ≤ (1/‖w‖) * 2 := mul_le_mul_of_nonneg_left (hb.h_bound (-1/w) hz) (by positivity)
        _ = 2/‖w‖ := by ring
    have : 2/‖w‖ ≤ (1:ℝ)/2 := by rw [div_le_iff₀ hnw]; linarith
    linarith
  have h1zh : 1 + (-1/w) * h (-1/w) ≠ 0 := by
    intro h0
    have hzneg : (-1/w) * h (-1/w) = -1 := by linear_combination h0
    have hh1 : ‖(-1/w) * h (-1/w)‖ = 1 := by rw [hzneg]; simp
    linarith
  have hsub := wMap_sub_eq hb.hr hb.f_eq hre hrw h1zh
  have hstep : (h (-1/w) / (1 + (-1/w) * h (-1/w)) - 1) * (1 + (-1/w) * h (-1/w))
      = h (-1/w) - (1 + (-1/w) * h (-1/w)) := by
    rw [sub_mul, div_mul_cancel₀ _ h1zh, one_mul]
  have hident : (wMap f w - w - 1) * (1 + (-1/w) * h (-1/w))
      = (h (-1/w) - 1 - a*(-1/w)) * (1 - (-1/w)) + (a-1)*(-1/w) - a*(-1/w)^2 := by
    rw [show wMap f w - w - 1 = h (-1/w) / (1 + (-1/w) * h (-1/w)) - 1 by rw [hsub], hstep]
    ring
  have hden : 1/2 ≤ ‖1 + (-1/w) * h (-1/w)‖ := by
    have h1 : ‖(1:ℂ)‖ ≤ ‖1 + (-1/w) * h (-1/w)‖ + ‖(-1/w) * h (-1/w)‖ := by
      have hh := norm_sub_le (1 + (-1/w) * h (-1/w)) ((-1/w) * h (-1/w))
      simpa using hh
    rw [norm_one] at h1
    linarith
  have hnum := norm_sub_identity_bound hb hz hzn
  have hEB2 : ‖wMap f w - w - 1‖ * ‖1 + (-1/w) * h (-1/w)‖
      ≤ (Ksub A a / 2) * ‖(-1/w : ℂ)‖ := by
    rw [← norm_mul, hident]
    exact hnum
  have hcell : ‖wMap f w - w - 1‖
      ≤ 2 * (‖wMap f w - w - 1‖ * ‖1 + (-1/w) * h (-1/w)‖) := by
    have h1 : 1 ≤ 2 * ‖1 + (-1/w) * h (-1/w)‖ := by linarith
    calc ‖wMap f w - w - 1‖ = ‖wMap f w - w - 1‖ * 1 := by ring
      _ ≤ ‖wMap f w - w - 1‖ * (2 * ‖1 + (-1/w) * h (-1/w)‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = 2 * (‖wMap f w - w - 1‖ * ‖1 + (-1/w) * h (-1/w)‖) := by ring
  calc ‖wMap f w - w - 1‖
      ≤ 2 * (‖wMap f w - w - 1‖ * ‖1 + (-1/w) * h (-1/w)‖) := hcell
    _ ≤ 2 * ((Ksub A a / 2) * ‖(-1/w : ℂ)‖) := by linarith [hEB2]
    _ = Ksub A a / ‖w‖ := by rw [hz1]; ring


/-! ## Facts on the good half-plane -/

/-- The basic facts available on the half-plane `Re w > 0` with `‖w‖ ≥ 4` and `‖w‖ > 1/r`. -/
lemma wMap_aux_facts (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hrw : 1/r < ‖w‖) (h4 : 4 ≤ ‖w‖) :
    w ≠ 0 ∧ (-1/w) ∈ ball 0 r ∧ ‖(-1/w : ℂ)‖ = 1/‖w‖ ∧ ‖(-1/w : ℂ)‖ ≤ 1 ∧
      ‖(-1/w) * h (-1/w)‖ ≤ 1/2 ∧ 1 + (-1/w) * h (-1/w) ≠ 0 ∧ f (-1/w) ≠ 0 := by
  have hnw : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) h4
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hnw)
  have hz : -1/w ∈ ball 0 r := by
    rw [mem_ball_zero_iff]; exact norm_neg_one_div_lt hb.hr hw0 hrw
  have hz1 : ‖(-1/w : ℂ)‖ = 1/‖w‖ := norm_neg_one_div w
  have hzn : ‖(-1/w : ℂ)‖ ≤ 1 := by rw [hz1]; rw [div_le_one hnw]; linarith
  have hzh : ‖(-1/w) * h (-1/w)‖ ≤ 1/2 := by
    have hbnd : ‖(-1/w) * h (-1/w)‖ ≤ 2/‖w‖ := by
      calc ‖(-1/w) * h (-1/w)‖ ≤ ‖(-1/w : ℂ)‖ * ‖h (-1/w)‖ := norm_mul_le _ _
        _ = (1/‖w‖) * ‖h (-1/w)‖ := by rw [hz1]
        _ ≤ (1/‖w‖) * 2 := mul_le_mul_of_nonneg_left (hb.h_bound (-1/w) hz) (by positivity)
        _ = 2/‖w‖ := by ring
    have : 2/‖w‖ ≤ (1:ℝ)/2 := by rw [div_le_iff₀ hnw]; linarith
    linarith
  have h1zh : 1 + (-1/w) * h (-1/w) ≠ 0 := by
    intro h0
    have hzneg : (-1/w) * h (-1/w) = -1 := by linear_combination h0
    have hh1 : ‖(-1/w) * h (-1/w)‖ = 1 := by rw [hzneg]; simp
    linarith
  have hfz : f (-1/w) ≠ 0 := by
    have he : f (-1/w) = (-1/w) * (1 + (-1/w) * h (-1/w)) := by rw [hb.f_eq (-1/w) hz]; ring
    rw [he]
    exact mul_ne_zero (div_ne_zero (by norm_num) hw0) h1zh
  exact ⟨hw0, hz, hz1, hzn, hzh, h1zh, hfz⟩

/-! ## Derivative of `wMap` -/

/-- Explicit value of the derivative of `wMap` on the good half-plane. -/
lemma deriv_wMap_eq_aux (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hrw : 1/r < ‖w‖) (h4 : 4 ≤ ‖w‖) :
    deriv (wMap f) w
      = (1 + 2*(-1/w)*h (-1/w) + (-1/w)^2 * deriv h (-1/w)) / (1 + (-1/w)*h (-1/w))^2 := by
  obtain ⟨hw0, hz, hz1, hzn, hzh, h1zh, hfz⟩ := wMap_aux_facts hb hrw h4
  have hcw : HasDerivAt chart (1/w^2) w := hasDerivAt_chart hw0
  have hf : HasDerivAt f (deriv f (-1/w)) (-1/w) := (differentiableAt_f hb hz).hasDerivAt
  have hcf : HasDerivAt chart (1/(f (-1/w))^2) (f (-1/w)) := hasDerivAt_chart hfz
  have h1 : HasDerivAt (f ∘ chart) (deriv f (-1/w) * (1/w^2)) w := hf.comp w hcw
  have h2 : HasDerivAt (chart ∘ (f ∘ chart))
      ((1/(f (-1/w))^2) * (deriv f (-1/w) * (1/w^2))) w := hcf.comp w h1
  have hwMap : wMap f = chart ∘ (f ∘ chart) := by funext u; simp [wMap, Function.comp]
  have hderiv : deriv (wMap f) w = (1/(f (-1/w))^2) * (deriv f (-1/w) * (1/w^2)) := by
    rw [hwMap]; exact h2.deriv
  rw [hderiv, hb.f_eq (-1/w) hz, deriv_f hb hz]
  field_simp
  ring

/-- `deriv (wMap f) = 1 + O(w⁻²)` on the good half-plane. -/
lemma deriv_wMap_bound_aux (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hrw : 1/r < ‖w‖) (h4 : 4 ≤ ‖w‖) :
    ‖deriv (wMap f) w - 1‖ ≤ Kderiv A' / ‖w‖^2 := by
  obtain ⟨hw0, hz, hz1, hzn, hzh, h1zh, hfz⟩ := wMap_aux_facts hb hrw h4
  have hderiv := deriv_wMap_eq_aux hb hrw h4
  have hsub : deriv (wMap f) w - 1
      = (-1/w)^2 * (deriv h (-1/w) - h (-1/w)^2) / (1 + (-1/w)*h (-1/w))^2 := by
    rw [hderiv, div_sub_one (pow_ne_zero 2 h1zh)]
    congr 1
    ring
  rw [hsub, norm_div, norm_pow]
  have hnum : ‖(-1/w)^2 * (deriv h (-1/w) - h (-1/w)^2)‖
      ≤ ‖(-1/w : ℂ)‖^2 * (A' + 4) := by
    rw [norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) 2)
    calc ‖deriv h (-1/w) - h (-1/w)^2‖ ≤ ‖deriv h (-1/w)‖ + ‖h (-1/w)^2‖ := norm_sub_le _ _
      _ ≤ A' + 4 := by
          apply add_le_add (hb.h_deriv_bound (-1/w) hz)
          rw [norm_pow]
          nlinarith [hb.h_bound (-1/w) hz, norm_nonneg (h (-1/w))]
  have hden : 1/2 ≤ ‖1 + (-1/w) * h (-1/w)‖ := by
    have h1 : ‖(1:ℂ)‖ ≤ ‖1 + (-1/w) * h (-1/w)‖ + ‖(-1/w) * h (-1/w)‖ := by
      have hh := norm_sub_le (1 + (-1/w) * h (-1/w)) ((-1/w) * h (-1/w))
      simpa using hh
    rw [norm_one] at h1
    linarith
  have hdenpos : 0 < ‖1 + (-1/w) * h (-1/w)‖ := by linarith
  have hdenpos2 : 0 < ‖1 + (-1/w) * h (-1/w)‖^2 := pow_pos hdenpos 2
  have h1den : 1 / ‖1 + (-1/w) * h (-1/w)‖^2 ≤ 4 := by
    rw [div_le_iff₀ hdenpos2]
    nlinarith [hden, norm_nonneg (1 + (-1/w) * h (-1/w))]
  calc ‖(-1/w)^2 * (deriv h (-1/w) - h (-1/w)^2)‖ / ‖1 + (-1/w)*h (-1/w)‖^2
      ≤ (‖(-1/w : ℂ)‖^2 * (A' + 4)) / ‖1 + (-1/w)*h (-1/w)‖^2 :=
        div_le_div_of_nonneg_right hnum hdenpos2.le
    _ = ‖(-1/w : ℂ)‖^2 * (A' + 4) * (1 / ‖1 + (-1/w)*h (-1/w)‖^2) := by ring
    _ ≤ ‖(-1/w : ℂ)‖^2 * (A' + 4) * 4 := by
        apply mul_le_mul_of_nonneg_left h1den (mul_nonneg (sq_nonneg _) (by linarith [hb.hA']))
    _ = Kderiv A' / ‖w‖^2 := by rw [hz1, Kderiv, div_pow, one_pow]; ring

/-! ## Differentiability of `wMap` on the good half-plane -/

lemma differentiableAt_wMap (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hrw : 1/r < ‖w‖) (h4 : 4 ≤ ‖w‖) : DifferentiableAt ℂ (wMap f) w := by
  obtain ⟨hw0, hz, hz1, hzn, hzh, h1zh, hfz⟩ := wMap_aux_facts hb hrw h4
  have hcw : DifferentiableAt ℂ chart w := (hasDerivAt_chart hw0).differentiableAt
  have hfd : DifferentiableAt ℂ f (-1/w) := differentiableAt_f hb hz
  have hcf : DifferentiableAt ℂ chart (f (-1/w)) := (hasDerivAt_chart hfz).differentiableAt
  have hcomp : DifferentiableAt ℂ (chart ∘ f ∘ chart) w := hcf.comp w (hfd.comp w hcw)
  have hwMap : wMap f = chart ∘ f ∘ chart := by funext u; simp [wMap, Function.comp]
  rwa [← hwMap] at hcomp

/-! ## Growth of the real part along the orbit -/

lemma orbit_re_growth_aux (hb : ParabolicBounds f h a r A A') {N : ℝ}
    (hN4 : 4 ≤ N) (hNr : 1/r < N) (hNgr : 2 * Ksub A a ≤ N)
    {w : ℂ} (hw : N < w.re) :
    ∀ k : ℕ, N + (k:ℝ)/2 ≤ ((wMap f)^[k] w).re := by
  intro k
  induction k with
  | zero => simpa using hw.le
  | succ k ih =>
    have hk2 : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
    have hWre : N ≤ ((wMap f)^[k] w).re := by linarith
    have hWpos : 0 < ((wMap f)^[k] w).re := by linarith
    have hWn : N ≤ ‖((wMap f)^[k] w)‖ := le_trans hWre (Complex.re_le_norm _)
    have hsub := wMap_sub_bound_aux hb hWpos (lt_of_lt_of_le hNr hWn) (le_trans hN4 hWn)
    have hstep : ((wMap f)^[k] w).re + 1/2 ≤ (wMap f ((wMap f)^[k] w)).re := by
      have h1 : ‖wMap f ((wMap f)^[k] w) - ((wMap f)^[k] w) - 1‖
          ≤ Ksub A a / ‖((wMap f)^[k] w)‖ := hsub
      have h2 : Ksub A a / ‖((wMap f)^[k] w)‖ ≤ 1/2 := by
        rw [div_le_iff₀ (by linarith)]; linarith [hNgr, hWn]
      have h3 : (wMap f ((wMap f)^[k] w)).re
          ≥ ((wMap f)^[k] w).re + 1 - ‖wMap f ((wMap f)^[k] w) - ((wMap f)^[k] w) - 1‖ := by
        have hE : (wMap f ((wMap f)^[k] w) - ((wMap f)^[k] w) - 1).re
            = (wMap f ((wMap f)^[k] w)).re - (((wMap f)^[k] w).re + 1) := by
          rw [show wMap f ((wMap f)^[k] w) - ((wMap f)^[k] w) - 1
              = wMap f ((wMap f)^[k] w) - (((wMap f)^[k] w) + 1) by ring, Complex.sub_re]
          simp [Complex.add_re, Complex.one_re]
        have := (abs_le.mp (Complex.abs_re_le_norm
          (wMap f ((wMap f)^[k] w) - ((wMap f)^[k] w) - 1))).1
        linarith
      linarith
    rw [Function.iterate_succ_apply']
    push_cast
    linarith

/-! ## A telescoping bound for `∑ 1/(N+i)²` -/

lemma sum_range_inv_sq_le (N : ℝ) (hN : 0 < N) (k : ℕ) :
    ∑ i ∈ Finset.range k, 1/(N + (i:ℝ))^2 ≤ 1/N^2 + 1/N := by
  have hterm : ∀ i : ℕ,
      1/(N + ((i+1:ℕ):ℝ))^2 ≤ 1/(N + (i:ℝ)) - 1/(N + ((i+1:ℕ):ℝ)) := by
    intro i
    push_cast
    rw [show N + ((i:ℝ) + 1) = N + (i:ℝ) + 1 by ring]
    have key : 1/(N + (i:ℝ)) - 1/(N + (i:ℝ) + 1) - 1/(N + (i:ℝ) + 1)^2
        = 1/((N + (i:ℝ)) * (N + (i:ℝ) + 1)^2) := by
      field_simp
      ring
    have hpos : 0 < 1/((N + (i:ℝ)) * (N + (i:ℝ) + 1)^2) := by positivity
    linarith [key, hpos]
  have hstep : ∀ n : ℕ, ∑ i ∈ Finset.range n, 1/(N + ((i+1:ℕ):ℝ))^2 ≤ 1/N := by
    intro n
    calc ∑ i ∈ Finset.range n, 1/(N + ((i+1:ℕ):ℝ))^2
        ≤ ∑ i ∈ Finset.range n, (1/(N + (i:ℝ)) - 1/(N + ((i+1:ℕ):ℝ))) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = 1/(N + ((0:ℕ):ℝ)) - 1/(N + (n:ℝ)) := by
          rw [Finset.sum_range_sub' (fun j : ℕ => 1/(N + (j:ℝ)))]
      _ ≤ 1/N := by
          have hn : 0 ≤ 1/(N + (n:ℝ)) := by positivity
          have h0 : N + ((0:ℕ):ℝ) = N := by norm_num
          rw [h0]; linarith
  cases k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ k =>
    rw [Finset.sum_range_succ']
    have := hstep k
    have h0 : 1/(N + ((0:ℕ):ℝ))^2 = 1/N^2 := by norm_num
    rw [h0]
    linarith

/-! ## Derivatives of iterates -/

lemma hasDerivAt_iterate {g : ℂ → ℂ} {u : ℂ} (k : ℕ)
    (hd : ∀ i < k, DifferentiableAt ℂ g (g^[i] u)) :
    HasDerivAt (g^[k]) (∏ i ∈ Finset.range k, deriv g (g^[i] u)) u := by
  induction k with
  | zero =>
    rw [Function.iterate_zero]
    simpa using hasDerivAt_id u
  | succ k ih =>
    have hd' : ∀ i < k, DifferentiableAt ℂ g (g^[i] u) := fun i hi => hd i (Nat.lt_succ_of_lt hi)
    have hk := ih hd'
    have hgk : DifferentiableAt ℂ g (g^[k] u) := hd k (Nat.lt_succ_self k)
    have hcomp : HasDerivAt (g ∘ g^[k])
        (deriv g (g^[k] u) * ∏ i ∈ Finset.range k, deriv g (g^[i] u)) u :=
      (hgk.hasDerivAt).comp u hk
    rw [Function.iterate_succ', Finset.prod_range_succ]
    convert hcomp using 1
    ring

lemma norm_deriv_iterate_le {g : ℂ → ℂ} {u : ℂ} (k : ℕ)
    (hd : ∀ i < k, DifferentiableAt ℂ g (g^[i] u)) :
    ‖deriv (g^[k]) u‖ ≤ ∏ i ∈ Finset.range k, ‖deriv g (g^[i] u)‖ := by
  rw [(hasDerivAt_iterate k hd).deriv, norm_prod]

/-! ## The main theorem -/

theorem wMap_iterate_deriv_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ N M : ℝ, 0 < N ∧ 1 / r < N ∧ 0 ≤ M ∧
      ∀ w : ℂ, N < w.re → ∀ k : ℕ, ‖deriv ((wMap f)^[k]) w‖ ≤ M := by
  set N : ℝ := max 4 (max (1/r) (max (2 * Ksub A a) (Kderiv A'))) + 2 with hNdef
  have hN4 : 4 ≤ N := by
    rw [hNdef]
    have h0 := le_max_left (4:ℝ) (max (1/r) (max (2 * Ksub A a) (Kderiv A')))
    linarith
  have hNr : 1/r < N := by
    rw [hNdef]
    have h1 : 1/r ≤ max 4 (max (1/r) (max (2 * Ksub A a) (Kderiv A'))) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hNgr : 2 * Ksub A a ≤ N := by
    rw [hNdef]
    have h1 : 2 * Ksub A a ≤ max 4 (max (1/r) (max (2 * Ksub A a) (Kderiv A'))) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    linarith
  have hNpos : 0 < N := by linarith
  refine ⟨N, Real.exp (8 * Kderiv A' / N), hNpos, hNr, Real.exp_nonneg _, ?_⟩
  intro w hw k
  have hgrowth : ∀ i : ℕ, N + (i:ℝ)/2 ≤ ((wMap f)^[i] w).re :=
    orbit_re_growth_aux hb hN4 hNr hNgr hw
  have hi_norm : ∀ i : ℕ, N ≤ ‖((wMap f)^[i] w)‖ := by
    intro i
    have h1 := hgrowth i
    have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
    have h2 := Complex.re_le_norm ((wMap f)^[i] w)
    linarith
  have hd : ∀ i < k, DifferentiableAt ℂ (wMap f) ((wMap f)^[i] w) := by
    intro i _
    exact differentiableAt_wMap hb (lt_of_lt_of_le hNr (hi_norm i)) (le_trans hN4 (hi_norm i))
  refine le_trans (norm_deriv_iterate_le (g := wMap f) (u := w) k hd) ?_
  have hKdnn : 0 ≤ Kderiv A' := Kderiv_nonneg hb.hA'
  calc ∏ i ∈ Finset.range k, ‖deriv (wMap f) ((wMap f)^[i] w)‖
      ≤ ∏ i ∈ Finset.range k, (1 + Kderiv A' / (N + (i:ℝ)/2)^2) := by
        apply Finset.prod_le_prod₀
        · intro i _; positivity
        · intro i _
          have hbnd := deriv_wMap_bound_aux hb (lt_of_lt_of_le hNr (hi_norm i))
            (le_trans hN4 (hi_norm i))
          have hD : ‖deriv (wMap f) ((wMap f)^[i] w)‖
              ≤ ‖deriv (wMap f) ((wMap f)^[i] w) - 1‖ + 1 := by
            have hh := norm_add_le (deriv (wMap f) ((wMap f)^[i] w) - 1) 1
            simpa using hh
          have hle : ‖deriv (wMap f) ((wMap f)^[i] w) - 1‖
              ≤ Kderiv A' / (N + (i:ℝ)/2)^2 := by
            have h0 : N + (i:ℝ)/2 ≤ ‖((wMap f)^[i] w)‖ :=
              le_trans (hgrowth i) (Complex.re_le_norm _)
            have h0nn : 0 ≤ N + (i:ℝ)/2 := by positivity
            have hni : (N + (i:ℝ)/2)^2 ≤ ‖((wMap f)^[i] w)‖^2 := by
              nlinarith [h0, norm_nonneg ((wMap f)^[i] w), h0nn]
            calc ‖deriv (wMap f) ((wMap f)^[i] w) - 1‖
                ≤ Kderiv A' / ‖((wMap f)^[i] w)‖^2 := hbnd
              _ ≤ Kderiv A' / (N + (i:ℝ)/2)^2 :=
                  div_le_div_of_nonneg_left hKdnn (by positivity) hni
          linarith
    _ ≤ Real.exp (∑ i ∈ Finset.range k, Kderiv A' / (N + (i:ℝ)/2)^2) :=
        Real.prod_one_add_le_exp_sum _ (fun i => div_nonneg hKdnn (sq_nonneg _))
    _ ≤ Real.exp (8 * Kderiv A' / N) := by
        apply Real.exp_le_exp.mpr
        have hsum : ∑ i ∈ Finset.range k, 1/(N + (i:ℝ)/2)^2 ≤ 8/N := by
          have h1 : ∑ i ∈ Finset.range k, 1/(N + (i:ℝ)/2)^2
              ≤ ∑ i ∈ Finset.range k, 4/(N + (i:ℝ))^2 := by
            apply Finset.sum_le_sum; intro i _
            have hi : (0:ℝ) ≤ (i:ℝ) := by positivity
            have h1 : (0:ℝ) < N + (i:ℝ)/2 := by linarith
            have h2 : (0:ℝ) < N + (i:ℝ) := by linarith
            rw [div_le_div_iff₀ (pow_pos h1 2) (pow_pos h2 2)]
            nlinarith [hNpos, hi]
          have h2 : ∑ i ∈ Finset.range k, 4/(N + (i:ℝ))^2
              = 4 * ∑ i ∈ Finset.range k, 1/(N + (i:ℝ))^2 := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [mul_one_div]
          rw [h2] at h1
          have h3 := sum_range_inv_sq_le N hNpos k
          have hN1 : 1 ≤ N := by linarith
          have h4 : 4 * (1/N^2 + 1/N) ≤ 8/N := by
            have hNsq : 0 < N^2 := by positivity
            have hA : 4/N^2 ≤ 4/N := by
              rw [div_le_div_iff₀ hNsq hNpos]; nlinarith [hN1]
            have hB : 4 * (1/N^2 + 1/N) = 4/N^2 + 4/N := by ring
            rw [hB]
            have hC : 4/N + 4/N = 8/N := by ring
            linarith [hA, hC]
          linarith
        calc ∑ i ∈ Finset.range k, Kderiv A' / (N + (i:ℝ)/2)^2
            = Kderiv A' * ∑ i ∈ Finset.range k, 1/(N + (i:ℝ)/2)^2 := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [mul_one_div]
          _ ≤ Kderiv A' * (8/N) := mul_le_mul_of_nonneg_left hsum hKdnn
          _ = 8 * Kderiv A' / N := by ring

end

end Work.FatouCoord.Estimate
