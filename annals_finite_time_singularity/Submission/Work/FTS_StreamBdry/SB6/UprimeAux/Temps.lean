import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Defs
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.Temps` — the `wfun` facts used by the ODE bound

The elementary facts about `wfun θ = sin²θ cos³θ` needed by the singular-ODE bound: positivity,
the two quotient bounds, the two lower bounds and the four integral comparisons.  Everything is
derived from the unconditional identity `wfun_div_s2_eq` of `OdeFacts`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false

lemma Wpos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < wfun θ := by
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  rw [wfun]
  exact mul_pos (pow_pos hs 2) (pow_pos hc 3)

/-- `wfun` is continuous (as the product `sin²·cos³`). -/
lemma continuous_wfun : Continuous wfun := by
  have h : wfun = fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 := rfl
  rw [h]; fun_prop

/-- `wfun θ = sin θ cos²θ / 2 · sin 2θ` on `[0, π/2]`. -/
lemma Wdiv_le_theta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    wfun θ / Real.sin (2 * θ) ≤ θ / 2 := by
  rw [wfun_div_s2_eq]
  have hsin : Real.sin θ ≤ θ := le_of_lt (Real.sin_lt hθ.1)
  have hcos : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hmul : Real.sin θ * Real.cos θ ^ 2 ≤ θ * 1 :=
    mul_le_mul hsin hcos (sq_nonneg (Real.cos θ)) hθ.1.le
  linarith

lemma Wdiv_le_right {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    wfun θ / Real.sin (2 * θ) ≤ (Real.pi / 2 - θ) ^ 2 / 2 := by
  rw [wfun_div_s2_eq]
  set δ : ℝ := Real.pi / 2 - θ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith [hθ.2]
  have hδle : δ ≤ Real.pi := by rw [hδ]; linarith [hθ.1, Real.pi_pos]
  have hcos : Real.cos θ = Real.sin δ := by rw [hδ, Real.sin_pi_div_two_sub]
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsδ : Real.sin δ ≤ δ := le_of_lt (Real.sin_lt hδpos)
  have hsδnn : 0 ≤ Real.sin δ := Real.sin_nonneg_of_mem_Icc ⟨hδpos.le, hδle⟩
  have hsδ2 : Real.sin δ ^ 2 ≤ δ ^ 2 := by nlinarith [hsδ, hsδnn, hδpos]
  rw [hcos]
  have hmul : Real.sin θ * Real.sin δ ^ 2 ≤ 1 * δ ^ 2 :=
    mul_le_mul hsin1 hsδ2 (sq_nonneg _) (by norm_num)
  linarith

lemma Wge_left {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2 ≤ wfun θ := by
  have hsin : 2 / Real.pi * θ ≤ Real.sin θ :=
    Real.mul_le_sin hθ.1.le (by linarith [hθ.2, Real.pi_pos])
  have hsin2 : (2 / Real.pi * θ) ^ 2 ≤ Real.sin θ ^ 2 := by
    have h1 : 0 ≤ 2 / Real.pi * θ := mul_nonneg (by positivity) hθ.1.le
    nlinarith [hsin, h1]
  have hsinn : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
  have hsinle : Real.sin θ ≤ Real.sqrt 2 / 2 := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos, hθ.1.le])
      (by linarith [Real.pi_pos]) hθ.2
    rwa [Real.sin_pi_div_four] at h
  have hsinsq : Real.sin θ ^ 2 ≤ 1 / 2 := by
    have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have h3 : Real.sin θ ^ 2 ≤ (Real.sqrt 2 / 2) ^ 2 := by
      have hnn : 0 ≤ Real.sqrt 2 / 2 := by positivity
      nlinarith [hsinle, hnn, hsinn]
    linarith [h2, h3]
  have hcos2 : 1 / 2 ≤ Real.cos θ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos θ := by
    have hnn : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos, hθ.1.le], by linarith [hθ.2, Real.pi_pos]⟩
    have h2 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.cos θ ^ 2 := by
      have h3 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
      linarith [h3, hcos2]
    nlinarith [h2, hnn, Real.sqrt_nonneg 2]
  have hcos3 : (Real.sqrt 2 / 2) ^ 3 ≤ Real.cos θ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcos 3
  have hval : (Real.sqrt 2 / 2) ^ 3 = Real.sqrt 2 / 4 := by
    rw [div_pow, show (Real.sqrt 2) ^ 3 = Real.sqrt 2 * (Real.sqrt 2) ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring_nf
  have hexp : (2 / Real.pi * θ) ^ 2 * (Real.sqrt 2 / 4)
      = Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2 := by
    field_simp
    ring
  rw [wfun]
  rw [hval] at hcos3
  calc Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2
      = (2 / Real.pi * θ) ^ 2 * (Real.sqrt 2 / 4) := hexp.symm
    _ ≤ Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
        mul_le_mul hsin2 hcos3 (by positivity) (sq_nonneg _)

lemma Wge_right {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    4 * (Real.pi / 2 - θ) ^ 3 / Real.pi ^ 3 ≤ wfun θ := by
  set δ : ℝ := Real.pi / 2 - θ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith [hθ.2]
  have hδle : δ ≤ Real.pi / 2 := by rw [hδ]; linarith [hθ.1, Real.pi_pos]
  have hcos : Real.cos θ = Real.sin δ := by rw [hδ, Real.sin_pi_div_two_sub]
  have hs : 2 / Real.pi * δ ≤ Real.sin δ := Real.mul_le_sin hδpos.le hδle
  have hs2 : (1 / 2 : ℝ) ≤ Real.sin θ ^ 2 := by
    have h1 : Real.sqrt 2 / 2 ≤ Real.sin θ := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        hθ.2.le hθ.1
      rwa [Real.sin_pi_div_four] at h
    have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have h3 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.sin θ ^ 2 := by
      have h := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 2 / 2) h1
      simpa [pow_two] using h
    linarith [h2, h3]
  have hc3 : (2 / Real.pi * δ) ^ 3 ≤ Real.cos θ ^ 3 := by
    rw [hcos]
    exact pow_le_pow_left₀ (by positivity) hs 3
  have hexp : (1 / 2 : ℝ) * ((2 / Real.pi * δ) ^ 3) = 4 * δ ^ 3 / Real.pi ^ 3 := by
    rw [mul_pow]
    field_simp
    ring
  rw [wfun, ← hexp]
  exact mul_le_mul hs2 hc3 (by positivity) (sq_nonneg _)

lemma Wderiv {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt wfun
      (wfun θ * (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)) θ := by
  have hsne : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hcne : Real.cos θ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 2) (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).pow 2
  have hc : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
      (3 * Real.cos θ ^ (3 - 1) * (-Real.sin θ)) θ :=
    (Real.hasDerivAt_cos θ).pow 3
  have h := hs.mul hc
  have hfun : wfun = (fun t : ℝ => Real.sin t ^ 2) * (fun t : ℝ => Real.cos t ^ 3) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  have hs2ne : 2 * Real.sin θ * Real.cos θ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hsne) hcne
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
  simp only [Pi.mul_apply]
  field_simp
  have hc2 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hc4 : Real.cos θ ^ 4 = (1 - Real.sin θ ^ 2) ^ 2 := by
    rw [show Real.cos θ ^ 4 = (Real.cos θ ^ 2) ^ 2 by ring, hc2]
  rw [hc4, hc2]
  ring

lemma Wint1 {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ∫ t in (0 : ℝ)..θ, wfun t ≤ θ ^ 3 / 3 := by
  have hle : ∫ t in (0 : ℝ)..θ, wfun t ≤ ∫ t in (0 : ℝ)..θ, t ^ 2 := by
    refine intervalIntegral.integral_mono_on hθ.1 (continuous_wfun.intervalIntegrable 0 θ) ?_
      (fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => t ^ 2).intervalIntegrable 0 θ
    · have ht1 : t ≤ Real.pi / 2 := le_trans ht.2 hθ.2
      have hsin : Real.sin t ≤ t := Real.sin_le ht.1
      have hsinn : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_mem_Icc ⟨ht.1, by linarith [ht1, Real.pi_pos]⟩
      have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
      have hcosnn : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [ht1]⟩
      have hs2 : Real.sin t ^ 2 ≤ t ^ 2 := by nlinarith [hsin, hsinn, ht.1]
      have hc2 : Real.cos t ^ 2 ≤ 1 := by nlinarith [hcos1, hcosnn]
      have hc3 : Real.cos t ^ 3 ≤ 1 := by
        calc Real.cos t ^ 3 = Real.cos t ^ 2 * Real.cos t := by ring
          _ ≤ 1 * 1 := mul_le_mul hc2 hcos1 hcosnn (by norm_num)
          _ = 1 := by norm_num
      rw [wfun]
      have := mul_le_mul hs2 hc3 (by positivity) (sq_nonneg t)
      linarith
  have hftc : ∫ t in (0 : ℝ)..θ, t ^ 2 = θ ^ 3 / 3 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) θ,
        HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
      intro t ht
      have h := (hasDerivAt_id t).pow 3
      have h2 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) ((3 * t ^ (3 - 1) * 1) / 3) t :=
        h.div_const 3
      convert h2 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => t ^ 2).intervalIntegrable 0 θ)]
    ring
  linarith [hftc ▸ hle]

lemma Wint2 {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ∫ t in (0 : ℝ)..θ, wfun t / Real.sin (2 * t) ≤ θ ^ 2 / 4 := by
  have hcont1 : Continuous (fun t : ℝ => wfun t / Real.sin (2 * t)) := by
    have h : (fun t : ℝ => wfun t / Real.sin (2 * t))
        = fun t => Real.sin t * Real.cos t ^ 2 / 2 := by
      funext t; exact wfun_div_s2_eq t
    rw [h]; fun_prop
  have hle : ∫ t in (0 : ℝ)..θ, wfun t / Real.sin (2 * t) ≤ ∫ t in (0 : ℝ)..θ, t / 2 := by
    refine intervalIntegral.integral_mono_on hθ.1 (hcont1.intervalIntegrable 0 θ) ?_
      (fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => t / 2).intervalIntegrable 0 θ
    · rw [wfun_div_s2_eq]
      have ht1 : t ≤ Real.pi / 2 := le_trans ht.2 hθ.2
      have hsin : Real.sin t ≤ t := Real.sin_le ht.1
      have hsinn : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_mem_Icc ⟨ht.1, by linarith [ht1, Real.pi_pos]⟩
      have hcos : Real.cos t ^ 2 ≤ 1 := by
        nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.sin t)]
      have := mul_le_mul hsin hcos (sq_nonneg _) ht.1
      linarith
  have hftc : ∫ t in (0 : ℝ)..θ, t / 2 = θ ^ 2 / 4 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) θ,
        HasDerivAt (fun s : ℝ => s ^ 2 / 4) (t / 2) t := by
      intro t ht
      have h := (hasDerivAt_id t).pow 2
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 4) ((2 * t ^ (2 - 1) * 1) / 4) t :=
        h.div_const 4
      convert h2 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => t / 2).intervalIntegrable 0 θ)]
    ring
  linarith [hftc ▸ hle]

lemma Wint3 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∫ t in θ..(Real.pi / 2), wfun t ≤ (Real.pi / 2 - θ) ^ 4 / 4 := by
  have hle : ∫ t in θ..(Real.pi / 2), wfun t
      ≤ ∫ t in θ..(Real.pi / 2), (Real.pi / 2 - t) ^ 3 := by
    refine intervalIntegral.integral_mono_on hθ.2.le
      (continuous_wfun.intervalIntegrable θ (Real.pi / 2)) ?_
      (fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => (Real.pi / 2 - t) ^ 3).intervalIntegrable
        θ (Real.pi / 2)
    · have ht1 : t ≤ Real.pi / 2 := ht.2
      have hcos : Real.cos t ≤ Real.pi / 2 - t := by
        have h := Real.sin_le (show (0:ℝ) ≤ Real.pi / 2 - t by linarith)
        rwa [Real.sin_pi_div_two_sub] at h
      have hcosnn : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [Real.pi_pos, hθ.1, ht.1], by linarith [ht1]⟩
      have hs1 : Real.sin t ^ 2 ≤ 1 := by
        nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t)]
      have hδnn : 0 ≤ Real.pi / 2 - t := by linarith
      rw [wfun]
      have hcube : Real.cos t ^ 3 ≤ (Real.pi / 2 - t) ^ 3 := pow_le_pow_left₀ hcosnn hcos 3
      have := mul_le_mul hs1 hcube (by positivity) (by norm_num : (0:ℝ) ≤ 1)
      linarith
  have hftc : ∫ t in θ..(Real.pi / 2), (Real.pi / 2 - t) ^ 3 = (Real.pi / 2 - θ) ^ 4 / 4 := by
    have hd : ∀ t ∈ Set.uIcc θ (Real.pi / 2),
        HasDerivAt (fun s : ℝ => -(Real.pi / 2 - s) ^ 4 / 4) ((Real.pi / 2 - t) ^ 3) t := by
      intro t ht
      have hinner : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (Real.pi / 2)
      have h3 := hinner.pow 4
      have h4 : HasDerivAt (fun s : ℝ => -(Real.pi / 2 - s) ^ 4 / 4)
          (-(4 * (Real.pi / 2 - t) ^ (4 - 1) * (-1)) / 4) t := h3.neg.div_const 4
      convert h4 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => (Real.pi / 2 - t) ^ 3).intervalIntegrable
        θ (Real.pi / 2))]
    ring
  linarith [hftc ▸ hle]

lemma Wint4 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∫ t in θ..(Real.pi / 2), wfun t / Real.sin (2 * t) ≤ (Real.pi / 2 - θ) ^ 3 / 6 := by
  have hcont1 : Continuous (fun t : ℝ => wfun t / Real.sin (2 * t)) := by
    have h : (fun t : ℝ => wfun t / Real.sin (2 * t))
        = fun t => Real.sin t * Real.cos t ^ 2 / 2 := by
      funext t; exact wfun_div_s2_eq t
    rw [h]; fun_prop
  have hle : ∫ t in θ..(Real.pi / 2), wfun t / Real.sin (2 * t)
      ≤ ∫ t in θ..(Real.pi / 2), (Real.pi / 2 - t) ^ 2 / 2 := by
    refine intervalIntegral.integral_mono_on hθ.2.le
      (hcont1.intervalIntegrable θ (Real.pi / 2)) ?_
      (fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => (Real.pi / 2 - t) ^ 2 / 2).intervalIntegrable
        θ (Real.pi / 2)
    · rw [wfun_div_s2_eq]
      have ht1 : t ≤ Real.pi / 2 := ht.2
      have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
      have hcos : Real.cos t ≤ Real.pi / 2 - t := by
        have h := Real.sin_le (show (0:ℝ) ≤ Real.pi / 2 - t by linarith [ht.2])
        rwa [Real.sin_pi_div_two_sub] at h
      have hcosnn : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [Real.pi_pos, hθ.1, ht.1], by linarith [ht1]⟩
      have hδnn : 0 ≤ Real.pi / 2 - t := by linarith
      have hsq : Real.cos t ^ 2 ≤ (Real.pi / 2 - t) ^ 2 := by
        nlinarith [hcos, hcosnn, hδnn]
      have := mul_le_mul hsin1 hsq (by positivity) (by norm_num : (0:ℝ) ≤ 1)
      linarith
  have hftc : ∫ t in θ..(Real.pi / 2), (Real.pi / 2 - t) ^ 2 / 2 = (Real.pi / 2 - θ) ^ 3 / 6 := by
    have hd : ∀ t ∈ Set.uIcc θ (Real.pi / 2),
        HasDerivAt (fun s : ℝ => -(Real.pi / 2 - s) ^ 3 / 6) ((Real.pi / 2 - t) ^ 2 / 2) t := by
      intro t ht
      have hinner : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (Real.pi / 2)
      have h3 := hinner.pow 3
      have h4 : HasDerivAt (fun s : ℝ => -(Real.pi / 2 - s) ^ 3 / 6)
          (-(3 * (Real.pi / 2 - t) ^ (3 - 1) * (-1)) / 6) t := h3.neg.div_const 6
      convert h4 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => (Real.pi / 2 - t) ^ 2 / 2).intervalIntegrable
        θ (Real.pi / 2))]
    ring
  linarith [hftc ▸ hle]

end Work.FTS_StreamBdry.SB6.UprimeAux
