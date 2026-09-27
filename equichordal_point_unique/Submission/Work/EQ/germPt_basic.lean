import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.GermSetup
import Submission.Work.EQ.germPt_of_real
import Submission.Work.EQ.tendsto_germPt_formula
import Submission.Work.EQ.continuousOn_germPt

/-! Basic local facts about the germ curve of the equichordal problem. -/

namespace Work.EQ

open Complex Metric Filter Set

/-! ## Helper lemmas -/

/-- The derivative of a holomorphic `h` at `0` along the real axis: writing
`h = ↑(h.re)` near `0`, the difference quotient `(h t).re / t` tends to `h'(0) = -1`. -/
lemma tendsto_re_div_of_hasDerivAt {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : HasDerivAt h (-1) 0) (h0 : h 0 = 0) (hreal : ∀ t : ℝ, |t| < r → (h t).im = 0) :
    Tendsto (fun t : ℝ => (h (t:ℂ)).re / t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (-1)) := by
  have hslope : Tendsto (slope h 0) (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) (nhds (-1 : ℂ)) :=
    hd.tendsto_slope
  have hcomp : Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhdsWithin ((0:ℂ)) {(0:ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => absurd (Complex.ofReal_eq_zero.mp h) (ne_of_gt ht)
  have h1 : Tendsto (fun t : ℝ => (slope h 0 (t:ℂ)).re) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (-1)) := by
    have hc := (Complex.continuous_re.tendsto (-1:ℂ)).comp (hslope.comp hcomp)
    have hneg : ((-1:ℂ)).re = (-1:ℝ) := by simp
    rw [hneg] at hc
    exact hc
  refine h1.congr' ?_
  filter_upwards [show Metric.ball (0:ℝ) r ∈ nhdsWithin (0:ℝ) (Ioi 0) from
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hr)] with t ht
  have ht' : |t| < r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; exact ht
  have him : (h (t:ℂ)).im = 0 := hreal t ht'
  have hh : h (t:ℂ) = ((h (t:ℂ)).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hs : slope h 0 (t:ℂ) = (t:ℂ)⁻¹ * ((h (t:ℂ)).re : ℂ) := by
    show ((t:ℂ) - 0)⁻¹ • (h (t:ℂ) - h 0) = (t:ℂ)⁻¹ * ((h (t:ℂ)).re : ℂ)
    rw [sub_zero, h0, sub_zero, smul_eq_mul, hh, Complex.ofReal_re]
  rw [hs]
  have key : (((h (t:ℂ)).re / t : ℝ) : ℂ) = (t:ℂ)⁻¹ * ((h (t:ℂ)).re : ℂ) := by
    rw [Complex.ofReal_div, div_eq_mul_inv, mul_comm]
  rw [← key, Complex.ofReal_re]

/-! ## The main statement -/

/-- Basic local facts about the germ curve: for the stable germ `h` (`h` analytic on `ball 0 r`,
`h 0 = 0`, `h' 0 = -1`, real on the real axis), the curve `t ↦ germPt a h t` is continuous on
`(0,ε)`, lies in the open upper half plane there, and converges to `A₁ = -1/2` as `t → 0⁺`. -/
theorem germPt_basic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ε : ℝ, 0 < ε ∧ ContinuousOn (germPt a h) (Set.Ioo 0 ε) ∧
      (∀ t, 0 < t → t < ε → 0 < (germPt a h t).im) ∧
      Filter.Tendsto (germPt a h) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((-(1/2) : ℝ) : ℂ)) := by
  obtain ⟨hr, han, h0, hderiv, hreal, _hFE⟩ := hh
  have hp : 0 < eqLam a := eqLam_pos ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one ha0 ha1
  have hne0 : eqLam a ≠ 0 := ne_of_gt hp
  have h1m : 0 < 1 - eqLam a := by linarith
  have hAn : AnalyticAt ℂ h 0 := han 0 (by rw [Metric.mem_ball, dist_self]; exact hr)
  have hd : HasDerivAt h (-1) 0 := by
    have h1 := hAn.differentiableAt.hasDerivAt
    rwa [hderiv] at h1
  -- the two real difference quotients
  set A : ℝ → ℝ := fun t => (h (t:ℂ)).re / t with hAdef
  set Bc : ℝ → ℝ := fun t => (h ((eqLam a : ℂ) * t)).re / t with hBcdef
  have hA : Tendsto A (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (-1)) := by
    rw [hAdef]
    exact tendsto_re_div_of_hasDerivAt hr hd h0 hreal
  have hshift : Tendsto (fun t : ℝ => eqLam a * t) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhdsWithin (0:ℝ) (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun t : ℝ => eqLam a * t) (nhds (0:ℝ)) (nhds (eqLam a * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hp ht
  have hBc : Tendsto Bc (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (-(eqLam a))) := by
    rw [hBcdef]
    have hcomp := hA.comp hshift
    have hmul := hcomp.const_mul (eqLam a)
    have htarget : eqLam a * (-1) = -(eqLam a) := by ring
    rw [htarget] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hstep : eqLam a * ((h (((eqLam a * t : ℝ) : ℂ))).re / (eqLam a * t)) =
        (h ((eqLam a : ℂ) * t)).re / t := by
      rw [Complex.ofReal_mul]
      have h2 : (eqLam a * t) ≠ 0 := mul_ne_zero hne0 (ne_of_gt ht)
      field_simp
    exact hstep
  -- basic eventual facts
  have hball : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), |t| < r ∧ |eqLam a * t| < r := by
    have hb : Metric.ball (0:ℝ) r ∈ nhdsWithin (0:ℝ) (Ioi 0) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hr)
    filter_upwards [hb] with t ht
    have ht' : |t| < r := by rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; exact ht
    refine ⟨ht', ?_⟩
    rw [abs_mul, abs_of_pos hp]
    nlinarith [abs_nonneg t]
  have hreal' : Filter.Eventually (fun t : ℝ =>
      (h (t:ℂ)).im = 0 ∧ (h ((eqLam a : ℂ) * t)).im = 0) (nhdsWithin (0:ℝ) (Ioi 0)) := by
    filter_upwards [hball] with t ht
    exact ⟨hreal t ht.1, by simpa [Complex.ofReal_mul] using hreal (eqLam a * t) ht.2⟩
  have hsign1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), A t < -1/2 :=
    hA.eventually_lt_const (by norm_num)
  have hsign2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), Bc t < -(eqLam a)/2 :=
    hBc.eventually_lt_const (show -(eqLam a) < -(eqLam a)/2 by linarith)
  have hsign3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), (1 - eqLam a)/2 < Bc t - A t := by
    have hsub := hBc.sub hA
    have htarget : -(eqLam a) - (-1) = 1 - eqLam a := by ring
    rw [htarget] at hsub
    have h := hsub.neg.eventually_lt_const
      (show -(1 - eqLam a) < -((1 - eqLam a)/2) by linarith)
    filter_upwards [h] with t ht
    linarith
  set P : ℝ → Prop := fun t => |t| < r ∧ |eqLam a * t| < r ∧ (h (t:ℂ)).im = 0 ∧
      (h ((eqLam a : ℂ) * t)).im = 0 ∧ A t < -1/2 ∧ Bc t < -(eqLam a)/2 ∧
      (1 - eqLam a)/2 < Bc t - A t with hP
  have hall : Filter.Eventually P (nhdsWithin (0:ℝ) (Ioi 0)) := by
    filter_upwards [hball, hreal', hsign1, hsign2, hsign3] with t h1 h2 h3 h4 h5
    rw [hP]
    exact ⟨h1.1, h1.2, h2.1, h2.2, h3, h4, h5⟩
  obtain ⟨ε, hε, hεP⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo 0 ε, P t := by
    obtain ⟨δ, hδ, hsub⟩ :=
      Metric.mem_nhdsWithin_iff.mp (show {t : ℝ | P t} ∈ nhdsWithin (0:ℝ) (Ioi 0) from hall)
    refine ⟨δ, hδ, fun t ht => hsub ⟨?_, ht.1⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2
  have hPu : ∀ t, P t → |t| < r ∧ |eqLam a * t| < r ∧ (h (t:ℂ)).im = 0 ∧
      (h ((eqLam a : ℂ) * t)).im = 0 ∧ A t < -1/2 ∧ Bc t < -(eqLam a)/2 ∧
      (1 - eqLam a)/2 < Bc t - A t := by
    intro t ht
    rw [hP] at ht
    exact ht
  have hIoo : Ioo (0:ℝ) ε ∈ nhdsWithin (0:ℝ) (Ioi 0) := by
    rw [Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hε, fun t ht => ?_⟩
    have htb : t ∈ Metric.ball (0:ℝ) ε := ht.1
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at htb
    exact ⟨ht.2, (abs_lt.mp htb).2⟩
  -- `A t = β/t`, `Bc t = γ/t` unfolding
  have hAt : ∀ t, A t = (h (t:ℂ)).re / t := by intro t; rw [hAdef]
  have hBct : ∀ t, Bc t = (h ((eqLam a : ℂ) * t)).re / t := by intro t; rw [hBcdef]
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · -- continuity
    refine continuousOn_germPt ?_ ?_
    · intro t ht
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hPu t (hεP t ht)
      exact ⟨(han (t:ℂ) (by simpa using h1)).continuousAt,
        (han ((eqLam a : ℂ) * t) (by simpa [Complex.ofReal_mul] using h2)).continuousAt⟩
    · intro t ht
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hPu t (hεP t ht)
      have hγβ : (h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re = t * (Bc t - A t) := by
        rw [hBct t, hAt t]
        have htne : t ≠ 0 := ne_of_gt ht.1
        field_simp
      have hJ : 0 < (h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re := by
        rw [hγβ]; exact mul_pos ht.1 (by linarith)
      intro hcon
      exact (sub_ne_zero.mp (ne_of_gt hJ)) (congrArg Complex.re hcon)
  · -- the germ curve lies in the upper half plane
    intro t ht0 htε
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hPu t (hεP t ⟨ht0, htε⟩)
    have htne : t ≠ 0 := ne_of_gt ht0
    have hJ : 0 < (h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re := by
      have hγβ : (h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re = t * (Bc t - A t) := by
        rw [hBct t, hAt t]; field_simp
      rw [hγβ]; exact mul_pos ht0 (by linarith)
    have hden : (h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re ≠ 0 := ne_of_gt hJ
    have hβ : (h (t:ℂ)).re < 0 := by
      have heq : (h (t:ℂ)).re = t * A t := by rw [hAt t]; field_simp
      rw [heq]; exact mul_neg_of_pos_of_neg ht0 (by linarith)
    have hγ : (h ((eqLam a : ℂ) * t)).re < 0 := by
      have heq : (h ((eqLam a : ℂ) * t)).re = t * Bc t := by rw [hBct t]; field_simp
      rw [heq]; exact mul_neg_of_pos_of_neg ht0 (by linarith)
    have hform := germPt_of_real (a := a) (h := h) (t := t) (β := (h (t:ℂ)).re)
      (γ := (h ((eqLam a : ℂ) * t)).re)
      (Complex.ext (by simp) (by simpa using h3)) (Complex.ext (by simp) (by simpa using h4)) hden
    have him : (germPt a h t).im = a * (h (t:ℂ)).re * (h ((eqLam a : ℂ) * t)).re /
        ((h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re) := by
      rw [hform]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
        zero_add]
    rw [him]
    exact div_pos (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ha0 hβ) hγ) hJ
  · -- the limit
    have hG := tendsto_germPt_formula (B := A) (C := Bc) ha0 ha1 hA hBc
    refine hG.congr' ?_
    filter_upwards [hIoo] with t htI
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hPu t (hεP t htI)
    have htne : t ≠ 0 := ne_of_gt htI.1
    have hJ : 0 < (h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re := by
      have hγβ : (h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re = t * (Bc t - A t) := by
        rw [hBct t, hAt t]; field_simp
      rw [hγβ]; exact mul_pos htI.1 (by linarith)
    have hden : (h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re ≠ 0 := ne_of_gt hJ
    have hform := germPt_of_real (a := a) (h := h) (t := t) (β := (h (t:ℂ)).re)
      (γ := (h ((eqLam a : ℂ) * t)).re)
      (Complex.ext (by simp) (by simpa using h3)) (Complex.ext (by simp) (by simpa using h4)) hden
    rw [hform]
    have hd : (h ((eqLam a : ℂ) * t)).re / t - (h (t:ℂ)).re / t ≠ 0 := by
      rw [div_sub_div_same]; exact div_ne_zero hden htne
    have e1 : a * Bc t / (Bc t - A t) - a / 2 =
        a * (h ((eqLam a : ℂ) * t)).re / ((h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re) -
          a / 2 := by
      simp only [hBct t, hAt t]
      field_simp
    have e2 : a * t * A t * Bc t / (Bc t - A t) =
        a * (h (t:ℂ)).re * (h ((eqLam a : ℂ) * t)).re /
          ((h ((eqLam a : ℂ) * t)).re - (h (t:ℂ)).re) := by
      simp only [hBct t, hAt t]
      field_simp
    rw [e1, e2]

end Work.EQ
