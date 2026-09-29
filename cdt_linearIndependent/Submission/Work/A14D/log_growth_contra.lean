import Mathlib

namespace Work.A14D

open Filter Complex
open scoped Topology

/-- Auxiliary contradiction: a real function equal to a bounded (continuously
convergent) expression eventually cannot equal `Real.log (t - 1)`, which tends
to `atBot` as `t → 1⁺`. -/
private lemma aux {u v : ℝ → ℝ} {a b : ℝ} (hb : b ≠ 0)
    (hu : Tendsto u (𝓝[>] (1 : ℝ)) (𝓝 a)) (hv : Tendsto v (𝓝[>] (1 : ℝ)) (𝓝 b))
    (hid : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), u t + 2 * v t * Real.log (t - 1) = 0) :
    False := by
  have hlne : NeBot (𝓝[>] (1 : ℝ)) := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  have hvne : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), v t ≠ 0 :=
    hv.eventually (isOpen_ne.mem_nhds hb)
  have hsub : Tendsto (fun t : ℝ => t - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hh : Tendsto (fun t : ℝ => t - 1) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
        have : Tendsto (fun t : ℝ => t - (1 : ℝ)) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
          tendsto_id.sub tendsto_const_nhds
        simpa using this
      exact hh.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (Set.mem_Ioi.mp ht)
  have hLatBot : Tendsto (fun t : ℝ => Real.log (t - 1)) (𝓝[>] (1 : ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hsub
  have hfin : Tendsto (fun t : ℝ => -(u t) / (2 * v t)) (𝓝[>] (1 : ℝ)) (𝓝 (-a / (2 * b))) := by
    have hnum : Tendsto (fun t : ℝ => -(u t)) (𝓝[>] (1 : ℝ)) (𝓝 (-a)) := hu.neg
    have hden : Tendsto (fun t : ℝ => 2 * v t) (𝓝[>] (1 : ℝ)) (𝓝 (2 * b)) :=
      hv.const_mul (2 : ℝ)
    have h2b : (2 * b : ℝ) ≠ 0 := by
      intro h; exact hb (by linarith)
    exact hnum.div hden h2b
  have hfin' : Tendsto (fun t : ℝ => Real.log (t - 1)) (𝓝[>] (1 : ℝ)) (𝓝 (-a / (2 * b))) := by
    refine (tendsto_congr' ?_).mpr hfin
    filter_upwards [hid, hvne] with t h1 h2
    have hv2 : (2 * v t : ℝ) ≠ 0 := mul_ne_zero two_ne_zero h2
    rw [eq_div_iff hv2]
    linarith
  have hfalse : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), False := by
    have hA : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), Real.log (t - 1) ≤ -a / (2 * b) - 1 :=
      (tendsto_atBot.mp hLatBot) (-a / (2 * b) - 1)
    have hB : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), -a / (2 * b) - 1 < Real.log (t - 1) :=
      hfin'.eventually (Ioi_mem_nhds (by linarith : -a / (2 * b) - 1 < -a / (2 * b)))
    filter_upwards [hA, hB] with t h1 h2
    linarith
  exact hlne.ne (eventually_false_iff_eq_bot.mp hfalse)

theorem log_growth_contra {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {e1 e2 : ℂ → ℂ}
    (he1 : DifferentiableOn ℂ e1 (Metric.ball (1 : ℂ) δ))
    (he2 : DifferentiableOn ℂ e2 (Metric.ball (1 : ℂ) δ)) (he2ne : e2 1 ≠ 0)
    (hid : ∀ t : ℝ, t ∈ Set.Ioo 1 (1 + ε) →
      e1 (t : ℂ) + 2 * e2 (t : ℂ) * (((Real.log (t - 1) : ℝ)) : ℂ) = 0) :
    False := by
  have hcont1 : ContinuousAt e1 (1 : ℂ) :=
    he1.continuousOn.continuousAt (Metric.ball_mem_nhds _ hδ)
  have hcont2 : ContinuousAt e2 (1 : ℂ) :=
    he2.continuousOn.continuousAt (Metric.ball_mem_nhds _ hδ)
  have hcast : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => e1 (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (e1 1)) :=
    hcont1.tendsto.comp hcast
  have h2 : Tendsto (fun t : ℝ => e2 (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (e2 1)) :=
    hcont2.tendsto.comp hcast
  have hevIoo : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), t ∈ Set.Ioo 1 (1 + ε) := by
    have hlt : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), t < 1 + ε :=
      IsOpen.mem_nhds isOpen_Iio (by show (1 : ℝ) < 1 + ε; linarith)
    filter_upwards [self_mem_nhdsWithin, hlt.filter_mono nhdsWithin_le_nhds] with t ht1 ht2
    exact ⟨Set.mem_Ioi.mp ht1, ht2⟩
  have hev_re : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
      (e1 (t : ℂ)).re + 2 * (e2 (t : ℂ)).re * Real.log (t - 1) = 0 := by
    filter_upwards [hevIoo] with t ht
    have h := congrArg Complex.re (hid t ht)
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_eq_add_neg,
      neg_zero, add_zero] at h
    exact h
  have hev_im : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
      (e1 (t : ℂ)).im + 2 * (e2 (t : ℂ)).im * Real.log (t - 1) = 0 := by
    filter_upwards [hevIoo] with t ht
    have h := congrArg Complex.im (hid t ht)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero,
      zero_add] at h
    exact h
  have hure : Tendsto (fun t : ℝ => (e1 (t : ℂ)).re) (𝓝[>] (1 : ℝ)) (𝓝 ((e1 1).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp h1
  have hvre : Tendsto (fun t : ℝ => (e2 (t : ℂ)).re) (𝓝[>] (1 : ℝ)) (𝓝 ((e2 1).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp h2
  have huim : Tendsto (fun t : ℝ => (e1 (t : ℂ)).im) (𝓝[>] (1 : ℝ)) (𝓝 ((e1 1).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp h1
  have hvim : Tendsto (fun t : ℝ => (e2 (t : ℂ)).im) (𝓝[>] (1 : ℝ)) (𝓝 ((e2 1).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp h2
  rcases eq_or_ne (e2 1).re 0 with hre | hre
  · refine aux (b := (e2 1).im) (a := (e1 1).im) ?_ huim hvim hev_im
    intro h
    exact he2ne (Complex.ext (by rw [hre, Complex.zero_re]) (by rw [h, Complex.zero_im]))
  · exact aux (b := (e2 1).re) (a := (e1 1).re) hre hure hvre hev_re

end Work.A14D
