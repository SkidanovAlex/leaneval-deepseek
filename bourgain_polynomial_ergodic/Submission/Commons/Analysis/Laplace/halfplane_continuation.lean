import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

namespace Commons.Analysis.Laplace

open MeasureTheory
open scoped Topology ComplexConjugate

/-! ### Elementary facts about a function vanishing on `(-∞,0]` and monotone on `[0,∞)` -/

lemma monotone_of_vanishing_monotoneOn_Ici {U : ℝ → ℝ} (hU0 : ∀ t : ℝ, t ≤ 0 → U t = 0)
    (hUmono : MonotoneOn U (Set.Ici 0)) : Monotone U := by
  intro a b hab
  rcases le_or_gt b 0 with hb | hb
  · rw [hU0 a (hab.trans hb), hU0 b hb]
  rcases lt_or_ge a 0 with ha | ha
  · have h0b : U 0 ≤ U b := hUmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hb.le) hb.le
    rw [hU0 a ha.le]
    rwa [hU0 0 le_rfl] at h0b
  · exact hUmono (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab

lemma nonneg_of_vanishing_monotoneOn_Ici {U : ℝ → ℝ} (hU0 : ∀ t : ℝ, t ≤ 0 → U t = 0)
    (hUmono : MonotoneOn U (Set.Ici 0)) : ∀ t : ℝ, 0 ≤ t → 0 ≤ U t := by
  intro t ht
  have h := (monotone_of_vanishing_monotoneOn_Ici hU0 hUmono) ht
  rwa [hU0 0 le_rfl] at h

/-- For `δ > 0` and `t ≥ 0`, `|t| e^{-δt} ≤ 1/δ`. -/
lemma abs_mul_exp_neg_le_inv {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 ≤ t) :
    |t| * Real.exp (-δ * t) ≤ 1 / δ := by
  have h2 : δ * t ≤ Real.exp (δ * t) := by
    have := Real.add_one_le_exp (δ * t); linarith
  have h3 : (δ * t) * Real.exp (-(δ * t)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(δ * t))).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have h4 : t * Real.exp (-(δ * t)) ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith [h3]
  rw [show -δ * t = -(δ * t) by ring]
  rcases eq_or_lt_of_le ht with h | h
  · subst h; simp only [abs_zero, zero_mul]; exact (div_pos one_pos hδ).le
  · rw [abs_of_pos h]; exact h4

lemma norm_ofReal_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

lemma norm_exp_neg_mul (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-(z * (t:ℂ)))‖ = Real.exp (-z.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- `(σ : ℂ) ^ (-(α+1))` for real `σ ≥ 0` equals the real power. -/
lemma cpow_neg_succ_ofReal {σ : ℝ} (hσ : 0 ≤ σ) (α : ℝ) :
    (σ : ℂ) ^ (-(α + 1 : ℂ)) = ((σ ^ (-(α + 1)) : ℝ) : ℂ) := by
  rw [show -(α + 1 : ℂ) = -(((α + 1 : ℝ)) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_neg]
  exact (Complex.ofReal_cpow hσ (-(α + 1))).symm

lemma re_mul_cpow_neg_succ (z : ℂ) {σ : ℝ} (hσ : 0 < σ) (α : ℝ) :
    (z * (σ : ℂ) ^ (-(α + 1 : ℂ))).re = z.re * σ ^ (-(α + 1)) := by
  rw [cpow_neg_succ_ofReal hσ.le α, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- **Integrability is forced.** Under the hypothesis that the real Laplace transform of `U`
equals `Re (H(1+σ) σ^{-(α+1)})` for every real `σ > 0`, the function `t ↦ e^{-σt} U t` is
integrable for every `σ > 0`. -/
lemma integrableOn_exp_mul_of_laplace_eq {U : ℝ → ℝ}
    (hU0 : ∀ t : ℝ, t ≤ 0 → U t = 0) (hUmono : MonotoneOn U (Set.Ici 0))
    {H : ℂ → ℂ} {α c : ℝ} (hHan : AnalyticOnNhd ℂ H {s : ℂ | 1 ≤ s.re})
    (hH1 : H 1 = (c : ℂ)) (hc : 0 < c)
    (hL : ∀ σ : ℝ, 0 < σ →
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-σ * t) * U t : ℝ)
        = (H (1 + σ) * (σ : ℂ) ^ (-(α + 1 : ℂ))).re) :
    ∀ σ : ℝ, 0 < σ → IntegrableOn (fun t : ℝ => Real.exp (-σ * t) * U t) (Set.Ioi 0) := by
  have hUmono' := monotone_of_vanishing_monotoneOn_Ici hU0 hUmono
  have hUnn := nonneg_of_vanishing_monotoneOn_Ici hU0 hUmono
  have hUmeas : Measurable U := hUmono'.measurable
  intro σ hσ
  by_contra hni
  have hzero : ∀ σ' : ℝ, σ' ∈ Set.Ioc 0 σ → (H (1 + (σ' : ℂ))).re = 0 := by
    intro σ' hσ'
    have hσ'pos : 0 < σ' := hσ'.1
    have hni' : ¬ IntegrableOn (fun t : ℝ => Real.exp (-σ' * t) * U t) (Set.Ioi 0) := by
      intro h
      apply hni
      refine h.mono' ?_ ?_
      · exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-σ * t)).aestronglyMeasurable).mul
          hUmeas.aestronglyMeasurable
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
        have ht0 : 0 ≤ t := le_of_lt ht
        have hUt : 0 ≤ U t := hUnn t ht0
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hUt)]
        refine mul_le_mul_of_nonneg_right ?_ hUt
        have h1 : σ' * t ≤ σ * t := mul_le_mul_of_nonneg_right hσ'.2 ht0
        rw [Real.exp_le_exp]
        linarith
    have h0 : (∫ t in Set.Ioi (0:ℝ), Real.exp (-σ' * t) * U t : ℝ) = 0 := integral_undef hni'
    have hh := hL σ' hσ'pos
    rw [h0] at hh
    rw [re_mul_cpow_neg_succ _ hσ'pos α] at hh
    have hpos : 0 < σ' ^ (-(α + 1)) := Real.rpow_pos_of_pos hσ'pos _
    exact (mul_eq_zero.mp hh.symm).resolve_right (ne_of_gt hpos)
  have hcontAt : ContinuousAt (fun σ' : ℝ => (H (1 + (σ' : ℂ))).re) 0 := by
    have h1 : ContinuousAt H ((1:ℂ) + ((0:ℝ):ℂ)) := by simpa using (hHan 1 (by simp)).continuousAt
    have h2 : ContinuousAt (fun σ' : ℝ => (1 : ℂ) + (σ' : ℂ)) 0 := by fun_prop
    have h3 : ContinuousAt (fun σ' : ℝ => H (1 + (σ' : ℂ))) 0 :=
      ContinuousAt.comp (g := H) (f := fun σ' : ℝ => (1:ℂ) + (σ' : ℂ)) (x := (0:ℝ)) h1 h2
    exact ContinuousAt.comp (g := Complex.re) (f := fun σ' : ℝ => H (1 + (σ' : ℂ)))
      (x := (0:ℝ)) Complex.continuous_re.continuousAt h3
  have htend : Filter.Tendsto (fun σ' : ℝ => (H (1 + (σ' : ℂ))).re) (𝓝[>] (0:ℝ))
      (𝓝 ((H 1).re)) := by
    have := hcontAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
    simpa using this
  have hfeq : (fun σ' : ℝ => (H (1 + (σ' : ℂ))).re) =ᶠ[𝓝[>] (0:ℝ)] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioc_mem_nhdsGT hσ] with σ' hσ'
    exact hzero σ' hσ'
  have hzero_tend : Filter.Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 ((H 1).re)) :=
    Filter.Tendsto.congr' hfeq htend
  have hc0 : (H 1).re = 0 := tendsto_nhds_unique hzero_tend tendsto_const_nhds
  rw [hH1, Complex.ofReal_re] at hc0
  exact absurd hc0 (ne_of_gt hc)

/-- Differentiation under the integral sign for the complex Laplace transform. -/
lemma hasDerivAt_laplaceIntegral {U : ℝ → ℝ} (hUm : Measurable U)
    (hUpo : ∀ t : ℝ, 0 ≤ t → 0 ≤ U t)
    (hint : ∀ σ : ℝ, 0 < σ → IntegrableOn (fun t : ℝ => Real.exp (-σ * t) * U t) (Set.Ioi 0))
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ => ∫ t in Set.Ioi (0:ℝ), Complex.exp (-(w * (t:ℂ))) * (U t : ℂ))
      (∫ t in Set.Ioi (0:ℝ), Complex.exp (-(z * (t:ℂ))) * (-(t:ℂ)) * (U t : ℂ)) z := by
  have hδ : 0 < z.re / 4 := by linarith
  have hboundInt : Integrable (fun t : ℝ => Real.exp (-(z.re/4) * t) * U t)
      (volume.restrict (Set.Ioi (0:ℝ))) := hint (z.re/4) hδ
  have hUmeas : AEStronglyMeasurable (fun t : ℝ => (U t : ℂ)) (volume.restrict (Set.Ioi (0:ℝ))) :=
    (Complex.measurable_ofReal.comp hUm).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0:ℝ)))
    (bound := fun t : ℝ => |t| * Real.exp (-(z.re/2) * t) * U t)
    (F := fun w : ℂ => fun t : ℝ => Complex.exp (-(w * (t:ℂ))) * (U t : ℂ))
    (F' := fun w : ℂ => fun t : ℝ => Complex.exp (-(w * (t:ℂ))) * (-(t:ℂ)) * (U t : ℂ))
    (x₀ := z) (s := Metric.ball z (z.re/2))
    (Metric.ball_mem_nhds z (half_pos hz)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun w =>
      (((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(w * (t:ℂ)))).aestronglyMeasurable).mul
        hUmeas)
  · have hmeas : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(z * (t:ℂ))) * (U t:ℂ))
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      (((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(z * (t:ℂ)))).aestronglyMeasurable).mul
        hUmeas)
    refine (integrable_norm_iff hmeas).mp ?_
    refine (hint z.re hz).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [norm_mul, norm_exp_neg_mul z t, norm_ofReal_abs, abs_of_nonneg (hUpo t ht.le)]
  · exact (((by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-(z * (t:ℂ))) * (-(t:ℂ))).aestronglyMeasurable).mul hUmeas)
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht w hw
    have ht0 : 0 ≤ t := le_of_lt ht
    have hUt : 0 ≤ U t := hUpo t ht0
    have hdist : ‖w - z‖ < z.re / 2 := by
      have := Metric.mem_ball.mp hw
      rwa [Complex.dist_eq] at this
    have hre : z.re / 2 < w.re := by
      have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
        simpa using Complex.abs_re_le_norm (w - z)
      linarith [neg_abs_le (w.re - z.re)]
    have hexp : Real.exp (-(w.re * t)) ≤ Real.exp (-(z.re/2) * t) := by
      rw [Real.exp_le_exp]; nlinarith [hre, ht0]
    have hnorm : ‖Complex.exp (-(w * (t:ℂ))) * (-(t:ℂ)) * (U t : ℂ)‖
        = Real.exp (-(w.re * t)) * |t| * U t := by
      rw [norm_mul, norm_mul, norm_exp_neg_mul, norm_neg, norm_ofReal_abs, norm_ofReal_abs,
        abs_of_nonneg hUt]
      rw [show Real.exp (-w.re * t) = Real.exp (-(w.re * t)) by congr 1; ring]
    rw [hnorm]
    calc Real.exp (-(w.re * t)) * |t| * U t
        = |t| * Real.exp (-(w.re * t)) * U t := by ring
      _ ≤ |t| * Real.exp (-(z.re/2) * t) * U t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (abs_nonneg t)) hUt
  · refine Integrable.mono' (hboundInt.const_mul (4 / z.re)) ?_ ?_
    · exact ((by fun_prop : Continuous fun t : ℝ =>
        |t| * Real.exp (-(z.re/2) * t)).aestronglyMeasurable).mul hUm.aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      have hUt : 0 ≤ U t := hUpo t ht0
      have hb1 : |t| * Real.exp (-(z.re/4) * t) ≤ 1 / (z.re/4) := abs_mul_exp_neg_le_inv hδ ht0
      have hb2 : 0 ≤ Real.exp (-(z.re/4) * t) * U t :=
        mul_nonneg (Real.exp_pos _).le hUt
      have hexp' : Real.exp (-(z.re/2) * t)
          = Real.exp (-(z.re/4) * t) * Real.exp (-(z.re/4) * t) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [Real.norm_eq_abs]
      have hb0 : 0 ≤ |t| * Real.exp (-(z.re/2) * t) * U t :=
        mul_nonneg (mul_nonneg (abs_nonneg t) (Real.exp_pos _).le) hUt
      rw [abs_of_nonneg hb0]
      calc |t| * Real.exp (-(z.re/2) * t) * U t
          = (|t| * Real.exp (-(z.re/4) * t)) * (Real.exp (-(z.re/4) * t) * U t) := by
              rw [hexp']; ring
        _ ≤ (1 / (z.re/4)) * (Real.exp (-(z.re/4) * t) * U t) :=
              mul_le_mul_of_nonneg_right hb1 hb2
        _ = (4 / z.re) * (Real.exp (-(z.re/4) * t) * U t) := by rw [one_div_div]
  · filter_upwards with t w hw
    have h1 : HasDerivAt (fun w : ℂ => -(w * (t:ℂ))) (-(t:ℂ)) w := by
      have hh := (hasDerivAt_id (w : ℂ)).mul_const (-(t:ℂ))
      simpa [mul_neg] using hh
    exact h1.cexp.mul_const (U t : ℂ)

/-- The complex Laplace transform is analytic on the open right half-plane. -/
lemma analyticOnNhd_laplaceIntegral {U : ℝ → ℝ} (hUm : Measurable U)
    (hUpo : ∀ t : ℝ, 0 ≤ t → 0 ≤ U t)
    (hint : ∀ σ : ℝ, 0 < σ → IntegrableOn (fun t : ℝ => Real.exp (-σ * t) * U t) (Set.Ioi 0)) :
    AnalyticOnNhd ℂ (fun w : ℂ => ∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-(w * (t : ℂ))) * (U t : ℂ)) {z : ℂ | 0 < z.re} := by
  rw [Complex.analyticOnNhd_iff_differentiableOn (isOpen_lt continuous_const Complex.continuous_re)]
  exact fun z hz => (hasDerivAt_laplaceIntegral hUm hUpo hint hz).differentiableAt.differentiableWithinAt

/-- The "real-part extension" of `H` is differentiable on a neighbourhood of every point of the
closed right half-plane, whenever `H` is analytic on a neighbourhood of `{1 ≤ Re}`. -/
lemma differentiableAt_rePart_eventually {H : ℂ → ℂ}
    (hHan : AnalyticOnNhd ℂ H {s : ℂ | 1 ≤ s.re}) {z : ℂ} (hz : 0 ≤ z.re) :
    ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ
      (fun w : ℂ => (H (1 + w) + conj (H (1 + conj w))) / 2) w := by
  have hVopen : IsOpen {v : ℂ | AnalyticAt ℂ H v} := isOpen_analyticAt ℂ H
  have hz1 : AnalyticAt ℂ H (1 + z) := hHan (1 + z) (by simp [Complex.add_re, hz])
  have hz2 : AnalyticAt ℂ H (1 + conj z) := hHan (1 + conj z) (by simp [Complex.add_re, hz])
  have hcont1 : Continuous fun w : ℂ => (1:ℂ) + w := by fun_prop
  have hcont2 : Continuous fun w : ℂ => (1:ℂ) + conj w := by fun_prop
  have hev1 : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ H (1 + w) :=
    (hVopen.preimage hcont1).mem_nhds (by simpa using hz1)
  have hev2 : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ H (1 + conj w) :=
    (hVopen.preimage hcont2).mem_nhds (by simpa using hz2)
  filter_upwards [hev1, hev2] with w hw1 hw2
  have hG : DifferentiableAt ℂ (fun v : ℂ => H (1 + v)) w :=
    (hw1.differentiableAt).comp w (by fun_prop)
  have hGc : DifferentiableAt ℂ (fun v : ℂ => H (1 + v)) (conj w) :=
    (hw2.differentiableAt).comp (conj w) (by fun_prop)
  have hR : DifferentiableAt ℂ (fun w : ℂ => conj (H (1 + conj w))) w := by
    simpa [Function.comp_def] using hGc.conj_conj
  exact (hG.add hR).div_const 2

/-- The closed right half-plane is preconnected. -/
lemma isPreconnected_re_nonneg : IsPreconnected {z : ℂ | 0 < z.re} := by
  have hconv : Convex ℝ {z : ℂ | 0 < z.re} := by
    have h : {z : ℂ | 0 < z.re} = Complex.reCLM ⁻¹' Set.Ioi (0:ℝ) := rfl
    rw [h]
    exact (convex_Ioi (0:ℝ)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  exact hconv.isPreconnected

/-- **Half-plane continuation of the Laplace-transform hypothesis.**
Let `U : ℝ → ℝ` vanish on `(-∞,0]` and be nondecreasing on `[0,∞)`, and let `H` be analytic and
bounded on `{Re s ≥ 1}` with `H 1 = c > 0`, and suppose
`∫_0^∞ e^{-σt} U t dt = Re (H(1+σ) σ^{-(α+1)})` for every real `σ > 0`.
Then there is `Ĥ`, analytic and bounded on the closed right half-plane, with `Ĥ 0 = c`,
`Ĥ σ = Re H(1+σ)` for real `σ > 0`, and realizing the complex Laplace transform
`∫_0^∞ e^{-zt} U t dt = Ĥ z · z^{-(α+1)}` for every `z` with `0 < z.re`.

Suggested route: `w ↦ (H(1+w) + conj (H(1+conj w)))/2` is holomorphic on a neighbourhood of the
closed half-plane and agrees with `Re H(1+σ)` on the positive real axis; both it and the (locally
uniformly convergent) complex Laplace transform are holomorphic on `{0 < z.re}`, and they agree on
the positive real axis, so they agree on `{0 < z.re}` by analytic continuation. -/
theorem halfplane_continuation {U : ℝ → ℝ} (hU0 : ∀ t : ℝ, t ≤ 0 → U t = 0)
    (hUmono : MonotoneOn U (Set.Ici 0))
    {H : ℂ → ℂ} {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hHan : AnalyticOnNhd ℂ H {s : ℂ | 1 ≤ s.re}) (hHb : ∃ B : ℝ, ∀ s : ℂ, 1 ≤ s.re → ‖H s‖ ≤ B)
    (hH1 : H 1 = (c : ℂ))
    (hL : ∀ σ : ℝ, 0 < σ →
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-σ * t) * U t : ℝ)
        = (H (1 + σ) * (σ : ℂ) ^ (-(α + 1 : ℂ))).re) :
    ∃ Ĥ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ĥ {z : ℂ | 0 ≤ z.re} ∧
      (∃ B' : ℝ, ∀ z : ℂ, 0 ≤ z.re → ‖Ĥ z‖ ≤ B') ∧
      Ĥ 0 = (c : ℂ) ∧
      (∀ σ : ℝ, 0 < σ → Ĥ (σ : ℂ) = ((H (1 + σ)).re : ℂ)) ∧
      ∀ z : ℂ, 0 < z.re →
        (∫ t in Set.Ioi (0:ℝ), Complex.exp (-(z * (t:ℂ))) * (U t : ℂ))
          = Ĥ z * z ^ (-(α + 1 : ℂ)) := by
  have hαpos : 0 < α := hα
  have hUmono' := monotone_of_vanishing_monotoneOn_Ici hU0 hUmono
  have hUnn := nonneg_of_vanishing_monotoneOn_Ici hU0 hUmono
  have hUmeas : Measurable U := hUmono'.measurable
  have hInt := integrableOn_exp_mul_of_laplace_eq hU0 hUmono hHan hH1 hc hL
  set Ĥ : ℂ → ℂ := fun w => (H (1 + w) + conj (H (1 + conj w))) / 2 with hĤdef
  have hĤanalytic : AnalyticOnNhd ℂ Ĥ {z : ℂ | 0 ≤ z.re} := by
    intro z hz
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    rw [hĤdef]
    exact differentiableAt_rePart_eventually hHan hz
  have hĤbound : ∃ B' : ℝ, ∀ z : ℂ, 0 ≤ z.re → ‖Ĥ z‖ ≤ B' := by
    obtain ⟨B, hB⟩ := hHb
    refine ⟨B, fun z hz => ?_⟩
    rw [hĤdef]
    have h1 : ‖H (1 + z)‖ ≤ B := hB (1 + z) (by simp [Complex.add_re, hz])
    have h2 : ‖H (1 + conj z)‖ ≤ B := hB (1 + conj z) (by simp [Complex.add_re, hz])
    calc ‖(H (1 + z) + conj (H (1 + conj z))) / 2‖
        = ‖H (1 + z) + conj (H (1 + conj z))‖ / 2 := by rw [norm_div]; norm_num
      _ ≤ (‖H (1 + z)‖ + ‖conj (H (1 + conj z))‖) / 2 := by
            have := norm_add_le (H (1 + z)) (conj (H (1 + conj z)))
            linarith
      _ = (‖H (1 + z)‖ + ‖H (1 + conj z)‖) / 2 := by rw [Complex.norm_conj]
      _ ≤ (B + B) / 2 := by linarith
      _ = B := by ring
  have hĤ0 : Ĥ 0 = (c : ℂ) := by
    simp only [hĤdef]
    have h0 : H (1 + (0:ℂ)) = (c : ℂ) := by simpa using hH1
    have h1 : H (1 + conj (0:ℂ)) = (c : ℂ) := by rw [map_zero, add_zero]; exact hH1
    rw [h0, h1, Complex.conj_ofReal]
    ring
  have hĤreal : ∀ σ : ℝ, 0 < σ → Ĥ (σ : ℂ) = ((H (1 + σ)).re : ℂ) := by
    intro σ hσ
    simp only [hĤdef]
    rw [show conj ((σ : ℝ) : ℂ) = ((σ : ℝ) : ℂ) from Complex.conj_ofReal σ]
    rw [Complex.add_conj]
    rw [show ((2 * (H (1 + (σ:ℂ))).re : ℝ) : ℂ) = 2 * ((H (1 + (σ:ℂ))).re : ℂ) by
      push_cast; ring]
    ring
  refine ⟨Ĥ, hĤanalytic, hĤbound, hĤ0, hĤreal, ?_⟩
  -- real-axis agreement
  have hreal : ∀ σ : ℝ, 0 < σ →
      (∫ t in Set.Ioi (0:ℝ), Complex.exp (-((σ:ℂ) * (t:ℂ))) * (U t : ℂ))
        = Ĥ (σ:ℂ) * (σ:ℂ) ^ (-(α + 1 : ℂ)) := by
    intro σ hσ
    have hpt : (∫ t in Set.Ioi (0:ℝ), Complex.exp (-((σ:ℂ) * (t:ℂ))) * (U t : ℂ))
        = ∫ t in Set.Ioi (0:ℝ), ((Real.exp (-σ * t) * U t : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      have hcast : (-(↑σ * ↑t) : ℂ) = ↑(-σ * t) := by
        rw [Complex.ofReal_mul, Complex.ofReal_neg]; ring
      rw [hcast]
    have h1 : (∫ t in Set.Ioi (0:ℝ), Complex.exp (-((σ:ℂ) * (t:ℂ))) * (U t : ℂ))
        = ((∫ t in Set.Ioi (0:ℝ), Real.exp (-σ * t) * U t : ℝ) : ℂ) := by
      rw [hpt]
      exact integral_ofReal
    rw [h1, hL σ hσ, hĤreal σ hσ, re_mul_cpow_neg_succ (H (1 + σ)) hσ α,
      cpow_neg_succ_ofReal hσ.le α, Complex.ofReal_mul]
  -- analytic continuation
  have hf_an : AnalyticOnNhd ℂ
      (fun z : ℂ => ∫ t in Set.Ioi (0:ℝ), Complex.exp (-(z * (t:ℂ))) * (U t : ℂ))
      {z : ℂ | 0 < z.re} := analyticOnNhd_laplaceIntegral hUmeas hUnn hInt
  have hg_an : AnalyticOnNhd ℂ (fun z : ℂ => Ĥ z * z ^ (-(α + 1 : ℂ))) {z : ℂ | 0 < z.re} := by
    refine (hĤanalytic.mono ?_).mul ?_
    · exact fun z hz => show (0:ℝ) ≤ z.re from le_of_lt hz
    · refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
      intro z hz
      have hzslit : z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        exact Or.inl hz
      exact (DifferentiableAt.cpow_const differentiableAt_id hzslit).differentiableWithinAt
  have hclosure : (1:ℂ) ∈ closure
      ({z : ℂ | (∫ t in Set.Ioi (0:ℝ), Complex.exp (-(z * (t:ℂ))) * (U t : ℂ))
        = Ĥ z * z ^ (-(α + 1 : ℂ))} \ {(1:ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((1 + ε/2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · exact hreal (1 + ε/2) (by linarith)
    · intro h
      have h' : (1 + ε/2 : ℝ) = 1 := by
        refine Complex.ofReal_injective ?_
        simpa using h
      linarith
    · rw [Complex.dist_eq]
      have hc' : (1:ℂ) - ((1 + ε/2 : ℝ) : ℂ) = ((-(ε/2) : ℝ) : ℂ) := by push_cast; ring
      rw [hc', norm_ofReal_abs, abs_of_neg (by linarith)]
      linarith
  have heqon := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure hf_an hg_an
    isPreconnected_re_nonneg (show (1:ℂ) ∈ {z : ℂ | 0 < z.re} by simp) hclosure
  intro z hz
  exact heqon hz

end Commons.Analysis.Laplace