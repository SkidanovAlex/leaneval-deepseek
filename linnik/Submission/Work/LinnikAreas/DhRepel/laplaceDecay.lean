import Mathlib

namespace Work.LinnikAreas.DhRepel

open MeasureTheory Set

/-- If `f` is `C²` on `(0, x₀)` with bounded second derivative and continuous on `[0, x₀]`,
then its derivative `deriv f` is interval integrable on `(0, x₀)`.  (The point is that a bounded
second derivative makes `deriv f` Lipschitz, hence bounded on the interval.) -/
theorem deriv_intervalIntegrable {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hb : ∃ B : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    IntervalIntegrable (deriv f) MeasureTheory.volume (0:ℝ) x₀ := by
  obtain ⟨B, hB⟩ := hb
  have hiter : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hdiffg : DifferentiableOn ℝ (deriv f) (Set.Ioo 0 x₀) := by
    have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 x₀) :=
      hf2.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h1.differentiableOn (by norm_num)
  have hMVT : ∀ x ∈ Set.Ioo 0 x₀, ∀ y ∈ Set.Ioo 0 x₀,
      ‖deriv f y - deriv f x‖ ≤ B * ‖y - x‖ := by
    intro x hx y hy
    refine Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Ioo 0 x₀)
      ?_ ?_ (convex_Ioo (0:ℝ) x₀) hx hy
    · intro z hz; exact (hdiffg z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
    · intro z hz; rw [← hiter]; exact hB z hz
  set c : ℝ := x₀ / 2 with hc
  have hc_mem : c ∈ Set.Ioo 0 x₀ := ⟨by positivity, by rw [hc]; linarith⟩
  have hbound : ∀ t ∈ Set.Ioo 0 x₀, ‖deriv f t‖ ≤ ‖deriv f c‖ + max B 0 * x₀ := by
    intro t ht
    have h2 : ‖deriv f t - deriv f c‖ ≤ max B 0 * x₀ := by
      have hm := hMVT c hc_mem t ht
      have hmul : B * ‖t - c‖ ≤ max B 0 * ‖t - c‖ :=
        mul_le_mul_of_nonneg_right (le_max_left B 0) (norm_nonneg _)
      have htc : ‖t - c‖ ≤ x₀ := by
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · rw [hc]; linarith [ht.1]
        · rw [hc]; linarith [ht.2, hx₀]
      exact hm.trans (hmul.trans (mul_le_mul_of_nonneg_left htc (le_max_right B 0)))
    calc ‖deriv f t‖ = ‖(deriv f t - deriv f c) + deriv f c‖ := by ring_nf
      _ ≤ ‖deriv f t - deriv f c‖ + ‖deriv f c‖ := norm_add_le _ _
      _ ≤ max B 0 * x₀ + ‖deriv f c‖ := by linarith
      _ = ‖deriv f c‖ + max B 0 * x₀ := by ring
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx₀.le]
  refine IntegrableOn.of_bound ?_ ?_ (‖deriv f c‖ + max B 0 * x₀) ?_
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  · exact (aestronglyMeasurable_deriv f volume).mono_measure Measure.restrict_le_self
  · rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with x hx
    exact hbound x hx

/-- Integration by parts specialised to the Laplace integral: for `z ≠ 0`,
`∫₀^{x₀} e^{-zt} f t = f 0 / z + (1/z) ∫₀^{x₀} (deriv f) t · e^{-zt}`,
using `f x₀ = 0` and the one-sided integration-by-parts identity valid for functions that are
only differentiable on the open interval. -/
theorem laplace_ibp {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hdiff : ∀ x ∈ Set.Ioo 0 x₀, HasDerivAt f (deriv f x) x)
    (hint : IntervalIntegrable (deriv f) MeasureTheory.volume (0:ℝ) x₀)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) :
    ∀ z : ℂ, z ≠ 0 →
      ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t =
        f 0 / z + (1 / z) * ∫ t in (0:ℝ)..x₀, deriv f t * Complex.exp (-(z * (t : ℂ))) := by
  intro z hz
  have hle : (0:ℝ) ≤ x₀ := hx₀.le
  set v : ℝ → ℂ := fun t => (-(1/z)) * Complex.exp (-(z * (t:ℂ))) with hv
  set v' : ℝ → ℂ := fun t => Complex.exp (-(z * (t:ℂ))) with hv'
  have hvcont : ContinuousOn v (Set.uIcc 0 x₀) := by rw [hv]; fun_prop
  have hv'int : IntervalIntegrable v' volume (0:ℝ) x₀ := by
    rw [hv']
    exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(z*(t:ℂ))))).intervalIntegrable 0 x₀
  have hvderiv : ∀ x ∈ Set.Ioo (min (0:ℝ) x₀) (max (0:ℝ) x₀), HasDerivAt v (v' x) x := by
    intro x hx
    rw [hv, hv']
    have h1 : HasDerivAt (fun t : ℝ => z * (t:ℂ)) z x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul z
    have h2 : HasDerivAt (fun t : ℝ => -(z * (t:ℂ))) (-z) x := h1.neg
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (-(z * (t:ℂ))))
        (Complex.exp (-(z*(x:ℂ))) * (-z)) x := h2.cexp
    have h4 : HasDerivAt (fun t : ℝ => (-(1/z)) * Complex.exp (-(z*(t:ℂ))))
        ((-(1/z)) * (Complex.exp (-(z*(x:ℂ))) * (-z))) x := h3.const_mul (-(1/z))
    have hder : (-(1/z)) * (Complex.exp (-(z*(x:ℂ))) * (-z)) = Complex.exp (-(z*(x:ℂ))) := by
      field_simp
    rwa [hder] at h4
  have hcont' : ContinuousOn f (Set.uIcc 0 x₀) := by rw [Set.uIcc_of_le hle]; exact hcont
  have hdiff' : ∀ x ∈ Set.Ioo (min (0:ℝ) x₀) (max (0:ℝ) x₀), HasDerivAt f (deriv f x) x := by
    intro x hx
    rw [min_eq_left hle, max_eq_right hle] at hx
    exact hdiff x hx
  have hmain : ∫ x in (0:ℝ)..x₀, f x * v' x =
      f x₀ * v x₀ - f 0 * v 0 - ∫ x in (0:ℝ)..x₀, deriv f x * v x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcont' hvcont hdiff' hvderiv
      hint hv'int
  have hL : ∫ x in (0:ℝ)..x₀, Complex.exp (-(z*(x:ℂ))) * f x = ∫ x in (0:ℝ)..x₀, f x * v' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hv']; ring
  have hR : ∫ x in (0:ℝ)..x₀, deriv f x * v x
      = (-(1/z)) * ∫ x in (0:ℝ)..x₀, deriv f x * Complex.exp (-(z*(x:ℂ))) := by
    have hcong : ∫ x in (0:ℝ)..x₀, deriv f x * v x
        = ∫ x in (0:ℝ)..x₀, (-(1/z)) * (deriv f x * Complex.exp (-(z*(x:ℂ)))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [hv]; ring
    rw [hcong, intervalIntegral.integral_const_mul]
  have hv0 : v 0 = -(1/z) := by rw [hv]; simp [Complex.exp_zero]
  have hfx0 : f x₀ = 0 := hvan x₀ le_rfl
  rw [hL, hmain, hR, hfx0, hv0]
  ring

/-- **Decay of the Laplace transform.**  For `f` continuous on `[0, x₀]`, `C²` with bounded
second derivative on `(0, x₀)` and vanishing for `t ≥ x₀`, the Laplace integral
`∫₀^{x₀} e^{-zt} f t` tends to `0` as `‖z‖ → ∞` in the right half-plane `Re z ≥ 0`. -/
theorem laplaceDecay {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hb : ∃ B : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t‖ < ε := by
  intro ε hε
  have hle : (0:ℝ) ≤ x₀ := hx₀.le
  have hdiff : ∀ x ∈ Set.Ioo 0 x₀, HasDerivAt f (deriv f x) x := by
    intro x hx
    exact (hf2.differentiableOn (by norm_num) x hx).differentiableAt
      (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
  have hint : IntervalIntegrable (deriv f) volume (0:ℝ) x₀ := deriv_intervalIntegrable hx₀ hf2 hb
  set K : ℝ := ∫ t in (0:ℝ)..x₀, ‖deriv f t‖ with hK
  have hnormint : IntervalIntegrable (fun t => ‖deriv f t‖) volume (0:ℝ) x₀ := hint.norm
  have hKnn : 0 ≤ K := by
    rw [hK]; exact intervalIntegral.integral_nonneg hle (fun t ht => norm_nonneg _)
  set C : ℝ := ‖f 0‖ + K with hC
  have hCnn : 0 ≤ C := by rw [hC]; exact add_nonneg (norm_nonneg _) hKnn
  refine ⟨C / ε + 1, ?_⟩
  intro z hzre hzR
  have hRpos : 0 < C / ε + 1 := by positivity
  have hzn_pos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hzR
  have hzne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hzn_pos; exact lt_irrefl 0 hzn_pos
  have hibp := laplace_ibp hx₀ hcont hdiff hint hvan z hzne
  have hI2int : IntervalIntegrable (fun t => deriv f t * Complex.exp (-(z*(t:ℂ))))
      volume (0:ℝ) x₀ := hint.mul_continuousOn (by fun_prop)
  have hb1 : ‖f 0 / z‖ ≤ ‖f 0‖ / ‖z‖ := by rw [norm_div]
  have hb2 : ‖(1/z) * ∫ t in (0:ℝ)..x₀, deriv f t * Complex.exp (-(z*(t:ℂ)))‖
      ≤ (1/‖z‖) * K := by
    rw [norm_mul]
    have h1z : ‖(1:ℂ)/z‖ = 1/‖z‖ := by rw [norm_div, norm_one]
    rw [h1z]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖∫ t in (0:ℝ)..x₀, deriv f t * Complex.exp (-(z*(t:ℂ)))‖
        ≤ ∫ t in (0:ℝ)..x₀, ‖deriv f t * Complex.exp (-(z*(t:ℂ)))‖ :=
          intervalIntegral.norm_integral_le_integral_norm hle
      _ ≤ ∫ t in (0:ℝ)..x₀, ‖deriv f t‖ := by
          refine intervalIntegral.integral_mono_on hle hI2int.norm hnormint ?_
          intro t ht
          rw [norm_mul]
          refine mul_le_of_le_one_right (norm_nonneg _) ?_
          rw [Complex.norm_exp]
          refine Real.exp_le_one_iff.mpr ?_
          have hzt : (-(z*(t:ℂ))).re = -(z.re * t) := by
            simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          rw [hzt]
          nlinarith [hzre, ht.1]
      _ = K := by rw [hK]
  rw [hibp]
  calc ‖f 0 / z + (1/z) * ∫ t in (0:ℝ)..x₀, deriv f t * Complex.exp (-(z*(t:ℂ)))‖
      ≤ ‖f 0 / z‖ + ‖(1/z) * ∫ t in (0:ℝ)..x₀, deriv f t * Complex.exp (-(z*(t:ℂ)))‖ :=
        norm_add_le _ _
    _ ≤ ‖f 0‖/‖z‖ + (1/‖z‖)*K := add_le_add hb1 hb2
    _ = C / ‖z‖ := by rw [hC]; field_simp
    _ < ε := by
        have hCz : C / ‖z‖ ≤ C / (C/ε + 1) := div_le_div_of_nonneg_left hCnn hRpos hzR
        have hlt : C / (C/ε + 1) < ε := by
          rw [div_lt_iff₀ hRpos]
          have hval : ε * (C/ε + 1) = C + ε := by field_simp
          rw [hval]; linarith
        exact lt_of_le_of_lt hCz hlt

end Work.LinnikAreas.DhRepel
