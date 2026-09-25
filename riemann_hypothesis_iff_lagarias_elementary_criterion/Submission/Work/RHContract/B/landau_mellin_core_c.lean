import Mathlib

namespace Work.RHContract.B

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- For every `n` and `δ > 0` there is `C ≥ 0` with `(log x)^n ≤ C * x^δ` for all `x ≥ 1`. -/
private lemma log_pow_le_const_mul_rpow {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x)^n ≤ C * x^δ := by
  refine ⟨((n+1)/δ)^n, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp only [pow_zero, one_mul]; exact Real.one_le_rpow hx hδ.le
  · have hp : 0 < δ / (n+1) := by positivity
    have h1 : Real.log x ≤ x ^ (δ/(n+1)) * ((n+1)/δ) := by
      have h := Real.log_le_rpow_div hx0.le hp
      have : x ^ (δ/(n+1)) / (δ/(n+1)) = x ^ (δ/(n+1)) * ((n+1)/δ) := by
        rw [div_eq_mul_inv, inv_div]
      linarith [h, this.le, this.ge]
    have h2 : 0 ≤ Real.log x := Real.log_nonneg hx
    have h3 : (x ^ (δ/(n+1)))^n = x ^ (δ/(n+1) * (n:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    calc (Real.log x)^n ≤ (x ^ (δ/(n+1)) * ((n+1)/δ))^n := pow_le_pow_left₀ h2 h1 n
      _ = ((n+1)/δ)^n * (x ^ (δ/(n+1)))^n := by rw [mul_pow]; ring
      _ = ((n+1)/δ)^n * x ^ (δ/(n+1) * (n:ℝ)) := by rw [h3]
      _ ≤ ((n+1)/δ)^n * x^δ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le hx
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith

/-- The moments `∫ h x * x^{-s₀-1} * (log x)^n` are finite (integrable) whenever the Mellin
integral converges for some exponent `> c`. -/
private lemma moment_integrable
    (f : ℝ → ℝ) (x₀ s₀ c : ℝ) (hx₀ : 1 ≤ x₀)
    (hmeas : Measurable f)
    (hnonneg : ∀ x : ℝ, x₀ ≤ x → 0 ≤ f x)
    (hconv : ∀ a : ℝ, c < a → IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioi x₀))
    (hs₀ : c < s₀) :
    ∀ n : ℕ, IntegrableOn (fun x : ℝ => f x * x ^ (-s₀ - 1) * (Real.log x)^n) (Set.Ioi x₀) := by
  intro n
  set a : ℝ := (s₀ + c)/2 with ha
  have ha_gt : c < a := by rw [ha]; linarith
  have hδpos : 0 < s₀ - a := by rw [ha]; linarith
  obtain ⟨C, hC0, hC⟩ := log_pow_le_const_mul_rpow hδpos n
  have hint := hconv a ha_gt
  refine Integrable.mono' (hint.const_mul C) ?_ ?_
  · have hmg : Measurable (fun x : ℝ => f x * x ^ (-s₀ - 1) * (Real.log x)^n) :=
      (hmeas.mul (by fun_prop)).mul (Real.measurable_log.pow_const n)
    exact hmg.aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : (1:ℝ) ≤ x := le_trans hx₀ hx.le
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hg_nn : 0 ≤ f x * x ^ (-s₀ - 1) * (Real.log x)^n :=
      mul_nonneg (mul_nonneg (hnonneg x hx.le) (Real.rpow_nonneg hx0.le _))
        (pow_nonneg (Real.log_nonneg hx1) n)
    rw [Real.norm_of_nonneg hg_nn]
    have hbound : (Real.log x)^n ≤ C * x^(s₀ - a) := hC x hx1
    have hxa : x ^ (-s₀ - 1) * x ^ (s₀ - a) = x ^ (-a - 1) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    calc f x * x ^ (-s₀ - 1) * (Real.log x)^n
        ≤ f x * x ^ (-s₀ - 1) * (C * x^(s₀ - a)) := by
          apply mul_le_mul_of_nonneg_left hbound
          exact mul_nonneg (hnonneg x hx.le) (Real.rpow_nonneg hx0.le _)
      _ = C * (f x * x ^ (-a - 1)) := by
          rw [show f x * x ^ (-s₀-1) * (C * x^(s₀-a))
              = C * (f x * (x ^ (-s₀-1) * x^(s₀-a))) by ring, hxa]

/-- Power-series expansion of the Mellin integral at a real point `s₀ > c`, valid in the disc
`‖z‖ < s₀ - c`. -/
private lemma mellin_expansion
    (f : ℝ → ℝ) (x₀ s₀ c : ℝ) (hx₀ : 1 ≤ x₀)
    (hmeas : Measurable f)
    (hnonneg : ∀ x : ℝ, x₀ ≤ x → 0 ≤ f x)
    (hconv : ∀ a : ℝ, c < a → IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioi x₀))
    (hs₀ : c < s₀)
    (z : ℂ) (hz : ‖z‖ < s₀ - c) :
    HasSum (fun n : ℕ =>
        (((∫ x in Set.Ioi x₀, f x * x ^ (-s₀ - 1) * (Real.log x)^n) : ℝ) : ℂ)
          * (-z)^n * (Nat.factorial n : ℂ)⁻¹)
      (∫ x in Set.Ioi x₀, (f x : ℂ) * (x : ℂ) ^ (-(s₀:ℂ) - z - 1)) := by
  have hmom := moment_integrable f x₀ s₀ c hx₀ hmeas hnonneg hconv hs₀
  let F : ℕ → ℝ → ℂ := fun n x =>
    ((f x * x ^ (-s₀ - 1) * (Real.log x)^n : ℝ) : ℂ) * ((-z)^n * (Nat.factorial n : ℂ)⁻¹)
  let bound : ℕ → ℝ → ℝ := fun n x =>
    f x * x ^ (-s₀ - 1) * (Real.log x)^n * (‖z‖^n * (Nat.factorial n : ℝ)⁻¹)
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.Ioi x₀)) := by
    intro n
    have hg : Measurable (fun x : ℝ => f x * x ^ (-s₀ - 1) * (Real.log x)^n) :=
      (hmeas.mul (by fun_prop)).mul (Real.measurable_log.pow_const n)
    have : Measurable (F n) := by
      simp only [F]
      exact (Complex.measurable_ofReal.comp hg).mul measurable_const
    exact this.aestronglyMeasurable
  have h_bound : ∀ n, ∀ᵐ x ∂(volume.restrict (Set.Ioi x₀)), ‖F n x‖ ≤ bound n x := by
    intro n
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : (1:ℝ) ≤ x := le_trans hx₀ hx.le
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hgn : 0 ≤ f x * x ^ (-s₀ - 1) * (Real.log x)^n :=
      mul_nonneg (mul_nonneg (hnonneg x hx.le) (Real.rpow_nonneg hx0.le _))
        (pow_nonneg (Real.log_nonneg hx1) n)
    simp only [F, bound]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hgn, norm_mul, norm_pow, norm_neg,
      norm_inv, Complex.norm_natCast]
  have hbound_summable : ∀ᵐ x ∂(volume.restrict (Set.Ioi x₀)), Summable fun n => bound n x := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hexp : HasSum (fun n : ℕ => (‖z‖ * Real.log x)^n * (Nat.factorial n : ℝ)⁻¹)
        (Real.exp (‖z‖ * Real.log x)) := by
      have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (‖z‖ * Real.log x)
      rw [← Real.exp_eq_exp_ℝ] at h
      simpa [smul_eq_mul, mul_comm] using h
    have h2 := hexp.summable.mul_left (f x * x ^ (-s₀-1))
    refine h2.congr (fun n => ?_)
    simp only [bound]
    rw [mul_pow]; ring
  have hbound_integrable :
      Integrable (fun x => ∑' n, bound n x) (volume.restrict (Set.Ioi x₀)) := by
    have hEq : (fun x => ∑' n, bound n x) =ᵐ[volume.restrict (Set.Ioi x₀)]
        (fun x => f x * x^(-(s₀-‖z‖)-1)) := by
      refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      change (∑' n, bound n x) = f x * x ^ (-(s₀-‖z‖)-1)
      have hx1 : (1:ℝ) ≤ x := le_trans hx₀ hx.le
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
      have hexp : HasSum (fun n : ℕ => (‖z‖ * Real.log x)^n * (Nat.factorial n : ℝ)⁻¹)
          (Real.exp (‖z‖ * Real.log x)) := by
        have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (‖z‖ * Real.log x)
        rw [← Real.exp_eq_exp_ℝ] at h
        simpa [smul_eq_mul, mul_comm] using h
      have h0 := hexp.mul_left (f x * x^(-s₀-1))
      have hc : (∑' n : ℕ, bound n x)
          = ∑' n : ℕ, (f x * x^(-s₀-1)) * ((‖z‖ * Real.log x)^n * (Nat.factorial n : ℝ)⁻¹) := by
        apply tsum_congr; intro n
        simp only [bound]
        rw [mul_pow]; ring
      rw [hc, h0.tsum_eq]
      have hexpz : Real.exp (‖z‖ * Real.log x) = x^(‖z‖) := by
        rw [mul_comm, ← Real.rpow_def_of_pos hx0]
      rw [hexpz, mul_assoc, ← Real.rpow_add hx0]
      congr 1; ring_nf
    have hInt : IntegrableOn (fun x => f x * x^(-(s₀-‖z‖)-1)) (Set.Ioi x₀) :=
      hconv (s₀ - ‖z‖) (by linarith)
    exact hInt.congr hEq.symm
  have h_lim : ∀ᵐ x ∂(volume.restrict (Set.Ioi x₀)),
      HasSum (fun n => F n x) ((f x : ℂ) * (x:ℂ)^(-(s₀:ℂ)-z-1)) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : (1:ℝ) ≤ x := le_trans hx₀ hx.le
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    have hexp : HasSum (fun n : ℕ => ((-z * (Real.log x : ℂ))^n) * (Nat.factorial n : ℂ)⁻¹)
        (Complex.exp (-z * (Real.log x : ℂ))) := by
      have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (-z * (Real.log x : ℂ))
      rw [← Complex.exp_eq_exp_ℂ] at h
      simpa [smul_eq_mul, mul_comm] using h
    have h0 := hexp.mul_left ((f x : ℂ) * ((x:ℂ)^(-(s₀:ℂ)-1)))
    have hcp : (x:ℂ)^(-(s₀:ℂ)-z-1) = (x:ℂ)^(-(s₀:ℂ)-1) * (x:ℂ)^(-z) := by
      rw [show -(s₀:ℂ) - z - 1 = (-(s₀:ℂ)-1) + (-z) by ring]
      rw [Complex.cpow_add _ _ hxne]
    have hxpow : (x:ℂ)^(-z) = Complex.exp (-z * (Real.log x : ℂ)) := by
      rw [Complex.cpow_def, Complex.ofReal_log hx0.le]
      simp only [hxne, if_false]; congr 1; ring
    have hfun : (fun n => F n x)
        = (fun n => (f x : ℂ) * ((x:ℂ)^(-(s₀:ℂ)-1))
            * (((-z * (Real.log x : ℂ))^n) * (Nat.factorial n : ℂ)⁻¹)) := by
      funext n
      simp only [F]
      have hv : ((f x * x^(-s₀-1) * (Real.log x)^n : ℝ) : ℂ)
          = (f x : ℂ) * ((x:ℂ)^(-(s₀:ℂ)-1)) * ((Real.log x : ℂ)^n) := by
        rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_cpow hx0.le]
        push_cast; ring
      rw [hv, mul_pow]; ring
    rw [hfun, hcp, hxpow]
    simpa only [mul_assoc] using h0
  have hmain := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi x₀)) bound hFmeas h_bound hbound_summable hbound_integrable h_lim
  have hFn : ∀ n, ∫ x, F n x ∂(volume.restrict (Set.Ioi x₀))
      = (((∫ x in Set.Ioi x₀, f x * x ^ (-s₀ - 1) * (Real.log x)^n) : ℝ) : ℂ)
          * ((-z)^n * (Nat.factorial n : ℂ)⁻¹) := by
    intro n
    simp only [F]
    rw [integral_mul_const]
    congr 1
    exact integral_ofReal
  rw [funext hFn] at hmain
  simpa only [mul_assoc] using hmain

theorem landau_mellin_core_c
    (h : ℝ → ℝ) (x₀ c r : ℝ) (hr : 0 < r) (hx₀ : 1 ≤ x₀)
    (hmeas : Measurable h) (hnonneg : ∀ x : ℝ, x₀ ≤ x → 0 ≤ h x)
    (hconv : ∀ a : ℝ, c < a → MeasureTheory.IntegrableOn (fun x : ℝ => h x * x ^ (-a - 1)) (Set.Ioi x₀))
    (A : ℂ → ℂ) (hA : AnalyticOn ℂ A (Metric.ball (c : ℂ) r))
    (hAint : ∀ s : ℂ, c < s.re → A s = ∫ x in Set.Ioi x₀, (h x : ℂ) * (x : ℂ) ^ (-s - 1)) :
    ∃ a : ℝ, a < c ∧ MeasureTheory.IntegrableOn (fun x : ℝ => h x * x ^ (-a - 1)) (Set.Ioi x₀) := by
  have hr4 : 0 < r/4 := by positivity
  set s₀ : ℝ := c + r/4 with hs₀def
  set ρ₀ : ℝ := 3*r/8 with hρ₀def
  have hs₀ : c < s₀ := by rw [hs₀def]; linarith
  have hs₀sub : s₀ - c = r/4 := by rw [hs₀def]; ring
  have hρ₀nn : 0 ≤ ρ₀ := by rw [hρ₀def]; positivity
  let M : ℕ → ℝ := fun n => ∫ x in Set.Ioi x₀, h x * x ^ (-s₀ - 1) * (Real.log x)^n
  let coeff : ℕ → ℂ := fun n => (-1)^n * ((M n : ℝ) : ℂ) * (Nat.factorial n : ℂ)⁻¹
  let G : ℂ → ℂ := fun z => ∫ x in Set.Ioi x₀, (h x : ℂ) * (x : ℂ) ^ (-(s₀:ℂ) - z - 1)
  have hMnn : ∀ n, 0 ≤ M n := by
    intro n
    simp only [M]
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro x hx
    have hx1 : (1:ℝ) ≤ x := le_trans hx₀ hx.le
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
    exact mul_nonneg (mul_nonneg (hnonneg x hx.le) (Real.rpow_nonneg hx0.le _))
      (pow_nonneg (Real.log_nonneg hx1) n)
  -- the power series of the Mellin integral at s₀
  have hGps : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ coeff) 0 := by
    rw [hasFPowerSeriesAt_iff]
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0:ℂ) hr4) fun z hz => ?_
    have hz' : ‖z‖ < s₀ - c := by
      rw [hs₀sub]; simpa [dist_zero_right] using Metric.mem_ball.mp hz
    have hHS := mellin_expansion h x₀ s₀ c hx₀ hmeas hnonneg hconv hs₀ z hz'
    have hfun : (fun n => z ^ n • (FormalMultilinearSeries.ofScalars ℂ coeff).coeff n)
        = (fun n => (M n : ℂ) * (-z)^n * (Nat.factorial n : ℂ)⁻¹) := by
      funext n
      simp only [FormalMultilinearSeries.coeff_ofScalars, coeff, smul_eq_mul]
      rw [neg_pow]; ring
    rw [hfun, zero_add]
    change HasSum (fun n => (M n : ℂ) * (-z)^n * (Nat.factorial n : ℂ)⁻¹) (G z)
    rw [show G z = ∫ x in Set.Ioi x₀, (h x : ℂ) * (x : ℂ) ^ (-(s₀:ℂ) - z - 1) from rfl]
    exact hHS
  -- the power series of `A` at `s₀`, with radius `r/2`
  let R : NNReal := ⟨r/2, by positivity⟩
  have hRpos : (0:NNReal) < R := by
    rw [← NNReal.coe_pos]; change (0:ℝ) < r/2; positivity
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => A (s₀ + z)) (Metric.closedBall (0:ℂ) R) := by
    have hAdiff : DifferentiableOn ℂ A (Metric.ball (c:ℂ) r) := hA.differentiableOn
    have hg : DifferentiableOn ℂ (fun z : ℂ => (s₀:ℂ) + z) (Metric.closedBall (0:ℂ) R) :=
      (differentiableOn_const (s₀:ℂ)).add differentiableOn_id
    have hmap : MapsTo (fun z : ℂ => (s₀:ℂ) + z) (Metric.closedBall (0:ℂ) R) (Metric.ball (c:ℂ) r) := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq]
      have hz' : ‖z‖ ≤ r/2 := by
        have h := Metric.mem_closedBall.mp hz
        rw [dist_zero_right] at h
        exact h
      have h1 : (s₀:ℂ) + z - (c:ℂ) = ((r/4:ℝ):ℂ) + z := by
        rw [hs₀def]; push_cast; ring
      rw [h1]
      calc ‖((r/4:ℝ):ℂ) + z‖ ≤ ‖((r/4:ℝ):ℂ)‖ + ‖z‖ := norm_add_le _ _
        _ = r/4 + ‖z‖ := by rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        _ ≤ r/4 + r/2 := by linarith
        _ < r := by linarith
    simpa [Function.comp_def] using hAdiff.comp hg hmap
  have hAps : HasFPowerSeriesOnBall (fun z : ℂ => A (s₀ + z))
      (cauchyPowerSeries (fun z : ℂ => A (s₀ + z)) 0 R) 0 (R : ENNReal) :=
    DifferentiableOn.hasFPowerSeriesOnBall hdiff hRpos
  -- `G` and `A s₀ + ·` agree near `0`
  have hAG : G =ᶠ[𝓝 (0:ℂ)] (fun z => A (s₀ + z)) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0:ℂ) hr4) fun z hz => ?_
    change G z = A (s₀ + z)
    have hz' : c < (s₀ + z).re := by
      have h1 : ‖z‖ < r/4 := by simpa [dist_zero_right] using Metric.mem_ball.mp hz
      have h2 : |z.re| ≤ ‖z‖ := by simpa using Complex.abs_re_le_norm z
      have h3 : (s₀ + z).re = s₀ + z.re := by simp
      rw [h3, hs₀def]
      linarith [neg_abs_le z.re, h1, h2]
    rw [hAint (s₀ + z) hz']
    change (∫ x in Set.Ioi x₀, (h x : ℂ) * (x : ℂ) ^ (-(s₀:ℂ) - z - 1))
        = ∫ x in Set.Ioi x₀, (h x : ℂ) * (x : ℂ) ^ (-((s₀:ℂ) + z) - 1)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [show -(s₀:ℂ) - z - 1 = -((s₀:ℂ) + z) - 1 by ring]
  obtain ⟨r₁, hGball⟩ := hGps.congr hAG
  have hex := hGball.exchange_radius hAps
  -- evaluate at `-ρ₀`
  have hy : -(ρ₀:ℂ) ∈ Metric.eball (0:ℂ) (R : ENNReal) := by
    rw [Metric.eball_coe, Metric.mem_ball, Complex.dist_eq]
    have hρnorm : ‖-(ρ₀:ℂ)‖ = ρ₀ := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₀nn]
    rw [sub_zero, hρnorm]
    change ρ₀ < r/2
    rw [hρ₀def]; linarith
  have hsum := hex.hasSum (y := -(ρ₀:ℂ)) hy
  have hterm : ∀ n, (FormalMultilinearSeries.ofScalars ℂ coeff) n (fun _ => -(ρ₀:ℂ))
      = ((M n * ρ₀^n * (Nat.factorial n : ℝ)⁻¹ : ℝ) : ℂ) := by
    intro n
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [coeff, smul_eq_mul]
    have hsign : (-1:ℂ)^n * (-1:ℂ)^n = 1 := by
      rw [← pow_add, show n + n = 2 * n by ring, pow_mul]; norm_num
    have hcast : ((M n * ρ₀^n * (Nat.factorial n : ℝ)⁻¹ : ℝ) : ℂ)
        = (M n : ℂ) * ((ρ₀:ℂ))^n * (Nat.factorial n : ℂ)⁻¹ := by
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
        Complex.ofReal_natCast]
    have hneg : (-(ρ₀:ℂ))^n = (-1:ℂ)^n * (ρ₀:ℂ)^n := neg_pow _ _
    rw [hneg, hcast]
    calc (-1:ℂ)^n * (M n : ℂ) * (Nat.factorial n : ℂ)⁻¹ * ((-1:ℂ)^n * (ρ₀:ℂ)^n)
        = ((-1:ℂ)^n * (-1:ℂ)^n) * ((M n : ℂ) * (Nat.factorial n : ℂ)⁻¹ * (ρ₀:ℂ)^n) := by ring
      _ = (M n : ℂ) * (ρ₀:ℂ)^n * (Nat.factorial n : ℂ)⁻¹ := by rw [hsign, one_mul]; ring
  have hSummC : Summable (fun n => ((M n * ρ₀^n * (Nat.factorial n : ℝ)⁻¹ : ℝ) : ℂ)) :=
    hsum.summable.congr (fun n => hterm n)
  have hSumm : Summable (fun n => M n * ρ₀^n * (Nat.factorial n : ℝ)⁻¹) :=
    Complex.summable_ofReal.mp hSummC
  -- the final Tonelli/lintegral computation
  set gg : ℕ → ℝ → ENNReal := fun n x =>
    ENNReal.ofReal (h x * x ^ (-s₀-1) * (Real.log x)^n * (ρ₀^n * (Nat.factorial n : ℝ)⁻¹))
    with hggdef
  have hgg_aem : ∀ n, AEMeasurable (gg n) (volume.restrict (Set.Ioi x₀)) := by
    intro n
    have hm : Measurable (fun x : ℝ =>
        h x * x ^ (-s₀-1) * (Real.log x)^n * (ρ₀^n * (Nat.factorial n : ℝ)⁻¹)) :=
      ((hmeas.mul (by fun_prop)).mul (Real.measurable_log.pow_const n)).mul measurable_const
    exact hm.aemeasurable.ennreal_ofReal
  have hlint := lintegral_tsum (μ := volume.restrict (Set.Ioi x₀)) hgg_aem
  have hRHS : ∀ n, ∫⁻ x, gg n x ∂(volume.restrict (Set.Ioi x₀))
      = ENNReal.ofReal (M n * ρ₀^n * (Nat.factorial n : ℝ)⁻¹) := by
    intro n
    have hfi : Integrable (fun x : ℝ =>
        h x * x ^ (-s₀-1) * (Real.log x)^n * (ρ₀^n * (Nat.factorial n : ℝ)⁻¹))
        (volume.restrict (Set.Ioi x₀)) := (moment_integrable h x₀ s₀ c hx₀ hmeas hnonneg hconv hs₀ n).mul_const _
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi x₀)] (fun x : ℝ =>
        h x * x ^ (-s₀-1) * (Real.log x)^n * (ρ₀^n * (Nat.factorial n : ℝ)⁻¹)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) ≤ x := le_trans hx₀ hx.le
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
      exact mul_nonneg (mul_nonneg (mul_nonneg (hnonneg x hx.le) (Real.rpow_nonneg hx0.le _))
        (pow_nonneg (Real.log_nonneg hx1) n)) (by positivity)
    rw [show gg n = (fun x : ℝ =>
        ENNReal.ofReal (h x * x ^ (-s₀-1) * (Real.log x)^n * (ρ₀^n * (Nat.factorial n : ℝ)⁻¹))) from rfl]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnn]
    congr 1
    rw [integral_mul_const]
    simp only [M]
    ring
  have hLHS : (∫⁻ x in Set.Ioi x₀, ENNReal.ofReal (h x * x ^ (-(s₀-ρ₀)-1)))
      = ∫⁻ x, (∑' n, gg n x) ∂(volume.restrict (Set.Ioi x₀)) := by
    apply MeasureTheory.lintegral_congr_ae
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    change ENNReal.ofReal (h x * x ^ (-(s₀-ρ₀)-1)) = ∑' n, gg n x
    symm
    have hx1 : (1:ℝ) ≤ x := le_trans hx₀ hx.le
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hxp : 0 ≤ x ^ (-s₀-1) := Real.rpow_nonneg hx0.le _
    have hexp : HasSum (fun n : ℕ => (ρ₀ * Real.log x)^n * (Nat.factorial n : ℝ)⁻¹)
        (Real.exp (ρ₀ * Real.log x)) := by
      have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (ρ₀ * Real.log x)
      rw [← Real.exp_eq_exp_ℝ] at h
      simpa [smul_eq_mul, mul_comm] using h
    have hfac : ∀ n, gg n x
        = ENNReal.ofReal (h x * x ^ (-s₀-1))
          * ENNReal.ofReal ((ρ₀ * Real.log x)^n * (Nat.factorial n : ℝ)⁻¹) := by
      intro n
      rw [show gg n x = ENNReal.ofReal
          (h x * x ^ (-s₀-1) * (Real.log x)^n * (ρ₀^n * (Nat.factorial n : ℝ)⁻¹)) from rfl]
      rw [← ENNReal.ofReal_mul (mul_nonneg (hnonneg x hx.le) hxp)]
      congr 1; rw [mul_pow]; ring
    rw [tsum_congr hfac, ENNReal.tsum_mul_left,
      ← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (pow_nonneg (mul_nonneg hρ₀nn (Real.log_nonneg hx1)) n)
          (by positivity)) hexp.summable, hexp.tsum_eq]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hnonneg x hx.le) hxp)]
    congr 1
    rw [mul_comm ρ₀, ← Real.rpow_def_of_pos hx0]
    rw [mul_assoc, ← Real.rpow_add hx0]
    congr 1
    ring_nf
  have hfin : ∫⁻ x in Set.Ioi x₀, ENNReal.ofReal (h x * x ^ (-(s₀-ρ₀)-1)) ≠ ⊤ := by
    rw [hLHS, hlint, tsum_congr hRHS,
      ← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (mul_nonneg (hMnn n) (pow_nonneg hρ₀nn n)) (by positivity)) hSumm]
    exact ENNReal.ofReal_ne_top
  refine ⟨s₀ - ρ₀, ?_, ?_⟩
  · rw [hs₀def, hρ₀def]; linarith
  · have h1 : AEStronglyMeasurable (fun x : ℝ => h x * x ^ (-(s₀-ρ₀)-1))
        (volume.restrict (Set.Ioi x₀)) :=
      (hmeas.mul (by fun_prop)).aestronglyMeasurable
    have h2 : 0 ≤ᵐ[volume.restrict (Set.Ioi x₀)] (fun x : ℝ => h x * x ^ (-(s₀-ρ₀)-1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) ≤ x := le_trans hx₀ hx.le
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
      exact mul_nonneg (hnonneg x hx.le) (Real.rpow_nonneg hx0.le _)
    show Integrable (fun x : ℝ => h x * x ^ (-(s₀-ρ₀)-1)) (volume.restrict (Set.Ioi x₀))
    rw [← MeasureTheory.lintegral_ofReal_ne_top_iff_integrable h1 h2]
    exact hfin

end

end Work.RHContract.B
