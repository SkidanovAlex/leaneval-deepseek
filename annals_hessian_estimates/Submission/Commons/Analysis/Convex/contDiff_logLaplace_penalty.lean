import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

set_option maxHeartbeats 800000

open MeasureTheory
open scoped Real

namespace Commons.Analysis.Convex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def innerProdₘ (n : ℕ) (y : V) : ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℝ :=
  (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (1 : ℝ)).compContinuousLinearMap
    (fun _ => innerSL ℝ y)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma innerProdₘ_apply (n : ℕ) (y : V) (m : Fin n → V) :
    innerProdₘ n y m = ∏ i, inner ℝ y (m i) := by
  simp [innerProdₘ, ContinuousMultilinearMap.compContinuousLinearMap_apply]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma continuous_innerProdₘ (n : ℕ) : Continuous (fun y : V => innerProdₘ n y) := by
  have h : (fun y : V => innerProdₘ n y) =
      (ContinuousMultilinearMap.compContinuousLinearMapLRight (𝕜 := ℝ)
        (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (1 : ℝ))).toFun ∘
        (fun y : V => fun _ : Fin n => innerSL ℝ y) := by
    ext y m
    simp [innerProdₘ, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [h]
  exact (ContinuousMultilinearMap.compContinuousLinearMapLRight _).cont.comp
    (continuous_pi (fun _ => (innerSL ℝ).continuous))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma norm_innerProdₘ_le (n : ℕ) (y : V) : ‖innerProdₘ n y‖ ≤ ‖y‖ ^ n := by
  refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖y‖ ^ n) (by positivity) (fun m => ?_)
  rw [innerProdₘ_apply]
  calc ‖∏ i, inner ℝ y (m i)‖ = ∏ i, ‖inner ℝ y (m i)‖ := by rw [norm_prod]
    _ ≤ ∏ i, ‖y‖ * ‖m i‖ := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _; exact norm_inner_le_norm _ _
    _ = ‖y‖ ^ n * ∏ i, ‖m i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma innerProdₘ_diag (n : ℕ) (y h : V) : innerProdₘ n y (fun _ => h) = (inner ℝ y h) ^ n := by
  rw [innerProdₘ_apply, Finset.prod_const, Finset.card_fin]

lemma exp_mul_pow_le {s : ℝ} (hs : 0 < s) {a t : ℝ} (_ht : 0 ≤ t) (n : ℕ) :
    Real.exp (a * t) * t ^ n ≤ s⁻¹ ^ n * (n.factorial : ℝ) * Real.exp ((a + s) * t) := by
  have h := Real.pow_div_factorial_le_exp (s * t) (by positivity) n
  have hsn : (s * t) ^ n = s ^ n * t ^ n := by rw [mul_pow]
  rw [hsn, div_le_iff₀ (by positivity : (0:ℝ) < (n.factorial:ℝ))] at h
  have hsne : s⁻¹ ^ n * s ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hs), one_pow]
  have key : t ^ n ≤ s⁻¹ ^ n * (n.factorial:ℝ) * Real.exp (s*t) := by
    calc t ^ n = s⁻¹ ^ n * (s ^ n * t ^ n) := by rw [← mul_assoc, hsne, one_mul]
      _ ≤ s⁻¹ ^ n * (Real.exp (s*t) * (n.factorial:ℝ)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = s⁻¹ ^ n * (n.factorial:ℝ) * Real.exp (s*t) := by ring
  calc Real.exp (a*t) * t^n
      ≤ Real.exp (a*t) * (s⁻¹^n * (n.factorial:ℝ) * Real.exp (s*t)) := by
        apply mul_le_mul_of_nonneg_left key (by positivity)
    _ = s⁻¹^n * (n.factorial:ℝ) * (Real.exp (a*t) * Real.exp (s*t)) := by ring
    _ = s⁻¹^n * (n.factorial:ℝ) * Real.exp ((a+s)*t) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- The formal power series of the weighted multidimensional Laplace transform. -/
noncomputable def mgfSeries (μ : Measure V) (g : V → ℝ) (x₀ : V) : FormalMultilinearSeries ℝ V ℝ :=
  fun n => (n.factorial : ℝ)⁻¹ • ∫ y, (g y * Real.exp (inner ℝ x₀ y)) • innerProdₘ n y ∂μ

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma norm_mgf_integrand_le (g : V → ℝ) (hg : ∀ y, 0 ≤ g y) {K : ℝ}
    {x₀ : V} (hx₀ : ‖x₀‖ < K) (n : ℕ) :
    ∀ y : V, ‖(g y * Real.exp (inner ℝ x₀ y)) • innerProdₘ n y‖
      ≤ (K - ‖x₀‖)⁻¹ ^ n * (n.factorial : ℝ) * (g y * Real.exp (K * ‖y‖)) := by
  intro y
  have hs_pos : 0 < K - ‖x₀‖ := by linarith
  have hgy : 0 ≤ g y := hg y
  have h1 : ‖(g y * Real.exp (inner ℝ x₀ y)) • innerProdₘ n y‖
      = (g y * Real.exp (inner ℝ x₀ y)) * ‖innerProdₘ n y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgy (Real.exp_nonneg _))]
  have h2 : Real.exp (inner ℝ x₀ y) ≤ Real.exp (‖x₀‖ * ‖y‖) :=
    Real.exp_le_exp.mpr (real_inner_le_norm x₀ y)
  have h3 : ‖innerProdₘ n y‖ ≤ ‖y‖ ^ n := norm_innerProdₘ_le n y
  rw [h1]
  calc g y * Real.exp (inner ℝ x₀ y) * ‖innerProdₘ n y‖
      ≤ g y * (Real.exp (‖x₀‖ * ‖y‖) * ‖y‖ ^ n) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (by positivity) (by positivity)) hgy
    _ ≤ g y * ((K - ‖x₀‖)⁻¹ ^ n * (n.factorial : ℝ) * Real.exp (K * ‖y‖)) := by
        apply mul_le_mul_of_nonneg_left _ hgy
        have hh := exp_mul_pow_le (a := ‖x₀‖) (s := K - ‖x₀‖) hs_pos (norm_nonneg y) n
        simpa only [show ‖x₀‖ + (K - ‖x₀‖) = K from by ring, mul_assoc] using hh
    _ = (K - ‖x₀‖)⁻¹ ^ n * (n.factorial : ℝ) * (g y * Real.exp (K * ‖y‖)) := by ring

lemma integrable_mgf_integrand (μ : Measure V) (g : V → ℝ) (hg : ∀ y, 0 ≤ g y)
    (hg_meas : AEStronglyMeasurable g μ) {K : ℝ}
    (hK : Integrable (fun y => g y * Real.exp (K * ‖y‖)) μ) {x₀ : V} (hx₀ : ‖x₀‖ < K) (n : ℕ) :
    Integrable (fun y => (g y * Real.exp (inner ℝ x₀ y)) • innerProdₘ n y) μ := by
  refine (hK.const_mul ((K - ‖x₀‖)⁻¹ ^ n * (n.factorial : ℝ))).mono' ?_ ?_
  · exact (hg_meas.mul (Real.continuous_exp.comp
      (continuous_const.inner continuous_id)).aestronglyMeasurable).smul
        (continuous_innerProdₘ n).aestronglyMeasurable
  · filter_upwards with y using norm_mgf_integrand_le g hg hx₀ n y


lemma mgfSeries_diag (μ : Measure V) (g : V → ℝ) (hg : ∀ y, 0 ≤ g y)
    (hg_meas : AEStronglyMeasurable g μ) {K : ℝ}
    (hK : Integrable (fun y => g y * Real.exp (K * ‖y‖)) μ) {x₀ : V} (hx₀ : ‖x₀‖ < K)
    (n : ℕ) (h : V) :
    mgfSeries μ g x₀ n (fun _ => h)
      = ∫ y, g y * Real.exp (inner ℝ x₀ y) * (inner ℝ y h) ^ n / n.factorial ∂μ := by
  have hint := integrable_mgf_integrand μ g hg hg_meas hK hx₀ n
  rw [mgfSeries, smul_apply,
    ContinuousMultilinearMap.integral_apply hint]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  rw [smul_apply, innerProdₘ_diag]
  simp only [smul_eq_mul]
  ring

lemma hasSum_exp_series (z : ℝ) : HasSum (fun n : ℕ => z ^ n / n.factorial) (Real.exp z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) z
  rwa [← Real.exp_eq_exp_ℝ] at h

lemma hasSum_mgfSeries (μ : Measure V) (g : V → ℝ) (hg : ∀ y, 0 ≤ g y)
    (hg_meas : AEStronglyMeasurable g μ) {K : ℝ}
    (hK : Integrable (fun y => g y * Real.exp (K * ‖y‖)) μ) {x₀ : V} (hx₀ : ‖x₀‖ < K)
    {h : V} (hh : ‖h‖ < K - ‖x₀‖) :
    HasSum (fun n => mgfSeries μ g x₀ n (fun _ => h))
      (∫ y, g y * Real.exp (inner ℝ (x₀ + h) y) ∂μ) := by
  have hs_pos : 0 < K - ‖x₀‖ := by linarith
  set s : ℝ := K - ‖x₀‖ with hs
  have hhs : ‖h‖ < s := by simp only [hs]; exact hh
  set F : ℕ → V → ℝ := fun n y =>
    g y * Real.exp (inner ℝ x₀ y) * (inner ℝ y h) ^ n / n.factorial with hFdef
  set bound : ℕ → V → ℝ := fun n y =>
    g y * Real.exp (‖x₀‖ * ‖y‖) * (s * ‖y‖) ^ n / n.factorial with hbound_def
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    have hinner1 : Continuous (fun y : V => inner ℝ x₀ y) := continuous_const.inner continuous_id
    have hinner2 : Continuous (fun y : V => inner ℝ y h) := continuous_id.inner continuous_const
    have hc : Continuous (fun y : V =>
        Real.exp (inner ℝ x₀ y) * (inner ℝ y h) ^ n / n.factorial) :=
      ((Real.continuous_exp.comp hinner1).mul (hinner2.pow n)).div_const _
    refine (hg_meas.mul hc.aestronglyMeasurable).congr ?_
    filter_upwards with y
    simp only [Pi.mul_apply, hFdef]
    ring
  have h_bound : ∀ n, ∀ᵐ y ∂μ, ‖F n y‖ ≤ bound n y := by
    intro n
    filter_upwards with y
    have hgy : 0 ≤ g y := hg y
    have h1 : Real.exp (inner ℝ x₀ y) ≤ Real.exp (‖x₀‖ * ‖y‖) :=
      Real.exp_le_exp.mpr (real_inner_le_norm x₀ y)
    have h2 : |inner ℝ y h| ≤ s * ‖y‖ := by
      have := norm_inner_le_norm (𝕜 := ℝ) y h
      rw [Real.norm_eq_abs] at this
      calc |inner ℝ y h| ≤ ‖y‖ * ‖h‖ := this
        _ ≤ ‖y‖ * s := by
            apply mul_le_mul_of_nonneg_left hhs.le (norm_nonneg y)
        _ = s * ‖y‖ := by ring
    have hfac : (0:ℝ) ≤ (n.factorial : ℝ) := by positivity
    simp only [hFdef, hbound_def, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, Real.abs_exp,
      Nat.abs_cast, abs_of_nonneg hgy]
    apply div_le_div_of_nonneg_right _ hfac
    calc g y * Real.exp (inner ℝ x₀ y) * |inner ℝ y h| ^ n
        ≤ g y * (Real.exp (‖x₀‖ * ‖y‖) * (s * ‖y‖) ^ n) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul h1 (pow_le_pow_left₀ (abs_nonneg _) h2 n) (by positivity) (by positivity)) hgy
      _ = g y * Real.exp (‖x₀‖ * ‖y‖) * (s * ‖y‖) ^ n := by ring
  have hbound_summable : ∀ᵐ y ∂μ, Summable (fun n => bound n y) := by
    filter_upwards with y
    have := (hasSum_exp_series (s * ‖y‖)).mul_left (g y * Real.exp (‖x₀‖ * ‖y‖))
    refine this.summable.congr (fun n => ?_)
    simp only [hbound_def]
    ring
  have hbound_tsum : ∀ y, ∑' n, bound n y = g y * Real.exp (K * ‖y‖) := by
    intro y
    have h1 := (hasSum_exp_series (s * ‖y‖)).mul_left (g y * Real.exp (‖x₀‖ * ‖y‖))
    have h2 : (∑' n, bound n y) = g y * Real.exp (‖x₀‖ * ‖y‖) * Real.exp (s * ‖y‖) := by
      rw [← h1.tsum_eq]
      apply tsum_congr
      intro n
      simp only [hbound_def]
      ring
    rw [h2, show g y * Real.exp (‖x₀‖ * ‖y‖) * Real.exp (s * ‖y‖)
          = g y * (Real.exp (‖x₀‖ * ‖y‖) * Real.exp (s * ‖y‖)) by ring]
    rw [← Real.exp_add]
    congr 1
    simp only [hs]; ring
  have hbound_integrable : Integrable (fun y => ∑' n, bound n y) μ :=
    hK.congr (Filter.Eventually.of_forall fun y => (hbound_tsum y).symm)
  have h_lim : ∀ᵐ y ∂μ, HasSum (fun n => F n y)
      (g y * Real.exp (inner ℝ (x₀ + h) y)) := by
    filter_upwards with y
    have h1 := (hasSum_exp_series (inner ℝ y h)).mul_left (g y * Real.exp (inner ℝ x₀ y))
    have h2 : (fun n => F n y)
        = (fun n => g y * Real.exp (inner ℝ x₀ y) * (inner ℝ y h) ^ n / n.factorial) := by
      funext n
      rfl
    have hgoal : g y * Real.exp (inner ℝ (x₀ + h) y)
        = g y * Real.exp (inner ℝ x₀ y) * Real.exp (inner ℝ y h) := by
      rw [inner_add_left, Real.exp_add, real_inner_comm h y]
      ring
    rw [h2, hgoal]
    simpa only [mul_div_assoc] using h1
  have hmain := hasSum_integral_of_dominated_convergence bound hF_meas h_bound
    hbound_summable hbound_integrable h_lim
  have hfun : (fun n => mgfSeries μ g x₀ n (fun _ => h)) = (fun n => ∫ y, F n y ∂μ) := by
    funext n
    rw [mgfSeries_diag μ g hg hg_meas hK hx₀ n h]
  rw [hfun]
  exact hmain


theorem analyticAt_integral_exp_inner (μ : Measure V) (g : V → ℝ) (hg : ∀ y, 0 ≤ g y)
    (hg_meas : AEStronglyMeasurable g μ) {K : ℝ}
    (hK : Integrable (fun y => g y * Real.exp (K * ‖y‖)) μ) {x₀ : V} (hx₀ : ‖x₀‖ < K) :
    AnalyticAt ℝ (fun x => ∫ y, g y * Real.exp (inner ℝ x y) ∂μ) x₀ := by
  have hs_pos : 0 < K - ‖x₀‖ := by linarith
  set rr : NNReal := ⟨(K - ‖x₀‖) / 2, by positivity⟩ with hrr
  have hrrR : (rr : ℝ) = (K - ‖x₀‖) / 2 := rfl
  refine ⟨mgfSeries μ g x₀, (rr : ENNReal), ?_, ?_, ?_⟩
  · set M : ℝ := ∫ y, g y * Real.exp (K * ‖y‖) ∂μ with hMdef
    have hMnn : 0 ≤ M := integral_nonneg (fun y => mul_nonneg (hg y) (Real.exp_nonneg _))
    apply (mgfSeries μ g x₀).le_radius_of_bound M
    intro n
    have hnorm : ‖mgfSeries μ g x₀ n‖ ≤ (K - ‖x₀‖)⁻¹ ^ n * M := by
      have hint := integrable_mgf_integrand μ g hg hg_meas hK hx₀ n
      have hbnd := norm_mgf_integrand_le g hg hx₀ n
      rw [mgfSeries, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n.factorial : ℝ)⁻¹)]
      calc (n.factorial : ℝ)⁻¹ * ‖∫ y, (g y * Real.exp (inner ℝ x₀ y)) • innerProdₘ n y ∂μ‖
          ≤ (n.factorial : ℝ)⁻¹ *
              ∫ y, ‖(g y * Real.exp (inner ℝ x₀ y)) • innerProdₘ n y‖ ∂μ := by
            apply mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
        _ ≤ (n.factorial : ℝ)⁻¹ *
              ∫ y, (K - ‖x₀‖)⁻¹ ^ n * (n.factorial : ℝ) * (g y * Real.exp (K * ‖y‖)) ∂μ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact integral_mono hint.norm (hK.const_mul _) (fun y => hbnd y)
        _ = (K - ‖x₀‖)⁻¹ ^ n * M := by
            rw [hMdef, integral_const_mul]
            field_simp
    calc ‖mgfSeries μ g x₀ n‖ * (rr : ℝ) ^ n
        ≤ ((K - ‖x₀‖)⁻¹ ^ n * M) * (rr : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = M * (1/2 : ℝ) ^ n := by
          rw [hrrR]
          rw [show (K - ‖x₀‖)⁻¹ ^ n * M * ((K - ‖x₀‖) / 2) ^ n
                = M * ((K - ‖x₀‖)⁻¹ * ((K - ‖x₀‖) / 2)) ^ n by rw [mul_pow]; ring]
          congr 1
          field_simp
      _ ≤ M * 1 := by
          apply mul_le_mul_of_nonneg_left _ hMnn
          exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = M := by ring
  · apply ENNReal.coe_pos.mpr
    change (0:ℝ) < (rr:ℝ)
    rw [hrrR]
    linarith
  · intro y hy
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm] at hy
    have hy2 : ‖y‖ < (K - ‖x₀‖) / 2 := by
      have h2 : (‖y‖₊ : ℝ) < (rr : ℝ) := NNReal.coe_lt_coe.mp (ENNReal.coe_lt_coe.mp hy)
      rw [hrrR] at h2
      exact_mod_cast h2
    exact hasSum_mgfSeries μ g hg hg_meas hK hx₀ (by linarith)


section Application

lemma integrable_exp_mul_exp_neg_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (c K : ℝ) (hc : 0 < c) :
    Integrable (fun y : V => Real.exp (K * ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) volume := by
  have hb : 0 < c/2 := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc
  have hbase : Integrable (fun y : V => Real.exp (-(c/2) * ‖y‖ ^ 2)) volume :=
    Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (c/2) hb
  refine (hbase.const_mul (Real.exp (K^2/(2*c)))).mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_norm)).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
  · filter_upwards with y
    have hy : 0 ≤ ‖y‖ := norm_nonneg y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
    have h2 : K * ‖y‖ - (c/2) * ‖y‖^2 ≤ K^2/(2*c) := by
      have h3 : 0 ≤ (c/2) * (‖y‖ - K/c)^2 := by positivity
      have h4 : (c/2) * (‖y‖ - K/c)^2 = K^2/(2*c) - (K*‖y‖ - (c/2)*‖y‖^2) := by
        field_simp; ring
      linarith [h3, h4]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith

end Application


section Main

/-- **Smoothness of the log-Laplace penalty.**

For a measurable set `A ⊆ ℝ^n` and `ε > 0`, the function
`x ↦ -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))` is `C^∞` on all of
`EuclideanSpace ℝ (Fin n)` whenever the integral `∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)` is
positive everywhere.

This is the "log-Laplace" (Moreau–Yosida smoothed) penalty for the constraint `x ∈ A`; it is
smooth, convex (for convex `A`), vanishes on `A` and blows up off `A` as `ε → 0`.

We prove the stronger statement that the function is real-analytic: `ContDiff ℝ ⊤` is
`ContDiff ℝ ω`, i.e. analyticity.  The crux is the smoothness (analyticity) of
`F x = ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)`: after completing the square,
`F x = Real.exp (-c ‖x‖ ^ 2) * T (2c • x)` where `c = ε⁻¹ ^ 2` and `T` is the
(weighted) multidimensional Laplace transform `T z = ∫ y, g y * Real.exp ⟨z, y⟩` with
`g y = 1_A y * Real.exp (-c ‖y‖ ^ 2)`.  Analyticity of such Laplace transforms -- the
multidimensional moment-generating function of a measure with exponential moments -- is
proved from scratch (`analyticAt_integral_exp_inner`), then composed with `Real.log`,
which is analytic away from `0`.

The main supporting results are:
* `analyticAt_integral_exp_inner`: the weighted multidimensional MGF is analytic;
* `integrable_exp_mul_exp_neg_sq`: Gaussian exponential moments are integrable. -/
theorem contDiff_logLaplace_penalty (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAm : MeasurableSet A)
    (hpos : ∀ x : EuclideanSpace ℝ (Fin n),
      0 < ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) =>
      -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))) := by
  set c : ℝ := (ε ^ 2)⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    A.indicator (fun y => Real.exp (-c * ‖y‖ ^ 2)) with hg
  have hgnn : ∀ y, 0 ≤ g y := by
    intro y; rw [hg]
    exact Set.indicator_nonneg (fun y _ => Real.exp_nonneg _) y
  have hgmeas : AEStronglyMeasurable g volume := by
    rw [hg]
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ hAm
    fun_prop
  have hcontE : ∀ K : ℝ, AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (K * ‖y‖)) volume := fun K =>
    (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
  have hmoment : ∀ K : ℝ, Integrable (fun y => g y * Real.exp (K * ‖y‖)) volume := by
    intro K
    refine (integrable_exp_mul_exp_neg_sq c K hcpos).mono' ?_ ?_
    · exact hgmeas.mul (hcontE K)
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hgnn y) (Real.exp_nonneg _)), hg]
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy]
        exact le_of_eq (mul_comm _ _)
      · rw [Set.indicator_of_notMem hy, zero_mul]
        exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  set T : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => ∫ y, g y * Real.exp (inner ℝ z y) ∂volume with hT
  have hT_an : AnalyticOnNhd ℝ T Set.univ := by
    intro z _
    rw [hT]
    exact analyticAt_integral_exp_inner volume g hgnn hgmeas (hmoment (‖z‖ + 1)) (by linarith)
  have hT_cd : ContDiff ℝ ⊤ T := hT_an.contDiff
  have hF_eq : ∀ x : EuclideanSpace ℝ (Fin n),
      (∫ y in A, Real.exp (-c * ‖x - y‖ ^ 2))
        = Real.exp (-c * ‖x‖ ^ 2) * T ((2*c) • x) := by
    intro x
    have hpoint : ∀ y : EuclideanSpace ℝ (Fin n),
        A.indicator (fun y => Real.exp (-c * ‖x - y‖ ^ 2)) y
          = Real.exp (-c * ‖x‖ ^ 2) * (g y * Real.exp (inner ℝ ((2*c) • x) y)) := by
      intro y
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy, hg, Set.indicator_of_mem hy]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [real_inner_smul_left, norm_sub_sq_real]
        ring
      · rw [Set.indicator_of_notMem hy, hg, Set.indicator_of_notMem hy, zero_mul, mul_zero]
    calc (∫ y in A, Real.exp (-c * ‖x - y‖ ^ 2))
        = ∫ y, A.indicator (fun y => Real.exp (-c * ‖x - y‖ ^ 2)) y ∂volume :=
          (integral_indicator hAm).symm
      _ = ∫ y, Real.exp (-c * ‖x‖ ^ 2) * (g y * Real.exp (inner ℝ ((2*c) • x) y)) ∂volume := by
          apply integral_congr_ae
          filter_upwards with y
          exact hpoint y
      _ = Real.exp (-c * ‖x‖ ^ 2) * ∫ y, g y * Real.exp (inner ℝ ((2*c) • x) y) ∂volume :=
          integral_const_mul _ _
      _ = Real.exp (-c * ‖x‖ ^ 2) * T ((2*c) • x) := rfl
  have hpos' : ∀ x : EuclideanSpace ℝ (Fin n),
      0 < Real.exp (-c * ‖x‖ ^ 2) * T ((2*c) • x) := by
    intro x
    rw [← hF_eq x]
    rw [show (∫ y in A, Real.exp (-c * ‖x - y‖ ^ 2))
          = ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) from
        setIntegral_congr_fun hAm (fun y _ => by congr 1; rw [hc, div_eq_mul_inv]; ring)]
    exact hpos x
  have hmain : ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-c * ‖x‖ ^ 2) * T ((2*c) • x)) := by
    apply ContDiff.mul
    · apply Real.contDiff_exp.comp
      rw [show (fun x : EuclideanSpace ℝ (Fin n) => -c * ‖x‖ ^ 2)
            = fun x => -c * inner ℝ x x from
          funext fun x => by rw [real_inner_self_eq_norm_sq]]
      exact ContDiff.const_smul (-c) (ContDiff.inner ℝ contDiff_id contDiff_id)
    · exact hT_cd.comp (contDiff_const_smul (2*c))
  rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
        -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)))
      = (fun x : EuclideanSpace ℝ (Fin n) =>
        -Real.log (Real.exp (-c * ‖x‖ ^ 2) * T ((2*c) • x))) from by
    funext x
    rw [show (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
          = ∫ y in A, Real.exp (-c * ‖x - y‖ ^ 2) from
        (setIntegral_congr_fun hAm (fun y _ => by congr 1; rw [hc, div_eq_mul_inv]; ring))]
    rw [hF_eq x]]
  apply ContDiff.neg
  exact ContDiff.log hmain (fun x => ne_of_gt (hpos' x))

end Main

end Commons.Analysis.Convex