import Submission.Rad.Identity
import Submission.Commons.Analysis.Integral.jensen_rpow_prob
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal BigOperators Interval
noncomputable section
namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The smooth form of the integrand `Jint`, where the `1/sinθ` has been removed. -/
noncomputable def Jsmooth (θ : ℝ) {n : ℕ} (f : Ω n → X) (x : Ω n) : X :=
  ∑ j : Fin n, ∑ ξ : Ω n,
    (((((ξ j : C) : ℝ) * Real.sin θ) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n)
      • (D j f) (mulΩ x ξ)

/-- `Jint` agrees with its smooth form where `sinθ ≠ 0`. -/
lemma Jint_eq_Jsmooth (θ : ℝ) {n : ℕ} (f : Ω n → X) (x : Ω n) (hsin : Real.sin θ ≠ 0) :
    Jint θ f x = Jsmooth θ f x := by
  rw [← Jsum_eq_Jint]
  unfold δSum1 Jsmooth
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [biasW_mul_delta θ ξ j hsin]


lemma abs_one_coe (z : C) : |((z : C) : ℝ)| = 1 := by
  rcases coe_real_eq z with h | h <;> simp [h]

lemma abs_coeff_le_one (θ : ℝ) {n : ℕ} (ξ : Ω n) (j : Fin n) :
    |((((ξ j : C) : ℝ) * Real.sin θ) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n| ≤ 1 := by
  have hz : |((ξ j : C) : ℝ)| ≤ 1 := by rw [abs_one_coe]
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hzsmul : |((ξ j : C) : ℝ) * Real.sin θ| ≤ 1 := by
    rw [abs_mul]
    simpa using (mul_le_mul hz hs (abs_nonneg _) (by norm_num) : |((ξ j : C) : ℝ)| * |Real.sin θ| ≤ 1 * 1)
  have hfactor : ∀ k : Fin n, |1 + Real.cos θ * ((ξ k : C) : ℝ)| ≤ 2 := by
    intro k
    have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have hzk : |((ξ k : C) : ℝ)| ≤ 1 := by rw [abs_one_coe]
    have habs : |Real.cos θ * ((ξ k : C) : ℝ)| ≤ 1 := by
      rw [abs_mul]
      simpa using (mul_le_mul hc hzk (abs_nonneg _) (by norm_num) : |Real.cos θ| * |((ξ k : C) : ℝ)| ≤ 1 * 1)
    have hlo : -1 ≤ Real.cos θ * ((ξ k : C) : ℝ) := (abs_le.mp habs).1
    have hhi : Real.cos θ * ((ξ k : C) : ℝ) ≤ 1 := (abs_le.mp habs).2
    have h0 : 0 ≤ 1 + Real.cos θ * ((ξ k : C) : ℝ) := by linarith
    have hle2 : 1 + Real.cos θ * ((ξ k : C) : ℝ) ≤ 2 := by linarith
    calc
      |1 + Real.cos θ * ((ξ k : C) : ℝ)| = 1 + Real.cos θ * ((ξ k : C) : ℝ) := abs_of_nonneg h0
      _ ≤ 2 := hle2
  have hP : |∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ))| ≤ (2 : ℝ) ^ n := by
    calc
      |∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ))|
          = ∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, |1 + Real.cos θ * ((ξ k : C) : ℝ)| := by
              rw [Finset.abs_prod]
      _ ≤ ∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (2 : ℝ) := by
              exact Finset.prod_le_prod (by intro k hk; positivity) (by intro k hk; exact hfactor k)
      _ ≤ ∏ k ∈ (Finset.univ : Finset (Fin n)), (2 : ℝ) := by
              exact Finset.prod_le_prod_of_subset_of_one_le (Finset.erase_subset j (Finset.univ : Finset (Fin n)))
                (by intro k hk; positivity) (by intro k hk hjk; norm_num)
      _ = (2 : ℝ) ^ n := by
              rw [Finset.prod_const]
              simp
  have hnum : |(((ξ j : C) : ℝ) * Real.sin θ) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))| ≤ (2 : ℝ) ^ n := by
    rw [abs_mul]
    have hmul : |((ξ j : C) : ℝ) * Real.sin θ| * |∏ k ∈ (Finset.univ : Finset (Fin n)).erase j,
        (1 + Real.cos θ * ((ξ k : C) : ℝ))| ≤ 1 * (2 : ℝ) ^ n := by
      exact mul_le_mul hzsmul hP (abs_nonneg _) (by norm_num)
    simpa using hmul
  calc
    |((((ξ j : C) : ℝ) * Real.sin θ) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n|
        = |(((ξ j : C) : ℝ) * Real.sin θ) *
          (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))| / (2 : ℝ) ^ n := by
            rw [abs_div]
            congr 1
            exact abs_of_pos (by positivity : 0 < (2 : ℝ) ^ n)
    _ ≤ (2 : ℝ) ^ n / (2 : ℝ) ^ n := by
            exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 := by
            field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

/-- `‖Jsmooth(θ,x)‖ ≤ ∑_{j,ξ} ‖D_j f (xξ)‖` for every `θ`. -/
lemma norm_Jsmooth_le {n : ℕ} (f : Ω n → X) (x : Ω n) (θ : ℝ) :
    ‖Jsmooth θ f x‖ ≤ (∑ j : Fin n, ∑ ξ : Ω n, ‖D j f (mulΩ x ξ)‖) := by
  unfold Jsmooth
  calc
    ‖∑ j : Fin n, ∑ ξ : Ω n,
        (((((ξ j : C) : ℝ) * Real.sin θ) *
            (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n)
          • (D j f) (mulΩ x ξ)‖
        ≤ ∑ j : Fin n, ‖∑ ξ : Ω n,
            (((((ξ j : C) : ℝ) * Real.sin θ) *
              (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n)
              • (D j f) (mulΩ x ξ)‖ := by
            exact norm_sum_le (Finset.univ) (fun j : Fin n => ∑ ξ : Ω n,
              (((((ξ j : C) : ℝ) * Real.sin θ) *
                (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n)
                • (D j f) (mulΩ x ξ))
    _ ≤ ∑ j : Fin n, ∑ ξ : Ω n,
          ‖(((((ξ j : C) : ℝ) * Real.sin θ) *
              (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n)
            • (D j f) (mulΩ x ξ)‖ := by
            apply Finset.sum_le_sum
            intro j hj
            exact norm_sum_le (Finset.univ) (fun ξ : Ω n =>
              (((((ξ j : C) : ℝ) * Real.sin θ) *
                (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n)
                • (D j f) (mulΩ x ξ))
    _ ≤ ∑ j : Fin n, ∑ ξ : Ω n, ‖D j f (mulΩ x ξ)‖ := by
            apply Finset.sum_le_sum
            intro j hj
            apply Finset.sum_le_sum
            intro ξ hξ
            calc
              ‖(((((ξ j : C) : ℝ) * Real.sin θ) *
                  (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n)
                • (D j f) (mulΩ x ξ)‖
                  = |((((ξ j : C) : ℝ) * Real.sin θ) *
                      (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ)))) / (2 : ℝ) ^ n|
                      * ‖D j f (mulΩ x ξ)‖ := by
                      rw [norm_smul, Real.norm_eq_abs]
              _ ≤ 1 * ‖D j f (mulΩ x ξ)‖ := by
                      exact mul_le_mul_of_nonneg_right (abs_coeff_le_one θ ξ j) (norm_nonneg _)
              _ = ‖D j f (mulΩ x ξ)‖ := by simp


/-- `sinθ > 0` on the support of `ν`. -/
lemma sin_pos_on_Ioc (θ : ℝ) (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) : 0 < Real.sin θ := by
  have h0 : 0 < θ := hθ.1
  have hlt : θ < Real.pi := lt_of_le_of_lt hθ.2 (half_lt_self Real.pi_pos)
  exact Real.sin_pos_of_pos_of_lt_pi h0 hlt

/-- On the support of `ν`, `Jint = Jsmooth`. -/
lemma Jint_eq_Jsmooth_on {n : ℕ} (f : Ω n → X) (x : Ω n) (θ : ℝ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    Jint θ f x = Jsmooth θ f x := by
  exact Jint_eq_Jsmooth θ f x (ne_of_gt (sin_pos_on_Ioc θ hθ))

/-- `∫_ν Jint = ∫_ν Jsmooth`. -/
lemma lintegral_nu_Jint_eq_Jsmooth {n : ℕ} (f : Ω n → X) (x : Ω n) :
    (∫ θ : ℝ, Jint θ f x ∂thetaMeasure) = ∫ θ : ℝ, Jsmooth θ f x ∂thetaMeasure := by
  apply integral_congr_ae
  change ∀ᵐ θ : ℝ ∂thetaMeasure, Jint θ f x = Jsmooth θ f x
  rw [MeasureTheory.ae_iff]
  have hsub : {θ : ℝ | Jint θ f x ≠ Jsmooth θ f x} ⊆
      {θ : ℝ | θ ∉ Set.Ioc (0 : ℝ) (Real.pi / 2)} := by
    intro θ hθ
    by_contra hnot
    have hθi : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by simpa using hnot
    exact hθ (Jint_eq_Jsmooth_on f x θ hθi)
  apply measure_mono_null hsub
  unfold thetaMeasure thetaSet
  rw [Measure.smul_apply]
  change ENNReal.ofReal (2 / Real.pi) • (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2)))
    (Set.Ioc (0 : ℝ) (Real.pi / 2))ᶜ = 0
  rw [Measure.restrict_apply (measurableSet_Ioc.compl)]
  simp

/-- The pointwise identity in the smooth `ν`-form. -/
lemma identity_nu_smooth {n : ℕ} (f : Ω n → X) (x : Ω n) :
    f x - meanX f = (Real.pi / 2) • (∫ θ : ℝ, Jsmooth θ f x ∂thetaMeasure) := by
  calc
    f x - meanX f = (Real.pi / 2) • (∫ θ : ℝ, Jint θ f x ∂thetaMeasure) := identity_nu f x
    _ = (Real.pi / 2) • (∫ θ : ℝ, Jsmooth θ f x ∂thetaMeasure) := by
          rw [lintegral_nu_Jint_eq_Jsmooth f x]

/-- `ν` has full mass on `(0, π/2]`. -/
lemma thetaMeasure_Ioc : thetaMeasure (Set.Ioc (0 : ℝ) (Real.pi / 2)) = 1 := by
  unfold thetaMeasure thetaSet
  rw [Measure.smul_apply]
  rw [Measure.restrict_apply measurableSet_Ioc]
  rw [Set.inter_self]
  rw [Real.volume_Ioc]
  simp
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) / Real.pi)]
  rw [← ENNReal.ofReal_one]
  congr 1
  field_simp [Real.pi_ne_zero]

/-- The constant bound of `‖Jsmooth(·, x)‖` on the whole line. -/
noncomputable def dBound {n : ℕ} (f : Ω n → X) (x : Ω n) : ℝ :=
  ∑ j : Fin n, ∑ ξ : Ω n, ‖D j f (mulΩ x ξ)‖

lemma norm_Jsmooth_le_dBound {n : ℕ} (f : Ω n → X) (x : Ω n) (θ : ℝ) :
    ‖Jsmooth θ f x‖ ≤ dBound f x := by
  unfold dBound
  exact norm_Jsmooth_le f x θ

lemma dBound_nonneg {n : ℕ} (f : Ω n → X) (x : Ω n) : 0 ≤ dBound f x := by
  unfold dBound
  positivity



/-- `W(θ,x,ξ) := Σ_j δ_j(θ)(ξ) • D_j f(xξ)`, the integrand inside the biased expectation. -/
noncomputable def Wfun (θ : ℝ) {n : ℕ} (f : Ω n → X) (x ξ : Ω n) : X :=
  ∑ j : Fin n, (delta θ ξ j) • (D j f) (mulΩ x ξ)

/-- `meanReal` is the explicit uniform average over the cube. -/
lemma meanReal_eq_sum {n : ℕ} (F : Ω n → ℝ) :
    meanReal F = ∑ x : Ω n, ((1 / 2 : ℝ) ^ n) * F x := by
  unfold meanReal
  rw [integral_uniform_eq (n := n) F]
  simp

/-- Continuous dependence of `Jsmooth` on `θ`. -/
lemma continuous_Jsmooth {n : ℕ} (f : Ω n → X) (x : Ω n) : Continuous (fun θ : ℝ => Jsmooth θ f x) := by
  unfold Jsmooth
  continuity

lemma integrable_Jsmooth_nu {n : ℕ} (f : Ω n → X) (x : Ω n) :
    Integrable (fun θ : ℝ => Jsmooth θ f x) thetaMeasure := by
  refine Integrable.of_bound ?hf (dBound f x) ?hb
  · exact (continuous_Jsmooth f x).aestronglyMeasurable
  · apply ae_of_all
    intro θ
    exact norm_Jsmooth_le_dBound f x θ

lemma integrable_norm_Jsmooth_pow {n : ℕ} (f : Ω n → X) (x : Ω n) {p : ℝ} (hp0 : 0 ≤ p) :
    Integrable (fun θ : ℝ => ‖Jsmooth θ f x‖ ^ p) thetaMeasure := by
  refine Integrable.of_bound ?hf ((dBound f x) ^ p) ?hb
  · exact ((continuous_Jsmooth f x).norm.rpow_const (by intro θ; exact Or.inr hp0)).aestronglyMeasurable
  · apply ae_of_all
    intro θ
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (Jsmooth θ f x)) p)] using
      (Real.rpow_le_rpow (norm_nonneg (Jsmooth θ f x)) (norm_Jsmooth_le_dBound f x θ) hp0)

/-- Pointwise Jensen bound: `‖f x - meanX f‖^p ≤ (π/2)^p ∫_ν ‖Jsmooth(θ,x)‖^p`. -/
lemma pointwise_pow_le {n : ℕ} (f : Ω n → X) (x : Ω n) {p : ℝ} (hp1 : 1 ≤ p) :
    ‖f x - meanX f‖ ^ p ≤ (Real.pi / 2) ^ p * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ p ∂thetaMeasure) := by
  have hp0 : 0 ≤ p := by linarith
  -- norm inequality first
  have hnorm : ‖f x - meanX f‖ ≤ (Real.pi / 2) * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ∂thetaMeasure) := by
    calc
      ‖f x - meanX f‖ = ‖(Real.pi / 2) • (∫ θ : ℝ, Jsmooth θ f x ∂thetaMeasure)‖ := by
            rw [identity_nu_smooth f x]
      _ = (Real.pi / 2) * ‖∫ θ : ℝ, Jsmooth θ f x ∂thetaMeasure‖ := by
            rw [norm_smul]
            congr 1
            exact abs_of_pos (by positivity : 0 < Real.pi / 2)
      _ ≤ (Real.pi / 2) * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ∂thetaMeasure) := by
            exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity : 0 ≤ Real.pi / 2)
  have hnonneg_integral : 0 ≤ ∫ θ : ℝ, ‖Jsmooth θ f x‖ ∂thetaMeasure := by
    exact integral_nonneg (by intro θ; exact norm_nonneg _)
  have hjensen : (∫ θ : ℝ, ‖Jsmooth θ f x‖ ∂thetaMeasure) ^ p ≤
      ∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ p ∂thetaMeasure := by
    exact Commons.Analysis.Integral.jensen_rpow_prob (μ := thetaMeasure) hp1
      (by apply ae_of_all; intro θ; exact norm_nonneg (Jsmooth θ f x))
      (integrable_Jsmooth_nu f x).norm
      (integrable_norm_Jsmooth_pow f x hp0)
  calc
    ‖f x - meanX f‖ ^ p ≤ ((Real.pi / 2) * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ∂thetaMeasure)) ^ p := by
          exact Real.rpow_le_rpow (norm_nonneg _) hnorm hp0
    _ = (Real.pi / 2) ^ p * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ∂thetaMeasure) ^ p := by
          rw [Real.mul_rpow]
          positivity
          exact hnonneg_integral
    _ ≤ (Real.pi / 2) ^ p * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ p ∂thetaMeasure) := by
          exact mul_le_mul_of_nonneg_left hjensen (by positivity : 0 ≤ (Real.pi / 2) ^ p)

/-- Per-`x`, per-`θ` Jensen bound over the biased measure (for `θ` with `sinθ ≠ 0`). -/
lemma Jint_pow_le_expW {n : ℕ} (f : Ω n → X) (x : Ω n) {p : ℝ} (hp1 : 1 ≤ p) (θ : ℝ)
    (hsin : Real.sin θ ≠ 0) :
    ‖Jint θ f x‖ ^ p ≤ (∫ ξ : Ω n, ‖Wfun θ f x ξ‖ ^ p ∂(biasedMeasure (n := n) θ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hJ : Jint θ f x = ∫ ξ : Ω n, Wfun θ f x ξ ∂(biasedMeasure (n := n) θ) := rfl
  have h1 : ‖Jint θ f x‖ ≤ ∫ ξ : Ω n, ‖Wfun θ f x ξ‖ ∂(biasedMeasure (n := n) θ) := by
    rw [hJ]
    exact norm_integral_le_integral_norm _
  have h2 : (∫ ξ : Ω n, ‖Wfun θ f x ξ‖ ∂(biasedMeasure (n := n) θ)) ^ p ≤
      ∫ ξ : Ω n, ‖Wfun θ f x ξ‖ ^ p ∂(biasedMeasure (n := n) θ) := by
    exact Commons.Analysis.Integral.jensen_rpow_prob (μ := biasedMeasure (n := n) θ) hp1
      (by apply ae_of_all; intro ξ; exact norm_nonneg (Wfun θ f x ξ))
      (integrable_biased θ (fun ξ : Ω n => ‖Wfun θ f x ξ‖))
      (integrable_biased θ (fun ξ : Ω n => ‖Wfun θ f x ξ‖ ^ p))
  calc
    ‖Jint θ f x‖ ^ p ≤ (∫ ξ : Ω n, ‖Wfun θ f x ξ‖ ∂(biasedMeasure (n := n) θ)) ^ p := by
          exact Real.rpow_le_rpow (norm_nonneg _) h1 hp0
    _ ≤ ∫ ξ : Ω n, ‖Wfun θ f x ξ‖ ^ p ∂(biasedMeasure (n := n) θ) := h2


end RadType
end
