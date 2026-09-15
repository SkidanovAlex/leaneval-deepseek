import Mathlib
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_entire_extension_cube
import Submission.Commons.Analysis.Fourier.memLp_two_of_memLp_two_fourierInv
import Submission.Commons.Analysis.Fourier.cexp_sum_add_I_mul_eq

set_option maxHeartbeats 800000

namespace Commons.Analysis.Fourier

open MeasureTheory Metric FourierTransform
open scoped BigOperators ENNReal FourierTransform SchwartzMap

variable {d : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin d)

section Conversions

/-- Membership in `L²` is equivalent to finiteness of the lintegral of the square of the
extended norm. -/
lemma memLp_two_iff_lintegral_enorm_sq_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂μ < ⊤ := by
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num),
    show ((2 : ℝ≥0∞).toReal) = 2 by norm_num]
  exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩

/-- For a nonnegative real-valued function, the Bochner integral agrees with the `toReal` of the
lintegral, including in the divergent case where both sides are `0`. -/
lemma integral_norm_sq_eq_toReal_lintegral_enorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂μ).toReal := by
  have hmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) μ := hf.norm.pow 2
  have hnn : ∀ x, ENNReal.ofReal (‖f x‖ ^ 2) = ‖f x‖ₑ ^ (2:ℝ) := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hmeas]
  congr 1
  exact lintegral_congr_ae (Filter.Eventually.of_forall fun x => hnn x)

end Conversions

section Phase

lemma inner_eq_sum_mul (a x : V) : inner ℝ a x = ∑ i : Fin d, x i * a i := by
  rw [PiLp.inner_apply]; simp

lemma fourierInv_apply_eq_integral_exp (G : V → ℂ) (x : V) :
    𝓕⁻ G x = ∫ a, Complex.exp (↑(2 * Real.pi * inner ℝ a x) * Complex.I) * G a := by
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul]

lemma inner_cast_eq_sum (a x : V) :
    (inner ℝ a x : ℂ) = ∑ i : Fin d, (x i : ℂ) * (a i : ℂ) := by
  rw [inner_eq_sum_mul]
  push_cast
  rfl

lemma exp_inner_eq (a x : V) :
    Complex.exp (↑(2 * Real.pi * inner ℝ a x) * Complex.I)
      = Complex.exp (2 * Real.pi * Complex.I * (∑ i : Fin d, (x i : ℂ) * (a i : ℂ))) := by
  have h : (↑(2 * Real.pi * inner ℝ a x) : ℂ)
      = 2 * Real.pi * (∑ i : Fin d, (x i : ℂ) * (a i : ℂ)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, inner_cast_eq_sum]
    ac_rfl
  rw [show (↑(2 * Real.pi * inner ℝ a x) * Complex.I : ℂ)
      = 2 * Real.pi * Complex.I * (∑ i : Fin d, (x i : ℂ) * (a i : ℂ)) by rw [h]; ring]

end Phase

section FTLaplace

/-- The Fourier--Laplace transform of `H` at `x + iy` is the (inverse) Fourier transform of
`G a = H a * exp (-(2π) ∑ᵢ yᵢ aᵢ)`. -/
lemma FT_apply_add_I_mul_eq (H : V → ℂ) (x y : V) :
    (∫ a, H a * Complex.exp (2 * Real.pi * Complex.I *
        (∑ i : Fin d, ((x i : ℂ) + (y i : ℂ) * Complex.I) * (a i : ℂ))))
      = 𝓕⁻ (fun a => H a * (Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i) : ℂ)) x := by
  rw [fourierInv_apply_eq_integral_exp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only []
  rw [cexp_sum_add_I_mul_eq, exp_inner_eq]
  ring

end FTLaplace

section Plancherel

/-- `𝓕⁻ G` is continuous when `G` is integrable. -/
lemma continuous_fourierInv_of_integrable_euclidean {G : V → ℂ} (hG : Integrable G) :
    Continuous (fun x : V => 𝓕⁻ G x) := by
  have h1 : MemLp G 1 (volume : Measure V) := memLp_one_iff_integrable.mpr hG
  have heq : (fun x : V => 𝓕⁻ G x) = ⇑(Real.Lp.fourierTransformInv h1.toLp) := by
    rw [Real.Lp.fourierTransformInv_toLp h1]
  rw [heq]
  exact (Real.Lp.fourierTransformInv h1.toLp).continuous

/-- **Complex Plancherel for integrable functions.** For any integrable `G`, the `lintegral`s of
the squares of the extended norms of `G` and of its inverse Fourier transform agree (both may be
infinite simultaneously). -/
lemma lintegral_enorm_sq_fourierInv_eq_of_integrable {G : V → ℂ} (hG : Integrable G) :
    ∫⁻ x, ‖𝓕⁻ G x‖ₑ ^ (2:ℝ) = ∫⁻ a, ‖G a‖ₑ ^ (2:ℝ) := by
  have hGmeas : AEStronglyMeasurable G (volume : Measure V) := hG.aestronglyMeasurable
  have hFmeas : AEStronglyMeasurable (fun x : V => 𝓕⁻ G x) (volume : Measure V) :=
    (continuous_fourierInv_of_integrable_euclidean hG).aestronglyMeasurable
  by_cases hfin : ∫⁻ a, ‖G a‖ₑ ^ (2:ℝ) < ⊤
  · have h2 : MemLp G 2 (volume : Measure V) :=
      (memLp_two_iff_lintegral_enorm_sq_lt_top hGmeas).mpr hfin
    have h1 : MemLp G 1 (volume : Measure V) := memLp_one_iff_integrable.mpr hG
    exact LogvinenkoSereda.lintegral_norm_sq_fourierInv h1 h2
  · have htop : ∫⁻ a, ‖G a‖ₑ ^ (2:ℝ) = ⊤ := top_unique (le_of_not_gt hfin)
    rw [htop]
    by_contra hne
    have hlt : ∫⁻ x, ‖𝓕⁻ G x‖ₑ ^ (2:ℝ) < ⊤ := lt_top_iff_ne_top.mpr hne
    have hmem : MemLp (fun x : V => 𝓕⁻ G x) 2 (volume : Measure V) :=
      (memLp_two_iff_lintegral_enorm_sq_lt_top hFmeas).mpr hlt
    have hmemG : MemLp G 2 (volume : Measure V) :=
      memLp_two_of_memLp_two_fourierInv hG hmem
    exact absurd ((memLp_two_iff_lintegral_enorm_sq_lt_top hGmeas).mp hmemG)
      (not_lt.mpr (le_of_eq htop.symm))

end Plancherel

section Main

/-- Bound on the exponential weight on the band cube. -/
lemma exp_neg_sum_le {σ : ℝ} {y : Fin d → ℝ} {a : V}
    (ha : a ∈ LogvinenkoSereda.bandCube d σ) :
    Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i)
      ≤ Real.exp (2 * Real.pi * σ * ∑ i : Fin d, |y i|) := by
  have hsum : |∑ i : Fin d, y i * a i| ≤ σ * ∑ i : Fin d, |y i| := by
    calc |∑ i : Fin d, y i * a i| ≤ ∑ i : Fin d, |y i * a i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin d, |y i| * |a i| := by simp [abs_mul]
      _ ≤ ∑ i : Fin d, |y i| * σ := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _)
      _ = σ * ∑ i : Fin d, |y i| := by rw [← Finset.sum_mul, mul_comm]
  have hle : -(2 * Real.pi) * ∑ i : Fin d, y i * a i
      ≤ 2 * Real.pi * σ * ∑ i : Fin d, |y i| := by
    have h1 : -(2 * Real.pi) * ∑ i : Fin d, y i * a i
        ≤ 2 * Real.pi * |∑ i : Fin d, y i * a i| := by
      have := neg_le_abs (∑ i : Fin d, y i * a i)
      nlinarith [abs_nonneg (∑ i : Fin d, y i * a i), Real.pi_pos]
    have h2 : 2 * Real.pi * |∑ i : Fin d, y i * a i|
        ≤ 2 * Real.pi * (σ * ∑ i : Fin d, |y i|) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    have h3 : 2 * Real.pi * (σ * ∑ i : Fin d, |y i|)
        = 2 * Real.pi * σ * ∑ i : Fin d, |y i| := by ring
    linarith [h2.trans_eq h3]
  exact Real.exp_le_exp.mpr hle

end Main

/-- `‖(Real.exp r : ℂ)‖ = Real.exp r`. -/
lemma norm_ofReal_exp (r : ℝ) : ‖(Real.exp r : ℂ)‖ = Real.exp r := by
  rw [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re]

/-- **Complex Plancherel along a horizontal slice of the Fourier-Laplace transform.** For `H` an
`L¹` function on `ℝᵈ` a.e. supported in the band cube of radius `σ ≥ 0`, and every real `y`,
`∫_x ‖FT (x + i y)‖² = ∫_ξ ‖H ξ‖² exp(-4π ∑ᵢ yᵢ ξᵢ)`, where `FT z = ∫_ξ H ξ e^{2πi z · ξ}`. -/
theorem FT_strip_integral_eq {d : ℕ} {σ : ℝ} (hσ : 0 ≤ σ)
    {H : EuclideanSpace ℝ (Fin d) → ℂ} (hH : MeasureTheory.Integrable H)
    (hsupp : ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      a ∉ {a : EuclideanSpace ℝ (Fin d) | ∀ i, |a i| ≤ σ} → H a = 0)
    (y : Fin d → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin d),
        ‖∫ a : EuclideanSpace ℝ (Fin d), H a * Complex.exp
            (2 * Real.pi * Complex.I *
              (∑ i, ((x i : ℂ) + (y i : ℂ) * Complex.I) * (a i : ℂ)))‖ ^ 2)
      = ∫ a : EuclideanSpace ℝ (Fin d),
          ‖H a‖ ^ 2 * Real.exp (-(4 * Real.pi) * (∑ i, y i * a i)) := by
  let F : EuclideanSpace ℝ (Fin d) → ℂ := fun a => H a * (Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i) : ℂ)
  have hsum_cont : Continuous (fun a : EuclideanSpace ℝ (Fin d) => ∑ i : Fin d, y i * a i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (EuclideanSpace.proj i).continuous
  have hc_cont : Continuous (fun a : EuclideanSpace ℝ (Fin d) =>
      (Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hsum_cont))
  have hmeasF : AEStronglyMeasurable F (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    simp only [F]
    exact hH.aestronglyMeasurable.mul hc_cont.aestronglyMeasurable
  have hbound : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ‖F a‖ ≤ Real.exp (2 * Real.pi * σ * ∑ i : Fin d, |y i|) * ‖H a‖ := by
    filter_upwards [hsupp] with a ha
    by_cases hmem : a ∈ LogvinenkoSereda.bandCube d σ
    · have hnorm : ‖F a‖ = ‖H a‖ * Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i) := by
        simp only [F]
        rw [norm_mul, norm_ofReal_exp]
      rw [hnorm]
      have hle := exp_neg_sum_le (d := d) (y := y) hmem
      nlinarith [norm_nonneg (H a), Real.exp_pos (2 * Real.pi * σ * ∑ i : Fin d, |y i|)]
    · simp only [F]
      rw [ha hmem]
      simp
  have hFint : Integrable F :=
    (hH.norm.const_mul (Real.exp (2 * Real.pi * σ * ∑ i : Fin d, |y i|))).mono' hmeasF hbound
  have hLHS : (∫ x : EuclideanSpace ℝ (Fin d), ‖∫ a : EuclideanSpace ℝ (Fin d), H a * Complex.exp (2 * Real.pi * Complex.I *
        (∑ i : Fin d, ((x i : ℂ) + (y i : ℂ) * Complex.I) * (a i : ℂ)))‖ ^ 2)
      = ∫ x : EuclideanSpace ℝ (Fin d), ‖𝓕⁻ F x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [F]
    rw [FT_apply_add_I_mul_eq]
  rw [hLHS]
  have hFmeas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) => 𝓕⁻ F x) (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (continuous_fourierInv_of_integrable_euclidean hFint).aestronglyMeasurable
  rw [integral_norm_sq_eq_toReal_lintegral_enorm_sq hFmeas,
    lintegral_enorm_sq_fourierInv_eq_of_integrable hFint,
    ← integral_norm_sq_eq_toReal_lintegral_enorm_sq hmeasF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hsq : (Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i)) ^ 2
      = Real.exp (-(4 * Real.pi) * (∑ i : Fin d, y i * a i)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [F]
  rw [norm_mul, norm_ofReal_exp, mul_pow, hsq]

end Commons.Analysis.Fourier
