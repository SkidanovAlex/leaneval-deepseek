import Mathlib
import Submission.Commons.Analysis.Fourier.nested_indicator_l2_bound
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped ENNReal FourierTransform ComplexInnerProductSpace Topology

set_option maxHeartbeats 8000000

noncomputable section

lemma enorm_eq_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  simp [enorm_eq_nnnorm]

lemma enorm_eq_ofReal_norm_real (z : ℝ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ :=
  (ofReal_norm (x := z)).symm

/-- Norm of a real number seen as a complex number. -/
lemma norm_ofReal_eq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

lemma lintegral_enorm_fourierInv_eq {h : ℝ → ℂ} (h1 : MemLp h 1 (volume : Measure ℝ))
    (h2 : MemLp h 2 (volume : Measure ℝ)) :
    (∫⁻ x : ℝ, ‖𝓕⁻ h x‖ₑ ^ (2:ℝ)) = ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2:ℝ) := by
  simp only [enorm_eq_ofReal_norm]
  exact lintegral_fourierInv_eq h1 h2

lemma integrable_comp_neg {g : ℝ → ℂ} (h : Integrable g (volume : Measure ℝ)) :
    Integrable (fun x : ℝ => g (-x)) (volume : Measure ℝ) := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))

lemma memLp_comp_neg {p : ℝ≥0∞} {g : ℝ → ℂ} (h : MemLp g p (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => g (-x)) p (volume : Measure ℝ) :=
  h.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))

lemma fourier_eq_fourierInv_comp_neg (f : ℝ → ℂ) (x : ℝ) :
    (𝓕 f) x = 𝓕⁻ (fun y : ℝ => f (-y)) x := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  simp

lemma lintegral_enorm_fourier_eq {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    (∫⁻ x : ℝ, ‖(𝓕 f) x‖ₑ ^ (2:ℝ)) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
  have h1 : MemLp (fun y : ℝ => f (-y)) 1 volume :=
    memLp_comp_neg (memLp_one_iff_integrable.mpr hf1)
  have h2 : MemLp (fun y : ℝ => f (-y)) 2 volume := memLp_comp_neg hf2
  calc (∫⁻ x : ℝ, ‖(𝓕 f) x‖ₑ ^ (2:ℝ))
      = ∫⁻ x : ℝ, ‖𝓕⁻ (fun y : ℝ => f (-y)) x‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr (fun x => ?_)
        rw [fourier_eq_fourierInv_comp_neg]
    _ = ∫⁻ x : ℝ, ‖(fun y : ℝ => f (-y)) x‖ₑ ^ (2:ℝ) :=
        lintegral_enorm_fourierInv_eq h1 h2
    _ = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) :=
        lintegral_neg_eq_self (fun x : ℝ => ‖f x‖ₑ ^ (2:ℝ))

/-- The band-pass operator on the frequency set `C`. -/
noncomputable def bandOp (C : Set ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  𝓕⁻ (Set.indicator C (𝓕 f)) x

lemma norm_fourier_le (H : ℝ → ℂ) (ξ : ℝ) : ‖(𝓕 H) ξ‖ ≤ ∫ x, ‖H x‖ := by
  rw [Real.fourier_eq']
  show ‖∫ v, Complex.exp ((↑(-2 * Real.pi * inner ℝ v ξ) : ℂ) * Complex.I) • H v‖
      ≤ ∫ x, ‖H x‖
  calc ‖∫ v, Complex.exp ((↑(-2 * Real.pi * inner ℝ v ξ) : ℂ) * Complex.I) • H v‖
      ≤ ∫ v, ‖Complex.exp ((↑(-2 * Real.pi * inner ℝ v ξ) : ℂ) * Complex.I) • H v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v, ‖H v‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        show ‖Complex.exp ((↑(-2 * Real.pi * inner ℝ v ξ) : ℂ) * Complex.I) • H v‖ = ‖H v‖
        rw [norm_smul, Complex.norm_exp]
        have hre : (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I : ℂ).re = 0 := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
          ring
        rw [hre, Real.exp_zero, one_mul]

lemma memLp_one_indicator_fourier (C : Set ℝ) (hC : MeasurableSet C)
    (hCb : Bornology.IsBounded C) (f : ℝ → ℂ) (hf : Integrable f) :
    MemLp (Set.indicator C (𝓕 f)) 1 volume := by
  have hfin : volume C < ⊤ := hCb.measure_lt_top
  have hg : MemLp (fun x : ℝ => C.indicator (fun _ => ((∫ y, ‖f y‖ : ℝ) : ℂ)) x) 1 volume :=
    memLp_indicator_const 1 hC _ (Or.inr hfin.ne)
  refine MemLp.of_le hg ?_ ?_
  · exact ((VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) hf).measurable.indicator hC).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have hcast : ‖(↑(∫ y, ‖f y‖) : ℂ)‖ = ∫ y, ‖f y‖ := by
        rw [show ‖(↑(∫ y, ‖f y‖) : ℂ)‖ = |∫ y, ‖f y‖| by simp,
          abs_of_nonneg (by positivity)]
      rw [hcast]
      exact norm_fourier_le f x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]

lemma memLp_two_indicator_fourier (C : Set ℝ) (hC : MeasurableSet C)
    (hCb : Bornology.IsBounded C) (f : ℝ → ℂ) (hf : Integrable f) :
    MemLp (Set.indicator C (𝓕 f)) 2 volume := by
  have hfin : volume C < ⊤ := hCb.measure_lt_top
  have hg : MemLp (fun x : ℝ => C.indicator (fun _ => ((∫ y, ‖f y‖ : ℝ) : ℂ)) x) 2 volume :=
    memLp_indicator_const 2 hC _ (Or.inr hfin.ne)
  refine MemLp.of_le hg ?_ ?_
  · exact ((VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) hf).measurable.indicator hC).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have hcast : ‖(↑(∫ y, ‖f y‖) : ℂ)‖ = ∫ y, ‖f y‖ := by
        rw [show ‖(↑(∫ y, ‖f y‖) : ℂ)‖ = |∫ y, ‖f y‖| by simp,
          abs_of_nonneg (by positivity)]
      rw [hcast]
      exact norm_fourier_le f x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]

lemma continuous_fourierInv_of_integrable (H : ℝ → ℂ) (hH : Integrable H) :
    Continuous (fun x : ℝ => (𝓕⁻ H) x) :=
  VectorFourier.fourierIntegral_continuous (μ := volume) (L := -innerₗ ℝ)
    Real.continuous_fourierChar (by fun_prop) hH

lemma bandOp_cont (C : Set ℝ) (hC : MeasurableSet C) (hCb : Bornology.IsBounded C)
    (f : ℝ → ℂ) (hf : Integrable f) : Continuous (bandOp C f) :=
  continuous_fourierInv_of_integrable _ (memLp_one_iff_integrable.mp (memLp_one_indicator_fourier C hC hCb f hf))

lemma lintegral_enorm_indicator_le (C : Set ℝ) (g : ℝ → ℂ) :
    (∫⁻ x : ℝ, ‖Set.indicator C g x‖ₑ ^ (2:ℝ)) ≤ ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
  refine lintegral_mono (fun x => ?_)
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  by_cases hx : x ∈ C
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; simp

lemma bandOp_lintegral (C : Set ℝ) (hC : MeasurableSet C) (hCb : Bornology.IsBounded C)
    (f : ℝ → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    (∫⁻ x : ℝ, ‖bandOp C f x‖ₑ ^ (2:ℝ)) ≤ ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
  have h1 := memLp_one_indicator_fourier C hC hCb f hf1
  have h2 := memLp_two_indicator_fourier C hC hCb f hf1
  calc (∫⁻ x : ℝ, ‖bandOp C f x‖ₑ ^ (2:ℝ))
      = ∫⁻ x : ℝ, ‖𝓕⁻ (Set.indicator C (𝓕 f)) x‖ₑ ^ (2:ℝ) := rfl
    _ = ∫⁻ x : ℝ, ‖Set.indicator C (𝓕 f) x‖ₑ ^ (2:ℝ) := lintegral_enorm_fourierInv_eq h1 h2
    _ ≤ ∫⁻ x : ℝ, ‖(𝓕 f) x‖ₑ ^ (2:ℝ) := lintegral_enorm_indicator_le C (𝓕 f)
    _ = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := lintegral_enorm_fourier_eq hf1 hf2

lemma bandOp_memLp (C : Set ℝ) (hC : MeasurableSet C) (hCb : Bornology.IsBounded C)
    (f : ℝ → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    MemLp (bandOp C f) 2 volume := by
  have h2 : eLpNorm (bandOp C f) 2 volume ≤ eLpNorm f 2 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
        (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (bandOp_cont C hC hCb f hf1).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
        (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hf2.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_le_rpow (bandOp_lintegral C hC hCb f hf1 hf2) (by norm_num)
  exact lt_of_le_of_lt h2 hf2.eLpNorm_lt_top

/-- `∫ x, v x * 𝓕⁻ H x = ∫ ξ, H ξ * 𝓕 v (-ξ)`: the "multiplication formula" for the inverse
Fourier transform, for `L¹ ∩ L²` functions. -/
lemma integral_mul_fourierInv (H v : ℝ → ℂ) (hH1 : Integrable H) (hv1 : Integrable v)
    (hH2 : MemLp H 2 (volume : Measure ℝ)) (hv2 : MemLp v 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, v x * 𝓕⁻ H x) = ∫ ξ : ℝ, H ξ * (𝓕 v) (-ξ) := by
  have hpt : ∀ x : ℝ, 𝓕⁻ H x
      = ∫ ξ : ℝ, Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • H ξ := by
    intro x
    rw [Real.fourierInv_eq']
  have hG : Integrable (fun p : ℝ × ℝ => v p.1 *
      (Complex.exp ((↑(2 * Real.pi * inner ℝ p.2 p.1) : ℂ) * Complex.I) • H p.2))
      (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖v p.1‖ * ‖H p.2‖) (volume.prod volume) :=
      (hv1.norm).mul_prod hH1.norm
    refine Integrable.mono' hdom ?_ ?_
    · have hexp : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          Complex.exp ((↑(2 * Real.pi * inner ℝ p.2 p.1) : ℂ) * Complex.I))
          (volume.prod volume) :=
        (by fun_prop : Continuous (fun p : ℝ × ℝ =>
          Complex.exp ((↑(2 * Real.pi * inner ℝ p.2 p.1) : ℂ) * Complex.I))).aestronglyMeasurable
      exact AEStronglyMeasurable.mul
        (hv2.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
        (hexp.smul (hH2.aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))))
    · filter_upwards with p
      rw [norm_mul, norm_smul, Complex.norm_exp]
      have hre : (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I : ℂ).re = 0 := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [hre, Real.exp_zero, one_mul]
  have hfou : ∀ ξ : ℝ, (𝓕 v) (-ξ)
      = ∫ x : ℝ, v x * Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) := by
    intro ξ
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with x
    show Complex.exp ((↑(-2 * Real.pi * inner ℝ x (-ξ)) : ℂ) * Complex.I) • v x
        = v x * Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)
    rw [smul_eq_mul, Real.inner_apply, Real.inner_apply]
    have hexp : Complex.exp ((↑(-2 * Real.pi * (x * -ξ)) : ℂ) * Complex.I)
        = Complex.exp ((↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [hexp, mul_comm]
  have hstep1 : (∫ x : ℝ, v x * 𝓕⁻ H x)
      = ∫ x : ℝ, ∫ ξ : ℝ, v x *
          (Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • H ξ) := by
    apply integral_congr_ae
    filter_upwards with x
    show v x * 𝓕⁻ H x
        = ∫ ξ : ℝ, v x * (Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • H ξ)
    rw [hpt x, integral_const_mul]
  have hstep2 : (∫ x : ℝ, ∫ ξ : ℝ, v x *
        (Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • H ξ))
      = ∫ ξ : ℝ, ∫ x : ℝ, v x *
        (Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • H ξ) :=
    integral_integral_swap hG
  have hstep3 : (∫ ξ : ℝ, ∫ x : ℝ, v x *
        (Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • H ξ))
      = ∫ ξ : ℝ, (∫ x : ℝ, v x *
          Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)) * H ξ := by
    apply integral_congr_ae
    filter_upwards with ξ
    show (∫ x : ℝ, v x * (Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • H ξ))
        = (∫ x : ℝ, v x * Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)) * H ξ
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul]
    ring
  have hstep4 : (∫ ξ : ℝ, (∫ x : ℝ, v x *
          Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)) * H ξ)
      = ∫ ξ : ℝ, H ξ * (𝓕 v) (-ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    show (∫ x : ℝ, v x * Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)) * H ξ
        = H ξ * (𝓕 v) (-ξ)
    rw [hfou ξ]
    ring
  rw [hstep1, hstep2, hstep3, hstep4]

lemma eLpNorm_two_eq (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    eLpNorm f 2 (volume : Measure ℝ) = (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num

lemma memLp_fourier {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume := by
  have hcont : Continuous (fun x : ℝ => (𝓕 f) x) :=
    VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) hf1
  rw [memLp_iff, eLpNorm_two_eq _ hcont.aestronglyMeasurable, lintegral_enorm_fourier_eq hf1 hf2,
    ← eLpNorm_two_eq _ hf2.aestronglyMeasurable]
  exact hf2.eLpNorm_lt_top

lemma memLp_fourierInv {h : ℝ → ℂ} (h1 : MemLp h 1 volume) (h2 : MemLp h 2 volume) :
    MemLp (𝓕⁻ h) 2 volume := by
  have hint : Integrable h := memLp_one_iff_integrable.mp h1
  have hcont : Continuous (fun x : ℝ => (𝓕⁻ h) x) :=
    VectorFourier.fourierIntegral_continuous (μ := volume) (L := -innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) hint
  rw [memLp_iff, eLpNorm_two_eq _ hcont.aestronglyMeasurable, lintegral_enorm_fourierInv_eq h1 h2,
    ← eLpNorm_two_eq _ h2.aestronglyMeasurable]
  exact h2.eLpNorm_lt_top

/-- Complexification preserves `MemLp`. -/
lemma memLp_ofReal {p : ℝ≥0∞} {g : ℝ → ℝ} (h : MemLp g p (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => (g x : ℂ)) p (volume : Measure ℝ) := by
  refine MemLp.of_le h ?_ ?_
  · exact (Complex.measurable_ofReal.comp_aemeasurable h.aemeasurable).aestronglyMeasurable
  · filter_upwards with x
    rw [show ‖(g x : ℂ)‖ = |g x| by simp]
    rfl

/-- **Plancherel pairing for `L¹ ∩ L²` functions** on `ℝ`:
`∫ ξ, (𝓕 u) ξ * conj ((𝓕 v) ξ) = ∫ x, u x * conj (v x)`. -/
lemma integral_fourier_mul_star (u v : ℝ → ℂ) (hu1 : Integrable u) (hv1 : Integrable v)
    (hu2 : MemLp u 2 (volume : Measure ℝ)) (hv2 : MemLp v 2 (volume : Measure ℝ)) :
    (∫ ξ : ℝ, (𝓕 u) ξ * star ((𝓕 v) ξ)) = ∫ x : ℝ, u x * star (v x) := by
  have hU : ((hu2.toLp u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] u :=
    MemLp.coeFn_toLp hu2
  have hV : ((hv2.toLp v : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] v :=
    MemLp.coeFn_toLp hv2
  have hFu : ((𝓕 (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (fun ξ => 𝓕 u ξ) :=
    fourier_toLp_ae_eq_fourier_of_memLp (memLp_one_iff_integrable.mpr hu1) hu2
  have hFv : ((𝓕 (hv2.toLp v) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (fun ξ => 𝓕 v ξ) :=
    fourier_toLp_ae_eq_fourier_of_memLp (memLp_one_iff_integrable.mpr hv1) hv2
  have h1 : ⟪hv2.toLp v, hu2.toLp u⟫ = ∫ x : ℝ, u x * star (v x) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hU, hV] with x hx1 hx2
    rw [hx1, hx2]
    simp only [RCLike.inner_apply, starRingEnd_apply]
  have h2 : ⟪𝓕 (hv2.toLp v), 𝓕 (hu2.toLp u)⟫ = ∫ ξ : ℝ, (𝓕 u) ξ * star ((𝓕 v) ξ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hFu, hFv] with ξ hx1 hx2
    rw [hx1, hx2]
    simp only [RCLike.inner_apply, starRingEnd_apply]
  rw [← h1, ← h2, MeasureTheory.Lp.inner_fourier_eq]

/-- `∫⁻ ‖g‖ₑ² = ofReal (∫ ‖g‖²)` for real-valued `g ∈ L²`. -/
lemma lintegral_enorm_rpow_two_real {g : ℝ → ℝ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    (∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) ∂volume)
      = ENNReal.ofReal (∫ x : ℝ, ‖g x‖ ^ (2:ℝ)) := by
  have h1 : MemLp (fun x : ℝ => ((g x : ℝ) : ℂ)) 2 volume := memLp_ofReal hg
  have h2 := NestedIndicator.lintegral_enorm_rpow_two volume h1
  rw [show (∫⁻ x : ℝ, ‖((g x : ℝ) : ℂ)‖ₑ ^ (2:ℝ) ∂volume)
      = ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) ∂volume from
    lintegral_congr (fun x => by
      rw [enorm_eq_ofReal_norm, norm_ofReal_eq, enorm_eq_ofReal_norm_real,
        Real.norm_eq_abs])] at h2
  rw [show (∫ x : ℝ, ‖((g x : ℝ) : ℂ)‖ ^ (2:ℝ)) = ∫ x : ℝ, ‖g x‖ ^ (2:ℝ) from
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by
      simp only [norm_ofReal_eq, Real.norm_eq_abs]))] at h2
  exact h2

/-- **Linearisation bound.**  For a nonnegative `L¹ ∩ L²` weight `w`, the maximal function of the
band-pass operators is dominated by the `L²`-norms of `w` and of `f`. -/
lemma linearization_bound {M : ℕ} (hM : 1 ≤ M) (C : Fin M → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (C i))
    (hnest : ∀ i j : Fin M, i ≤ j → C j ⊆ C i) (hbd : ∀ i, Bornology.IsBounded (C i))
    (f : ℝ → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (w : ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : Integrable w) (hw2 : MemLp w 2 volume) :
    (∫ x : ℝ, w x * (⨆ i : Fin M, ‖bandOp (C i) f x‖))
      ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, w x ^ 2)
          * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
  classical
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  set F : Fin M → ℝ → ℂ := fun i => bandOp (C i) f with hF
  have hFcont : ∀ i, Continuous (F i) := fun i => bandOp_cont (C i) (hmeas i) (hbd i) f hf1
  have hFmem : ∀ i, MemLp (F i) 2 volume :=
    fun i => bandOp_memLp (C i) (hmeas i) (hbd i) f hf1 hf2
  set G : ℝ → ℝ := fun x => ⨆ i : Fin M, ‖F i x‖ with hG
  have hGbdd : ∀ x : ℝ, BddAbove (Set.range fun i : Fin M => ‖F i x‖) :=
    fun x => (Set.finite_range _).bddAbove
  have hGle : ∀ x (i : Fin M), ‖F i x‖ ≤ G x := fun x i => le_ciSup (hGbdd x) i
  have hGmeas : Measurable G := by
    rw [hG]
    exact Measurable.iSup (fun i => (hFcont i).norm.measurable)
  have hGnonneg : ∀ x, 0 ≤ G x :=
    fun x => le_trans (norm_nonneg _) (hGle x ⟨0, hM⟩)
  -- the phase
  set sg : Fin M → ℝ → ℂ := fun i x => if F i x = 0 then 1
      else (starRingEnd ℂ) (F i x) / ((‖F i x‖ : ℝ) : ℂ) with hsg
  have hsg_apply : ∀ i x, sg i x
      = if F i x = 0 then 1 else (starRingEnd ℂ) (F i x) / ((‖F i x‖ : ℝ) : ℂ) :=
    fun i x => rfl
  have hsg_meas : ∀ i, Measurable (sg i) := by
    intro i
    rw [hsg]
    refine Measurable.ite ?_ measurable_const ?_
    · exact (measurableSet_singleton (0:ℂ)).preimage (hFcont i).measurable
    · exact (Complex.continuous_conj.comp (hFcont i)).measurable.div
        (Complex.measurable_ofReal.comp (hFcont i).norm.measurable)
  have hsg_norm : ∀ i x, ‖sg i x‖ ≤ 1 := by
    intro i x
    rw [hsg_apply]
    by_cases h : F i x = 0
    · rw [if_pos h]; simp
    · rw [if_neg h, norm_div, Complex.norm_conj]
      have hpos : (0:ℝ) < ‖F i x‖ := norm_pos_iff.mpr h
      rw [show ‖((‖F i x‖ : ℝ) : ℂ)‖ = ‖F i x‖ from by
        rw [show ‖((‖F i x‖ : ℝ) : ℂ)‖ = |‖F i x‖| by simp, abs_of_nonneg (norm_nonneg _)],
        div_self (ne_of_gt hpos)]
  have hsg_mul : ∀ i x, sg i x * F i x = ((‖F i x‖ : ℝ) : ℂ) := by
    intro i x
    rw [hsg_apply]
    by_cases h : F i x = 0
    · rw [if_pos h, h, norm_zero]; simp
    · rw [if_neg h, div_mul_eq_mul_div]
      rw [show (starRingEnd ℂ) (F i x) * F i x
          = ((‖F i x‖ : ℝ) : ℂ) * ((‖F i x‖ : ℝ) : ℂ) from by
        rw [RCLike.conj_mul, sq]
        rfl]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_div]
      congr 1
      field_simp
  -- the partition
  set A : Fin M → ℝ → ℝ := fun i x => if (∀ j : Fin M, ‖F j x‖ ≤ ‖F i x‖) then 1 else 0
    with hA
  set B : Fin M → ℝ → ℝ := fun i x => ∏ j : Fin M, (if i < j ∧ G x = ‖F j x‖ then 0 else 1)
    with hB
  set wi : Fin M → ℝ → ℂ := fun i x => (w x : ℂ) * (A i x : ℂ) * (B i x : ℂ) * sg i x
    with hwi
  have hA_meas : ∀ i, Measurable (A i) := by
    intro i
    rw [hA]
    refine Measurable.ite ?_ measurable_const measurable_const
    rw [show {x : ℝ | ∀ j : Fin M, ‖F j x‖ ≤ ‖F i x‖}
        = ⋂ j : Fin M, {x : ℝ | ‖F j x‖ ≤ ‖F i x‖} from by ext x; simp]
    exact MeasurableSet.iInter
      (fun j => measurableSet_le (hFcont j).norm.measurable (hFcont i).norm.measurable)
  have hB_meas : ∀ i, Measurable (B i) := by
    intro i
    rw [hB]
    refine Finset.measurable_prod _ (fun j _ => ?_)
    refine Measurable.ite ?_ measurable_const measurable_const
    by_cases hij : i < j
    · rw [show {x : ℝ | i < j ∧ G x = ‖F j x‖} = {x : ℝ | G x = ‖F j x‖} from by
        ext x; simp [hij]]
      exact measurableSet_eq_fun hGmeas (hFcont j).norm.measurable
    · rw [show {x : ℝ | i < j ∧ G x = ‖F j x‖} = ∅ from by
        ext x; simp [hij]]
      exact MeasurableSet.empty
  have hA_le : ∀ i x, A i x ≤ 1 := by
    intro i x; simp only [hA]; split <;> norm_num
  have hA_nonneg : ∀ i x, 0 ≤ A i x := by
    intro i x; simp only [hA]; split <;> norm_num
  have hB_le : ∀ i x, B i x ≤ 1 := by
    intro i x
    rw [hB]
    refine Finset.prod_le_one₀ (fun j _ => ?_) (fun j _ => ?_)
    · by_cases h : i < j ∧ G x = ‖F j x‖ <;> simp [h]
    · by_cases h : i < j ∧ G x = ‖F j x‖ <;> simp [h]
  have hB_nonneg : ∀ i x, 0 ≤ B i x := by
    intro i x
    rw [hB]
    refine Finset.prod_nonneg (fun j _ => ?_)
    by_cases h : i < j ∧ G x = ‖F j x‖ <;> simp [h]
  have hwi_bound : ∀ i x, ‖wi i x‖ ≤ w x := by
    intro i x
    rw [hwi]
    have h1 : ‖((A i x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [show ‖((A i x : ℝ) : ℂ)‖ = |A i x| by simp, abs_of_nonneg (hA_nonneg i x)]
      exact hA_le i x
    have h2 : ‖((B i x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [show ‖((B i x : ℝ) : ℂ)‖ = |B i x| by simp, abs_of_nonneg (hB_nonneg i x)]
      exact hB_le i x
    have h3 : ‖((w x : ℝ) : ℂ)‖ = w x := by
      rw [show ‖((w x : ℝ) : ℂ)‖ = |w x| by simp, abs_of_nonneg (hw0 x)]
    rw [norm_mul, norm_mul, norm_mul, h3]
    have ha : 0 ≤ ‖((A i x : ℝ) : ℂ)‖ := norm_nonneg _
    have hb : 0 ≤ ‖((B i x : ℝ) : ℂ)‖ := norm_nonneg _
    have hc : 0 ≤ ‖sg i x‖ := norm_nonneg _
    calc w x * ‖((A i x : ℝ) : ℂ)‖ * ‖((B i x : ℝ) : ℂ)‖ * ‖sg i x‖
        ≤ w x * ‖((A i x : ℝ) : ℂ)‖ * ‖((B i x : ℝ) : ℂ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hsg_norm i x)
            (mul_nonneg (mul_nonneg (hw0 x) ha) hb)
      _ ≤ w x * ‖((A i x : ℝ) : ℂ)‖ * 1 * 1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2
            (mul_nonneg (hw0 x) ha)) (by norm_num)
      _ ≤ w x * 1 * 1 * 1 := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (hw0 x)) (by norm_num)
      _ = w x := by ring
  -- the greatest maximiser
  have hpoint : ∀ x : ℝ, (∑ i, wi i x * F i x) = ((w x * G x : ℝ) : ℂ) := by
    intro x
    obtain ⟨i0, hi0mem, hi0max⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun i : Fin M => ∀ j : Fin M, ‖F j x‖ ≤ ‖F i x‖))
      (fun i : Fin M => i)
      (by
        obtain ⟨i1, -, hi1⟩ := Finset.exists_max_image Finset.univ (fun i : Fin M => ‖F i x‖)
          ⟨⟨0, hM⟩, Finset.mem_univ _⟩
        exact ⟨i1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hi1 j (Finset.mem_univ j)⟩⟩)
    have hi0amax : ∀ j : Fin M, ‖F j x‖ ≤ ‖F i0 x‖ := (Finset.mem_filter.mp hi0mem).2
    have hGi0 : G x = ‖F i0 x‖ := le_antisymm (ciSup_le hi0amax) (hGle x i0)
    have hA1 : A i0 x = 1 := by
      simp only [hA]
      rw [if_pos hi0amax]
    have hB1 : B i0 x = 1 := by
      rw [hB]
      refine Finset.prod_eq_one (fun j _ => ?_)
      have hnot : ¬ (i0 < j ∧ G x = ‖F j x‖) := by
        rintro ⟨hij, hGj⟩
        have hmax : ∀ k : Fin M, ‖F k x‖ ≤ ‖F j x‖ := fun k => by rw [← hGj]; exact hGle x k
        have hmem : j ∈ Finset.univ.filter
            (fun i : Fin M => ∀ k : Fin M, ‖F k x‖ ≤ ‖F i x‖) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmax⟩
        exact absurd (hi0max j hmem) (not_le.mpr hij)
      simp only [hnot, if_false]
    have hzero : ∀ i : Fin M, i ≠ i0 → wi i x * F i x = 0 := by
      intro i hi
      by_cases hamax : ∀ j : Fin M, ‖F j x‖ ≤ ‖F i x‖
      · have hmem : i ∈ Finset.univ.filter
            (fun k : Fin M => ∀ j : Fin M, ‖F j x‖ ≤ ‖F k x‖) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hamax⟩
        have hlt : i < i0 := lt_of_le_of_ne (hi0max i hmem) hi
        have hBzero : B i x = 0 := by
          rw [hB]
          exact Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [if_pos ⟨hlt, hGi0⟩])
        simp only [hwi]
        rw [hBzero]
        simp
      · have hAzero : A i x = 0 := by
          simp only [hA]
          rw [if_neg hamax]
        simp only [hwi]
        rw [hAzero]
        simp
    rw [Finset.sum_eq_single i0 (fun i _ hi => hzero i hi)
      (fun h => absurd (Finset.mem_univ i0) h)]
    simp only [hwi, hA1, hB1, Pi.one_apply, Complex.ofReal_one, mul_one]
    rw [mul_assoc, hsg_mul i0 x, ← hGi0]
    push_cast
    ring

  -- disjointness of the supports of the weights
  have hdisj : ∀ i j : Fin M, i ≠ j → ∀ x : ℝ, wi i x * star (wi j x) = 0 := by
    intro i j hij x
    by_cases hamax_i : ∀ k : Fin M, ‖F k x‖ ≤ ‖F i x‖
    · by_cases hamax_j : ∀ k : Fin M, ‖F k x‖ ≤ ‖F j x‖
      · rcases lt_or_gt_of_ne hij with hlt | hlt
        · have hGj : G x = ‖F j x‖ := le_antisymm (ciSup_le hamax_j) (hGle x j)
          have hBzero : B i x = 0 := by
            rw [hB]
            exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos ⟨hlt, hGj⟩])
          rw [hwi]
          simp [hBzero]
        · have hGi : G x = ‖F i x‖ := le_antisymm (ciSup_le hamax_i) (hGle x i)
          have hBzero : B j x = 0 := by
            rw [hB]
            exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos ⟨hlt, hGi⟩])
          rw [hwi]
          simp [hBzero]
      · have hAj : A j x = 0 := by
          simp only [hA]
          rw [if_neg hamax_j]
        rw [hwi]
        simp [hAj]
    · have hAi : A i x = 0 := by
        simp only [hA]
        rw [if_neg hamax_i]
      rw [hwi]
      simp [hAi]
  -- measurability and integrability of the weights
  have hwi_aemeas : ∀ i, AEMeasurable (wi i) volume := by
    intro i
    have h1 : AEMeasurable (fun x : ℝ => ((w x : ℝ) : ℂ)) volume :=
      Complex.measurable_ofReal.comp_aemeasurable hw2.aemeasurable
    have h2 : AEMeasurable (fun x : ℝ => ((A i x : ℝ) : ℂ)) volume :=
      (Complex.measurable_ofReal.comp (hA_meas i)).aemeasurable
    have h3 : AEMeasurable (fun x : ℝ => ((B i x : ℝ) : ℂ)) volume :=
      (Complex.measurable_ofReal.comp (hB_meas i)).aemeasurable
    have h4 : AEMeasurable (sg i) volume := (hsg_meas i).aemeasurable
    exact ((h1.mul h2).mul h3).mul h4
  have hwi_memLp : ∀ i, MemLp (wi i) 2 volume := by
    intro i
    refine MemLp.of_le (memLp_ofReal hw2) (hwi_aemeas i).aestronglyMeasurable ?_
    filter_upwards with x
    rw [norm_ofReal_eq, abs_of_nonneg (hw0 x)]
    exact hwi_bound i x
  have hwi_int : ∀ i, Integrable (wi i) := by
    intro i
    rw [← memLp_one_iff_integrable]
    refine MemLp.of_le (memLp_ofReal (memLp_one_iff_integrable.mpr hw1))
      (hwi_aemeas i).aestronglyMeasurable ?_
    filter_upwards with x
    rw [norm_ofReal_eq, abs_of_nonneg (hw0 x)]
    exact hwi_bound i x
  -- integrability of the individual terms and of the sum
  have hFsum_memLp : MemLp (fun x : ℝ => ∑ i : Fin M, ‖F i x‖) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (Fin M)) (fun i _ => (hFmem i).norm)
  have hprod_int : Integrable (fun x : ℝ => w x * ∑ i : Fin M, ‖F i x‖) := by
    have h : Integrable (fun x : ℝ => (((w x * ∑ i : Fin M, ‖F i x‖ : ℝ)) : ℂ)) := by
      have hh := (memLp_ofReal hw2).integrable_mul (memLp_ofReal hFsum_memLp)
      refine hh.congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
    refine h.norm.congr ?_
    filter_upwards with x
    have hw : ‖((w x : ℝ) : ℂ)‖ = w x := by
      rw [norm_ofReal_eq, abs_of_nonneg (hw0 x)]
    have hs : ‖(((∑ i : Fin M, ‖F i x‖) : ℝ) : ℂ)‖ = ∑ i : Fin M, ‖F i x‖ := by
      rw [norm_ofReal_eq, abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    show ‖(((w x * ∑ i : Fin M, ‖F i x‖ : ℝ)) : ℂ)‖ = w x * ∑ i : Fin M, ‖F i x‖
    rw [show (((w x * ∑ i : Fin M, ‖F i x‖ : ℝ)) : ℂ)
        = ((w x : ℝ) : ℂ) * (((∑ i : Fin M, ‖F i x‖) : ℝ) : ℂ) by push_cast; ring,
      norm_mul, hw, hs]
  have hterm_int : ∀ i : Fin M, Integrable (fun x : ℝ => wi i x * F i x) := by
    intro i
    refine Integrable.mono' hprod_int ?_ ?_
    · exact (hwi_int i).aestronglyMeasurable.mul (hFmem i).aestronglyMeasurable
    · filter_upwards with x
      calc ‖wi i x * F i x‖ = ‖wi i x‖ * ‖F i x‖ := norm_mul _ _
        _ ≤ w x * ‖F i x‖ := mul_le_mul_of_nonneg_right (hwi_bound i x) (norm_nonneg _)
        _ ≤ w x * ∑ j : Fin M, ‖F j x‖ := by
            refine mul_le_mul_of_nonneg_left ?_ (hw0 x)
            exact Finset.single_le_sum (fun j _ => norm_nonneg (F j x)) (Finset.mem_univ i)
  have hsum_int : Integrable (fun x : ℝ => ∑ i : Fin M, wi i x * F i x) := by
    rw [← memLp_one_iff_integrable]
    exact memLp_finsetSum (Finset.univ : Finset (Fin M)) (fun i _ => memLp_one_iff_integrable.mpr (hterm_int i))
  -- Step 1: the left-hand side is the real part of the total sum
  have hAeq : (∫ x : ℝ, w x * G x) = (∫ x : ℝ, ∑ i : Fin M, wi i x * F i x).re := by
    have h1 : (∫ x : ℝ, w x * G x) = ∫ x : ℝ, (∑ i : Fin M, wi i x * F i x).re := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show w x * G x = (∑ i : Fin M, wi i x * F i x).re
      rw [hpoint x]
      simp
    rw [h1]
    exact integral_re hsum_int
  -- Step 2: each term is a Fourier pairing
  have hterm : ∀ i : Fin M, (∫ x : ℝ, wi i x * F i x)
      = ∫ ξ : ℝ, (Set.indicator (C i) (𝓕 f)) ξ * (𝓕 (wi i)) (-ξ) := by
    intro i
    simp only [hF]
    exact integral_mul_fourierInv _ _
      (memLp_one_iff_integrable.mp (memLp_one_indicator_fourier (C i) (hmeas i) (hbd i) f hf1))
      (hwi_int i)
      (memLp_two_indicator_fourier (C i) (hmeas i) (hbd i) f hf1)
      (hwi_memLp i)
  -- the Fourier transforms of the weights
  set V : Fin M → ℝ → ℂ := fun i ξ => (𝓕 (wi i)) (-ξ) with hVdef
  have hV_memLp : ∀ i, MemLp (V i) 2 volume := by
    intro i
    rw [hVdef]
    exact memLp_comp_neg (memLp_fourier (hwi_int i) (hwi_memLp i))
  have hV_orth : ∀ i j : Fin M, i ≠ j → ∫ ξ : ℝ, V i ξ * star (V j ξ) = 0 := by
    intro i j hij
    have h1 : (∫ ξ : ℝ, V i ξ * star (V j ξ))
        = ∫ ξ : ℝ, (𝓕 (wi i)) ξ * star ((𝓕 (wi j)) ξ) := by
      rw [show (fun ξ : ℝ => V i ξ * star (V j ξ))
          = (fun ξ : ℝ => (fun η : ℝ => (𝓕 (wi i)) η * star ((𝓕 (wi j)) η)) (-ξ)) from by
        funext ξ; simp only [hVdef, neg_neg]]
      exact MeasureTheory.integral_neg_eq_self
        (fun η : ℝ => (𝓕 (wi i)) η * star ((𝓕 (wi j)) η)) (volume : Measure ℝ)
    have h2 : (∫ ξ : ℝ, (𝓕 (wi i)) ξ * star ((𝓕 (wi j)) ξ))
        = ∫ x : ℝ, wi i x * star (wi j x) :=
      integral_fourier_mul_star (wi i) (wi j) (hwi_int i) (hwi_int j) (hwi_memLp i) (hwi_memLp j)
    have h3 : (∫ x : ℝ, wi i x * star (wi j x)) = 0 := by
      rw [show (fun x : ℝ => wi i x * star (wi j x)) = fun _ => (0 : ℂ) from
        funext (fun x => hdisj i j hij x)]
      simp
    rw [h1, h2, h3]
  -- the pointwise `ℓ²` bound for the weights
  have hpt : ∀ x : ℝ, ∑ i : Fin M, ‖wi i x‖ ^ 2 ≤ w x ^ 2 := by
    intro x
    have hcard : (Finset.univ.filter (fun i : Fin M => wi i x ≠ 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      by_contra hij
      exact mul_ne_zero (Finset.mem_filter.mp hi).2
        (star_ne_zero.mpr (Finset.mem_filter.mp hj).2) (hdisj i j hij x)
    calc ∑ i : Fin M, ‖wi i x‖ ^ 2
        = ∑ i ∈ Finset.univ.filter (fun i : Fin M => wi i x ≠ 0), ‖wi i x‖ ^ 2 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases h : wi i x = 0 <;> simp [h]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin M => wi i x ≠ 0), w x ^ 2 := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have h1 : ‖wi i x‖ ≤ w x := hwi_bound i x
          have h2 : 0 ≤ ‖wi i x‖ := norm_nonneg _
          have h3 : 0 ≤ w x := hw0 x
          nlinarith [h1, h2, h3]
      _ = ((Finset.univ.filter (fun i : Fin M => wi i x ≠ 0)).card : ℝ) * w x ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * w x ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact_mod_cast hcard
      _ = w x ^ 2 := one_mul _
  -- integrability of the squared norms
  have hw_sq_int : Integrable (fun x : ℝ => w x ^ 2) := by
    have h : Integrable (fun x : ℝ => (((w x * w x : ℝ)) : ℂ)) := by
      have hh := (memLp_ofReal hw2).integrable_mul (memLp_ofReal hw2)
      refine hh.congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
    refine h.norm.congr ?_
    filter_upwards with x
    have h1 : ‖((w x : ℝ) : ℂ)‖ = w x := by rw [norm_ofReal_eq, abs_of_nonneg (hw0 x)]
    show ‖(((w x * w x : ℝ)) : ℂ)‖ = w x ^ 2
    rw [show (((w x * w x : ℝ)) : ℂ) = ((w x : ℝ) : ℂ) * ((w x : ℝ) : ℂ) by push_cast; ring,
      norm_mul, h1]
    ring
  have hwi_sq_int : ∀ i : Fin M, Integrable (fun x : ℝ => ‖wi i x‖ ^ 2) := by
    intro i
    refine Integrable.mono' hw_sq_int ?_ ?_
    · exact ((hwi_aemeas i).norm.pow_const 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : ‖wi i x‖ ≤ w x := hwi_bound i x
      nlinarith [norm_nonneg (wi i x), hw0 x, h1]
  have hnorm_w : (∑ i : Fin M, ∫ x : ℝ, ‖wi i x‖ ^ 2) ≤ ∫ x : ℝ, w x ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ => hwi_sq_int i)]
    refine integral_mono_ae (integrable_finsetSum _ (fun i _ => hwi_sq_int i)) hw_sq_int ?_
    filter_upwards with x
    exact hpt x
  -- the nested projection bound
  have hBsum_memLp : MemLp (fun ξ : ℝ => ∑ i : Fin M, ‖V i ξ‖) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (Fin M)) (fun i _ => (hV_memLp i).norm)
  have hB_memLp : MemLp (fun ξ : ℝ => ∑ i : Fin M, Set.indicator (C i) (V i) ξ) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (Fin M)) (fun i _ => MemLp.indicator (hmeas i) (hV_memLp i))
  have hBnd : Real.sqrt (∫ ξ : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ ^ 2)
      ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ i : Fin M, ∫ ξ : ℝ, ‖V i ξ‖ ^ 2) := by
    have hbound := nested_indicator_l2_bound volume M hM C V hmeas hnest hV_memLp hV_orth
    have hVlin : ∀ i : Fin M, (∫⁻ a : ℝ, ‖V i a‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ 2) :=
      fun i => by
        simpa only [Real.rpow_two] using
          NestedIndicator.lintegral_enorm_rpow_two volume (hV_memLp i)
    have hBlin : (∫⁻ a : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ a : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ 2) :=
      by simpa only [Real.rpow_two] using
        NestedIndicator.lintegral_enorm_rpow_two volume hB_memLp
    have hsum_lin : (∑ i : Fin M, ∫⁻ a : ℝ, ‖V i a‖ₑ ^ (2:ℝ) ∂volume)
        = ∑ i : Fin M, ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ 2) :=
      Finset.sum_congr rfl (fun i _ => hVlin i)
    have hreal : (∫ a : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ 2)
        ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2 * ∑ i : Fin M, ∫ a : ℝ, ‖V i a‖ ^ 2 := by
      have key : ENNReal.ofReal (∫ a : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ 2)
          ≤ ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2)
            * ∑ i : Fin M, ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ 2) := by
        rw [← hBlin, ← hsum_lin]
        exact hbound
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
        ← ENNReal.ofReal_mul (show (0:ℝ) ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2 by
          positivity)] at key
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key
    calc Real.sqrt (∫ a : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ 2)
        ≤ Real.sqrt ((2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2
            * ∑ i : Fin M, ∫ a : ℝ, ‖V i a‖ ^ 2) := Real.sqrt_le_sqrt hreal
      _ = (2 * ((Nat.log2 M : ℝ) + 1) + 3)
            * Real.sqrt (∑ i : Fin M, ∫ a : ℝ, ‖V i a‖ ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- Cauchy--Schwarz
  have hCS : ‖∫ ξ : ℝ, (𝓕 f) ξ * (∑ i : Fin M, Set.indicator (C i) (V i) ξ)‖
      ≤ Real.sqrt (∫ ξ : ℝ, ‖(𝓕 f) ξ‖ ^ 2)
        * Real.sqrt (∫ ξ : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ ^ 2) := by
    have hFmem2 : MemLp (𝓕 f) (ENNReal.ofReal 2) volume := by
      simpa using memLp_fourier hf1 hf2
    have h1 : ‖∫ ξ : ℝ, (𝓕 f) ξ * (∑ i : Fin M, Set.indicator (C i) (V i) ξ)‖
        ≤ ∫ ξ : ℝ, ‖(𝓕 f) ξ‖ * ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ := by
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine integral_mono_ae ?_ ?_ ?_
      · exact ((memLp_fourier hf1 hf2).integrable_mul hB_memLp).norm
      · exact ((memLp_fourier hf1 hf2).norm).integrable_mul hB_memLp.norm
      · filter_upwards with ξ
        rw [norm_mul]
    have h2 := integral_mul_norm_le_Lp_mul_Lq (μ := volume) (f := 𝓕 f)
      (g := fun ξ : ℝ => ∑ i : Fin M, Set.indicator (C i) (V i) ξ) (p := 2) (q := 2)
      (by rw [Real.holderConjugate_iff]; norm_num) hFmem2
      (by simpa only [ENNReal.ofReal_ofNat] using hB_memLp)
    refine le_trans h1 ?_
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h2
  -- Plancherel for `f`
  have hnorm_f : (∫ ξ : ℝ, ‖(𝓕 f) ξ‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
    have h1 : (∫⁻ ξ : ℝ, ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ ξ : ℝ, ‖(𝓕 f) ξ‖ ^ 2) := by
      simpa only [Real.rpow_two] using
        NestedIndicator.lintegral_enorm_rpow_two volume (memLp_fourier hf1 hf2)
    have h2 : (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2) := by
      simpa only [Real.rpow_two] using
        NestedIndicator.lintegral_enorm_rpow_two volume hf2
    have h3 := lintegral_enorm_fourier_eq hf1 hf2
    rw [h1, h2] at h3
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp h3
  -- Plancherel for the weights
  have hnorm_wi : ∀ i : Fin M, (∫ ξ : ℝ, ‖V i ξ‖ ^ 2) = ∫ x : ℝ, ‖wi i x‖ ^ 2 := by
    intro i
    have hVeq : ∀ ξ : ℝ, V i ξ = 𝓕⁻ (wi i) ξ := by
      intro ξ
      rw [hVdef]
      exact (Real.fourierInv_eq_fourier_neg (wi i) ξ).symm
    have h1 : (∫⁻ ξ : ℝ, ‖V i ξ‖ₑ ^ (2:ℝ) ∂volume)
        = ∫⁻ ξ : ℝ, ‖𝓕⁻ (wi i) ξ‖ₑ ^ (2:ℝ) ∂volume :=
      lintegral_congr (fun ξ => by rw [hVeq ξ])
    have hVl : (∫⁻ a : ℝ, ‖V i a‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ (2:ℝ)) :=
      NestedIndicator.lintegral_enorm_rpow_two volume (hV_memLp i)
    have hwl : (∫⁻ a : ℝ, ‖wi i a‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ a : ℝ, ‖wi i a‖ ^ (2:ℝ)) :=
      NestedIndicator.lintegral_enorm_rpow_two volume (hwi_memLp i)
    have h6 : ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ (2:ℝ))
        = ENNReal.ofReal (∫ a : ℝ, ‖wi i a‖ ^ (2:ℝ)) := by
      calc ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ (2:ℝ))
          = ∫⁻ a : ℝ, ‖V i a‖ₑ ^ (2:ℝ) ∂volume := hVl.symm
        _ = ∫⁻ a : ℝ, ‖𝓕⁻ (wi i) a‖ₑ ^ (2:ℝ) ∂volume := h1
        _ = ∫⁻ a : ℝ, ‖wi i a‖ₑ ^ (2:ℝ) ∂volume :=
              lintegral_enorm_fourierInv_eq (memLp_one_iff_integrable.mpr (hwi_int i)) (hwi_memLp i)
        _ = ENNReal.ofReal (∫ a : ℝ, ‖wi i a‖ ^ (2:ℝ)) := hwl
    have h7 := (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun a => by positivity))
      (integral_nonneg (fun a => by positivity))).mp h6
    simpa only [Real.rpow_two] using h7
  -- assembly
  have hCsum : (∫ x : ℝ, ∑ i : Fin M, wi i x * F i x)
      = ∫ ξ : ℝ, (𝓕 f) ξ * (∑ i : Fin M, Set.indicator (C i) (V i) ξ) := by
    have hsumm : ∀ i : Fin M,
        Integrable (fun ξ : ℝ => (Set.indicator (C i) (𝓕 f)) ξ * (𝓕 (wi i)) (-ξ)) := by
      intro i
      have h1 : MemLp (fun ξ : ℝ => (Set.indicator (C i) (𝓕 f)) ξ) 2 volume :=
        memLp_two_indicator_fourier (C i) (hmeas i) (hbd i) f hf1
      have h2 : MemLp (fun ξ : ℝ => (𝓕 (wi i)) (-ξ)) 2 volume :=
        memLp_comp_neg (memLp_fourier (hwi_int i) (hwi_memLp i))
      exact memLp_one_iff_integrable.mp (MemLp.mul' (p := 2) (q := 2) (r := 1) h1 h2)
    rw [integral_finsetSum _ (fun i _ => hterm_int i)]
    simp only [hterm]
    rw [← integral_finsetSum _ (fun i _ => hsumm i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show (∑ i : Fin M, (Set.indicator (C i) (𝓕 f)) ξ * (𝓕 (wi i)) (-ξ))
        = (𝓕 f) ξ * ∑ i : Fin M, Set.indicator (C i) (V i) ξ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : ξ ∈ C i <;> simp [h, hVdef]
  have hmain : (∫ x : ℝ, w x * G x) ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3)
      * Real.sqrt (∫ x : ℝ, w x ^ 2) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
    calc (∫ x : ℝ, w x * G x) = (∫ x : ℝ, ∑ i : Fin M, wi i x * F i x).re := hAeq
      _ ≤ ‖∫ x : ℝ, ∑ i : Fin M, wi i x * F i x‖ := Complex.re_le_norm _
      _ = ‖∫ ξ : ℝ, (𝓕 f) ξ * (∑ i : Fin M, Set.indicator (C i) (V i) ξ)‖ := by rw [hCsum]
      _ ≤ Real.sqrt (∫ ξ : ℝ, ‖(𝓕 f) ξ‖ ^ 2)
            * Real.sqrt (∫ ξ : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ ^ 2) := hCS
      _ ≤ Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) * ((2 * ((Nat.log2 M : ℝ) + 1) + 3)
            * Real.sqrt (∑ i : Fin M, ∫ ξ : ℝ, ‖V i ξ‖ ^ 2)) := by
          rw [hnorm_f]
          exact mul_le_mul_of_nonneg_left hBnd (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) * ((2 * ((Nat.log2 M : ℝ) + 1) + 3)
            * Real.sqrt (∫ x : ℝ, w x ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (Real.sqrt_nonneg _)
          refine Real.sqrt_le_sqrt ?_
          calc (∑ i : Fin M, ∫ ξ : ℝ, ‖V i ξ‖ ^ 2)
              = ∑ i : Fin M, ∫ x : ℝ, ‖wi i x‖ ^ 2 := Finset.sum_congr rfl (fun i _ => hnorm_wi i)
            _ ≤ ∫ x : ℝ, w x ^ 2 := hnorm_w
      _ = (2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, w x ^ 2)
            * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by ring
  simpa only [hG, hF] using hmain

/-- Finite suprema commute with `ENNReal.ofReal`. -/
lemma iSup_ofReal_finset {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    (⨆ i, ENNReal.ofReal (y i)) = ENNReal.ofReal (⨆ i, y i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h1 : (⨆ i, ENNReal.ofReal (y i)) = 0 := iSup_of_empty _
    have h2 : (⨆ i, y i) = 0 := Real.iSup_of_isEmpty y
    rw [h1, h2, ENNReal.ofReal_zero]
  · refine le_antisymm ?_ ?_
    · exact ciSup_le fun i => ENNReal.ofReal_le_ofReal (le_ciSup (Set.finite_range y).bddAbove i)
    · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ y
        ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
      have hsup : (⨆ i, y i) = y i₀ :=
        le_antisymm (ciSup_le fun i => hi₀ i (Finset.mem_univ i))
          (le_ciSup (Set.finite_range y).bddAbove i₀)
      rw [hsup]
      exact le_iSup (fun i => ENNReal.ofReal (y i)) i₀

/-- **Maximal bound for the band-pass operators over nested neighbourhoods** (the
Bourgain–BDG estimate, `L²` form). -/
lemma maximal_bound_nice {M : ℕ} (hM : 1 ≤ M) (C : Fin M → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (C i))
    (hnest : ∀ i j : Fin M, i ≤ j → C j ⊆ C i) (hbd : ∀ i, Bornology.IsBounded (C i))
    (f : ℝ → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    ∫⁻ x : ℝ, (⨆ i : Fin M, ‖bandOp (C i) f x‖ₑ) ^ (2:ℝ) ∂volume
      ≤ ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2)
        * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) ∂volume := by
  classical
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hFmem : ∀ i, MemLp (fun x : ℝ => ‖bandOp (C i) f x‖) 2 volume :=
    fun i => (bandOp_memLp (C i) (hmeas i) (hbd i) f hf1 hf2).norm
  set G : ℝ → ℝ := fun x => ⨆ i : Fin M, ‖bandOp (C i) f x‖ with hG
  have hGbdd : ∀ x : ℝ, BddAbove (Set.range fun i : Fin M => ‖bandOp (C i) f x‖) :=
    fun x => (Set.finite_range _).bddAbove
  have hGle : ∀ x (i : Fin M), ‖bandOp (C i) f x‖ ≤ G x :=
    fun x i => le_ciSup (hGbdd x) i
  have hGmeas : Measurable G := by
    rw [hG]
    exact Measurable.iSup (fun i => (bandOp_cont (C i) (hmeas i) (hbd i) f hf1).norm.measurable)
  have hGnonneg : ∀ x, 0 ≤ G x :=
    fun x => le_trans (norm_nonneg _) (hGle x ⟨0, hM⟩)
  have hGmem : MemLp G 2 volume := by
    have hdom : MemLp (fun x : ℝ => ∑ i : Fin M, ‖bandOp (C i) f x‖) 2 volume :=
      memLp_finsetSum (Finset.univ : Finset (Fin M)) (fun i _ => hFmem i)
    refine MemLp.mono' hdom hGmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (hGnonneg x)]
    exact ciSup_le (fun i =>
      Finset.single_le_sum (fun j _ => norm_nonneg (bandOp (C j) f x)) (Finset.mem_univ i))
  -- the linearisation bound
  have hlin : ∀ w : ℝ → ℝ, (∀ x, 0 ≤ w x) → Integrable w → MemLp w 2 volume →
      (∫ x : ℝ, w x * G x)
        ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, w x ^ 2)
            * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
    intro w hw0 hw1 hw2
    have := linearization_bound hM C hmeas hnest hbd f hf1 hf2 w hw0 hw1 hw2
    simpa only [hG] using this
  -- integrability of `G²`
  have hGsq_int : Integrable (fun x : ℝ => G x ^ 2) := by
    have h : Integrable (fun x : ℝ => (((G x * G x : ℝ)) : ℂ)) := by
      have hh := (memLp_ofReal hGmem).integrable_mul (memLp_ofReal hGmem)
      refine hh.congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
    refine h.norm.congr ?_
    filter_upwards with x
    have h1 : ‖((G x : ℝ) : ℂ)‖ = G x := by
      rw [norm_ofReal_eq, abs_of_nonneg (hGnonneg x)]
    show ‖(((G x * G x : ℝ)) : ℂ)‖ = G x ^ 2
    rw [show (((G x * G x : ℝ)) : ℂ) = ((G x : ℝ) : ℂ) * ((G x : ℝ) : ℂ) by push_cast; ring,
      norm_mul, h1]
    ring
  -- the truncated weights give the bound for each `N`
  have hN : ∀ N : ℕ, (∫ x : ℝ, G x ^ 2 * (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator (fun _ => (1:ℝ)) x)
      ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, G x ^ 2)
          * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
    intro N
    set T : Set ℝ := Set.Icc (-(N:ℝ)) (N:ℝ) with hT
    have hTmeas : MeasurableSet T := measurableSet_Icc
    have hTfin : volume T < ⊤ := by
      rw [hT, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    have hind_int : Integrable (T.indicator (fun _ => (1:ℝ))) volume :=
      (integrable_indicator_iff hTmeas).2 (integrableOn_const hTfin.ne)
    have hTle : ∀ x : ℝ, T.indicator (fun _ => (1:ℝ)) x ≤ 1 := fun x => by
      by_cases hx : x ∈ T <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    have hTnn : ∀ x : ℝ, 0 ≤ T.indicator (fun _ => (1:ℝ)) x := fun x => by
      by_cases hx : x ∈ T <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    have hTmeas_aesm : AEStronglyMeasurable (T.indicator (fun _ => (1:ℝ))) volume :=
      (measurable_const.indicator hTmeas).aestronglyMeasurable
    simp only [hT] at hTle hTnn hTmeas_aesm hind_int
    have hw0 : ∀ x : ℝ, 0 ≤ G x * T.indicator (fun _ => (1:ℝ)) x :=
      fun x => mul_nonneg (hGnonneg x) (hTnn x)
    have hdom_int : Integrable (fun x : ℝ => G x ^ 2 + T.indicator (fun _ => (1:ℝ)) x) :=
      hGsq_int.add hind_int
    have hw1 : Integrable (fun x : ℝ => G x * T.indicator (fun _ => (1:ℝ)) x) := by
      refine Integrable.mono' (g := fun x : ℝ => G x ^ 2 + T.indicator (fun _ => (1:ℝ)) x)
        hdom_int ?_ ?_
      · exact hGmeas.aestronglyMeasurable.mul hTmeas_aesm
      · filter_upwards with x
        rw [Real.norm_of_nonneg (hw0 x)]
        by_cases hx : x ∈ T
        · rw [Set.indicator_of_mem hx]
          nlinarith [hGnonneg x, sq_nonneg (G x - 1)]
        · rw [Set.indicator_of_notMem hx]
          nlinarith [hGnonneg x, hTnn x]
    have hw2 : MemLp (fun x : ℝ => G x * T.indicator (fun _ => (1:ℝ)) x) 2 volume := by
      refine MemLp.of_le hGmem ?_ ?_
      · exact hGmeas.aestronglyMeasurable.mul hTmeas_aesm
      · filter_upwards with x
        rw [Real.norm_of_nonneg (hw0 x), Real.norm_of_nonneg (hGnonneg x)]
        nlinarith [hGnonneg x, hTle x, hTnn x]
    have hkey := hlin _ hw0 hw1 hw2
    have hsq : (∫ x : ℝ, (G x * T.indicator (fun _ => (1:ℝ)) x) ^ 2) ≤ ∫ x : ℝ, G x ^ 2 := by
      refine integral_mono_ae ?_ hGsq_int ?_
      · refine Integrable.mono' (g := fun x : ℝ => G x ^ 2) hGsq_int ?_ ?_
        · exact (hGmeas.aestronglyMeasurable.mul hTmeas_aesm).pow 2
        · filter_upwards with x
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          have h3 : G x * T.indicator (fun _ => (1:ℝ)) x ≤ G x := by
            nlinarith [hGnonneg x, hTle x, hTnn x]
          exact pow_le_pow_left₀ (mul_nonneg (hGnonneg x) (hTnn x)) h3 2
      · filter_upwards with x
        have h3 : G x * T.indicator (fun _ => (1:ℝ)) x ≤ G x := by
          nlinarith [hGnonneg x, hTle x, hTnn x]
        exact pow_le_pow_left₀ (mul_nonneg (hGnonneg x) (hTnn x)) h3 2
    have hprod : (∫ x : ℝ, (G x * T.indicator (fun _ => (1:ℝ)) x) * G x)
        = ∫ x : ℝ, G x ^ 2 * T.indicator (fun _ => (1:ℝ)) x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    calc (∫ x : ℝ, G x ^ 2 * T.indicator (fun _ => (1:ℝ)) x)
        = ∫ x : ℝ, (G x * T.indicator (fun _ => (1:ℝ)) x) * G x := hprod.symm
      _ ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3)
            * Real.sqrt (∫ x : ℝ, (G x * T.indicator (fun _ => (1:ℝ)) x) ^ 2)
            * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := hkey
      _ ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, G x ^ 2)
            * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (by positivity)
  -- pass to the limit
  have htend : Tendsto
      (fun N : ℕ => ∫ x : ℝ, G x ^ 2 * (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator (fun _ => (1:ℝ)) x)
      atTop (𝓝 (∫ x : ℝ, G x ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => G x ^ 2) ?_ hGsq_int ?_ ?_
    · intro N
      exact (hGmeas.pow_const 2).aestronglyMeasurable.mul
        ((measurable_const.indicator measurableSet_Icc).aestronglyMeasurable)
    · intro N
      filter_upwards with x
      have h1 : (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator (fun _ => (1:ℝ)) x ≤ 1 := by
        by_cases hx : x ∈ Set.Icc (-(N:ℝ)) (N:ℝ) <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      have h2 : 0 ≤ (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator (fun _ => (1:ℝ)) x := by
        by_cases hx : x ∈ Set.Icc (-(N:ℝ)) (N:ℝ) <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) h2)]
      have hsq : (0:ℝ) ≤ G x ^ 2 := sq_nonneg _
      nlinarith [hsq, h1, h2]
    · filter_upwards with x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (Nat.ceil |x|)] with N hN
      have hx : x ∈ Set.Icc (-(N:ℝ)) (N:ℝ) := by
        refine ⟨?_, ?_⟩
        · rw [neg_le]
          exact le_trans (neg_le_abs x) (le_trans (Nat.le_ceil |x|) (by exact_mod_cast hN))
        · exact le_trans (le_abs_self x) (le_trans (Nat.le_ceil |x|) (by exact_mod_cast hN))
      rw [Set.indicator_of_mem hx, mul_one]
  have hfinal : (∫ x : ℝ, G x ^ 2) ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, G x ^ 2)
      * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) :=
    le_of_tendsto htend (Filter.Eventually.of_forall hN)
  -- conclude
  have hsq_bound : (∫ x : ℝ, G x ^ 2) ≤ ((2 * ((Nat.log2 M : ℝ) + 1) + 3)) ^ 2 * (∫ x : ℝ, ‖f x‖ ^ 2) := by
    rcases eq_or_lt_of_le (integral_nonneg (f := fun x : ℝ => G x ^ 2) (fun x => sq_nonneg (G x))) with h | h
    · rw [← h]; positivity
    · have hb : Real.sqrt (∫ x : ℝ, G x ^ 2) ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3)
          * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
        have hpos : 0 < Real.sqrt (∫ x : ℝ, G x ^ 2) := Real.sqrt_pos.mpr h
        have hfinal' : Real.sqrt (∫ x : ℝ, G x ^ 2) * Real.sqrt (∫ x : ℝ, G x ^ 2)
            ≤ ((2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2))
              * Real.sqrt (∫ x : ℝ, G x ^ 2) := by
          rw [← sq]
          calc (Real.sqrt (∫ x : ℝ, G x ^ 2)) ^ 2 = ∫ x : ℝ, G x ^ 2 :=
                Real.sq_sqrt (integral_nonneg (f := fun x : ℝ => G x ^ 2) (fun x => sq_nonneg (G x)))
            _ ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, G x ^ 2)
                  * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := hfinal
            _ = ((2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2))
                  * Real.sqrt (∫ x : ℝ, G x ^ 2) := by ring
        exact le_of_mul_le_mul_right hfinal' hpos
      calc (∫ x : ℝ, G x ^ 2) = (Real.sqrt (∫ x : ℝ, G x ^ 2)) ^ 2 :=
            (Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (G x)))).symm
        _ ≤ ((2 * ((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
        _ = (2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2 * (∫ x : ℝ, ‖f x‖ ^ 2) := by
            rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖))]
  have hGiSup : ∀ x : ℝ, (⨆ i : Fin M, ‖bandOp (C i) f x‖ₑ) = ‖G x‖ₑ := by
    intro x
    rw [hG]
    rw [show ‖(⨆ i : Fin M, ‖bandOp (C i) f x‖)‖ₑ
        = ENNReal.ofReal (⨆ i : Fin M, ‖bandOp (C i) f x‖) by
      rw [enorm_eq_ofReal_norm_real,
        Real.norm_of_nonneg (le_trans (norm_nonneg _) (le_ciSup (hGbdd x) ⟨0, hM⟩))]]
    rw [show (⨆ i : Fin M, ‖bandOp (C i) f x‖ₑ)
        = ⨆ i : Fin M, ENNReal.ofReal (‖bandOp (C i) f x‖) from
      iSup_congr (fun i => enorm_eq_ofReal_norm _)]
    exact iSup_ofReal_finset (fun i : Fin M => ‖bandOp (C i) f x‖)
  calc ∫⁻ x : ℝ, (⨆ i : Fin M, ‖bandOp (C i) f x‖ₑ) ^ (2:ℝ) ∂volume
      = ∫⁻ x : ℝ, ‖G x‖ₑ ^ (2:ℝ) ∂volume := by
        refine lintegral_congr (fun x => ?_)
        rw [hGiSup x]
    _ = ENNReal.ofReal (∫ x : ℝ, ‖G x‖ ^ (2:ℝ)) :=
        lintegral_enorm_rpow_two_real hGmem
    _ = ENNReal.ofReal (∫ x : ℝ, G x ^ 2) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show ‖G x‖ ^ (2:ℝ) = G x ^ 2
        rw [Real.norm_of_nonneg (hGnonneg x), Real.rpow_two]
    _ ≤ ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2 * (∫ x : ℝ, ‖f x‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal hsq_bound
    _ = ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2)
          * ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2) := ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2)
          * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) ∂volume := by
        rw [show ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2)
            = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) ∂volume from by
          rw [show (∫ x : ℝ, ‖f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ (2:ℝ) from
            integral_congr_ae (Filter.Eventually.of_forall (fun x => (Real.rpow_two _).symm))]
          exact (NestedIndicator.lintegral_enorm_rpow_two volume hf2).symm]

lemma integral_fourier_neg_div (f : ℝ → ℂ) (θ : ℝ) :
    (∫ y : ℝ, f y * Complex.exp (Complex.I * (y : ℂ) * (θ : ℂ)))
      = 𝓕 f (-(θ / (2 * Real.pi))) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show f y * Complex.exp (Complex.I * (y : ℂ) * (θ : ℂ))
      = Complex.exp ((↑(-2 * Real.pi * inner ℝ y (-(θ / (2 * Real.pi)))) : ℂ) * Complex.I) • f y
  rw [Real.inner_apply, smul_eq_mul]
  have h : -2 * Real.pi * (y * (-(θ / (2 * Real.pi)))) = y * θ := by
    field_simp
  rw [h]
  have hexp : Complex.exp (Complex.I * (y : ℂ) * (θ : ℂ))
      = Complex.exp ((↑(y * θ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexp, mul_comm]

lemma exp_sub_factor (x y θ : ℝ) :
    Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))
      = Complex.exp (-(Complex.I * ((x : ℂ)) * (θ : ℂ)))
        * Complex.exp (Complex.I * ((y : ℂ)) * (θ : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Evaluation of the inner integral in `y`. -/
lemma inner_integral_eval (f : ℝ → ℂ) (hf : Integrable f) (B : Set ℝ) (x θ : ℝ) :
    (∫ y : ℝ, f y * Set.indicator B
        (fun _ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)
      = Set.indicator B (fun _ => Complex.exp (-(Complex.I * ((x : ℂ)) * (θ : ℂ)))
            * 𝓕 f (-(θ / (2 * Real.pi)))) θ := by
  by_cases hθ : θ ∈ B
  · simp only [Set.indicator_of_mem hθ]
    have hpt : ∀ y : ℝ, f y * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))
        = Complex.exp (-(Complex.I * ((x : ℂ)) * (θ : ℂ)))
          * (f y * Complex.exp (Complex.I * (y : ℂ) * (θ : ℂ))) := by
      intro y
      rw [exp_sub_factor x y θ]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_const_mul, integral_fourier_neg_div]
  · simp only [Set.indicator_of_notMem hθ, mul_zero]
    simp

/-- The substitution `θ = 2π ξ`, reflection and recognition of the inverse Fourier integral. -/
lemma fourierInv_scaled_indicator (f : ℝ → ℂ) (B : Set ℝ) (x : ℝ) :
    (∫ θ : ℝ, Set.indicator B (fun _ => Complex.exp (-(Complex.I * ((x : ℂ)) * (θ : ℂ)))
            * 𝓕 f (-(θ / (2 * Real.pi)))) θ)
      = 2 * Real.pi * 𝓕⁻ (fun ξ : ℝ => Set.indicator {ξ : ℝ | -2 * Real.pi * ξ ∈ B}
            (fun ξ => 𝓕 f ξ) ξ) x := by
  set g : ℝ → ℂ := fun θ => Set.indicator B (fun _ => Complex.exp (-(Complex.I * ((x : ℂ)) * (θ : ℂ)))
            * 𝓕 f (-(θ / (2 * Real.pi)))) θ with hg
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  have hsub : (∫ θ, g θ) = 2 * Real.pi * ∫ ξ, g (2*Real.pi*ξ) := by
    have h := Measure.integral_comp_inv_mul_left g ((2 * Real.pi)⁻¹)
    rw [inv_inv, abs_of_pos (inv_pos.mpr h2π)] at h
    have hsmul : (∫ y, g y) = (2 * Real.pi) • ∫ ξ, g (2*Real.pi*ξ) := by
      rw [h, smul_inv_smul₀ h2π.ne']
    rw [hsmul, Complex.real_smul]
    push_cast
    ring
  rw [hsub]
  have h1 : (∫ ξ, g (2*Real.pi*ξ)) = ∫ ξ, g (2*Real.pi*(-ξ)) := by
    rw [← MeasureTheory.integral_neg_eq_self (fun ξ => g (2*Real.pi*ξ)) (volume : Measure ℝ)]
  rw [h1, Real.fourierInv_eq']
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show g (2*Real.pi*(-ξ)) = Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) •
      Set.indicator {ξ : ℝ | -2 * Real.pi * ξ ∈ B} (fun ξ => 𝓕 f ξ) ξ
  have hBiff : (2 * Real.pi * (-ξ) ∈ B) ↔ (-2 * Real.pi * ξ ∈ B) := by
    have he : 2 * Real.pi * (-ξ) = -2 * Real.pi * ξ := by ring
    rw [he]
  by_cases hB : -2 * Real.pi * ξ ∈ B
  · have hB' : 2 * Real.pi * (-ξ) ∈ B := hBiff.mpr hB
    have hmem : ξ ∈ {y : ℝ | -2 * Real.pi * y ∈ B} := hB
    rw [hg]
    simp only [Real.inner_apply]
    rw [Set.indicator_of_mem hB', Set.indicator_of_mem hmem, smul_eq_mul]
    have harg : -(2 * Real.pi * -ξ / (2 * Real.pi)) = ξ := by
      field_simp
    rw [harg]
    congr 1
    push_cast
    ring_nf
  · have hB' : ¬ (2 * Real.pi * (-ξ) ∈ B) := fun hh => hB (hBiff.mp hh)
    have hmem : ξ ∉ {y : ℝ | -2 * Real.pi * y ∈ B} := hB
    rw [hg]
    simp only [Real.inner_apply]
    rw [Set.indicator_of_notMem hB', Set.indicator_of_notMem hmem, smul_zero]

lemma integrable_pair (f : ℝ → ℂ) (hf : Integrable f) (B : Set ℝ)
    (hB : MeasurableSet B) (hBfin : volume B < ⊤) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => f p.1 *
      Set.indicator B (fun θ => Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * (θ : ℂ)))) p.2)
      (volume.prod volume) := by
  classical
  have hdom : Integrable (fun p : ℝ × ℝ => ‖f p.1‖ * (B.indicator (fun _ => (1:ℝ)) p.2))
      (volume.prod volume) :=
    (hf.norm).mul_prod ((integrable_indicator_iff hB).2 (integrableOn_const hBfin.ne))
  refine Integrable.mono' hdom ?_ ?_
  · refine AEStronglyMeasurable.mul
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst) ?_
    have hmeas : Measurable (fun p : ℝ × ℝ =>
        if p.2 ∈ B then Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * ((p.2 : ℝ) : ℂ))) else 0) := by
      refine Measurable.ite (hB.preimage measurable_snd) ?_ measurable_const
      fun_prop
    refine (hmeas.aestronglyMeasurable).congr ?_
    filter_upwards with p
    show (if p.2 ∈ B then Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * ((p.2 : ℝ) : ℂ))) else 0)
        = Set.indicator B (fun θ => Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * (θ : ℂ)))) p.2
    by_cases h : p.2 ∈ B
    · rw [if_pos h, Set.indicator_of_mem h]
    · rw [if_neg h, Set.indicator_of_notMem h]
  · filter_upwards with p
    have hexp : ∀ θ : ℝ,
        ‖Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * ((θ : ℝ) : ℂ)))‖ = 1 := by
      intro θ
      rw [Complex.norm_exp]
      have hre : (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * ((θ : ℝ) : ℂ))).re = 0 := by
        simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, mul_one, zero_mul, sub_zero, neg_zero]
      rw [hre, Real.exp_zero]
    rw [norm_mul]
    by_cases h : p.2 ∈ B
    · rw [Set.indicator_of_mem h, hexp, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp

set_option maxHeartbeats 1000000 in
lemma iterated_eq_fourierInv (f : ℝ → ℂ) (hf : Integrable f)
    (B : Set ℝ) (hB : MeasurableSet B) (hBfin : volume B < ⊤) (x : ℝ) :
    (∫ y : ℝ, f y * (∫ θ : ℝ, Set.indicator B
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = 2 * Real.pi * 𝓕⁻ (fun ξ : ℝ => Set.indicator {ξ : ℝ | -2 * Real.pi * ξ ∈ B}
            (fun ξ => 𝓕 f ξ) ξ) x := by
  have hpair := integrable_pair f hf B hB hBfin x
  have hswap : (∫ y : ℝ, ∫ θ : ℝ, f y *
        Set.indicator B (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)
      = ∫ θ : ℝ, ∫ y : ℝ, f y *
        Set.indicator B (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ := by
    refine MeasureTheory.integral_integral_swap ?_
    exact hpair
  calc (∫ y : ℝ, f y * (∫ θ : ℝ, Set.indicator B
          (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = ∫ y : ℝ, ∫ θ : ℝ, f y *
          Set.indicator B (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact (integral_const_mul (f y) (fun θ => Set.indicator B
          (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)).symm
    _ = ∫ θ : ℝ, ∫ y : ℝ, f y *
          Set.indicator B (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ := hswap
    _ = ∫ θ : ℝ, Set.indicator B (fun _ => Complex.exp (-(Complex.I * ((x : ℂ)) * (θ : ℂ)))
            * 𝓕 f (-(θ / (2 * Real.pi)))) θ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        exact inner_integral_eval f hf B x θ
    _ = 2 * Real.pi * 𝓕⁻ (fun ξ : ℝ => Set.indicator {ξ : ℝ | -2 * Real.pi * ξ ∈ B}
            (fun ξ => 𝓕 f ξ) ξ) x := fourierInv_scaled_indicator f B x

/-! ## The neighbourhood sets of the target and their frequency images -/

/-- The `s`-neighbourhood of the finite frequency set `lam`. -/
def neighSet {K : ℕ} (lam : Fin K → ℝ) (s : ℝ) : Set ℝ := {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ s}

lemma measurableSet_neighSet {K : ℕ} (lam : Fin K → ℝ) (s : ℝ) :
    MeasurableSet (neighSet lam s) := by
  have hset : neighSet lam s = ⋃ k : Fin K, {θ : ℝ | |θ - lam k| ≤ s} := by
    ext θ; simp only [neighSet, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  exact MeasurableSet.iUnion (fun k => measurableSet_le (by fun_prop) measurable_const)

lemma abs_le_of_mem_neighSet {K : ℕ} (lam : Fin K → ℝ) {s θ : ℝ} (hθ : θ ∈ neighSet lam s) :
    |θ| ≤ ∑ k : Fin K, |lam k| + s := by
  obtain ⟨k, hk⟩ := hθ
  have h1 : |θ| ≤ |lam k| + |θ - lam k| := by
    have h := abs_add_le (lam k) (θ - lam k)
    have he : lam k + (θ - lam k) = θ := by ring
    rwa [he] at h
  have h3 : |lam k| ≤ ∑ k' : Fin K, |lam k'| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (lam i)) (Finset.mem_univ k)
  linarith

lemma isBounded_neighSet {K : ℕ} (lam : Fin K → ℝ) (s : ℝ) :
    Bornology.IsBounded (neighSet lam s) := by
  refine isBounded_iff_forall_norm_le.mpr
    ⟨∑ k : Fin K, |lam k| + s, fun θ hθ => ?_⟩
  rw [Real.norm_eq_abs]
  exact abs_le_of_mem_neighSet lam hθ

lemma volume_neighSet_lt_top {K : ℕ} (lam : Fin K → ℝ) (s : ℝ) :
    volume (neighSet lam s) < ⊤ :=
  (isBounded_neighSet lam s).measure_lt_top

lemma neighSet_mono {K : ℕ} (lam : Fin K → ℝ) {s s' : ℝ} (h : s ≤ s') :
    neighSet lam s ⊆ neighSet lam s' := by
  rintro θ ⟨k, hk⟩
  exact ⟨k, le_trans hk h⟩

/-- The frequency set `C_s = {ξ : ℝ | -2πξ ∈ A_s}` attached to the radius `s`. -/
def freqSet {K : ℕ} (lam : Fin K → ℝ) (s : ℝ) : Set ℝ :=
  {ξ : ℝ | -2 * Real.pi * ξ ∈ neighSet lam s}

lemma measurableSet_freqSet {K : ℕ} (lam : Fin K → ℝ) (s : ℝ) :
    MeasurableSet (freqSet lam s) :=
  (measurableSet_neighSet lam s).preimage (by fun_prop)

lemma isBounded_freqSet {K : ℕ} (lam : Fin K → ℝ) (s : ℝ) :
    Bornology.IsBounded (freqSet lam s) := by
  refine isBounded_iff_forall_norm_le.mpr
    ⟨(∑ k : Fin K, |lam k| + s) / (2 * Real.pi), fun ξ hξ => ?_⟩
  have h : |(-2 * Real.pi * ξ)| ≤ ∑ k : Fin K, |lam k| + s :=
    abs_le_of_mem_neighSet lam hξ
  rw [show (-2 * Real.pi * ξ) = -(2 * Real.pi * ξ) by ring, abs_neg, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h
  rw [Real.norm_eq_abs, le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
  linarith

lemma freqSet_mono {K : ℕ} (lam : Fin K → ℝ) {s s' : ℝ} (h : s ≤ s') :
    freqSet lam s ⊆ freqSet lam s' :=
  fun _ hξ => neighSet_mono lam h hξ

/-- The frequency sets of the target, reindexed along `S` in the *decreasing* order required by
the nested-band maximal bound (`scaleSets lam S j ⊆ scaleSets lam S i` for `i ≤ j`). -/
noncomputable def scaleSets {K : ℕ} (lam : Fin K → ℝ) (S : Finset ℝ) :
    Fin S.card → Set ℝ :=
  fun i => freqSet lam (((S.orderIsoOfFin rfl) (Fin.rev i) : ↥S) : ℝ)

lemma measurableSet_scaleSets {K : ℕ} (lam : Fin K → ℝ) (S : Finset ℝ) (i : Fin S.card) :
    MeasurableSet (scaleSets lam S i) :=
  measurableSet_freqSet lam _

lemma isBounded_scaleSets {K : ℕ} (lam : Fin K → ℝ) (S : Finset ℝ) (i : Fin S.card) :
    Bornology.IsBounded (scaleSets lam S i) :=
  isBounded_freqSet lam _

lemma scaleSets_antitone {K : ℕ} (lam : Fin K → ℝ) (S : Finset ℝ) :
    ∀ i j : Fin S.card, i ≤ j → scaleSets lam S j ⊆ scaleSets lam S i := by
  intro i j hij
  have hrev : Fin.rev j ≤ Fin.rev i := by
    rw [Fin.rev_le_rev]; exact hij
  have hmono := (S.orderIsoOfFin rfl).monotone hrev
  have hcoe : (((S.orderIsoOfFin rfl) (Fin.rev j) : ↥S) : ℝ)
      ≤ (((S.orderIsoOfFin rfl) (Fin.rev i) : ↥S) : ℝ) := hmono
  exact freqSet_mono lam hcoe

/-! ### Reindexing a finite supremum along `S` -/

lemma iSup_mem_eq_sup {α : Type*} (S : Finset α) (g : α → ℝ≥0∞) :
    (⨆ s ∈ S, g s) = S.sup g :=
  (Finset.sup_eq_iSup S g).symm

lemma sup_eq_sup_comp_orderIso {M : ℕ} {α : Type*} [LinearOrder α] (S : Finset α)
    (e : Fin M ≃o ↥S) (g : α → ℝ≥0∞) :
    S.sup g = (Finset.univ : Finset (Fin M)).sup (fun i => g ((e i : ↥S) : α)) := by
  refine le_antisymm (Finset.sup_le (fun s hs => ?_)) (Finset.sup_le (fun i _ => ?_))
  · obtain ⟨i, hi⟩ := e.surjective ⟨s, hs⟩
    have hi' : ((e i : ↥S) : α) = s := congrArg Subtype.val hi
    rw [← hi']
    exact Finset.le_sup (f := fun i : Fin M => g ((e i : ↥S) : α)) (Finset.mem_univ i)
  · exact Finset.le_sup (f := g) (e i).2

lemma sup_eq_sup_rev {M : ℕ} (g : Fin M → ℝ≥0∞) :
    (Finset.univ : Finset (Fin M)).sup g
      = (Finset.univ : Finset (Fin M)).sup (fun i => g (Fin.rev i)) := by
  refine le_antisymm (Finset.sup_le (fun i _ => ?_)) (Finset.sup_le (fun i _ => ?_))
  · have h := Finset.le_sup (f := fun j : Fin M => g (Fin.rev j)) (Finset.mem_univ (Fin.rev i))
    rwa [Fin.rev_rev] at h
  · exact Finset.le_sup (f := g) (Finset.mem_univ (Fin.rev i))

lemma sup_univ_eq_iSup {M : ℕ} (g : Fin M → ℝ≥0∞) :
    (Finset.univ : Finset (Fin M)).sup g = ⨆ i, g i := by
  simpa using (Finset.sup_eq_iSup (Finset.univ : Finset (Fin M)) g)

lemma reindex_sup {K : ℕ} (lam : Fin K → ℝ) (S : Finset ℝ) (g : ℝ → ℝ≥0∞) :
    (⨆ s ∈ S, g s) = ⨆ i : Fin S.card, g (((S.orderIsoOfFin rfl) (Fin.rev i) : ↥S) : ℝ) := by
  rw [iSup_mem_eq_sup, sup_eq_sup_comp_orderIso S (S.orderIsoOfFin rfl) g,
    sup_eq_sup_rev (fun i => g (((S.orderIsoOfFin rfl) i : ↥S) : ℝ)), sup_univ_eq_iSup]

/-- **The exact form of the target's maximal function**: the supremum over the radii in `S` of the
band-pass operators of the neighbourhoods, identified (for `f ∈ L¹ ∩ L²`) with `2π` times the
supremum of the nested band-pass operators `bandOp (scaleSets lam S i)`. -/
lemma sup_iterated_eq {K : ℕ} (lam : Fin K → ℝ) (S : Finset ℝ)
    (f : ℝ → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (x : ℝ) :
    (⨆ s ∈ S, ‖∫ y : ℝ, f y *
          (∫ θ : ℝ, Set.indicator (neighSet lam s)
            (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ)
      = ENNReal.ofReal (2 * Real.pi) *
          (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) f x‖ₑ) := by
  classical
  have hId : ∀ s : ℝ, (∫ y : ℝ, f y *
        (∫ θ : ℝ, Set.indicator (neighSet lam s)
          (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = 2 * Real.pi * bandOp (freqSet lam s) f x := by
    intro s
    rw [iterated_eq_fourierInv f hf1 (neighSet lam s) (measurableSet_neighSet lam s)
      (volume_neighSet_lt_top lam s) x]
    rfl
  have h2pi : ‖((2 : ℂ) * ((Real.pi : ℝ) : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, norm_ofReal_eq, abs_of_pos Real.pi_pos]
    norm_num
  have hstep : ∀ s : ℝ,
      ‖∫ y : ℝ, f y *
        (∫ θ : ℝ, Set.indicator (neighSet lam s)
          (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ
      = ENNReal.ofReal (2 * Real.pi) * ‖bandOp (freqSet lam s) f x‖ₑ := by
    intro s
    rw [hId s, enorm_eq_ofReal_norm, norm_mul, h2pi,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi), ← enorm_eq_ofReal_norm]
  calc (⨆ s ∈ S, ‖∫ y : ℝ, f y *
        (∫ θ : ℝ, Set.indicator (neighSet lam s)
          (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ)
      = ⨆ s ∈ S, ENNReal.ofReal (2 * Real.pi) * ‖bandOp (freqSet lam s) f x‖ₑ := by
        refine iSup_congr (fun s => iSup_congr (fun _ => ?_))
        exact hstep s
    _ = ⨆ i : Fin S.card,
          ENNReal.ofReal (2 * Real.pi) * ‖bandOp (scaleSets lam S i) f x‖ₑ :=
        reindex_sup lam S (fun s => ENNReal.ofReal (2 * Real.pi) * ‖bandOp (freqSet lam s) f x‖ₑ)
    _ = ENNReal.ofReal (2 * Real.pi) *
          (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) f x‖ₑ) :=
        (ENNReal.mul_iSup _ _).symm

/-- In `ℝ≥0∞`, the square of a supremum is at most the supremum of the squares. -/
lemma iSup_rpow_two_le {ι : Type*} (g : ι → ℝ≥0∞) :
    (⨆ i, g i) ^ (2:ℝ) ≤ ⨆ i, (g i) ^ (2:ℝ) := by
  have h : (⨆ i, g i) ^ (2:ℝ) = (⨆ i, g i) * (⨆ i, g i) := by
    rw [ENNReal.rpow_two, pow_two]
  have h1 : (⨆ i, g i) * (⨆ i, g i) = ⨆ i, ⨆ j, g i * g j := by
    rw [ENNReal.iSup_mul]
    exact iSup_congr (fun i => ENNReal.mul_iSup (g i) g)
  rw [h, h1]
  refine iSup_le (fun i => iSup_le (fun j => ?_))
  rcases le_total (g i) (g j) with hle | hle
  · calc g i * g j ≤ g j * g j := mul_le_mul' hle le_rfl
      _ = (g j) ^ (2:ℝ) := by rw [ENNReal.rpow_two, pow_two]
      _ ≤ ⨆ k, (g k) ^ (2:ℝ) := le_iSup (fun k => (g k) ^ (2:ℝ)) j
  · calc g i * g j ≤ g i * g i := mul_le_mul' le_rfl hle
      _ = (g i) ^ (2:ℝ) := by rw [ENNReal.rpow_two, pow_two]
      _ ≤ ⨆ k, (g k) ^ (2:ℝ) := le_iSup (fun k => (g k) ^ (2:ℝ)) i

/-- The square of the `liminf` of an `ℝ≥0∞`-valued sequence is at most the `liminf` of the
squares (squaring is monotone and preserves suprema). -/
lemma sq_liminf_bound (u : ℕ → ℝ≥0∞) :
    (Filter.liminf u Filter.atTop) ^ (2:ℝ) ≤
      Filter.liminf (fun n => (u n) ^ (2:ℝ)) Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  refine le_trans (iSup_rpow_two_le (fun N : ℕ => ⨅ n ≥ N, u n)) ?_
  refine iSup_le (fun N => ?_)
  calc (⨅ n ≥ N, u n) ^ (2:ℝ)
      ≤ (⨅ n ≥ N, (u n) ^ (2:ℝ)) := by
        refine le_iInf₂ (fun n hn => ?_)
        refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0:ℝ) ≤ 2)
        exact le_trans (iInf_le _ n) (iInf_le _ hn)
    _ ≤ ⨆ N : ℕ, ⨅ n ≥ N, (u n) ^ (2:ℝ) :=
        le_iSup (fun N : ℕ => ⨅ n ≥ N, (u n) ^ (2:ℝ)) N

/-- **Step 1 of the proof of Bourgain's Lemma 4.32 (real line, `L¹ ∩ L²` case).**

For `f ∈ L¹ ∩ L²(ℝ)`, the maximal function of the band-pass operators over the radii in a finite
set `S`, with the target's explicit iterated-integral form, is bounded by
`2π (2 log₂ #S + 5)` — the nested-band maximal bound applied to `f` and the identification of the
band-pass operator with `2π 𝓕⁻(1_{C_s} 𝓕 f)`. -/
lemma nice_bound {K : ℕ} (lam : Fin K → ℝ) (S : Finset ℝ) (hS : ∀ s ∈ S, 0 < s)
    (f : ℝ → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    (∫⁻ x : ℝ, (⨆ s ∈ S, ‖∫ y : ℝ, f y *
          (∫ θ : ℝ, Set.indicator (neighSet lam s)
            (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2:ℝ))
      ≤ ENNReal.ofReal ((2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2)
          * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    have hzero : ∀ x : ℝ, (⨆ s ∈ (∅ : Finset ℝ), ‖∫ y : ℝ, f y *
          (∫ θ : ℝ, Set.indicator (neighSet lam s)
            (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2:ℝ)
        = (0 : ℝ≥0∞) := by
      intro x
      rw [iSup_mem_eq_sup, Finset.sup_empty, ENNReal.bot_eq_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
    rw [show (∫⁻ x : ℝ, (⨆ s ∈ (∅ : Finset ℝ), ‖∫ y : ℝ, f y *
          (∫ θ : ℝ, Set.indicator (neighSet lam s)
            (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2:ℝ))
        = ∫⁻ _x : ℝ, (0 : ℝ≥0∞) from lintegral_congr hzero]
    simp
  · have hM : 1 ≤ S.card := Finset.card_pos.mpr hSne
    have hpoint : ∀ x : ℝ, (⨆ s ∈ S, ‖∫ y : ℝ, f y *
          (∫ θ : ℝ, Set.indicator (neighSet lam s)
            (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ)
        = ENNReal.ofReal (2 * Real.pi) *
            (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) f x‖ₑ) :=
      fun x => sup_iterated_eq lam S f hf1 hf2 x
    have h2pi_pow : (ENNReal.ofReal (2 * Real.pi)) ^ (2:ℝ)
        = ENNReal.ofReal ((2 * Real.pi) ^ 2) := by
      rw [← Real.rpow_two (2 * Real.pi),
        ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi) (by norm_num)]
    calc (∫⁻ x : ℝ, (⨆ s ∈ S, ‖∫ y : ℝ, f y *
            (∫ θ : ℝ, Set.indicator (neighSet lam s)
              (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2:ℝ))
        = ∫⁻ x : ℝ, (ENNReal.ofReal (2 * Real.pi) *
            (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) f x‖ₑ)) ^ (2:ℝ) :=
          lintegral_congr (fun x => by rw [hpoint x])
      _ = ∫⁻ x : ℝ, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
            (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) f x‖ₑ) ^ (2:ℝ) := by
          refine lintegral_congr (fun x => ?_)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), h2pi_pow]
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 2) *
            ∫⁻ x : ℝ, (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) f x‖ₑ) ^ (2:ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2) *
            (ENNReal.ofReal ((2 * ((Nat.log2 S.card : ℝ) + 1) + 3) ^ 2)
              * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ)) :=
          mul_le_mul' le_rfl (maximal_bound_nice hM (scaleSets lam S) (measurableSet_scaleSets lam S)
            (scaleSets_antitone lam S) (isBounded_scaleSets lam S) f hf1 hf2)
      _ = ENNReal.ofReal ((2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2)
            * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ 2)]
          congr 2
          ring

/-! ### Auxiliary analytic facts for the extension to all of `L²` -/

/-- The inner `θ`-integral `θ ↦ 1_B(θ) exp(-I(x-y)θ)`, viewed as a function of `y`, is a.e.
strongly measurable (as a Bochner integral of a jointly measurable function). -/
lemma aesm_inner_theta (B : Set ℝ) (hB : MeasurableSet B) (x : ℝ) :
    AEStronglyMeasurable (fun y : ℝ => ∫ θ : ℝ, Set.indicator B
      (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)
      (volume : Measure ℝ) := by
  have hbase : Measurable (fun p : ℝ × ℝ =>
      Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * ((p.2 : ℝ) : ℂ)))) := by fun_prop
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ B} := hB.preimage measurable_snd
  have heq : (Function.uncurry (fun y θ : ℝ => Set.indicator B
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = {p : ℝ × ℝ | p.2 ∈ B}.indicator (fun p : ℝ × ℝ =>
          Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * ((p.2 : ℝ) : ℂ)))) := by
    funext p
    show Set.indicator B (fun θ => Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * (θ : ℂ)))) p.2
      = Set.indicator {p : ℝ × ℝ | p.2 ∈ B} (fun p : ℝ × ℝ =>
          Complex.exp (-(Complex.I * (((x - p.1 : ℝ) : ℂ)) * ((p.2 : ℝ) : ℂ)))) p
    by_cases h : p.2 ∈ B
    · have h' : p ∈ {p : ℝ × ℝ | p.2 ∈ B} := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
    · have h' : p ∉ {p : ℝ × ℝ | p.2 ∈ B} := h
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  have hsm : StronglyMeasurable (Function.uncurry (fun y θ : ℝ => Set.indicator B
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)) := by
    rw [heq]
    exact (hbase.indicator hset).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ)) hsm).aestronglyMeasurable

/-- Elementary constant comparison: `2π (2 log₂ M + 5) ≤ 100 π log (M + 2)`. -/
lemma two_pi_log2_bound (M : ℕ) :
    2 * Real.pi * (2 * ((Nat.log2 M : ℝ) + 1) + 3) ≤
      100 * Real.pi * Real.log ((M : ℝ) + 2) := by
  have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hMnn : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  have hM2 : (2:ℝ) ≤ (M:ℝ) + 2 := by linarith
  have hlogM : (1:ℝ)/2 ≤ Real.log ((M:ℝ) + 2) :=
    le_trans hlog2half (Real.log_le_log (by norm_num : (0:ℝ) < 2) hM2)
  have hlogMpos : 0 < Real.log ((M:ℝ) + 2) := lt_of_lt_of_le (by norm_num) hlogM
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [Nat.log2_zero]
    have h2 : 2 * Real.pi * (2 * (((0:ℕ):ℝ) + 1) + 3) = 10 * Real.pi := by ring
    have h3 : 100 * Real.pi * Real.log (((0:ℕ):ℝ) + 2) = 100 * Real.pi * Real.log 2 := by
      norm_num
    rw [h2, h3]
    nlinarith [Real.pi_pos, hlog2half]
  · have hlog2M : (Nat.log2 M : ℝ) * Real.log 2 ≤ Real.log ((M:ℝ)) := by
      have h2 : ((2:ℝ) ^ (Nat.log2 M)) ≤ (M:ℝ) := by
        have h : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 (by omega : M ≠ 0)
        rw [← Nat.log2_eq_log_two] at h
        exact_mod_cast h
      have h3 := Real.log_le_log (by positivity) h2
      rwa [Real.log_pow] at h3
    have h4 : Real.log ((M:ℝ)) ≤ Real.log ((M:ℝ) + 2) :=
      Real.log_le_log (by positivity) (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 2))
    have hkey : (Nat.log2 M : ℝ) ≤ 2 * Real.log ((M:ℝ) + 2) := by
      nlinarith [hlog2M, h4, hlog2half, hlogMpos]
    have hbig : 2 * ((Nat.log2 M : ℝ) + 1) + 3 ≤ 50 * Real.log ((M:ℝ) + 2) := by
      nlinarith [hkey, hlogM, hlogMpos]
    calc 2 * Real.pi * (2 * ((Nat.log2 M : ℝ) + 1) + 3)
        ≤ 2 * Real.pi * (50 * Real.log ((M:ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hbig (by positivity)
      _ = 100 * Real.pi * Real.log ((M:ℝ) + 2) := by ring

/-- **Bourgain's Lemma 4.32 (the dual Doob / Burkholder-Davis-Gundy estimate for nested frequency projections), real-line form.**  For a finite set `S` of positive radii, the maximal function over the radii in `S` of the band-pass operators onto the `s`-neighbourhoods of a finite frequency set `lam : Fin K → ℝ` is bounded on `L²(ℝ)` by `C log (#S + 2)`, with `C` independent of `K` and of `S`.  Only the nesting of the neighbourhoods is used. -/
theorem nested_scales_maximal_l2_real {K : ℕ} (lam : Fin K → ℝ) (S : Finset ℝ)
    (hS : ∀ s ∈ S, 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f 2 MeasureTheory.volume →
      ∫⁻ x, (⨆ s ∈ S, ‖∫ y : ℝ, f y *
            (∫ θ : ℝ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ s}
              (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C * Real.log ((S.card : ℝ) + 2)) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume := by
  classical
  refine ⟨100 * Real.pi, by positivity, fun f hf => ?_⟩
  -- a measurable representative of `f`
  set g : ℝ → ℂ := hf.aestronglyMeasurable.mk f with hgdef
  have hgm : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hae : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgmem : MemLp g 2 volume :=
    hf.congr_norm hgm.aestronglyMeasurable (hae.mono (fun y hy => by rw [hy]))
  -- bounded, compactly supported truncations
  set T : ℕ → Set ℝ := fun n => {y : ℝ | ‖g y‖ ≤ (n:ℝ) ∧ |y| ≤ (n:ℝ)} with hTdef
  set fn : ℕ → ℝ → ℂ := fun n => Set.indicator (T n) g with hfndef
  have hTmeas : ∀ n, MeasurableSet (T n) := fun n =>
    (measurableSet_le hgm.measurable.norm measurable_const).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hfn_meas : ∀ n, Measurable (fn n) := fun n =>
    Measurable.ite (hTmeas n) hgm.measurable measurable_const
  have hfn_le : ∀ n y, ‖fn n y‖ ≤ ‖g y‖ := by
    intro n y
    show ‖Set.indicator (T n) g y‖ ≤ ‖g y‖
    by_cases h : y ∈ T n
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, norm_zero]
      positivity
  have hfn_tend : ∀ y, Tendsto (fun n => fn n y) atTop (𝓝 (g y)) := by
    intro y
    have h1 : ∀ᶠ n : ℕ in atTop, ‖g y‖ ≤ (n:ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈‖g y‖⌉₊] with n hn
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h2 : ∀ᶠ n : ℕ in atTop, |y| ≤ (n:ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈|y|⌉₊] with n hn
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h3 : ∀ᶠ n : ℕ in atTop, g y = fn n y := by
      filter_upwards [h1, h2] with n h1n h2n
      show g y = Set.indicator (T n) g y
      exact (Set.indicator_of_mem (s := T n) (show y ∈ T n from ⟨h1n, h2n⟩) g).symm
    exact tendsto_const_nhds.congr' h3
  have hfn_mem : ∀ n, MemLp (fn n) 2 volume := by
    intro n
    refine MemLp.mono' (p := 2) (μ := volume) (g := fun y : ℝ => ‖g y‖) hgmem.norm
      (hfn_meas n).aestronglyMeasurable ?_
    filter_upwards with y
    exact hfn_le n y
  have hfn_int : ∀ n, Integrable (fn n) := by
    intro n
    have hfin : volume (Set.Icc (-(n:ℝ)) (n:ℝ)) < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hdom : Integrable
        (fun y : ℝ => (n:ℝ) * (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℝ)) y)
        volume :=
      ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const hfin.ne)).const_mul
        (n:ℝ)
    refine Integrable.mono' hdom (hfn_meas n).aestronglyMeasurable ?_
    filter_upwards with y
    show ‖Set.indicator (T n) g y‖ ≤
      (n:ℝ) * (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℝ)) y
    by_cases h : y ∈ T n
    · rw [Set.indicator_of_mem h]
      have hy : y ∈ Set.Icc (-(n:ℝ)) (n:ℝ) := by
        rw [Set.mem_Icc, ← abs_le]
        exact h.2
      rw [Set.indicator_of_mem hy]
      simpa using h.1
    · rw [Set.indicator_of_notMem h, norm_zero]
      have hnn : (0:ℝ) ≤ (n:ℝ) * (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℝ)) y :=
        mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
      linarith
  -- the iterated integral of the target
  set I : (ℝ → ℂ) → ℝ → ℝ → ℂ := fun v s x => ∫ y : ℝ, v y *
      (∫ θ : ℝ, Set.indicator (neighSet lam s)
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ) with hIdef
  set b : ℝ → ℝ≥0∞ := fun x => ⨆ s ∈ S, ‖I f s x‖ₑ with hbdef
  set u : ℕ → ℝ → ℝ≥0∞ := fun n x => ⨆ s ∈ S, ‖I (fn n) s x‖ₑ with hudef
  have hb_eq_g : ∀ x : ℝ, b x = ⨆ s ∈ S, ‖I g s x‖ₑ := by
    intro x
    rw [hbdef]
    refine iSup_congr (fun s => iSup_congr (fun _ => ?_))
    congr 1
    exact integral_congr_ae (hae.mono (fun y hy => by simp only [hy]))
  -- every truncation satisfies the `L¹ ∩ L²` bound
  have hbound_n : ∀ n, (∫⁻ x : ℝ, (u n x) ^ (2:ℝ)) ≤
      ENNReal.ofReal ((2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2)
        * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
    intro n
    have h1 := nice_bound lam S hS (fn n) (hfn_int n) (hfn_mem n)
    have h2 : (∫⁻ x : ℝ, ‖fn n x‖ₑ ^ (2:ℝ)) ≤ ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
      refine lintegral_mono (fun x => ?_)
      refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0:ℝ) ≤ 2)
      rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hfn_le n x)
    calc (∫⁻ x : ℝ, (u n x) ^ (2:ℝ))
        ≤ ENNReal.ofReal ((2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2)
            * ∫⁻ x : ℝ, ‖fn n x‖ₑ ^ (2:ℝ) := h1
      _ ≤ ENNReal.ofReal ((2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2)
            * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := mul_le_mul' le_rfl h2
  -- a.e. measurability of the truncation maximal functions
  have hu_meas : ∀ n, AEMeasurable (fun x : ℝ => (u n x) ^ (2:ℝ)) volume := by
    intro n
    have hEq : ∀ x : ℝ, u n x = ENNReal.ofReal (2 * Real.pi) *
        (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) (fn n) x‖ₑ) :=
      fun x => sup_iterated_eq lam S (fn n) (hfn_int n) (hfn_mem n) x
    have hcont : ∀ i : Fin S.card, Continuous (bandOp (scaleSets lam S i) (fn n)) :=
      fun i => bandOp_cont _ (measurableSet_scaleSets lam S i) (isBounded_scaleSets lam S i) _
        (hfn_int n)
    have hV : AEMeasurable (fun x : ℝ =>
        (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) (fn n) x‖ₑ) ^ (2:ℝ)) volume :=
      (Measurable.iSup (fun i => (hcont i).measurable.enorm)).aemeasurable.pow_const (2:ℝ)
    have hV2 : AEMeasurable (fun x : ℝ => (ENNReal.ofReal (2 * Real.pi)) ^ (2:ℝ) *
        (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) (fn n) x‖ₑ) ^ (2:ℝ)) volume :=
      hV.const_mul _
    have hEq2 : (fun x : ℝ => (ENNReal.ofReal (2 * Real.pi)) ^ (2:ℝ) *
          (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) (fn n) x‖ₑ) ^ (2:ℝ)) =ᵐ[volume]
        (fun x : ℝ => (u n x) ^ (2:ℝ)) :=
      Eventually.of_forall (fun x => by
        show (ENNReal.ofReal (2 * Real.pi)) ^ (2:ℝ) *
            (⨆ i : Fin S.card, ‖bandOp (scaleSets lam S i) (fn n) x‖ₑ) ^ (2:ℝ)
          = (u n x) ^ (2:ℝ)
        rw [hEq x, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)])
    exact hV2.congr hEq2
  -- the pointwise `liminf` bound
  have hlim : ∀ x : ℝ, b x ≤ Filter.liminf (fun n => u n x) Filter.atTop := by
    intro x
    rw [hb_eq_g x, iSup_mem_eq_sup]
    refine Finset.sup_le (fun s hs => ?_)
    set c : ℝ → ℂ := fun y => ∫ θ : ℝ, Set.indicator (neighSet lam s)
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ with hcdef
    have hc_aesm : AEStronglyMeasurable c (volume : Measure ℝ) :=
      aesm_inner_theta (neighSet lam s) (measurableSet_neighSet lam s) x
    have hs_le_u : ∀ n, ‖I (fn n) s x‖ₑ ≤ u n x := by
      intro n
      have h := Finset.le_sup (f := fun s' : ℝ => ‖I (fn n) s' x‖ₑ) hs
      refine le_trans h ?_
      exact le_of_eq (iSup_mem_eq_sup S (fun s' : ℝ => ‖I (fn n) s' x‖ₑ)).symm
    by_cases hInt : Integrable (fun y : ℝ => g y * c y)
    · have htend : Tendsto (fun n => ∫ y : ℝ, fn n y * c y) atTop
          (𝓝 (∫ y : ℝ, g y * c y)) := by
        refine tendsto_integral_of_dominated_convergence (fun y : ℝ => ‖g y * c y‖)
          (fun n => (hfn_meas n).aestronglyMeasurable.mul hc_aesm) hInt.norm
          (fun n => ?_) (Eventually.of_forall fun y => ?_)
        · filter_upwards with y
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_right (hfn_le n y) (norm_nonneg _)
        · exact (hfn_tend y).mul_const (c y)
      have hnormE : Tendsto (fun n => ‖∫ y : ℝ, fn n y * c y‖ₑ) atTop
          (𝓝 (‖∫ y : ℝ, g y * c y‖ₑ)) := by
        have hnorm : Tendsto (fun n => ‖∫ y : ℝ, fn n y * c y‖) atTop
            (𝓝 ‖∫ y : ℝ, g y * c y‖) := htend.norm
        simp only [enorm_eq_ofReal_norm]
        exact (ENNReal.continuous_ofReal.tendsto ‖∫ y : ℝ, g y * c y‖).comp hnorm
      rw [show ‖I g s x‖ₑ = ‖∫ y : ℝ, g y * c y‖ₑ from rfl, ← hnormE.liminf_eq]
      exact Filter.liminf_le_liminf (Eventually.of_forall hs_le_u)
    · rw [show I g s x = (0:ℂ) from integral_undef hInt]
      simp
  -- Fatou's lemma
  have hFatou : (∫⁻ x : ℝ, (b x) ^ (2:ℝ)) ≤
      Filter.liminf (fun n => ∫⁻ x : ℝ, (u n x) ^ (2:ℝ)) Filter.atTop := by
    refine le_trans ?_ (MeasureTheory.lintegral_liminf_le' (μ := volume)
      (f := fun n x => (u n x) ^ (2:ℝ)) (u := Filter.atTop) (fun n => hu_meas n))
    refine lintegral_mono (fun x => ?_)
    exact le_trans (ENNReal.rpow_le_rpow (hlim x) (by norm_num : (0:ℝ) ≤ 2))
      (sq_liminf_bound (fun n => u n x))
  have hK : Filter.liminf (fun n => ∫⁻ x : ℝ, (u n x) ^ (2:ℝ)) Filter.atTop ≤
      ENNReal.ofReal ((2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2)
        * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
    have h2 := Filter.liminf_le_liminf (f := Filter.atTop)
      (v := fun n => ∫⁻ x : ℝ, (u n x) ^ (2:ℝ))
      (u := fun _ => ENNReal.ofReal ((2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2)
        * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ))
      (Eventually.of_forall hbound_n)
    rwa [Filter.liminf_const] at h2
  have hG : (∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ)) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
    refine lintegral_congr_ae (hae.mono (fun y hy => ?_))
    simp only [hy]
  have hconst : (2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2
      ≤ (100 * Real.pi * Real.log ((S.card : ℝ) + 2)) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    have hb := two_pi_log2_bound S.card
    linarith [hb]
  calc (∫⁻ x : ℝ, (⨆ s ∈ S, ‖I f s x‖ₑ) ^ (2:ℝ))
      = ∫⁻ x : ℝ, (b x) ^ (2:ℝ) := rfl
    _ ≤ Filter.liminf (fun n => ∫⁻ x : ℝ, (u n x) ^ (2:ℝ)) Filter.atTop := hFatou
    _ ≤ ENNReal.ofReal ((2 * Real.pi * (2 * ((Nat.log2 S.card : ℝ) + 1) + 3)) ^ 2)
          * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := hK
    _ ≤ ENNReal.ofReal ((100 * Real.pi * Real.log ((S.card : ℝ) + 2)) ^ 2)
          * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl
    _ = ENNReal.ofReal ((100 * Real.pi * Real.log ((S.card : ℝ) + 2)) ^ 2)
          * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by rw [hG]

end

end Commons.Analysis.Fourier
