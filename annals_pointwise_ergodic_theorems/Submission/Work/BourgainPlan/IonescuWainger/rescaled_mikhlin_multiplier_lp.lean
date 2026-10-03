import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.cutoff
import Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp
import Submission.Commons.Analysis.Fourier.fourier_scaled_translate
import Submission.Work.Analysis.Fourier.modulation_temperate_growth
import Submission.Commons.Analysis.Fourier.fourierInv_comp_add_eq_modulation
import Submission.Commons.Analysis.Integral.continuous_integral_czE_smul

/-!
# The rescaled (translated + dilated) Mikhlin multiplier theorem on `ℝ`

`mikhlin_multiplier_lp` (in `Submission/Commons`) gives the `L^p` bound for the multiplier with
symbol `m` itself. What the Ionescu–Wainger/Bourgain applications need is the same bound for the
*rescaled* symbol `ξ ↦ m ((ξ - c)/ε)`, uniformly in the scaling parameters `ε > 0`, `c ∈ ℝ`.

We obtain it from the unscaled theorem by the two elementary isometries of the Fourier side:
translation in frequency is a modulation in space (a unimodular pointwise factor, hence an
`L^p` isometry), and dilation in frequency is a dilation in space (a measure-preserving change of
variables up to the constant `ε`).  Concretely, with `G₁ = e^{-2πi c ·} G` and
`K₁ = G₁ (·/ε)`, one has `𝓕K₁ ζ = ε · 𝓕G (εζ + c)` and
`𝓕⁻(m((·-c)/ε) 𝓕G) x = e^{2πi c x} · 𝓕⁻(m 𝓕K₁) (εx)`, whence the `L^q` norms of the two
sides differ by exactly the two changes of variables `x ↦ εx` and `x ↦ ε⁻¹x`.
-/

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

open Commons.Analysis.CalderonZygmund (czE)

/-- The modulation `x ↦ e^{2πi a x}`. -/
def rmodFun (a : ℝ) : ℝ → ℂ := fun x => Complex.exp (↑(2 * Real.pi * a * x) * Complex.I)

lemma rmodFun_norm (a x : ℝ) : ‖rmodFun a x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma rmodFun_temperate (a : ℝ) : Function.HasTemperateGrowth (rmodFun a) := by
  change Function.HasTemperateGrowth
    (fun x => Complex.exp (↑(2 * Real.pi * a * x) * Complex.I))
  exact Work.Analysis.Fourier.modulation_temperate_growth a

/-- The modulation rule for the Fourier transform: `𝓕 (G · e^{2πi a ·}) = (𝓕 G)(· - a)`. -/
lemma fourier_mul_rmodFun (G : ℝ → ℂ) (a η : ℝ) :
    FourierTransform.fourier (fun x : ℝ => G x * rmodFun a x) η
      = FourierTransform.fourier G (η - a) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  change (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * (x * η)) * Complex.I)
        • (G x * rmodFun a x)) = ∫ x : ℝ,
      Complex.exp (↑(-2 * Real.pi * (x * (η - a))) * Complex.I) • G x
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, rmodFun]
  rw [show Complex.exp (↑(-2 * Real.pi * (x * η)) * Complex.I) *
        (G x * Complex.exp (↑(2 * Real.pi * a * x) * Complex.I))
      = (Complex.exp (↑(-2 * Real.pi * (x * η)) * Complex.I) *
          Complex.exp (↑(2 * Real.pi * a * x) * Complex.I)) * G x by ring,
    ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- The dilation rule for the Fourier transform. -/
lemma fourier_dilate_inv (f : ℝ → ℂ) (ε ξ : ℝ) (hε : 0 < ε) :
    FourierTransform.fourier (fun x : ℝ => f (ε⁻¹ * x)) ξ
      = (ε : ℂ) * FourierTransform.fourier f (ε * ξ) := by
  have h := Commons.Analysis.Fourier.fourier_comp_inv_smul (V := ℝ) f hε ξ
  rw [Module.finrank_self ℝ, pow_one] at h
  have h1 : (fun x : ℝ => f (ε⁻¹ • x)) = fun x : ℝ => f (ε⁻¹ * x) := by
    funext x; rw [smul_eq_mul]
  rw [h1] at h
  rw [h, Complex.real_smul, smul_eq_mul]

/-- Scalar linearity of the inverse Fourier transform. -/
lemma fourierInv_const_smul' (a : ℂ) (B : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv (a • B) x
      = a • FourierTransformInv.fourierInv B x := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq', ← MeasureTheory.integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The dilation rule for the inverse Fourier transform. -/
lemma fourierInv_dilate (B : ℝ → ℂ) (ε x : ℝ) (hε : 0 < ε) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => B (ξ / ε)) x
      = (ε : ℂ) * FourierTransformInv.fourierInv B (ε * x) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  have hcoe : (fun ξ : ℝ => B (ξ / ε)) = fun ξ : ℝ => B (ε⁻¹ * ξ) := by
    funext ξ; rw [div_eq_inv_mul, mul_comm]
  rw [hcoe, fourier_dilate_inv B ε (-x) hε, show ε * -x = -(ε * x) by ring]

/-- The affine rule for the inverse Fourier transform:
`𝓕⁻ (A((· - c)/ε)) x = e^{2πi c x} · ε · 𝓕⁻ A (εx)`. -/
lemma fourierInv_affine (A : ℝ → ℂ) (ε c x : ℝ) (hε : 0 < ε) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => A ((ξ - c) / ε)) x
      = rmodFun c x * (ε : ℂ) * FourierTransformInv.fourierInv A (ε * x) := by
  have h1 : (fun ξ : ℝ => A ((ξ - c) / ε))
      = fun ξ : ℝ => (fun η : ℝ => A (η / ε)) (ξ + (-c)) := by
    funext ξ; simp only [sub_eq_add_neg]
  rw [h1, Commons.Analysis.Fourier.fourierInv_comp_add_eq_modulation
      (fun η : ℝ => A (η / ε)) (-c) x, fourierInv_dilate A ε x hε]
  have harg : -(2 * ↑Real.pi * Complex.I * ↑((-c) * x))
      = ↑(2 * Real.pi * c * x) * Complex.I := by
    push_cast; ring
  rw [harg]
  show Complex.exp (↑(2 * Real.pi * c * x) * Complex.I)
        * ((ε : ℂ) * FourierTransformInv.fourierInv A (ε * x))
      = rmodFun c x * (ε : ℂ) * FourierTransformInv.fourierInv A (ε * x)
  unfold rmodFun
  ring

/-- The multiplier operator in the exact shape in which `mikhlin_multiplier_lp` produces its
bound. -/
def multOp (f V : ℝ → ℂ) : ℝ → ℂ := fun x => ∫ ξ : ℝ, (f ξ * czE x ξ) • V ξ

lemma czE_eq (x ξ : ℝ) :
    czE x ξ = Complex.exp (↑(2 * Real.pi * (x * ξ)) * Complex.I) := by
  rw [czE]; congr 1; push_cast; ring

/-- The multiplier operator against a Fourier transform is the inverse Fourier transform of the
product. -/
lemma fourierInv_mul_eq_multOp (f V : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => f ξ * V ξ) x = multOp f V x := by
  rw [multOp, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Real.inner_apply, smul_eq_mul, czE_eq]
  have harg : (2 * Real.pi * (ξ * x) : ℝ) = 2 * Real.pi * (x * ξ) := by ring
  rw [harg]
  ring

/-- Change of variables `x ↦ ε x` in a lower Lebesgue integral. -/
lemma lintegral_comp_mul_left_affine (F : ℝ → ℝ≥0∞) (hF : Measurable F) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x, F (ε * x) = ENNReal.ofReal ε⁻¹ * ∫⁻ x, F x := by
  rw [← MeasureTheory.lintegral_map (f := F) (g := fun x : ℝ => ε * x)
      hF (by fun_prop),
    Real.map_volume_mul_left hε.ne', MeasureTheory.lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr hε)]
  rfl

/-- `(eLpNorm f (ofReal q)) ^ q = ∫⁻ ‖f‖ₑ ^ q` for `q > 0`. -/
lemma eLpNorm_rpow_eq_lintegral {q : ℝ} (hq : 0 < q) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    (eLpNorm f (ENNReal.ofReal q) (volume : Measure ℝ)) ^ q
      = ∫⁻ x : ℝ, ‖f x‖ₑ ^ q := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := f) (p := ENNReal.ofReal q)
      (μ := (volume : Measure ℝ)) (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]

theorem rescaled_mikhlin_multiplier_lp (q : ℝ) (hq : 1 < q) : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (A : ℝ), 0 ≤ A → ContDiff ℝ 2 m → (∀ ξ : ℝ, ‖m ξ‖ ≤ A) → (∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ A) → (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A) → ∀ (ε c : ℝ), 0 < ε → ∀ (G : SchwartzMap ℝ ℂ), ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv (fun ξ : ℝ => m ((ξ - c) / ε) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ q ≤ ENNReal.ofReal ((C * A) ^ q) * ∫⁻ x : ℝ, ‖(G : ℝ → ℂ) x‖ₑ ^ q := by
  obtain ⟨Cq, hCqpos, hCq⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp q hq
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  refine ⟨Cq, hCqpos, ?_⟩
  intro m A hA hmCD hm0 hm1 hm2 ε c hε G
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  -- `G₁ = e^{-2πi c ·} G`
  set G1 : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (rmodFun (-c)) G with hG1def
  have hG1coe : (G1 : ℝ → ℂ) = fun x => rmodFun (-c) x * (G : ℝ → ℂ) x := by
    have h := SchwartzMap.smulLeftCLM_apply (F := ℂ) (rmodFun_temperate (-c)) G
    rw [hG1def, h]
    funext x; rw [smul_eq_mul]
  have hG1norm : ∀ x, ‖(G1 : ℝ → ℂ) x‖ = ‖(G : ℝ → ℂ) x‖ := by
    intro x
    rw [congrFun hG1coe x, norm_mul, rmodFun_norm, one_mul]
  -- `K₁ = G₁(·/ε)`
  set dil : ℝ → ℝ := fun x => ε⁻¹ * x with hdil
  have hdil_temperate : Function.HasTemperateGrowth dil := by
    rw [hdil]
    have heq : (fun x : ℝ => ε⁻¹ * x) = ⇑((ε⁻¹) • (1 : ℝ →L[ℝ] ℝ)) := by
      funext x; simp
    rw [heq]
    exact ContinuousLinearMap.hasTemperateGrowth _
  have hdil_upper : ∃ k C, ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖dil x‖) ^ k := by
    refine ⟨1, ε, fun x => ?_⟩
    rw [hdil, pow_one]
    have h1 : ‖((ε⁻¹) * x : ℝ)‖ = ε⁻¹ * ‖x‖ := by
      rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    rw [h1, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    linarith [hε, norm_nonneg x]
  set K1 : SchwartzMap ℝ ℂ := SchwartzMap.compCLM ℂ hdil_temperate hdil_upper G1 with hK1def
  have hK1coe : (K1 : ℝ → ℂ) = fun x => (G1 : ℝ → ℂ) (ε⁻¹ * x) := by
    have h := SchwartzMap.compCLM_apply ℂ hdil_temperate hdil_upper G1
    rw [hK1def, h]
    funext x
    simp only [Function.comp_apply]
    rw [hdil]
  have hK1norm : ∀ x, ‖(K1 : ℝ → ℂ) x‖ = ‖(G : ℝ → ℂ) (ε⁻¹ * x)‖ := by
    intro x
    rw [congrFun hK1coe x, hG1norm]
  set VK : ℝ → ℂ := FourierTransform.fourier (K1 : ℝ → ℂ) with hVK
  -- Fourier transform of `K₁`
  have hFK1 : ∀ ζ, VK ζ
      = (ε : ℂ) * FourierTransform.fourier (G : ℝ → ℂ) (ε * ζ + c) := by
    intro ζ
    rw [hVK, hK1coe, fourier_dilate_inv (G1 : ℝ → ℂ) ε ζ hε]
    congr 1
    have hfun : (G1 : ℝ → ℂ) = fun x : ℝ => (G : ℝ → ℂ) x * rmodFun (-c) x := by
      funext x; rw [congrFun hG1coe x, mul_comm]
    rw [hfun, fourier_mul_rmodFun (G : ℝ → ℂ) (-c) (ε * ζ)]
    have har : ε * ζ - (-c) = ε * ζ + c := by ring
    rw [har]
  have hFK1' : ∀ ξ, VK ((ξ - c) / ε)
      = (ε : ℂ) * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
    intro ξ
    rw [hFK1]
    have harg : ε * ((ξ - c) / ε) + c = ξ := by
      field_simp
      ring
    rw [harg]
  set A' : ℝ → ℂ := fun ζ => m ζ * VK ζ with hA'
  -- the symbol identity
  have hS : (fun ξ : ℝ => m ((ξ - c) / ε) * FourierTransform.fourier (G : ℝ → ℂ) ξ)
      = (ε : ℂ)⁻¹ • (fun ξ : ℝ => A' ((ξ - c) / ε)) := by
    funext ξ
    rw [Pi.smul_apply, smul_eq_mul]
    simp only [hA']
    rw [hFK1' ξ]
    rw [show (ε : ℂ)⁻¹ * (m ((ξ - c) / ε)
            * ((ε : ℂ) * FourierTransform.fourier (G : ℝ → ℂ) ξ))
        = ((ε : ℂ)⁻¹ * (ε : ℂ))
            * (m ((ξ - c) / ε) * FourierTransform.fourier (G : ℝ → ℂ) ξ) by ring,
      inv_mul_cancel₀ hεc, one_mul]
  -- the pointwise identity after applying `𝓕⁻`
  have hL : ∀ x, FourierTransformInv.fourierInv
        (fun ξ : ℝ => m ((ξ - c) / ε) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x
      = rmodFun c x * multOp m VK (ε * x) := by
    intro x
    rw [hS, fourierInv_const_smul', fourierInv_affine A' ε c x hε, hA',
      fourierInv_mul_eq_multOp]
    rw [smul_eq_mul]
    rw [show (ε : ℂ)⁻¹ * (rmodFun c x * (ε : ℂ) * multOp m VK (ε * x))
        = ((ε : ℂ)⁻¹ * (ε : ℂ)) * (rmodFun c x * multOp m VK (ε * x)) by ring,
      inv_mul_cancel₀ hεc, one_mul]
  set Op : ℝ → ℂ := multOp m VK with hOp
  -- `Op` is continuous (hence measurable)
  have hOpcont : Continuous Op := by
    have hVint : Integrable VK := by
      rw [hVK]
      simpa only [SchwartzMap.fourier_coe] using
        (SchwartzMap.integrable (FourierTransform.fourier K1) (μ := volume))
    have hAint : Integrable (fun ξ : ℝ => m ξ • VK ξ) := by
      have := hVint.bdd_mul hmCD.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hm0)
      simpa only [smul_eq_mul] using this
    have hcont := Commons.Analysis.Integral.continuous_integral_czE_smul
      (fun ξ : ℝ => m ξ • VK ξ) hAint
    rw [hOp]
    refine hcont.congr (fun x => ?_)
    simp only [multOp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    unfold czE
    simp only [smul_eq_mul]
    ring
  -- Mikhlin, converted to lower integrals
  have hOp_bound : ∫⁻ y : ℝ, ‖Op y‖ₑ ^ q
      ≤ ENNReal.ofReal ((Cq * A) ^ q) * ∫⁻ y : ℝ, ‖(K1 : ℝ → ℂ) y‖ₑ ^ q := by
    have hmik := hCq m A hA hmCD hm0 hm1 hm2 K1
    have hr : (eLpNorm Op (ENNReal.ofReal q) (volume : Measure ℝ)) ^ q
        ≤ (ENNReal.ofReal (Cq * A)
            * eLpNorm (K1 : ℝ → ℂ) (ENNReal.ofReal q) (volume : Measure ℝ)) ^ q := by
      have hEq : Op
          = fun x : ℝ => ∫ ξ : ℝ, (m ξ * czE x ξ)
              • FourierTransform.fourier (K1 : ℝ → ℂ) ξ := by
        rw [hOp, hVK]; rfl
      rw [hEq]
      exact ENNReal.rpow_le_rpow hmik hqpos.le
    rw [eLpNorm_rpow_eq_lintegral hqpos Op hOpcont.aestronglyMeasurable,
      ENNReal.mul_rpow_of_nonneg _ _ hqpos.le,
      eLpNorm_rpow_eq_lintegral hqpos (K1 : ℝ → ℂ) K1.continuous.aestronglyMeasurable,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCqpos.le hA) hqpos.le] at hr
    exact hr
  -- the `K₁` integral
  have hK1int : ∫⁻ y : ℝ, ‖(K1 : ℝ → ℂ) y‖ₑ ^ q
      = ENNReal.ofReal ε * ∫⁻ y : ℝ, ‖(G : ℝ → ℂ) y‖ₑ ^ q := by
    have h1 : ∫⁻ y : ℝ, ‖(K1 : ℝ → ℂ) y‖ₑ ^ q
        = ∫⁻ y : ℝ, ‖(G : ℝ → ℂ) (ε⁻¹ * y)‖ₑ ^ q := by
      refine lintegral_congr (fun y => ?_)
      rw [← ofReal_norm, ← ofReal_norm, hK1norm y]
    rw [h1, lintegral_comp_mul_left_affine (fun y : ℝ => ‖(G : ℝ → ℂ) y‖ₑ ^ q)
      (ENNReal.continuous_rpow_const.comp (G.continuous.enorm)).measurable ε⁻¹ (inv_pos.mpr hε)]
    simp only [inv_inv]
  -- the left-hand side
  have hLHS1 : ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => m ((ξ - c) / ε) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ q
      = ∫⁻ x : ℝ, ‖Op (ε * x)‖ₑ ^ q := by
    refine lintegral_congr (fun x => ?_)
    rw [hL x, enorm_mul,
      show ‖rmodFun c x‖ₑ = 1 by rw [← ofReal_norm, rmodFun_norm, ENNReal.ofReal_one],
      one_mul]
  have hLHS2 : ∫⁻ x : ℝ, ‖Op (ε * x)‖ₑ ^ q
      = ENNReal.ofReal ε⁻¹ * ∫⁻ y : ℝ, ‖Op y‖ₑ ^ q :=
    lintegral_comp_mul_left_affine (fun y : ℝ => ‖Op y‖ₑ ^ q)
      (ENNReal.continuous_rpow_const.comp hOpcont.enorm).measurable ε hε
  calc ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => m ((ξ - c) / ε) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ q
      = ∫⁻ x : ℝ, ‖Op (ε * x)‖ₑ ^ q := hLHS1
    _ = ENNReal.ofReal ε⁻¹ * ∫⁻ y : ℝ, ‖Op y‖ₑ ^ q := hLHS2
    _ ≤ ENNReal.ofReal ε⁻¹
          * (ENNReal.ofReal ((Cq * A) ^ q) * ∫⁻ y : ℝ, ‖(K1 : ℝ → ℂ) y‖ₑ ^ q) :=
        mul_le_mul_of_nonneg_left hOp_bound bot_le
    _ = ENNReal.ofReal ε⁻¹
          * (ENNReal.ofReal ((Cq * A) ^ q)
              * (ENNReal.ofReal ε * ∫⁻ y : ℝ, ‖(G : ℝ → ℂ) y‖ₑ ^ q)) := by rw [hK1int]
    _ = ENNReal.ofReal ((Cq * A) ^ q) * ∫⁻ y : ℝ, ‖(G : ℝ → ℂ) y‖ₑ ^ q := by
        have hεmul : ENNReal.ofReal ε⁻¹ * ENNReal.ofReal ε = 1 := by
          rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hε)), inv_mul_cancel₀ hε.ne',
            ENNReal.ofReal_one]
        have hinner : ENNReal.ofReal ε⁻¹
              * (ENNReal.ofReal ε * ∫⁻ y : ℝ, ‖(G : ℝ → ℂ) y‖ₑ ^ q)
            = ∫⁻ y : ℝ, ‖(G : ℝ → ℂ) y‖ₑ ^ q := by
          rw [← mul_assoc, hεmul, one_mul]
        rw [mul_left_comm, hinner]

end

end Work.BourgainPlan.IonescuWainger
