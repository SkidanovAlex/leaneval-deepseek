import Mathlib
import Submission.Work.BSKinetic.familyFormUnproj_eq_kernelForm
import Submission.Work.OneBodyKin.fourier_convScale
import Submission.Work.OneBodyKin.quadForm_conv_eq_fourier
import Submission.Work.SmallBoxBridge.Kernel.kinKernelC_eq_ofReal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol` — the unprojected family form in Fourier space

For a *radial* symbol `F(‖·‖)` with `p ↦ F ‖p‖ ∈ L¹(ℝ³)` the unprojected moving-box family form
of FS's `lem:LocKinEn` is diagonal in the `p`-convention Fourier transform, with the explicit
symbol `symA`:

  `bsFamilyFormUnproj ℓ F ψ = (2π)⁻³ ∫_q symA ℓ F q · ‖kinFT ψ q‖² dq`,

where `symA ℓ F q = (2π)⁻³ ∫_p F ‖q + ℓ⁻¹ • p‖ · profHat(p)² dp` (`Work.OneBodyKin.symA`).

## Proof

* `Work.BSKinetic.familyFormUnproj_eq_kernelForm` identifies the family form with the quadratic
  form of the convolution kernel `k = convScale ℓ · kinKernel F`;
* `Work.OneBodyKin.quadForm_conv_eq_fourier` (Plancherel for a convolution quadratic form)
  rewrites that quadratic form as `(2π)⁻³ ∫_q Re(kinFT k q)·‖kinFT ψ q‖²`;
* it remains to identify the Fourier transform of the *product* `convScale ℓ · kinKernel F` with
  `symA ℓ F q`.  This is the content of `ftKernelConvScale_eq_symA`: expanding the kernel
  `kinKernel F z = (2π)⁻³∫_p F‖p‖ e^{i⟪p,z⟫}dp = kinKernelC F z`
  (`Work.SmallBoxBridge.Kernel.kinKernelC_eq_ofReal`), Fubini over `(z,p)` and the closed form
  `∫_z convScale ℓ z · e^{-i⟪r,z⟫}dz = ℓ³ profHat(ℓ • r)²` (`fourier_convScale`) give

    `∫_z k z · e^{-i⟪q,z⟫}dz = (2π)⁻³ ℓ³ ∫_p F‖p‖ profHat(ℓ • (q − p))² dp`,

  which is `symA ℓ F q` by the change of variables `symA_eq_shiftedIntegral`
  (`v = ℓ • x`, then the translation `x = p − q`, then evenness of `profHat`).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Auxiliary facts about the window autocorrelation -/

private lemma hasCompactSupport_convScale {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasCompactSupport (Submission.BoseGases.convScale ℓ) := by
  have hchi : HasCompactSupport Submission.BoseGases.chi :=
    Submission.BoseGases.chi_hasCompactSupport
  have hconv : HasCompactSupport (fun x : ℝ³ =>
      Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x) := by
    rw [Submission.BoseGases.conv3_eq_convolution]
    exact hchi.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hchi
  have hpre : HasCompactSupport (fun z : ℝ³ =>
      Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi (ℓ⁻¹ • z)) := by
    have h := hconv.comp_homeomorph (Homeomorph.smulOfNeZero ℓ⁻¹ (inv_ne_zero (ne_of_gt hℓ)))
    simpa [Homeomorph.smulOfNeZero, Function.comp_def] using h
  unfold Submission.BoseGases.convScale
  exact hpre

private lemma integrable_convScale {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.Integrable (Submission.BoseGases.convScale ℓ) :=
  (Work.BSKinetic.continuous_convScale ℓ).integrable_of_hasCompactSupport
    (hasCompactSupport_convScale hℓ)

/-- The convolution kernel `convScale ℓ · kinKernel F` of the unprojected family form is
integrable: it is supported in a compact set (`convScale ℓ` is) and bounded (`kinKernel_bdd`). -/
lemma integrable_convScale_mul_kinKernel {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) :
    MeasureTheory.Integrable
      (fun z : ℝ³ => Submission.BoseGases.convScale ℓ z * Submission.BoseGases.kinKernel F z) := by
  refine (integrable_convScale hℓ).mul_bdd (c := ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, ‖F ‖p‖‖)
    ((Work.SmallBoxBridge.Resolve.kinKernel_stronglyMeasurable hFi).aestronglyMeasurable) ?_
  filter_upwards with z
  exact Work.SmallBoxBridge.Resolve.kinKernel_bdd F hFi z

/-! ## The change of variables in `symA` -/

/-- The symbol `symA ℓ F q = (2π)⁻³∫_p F‖q + ℓ⁻¹•p‖ profHat(p)²` with the `F`-factor carrying
the momentum: the dilation `v = ℓ • x` (`v`-volume factor `ℓ³`), the translation `x = p − q` and
the evenness of `profHat` give

  `symA ℓ F q = (2π)⁻³ · ℓ³ ∫_p F‖p‖ · profHat(ℓ • (q − p))²`. -/
lemma symA_eq_shiftedIntegral {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) (q : ℝ³) :
    symA ℓ F q = ((2 * Real.pi) ^ 3)⁻¹ *
      (ℓ ^ 3 * ∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • (q - p))) ^ 2) := by
  have hdil : (∫ v : ℝ³, F ‖q + ℓ⁻¹ • v‖ * (profHat v) ^ 2)
      = ℓ ^ 3 * ∫ x : ℝ³, F ‖q + x‖ * (profHat (ℓ • x)) ^ 2 := by
    rw [Submission.BoseGases.integral_comp_smul_right
      (fun v : ℝ³ => F ‖q + ℓ⁻¹ • v‖ * (profHat v) ^ 2) hℓ]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    have hx : ℓ⁻¹ • (ℓ • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
    rw [hx]
  have htr : (∫ x : ℝ³, F ‖q + x‖ * (profHat (ℓ • x)) ^ 2)
      = ∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • (p - q))) ^ 2 := by
    rw [← Submission.BoseGases.integral_comp_add_left
      (fun p : ℝ³ => F ‖p‖ * (profHat (ℓ • (p - q))) ^ 2) q]
    apply integral_congr_ae
    filter_upwards with x
    have h1 : q + x - q = x := by abel
    rw [h1]
  have heven : (∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • (p - q))) ^ 2)
      = ∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • (q - p))) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with p
    have h1 : ℓ • (p - q) = -(ℓ • (q - p)) := by module
    rw [h1, profHat_even]
  unfold symA
  rw [hdil, htr, heven]

/-! ## The Fourier transform of the kernel `convScale ℓ · kinKernel F` -/

/-- The product formula for the two phases around a shift: `e^{i⟪p,z⟫}·e^{-i⟪q,z⟫}
= e^{-i⟪q−p,z⟫}`. -/
private lemma exp_inner_mul_exp_inner_neg (p q z : ℝ³) :
    Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ (q - p) z : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_sub_left]
  push_cast
  ring

set_option maxHeartbeats 3200000 in
/-- The Fourier transform of the kernel of the unprojected family form, in complex form:
expanding `kinKernel F` as its `e^{i⟪p,z⟫}`-integral, Fubini in `(z,p)` and `fourier_convScale`
give `∫_z k z e^{-i⟪q,z⟫}dz = (2π)⁻³ ℓ³ ∫_p F‖p‖ profHat(ℓ • (q − p))² dp`. -/
private lemma ftKernelConvScale_eq_symA_core {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) (q : ℝ³) :
    (∫ z : ℝ³, (Submission.BoseGases.convScale ℓ z : ℂ) * (Submission.BoseGases.kinKernel F z : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = ((((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 3 *
          ∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • (q - p))) ^ 2) : ℝ) : ℂ) := by
  set Φ : ℝ³ → ℝ³ → ℂ := fun z p =>
      (Submission.BoseGases.convScale ℓ z : ℂ) *
        ((F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))) with hΦ
  -- joint integrability of the `(z,p)`-integrand: it is dominated by the product
  -- `‖convScale ℓ z‖ · ‖F ‖p‖‖`, which is integrable for the product measure
  have hΦint : MeasureTheory.Integrable (Function.uncurry Φ) (volume.prod volume) := by
    have hdom : MeasureTheory.Integrable
        (fun w : ℝ³ × ℝ³ => ‖Submission.BoseGases.convScale ℓ w.1‖ * ‖F ‖w.2‖‖)
        (volume.prod volume) :=
      (integrable_convScale hℓ).norm.mul_prod hFi.norm
    refine Integrable.mono' hdom ?_ ?_
    · have h1 : AEStronglyMeasurable (fun w : ℝ³ × ℝ³ =>
          (Submission.BoseGases.convScale ℓ w.1 : ℂ)) (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          ((Work.BSKinetic.continuous_convScale ℓ).comp continuous_fst).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun w : ℝ³ × ℝ³ => (F ‖w.2‖ : ℂ)) (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable (hFi.1.comp_snd)
      have h3 : Continuous (fun w : ℝ³ × ℝ³ =>
          Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))) := by
        apply Complex.continuous_exp.comp
        exact continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_snd.prodMk continuous_fst)))
      have h4 : Continuous (fun w : ℝ³ × ℝ³ =>
          Complex.exp (-(Complex.I * (inner ℝ q w.1 : ℂ)))) := by
        apply Complex.continuous_exp.comp
        apply Continuous.neg
        exact continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_const.prodMk continuous_fst)))
      have h5 : AEStronglyMeasurable (fun w : ℝ³ × ℝ³ =>
          (Submission.BoseGases.convScale ℓ w.1 : ℂ) *
            ((F ‖w.2‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))) *
            Complex.exp (-(Complex.I * (inner ℝ q w.1 : ℂ)))) (volume.prod volume) := by
        convert (h1.mul (h2.mul h3.aestronglyMeasurable)).mul h4.aestronglyMeasurable using 1
        all_goals
          funext w
          simp only [Pi.mul_apply]
      change AEStronglyMeasurable (fun w : ℝ³ × ℝ³ => Φ w.1 w.2) (volume.prod volume)
      exact h5
    · filter_upwards with w
      simp only [Function.uncurry, hΦ, norm_mul, Work.SmallBoxBridge.Resolve.cnorm_ofReal,
        Work.SmallBoxBridge.Resolve.norm_exp_I_mul,
        Work.SmallBoxBridge.Resolve.norm_exp_neg_I_mul, mul_one]
      exact le_of_eq (by ring)
  -- the kernel is the constant `(2π)⁻³` times its `e^{i⟪p,z⟫}`-integral
  have hstep1 : (∫ z : ℝ³, (Submission.BoseGases.convScale ℓ z : ℂ) *
        (Submission.BoseGases.kinKernel F z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ z : ℝ³, ∫ p : ℝ³, Φ z p := by
    have hper : ∀ z : ℝ³, (Submission.BoseGases.convScale ℓ z : ℂ) *
          (Submission.BoseGases.kinKernel F z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))
        = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ p : ℝ³, Φ z p := by
      intro z
      rw [← Work.SmallBoxBridge.Kernel.kinKernelC_eq_ofReal F z,
        Submission.BoseGases.kinKernelC]
      simp only [hΦ]
      rw [integral_mul_const, integral_const_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hper), integral_const_mul]
  -- Fubini in `(z,p)`
  have hstep2 : (∫ z : ℝ³, ∫ p : ℝ³, Φ z p) = ∫ p : ℝ³, ∫ z : ℝ³, Φ z p :=
    MeasureTheory.integral_integral_swap hΦint
  -- the `z`-integral at fixed `p` is `ℓ³ profHat(ℓ • (q − p))²`
  have hstep3 : ∀ p : ℝ³, (∫ z : ℝ³, Φ z p)
      = (F ‖p‖ : ℂ) * ((ℓ : ℂ) ^ 3 * ((profHat (ℓ • (q - p)) : ℝ) : ℂ) ^ 2) := by
    intro p
    have hpt : (fun z : ℝ³ => Φ z p) = fun z : ℝ³ => (F ‖p‖ : ℂ) *
        ((Submission.BoseGases.convScale ℓ z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ (q - p) z : ℂ)))) := by
      funext z
      simp only [hΦ]
      rw [show (Submission.BoseGases.convScale ℓ z : ℂ) *
            ((F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))) *
            Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))
          = (F ‖p‖ : ℂ) * ((Submission.BoseGases.convScale ℓ z : ℂ) *
            (Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
              Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))) from by ring]
      rw [exp_inner_mul_exp_inner_neg p q z]
    rw [hpt, integral_const_mul, fourier_convScale hℓ (q - p)]
  -- back to the real `p`-integral
  have hstep4 : (∫ p : ℝ³, ∫ z : ℝ³, Φ z p)
      = (((ℓ ^ 3 * ∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • (q - p))) ^ 2) : ℝ) : ℂ) := by
    rw [show (fun p : ℝ³ => ∫ z : ℝ³, Φ z p) = fun p : ℝ³ =>
        (F ‖p‖ : ℂ) * ((ℓ : ℂ) ^ 3 * ((profHat (ℓ • (q - p)) : ℝ) : ℂ) ^ 2) from
      funext hstep3]
    rw [show (fun p : ℝ³ => (F ‖p‖ : ℂ) * ((ℓ : ℂ) ^ 3 * ((profHat (ℓ • (q - p)) : ℝ) : ℂ) ^ 2))
        = fun p : ℝ³ => (((ℓ ^ 3 * (F ‖p‖ * (profHat (ℓ • (q - p))) ^ 2)) : ℝ) : ℂ) from by
      funext p
      push_cast
      ring]
    rw [show (∫ p : ℝ³, (((ℓ ^ 3 * (F ‖p‖ * (profHat (ℓ • (q - p))) ^ 2)) : ℝ) : ℂ))
        = ((∫ p : ℝ³, (ℓ ^ 3 * (F ‖p‖ * (profHat (ℓ • (q - p))) ^ 2)) : ℝ) : ℂ)
        from integral_ofReal]
    rw [integral_const_mul]
  rw [hstep1, hstep2, hstep4]
  push_cast
  ring

/-- **The Fourier transform of the kernel of the unprojected family form.**  The real part of
`∫_z convScale ℓ z · kinKernel F z · e^{-i⟪q,z⟫}dz` is the symbol `symA ℓ F q`. -/
lemma kinKernel_mul_convScale_fourier_re {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) (q : ℝ³) :
    (∫ z : ℝ³, ((Submission.BoseGases.convScale ℓ z * Submission.BoseGases.kinKernel F z : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))).re = symA ℓ F q := by
  have h1 : (∫ z : ℝ³, ((Submission.BoseGases.convScale ℓ z * Submission.BoseGases.kinKernel F z : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = ∫ z : ℝ³, (Submission.BoseGases.convScale ℓ z : ℂ) *
        (Submission.BoseGases.kinKernel F z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [Complex.ofReal_mul]
  rw [h1, ftKernelConvScale_eq_symA_core hℓ hFi q, Complex.ofReal_re,
    symA_eq_shiftedIntegral hℓ F q]

/-! ## The unprojected family form in Fourier space -/

theorem bsFamilyFormUnproj_eq_symbol {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hFnn : ∀ r : ℝ, 0 ≤ F r) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BSKinetic.bsFamilyFormUnproj ℓ F ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.symA ℓ F q *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  rw [Work.BSKinetic.familyFormUnproj_eq_kernelForm hℓ ψ hψ hcs hFi hFnn]
  rw [Work.OneBodyKin.quadForm_conv_eq_fourier (k := fun z : ℝ³ =>
    Submission.BoseGases.convScale ℓ z * Submission.BoseGases.kinKernel F z)
    (integrable_convScale_mul_kinKernel hℓ hFi) hψ hcs]
  congr 1
  apply integral_congr_ae
  filter_upwards with q
  rw [kinKernel_mul_convScale_fourier_re hℓ hFi q]

end Work.OneBodyKin
