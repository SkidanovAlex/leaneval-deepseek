import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.SmallBoxD1PerP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-281 (cont.) — integrability of the D1 KINETIC half

`SmallBoxD1PerP.kinPWord` is `(2π)⁻¹³ * ∫ p, fsKinCoeff c ‖p‖ * (modeP …)`; the D1
integration needs this Bochner integral to be non-junk, i.e. the integrand `Integrable`.
This module reduces that to the DECAY of the χ-cosine mode overlaps:

  `qModeRe s p z = χ_s(z)·cos⟨p,z⟩ − (s³)⁻¹·(modeChat s p).re`   (★)

so that `boxOp s 1 (qModeRe s p) Φ x` is a sum of the `χ`-cosine overlaps
`A_i(x,p) = ∫_{acube}χ(z)cos⟨p,z⟩Φ(x_{i←z})dz` (which is the real part of
`𝓕(χ·Φ_i^x)(p/2π)` — a compactly supported SMOOTH function, hence with rapidly decaying
Fourier transform) and the `p`-independent integral `B_i(x) = ∫_{acube}Φ(x_{i←z})dz`.

## Contents

* `qModeRe_eq`, `qModeIm_eq` — the real/imaginary parts of the mode (★);
* `boxOp_qModeRe_eq` — the decomposition of `boxOp s 1 (qModeRe s p) Φ x`;
* `sq_sum_le_card_mul_sum_sq_card` — the `(ΣJ)² ≤ (n+1)ΣJ²` Cauchy–Schwarz step;
* `cosCoeff_eq_re_fourier` — `∫χ(z)cos⟨p,z⟩Ψ(z)dz = (𝓕(χΨ)((2π)⁻¹•p)).re`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 The real and imaginary parts of the momentum mode -/

/-- the exponential of a negative inner product: `(e^{−i⟨p,z⟩}).re = cos⟨p,z⟩`. -/
lemma exp_neg_inner_re (p z : ℝ³) :
    (Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))).re = Real.cos (inner ℝ p z) := by
  have h : -(Complex.I * ((inner ℝ p z : ℝ) : ℂ))
      = (((-inner ℝ p z : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **(★)** the real part of the mode: `qModeRe s p z = χ_s(z)cos⟨p,z⟩ − (s³)⁻¹(modeChat s p).re`. -/
lemma qModeRe_eq (ℓ : ℝ) (p z : ℝ³) :
    qModeRe ℓ p z = chiScale ℓ z * Real.cos (inner ℝ p z) - (ℓ ^ 3)⁻¹ * (modeChat ℓ p).re := by
  have hexp := exp_neg_inner_re p z
  have hk : (((ℓ ^ 3 : ℝ) : ℂ))⁻¹ = (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) :=
    (Complex.ofReal_inv (ℓ ^ 3 : ℝ)).symm
  have hk' : ((ℓ : ℂ) ^ 3)⁻¹ = (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow ℓ 3]; exact hk
  rw [qModeRe, qMode, Complex.sub_re, Complex.mul_re, Complex.mul_re, hexp, hk']
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- a helper: `((ℓ : ℂ)⁻¹)^k = ↑((ℓ⁻¹)^k : ℝ)`. -/
lemma ofReal_inv_pow_eq (ℓ : ℝ) (k : ℕ) : ((ℓ : ℂ)⁻¹) ^ k = (((ℓ⁻¹) ^ k : ℝ) : ℂ) := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_pow]

/-- the imaginary part of the mode. -/
lemma qModeIm_eq (ℓ : ℝ) (p z : ℝ³) :
    qModeIm ℓ p z = - (chiScale ℓ z * Real.sin (inner ℝ p z) + (ℓ ^ 3)⁻¹ * (modeChat ℓ p).im) := by
  have hexp : (Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))).im
      = -Real.sin (inner ℝ p z) := by
    have h : -(Complex.I * ((inner ℝ p z : ℝ) : ℂ))
        = (((-inner ℝ p z : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    rw [h, Complex.exp_ofReal_mul_I_im]
    rw [Real.sin_neg]
  have hk' : ((ℓ : ℂ) ^ 3)⁻¹ = (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow ℓ 3]
    exact (Complex.ofReal_inv (ℓ ^ 3 : ℝ)).symm
  rw [qModeIm, qMode, Complex.sub_im, Complex.mul_im, Complex.mul_im, hexp, hk']
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  ring


/-! ## 2 The decomposition of `boxOp s 1 (qModeRe s p) Φ x` -/

/-- **The `χ`-cosine decomposition** of the kinetic mode operator. -/
lemma boxOp_qModeRe_eq {s : ℝ} (hs : 0 < s) {n : ℕ} (p : ℝ³)
    {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) (x : X (n + 1)) :
    boxOp s (fun _ => (1 : ℝ)) (qModeRe s p) Φ x
      = ∑ i : Fin (n + 1),
          ((∫ z in acube s, chiScale s z * Real.cos (inner ℝ p z) * Φ (Function.update x i z))
            - ((s ^ 3)⁻¹ * (modeChat s p).re) *
                (∫ z in acube s, Φ (Function.update x i z))) := by
  rw [boxOp]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_mul]
  rw [show (∫ z in acube s, qModeRe s p z * Φ (Function.update x i z))
      = ∫ z in acube s, (chiScale s z * Real.cos (inner ℝ p z) * Φ (Function.update x i z)
          - ((s ^ 3)⁻¹ * (modeChat s p).re) * Φ (Function.update x i z)) from by
    refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
    rw [qModeRe_eq]
    ring]
  have hcont1 : Continuous fun z : ℝ³ =>
      chiScale s z * Real.cos (inner ℝ p z) * Φ (Function.update x i z) :=
    ((chiScale_continuous s).mul
      (Real.continuous_cos.comp (continuous_const.inner continuous_id))).mul
      (hΦ.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id))
  have hcont2 : Continuous fun z : ℝ³ =>
      ((s ^ 3)⁻¹ * (modeChat s p).re) * Φ (Function.update x i z) :=
    continuous_const.mul
      (hΦ.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id))
  rw [MeasureTheory.integral_sub
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont1.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont2.continuousOn)]
  rw [MeasureTheory.integral_const_mul]

/-! ## 3 The Cauchy–Schwarz step -/

/-- `(Σ_i J_i)² ≤ (n+1)·Σ_i J_i²` (the `Finset` Cauchy–Schwarz). -/
lemma sq_sum_fin_le {n : ℕ} (J : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), J i) ^ 2 ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1), (J i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := J)
  simpa using h


/-! ## 4 The chi-cosine overlap as a real Fourier coefficient -/

/-- **The Fourier identification of the chi-cosine overlap** (frequency form).
With `F := (chi_s * Psi) : C`, the cosine overlap against the oscillation
`cos(-2\pi<z,xi>)` is the real part of `F`'s Fourier transform at `xi`.  Since `F` is
compactly supported and smooth, this decays faster than any power of `||xi||` -- the engine
of the D1 kinetic integrability. -/
lemma cosCoeff_eq_re_fourier {s : ℝ} (hs : 0 < s) (ξ : ℝ³) {Ψ : ℝ³ → ℝ}
    (hΨ : Continuous Ψ) :
    (∫ z in acube s, chiScale s z * Real.cos (-2 * Real.pi * inner ℝ z ξ) * Ψ z)
      = (FourierTransform.fourier (fun z => ((chiScale s z * Ψ z : ℝ) : ℂ)) ξ).re := by
  set F : ℝ³ → ℂ := fun z => ((chiScale s z * Ψ z : ℝ) : ℂ) with hFdef
  have hFcont : Continuous F :=
    Complex.continuous_ofReal.comp ((chiScale_continuous s).mul hΨ)
  have hsupp : ∀ v, v ∉ acube s → F v = 0 := by
    intro v hv
    have hχ : chiScale s v = 0 := not_ne_iff.mp (fun hh => hv (chiScale_mem_acube hs hh))
    simp only [hFdef]
    rw [show chiScale s v * Ψ v = 0 from by rw [hχ, zero_mul], Complex.ofReal_zero]
  have hcube : (∫ v : ℝ³,
        Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v)
      = ∫ v in acube s,
          Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun v : ℝ³ =>
        Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v)
      (fun v hv => by rw [hsupp v hv, smul_zero])).symm
  have hcont : Continuous fun v : ℝ³ =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v := by
    fun_prop
  have hint : IntegrableOn (fun v : ℝ³ =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v) (acube s) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hs) hcont.continuousOn
  have hpt : ∀ z ∈ acube s,
      chiScale s z * Real.cos (-2 * Real.pi * inner ℝ z ξ) * Ψ z
        = (Complex.exp (↑(-2 * Real.pi * inner ℝ z ξ) * Complex.I) • F z).re := by
    intro z _
    have him : (F z).im = 0 := by simp [hFdef]
    have hre : (F z).re = chiScale s z * Ψ z := by simp [hFdef]
    rw [smul_eq_mul, Complex.mul_re, hre, him, mul_zero, sub_zero]
    rw [Complex.exp_ofReal_mul_I_re]
    ring
  have hmain : (FourierTransform.fourier F ξ).re
      = (∫ v in acube s,
          Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v).re := by
    rw [Real.fourier_eq', ← hcube]
  have hswap : (∫ v in acube s,
        Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v).re
      = ∫ v in acube s,
          (Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v).re :=
    (Complex.reCLM.integral_comp_comm (μ := (volume : Measure ℝ³).restrict (acube s))
      (φ := fun v : ℝ³ => Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v)
      hint).symm
  rw [hmain, hswap]
  exact setIntegral_congr_fun (acube_measurable s) hpt

end BoseGases
end Submission
