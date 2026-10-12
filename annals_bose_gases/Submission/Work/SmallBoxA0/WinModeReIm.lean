import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.WinMode
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-288 (cont.) — the real/imaginary mode identities for an arbitrary window

`winQMode χ ℓ p y = χ(y)e^{−i⟨p,y⟩} − ℓ^{−3} winChat χ ℓ p` is complex, so its real and
imaginary parts decompose as

    winQModeRe χ ℓ p y = χ(y)·cos⟨p,y⟩ − ℓ^{−3}·(winChat χ ℓ p).re
    winQModeIm χ ℓ p y = −χ(y)·sin⟨p,y⟩ − ℓ^{−3}·(winChat χ ℓ p).im

(the window-generic counterparts of `qModeRe_eq` / `qModeIm_eq` of
`Submission/Work/SmallBoxD1KinIntegrable.lean`), together with the resulting DECOMPOSITION of
the slot integrals `∫_{acube s} winQModeRe χ s p z·Φ(x_{i↦z})dz` into a χ-cosine overlap and the
`p`-independent term `(s³)⁻¹(winChat.re)·∫Φ`.  These are the algebra steps that turn the
integrability of the windowed kinetic word into the Fourier decay of `χ·(Φ∘update)`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1 The exponential's real and imaginary parts -/

/-- `(e^{−i⟨p,z⟩}).re = cos⟨p,z⟩`. -/
lemma win_exp_neg_inner_re (p z : ℝ³) :
    (Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))).re = Real.cos (inner ℝ p z) := by
  have h : -(Complex.I * ((inner ℝ p z : ℝ) : ℂ))
      = (((-inner ℝ p z : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- `(e^{−i⟨p,z⟩}).im = −sin⟨p,z⟩`. -/
lemma win_exp_neg_inner_im (p z : ℝ³) :
    (Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))).im = -Real.sin (inner ℝ p z) := by
  have h : -(Complex.I * ((inner ℝ p z : ℝ) : ℂ))
      = (((-inner ℝ p z : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

/-! ## 2 The real and imaginary parts of the windowed mode -/

/-- the real part of the windowed mode. -/
lemma winQModeRe_apply (χ : ℝ³ → ℝ) (ℓ : ℝ) (p z : ℝ³) :
    winQModeRe χ ℓ p z = χ z * Real.cos (inner ℝ p z) - (ℓ ^ 3)⁻¹ * (winChat χ ℓ p).re := by
  have hexp := win_exp_neg_inner_re p z
  have hk : (((ℓ ^ 3 : ℝ) : ℂ))⁻¹ = (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) :=
    (Complex.ofReal_inv (ℓ ^ 3 : ℝ)).symm
  have hk' : ((ℓ : ℂ) ^ 3)⁻¹ = (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow ℓ 3]; exact hk
  rw [winQModeRe, winQMode, Complex.sub_re, Complex.mul_re, Complex.mul_re, hexp, hk']
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- the imaginary part of the windowed mode. -/
lemma winQModeIm_apply (χ : ℝ³ → ℝ) (ℓ : ℝ) (p z : ℝ³) :
    winQModeIm χ ℓ p z = -(χ z * Real.sin (inner ℝ p z) + (ℓ ^ 3)⁻¹ * (winChat χ ℓ p).im) := by
  have hexp := win_exp_neg_inner_im p z
  have hk : (((ℓ ^ 3 : ℝ) : ℂ))⁻¹ = (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) :=
    (Complex.ofReal_inv (ℓ ^ 3 : ℝ)).symm
  have hk' : ((ℓ : ℂ) ^ 3)⁻¹ = (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow ℓ 3]; exact hk
  rw [winQModeIm, winQMode, Complex.sub_im, Complex.mul_im, Complex.mul_im, hexp, hk']
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  ring

/-! ## 3 The slot decomposition -/

/-- **The slot decomposition of the real part.**  `∫_{acube s} (Re g_p)·Φ(x_{i↦·})` is the
χ-cosine overlap minus the (`p`-dependent) constant `(s³)⁻¹(winChat.re)` times `∫Φ`. -/
lemma winQModeRe_slot_split {χ : ℝ³ → ℝ} {s : ℝ} (hs : 0 < s) (hχc : Continuous χ) {n : ℕ}
    (p : ℝ³) {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) (x : X (n + 1)) (i : Fin (n + 1)) :
    (∫ z in acube s, winQModeRe χ s p z * Φ (Function.update x i z))
      = (∫ z in acube s, χ z * Real.cos (inner ℝ p z) * Φ (Function.update x i z))
        - ((s ^ 3)⁻¹ * (winChat χ s p).re) * (∫ z in acube s, Φ (Function.update x i z)) := by
  have hint : (∫ z in acube s, winQModeRe χ s p z * Φ (Function.update x i z))
      = ∫ z in acube s, (χ z * Real.cos (inner ℝ p z) * Φ (Function.update x i z)
          - ((s ^ 3)⁻¹ * (winChat χ s p).re) * Φ (Function.update x i z)) := by
    refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
    rw [winQModeRe_apply]; ring
  rw [hint]
  have hcont1 : Continuous (fun z : ℝ³ =>
      χ z * Real.cos (inner ℝ p z) * Φ (Function.update x i z)) :=
    ((hχc.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))).mul
      (hΦ.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id)))
  have hcont2 : Continuous (fun z : ℝ³ =>
      ((s ^ 3)⁻¹ * (winChat χ s p).re) * Φ (Function.update x i z)) :=
    continuous_const.mul
      (hΦ.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id))
  rw [MeasureTheory.integral_sub
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont1.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont2.continuousOn)]
  rw [MeasureTheory.integral_const_mul]

/-- **The slot decomposition of the imaginary part.** -/
lemma winQModeIm_slot_split {χ : ℝ³ → ℝ} {s : ℝ} (hs : 0 < s) (hχc : Continuous χ) {n : ℕ}
    (p : ℝ³) {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) (x : X (n + 1)) (i : Fin (n + 1)) :
    (∫ z in acube s, winQModeIm χ s p z * Φ (Function.update x i z))
      = -((∫ z in acube s, χ z * Real.sin (inner ℝ p z) * Φ (Function.update x i z))
        + ((s ^ 3)⁻¹ * (winChat χ s p).im) * (∫ z in acube s, Φ (Function.update x i z))) := by
  have hint : (∫ z in acube s, winQModeIm χ s p z * Φ (Function.update x i z))
      = ∫ z in acube s, (-(χ z * Real.sin (inner ℝ p z) * Φ (Function.update x i z))
          - ((s ^ 3)⁻¹ * (winChat χ s p).im) * Φ (Function.update x i z)) := by
    refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
    rw [winQModeIm_apply]; ring
  rw [hint]
  have hcont1 : Continuous (fun z : ℝ³ =>
      -(χ z * Real.sin (inner ℝ p z) * Φ (Function.update x i z))) :=
    (((hχc.mul (Real.continuous_sin.comp (continuous_const.inner continuous_id))).mul
      (hΦ.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id)))).neg
  have hcont2 : Continuous (fun z : ℝ³ =>
      ((s ^ 3)⁻¹ * (winChat χ s p).im) * Φ (Function.update x i z)) :=
    continuous_const.mul
      (hΦ.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id))
  rw [MeasureTheory.integral_sub
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont1.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont2.continuousOn)]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
  ring

end Work.SmallBoxA0
