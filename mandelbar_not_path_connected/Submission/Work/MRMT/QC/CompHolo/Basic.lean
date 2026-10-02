/-
Work.MRMT.QC.CompHolo — local calculus facts for a holomorphic injection `f` with `deriv f ≠ 0`.

These are the elementary (but pointwise) ingredients used to show that quasiconformality with
dilatation `μ` is preserved by precomposition with a conformal map `f`:

* `fderiv_real_eq_smul_one`: the real Fréchet derivative of a complex differentiable `f` is
  multiplication by `deriv f z`;
* `dz_holo`, `dzbar_holo`: consequently `∂f = f'` and `∂̄f = 0`;
* `fderiv_comp_holo`, `dz_comp_holo`, `dzbar_comp_holo`: the chain rule for the pointwise
  Wirtinger derivatives when the inner map is holomorphic;
* `abs_det_fderiv_eq`: `|det (D f z)| = ‖f' z‖²`, the Jacobian of a conformal map.
-/
import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.QC

/-! ## The real Fréchet derivative of a holomorphic map -/

theorem fderiv_real_eq_smul_one {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    fderiv ℝ f z = deriv f z • (1 : ℂ →L[ℝ] ℂ) :=
  hf.hasDerivAt.complexToReal_fderiv.fderiv

theorem dz_holo {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) : dz f z = deriv f z := by
  have h : fderiv ℝ f z = deriv f z • (1 : ℂ →L[ℝ] ℂ) := fderiv_real_eq_smul_one hf
  rw [dz, h]
  show (((deriv f z • (1 : ℂ →L[ℝ] ℂ)) 1) -
      I * ((deriv f z • (1 : ℂ →L[ℝ] ℂ)) Complex.I)) / 2 = deriv f z
  rw [show (deriv f z • (1 : ℂ →L[ℝ] ℂ)) 1 = deriv f z by simp,
    show (deriv f z • (1 : ℂ →L[ℝ] ℂ)) Complex.I = deriv f z * Complex.I by simp]
  have : Complex.I * (deriv f z * Complex.I) = - deriv f z := by
    calc Complex.I * (deriv f z * Complex.I) = deriv f z * (Complex.I * Complex.I) := by ring
      _ = deriv f z * (-1) := by rw [Complex.I_mul_I]
      _ = - deriv f z := by ring
  rw [this]
  ring

theorem dzbar_holo {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) : dzbar f z = 0 := by
  have h : fderiv ℝ f z = deriv f z • (1 : ℂ →L[ℝ] ℂ) := fderiv_real_eq_smul_one hf
  rw [dzbar, h]
  show (((deriv f z • (1 : ℂ →L[ℝ] ℂ)) 1) +
      I * ((deriv f z • (1 : ℂ →L[ℝ] ℂ)) Complex.I)) / 2 = 0
  rw [show (deriv f z • (1 : ℂ →L[ℝ] ℂ)) 1 = deriv f z by simp,
    show (deriv f z • (1 : ℂ →L[ℝ] ℂ)) Complex.I = deriv f z * Complex.I by simp]
  have : Complex.I * (deriv f z * Complex.I) = - deriv f z := by
    calc Complex.I * (deriv f z * Complex.I) = deriv f z * (Complex.I * Complex.I) := by ring
      _ = deriv f z * (-1) := by rw [Complex.I_mul_I]
      _ = - deriv f z := by ring
  rw [this]
  ring

/-- An `ℝ`-linear endomorphism of `ℂ` is determined by its values on `1` and `I`. -/
theorem fderiv_complex_apply (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L Complex.I := by
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • (Complex.I : ℂ) :=
    Complex.ext (by simp) (by simp)
  rw [hw, map_add, map_smul, map_smul]
  simp

theorem fderiv_complex_apply_mul_I (L : ℂ →L[ℝ] ℂ) (c : ℂ) :
    L (c * Complex.I) = (-(c.im : ℂ)) * L 1 + (c.re : ℂ) * L Complex.I := by
  rw [fderiv_complex_apply]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem fderiv_comp_holo {g f : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℂ f z) :
    fderiv ℝ (g ∘ f) z = (fderiv ℝ g (f z)).comp (deriv f z • (1 : ℂ →L[ℝ] ℂ)) :=
  (hg.hasFDerivAt.comp z hf.hasDerivAt.complexToReal_fderiv).fderiv

/-- Chain rule for `∂` when the inner map is holomorphic. -/
theorem dz_comp_holo {g f : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℂ f z) : dz (g ∘ f) z = deriv f z * dz g (f z) := by
  rw [dz, (hg.hasFDerivAt.comp z hf.hasDerivAt.complexToReal_fderiv).fderiv, dz]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [show (deriv f z • (1 : ℂ →L[ℝ] ℂ)) 1 = deriv f z by simp,
    show (deriv f z • (1 : ℂ →L[ℝ] ℂ)) Complex.I = deriv f z * Complex.I by simp]
  rw [fderiv_complex_apply (fderiv ℝ g (f z)) (deriv f z),
    fderiv_complex_apply_mul_I (fderiv ℝ g (f z)) (deriv f z)]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

/-- Chain rule for `∂̄` when the inner map is holomorphic. -/
theorem dzbar_comp_holo {g f : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℂ f z) : dzbar (g ∘ f) z = star (deriv f z) * dzbar g (f z) := by
  rw [dzbar, (hg.hasFDerivAt.comp z hf.hasDerivAt.complexToReal_fderiv).fderiv, dzbar]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [show (deriv f z • (1 : ℂ →L[ℝ] ℂ)) 1 = deriv f z by simp,
    show (deriv f z • (1 : ℂ →L[ℝ] ℂ)) Complex.I = deriv f z * Complex.I by simp]
  rw [fderiv_complex_apply (fderiv ℝ g (f z)) (deriv f z),
    fderiv_complex_apply_mul_I (fderiv ℝ g (f z)) (deriv f z)]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

/-! ## The Jacobian of a conformal map -/

/-- The determinant of multiplication by `c` on `ℂ`, viewed as an `ℝ`-linear map, is
`‖c‖²`. -/
theorem det_smul_one (c : ℂ) :
    LinearMap.det ((c • (1 : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)) = Complex.normSq c := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  have hm : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
      (c • (1 : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = !![c.re, -c.im; c.im, c.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr, mul_re,
        mul_im]
  rw [hm]
  simp [Complex.normSq_apply]

/-- **The Jacobian of a holomorphic map**: `|det (D f z)| = ‖f' z‖²`. -/
theorem abs_det_fderiv_eq {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    |(fderiv ℝ f z).det| = ‖deriv f z‖ ^ 2 := by
  rw [fderiv_real_eq_smul_one hf]
  change |LinearMap.det ((deriv f z • (1 : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))| = ‖deriv f z‖ ^ 2
  rw [det_smul_one, Complex.normSq_eq_norm_sq]
  exact abs_of_nonneg (by positivity)

end Work.MRMT.QC
