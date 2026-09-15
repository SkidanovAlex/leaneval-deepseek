import Submission.FUP.BMReduction
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# The `∂̄`-calculus on `ℂᵈ` and Hörmander's positivity condition

This module sets up the (small) part of the theory of several complex variables needed for
Cohen's §5 (`prop:psh_to_bounded_fourier`):

* the Wirtinger derivatives `∂/∂z_j` and `∂/∂z̄_j`, defined via `fderiv ℝ`;
* the `(0,1)`-forms and their `∂̄`;
* Hörmander's positivity condition `∂∂̄φ ≥ κ`, in the *distributional* form appropriate for a
  plurisubharmonic `φ` which is only upper semicontinuous.

For the last point we use the elementary identity, valid for every `C²` function `ψ`,
`4 ∂_j∂̄_kψ = ∂²_{x_jx_k}ψ + ∂²_{y_jy_k}ψ` (the mixed partials commute, so the imaginary part
vanishes).  Consequently the distributional pairing of `∂∂̄φ` against the rank-one positive test
tensors `α_j ᾱ_k` can be written purely in terms of *real* second derivatives of the test function,
which is the form in which it is most convenient to verify: the classical positivity of the
Hermitian Hessian of a smooth plurisubharmonic weight is a statement about the real Hessian
restricted to complex lines.
-/

namespace Submission.FUP

section Wirtinger

/-- The Wirtinger derivative `∂/∂z_j = ½(∂/∂x_j - i ∂/∂y_j)`, expressed through `fderiv ℝ`:
applied to the `j`-th coordinate vector `e_j` it gives `∂/∂x_j`, and applied to `I • e_j` it gives
`∂/∂y_j`. -/
noncomputable def partialZ (j : Fin d) (f : ℂᵈ → ℂ) (z : ℂᵈ) : ℂ :=
  (fderiv ℝ f z (Pi.single j 1) - Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2

/-- The Wirtinger derivative `∂/∂z̄_j = ½(∂/∂x_j + i ∂/∂y_j)`. -/
noncomputable def partialZbar (j : Fin d) (f : ℂᵈ → ℂ) (z : ℂᵈ) : ℂ :=
  (fderiv ℝ f z (Pi.single j 1) + Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2

@[simp] lemma partialZ_zero (j : Fin d) :
    partialZ j (fun _ : ℂᵈ => (0 : ℂ)) = 0 := by
  funext z; simp [partialZ]

@[simp] lemma partialZbar_zero (j : Fin d) :
    partialZbar j (fun _ : ℂᵈ => (0 : ℂ)) = 0 := by
  funext z; simp [partialZbar]

@[simp] lemma partialZ_const (j : Fin d) (c : ℂ) :
    partialZ j (fun _ : ℂᵈ => c) = 0 := by
  funext z; simp [partialZ]

@[simp] lemma partialZbar_const (j : Fin d) (c : ℂ) :
    partialZbar j (fun _ : ℂᵈ => c) = 0 := by
  funext z; simp [partialZbar]

lemma partialZ_add (j : Fin d) {f g : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    partialZ j (fun z => f z + g z) z = partialZ j f z + partialZ j g z := by
  have h : fderiv ℝ (fun z => f z + g z) z = fderiv ℝ f z + fderiv ℝ g z := fderiv_add hf hg
  simp only [partialZ, h, ContinuousLinearMap.add_apply]
  ring

lemma partialZbar_add (j : Fin d) {f g : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    partialZbar j (fun z => f z + g z) z = partialZbar j f z + partialZbar j g z := by
  have h : fderiv ℝ (fun z => f z + g z) z = fderiv ℝ f z + fderiv ℝ g z := fderiv_add hf hg
  simp only [partialZbar, h, ContinuousLinearMap.add_apply]
  ring

lemma partialZ_const_mul (j : Fin d) (c : ℂ) {f : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z) :
    partialZ j (fun z => c * f z) z = c * partialZ j f z := by
  have h : fderiv ℝ (fun z => c * f z) z = c • fderiv ℝ f z := fderiv_const_mul hf c
  simp only [partialZ, h, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma partialZbar_const_mul (j : Fin d) (c : ℂ) {f : ℂᵈ → ℂ} {z : ℂᵈ} (hf : DifferentiableAt ℝ f z) :
    partialZbar j (fun z => c * f z) z = c * partialZbar j f z := by
  have h : fderiv ℝ (fun z => c * f z) z = c • fderiv ℝ f z := fderiv_const_mul hf c
  simp only [partialZbar, h, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end Wirtinger

section Dbar

/-- The `∂̄` of a smooth function, as a `(0,1)`-form `ℂᵈ → (Fin d → ℂ)`. -/
noncomputable def dbarFun (f : ℂᵈ → ℂ) : ℂᵈ → (Fin d → ℂ) := fun z j => partialZbar j f z

/-- The `∂̄` of a `(0,1)`-form.  Normalisation is irrelevant for us; what matters is that
`dbarForm η = 0` is the closedness condition in the `∂̄`-Poincaré lemma. -/
noncomputable def dbarForm (η : ℂᵈ → (Fin d → ℂ)) : ℂᵈ → (Fin d → Fin d → ℂ) :=
  fun z j k => partialZbar k (fun w => η w j) z - partialZbar j (fun w => η w k) z

/-- `∂̄η = 0`. -/
def DbarClosed (η : ℂᵈ → (Fin d → ℂ)) : Prop := dbarForm η = 0

/-- Pointwise Hermitian norm of a `(0,1)`-form (with respect to the flat metric). -/
noncomputable def formNormSq (η : ℂᵈ → (Fin d → ℂ)) : ℂᵈ → ℝ := fun z => ∑ j, ‖η z j‖ ^ 2

/-- `∂̄` preserves `C^∞`-smoothness. -/
lemma contDiff_dbarFun {f : ℂᵈ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dbarFun f) := by
  change ContDiff ℝ ∞ (fun z j => partialZbar j f z)
  refine contDiff_pi.mpr fun j => ?_
  have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) le_rfl
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (Pi.single j (1 : ℂ))) :=
    hf'.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (Pi.single j Complex.I)) :=
    hf'.clm_apply contDiff_const
  have h3 : ContDiff ℝ ∞ (fun z => (fderiv ℝ f z (Pi.single j (1 : ℂ))
      + Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2) :=
    (h1.add (contDiff_const.mul h2)).div_const 2
  convert h3 using 1
  funext z
  rw [partialZbar]

/-- The Hermitian Hessian `(∂∂̄φ)_{jk} = ∂_j ∂̄_k φ`. -/
noncomputable def hermHess (j k : Fin d) (φ : ℂᵈ → ℝ) : ℂᵈ → ℂ :=
  fun z => partialZ j (partialZbar k (fun w => (φ w : ℂ))) z

/-- `∂²ψ/∂x_j∂x_k (z) = (D²ψ z)![e_j, e_k]`. -/
noncomputable def dxx (j k : Fin d) (ψ : ℂᵈ → ℝ) : ℂᵈ → ℝ :=
  fun z => (iteratedFDeriv ℝ 2 ψ z) ![Pi.single j 1, Pi.single k 1]

/-- `∂²ψ/∂y_j∂y_k (z) = (D²ψ z)![I•e_j, I•e_k]`. -/
noncomputable def dyy (j k : Fin d) (ψ : ℂᵈ → ℝ) : ℂᵈ → ℝ :=
  fun z => (iteratedFDeriv ℝ 2 ψ z) ![Pi.single j Complex.I, Pi.single k Complex.I]

/-- `∂²ψ/∂x_j∂y_k (z) = (D²ψ z)![e_j, I•e_k]`. -/
noncomputable def dxy (j k : Fin d) (ψ : ℂᵈ → ℝ) : ℂᵈ → ℝ :=
  fun z => (iteratedFDeriv ℝ 2 ψ z) ![Pi.single j 1, Pi.single k Complex.I]

/-- `∂²ψ/∂y_j∂x_k (z) = (D²ψ z)![I•e_j, e_k]`. -/
noncomputable def dyx (j k : Fin d) (ψ : ℂᵈ → ℝ) : ℂᵈ → ℝ :=
  fun z => (iteratedFDeriv ℝ 2 ψ z) ![Pi.single j Complex.I, Pi.single k 1]

/-- The real quadratic function `Re(α_j ᾱ_k)` attached to a test `(1,0)`-form `α`. -/
noncomputable def formTest (α : ℂᵈ → (Fin d → ℂ)) (j k : Fin d) : ℂᵈ → ℝ :=
  fun z => Complex.re (α z j * star (α z k))

/-- The imaginary quadratic function `Im(α_j ᾱ_k)`. -/
noncomputable def formImag (α : ℂᵈ → (Fin d → ℂ)) (j k : Fin d) : ℂᵈ → ℝ :=
  fun z => Complex.im (α z j * star (α z k))

/-- **The quadratic form of `∂∂̄φ` applied to a test `(1,0)`-form.**
This is `∑_{j,k} Re ∂_j∂̄_k(α_j ᾱ_k)(z)` written with real second derivatives.  Indeed
`4 ∂_j∂̄_kψ = (∂²_{x_jx_k} + ∂²_{y_jy_k})ψ + i(∂²_{x_jy_k} - ∂²_{y_jx_k})ψ` (mixed partials commute;
the two mixed terms are *different* unless `j = k`), so taking real parts gives
`4 Re ∂_j∂̄_kψ = (∂²_{x_jx_k} + ∂²_{y_jy_k})(Re ψ) - (∂²_{x_jy_k} - ∂²_{y_jx_k})(Im ψ)`,
which is the expression below.  *The mixed terms cannot be dropped*: the real Hessian of `φ`
restricted to a complex line is `4 Re ∑_{j,k} w_j \bar w_k ∂_j∂̄_kφ(z)` only with them present
(see `Commons.Analysis.Calculus.realHessian_expansion_corrected`). -/
noncomputable def dbarDbarTest (α : ℂᵈ → (Fin d → ℂ)) : ℂᵈ → ℝ :=
  fun z => (1 / 4) * ∑ j, ∑ k,
    ((dxx j k (formTest α j k) z + dyy j k (formTest α j k) z)
      - dxy j k (formImag α j k) z + dyx j k (formImag α j k) z)

/-- **Hörmander's positivity condition `∂∂̄φ ≥ κ`** in distributional form:
`∫ κ‖α‖² ≤ ∫ φ · dbarDbarTest α`
for every compactly supported smooth `(1,0)`-form `α`.  The integrand on the right is
`Re ∑_{j,k} ∂_j∂̄_k(α_j ᾱ_k)`, i.e. `∂∂̄φ` paired with the rank-one positive test tensor
`α ⊗ ᾱ`; it is written in `dbarDbarTest` with real second derivatives of the test function, which
is the form in which the integration by parts and the pointwise positivity are verified. -/
def DbarDbarPos (φ : ℂᵈ → ℝ) (κ : ℂᵈ → ℝ) : Prop :=
  ∀ α : ℂᵈ → (Fin d → ℂ), ContDiff ℝ ∞ α → HasCompactSupport α →
    Integrable (fun z => κ z * formNormSq α z) ∧
    Integrable (fun z => φ z * dbarDbarTest α z) ∧
    ∫ z, κ z * formNormSq α z ≤ ∫ z, φ z * dbarDbarTest α z

end Dbar

end Submission.FUP
