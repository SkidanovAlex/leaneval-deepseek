import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.E2_T_smul

/-!
# The `q`-expansion of the weight-two Eisenstein series `E₂`

We compute the coefficients of the `q`-expansion of the normalized weight-two
Eisenstein series
`E₂(τ) = 1 - 24 ∑_{n ≥ 1} σ₁(n) qⁿ`,  `q = exp (2 π i τ)`:

`(qExpansion 1 E₂).coeff n = 1` for `n = 0` and `-24 σ₁(n)` for `n ≥ 1`.

The proof is an application of the uniqueness of `q`-expansion coefficients
(`qExpansion_coeff_unique_plain`, a reformulation of Mathlib's
`UpperHalfPlane.qExpansion_coeff_unique` for plain functions `ℍ → ℂ`), applied to
Mathlib's `EisensteinSeries.hasSum_qExpansion_E2`.  The required inputs are
periodicity of `E₂` with period `1` (`E2_periodic_one`, deduced from the `T`-invariance
of the slash action `E2_T_smul`), holomorphy (`E2_mdifferentiable`) and boundedness at
the cusp (`EisensteinSeries.isBoundedAtImInfty_E2`).
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- `E₂` is periodic of period `1` on `ℍ`: it is invariant under `z ↦ z + 1`.
This is the input needed to speak about the `q`-expansion of `E₂` (i.e. to define its
`cuspFunction`). -/
theorem E2_periodic_one : Function.Periodic (E2 ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    have h1 : UpperHalfPlane.ofComplex (w + 1) = ModularGroup.T • UpperHalfPlane.ofComplex w := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw, modular_T_smul,
        UpperHalfPlane.ofComplex_apply_of_im_pos hw']
      ext
      simp [UpperHalfPlane.coe_vadd, add_comm]
    simp only [Function.comp_apply]
    rw [h1, E2_T_smul]
  · have hw0 : w.im ≤ 0 := le_of_not_gt hw
    have hw' : (w + 1).im ≤ 0 := by simpa using hw0
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0]

/-- Uniqueness of `q`-expansion coefficients, stated for a plain function `f : ℍ → ℂ`
rather than in the `FunLike` generality of `UpperHalfPlane.qExpansion_coeff_unique`:
if `cuspFunction h f` is analytic at `0` and `f τ = ∑' m, c m * q^m` for all `τ`, then
`c m` is the `m`-th coefficient of the `q`-expansion of `f`. -/
lemma qExpansion_coeff_unique_plain {c : ℕ → ℂ} {f : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam h ↑τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m := by
  have h1 : HasFPowerSeriesAt (cuspFunction h f) (FormalMultilinearSeries.ofScalars ℂ c) 0 :=
    (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f)
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (qExpansion h f).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hfanalytic.hasFPowerSeriesAt
  have h3 := h1.eq_formalMultilinearSeries h2
  have h4 := congr_arg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff m) h3
  simpa using h4

theorem E2_qExpansion_coeff (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 E2).coeff n =
      if n = 0 then 1 else -24 * ((ArithmeticFunction.sigma 1 n : ℕ) : ℂ) := by
  have hanalytic : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos E2_periodic_one E2_mdifferentiable
      EisensteinSeries.isBoundedAtImInfty_E2
  have hhas : ∀ τ : ℍ,
      HasSum (fun m ↦ (if m = 0 then 1 else -24 * ((ArithmeticFunction.sigma 1 m : ℕ) : ℂ)) •
        Function.Periodic.qParam 1 ↑τ ^ m) (E2 τ) := by
    intro τ
    simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
      using EisensteinSeries.hasSum_qExpansion_E2 τ
  exact (qExpansion_coeff_unique_plain one_pos hanalytic hhas n).symm

end Work.Modular
