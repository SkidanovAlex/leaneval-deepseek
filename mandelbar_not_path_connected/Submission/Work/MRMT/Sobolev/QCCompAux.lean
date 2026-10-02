/-
Copyright: Work.MRMT (mandelbar) subproject.

# Auxiliary lemmas for the composition rule for quasiconformal maps

The determinant of the real Fréchet derivative of a map `f : ℂ → ℂ` is expressed through the
Wirtinger derivatives, and the `IsQCOn` hypothesis (a.e. relation `∂̄f = μ ∂f` with `‖μ‖ ≤ k < 1`)
is converted into the pointwise a.e. distortion bounds
`‖∂f‖ ≤ C √(det Df)`, `‖∂̄f‖ ≤ C √(det Df)`, used to control the composite in the proof of
`Work.MRMT.Sobolev.isDbarDerivOn_comp_qc`.
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

namespace Work.MRMT.Sobolev

/-- Determinant of a real-linear endomorphism of `ℂ` in terms of its Wirtinger derivatives. -/
theorem det_lin (L : ℂ →L[ℝ] ℂ) :
    L.det = Complex.normSq ((L 1 - I * L I) / 2) - Complex.normSq ((L 1 + I * L I) / 2) := by
  change LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  have hm : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (L : ℂ →ₗ[ℝ] ℂ)
      = !![(L 1).re, (L I).re; (L 1).im, (L I).im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI]
  rw [hm]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.div_re, Complex.div_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  norm_num
  ring

/-- `det (D f z) = ‖∂f z‖² - ‖∂̄f z‖²`. -/
theorem det_fderiv_eq (f : ℂ → ℂ) (z : ℂ) :
    (fderiv ℝ f z).det = ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2 := by
  have h := det_lin (fderiv ℝ f z)
  rw [dz, dzbar, h]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]

/-- The `IsQCOn` condition gives, a.e., the determinant identity and the distortion bounds
`‖∂f‖ ≤ (√(1-k²))⁻¹ √(det Df)`, `‖∂̄f‖ ≤ k (√(1-k²))⁻¹ √(det Df)`, together with `0 ≤ det Df`. -/
theorem distortion {φ μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hrel : ∀ᵐ z ∂(volume : Measure ℂ), dzbar φ z = μ z * dz φ z)
    (hμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (fderiv ℝ φ z).det = ‖dz φ z‖ ^ 2 - ‖dzbar φ z‖ ^ 2 ∧
      0 ≤ (fderiv ℝ φ z).det ∧
      ‖dz φ z‖ ≤ (Real.sqrt (1 - k ^ 2))⁻¹ * Real.sqrt ((fderiv ℝ φ z).det) ∧
      ‖dzbar φ z‖ ≤ k * (Real.sqrt (1 - k ^ 2))⁻¹ * Real.sqrt ((fderiv ℝ φ z).det) := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.mpr hk2
  have hsinv : 0 ≤ (Real.sqrt (1 - k ^ 2))⁻¹ := le_of_lt (inv_pos.mpr hs)
  filter_upwards [hrel, hμ] with z hr hz
  have hdet := det_fderiv_eq φ z
  have hb : ‖dzbar φ z‖ ≤ k * ‖dz φ z‖ := by
    rw [hr, norm_mul]; exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hsq : ‖dzbar φ z‖ ^ 2 ≤ k ^ 2 * ‖dz φ z‖ ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg (dzbar φ z)) hb
    rw [← sq, ← sq] at h
    convert h using 1
    ring
  have hdetge : (1 - k ^ 2) * ‖dz φ z‖ ^ 2 ≤ (fderiv ℝ φ z).det := by
    rw [hdet]; nlinarith
  have hdetnn : 0 ≤ (fderiv ℝ φ z).det := by
    rw [hdet]; nlinarith [hsq, sq_nonneg k, norm_nonneg (dz φ z)]
  have hsqrt : Real.sqrt (1 - k ^ 2) * ‖dz φ z‖ ≤ Real.sqrt ((fderiv ℝ φ z).det) := by
    rw [← Real.sqrt_sq (norm_nonneg (dz φ z)), ← Real.sqrt_mul hk2.le]
    exact Real.sqrt_le_sqrt hdetge
  have hfirst : ‖dz φ z‖ ≤
      (Real.sqrt (1 - k ^ 2))⁻¹ * Real.sqrt ((fderiv ℝ φ z).det) := by
    have := mul_le_mul_of_nonneg_left hsqrt hsinv
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), one_mul] at this
  refine ⟨hdet, hdetnn, hfirst, ?_⟩
  calc ‖dzbar φ z‖ ≤ k * ‖dz φ z‖ := hb
    _ ≤ k * ((Real.sqrt (1 - k ^ 2))⁻¹ * Real.sqrt ((fderiv ℝ φ z).det)) :=
        mul_le_mul_of_nonneg_left hfirst hk
    _ = k * (Real.sqrt (1 - k ^ 2))⁻¹ * Real.sqrt ((fderiv ℝ φ z).det) := by ring


/-- The `∂̄`-chain-rule expression for the composite `v ∘ φ`:
`∂v(φ z) · ∂̄φ(z) + ∂̄v(φ z) · conj(∂φ(z))`. -/
def compDbar (v φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  dz v (φ z) * dzbar φ z + dzbar v (φ z) * star (dz φ z)

end Work.MRMT.Sobolev
