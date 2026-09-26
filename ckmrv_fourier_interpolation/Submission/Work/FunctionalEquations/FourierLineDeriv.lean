import Mathlib
import Submission.Work.FunctionalEquations.Basic

/-!
# The Fourier transform of an iterated directional derivative

For the unit coordinate vector `m = realIncl 1` of `R^n`, the Fourier transform of the
`P`-fold iterated directional derivative `∂_m^P f` is multiplication of the Fourier
transform by `(2 π i ⟪ξ, m⟫)^P`.  Evaluating the inner product at the coordinate vector
turns this into the factor `(2 π i ξ₀)^P` appearing in the paper.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap
open LineDeriv

/-- **Iterated directional derivative and Fourier transform.**  For every `P`, evaluating
the Fourier transform of `∂_m^P f` at `ξ` multiplies the Fourier transform of `f` by the
`P`-th power of `2 π i ⟪ξ, m⟫`, where `m = realIncl 1`. -/
private lemma fourier_lineDeriv_iterate {n : ℕ} [NeZero n] (P : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (ξ : EuclideanSpace ℝ (Fin n)) :
    (𝓕 ((LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ)
        (realIncl (n := n) 1))^[P] f)) ξ
      = (2 * ↑Real.pi * Complex.I * ((inner ℝ ξ (realIncl (n := n) 1) : ℝ) : ℂ)) ^ P *
          (𝓕 f) ξ := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Function.iterate_succ_apply']
    rw [LineDeriv.lineDerivOpCLM_apply]
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    rw [smul_apply]
    rw [SchwartzMap.smulLeftCLM_apply_apply (by
      exact ((innerSL ℝ).flip (realIncl (n := n) 1)).hasTemperateGrowth)]
    rw [ih, Complex.real_smul]
    ring

/-- The inner product with the unit coordinate vector `realIncl 1` is the zeroth
coordinate. -/
private lemma inner_realIncl_one {n : ℕ} [NeZero n] (ξ : EuclideanSpace ℝ (Fin n)) :
    (inner ℝ ξ (realIncl (n := n) 1) : ℝ) = ξ 0 := by
  simp [realIncl, PiLp.inner_apply]

theorem FourierLineDeriv {n : ℕ} [NeZero n] (P : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (ξ : EuclideanSpace ℝ (Fin n)) :
    FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ))
        ((LineDeriv.lineDerivOpCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (realIncl (n := n) 1))^[P] f) ξ
      = (2 * ↑Real.pi * Complex.I * ((ξ 0 : ℝ) : ℂ)) ^ P *
          (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f) ξ := by
  simp only [FourierTransform.fourierCLM_apply]
  rw [fourier_lineDeriv_iterate P f ξ, inner_realIncl_one]

end Work.FunctionalEquations
