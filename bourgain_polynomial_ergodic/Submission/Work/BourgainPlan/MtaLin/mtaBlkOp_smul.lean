import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs

/-!
# `ℂ`-homogeneity of the block operators `mtaBlkOp`

The block operator `mtaBlkOp P K ε s` of `Maximal/MtaDefs.lean` is built from the curve averages
`curveSigma`, the dyadic differences `dyadD` and the Littlewood–Paley projections `dyadicProj`:

`mtaBlkOp P K ε s h = ∑_{k<K} S̃_{dk+s}(ε_k · S_{dk+s}(D_k h))`.

Each ingredient is `ℂ`-homogeneous, so the same is true of the operator.  The proof is pointwise:
`curveSigma` is an interval integral (`intervalIntegral.integral_smul`), `dyadD` is a difference of
two of them, and `dyadicProj ψ l g = 𝓕⁻(ξ ↦ ψ (2^l ξ) · 𝓕 g ξ)` is a composition of the Fourier
transform and its inverse, both of which are integrals (`Real.fourier_real_eq`, `Real.fourierInv_eq`)
and hence homogeneous (`MeasureTheory.integral_smul`).
-/

open MeasureTheory
open Work.BourgainPlan.Maximal

namespace Work.BourgainPlan.MtaLin

noncomputable section

/-- Homogeneity of the curve average `σ_n h(x) = ∫₀¹ h(x - P(n t)) dt`. -/
lemma mtaCurveSigma_smul (P : Polynomial ℤ) (n : ℕ) (c : ℂ) (h : ℝ → ℂ) :
    curveSigma P n (c • h) = fun x => c * curveSigma P n h x := by
  funext x
  simp only [curveSigma_apply, Pi.smul_apply]
  rw [intervalIntegral.integral_smul, smul_eq_mul]

/-- Homogeneity of the dyadic difference `D_k = σ_{2^k} - σ_{2^{k+1}}`. -/
lemma mtaDyadD_smul (P : Polynomial ℤ) (k : ℕ) (c : ℂ) (h : ℝ → ℂ) :
    dyadD P k (c • h) = c • dyadD P k h := by
  have h' : dyadD P k (c • h) = fun x => c * dyadD P k h x := by
    funext x
    simp only [dyadD]
    rw [mtaCurveSigma_smul, mtaCurveSigma_smul]
    ring
  rw [h']
  rfl

/-- Homogeneity of the Fourier transform on `ℝ → ℂ`. -/
lemma mtaFourier_smul (c : ℂ) (g : ℝ → ℂ) :
    FourierTransform.fourier (c • g) = c • FourierTransform.fourier g := by
  funext ξ
  rw [Real.fourier_real_eq (c • g) ξ]
  simp only [Pi.smul_apply]
  rw [Real.fourier_real_eq g ξ, ← MeasureTheory.integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- Homogeneity of the inverse Fourier transform on `ℝ → ℂ`. -/
lemma mtaFourierInv_smul (c : ℂ) (g : ℝ → ℂ) :
    FourierTransform.fourierInv (c • g) = c • FourierTransform.fourierInv g := by
  funext ξ
  rw [Real.fourierInv_eq (c • g) ξ]
  simp only [Pi.smul_apply]
  rw [Real.fourierInv_eq g ξ, ← MeasureTheory.integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- Homogeneity of the Littlewood–Paley projection `dyadicProj ψ l`. -/
lemma mtaDyadicProj_smul (ψ : ℝ → ℝ) (l : ℤ) (c : ℂ) (g : ℝ → ℂ) :
    dyadicProj ψ l (c • g) = c • dyadicProj ψ l g := by
  funext x
  unfold dyadicProj
  rw [mtaFourier_smul]
  rw [show (fun ξ : ℝ => (ψ ((2:ℝ)^l * ξ) : ℂ) * (c • FourierTransform.fourier g) ξ)
      = c • (fun ξ : ℝ => (ψ ((2:ℝ)^l * ξ) : ℂ) * FourierTransform.fourier g ξ) from by
        funext ξ; simp only [Pi.smul_apply, smul_eq_mul]; ring]
  rw [mtaFourierInv_smul]

/-- **The block operators `mtaBlkOp` are `ℂ`-homogeneous in their input.** -/
theorem mtaBlkOp_smul (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) (c : ℂ) (u : ℝ → ℂ) (x : ℝ) :
    Work.BourgainPlan.Maximal.mtaBlkOp P K ε s (c • u) x = c * Work.BourgainPlan.Maximal.mtaBlkOp P K ε s u x := by
  simp only [mtaBlkOp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hinner :
      (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k (c • u)) y)
        = c • (fun y : ℝ =>
            ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k u) y) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mtaDyadD_smul, mtaDyadicProj_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hinner, mtaDyadicProj_smul]
  simp only [Pi.smul_apply, smul_eq_mul]

end

end Work.BourgainPlan.MtaLin
