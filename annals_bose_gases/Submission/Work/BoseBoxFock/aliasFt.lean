import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.Convolution
import Submission.Work.BoseBoxFock.AliasDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aliasFt` — the auto-correlation is the modulus-square of `kinFT`

For `g : ℝ³ → ℂ` smooth with compact support, the auto-correlation
`autocorr g u = ∫ x, g x · conj (g (x − u))` has `p`-Fourier transform `‖kinFT g p‖²`:

    ‖kinFT g p‖² = Re ∫_u autocorr g u · exp (−I⟪p,u⟫) .

The proof is the convolution form of Wiener–Khinchin:

* `autocorr g = g ⋆ conj∘g∘(−·)` (`autocorr_eq_convolution`);
* the Fourier transform of the conjugate reflection is the conjugate of the Fourier transform
  (`fourier_conj_neg`);
* hence `𝓕 (autocorr g) ξ = 𝓕 g ξ · conj (𝓕 g ξ) = ‖𝓕 g ξ‖²` (`Real.fourier_mul_convolution_eq`);
* `𝓕 g ((2π)⁻¹ • p) = kinFT g p` (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`) and the
  Fourier integral at `(2π)⁻¹ • p` is the `p`-convention integral (`exp_neg_two_pi_inner`).

Taking real parts at the end gives the statement.
-/

noncomputable section

open MeasureTheory

open scoped Real FourierTransform

namespace Work.BoseBoxFock

set_option maxHeartbeats 1600000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `p`-convention phase `u ↦ exp (−I⟪p,u⟫)`. -/
private noncomputable def aliasPhase (p u : E3) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))

/-- `exp (−2πI⟪u, (2π)⁻¹ • p⟫)` is the `p`-convention phase `exp (−I⟪p,u⟫)`. -/
private lemma exp_neg_two_pi_inner (p u : E3) :
    Complex.exp (↑(-2 * π * inner ℝ u ((2 * π)⁻¹ • p)) * Complex.I) = aliasPhase p u := by
  have h2 : (2 * π : ℝ) ≠ 0 := by positivity
  have harg : -2 * π * inner ℝ u ((2 * π)⁻¹ • p) = -inner ℝ p u := by
    rw [inner_smul_right, real_inner_comm p u]
    field_simp
  rw [harg, aliasPhase]
  congr 1
  push_cast
  ring

/-- **The Fourier transform of the conjugate reflection** `v ↦ conj (f (−v))` is the conjugate of
the Fourier transform. -/
private lemma fourier_conj_neg (f : E3 → ℂ) (ξ : E3) :
    𝓕 (fun v : E3 => (starRingEnd ℂ) (f (-v))) ξ = (starRingEnd ℂ) (𝓕 f ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  have hpt : ∀ v : E3,
      (𝐞 (-(inner ℝ (-v) ξ)) : Circle) • (starRingEnd ℂ) (f (-(-v)))
        = (starRingEnd ℂ) ((𝐞 (-(inner ℝ v ξ)) : Circle) • f v) := by
    intro v
    rw [inner_neg_left, neg_neg, neg_neg]
    rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul]
    congr 1
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]
  rw [← integral_neg_eq_self (fun v : E3 =>
        (𝐞 (-(inner ℝ v ξ)) : Circle) • (starRingEnd ℂ) (f (-v))) volume]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- **The auto-correlation is the convolution with the conjugate reflection.** -/
private lemma autocorr_eq_convolution (g : E3 → ℂ) :
    autocorr g = convolution g (fun v : E3 => (starRingEnd ℂ) (g (-v)))
      (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext u
  rw [MeasureTheory.convolution_def]
  simp only [autocorr, ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [neg_sub]

theorem aliasFt {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖Submission.BoseGases.kinFT g p‖ ^ 2
      = (∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.autocorr g u
            * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))).re := by
  have hg1 : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hG1 : Integrable (fun v : E3 => (starRingEnd ℂ) (g (-v))) := by
    have h := (ContinuousLinearEquiv.integrable_comp_iff (φ := fun v : E3 => g (-v))
      Complex.conjCLE).2 hg1.comp_neg
    simpa [Complex.conjCLE_apply] using h
  have hconv : autocorr g = convolution g (fun v : E3 => (starRingEnd ℂ) (g (-v)))
      (ContinuousLinearMap.mul ℂ ℂ) volume := autocorr_eq_convolution g
  -- the complex form of the identity
  have hmain : ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ)
      = ∫ u : E3, autocorr g u * aliasPhase p u := by
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    have hns : ((‖𝓕 g ((2 * π)⁻¹ • p)‖ ^ 2 : ℝ) : ℂ)
        = 𝓕 g ((2 * π)⁻¹ • p) * (starRingEnd ℂ) (𝓕 g ((2 * π)⁻¹ • p)) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      exact mul_comm _ _
    rw [hns]
    rw [← fourier_conj_neg g ((2 * π)⁻¹ • p)]
    rw [← Real.fourier_mul_convolution_eq hg1 hG1 ((2 * π)⁻¹ • p)]
    rw [Real.fourier_eq']
    simp only [smul_eq_mul]
    simp_rw [hconv, exp_neg_two_pi_inner p]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
  change ‖Submission.BoseGases.kinFT g p‖ ^ 2
      = (∫ u : E3, autocorr g u * aliasPhase p u).re
  rw [← hmain]
  exact (Complex.ofReal_re _).symm

end Work.BoseBoxFock
