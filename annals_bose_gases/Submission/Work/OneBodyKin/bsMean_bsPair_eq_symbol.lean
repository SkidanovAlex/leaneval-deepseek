import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.bsMean_bsPair_eq_kernelForm
import Submission.Work.OneBodyKin.kinFT_bsKern
import Submission.Work.OneBodyKin.quadForm_conv_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The convolution-kernel double integral of `bsKern` in the `kinFT` normalisation: the inner
`z`-integral of `quadForm_conv_eq_fourier` is `kinFT (bsKern ℓ F)`. -/
private lemma bskern_inner_eq (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) :
    (∫ z : ℝ³, (Work.OneBodyKin.bsKern ℓ F z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = Submission.BoseGases.kinFT (fun d : ℝ³ => (Work.OneBodyKin.bsKern ℓ F d : ℂ)) q := by
  rw [Submission.BoseGases.kinFT]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  exact mul_comm _ _

/-- The real part of the pointwise symbol: `(boxHat · symD).re = boxHat · symD`. -/
private lemma bskern_re (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) :
    ((Work.OneBodyKin.boxHat ℓ q : ℂ) * (Work.OneBodyKin.symD ℓ F q : ℂ)).re
      = Work.OneBodyKin.boxHat ℓ q * Work.OneBodyKin.symD ℓ F q := by
  simp

theorem bsMean_bsPair_eq_symbol {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsMean ℓ u ψ * Work.OneBodyKin.bsPair ℓ F u ψ)
      = ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.boxHat ℓ q * Work.OneBodyKin.symD ℓ F q *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  -- the kernel form of the cross term
  have hKern := Work.OneBodyKin.bsMean_bsPair_eq_kernelForm hℓ hFi ψ hψ hcs
  -- the quadratic form of the convolution kernel `bsKern`, in Fourier space
  have hquad := Work.OneBodyKin.quadForm_conv_eq_fourier (Work.OneBodyKin.integrable_bsKern hℓ hFi)
    hψ hcs
  -- the pointwise identification of the Fourier integrand
  have hpt : ∀ q : ℝ³,
      (∫ z : ℝ³, (Work.OneBodyKin.bsKern ℓ F z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))).re *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
      = (Work.OneBodyKin.boxHat ℓ q * Work.OneBodyKin.symD ℓ F q) *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2 := by
    intro q
    rw [bskern_inner_eq ℓ F q, Work.OneBodyKin.kinFT_bsKern hℓ hFi q, bskern_re ℓ F q]
  calc (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.BSKinetic.bsMean ℓ u ψ * Work.OneBodyKin.bsPair ℓ F u ψ)
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
            Work.OneBodyKin.bsKern ℓ F (x - y) * ψ x * ψ y := hKern
    _ = ((2 * Real.pi) ^ 3)⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            (∫ z : EuclideanSpace ℝ (Fin 3), (Work.OneBodyKin.bsKern ℓ F z : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))).re *
              ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2) := by
        rw [hquad]
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            Work.OneBodyKin.boxHat ℓ q * Work.OneBodyKin.symD ℓ F q *
              ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
        rw [← mul_assoc]
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end Work.OneBodyKin
