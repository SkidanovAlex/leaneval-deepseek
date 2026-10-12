import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.kinFT_conv_pair
import Submission.Work.BoseBoxFock.latticePoisson_kernel
import Submission.Work.BoseK15.ChiReg_corpus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.convWindow_kinFT`

The Fourier transform of the windowed convolution `W ⋆ χ_ℓ` is the product of the Fourier
transforms, `Ŵ(p)·χ̂(ℓ p)`, up to the dilation factor `ℓ³`:

    `ℓ³ · (kinFT W p · hatChi (ℓ • p)) = kinFT (W ⋆ chiScale ℓ) p`.

Here `kinFT u p = ∫_y e^{−i⟪p,y⟫}u y` is the corpus's `p`-convention Fourier transform
(`Submission.BoseGases.kinFT`), `chiScale ℓ = χ(·/ℓ)` is the bump dilated to the box of side `ℓ`
and `hatChi q = ∫_x χ x · cos⟪q,x⟫` is FS's cosine transform (`Work.BoseB4.BoxData.hatChi`).

## Proof

Three inputs, all already in the corpus:

* **the convolution theorem in the `p`-convention** `kinFT_conv_pair`: for `W`, `h` integrable,
  the product of the two transforms is the transform of the position-space convolution
  `u ↦ ∫_x W x · h(u−x)`, which is exactly Mathlib's `MeasureTheory.convolution` at the
  bilinear map `ContinuousLinearMap.lsmul ℝ ℝ` (`convolution_def`);
* **the transform of the dilated bump** `Work.OneBodyKin.kinFT_chiScale`:
  `kinFT (chiScale ℓ) p = ℓ³ · profHat (ℓ • p)`, a single dilation substitution;
* **the dictionary** `profHat = hatChi`: both are the cosine transform of `χ`, which agrees with
  the complex exponential transform because `χ` is even (the sine part is odd, hence integrates
  to zero).  `Work.OneBodyKin.profHat` and `Work.BoseK15.corpusBox.hatChi` are definitionally
  the same integral, so the identification is `rfl`.

The only non-definitional bookkeeping is the commutativity of the order of the two factors
inside the integrand (`e^{−i⟪p,·⟫}` on the left in `kinFT`, on the right in `kinFT_conv_pair`).
-/

open MeasureTheory

namespace Work.BoseBoxFock

theorem convWindow_kinFT {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWs : HasCompactSupport W)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (ℓ : ℂ) ^ 3 * (Submission.BoseGases.kinFT (fun y : EuclideanSpace ℝ (Fin 3) => (W y : ℂ)) p
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ))
      = Submission.BoseGases.kinFT
          (fun u : EuclideanSpace ℝ (Fin 3) =>
            ((MeasureTheory.convolution W (Submission.BoseGases.chiScale ℓ)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume u : ℝ) : ℂ)) p := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- integrability of the two convolution factors
  have hWint : Integrable W := hW.continuous.integrable_of_hasCompactSupport hWs
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_contDiff hℓne
  have hχcs : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_hasCompactSupport hℓne
  have hχint : Integrable (Submission.BoseGases.chiScale ℓ) :=
    hχcd.continuous.integrable_of_hasCompactSupport hχcs
  -- Mathlib's convolution is the position-space convolution appearing in `kinFT_conv_pair`
  have hconv : ∀ u : EuclideanSpace ℝ (Fin 3),
      MeasureTheory.convolution W (Submission.BoseGases.chiScale ℓ)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume u
      = ∫ x, W x * Submission.BoseGases.chiScale ℓ (u - x) := by
    intro u
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- the convolution theorem, in the sign/order convention in which it is proved
  have hprod := kinFT_conv_pair (W := W) (h := Submission.BoseGases.chiScale ℓ) hWint hχint p
  -- the dictionary `profHat = hatChi` (the same cosine integral)
  have hprof : Work.OneBodyKin.profHat (ℓ • p) = Work.BoseK15.corpusBox.hatChi (ℓ • p) := rfl
  -- the transform of the dilated bump, in the multiplicative form used below
  have hχfac : (∫ y : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ y : ℂ)
      * Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))))
      = (ℓ : ℂ) ^ 3 * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) := by
    have h1 := Work.OneBodyKin.kinFT_chiScale hℓ p
    rw [Submission.BoseGases.kinFT] at h1
    rw [hprof] at h1
    rw [← h1]
    apply integral_congr_ae
    filter_upwards with y
    ring
  -- commutation of the two factors of the `W`-integrand
  have hWfac : (∫ x : EuclideanSpace ℝ (Fin 3), (W x : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
      = (∫ y : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (W y : ℂ)) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  -- the target, after unfolding the definition of `kinFT` on both sides
  have hkey : Submission.BoseGases.kinFT
        (fun u : EuclideanSpace ℝ (Fin 3) =>
          ((MeasureTheory.convolution W (Submission.BoseGases.chiScale ℓ)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume u : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT (fun y : EuclideanSpace ℝ (Fin 3) => (W y : ℂ)) p
        * ((ℓ : ℂ) ^ 3 * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)) := by
    show (∫ u : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))
          * ((MeasureTheory.convolution W (Submission.BoseGases.chiScale ℓ)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume u : ℝ) : ℂ))
        = (∫ y : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (W y : ℂ))
          * ((ℓ : ℂ) ^ 3 * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ))
    calc (∫ u : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p u : ℂ)))
          * ((MeasureTheory.convolution W (Submission.BoseGases.chiScale ℓ)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume u : ℝ) : ℂ))
        = ∫ u : EuclideanSpace ℝ (Fin 3),
            ((∫ x, W x * Submission.BoseGases.chiScale ℓ (u - x) : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ))) := by
          apply integral_congr_ae
          filter_upwards with u
          rw [hconv u, mul_comm]
      _ = (∫ x : EuclideanSpace ℝ (Fin 3),
              (W x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
            * (∫ y : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ y : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))) := hprod.symm
      _ = (∫ y : EuclideanSpace ℝ (Fin 3),
              Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (W y : ℂ))
            * ((ℓ : ℂ) ^ 3 * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)) := by
          rw [hWfac, hχfac]
  rw [hkey]
  ring

end Work.BoseBoxFock
