import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
# `Work.BoseFixB2.DvApriori.bsOneBody_polar`

The one-body big-box spectral word `Work.BSKinetic.bsOneBody ℓ F u ψ` is
`(2π)⁻³ ∫_p F(‖p‖)·‖kinFT (χ_u·Q_uψ)(p)‖²`; it is the *diagonal of a complex bilinear form* in the
windowed state, so the difference at `f+g` and `f−g` polarises it.

The proof is the pointwise identity in `ℂ`

  `‖z+w‖² − ‖z−w‖² = 4·Re(star z · w)`

transported through the `p`-integral:

* `bsQ` (= `Qfree`) is additive/subtractive in the state (`FsTAux.bsQ_{add,sub}`),
* `kinFT` is additive/subtractive on integrable states (`FsTAux.kinFT_{add,sub}`),
* both `p`-integrands are integrable, being a smooth compactly supported (windowed, hence
  compactly supported) state times the symbol `[‖·‖−c]₊²`
  (`FsTAux.integrable_fsKinCoeff_kinFT_sq`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB2.DvApriori

open Work.BoseKinLoc Work.BSKinetic

set_option maxHeartbeats 2000000

/-- **Polarisation of the squared norm in `ℂ`**: for `z w : ℂ`,
`‖z + w‖² − ‖z − w‖² = 4·Re(star z · w)`.  This is the pointwise content of the polarisation
identity: the two cross terms `±2 Re(inner ℝ z w)` of `norm_add_sq_real`/`norm_sub_sq_real`
add up, and `Complex.inner` identifies `inner ℝ z w` with `Re(star z · w)`. -/
lemma norm_sq_sub_norm_sq (z w : ℂ) :
    ‖z + w‖ ^ 2 - ‖z - w‖ ^ 2 = 4 * (star z * w).re := by
  rw [norm_add_sq_real, norm_sub_sq_real, Complex.inner]
  simp only [Complex.star_def]
  rw [mul_comm w (starRingEnd ℂ z)]
  ring

/-- The polarisation identity for the one-body spectral word `bsOneBody`:
`bsOneBody ℓ [‖·‖−c]₊² 0` is a quadratic form, so its difference at `f+g` and `f−g` is
`4·(2π)⁻³∫_p [‖p‖−c]₊²·Re(star(kinFT(χ₀Q₀f)(p))·kinFT(χ₀Q₀g)(p)) dp`, where `χ₀ = bsWin ℓ 0`
is the box window and `Q₀ = Qfree ℓ 0` the box mean-free projection. -/
theorem bsOneBody_polar {ℓ : ℝ} (hℓ : 0 < ℓ) {c : ℝ}
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0 (fun z => f z + g z)
      - Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0 (fun z => f z - g z)
    = 4 * ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          (star (Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 f z : ℂ)) p)
            * Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
              (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BoseKinLoc.Qfree ℓ 0 g z : ℂ)) p).re := by
  -- `Qfree` is the chapter's name for `bsQ`, which is what `bsOneBody` unfolds to
  simp only [Qfree]
  -- the window and the windowed states are smooth with compact support
  have hWin : ContDiff ℝ (⊤ : ℕ∞) (bsWin ℓ 0) := by
    have h' : bsWin ℓ 0 = fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ (z - ℓ • 0) := rfl
    rw [h']
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).comp
      (contDiff_id.sub contDiff_const)
  have hWcs : HasCompactSupport (bsWin ℓ 0) := bsWin_hasCompactSupport hℓ 0
  have hcd : ∀ {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      ContDiff ℝ (⊤ : ℕ∞) (fun z => bsWin ℓ 0 z * bsQ ℓ 0 ψ z) := by
    intro ψ hψ
    have hQ : ContDiff ℝ (⊤ : ℕ∞) (bsQ ℓ 0 ψ) := by
      have h' : bsQ ℓ 0 ψ = fun z => ψ z - bsMean ℓ 0 ψ := rfl
      rw [h']; exact hψ.sub contDiff_const
    exact hWin.mul hQ
  have hcs : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ,
      HasCompactSupport (fun z => bsWin ℓ 0 z * bsQ ℓ 0 ψ z) :=
    fun _ => HasCompactSupport.mul_right hWcs
  have hint : ∀ {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((bsWin ℓ 0 z * bsQ ℓ 0 ψ z : ℝ) : ℂ)) := by
    intro ψ hψ
    exact (Complex.continuous_ofReal.comp (hcd hψ).continuous).integrable_of_hasCompactSupport
      ((hcs ψ).comp_left (by simp))
  have hcast : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ,
      (fun z : EuclideanSpace ℝ (Fin 3) => (bsWin ℓ 0 z : ℂ) * (bsQ ℓ 0 ψ z : ℂ))
        = fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 ψ z : ℝ) : ℂ) := by
    intro ψ
    funext z
    rw [Complex.ofReal_mul]
  -- the pointwise splitting of the windowed states
  have hsplit_add : (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((bsWin ℓ 0 z * bsQ ℓ 0 (fun z => f z + g z) z : ℝ) : ℂ))
      = fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 f z : ℝ) : ℂ)
          + ((bsWin ℓ 0 z * bsQ ℓ 0 g z : ℝ) : ℂ) := by
    funext z
    rw [congrFun (Work.BoseFixB2.Polar.FsTAux.bsQ_add hℓ 0 hf.continuous hg.continuous) z]
    push_cast
    ring
  have hsplit_sub : (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((bsWin ℓ 0 z * bsQ ℓ 0 (fun z => f z - g z) z : ℝ) : ℂ))
      = fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 f z : ℝ) : ℂ)
          - ((bsWin ℓ 0 z * bsQ ℓ 0 g z : ℝ) : ℂ) := by
    funext z
    rw [congrFun (Work.BoseFixB2.Polar.FsTAux.bsQ_sub hℓ 0 hf.continuous hg.continuous) z]
    push_cast
    ring
  -- the Fourier transforms split
  have hKadd : ∀ p, Submission.BoseGases.kinFT (fun z =>
        ((bsWin ℓ 0 z * bsQ ℓ 0 (fun z => f z + g z) z : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT
          (fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 f z : ℝ) : ℂ)) p
        + Submission.BoseGases.kinFT
          (fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 g z : ℝ) : ℂ)) p := by
    intro p
    rw [hsplit_add]
    exact Work.BoseFixB2.Polar.FsTAux.kinFT_add (hint hf) (hint hg) p
  have hKsub : ∀ p, Submission.BoseGases.kinFT (fun z =>
        ((bsWin ℓ 0 z * bsQ ℓ 0 (fun z => f z - g z) z : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT
          (fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 f z : ℝ) : ℂ)) p
        - Submission.BoseGases.kinFT
          (fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 g z : ℝ) : ℂ)) p := by
    intro p
    rw [hsplit_sub]
    exact Work.BoseFixB2.Polar.FsTAux.kinFT_sub (hint hf) (hint hg) p
  -- integrability of the four `p`-integrands
  have hintp := Work.BoseFixB2.Polar.FsTAux.integrable_fsKinCoeff_kinFT_sq (c := c)
    (hcd (hf.add hg)) (hcs (fun z => f z + g z))
  have hintm := Work.BoseFixB2.Polar.FsTAux.integrable_fsKinCoeff_kinFT_sq (c := c)
    (hcd (hf.sub hg)) (hcs (fun z => f z - g z))
  have hintf := Work.BoseFixB2.Polar.FsTAux.integrable_fsKinCoeff_kinFT_sq (c := c)
    (hcd hf) (hcs f)
  have hintg := Work.BoseFixB2.Polar.FsTAux.integrable_fsKinCoeff_kinFT_sq (c := c)
    (hcd hg) (hcs g)
  -- the `p`-integral identity
  have key : (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z =>
          ((bsWin ℓ 0 z * bsQ ℓ 0 (fun z => f z + g z) z : ℝ) : ℂ)) p‖ ^ 2)
      - (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z =>
          ((bsWin ℓ 0 z * bsQ ℓ 0 (fun z => f z - g z) z : ℝ) : ℂ)) p‖ ^ 2)
      = 4 * (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
          (star (Submission.BoseGases.kinFT (fun z =>
              ((bsWin ℓ 0 z * bsQ ℓ 0 f z : ℝ) : ℂ)) p)
            * Submission.BoseGases.kinFT (fun z =>
              ((bsWin ℓ 0 z * bsQ ℓ 0 g z : ℝ) : ℂ)) p).re) := by
    rw [← MeasureTheory.integral_sub hintp hintm, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hKadd p, hKsub p]
    have hpolar := norm_sq_sub_norm_sq
      (Submission.BoseGases.kinFT (fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 f z : ℝ) : ℂ)) p)
      (Submission.BoseGases.kinFT (fun z => ((bsWin ℓ 0 z * bsQ ℓ 0 g z : ℝ) : ℂ)) p)
    linear_combination (norm := ring) (Submission.BoseGases.fsKinCoeff c ‖p‖) * hpolar
  unfold bsOneBody
  rw [hcast (fun z => f z + g z), hcast (fun z => f z - g z), hcast f, hcast g]
  linear_combination ((2 * Real.pi) ^ 3)⁻¹ * key

end Work.BoseFixB2.DvApriori
