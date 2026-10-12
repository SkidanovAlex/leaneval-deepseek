import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.momForm_const_mul` — the large-momentum word is `2`-homogeneous

The bare large-momentum form of FS `eq:DefT`,

    `momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹ < ‖p‖} ‖𝓕(θ_u·Q_uψ)(p)‖²`,

is a **quadratic form** in the one-body state `ψ`: scaling `ψ ↦ c·ψ` scales it by `c²`.  This
is the `momWord` ingredient of the localisation assembly (`Word.fsT_const_mul`), and it needs
no smoothness, support or integrability hypothesis on `ψ`:

* `Q_u` is linear in `ψ` (`bsQ_const_mul`), the indicator `θ_u = indU ℓ u` does not depend on
  `ψ`, so the windowed state of `c·ψ` is the complex multiple by `(c:ℂ)` of the windowed state
  of `ψ`;
* `kinFT` is `ℂ`-linear in the state (`kinFT_const_mul`), an unconditional Bochner-integral
  identity (`MeasureTheory.integral_const_mul`);
* `‖(c:ℂ)·w‖² = c²‖w‖²` for real `c` (`norm_sq_ofReal_mul`);
* the outer `p`-integral is linear (`MeasureTheory.integral_const_mul`), and the junk
  convention for non-integrable integrands is itself `2`-homogeneous.

Hence no hypothesis is carried on `ψ` in the theorem.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Word

open Work.BoseKinLoc
open Work.BSKinetic
open Submission.BoseGases

set_option autoImplicit false

/-! ## 0. Auxiliary linearity lemmas -/

-- Variable-scope for the auxiliary linearity lemmas of this file.
namespace MomAux

/-- The `p`-convention Fourier transform `kinFT` is `ℂ`-linear in the state. -/
lemma kinFT_const_mul (c : ℂ) (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    kinFT (fun z => c * f z) p = c * kinFT f p := by
  unfold kinFT
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  ring

/-- The moving-box mean is linear in the state. -/
lemma bsMean_const_mul (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    bsMean ℓ u (fun z => c * ψ z) = c * bsMean ℓ u ψ := by
  unfold bsMean
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The box-mean-free projection `Q_u = 1 − (box mean)` is linear in the state. -/
lemma bsQ_const_mul (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    bsQ ℓ u (fun z => c * ψ z) = fun x => c * bsQ ℓ u ψ x := by
  funext x
  unfold bsQ
  rw [bsMean_const_mul]
  ring

/-- Squaring the norm of a complex multiple by a *real* scalar. -/
lemma norm_sq_ofReal_mul (c : ℝ) (w : ℂ) : ‖(c : ℂ) * w‖ ^ 2 = c ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  have h : ‖(c : ℂ)‖ ^ 2 = c ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [h]

end MomAux

open MomAux

/-! ## 1. The theorem -/

theorem momForm_const_mul {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) (c : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.momForm ℓ d u (fun z => c * ψ z) = c ^ 2 * Work.BoseKinLoc.momForm ℓ d u ψ := by
  -- the mean-free projection is linear
  have hQ : ∀ z, Qfree ℓ u (fun z => c * ψ z) z = c * Qfree ℓ u ψ z := by
    intro z
    exact congrFun (bsQ_const_mul ℓ u c ψ) z
  -- the windowed state of `c·ψ` is `(c:ℂ)` times the windowed state of `ψ`
  have hfun : (fun z => (indU ℓ u z : ℂ) * ((Qfree ℓ u (fun z => c * ψ z) z : ℝ) : ℂ))
      = fun z => (c : ℂ) * ((indU ℓ u z : ℂ) * ((Qfree ℓ u ψ z : ℝ) : ℂ)) := by
    funext z
    rw [hQ z]
    push_cast
    ring
  -- `kinFT` of the rescaled windowed state
  have hkin : ∀ p, kinFT (fun z => (indU ℓ u z : ℂ) * ((Qfree ℓ u (fun z => c * ψ z) z : ℝ) : ℂ)) p
      = (c : ℂ) * kinFT (fun z => (indU ℓ u z : ℂ) * ((Qfree ℓ u ψ z : ℝ) : ℂ)) p := by
    intro p
    rw [hfun]
    exact kinFT_const_mul (c : ℂ) _ p
  -- the `p`-integral scales by `c²`
  have hint : (∫ p : EuclideanSpace ℝ (Fin 3), momProj ℓ d p *
        ‖kinFT (fun z => (indU ℓ u z : ℂ) * ((Qfree ℓ u (fun z => c * ψ z) z : ℝ) : ℂ)) p‖ ^ 2)
      = c ^ 2 * ∫ p : EuclideanSpace ℝ (Fin 3), momProj ℓ d p *
        ‖kinFT (fun z => (indU ℓ u z : ℂ) * ((Qfree ℓ u ψ z : ℝ) : ℂ)) p‖ ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hkin p, norm_sq_ofReal_mul]
    ring
  unfold momForm
  rw [hint]
  ring

end Work.BoseKinLoc.Word
