import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.OneBodyKin.fourier_convScale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.kinFT_chiScale`

The `p`-convention Fourier transform of the *scaled* bump `chiScale ℓ = χ(·/ℓ)` is `ℓ³` times
the bump profile at `ℓ • p`:

    `kinFT (chiScale ℓ) p = ℓ³ · profHat (ℓ • p)`.

The computation is a single dilation substitution `z = ℓ • w` (Jacobian `ℓ³`, the complex-valued
dilation lemma `integral_eq_smul_integral_comp_smul` of `fourier_convScale_scaling`), together
with `⟪p, ℓ•w⟫ = ⟪ℓ•p, w⟫`, `χ(ℓ⁻¹ • (ℓ•w)) = χ w`, and the identification
`kinFT χ = profHat` of `kinFT_chi_eq`.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem kinFT_chiScale {ℓ : ℝ} (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ z : ℂ)) p
      = (ℓ : ℂ) ^ 3 * (Work.OneBodyKin.profHat (ℓ • p) : ℂ) := by
  -- pointwise substitution `z = ℓ • w`
  have hpt : ∀ w : ℝ³,
      Complex.exp (-(Complex.I * (inner ℝ p (ℓ • w) : ℂ))) *
          (Submission.BoseGases.chiScale ℓ (ℓ • w) : ℂ)
        = Complex.exp (-(Complex.I * (inner ℝ (ℓ • p) w : ℂ))) *
          (Submission.BoseGases.chi w : ℂ) := by
    intro w
    have hcs : Submission.BoseGases.chiScale ℓ (ℓ • w) = Submission.BoseGases.chi w := by
      rw [Submission.BoseGases.chiScale, smul_smul, inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
    have hinner : inner ℝ p (ℓ • w) = inner ℝ (ℓ • p) w := by
      rw [inner_smul_right, inner_smul_left]
      simp
    rw [hcs, hinner]
  rw [Submission.BoseGases.kinFT]
  rw [integral_eq_smul_integral_comp_smul
    (g := fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Submission.BoseGases.chiScale ℓ z : ℂ)) hℓ]
  rw [show (∫ s : ℝ³,
        Complex.exp (-(Complex.I * (inner ℝ p (ℓ • s) : ℂ))) *
          (Submission.BoseGases.chiScale ℓ (ℓ • s) : ℂ))
      = ∫ w : ℝ³,
          Complex.exp (-(Complex.I * (inner ℝ (ℓ • p) w : ℂ))) *
            (Submission.BoseGases.chi w : ℂ) from by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpt]
  rw [show (∫ w : ℝ³,
          Complex.exp (-(Complex.I * (inner ℝ (ℓ • p) w : ℂ))) *
            (Submission.BoseGases.chi w : ℂ))
      = Submission.BoseGases.kinFT (fun z : ℝ³ => (Submission.BoseGases.chi z : ℂ)) (ℓ • p)
    from rfl]
  rw [kinFT_chi_eq, Complex.real_smul, Complex.ofReal_pow]

end Work.OneBodyKin
