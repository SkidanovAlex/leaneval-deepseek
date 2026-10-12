import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.plancherel_pconv
import Submission.Work.OneBodyKin.kinFT_chi_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.profHat_sq_integral`

The total mass of the squared Fourier profile of the bump `χ`:

    `∫_p profHat(p)² dp = (2π)³`.

Since `χ` is even and real, `profHat` is its Fourier transform in the `p`-convention
(`Work.OneBodyKin.kinFT_chi_eq`), so this is the Plancherel identity at the `L²`-normalized
bump: `∫_p ‖kinFT χ‖² = (2π)³ ∫_x χ² = (2π)³ · 1 = (2π)³`.  Both the Plancherel identity
(`Work.BSKinetic.plancherel_pconv`) and the normalization `∫_x χ² = 1`
(`Submission.BoseGases.chi_L2`) already exist in the corpus; the only work here is the
bookkeeping of the `(2π)³` factor and the identification of the real square with the complex
squared modulus.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

theorem profHat_sq_integral :
    (∫ p : EuclideanSpace ℝ (Fin 3), (Work.OneBodyKin.profHat p) ^ 2) = (2 * Real.pi) ^ 3 := by
  -- Step 1: pointwise, the real square of `profHat` is the squared modulus of `kinFT χ`.
  have hpt : ∀ p : ℝ³, (profHat p) ^ 2
      = ‖kinFT (fun z : ℝ³ => (chi z : ℂ)) p‖ ^ 2 := by
    intro p
    rw [kinFT_chi_eq p]
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  have h1 : (∫ p : ℝ³, (profHat p) ^ 2)
      = ∫ p : ℝ³, ‖kinFT (fun z : ℝ³ => (chi z : ℂ)) p‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with p
    exact hpt p
  rw [h1]
  -- Step 2: Plancherel at the `L²`-normalized bump `χ`, whose total mass is `1`.
  have hp := Work.BSKinetic.plancherel_pconv chi chi_contDiff chi_hasCompactSupport
  rw [chi_L2] at hp
  -- `hp : (2π)⁻³ * ∫_p ‖kinFT χ p‖² = 1`
  have hA : ((2 * Real.pi) ^ 3) ≠ 0 := by positivity
  rw [inv_mul_eq_iff_eq_mul₀ hA] at hp
  -- `hp : ∫_p ‖kinFT χ p‖² = (2π)³ * 1`
  simpa using hp

end Work.OneBodyKin
