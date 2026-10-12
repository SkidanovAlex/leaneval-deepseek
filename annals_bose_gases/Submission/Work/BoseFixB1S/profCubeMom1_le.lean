import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.symACube_fsKinCoeff_mix_scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.profCubeMom1_le`

The first moment of the cube cutoff's cosine profile is dominated by the mass plus the second
moment:

    `(2π)⁻³ ∫_p (profHatCube M p)² ‖p‖ ≤ 1 + (2π)⁻³ ∫_p (profHatCube M p)² ‖p‖²`.

Since `‖p‖ ≤ 1 + ‖p‖²` pointwise and `(2π)⁻³ ∫ (profHatCube M p)² = 1` (the proved
`pcProfHatCube_mass_eq`), this is the pointwise inequality integrated against the nonnegative
weight `(profHatCube M p)²` (whose first and second weighted integrals are integrable by
`profCubeMom2Integrable`, hence also the dominating function).
-/

namespace Work.BoseFixB1S

open MeasureTheory Filter
open scoped Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem profCubeMom1_le (M : ℕ) (hM : 1 ≤ M) :
    ((2 * Real.pi) ^ 3)⁻¹ *
      (∫ p : EuclideanSpace ℝ (Fin 3), (Work.BoseFixB1S.profHatCube M p) ^ 2 * ‖p‖)
    ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ *
      (∫ p : EuclideanSpace ℝ (Fin 3), (Work.BoseFixB1S.profHatCube M p) ^ 2 * ‖p‖ ^ 2) := by
  have hA : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ :=
    inv_pos.mpr (by positivity)
  have hmass := pcProfHatCube_mass_eq M hM
  have hsq : Integrable (fun p : E3 => (profHatCube M p) ^ 2) := profCubeSqIntegrable M hM
  have h2 : Integrable (fun p : E3 => (profHatCube M p) ^ 2 * ‖p‖ ^ 2) :=
    (profCubeMom2Integrable M hM).congr (Eventually.of_forall fun p => by ring)
  have hg : Integrable (fun p : E3 =>
      (profHatCube M p) ^ 2 + (profHatCube M p) ^ 2 * ‖p‖ ^ 2) := hsq.add h2
  have hle : (∫ p : E3, (profHatCube M p) ^ 2 * ‖p‖)
      ≤ ∫ p : E3, ((profHatCube M p) ^ 2 + (profHatCube M p) ^ 2 * ‖p‖ ^ 2) := by
    refine integral_mono_of_nonneg ?_ hg ?_
    · exact Eventually.of_forall fun p => mul_nonneg (sq_nonneg _) (norm_nonneg _)
    · refine Eventually.of_forall fun p => ?_
      show (profHatCube M p) ^ 2 * ‖p‖
        ≤ (profHatCube M p) ^ 2 + (profHatCube M p) ^ 2 * ‖p‖ ^ 2
      have h1 : ‖p‖ ≤ 1 + ‖p‖ ^ 2 := by
        nlinarith [sq_nonneg (‖p‖ - 1), norm_nonneg p]
      calc (profHatCube M p) ^ 2 * ‖p‖
          ≤ (profHatCube M p) ^ 2 * (1 + ‖p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (profHatCube M p) ^ 2 + (profHatCube M p) ^ 2 * ‖p‖ ^ 2 := by ring
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, (profHatCube M p) ^ 2 * ‖p‖)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : E3, ((profHatCube M p) ^ 2 + (profHatCube M p) ^ 2 * ‖p‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hle hA.le
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          ((∫ p : E3, (profHatCube M p) ^ 2)
            + (∫ p : E3, (profHatCube M p) ^ 2 * ‖p‖ ^ 2)) := by
        rw [integral_add hsq h2]
    _ = 1 + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, (profHatCube M p) ^ 2 * ‖p‖ ^ 2) := by
        rw [mul_add, hmass]

end Work.BoseFixB1S
