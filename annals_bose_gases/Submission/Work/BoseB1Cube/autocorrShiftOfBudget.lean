import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.autocorr_sub_le
import Submission.Work.BoseB1Cube.shiftMassLower
import Submission.Work.BoseFixB1B.chiSmallB_windowData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

set_option linter.unusedVariables false

/-- **The autocorrelation of the sliding cutoff stays within a factor `(1 − δ)` of its mass
after a shift of length at most `R`, as soon as the mass dominates
`δ⁻¹R²C²(ℓd)³`.**

Here `χ = chiSmallB M ℓ d u`, `C` is a sup bound for `‖∇χ‖`, and `hint` bounds `∫‖∇χ‖` by
`C(ℓd)³`.  The `L²` modulus of continuity of `χ` at the shift `z` (`Work.BoseB1Cube.autocorr_sub_le`,
via the polarisation identity and the line-average identity) gives

    ∫χ² − ∫χ(x)χ(x−z) ≤ (‖z‖²/2)·C·(C(ℓd)³) ≤ (R²/2)C²(ℓd)³ ≤ δ·∫χ² ,

the last step being exactly the mass hypothesis.  Rearranging gives
`(1−δ)∫χ² ≤ ∫χ(x)χ(x−z)`. -/
theorem autocorrShiftOfBudget {M : ℕ} (hM : 4 ≤ M) {ℓ d δ R : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hδ : 0 < δ) (u : EuclideanSpace ℝ (Fin 3)) {C : ℝ}
    (hsup : ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖ ≤ C)
    (hint : ∫ x : EuclideanSpace ℝ (Fin 3),
      ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖ ≤ C * (ℓ * d) ^ 3)
    (hmass : (1 / δ) * R ^ 2 * C ^ 2 * (ℓ * d) ^ 3
      ≤ Work.SmallBoxSliding.chiMass M ℓ d u) :
    ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      (1 - δ) * Work.SmallBoxSliding.chiMass M ℓ d u
        ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
            * Submission.BoseGases.chiSmallB M ℓ d u (x - z) := by
  intro z hz
  -- ### The cutoff is `C²` with compact support and nonnegative
  have h2 : ContDiff ℝ 2 (Submission.BoseGases.chiSmallB M ℓ d u) :=
    (Work.BoseFixB1B.chiSmallB_contDiff_three hM hℓ u).of_le (by norm_num)
  have hcs : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) :=
    Submission.BoseGases.chiSmallB_hasCompactSupport (by omega) hℓ u
  have hnn : ∀ x : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    fun x => Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  -- ### The `L²` modulus-of-continuity bound
  have hsub := autocorr_sub_le h2 hcs hnn hsup hint z
  -- ### Nonnegativity of the constants
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hsup 0)
  have hld0 : 0 ≤ (ℓ * d) ^ 3 :=
    pow_nonneg (le_of_lt (mul_pos hℓ hd)) 3
  have hY0 : 0 ≤ R ^ 2 * C ^ 2 * (ℓ * d) ^ 3 :=
    mul_nonneg (mul_nonneg (sq_nonneg R) (sq_nonneg C)) hld0
  have hX0 : 0 ≤ C * C * (ℓ * d) ^ 3 :=
    mul_nonneg (mul_nonneg hC0 hC0) hld0
  -- ### The mass hypothesis, in the integral spelling
  have hmassint : (1 / δ) * R ^ 2 * C ^ 2 * (ℓ * d) ^ 3
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x ^ 2 := by
    rw [← Work.SmallBoxSliding.chiMass_def]
    exact hmass
  have hmassR : R ^ 2 * C ^ 2 * (ℓ * d) ^ 3
      ≤ δ * ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hmassint (le_of_lt hδ)
    have heq : δ * ((1 / δ) * R ^ 2 * C ^ 2 * (ℓ * d) ^ 3)
        = R ^ 2 * C ^ 2 * (ℓ * d) ^ 3 := by
      field_simp
    rwa [heq] at h
  -- ### The arithmetic: the defect is at most `δ·mass`
  have hstep1 : ‖z‖ ^ 2 / 2 * (C * C * (ℓ * d) ^ 3)
      ≤ R ^ 2 / 2 * (C * C * (ℓ * d) ^ 3) := by
    have hz2 : ‖z‖ ^ 2 / 2 ≤ R ^ 2 / 2 := by nlinarith [norm_nonneg z]
    exact mul_le_mul_of_nonneg_right hz2 hX0
  have hstep2 : R ^ 2 / 2 * (C * C * (ℓ * d) ^ 3)
      ≤ R ^ 2 * C ^ 2 * (ℓ * d) ^ 3 := by
    nlinarith [hY0]
  have hle : ‖z‖ ^ 2 / 2 * C * (C * (ℓ * d) ^ 3)
      ≤ δ * ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x ^ 2 := by
    have hkey : ‖z‖ ^ 2 / 2 * C * (C * (ℓ * d) ^ 3)
        = ‖z‖ ^ 2 / 2 * (C * C * (ℓ * d) ^ 3) := by ring
    rw [hkey]
    linarith [hstep1, hstep2, hmassR]
  -- ### Assembly
  have hfinal : (1 - δ) * (∫ x : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.chiSmallB M ℓ d u x ^ 2)
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
          * Submission.BoseGases.chiSmallB M ℓ d u (x - z) := by
    linarith [hsub, hle]
  rw [Work.SmallBoxSliding.chiMass_def]
  exact hfinal

end Work.BoseB1Cube
