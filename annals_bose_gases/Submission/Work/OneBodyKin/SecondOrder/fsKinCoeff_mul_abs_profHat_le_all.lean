import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.OneBodyKin.exists_fsKinCoeff_mul_abs_profHat_le
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SecondOrder.fsKinCoeff_mul_abs_profHat_le_all`

The integral `∫_p [‖p‖ − C]₊² |profHat p| dp` tends to `0` as `C → ∞`; here we record the
*upward-closed* form of that statement: once the cut-off `C` is large enough, every larger
cut-off works as well.

The point is the **monotonicity of `fsKinCoeff` in its cut-off**: for `C ≤ C'`,
`[r − C']₊² ≤ [r − C]₊²` because `r ↦ max (r − C) 0` is nonincreasing in `C` and nonnegative.
Multiplying by `|profHat p| ≥ 0` gives a pointwise inequality of integrands, hence (both
integrands being integrable, `integrable_fsKinCoeff_mul_abs_profHat`) an inequality of integrals.
Combined with `Work.OneBodyKin.exists_fsKinCoeff_mul_abs_profHat_le`, which supplies one good
cut-off `C₀`, this yields the claimed `∀ C ≥ C₀` statement.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real

namespace Work.OneBodyKin.SecondOrder

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`fsKinCoeff` is antitone in its cut-off parameter**: larger cut-off, smaller coefficient.
Indeed `r ↦ [r − c]₊` is nonincreasing in `c`, and squaring preserves the order on `[0, ∞)`. -/
lemma fsKinCoeff_antitone {c c' r : ℝ} (h : c ≤ c') :
    Submission.BoseGases.fsKinCoeff c' r ≤ Submission.BoseGases.fsKinCoeff c r := by
  unfold Submission.BoseGases.fsKinCoeff
  have hle : max (r - c') 0 ≤ max (r - c) 0 :=
    max_le_max (by linarith) le_rfl
  exact sq_le_sq.mpr (by
    rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (le_max_right _ _)]
    exact hle)

/-- **The cut-off can be made arbitrarily large.**  For every `δ > 0` there is a cut-off `C₀ > 0`
such that *every* cut-off `C ≥ C₀` makes the FS-weighted profile-integral at most `δ`:
`∫_p [‖p‖ − C]₊² |profHat p| dp ≤ δ`.

This is `Work.OneBodyKin.exists_fsKinCoeff_mul_abs_profHat_le` (one good cut-off) upgraded to the
upward-closed form by the antitonicity of `fsKinCoeff` in the cut-off. -/
theorem fsKinCoeff_mul_abs_profHat_le_all (δ : ℝ) (hδ : 0 < δ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p| ≤ δ := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.OneBodyKin.exists_fsKinCoeff_mul_abs_profHat_le δ hδ
  refine ⟨C₀, hC₀pos, fun C hC => ?_⟩
  have hmono :
      ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p|
        ≤ ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C₀ ‖p‖ * |Work.OneBodyKin.profHat p| := by
    refine integral_mono_ae (Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat C)
      (Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat C₀) ?_
    filter_upwards with p
    exact mul_le_mul_of_nonneg_right (fsKinCoeff_antitone hC) (abs_nonneg _)
  linarith

end Work.OneBodyKin.SecondOrder
