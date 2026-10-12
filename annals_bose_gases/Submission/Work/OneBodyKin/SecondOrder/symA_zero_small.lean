import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.OneBodyKin.SecondOrder.exists_fsKinCoeff_mul_profHat_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SecondOrder.symA_zero_small`

At scale `ℓ = 1` and momentum `q = 0`, the unprojected family symbol is

    `symA 1 F 0 = (2π)⁻³ ∫_p F(‖p‖) · profHat(p)² dp`,

so for the FS cut-off `F = fsKinCoeff C = [· − C]₊²` the symbol is the integral of
`[‖p‖ − C]₊² profHat(p)²`, which tends to `0` as `C → ∞` by dominated convergence
(dominated by `(1 + ‖p‖)² profHat(p)²`, integrable by `integrable_profHat_sq_mul_norm_pow 2`).

Here we record the resulting "the cut-off can be made large" statement: for every `ε > 0` the
origin value `symA 1 (fsKinCoeff C) 0` is at most `ε` once the cut-off `C` is large enough.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real

namespace Work.OneBodyKin.SecondOrder

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- At the origin and at scale `1` the unprojected symbol is the plain integral of the symbol
weighted by the squared bump profile. -/
lemma symA_one_zero (F : ℝ → ℝ) :
    Work.OneBodyKin.symA 1 F 0 =
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 := by
  simp only [Work.OneBodyKin.symA, zero_add, inv_one, one_smul]

theorem symA_zero_small (ε : ℝ) (hε : 0 < ε) :
    ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C →
      Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0 ≤ ε := by
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  have hδ : 0 < (2 * Real.pi) ^ 3 * ε := mul_pos hpi hε
  obtain ⟨C0, hC0⟩ := exists_fsKinCoeff_mul_profHat_sq_le ((2 * Real.pi) ^ 3 * ε) hδ
  refine ⟨C0, fun C hC => ?_⟩
  rw [symA_one_zero]
  refine (mul_le_mul_of_nonneg_left (hC0 C hC) (by positivity)).trans (le_of_eq ?_)
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpi), one_mul]

end Work.OneBodyKin.SecondOrder
