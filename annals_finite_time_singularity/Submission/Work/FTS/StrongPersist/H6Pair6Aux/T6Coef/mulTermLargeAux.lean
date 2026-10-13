import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The pointwise domination of a leaf-weighted pair of slots by the two square roots of the
level-`l` and level-`6` integrands, in the weight-comparison form. -/
theorem pairDom {α : ℝ} (hα : 0 < α) {A f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ}
    {b₁ a₁ b a l : ℕ}
    (hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ)
    (hρA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
      → ρ z θ ≤ Work.FTS.TransportS.slotW α a₁ z θ)
    (hρf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
      → ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ)
    (hA : (l = 6 ∧ a₁ + b₁ ≤ 6) ∨ (l = 4 ∧ a₁ + b₁ ≤ 4))
    (hf : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * |Work.Spaces.mixed b₁ a₁ A z θ| * |Work.Spaces.mixed b a f z θ|
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α l A z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have h1 : ρ z θ * (Work.Spaces.mixed b₁ a₁ A z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α l A z θ := by
    refine le_trans (mul_le_mul_of_nonneg_right (hρA z θ hz hθ0 hθ1) (sq_nonneg _)) ?_
    rcases hA with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Work.FTS.StrongPersist.H6Pair6Aux.slotW_mul_le6 α hα A hθ h
    · exact Work.FTS.StrongPersist.H6Pair6Aux.slotW_mul_le4 α hα A hθ h
  have h2 : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    le_trans (mul_le_mul_of_nonneg_right (hρf z θ hz hθ0 hθ1) (sq_nonneg _))
      (Work.FTS.StrongPersist.H6Pair6Aux.slotW_mul_le6 α hα f hθ hf)
  exact Work.FTS.StrongPersist.H6Pair6Aux.leaf_prod_sqrt_le (hρnn z θ hz hθ0 hθ1) h1 h2

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
