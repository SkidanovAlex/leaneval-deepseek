import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.Cores.PPureShiftRad.Basic
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.Basic
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.MajEst
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TopSlotTwoFts

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The mean-value (dilation) estimate for the difference quotient, in the shape required by
`TL2.shiftZeroSlots_aux`; this is the clean `pPureShiftAux` version. -/
theorem dilEstimateClean : Work.FTS.EllipticEst.Cores.Pieces.TL2.DilEstimate := by
  intro α c g hg hmem hc
  exact Work.FTS.EllipticEst.Cores.pPureShiftAux.HkMem_dq_and_HkSq_dq_le_self hg hmem hc

/-- The iterated difference-quotient limit `(dq c)^j f → D_z^j f`, in the shape required by
`TL2.shiftZeroSlots_aux`. -/
theorem dqLimitClean : Work.FTS.EllipticEst.Cores.Pieces.TL2.DqLimit := by
  intro f hf j z θ hz hθ
  exact Work.FTS.EllipticEst.Cores.Dil.dqIterTendsto hf j hz hθ

/-- **The level-`0` slots at the radial shifts `j ≤ 2`.**

For `0 < α ≤ 1/4` and a datum of the weak class `TT.EllWeakPos α 2 F Ψ`, every `j ≤ 2` satisfies

`α⁴·|z²∂_z²(D_z^jΨ)|²_{ℋ⁰} + |∂_θ²(D_z^jΨ)|²_{ℋ⁰} ≤ C·|F|²_{ℋ²}`

with a universal (`α`-independent) constant `C`, granted the level-`0` estimate `EllWeak0`. -/
theorem ShiftZeroSlots2 (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ → ∀ j : ℕ, j ≤ 2 →
      α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₀, hC₀pos, hEW⟩ := h0
  obtain ⟨C0, hC0pos, h0b⟩ :=
    Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots_bound dilEstimateClean dqLimitClean
      2 0 (by norm_num) C₀ hC₀pos hEW
  obtain ⟨C1, hC1pos, h1b⟩ :=
    Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots_bound dilEstimateClean dqLimitClean
      2 1 (by norm_num) C₀ hC₀pos hEW
  obtain ⟨C2, hC2pos, h2b⟩ :=
    Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots_bound dilEstimateClean dqLimitClean
      2 2 (by norm_num) C₀ hC₀pos hEW
  refine ⟨max (max C0 C1) C2 + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk j hj
  have hNF : (0 : ℝ) ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hm0 : C0 ≤ max (max C0 C1) C2 + 1 := by
    have h1 : C0 ≤ max C0 C1 := le_max_left _ _
    have h2 : max C0 C1 ≤ max (max C0 C1) C2 := le_max_left _ _
    linarith
  have hm1 : C1 ≤ max (max C0 C1) C2 + 1 := by
    have h1 : C1 ≤ max C0 C1 := le_max_right _ _
    have h2 : max C0 C1 ≤ max (max C0 C1) C2 := le_max_left _ _
    linarith
  have hm2 : C2 ≤ max (max C0 C1) C2 + 1 := by
    have h1 : C2 ≤ max (max C0 C1) C2 := le_max_right _ _
    linarith
  interval_cases j
  · exact le_trans (h0b α F Ψ hα hα4 hwk) (mul_le_mul_of_nonneg_right hm0 hNF)
  · exact le_trans (h1b α F Ψ hα hα4 hwk) (mul_le_mul_of_nonneg_right hm1 hNF)
  · exact le_trans (h2b α F Ψ hα hα4 hwk) (mul_le_mul_of_nonneg_right hm2 hNF)

end Work.FTS.EllipticEst.TopSlotTwoFts
