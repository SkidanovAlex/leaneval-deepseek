import Submission.Work.OddCurve.Free
import Submission.Work.OddCurve.Free.momentEqsOn_Ioc_one_of_smallSlopes_free

/-!
# The corrected reduction: transition-slope curve ⟹ `OddCurveExistsFree`

The free-tip analogue of `Work.OddCurve.Reduction`: a curve with the *free-tip* envelope structure
and the two moment equations on the transition slopes `0 < s ≤ 1 - τ` gives
`Work.OddCurve.Free.OddCurveExistsFree`, the corrected deliverable (the two moment equations on all
slopes `0 < s ≤ 1`, with the tips left free), using
`Work.OddCurve.Free.momentEqsOn_Ioc_one_of_smallSlopes_free` for the tail.

This is the shape in which the paper's Steps 2 + 3 should be attacked once the interface is relaxed:
the single remaining input becomes `SmallSlopeCurveExistsFree n` (with `CurveDataFree`-style
hypotheses, i.e. the same construction as before but without the tip normalisation).
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise

/-- The transition-slope existence statement, in the free-tip interface: for every sufficiently
small flat bump there is a curve with the free-tip envelope structure and the two moment equations
on the transition slopes `0 < s ≤ 1 - τ`. -/
def SmallSlopeCurveExistsFree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBump ε h → h ≠ 0 →
    ∃ x y : ℝ → ℝ, IsEnvelopeCurveFree h x y ∧ SmallSlopeEqs n h x y

/-- The old transition-slope statement implies the free-tip one. -/
theorem smallSlopeCurveExistsFree_of_smallSlopeCurveExists (n : ℕ)
    (H : SmallSlopeCurveExists n) : SmallSlopeCurveExistsFree n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hbump hne => ?_⟩
  obtain ⟨x, y, hIC, hsl⟩ := H' h hbump hne
  exact ⟨x, y, isEnvelopeCurveFree_of_isEnvelopeCurve hIC, hsl⟩

/-- **The corrected main reduction.**  The transition-slope curve (the paper's Steps 2 and 3) gives
`OddCurveExistsFree`. -/
theorem oddCurveExistsFree_of_smallSlopeCurveExistsFree (n : ℕ)
    (H : SmallSlopeCurveExistsFree n) : OddCurveExistsFree n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hbump hne => ?_⟩
  obtain ⟨x, y, hIC, hsl⟩ := H' h hbump hne
  exact ⟨refConst n, x, y, hIC,
    momentEqsOn_Ioc_one_of_smallSlopes_free n hIC
      (fun s hs => hbump.eventuallyEq_zero_of_gt hs) hsl⟩

/-- The old chain through `OddCurveExists` is recovered from the corrected one plus the tips. -/
theorem smallSlopeCurveExists_of_smallSlopeCurveExistsFree (n : ℕ)
    (H : SmallSlopeCurveExistsFree n)
    (Htips : ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBump ε h → h ≠ 0 →
      ∀ x y : ℝ → ℝ, SmallSlopeEqs n h x y →
        Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 1) ∧ Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    SmallSlopeCurveExists n := by
  obtain ⟨ε, hε, H'⟩ := H
  obtain ⟨ε', hε', Htips⟩ := Htips
  refine ⟨min ε ε', lt_min hε hε', fun h hbump hne => ?_⟩
  have hmL : min ε ε' ≤ ε := min_le_left ε ε'
  have hmR : min ε ε' ≤ ε' := min_le_right ε ε'
  have hbumpε : IsSmallFlatBump ε h :=
    ⟨hbump.1, hbump.2.1, fun s => le_trans (hbump.2.2.1 s) hmL,
      fun s => le_trans (hbump.2.2.2.1 s) hmL,
      fun s => le_trans (hbump.2.2.2.2.1 s) hmL, hbump.2.2.2.2.2⟩
  have hbumpε' : IsSmallFlatBump ε' h :=
    ⟨hbump.1, hbump.2.1, fun s => le_trans (hbump.2.2.1 s) hmR,
      fun s => le_trans (hbump.2.2.2.1 s) hmR,
      fun s => le_trans (hbump.2.2.2.2.1 s) hmR, hbump.2.2.2.2.2⟩
  obtain ⟨x, y, hfr, hsl⟩ := H' h hbumpε hne
  obtain ⟨hx, hy⟩ := Htips h hbumpε' hne x y hsl
  exact ⟨x, y, isEnvelopeCurve_of_isEnvelopeCurveFree_of_tips hfr hx hy, hsl⟩

end

end Free
end Work.OddCurve
