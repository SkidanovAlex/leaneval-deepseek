import Submission.Work.OddCurve.Reduction
import Submission.Odd.Final

/-!
# The endgame: `OddCurveExists` gives the odd-dimensional family data

This file closes the loop between this chapter and the consumer
`Submission.Odd.Final.odd_floating_family_data_of_envelope_curve`: from
`Work.OddCurve.OddCurveExists n` (the deliverable of the chapter, `d = 2n+1`, `n ≥ 1`) and the bump
construction `Work.OddCurve.exists_isSmallFlatBump` one obtains `Submission.Odd.OddFamilyData d`, the
package consumed by `Submission.Odd.Leaf` to prove Ryabogin's odd-dimensional case.

So the whole odd half of the main theorem is: `Work.OddCurve.SmallSlopeCurveExists n`
⟶ `Work.OddCurve.OddCurveExists n` (`Work.OddCurve.oddCurveExists_of_smallSlopeCurveExists`)
⟶ `Submission.Odd.OddFamilyData d` (`Work.OddCurve.oddFamilyData_of_oddCurveExists`).
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise

/-- **The endgame.**  `OddCurveExists n` (for `d = 2n+1`, `n ≥ 1`, `d ≥ 3`) produces the
odd-dimensional family data of Ryabogin's construction. -/
theorem oddFamilyData_of_oddCurveExists {d : ℕ} [NeZero d] (hd : 3 ≤ d) (hdodd : Odd d)
    (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n) (H : OddCurveExists n) :
    Submission.Odd.OddFamilyData d := by
  obtain ⟨ε, hε, hcurve⟩ := H
  obtain ⟨h, hbump, hne, _h0, ⟨s₀, hs₀, hs₀ne⟩⟩ := exists_isSmallFlatBump ε hε
  obtain ⟨C, x, y, hH, hme⟩ := hcurve h hbump hne
  obtain ⟨hA, hB⟩ :=
    (momentEqsOn_Ioc_iff n C h x y (Work.OddEnvelope.envelopeProfile h x y)).mp hme
  have hzero : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → h s = 0 := by
    intro s hs
    by_contra hne'
    have hmem : s ∈ Function.support h := by simpa [Function.mem_support] using hne'
    have hsub := hbump.support_subset hmem
    exact absurd hs (not_le.mpr hsub.2)
  exact Submission.Odd.odd_floating_family_data_of_envelope_curve (d := d) hd hdodd n hdn hn
    hbump.contDiff ⟨s₀, hs₀, hs₀ne⟩ hzero hH
    (fun s hs hs1 => hA s hs hs1) (fun s hs hs1 => hB s hs hs1)

/-- **The endgame, from the remaining input.**  The transition-slope curve alone gives the
odd-dimensional family data. -/
theorem oddFamilyData_of_smallSlopeCurveExists {d : ℕ} [NeZero d] (hd : 3 ≤ d) (hdodd : Odd d)
    (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n) (H : SmallSlopeCurveExists n) :
    Submission.Odd.OddFamilyData d :=
  oddFamilyData_of_oddCurveExists hd hdodd n hdn hn (oddCurveExists_of_smallSlopeCurveExists n H)

end

end Work.OddCurve
