import Mathlib
import Submission.Work.KT.CapCoord

namespace Work.KT

/-- **Continuity of the meridian formula** on the set where the height is at most `1/2`.
The domain is the subtype of pairs `(η, z) ∈ ℝ × (Eu m × ℝ)` with `z.2 ≤ 1/2` (written
`q.1.1` for `η` and `q.1.2` for `z`), on which the denominator `1 - z.2` of `merCoord` is bounded
below by `1/2 > 0`. -/
lemma continuous_merCoord (m : ℕ) :
    Continuous fun q : {q : ℝ × (Eu m × ℝ) // q.2.2 ≤ 1 / 2} => merCoord m q.1.1 q.1.2 := by
  have hη : Continuous fun q : {q : ℝ × (Eu m × ℝ) // q.2.2 ≤ 1 / 2} => q.1.1 :=
    continuous_subtype_val.fst
  have hz : Continuous fun q : {q : ℝ × (Eu m × ℝ) // q.2.2 ≤ 1 / 2} => q.1.2.2 :=
    continuous_subtype_val.snd.snd
  have hz1 : Continuous fun q : {q : ℝ × (Eu m × ℝ) // q.2.2 ≤ 1 / 2} => q.1.2.1 :=
    continuous_subtype_val.snd.fst
  have hden : ∀ q : {q : ℝ × (Eu m × ℝ) // q.2.2 ≤ 1 / 2}, 1 - q.1.2.2 ≠ 0 := by
    intro q
    have hq : q.1.2.2 ≤ 1 / 2 := q.2
    have hpos : 0 < 1 - q.1.2.2 := by linarith
    exact ne_of_gt hpos
  have harg : Continuous fun q : {q : ℝ × (Eu m × ℝ) // q.2.2 ≤ 1 / 2} =>
      q.1.1 * (2 - q.1.1 * (q.1.2.2 + 1)) / (1 - q.1.2.2) :=
    (hη.mul (continuous_const.sub (hη.mul (hz.add continuous_const)))).div
      (continuous_const.sub hz) hden
  simp only [merCoord]
  exact Continuous.prodMk ((Real.continuous_sqrt.comp harg).smul hz1)
    (continuous_const.add (hη.mul (hz.add continuous_const)))

end Work.KT
