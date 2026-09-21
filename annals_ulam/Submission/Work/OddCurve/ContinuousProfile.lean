import Submission.Work.OddCurve.Defs

/-!
# The envelope profile is continuous on `ℝ`

`Work.OddEnvelope` proves that `envelopeProfile h x y` is continuous on the closed interval
`[-1,1]` (`continuousOn_envelopeProfile'`) and that it vanishes at `±1`; outside `[-1,1]` it is
identically `0`.  Gluing the three closed pieces `(-∞,-1]`, `[-1,1]`, `[1,∞)` therefore gives
global continuity — which is what the Leibniz rules for the moment integrals
(`Work.OddCurve.hasDerivAt_integral_rad` and its variants, which ask for `Continuous f`) consume.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The envelope profile is globally continuous. -/
theorem continuous_envelopeProfile {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    Continuous (Work.OddEnvelope.envelopeProfile h x y) := by
  have hz_lt : ∀ t : ℝ, t < -1 → Work.OddEnvelope.envelopeProfile h x y t = 0 := by
    intro t ht
    have h1 : t ∉ Set.Ioo (0 : ℝ) 1 := fun hc => by linarith [hc.1]
    have h2 : t ∉ Set.Ioo (-1 : ℝ) 0 := fun hc => by linarith [hc.1]
    have h3 : t ≠ 0 := by linarith
    simp only [Work.OddEnvelope.envelopeProfile]
    rw [if_neg h1, if_neg h2, if_neg h3]
  have hz_gt : ∀ t : ℝ, 1 < t → Work.OddEnvelope.envelopeProfile h x y t = 0 := by
    intro t ht
    have h1 : t ∉ Set.Ioo (0 : ℝ) 1 := fun hc => by linarith [hc.2]
    have h2 : t ∉ Set.Ioo (-1 : ℝ) 0 := fun hc => by linarith [hc.2]
    have h3 : t ≠ 0 := by linarith
    simp only [Work.OddEnvelope.envelopeProfile]
    rw [if_neg h1, if_neg h2, if_neg h3]
  have hleft : ContinuousOn (Work.OddEnvelope.envelopeProfile h x y) (Set.Iic (-1)) := by
    refine ContinuousOn.congr (continuousOn_const (c := (0 : ℝ))) ?_
    intro t ht
    rcases lt_or_eq_of_le (show t ≤ (-1 : ℝ) from ht) with h' | h'
    · exact hz_lt t h'
    · rw [h']; exact Work.OddEnvelope.envelopeProfile_left_end
  have hright : ContinuousOn (Work.OddEnvelope.envelopeProfile h x y) (Set.Ici 1) := by
    refine ContinuousOn.congr (continuousOn_const (c := (0 : ℝ))) ?_
    intro t ht
    rcases lt_or_eq_of_le (show (1 : ℝ) ≤ t from ht) with h' | h'
    · exact hz_gt t h'
    · rw [← h']; exact Work.OddEnvelope.envelopeProfile_right_end
  have hmid : ContinuousOn (Work.OddEnvelope.envelopeProfile h x y) (Set.Icc (-1) 1) :=
    Work.OddEnvelope.continuousOn_envelopeProfile' H
  have hun : Set.Iic (-1 : ℝ) ∪ Set.Icc (-1) 1 = Set.Iic 1 := by
    ext t
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro (h' | ⟨h1, h2''⟩)
      · linarith
      · exact h2''
    · intro h'
      by_cases h'' : t ≤ -1
      · exact Or.inl h''
      · push Not at h''
        exact Or.inr ⟨le_of_lt h'', h'⟩
  have h2 : ContinuousOn (Work.OddEnvelope.envelopeProfile h x y)
      (Set.Iic (-1) ∪ Set.Icc (-1) 1) :=
    ContinuousOn.union_of_isClosed hleft hmid isClosed_Iic isClosed_Icc
  have hP : ContinuousOn (Work.OddEnvelope.envelopeProfile h x y) (Set.Iic 1) := by
    have h2' := h2
    rwa [hun] at h2'
  have h5 : ContinuousOn (Work.OddEnvelope.envelopeProfile h x y) (Set.univ) := by
    simpa [Set.Iic_union_Ici] using
      (ContinuousOn.union_of_isClosed hP hright isClosed_Iic isClosed_Ici)
  rwa [continuousOn_univ] at h5

end

end Work.OddCurve
