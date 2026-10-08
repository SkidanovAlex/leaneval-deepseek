import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.D16Aux
import Submission.Work.DSTR.D16.case1
import Submission.Work.DSTR.D16.case2
import Submission.Work.DSTR.D16.case34

namespace Work.DSTR

/-- **D16** (`Work.GW2.D16Prop`, Bender 1981 1.6): the four cases of a D-group.  Assembled from the leaves `DS2`--`DS7`, `InvolutionFusionProp` (for the central-involution case) and Bender 1.2 (`E1`).

The four clauses of `DShape (X ⧸ O(X))` are handled by
`Work.DSTR.case1` (`X/O(X)` a `2`-group: clauses (a), (b)),
`Work.DSTR.D16.case2` (a self-centralizing normal four-group: clauses (a), (b), (c)) and
`Work.DSTR.D16.case34` (`A₇` or a normal `L₂(q)`/`PGL₂(q)` of odd index: clauses (a), (b), (d)).
-/
theorem d16 (h2 : Work.GW2.OddCoreQuotProp) (h3 : Work.GW2.TwoRankProp)
    (h4 : Work.GW2.QuasisimpleSylowProp) (h5 : Work.GW2.LayerUniqueProp)
    (h6 : Work.GW2.QuasisimpleCenterOddProp) (h7 : Work.GW2.LayerShapeProp)
    (hfus : Work.GW2.InvolutionFusionProp) (he1 : Work.GW2.FittingSelfCentralizingProp) :
    Work.GW2.D16Prop := by
  intro X instG instF hFT hD hDG
  change d16a X ∨ d16b X ∨ d16c X ∨ d16d X
  rcases hDG with h1 | h2 | h3 | h4
  · rcases case1 X hFT hD h1 with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  · by_cases hP : IsPGroup 2 (X ⧸ Work.GW2.oddCore X)
    · rcases case1 X hFT hD hP with ha | hb
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
    · rcases Work.DSTR.D16.case2 X hFT hD hP h2 with ha | hb | hc
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Or.inl hc))
  · rcases Work.DSTR.D16.case34 X hFT hD (Or.inl h3) with ha | hb | hd
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inr hd))
  · rcases Work.DSTR.D16.case34 X hFT hD (Or.inr h4) with ha | hb | hd
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inr hd))

end Work.DSTR
