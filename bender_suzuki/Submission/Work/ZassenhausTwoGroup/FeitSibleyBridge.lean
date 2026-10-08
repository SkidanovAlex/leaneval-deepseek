import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.coprime_card
import Submission.Work.ZassenhausTwoGroup.isNilpotent_Q
import Submission.Work.ZassenhausTwoGroup.twoPoint_ne_bot
import Submission.Work.ZassenhausTwoGroup.twoPart_sup_oddPart
import Submission.Work.ZassenhausTwoGroup.twoPart_inf_oddPart
import Submission.Work.ZassenhausTwoGroup.twoPart_commute_oddPart
import Submission.Work.ZassenhausTwoGroup.coprime_twoPart_oddPart
import Submission.Work.ZassenhausTwoGroup.isNilpotent_twoPart
import Submission.Work.ZassenhausTwoGroup.odd_card_oddPart
import Submission.Work.ZassenhausTwoGroup.isPGroup_two_iff
import Submission.Work.ZassenhausTwoGroup.not_isPGroup_two_of_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Feit–Sibley input for the Zassenhaus set-up

This module feeds the rank-one Zassenhaus data `H = Q ⋊ D` into the Feit–Sibley theorem
(Peterfalvi II, Appendice XII), i.e. into the black box `FeitSibleyProp`:

> `H = Q ⋊ D < G`, `(|D|,|Q|) = 1`, `Q` T.I., `Q = S × Q₁`, `S` nilpotent, `D` fixed point
> freely on `Q₁`, `Q₁` not a `2`-group, `|D|` odd ⟹ `𝓢 = {χ ∈ Irr H | Q₁ ⊄ ker χ}` has at
> least two members and is coherent for `Ind_H^G`.

In the rank-one set-up one takes
`D = twoPoint H t`, `Q₁ = O_{2'}(Q) = oddPart Q` and `S = O_2(Q) = twoPart Q`; the hypotheses
are supplied by the `Setting` lemmas of this area (`fpf_on_Q`, `isTI_Q`, `coprime_card`,
`isNilpotent_Q`, `twoPoint_ne_bot`, `twoPart_sup_oddPart`, `twoPart_inf_oddPart`,
`twoPart_commute_oddPart`, `coprime_twoPart_oddPart`, `isNilpotent_twoPart`, `odd_card_oddPart`,
`not_isPGroup_two_of_odd`).

The conclusion `Coherent (scriptS H (oddPart Q)) (indLin H)` is exactly the hypothesis under
which Feit's exceptional-character computation (Theorem 2 of Feit 1960, and Corollaries
2.1–2.4) produces the exceptional characters — see `Exceptional`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

noncomputable section

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G] [Fintype G]

theorem oddPart_le (Q : Subgroup G) : oddPart Q ≤ Q := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem twoPart_le (Q : Subgroup G) : twoPart Q ≤ Q := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- **The Feit–Sibley theorem in the rank-one Zassenhaus set-up.**  If `Q` is not a `2`-group
(so `O_{2'}(Q) ≠ 1` by nilpotency of `Q`) then `𝓢 = {χ ∈ Irr H | O_{2'}(Q) ⊄ ker χ}` has at
least two members and is coherent for `Ind_H^G`.

This is the single black box of the area (Peterfalvi II App. XII; Sibley 1976, Theorem 1). -/
theorem coherent_of_not_isPGroup [IsSimpleGroup G] {H Q : Subgroup G} {t : G}
    (hFS : FeitSibleyProp) (hTh : ThompsonFrobeniusProp)
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hnot : ¬ IsPGroup 2 Q) :
    2 ≤ (scriptS H (oddPart Q)).card ∧ Work.Coherence.Coherent (scriptS H (oddPart Q)) (indLin H) := by
  have hnil : Group.IsNilpotent Q := isNilpotent_Q hTh h hz (twoPoint_ne_bot h hz)
  have hQ1ne : oddPart Q ≠ ⊥ := fun hbot => hnot ((isPGroup_two_iff hnil).mpr hbot)
  have hD_le_H : twoPoint H t ≤ H := inf_le_left
  refine hFS G H Q (twoPoint H t) (twoPart Q) (oddPart Q)
    h.stronglyEmbedded.1 h.le h.normal hD_le_H h.inf_eq h.sup_eq
    (coprime_card h hz) (isTI_Q h hz) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact twoPart_sup_oddPart hnil
  · exact twoPart_inf_oddPart
  · exact twoPart_commute_oddPart hnil
  · exact coprime_twoPart_oddPart
  · exact isNilpotent_twoPart
  · intro d hd hdne x hx hfix
    exact fpf_on_Q h hz d hd hdne x (oddPart_le Q hx) hfix
  · exact not_isPGroup_two_of_odd (odd_card_oddPart) hQ1ne
  · exact odd_card_twoPoint h.stronglyEmbedded h.not_mem

end Work.ZassenhausTwoGroup
