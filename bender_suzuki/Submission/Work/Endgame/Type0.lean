import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.isSimpleBenderGroup_of_benderConclusion
import Submission.Work.Endgame.not_isStronglyEmbedded_of_not_hasFourGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The endgame for groups in `Type` (universe `0`)

Theorem B, Brauer–Suzuki and the model facts prove the challenge for every group in `Type`.  The
case split is on the 2-rank:

* `HasFourGroup G`: Theorem B applies (`hB G ⟨hfour, ⟨M, hM⟩⟩`) and its conclusion
  `BenderConclusion G` yields `IsSimpleBenderGroup G`
  (`isSimpleBenderGroup_of_benderConclusion`, using `Even (Nat.card G)` from the four-group);
* `¬ HasFourGroup G`: Brauer–Suzuki makes an involution central, which is impossible in a simple
  group of even order with a proper subgroup of even order
  (`not_isStronglyEmbedded_of_not_hasFourGroup`).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.Endgame

theorem isSimpleBenderGroup_of_type0 (hB : TheoremB) (hBrSz : BrauerSuzukiProp)
    (hMod : ModelFactsProp) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (M : Subgroup G) (hM : IsStronglyEmbedded M) : IsSimpleBenderGroup G := by
  by_cases hfour : HasFourGroup G
  · exact isSimpleBenderGroup_of_benderConclusion hMod (hB G ⟨hfour, ⟨M, hM⟩⟩)
      (HasFourGroup.even_natCard hfour)
  · exact absurd hM (not_isStronglyEmbedded_of_not_hasFourGroup hBrSz hfour M)

end Work.Endgame
