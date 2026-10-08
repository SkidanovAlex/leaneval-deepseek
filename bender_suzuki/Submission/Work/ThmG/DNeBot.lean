import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.ThmG.twoPoint_ne_bot_of_not_zassenhaus

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D ≠ 1`: Ch. II §4 Prop. 2 (b) with p. 236, proved in this area

In the split rank-one situation, `G` is not a Zassenhaus group precisely when `V = C_D(t) ≠ 1`;
in particular `D = H ∩ Hᵗ ≠ 1` (this is what the degree count uses: `|D| ≥ 3`).

The proof is elementary and needs no structural input: an element of odd prime order fixing three
distinct points of `Ω = G ⧸ H` can be conjugated into `D`, and `D = ⊥` would kill it (the
reduction to odd prime order uses that an involution lies in exactly one conjugate of `H`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical
open Submission.Blueprint

namespace Work.ThmG

/-- Ch. II §4 Prop. 2 (b) with p. 236, in the form of the second field of `RankOneStructure`. -/
theorem dNeBotProp : DNeBotProp := by
  intro G _ _ H Q t hh
  obtain ⟨-, -, hsplit, hz, -⟩ := hh
  exact twoPoint_ne_bot_of_not_zassenhaus hsplit hz

/-- `rankOneStructure_of` with field 2 discharged internally: seven external inputs suffice. -/
theorem rankOneStructure_of_seven (h1 : KNeOneProp) (h3 : CoprimeDQProp) (h4 : FpfOddPartProp)
    (h5 : ExistsLinearProp) (h6 : IndTwoProp) (h7 : DegreeProp) (h8 : VanishesOffProp) :
    RankOneStructureProp :=
  rankOneStructure_of h1 dNeBotProp h3 h4 h5 h6 h7 h8

end Work.ThmG
