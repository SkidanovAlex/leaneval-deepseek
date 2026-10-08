import Mathlib
import Submission.Work.Reductions.Defs
import Submission.Work.ThreePoints.Omega
import Submission.Work.Reductions.stronglyEmbedded_subgroupOf
import Submission.Work.Reductions.stronglyEmbedded_involutions_conj
import Submission.Work.Reductions.isSimpleGroup_of_oddCore_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A normal subgroup containing all involutions is transitive on `Ω = G ⧸ H`

This is the auxiliary statement used in the proof of `isSimpleGroup_of_oddCore_eq_bot`
(Peterfalvi I Ch. I §6 Cor. 3); it is exported here as its own module.  The substance is
`Work.Reductions.isPretransitive_of_involutions_aux`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Reductions

theorem isPretransitive_of_involutions {G : Type} [Group G] [Finite G] {H L : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) (hL : L.Normal)
    (hinv : ∀ x : G, orderOf x = 2 → x ∈ L)
    (hproper : ¬ L ≤ H) (heven : Even (Nat.card ↥(H ⊓ L))) :
    ∀ ω : G ⧸ H, ∃ l : L, (l : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = ω :=
  isPretransitive_of_involutions_aux hH hL hinv hproper heven

end Work.Reductions
