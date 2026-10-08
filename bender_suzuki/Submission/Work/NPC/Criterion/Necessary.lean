/-
Area A9, sub-area `Criterion`: the transfer criterion `P* = ⁅P, P⁆` for a normal `p`-complement.

The classical *transfer criterion* (Frobenius; Gorenstein, *Finite Groups*, Chapter 7; Huppert,
*Endliche Gruppen I*, Satz IV.4.7/4.9) states that a finite group `G` has a normal `p`-complement
if and only if for a Sylow `p`-subgroup `P`

    `P ∩ G' = ⁅P, P⁆`    (equivalently `P* = ⁅P, P⁆`, by the focal subgroup theorem
                          `Subgroup.commutator_inf_eq_focalSubgroup`).

This file proves the *easy* (necessary) direction: a normal `p`-complement forces `P* = ⁅P, P⁆`.
The converse is the deep direction; see `Criterion/Reduction.lean` and `HINTS.md` §2.

The route here uses only the already available equivalences of Frobenius' criterion proved in
`Submission.Work.NPC.Frobenius`:

  normal `p`-complement  ⟹  Frobenius' condition (`N_G(Q)/C_G(Q)` a `p`-group)
                         ⟹  the Sylow `P` is conjugacy-closed in `G`
                         ⟹  `P* = ⁅P, P⁆`.
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Fusion
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_of_hasNormalPComplement
import Submission.Work.NPC.Frobenius.conjugacyClosed_sylow_of_hasFrobeniusCondition

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement

namespace Work.NPC.Criterion

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **The transfer criterion is necessary.**  If `G` has a normal `p`-complement then the focal
subgroup of any Sylow `p`-subgroup equals its commutator subgroup — equivalently `P ∩ G' = ⁅P, P⁆`
by the focal subgroup theorem. -/
theorem focalSubgroup_eq_commutator_of_hasNormalPComplement (P : Sylow p G)
    (h : HasNormalPComplement p G) :
    (P : Subgroup G).focalSubgroup = ⁅(P : Subgroup G), (P : Subgroup G)⁆ :=
  focalSubgroup_eq_commutator_of_conjugacyClosed (P := (P : Subgroup G))
    (Frobenius.conjugacyClosed_sylow_of_hasFrobeniusCondition P
      (Frobenius.hasFrobeniusCondition_of_hasNormalPComplement h))

/-- The same statement in the `P ∩ G'` form, via the focal subgroup theorem. -/
theorem commutator_inf_eq_commutator_of_hasNormalPComplement (P : Sylow p G)
    (h : HasNormalPComplement p G) :
    _root_.commutator G ⊓ (P : Subgroup G) = ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
  rw [Subgroup.commutator_inf_eq_focalSubgroup]
  exact focalSubgroup_eq_commutator_of_hasNormalPComplement P h

/-- Conversely, the *conjugacy-closedness* of a Sylow subgroup is necessary for a normal
`p`-complement (this is the same statement as the necessary direction of the criterion, read
through the fusion of `P`). -/
theorem isConj_in_of_hasNormalPComplement (P : Sylow p G) (h : HasNormalPComplement p G)
    (x y : ↥(P : Subgroup G)) (hxy : IsConj (x : G) (y : G)) : IsConj x y :=
  Frobenius.conjugacyClosed_sylow_of_hasFrobeniusCondition P
    (Frobenius.hasFrobeniusCondition_of_hasNormalPComplement h) x y hxy

end Work.NPC.Criterion
