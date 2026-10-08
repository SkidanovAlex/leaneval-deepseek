/-
Area A9, sub-area `Fpf`: re-export of the fixed-point-free-automorphism theorem.

The lead's design (`Submission/Work/NOTES_LEAD_ft_npc.md` §2) places the theorem
`Work.NPC.Fpf.isNilpotent_of_fpf_prime` — "a finite **solvable** group with a fixed-point-free
automorphism of prime order is nilpotent" — in this area.  Its definitions (`IsFpf`, `IsInv`, ...)
are in `Submission/Work/NPC/Fpf/Defs.lean`; the lemmas F1–F9 are proved in
`Submission/Work/Frobenius/Fpf/` (area A8).  This module re-exports the main theorem under the name
of the lead's spec so that consumers can use either.
-/
import Submission.Work.Frobenius.Fpf.isNilpotent_of_fpf_prime
import Submission.Work.Frobenius.Fpf.le_centralizer_of_fpf
import Submission.Work.Frobenius.Fpf.exists_characteristic_abelian_pGroup
import Submission.Work.Frobenius.Fpf.exists_invariant_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Fpf

/-- **F9 (lead's §2):** a finite solvable group with a fixed-point-free automorphism of prime order
is nilpotent. -/
alias isNilpotent_of_fpf_prime := Work.Frobenius.Fpf.isNilpotent_of_fpf_prime

/-- **F7 (KEY):** an `α`-invariant subgroup `Q` whose order is coprime to the order of an
`α`-invariant normal abelian subgroup `V` centralises `V`. -/
alias le_centralizer_of_fpf := Work.Frobenius.Fpf.le_centralizer_of_fpf

/-- **F8:** a nontrivial finite solvable group has a nontrivial characteristic abelian
`p`-subgroup. -/
alias exists_characteristic_abelian_pGroup := Work.Frobenius.Fpf.exists_characteristic_abelian_pGroup

/-- **F6:** an `α`-invariant Sylow subgroup exists. -/
alias exists_isInv_sylow := Work.Frobenius.Fpf.exists_invariant_sylow

end Work.NPC.Fpf
