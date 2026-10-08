import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.exists_invariant_sylow_ge_of_solvable

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An `A`-invariant `p`-subgroup lies in an `A`-invariant Sylow

The unrestricted form of this statement (without the solvability hypothesis) is *not* provable
here: by Schur–Zassenhaus / the Glauberman fixed-point lemma it is equivalent to the conjugacy part
of Schur–Zassenhaus for the coprime pair `(A, G)`, which in general needs `A` or `G` solvable
(otherwise it is Feit–Thompson itself, the target of this project).  This file therefore states the
version with `hsol : Group.IsSolvable A ∨ Group.IsSolvable G` (as the blueprint allows: it is
always available in a minimal counterexample), proved from
`Work.Coprime.exists_invariant_sylow_ge_of_solvable`.
-/
open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Coprime

/-- Every `A`-invariant `p`-subgroup of `G` is contained in an `A`-invariant Sylow `p`-subgroup. -/
theorem exists_invariant_sylow_ge (A : Type*) {G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G) (p : ℕ) [Fact p.Prime]
    (Q : Subgroup G) [FT.IsInvariant A Q] (hQ : IsPGroup p Q) :
    ∃ P : Sylow p G, Q ≤ P ∧ ∀ a : A, a • P = P :=
  exists_invariant_sylow_ge_of_solvable A hcop hsol p Q hQ

end Work.Coprime
