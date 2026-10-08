import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.exists_invariant_sylow_of_solvable

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.Coprime

/-- **Coprime action: existence of an `A`-invariant Sylow `p`-subgroup.**

Let the finite group `A` act by automorphisms on the finite group `G` (via a
`MulDistribMulAction`), with `Nat.card A` coprime to `Nat.card G`, and suppose that `A` or `G` is
solvable.  Then for every prime `p` there exists a Sylow `p`-subgroup `P` of `G` which is fixed by
the action of `A` (i.e. `a • P = P` for all `a : A`).

This is the direct application of Glauberman's fixed-point lemma to the transitive `G`-set
`Sylow p G`; see `Work.Coprime.exists_invariant_sylow_of_solvable` for the proof. -/
theorem exists_invariant_sylow (A : Type*) {G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G) (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p G, ∀ a : A, a • P = P :=
  exists_invariant_sylow_of_solvable A hcop hsol p

end Work.Coprime
