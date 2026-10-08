import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.glauberman_exists_fixed

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.Coprime

/-- **Coprime action, solvable case (existence of an invariant Sylow subgroup).**

Let `A` act by automorphisms on the finite group `G`, with `Nat.card A` coprime to `Nat.card G`,
and suppose that `A` or `G` is solvable.  Then for every prime `p` there is a Sylow `p`-subgroup
of `G` that is invariant under the action of `A`.

This is the direct application of Glauberman's fixed point lemma
(`Work.Coprime.glauberman_exists_fixed`) to the `G`-set `Sylow p G`, on which `G` acts by
conjugation (transitively, by Sylow's theorem) and `A` acts by transport of structure; an
`A`-fixed point of this set is exactly an `A`-invariant Sylow `p`-subgroup. -/
theorem exists_invariant_sylow_of_solvable (A : Type*) {G : Type*} [Group A] [Group G] [Finite A]
    [Finite G] [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G) (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p G, ∀ a : A, a • P = P := by
  refine Work.Coprime.glauberman_exists_fixed A G (Sylow p G) hcop hsol ?_ ?_
  · -- compatibility of the `A`-action on `Sylow p G` with the conjugation action of `G`
    intro a g P
    ext x
    simp only [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.inv_apply,
      MulAut.conj_symm_apply, smul_mul', smul_inv', inv_smul_smul]
  · -- `G` acts transitively on its Sylow `p`-subgroups (Sylow's theorem)
    intro P Q
    exact MulAction.exists_smul_eq G P Q

end Work.Coprime
