/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Karrass--Magnus--Solitar torsion theorem

`Work.OROneRel.KMSTorsionAt r` (`r : FreeGroup α` arbitrary): for `r = u ^ l` with `1 ≤ l` and `u`
not a proper power, the class of `u` in `⟨α | r⟩` has order exactly `l` and every element of finite
order in `⟨α | r⟩` is conjugate to a power of that class.

The proof is the root-tracked induction `Work.OROneRel.kmsRoot_all`
(`Submission/Work/OROneRel/kmsRoot_all.lean`), whose two steps are

* the exponent-sum-zero Magnus rewriting (`Work.OROneRel.kmsRoot_epsZero`, from
  `magnus_step_root_eps_zero` in the self-contained module `magnus_step_root_eps_zero.lean`), and
* Magnus's embedding of the no-zero-exponent-sum case (`Work.OROneRel.kmsRoot_of_subst`), routed
  through the amalgam `⟨α | u^l⟩ ∗_ℤ ℤ` (`subst_pushout_equiv`, `substHom_injective`) and the
  star-tree conjugacy transfer (`pushoutI_conj_transfer`).

The earlier route through the root-tracked Magnus step `magnus_step_root` (which needed the
`Z`-domain/window machinery) has been retired: this module no longer imports it.
-/
import Mathlib
import Submission.Work.OROneRel.KMSDefs
import Submission.Work.OROneRel.kmsRoot_all

namespace Work.OROneRel

universe u

/-- **The Karrass--Magnus--Solitar torsion theorem** for one-relator groups, in the form required by
node `N2`: for `r = u ^ l` with `1 ≤ l` and `u` not a proper power, the class of `u` in `⟨α | r⟩`
has order exactly `l`, and every element of finite order in `⟨α | r⟩` is conjugate to a power of
that class. -/
theorem kms_torsion_at {α : Type u} (r : FreeGroup α) : Work.OROneRel.KMSTorsionAt r := by
  intro u l hl hr hu
  subst hr
  exact kmsRoot_all (relatorNorm u) u l hl hu le_rfl

end Work.OROneRel
