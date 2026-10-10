import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Defs.Induced
import Submission.Work.SSGRoute.PT.shapiro_H2_lift_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Shapiro lift of a `2`-cocycle is a `2`-cocycle

For a group `G`, a subgroup `U ≤ G` and a `U`-module `M`, `Submission/Work/SSGRoute/PT/shapiro_H2_lift_defs.lean`
defines the Shapiro lift of a `2`-cochain `a : U × U → M` to a `2`-cochain on `G` with values in
the coinduced module `Coind_U^G M`:

  `shapiroLift U a (g, h) x = coord U x • a (A g (xU), A h (g⁻¹ • xU))`.

This file proves that it is a `2`-cocycle: the cocycle condition on `U` transports to the cocycle
condition on `G` because the `G`-action on `Coind_U^G M` turns the twist by `A g (xU)` into the
`U`-action, and the `U`-coordinates are multiplicative (`A_mul'`).  Nothing about continuity is
needed: the statement is about the *algebraic* cocycles `Work.GroupCohomology.Z2`.
-/

namespace Work.SSGRoute.PT

open scoped Classical

/-- **The Shapiro lift preserves the `2`-cocycle condition.**  If `a : U × U → M` is a `2`-cocycle
on `U` (in particular, a continuous one), then its Shapiro lift is a `2`-cocycle on `G` with values
in `Coind_U^G M`. -/
theorem shapiroLift_mem_Z2 {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (a : U × U → M) (ha : a ∈ Work.AbsoluteKummer.Z2 U M) :
    Work.SSGRoute.PT.shapiroLift U a ∈ Work.GroupCohomology.Z2 G (Work.SSGRoute.PT.Coind G U M) := by
  rw [Work.GroupCohomology.mem_Z2_iff]
  intro g h k
  have haZ : a ∈ Work.GroupCohomology.Z2 U M := (AddSubgroup.mem_inf.mp ha).1
  have Hcocy := ((Work.GroupCohomology.mem_Z2_iff U M) a).mp haZ
  apply Subtype.ext
  funext x
  simp only [AddSubgroup.coe_add, Pi.add_apply]
  rw [shapiroLift_apply, shapiroLift_apply, shapiroLift_smul_apply, shapiroLift_apply]
  rw [A_mul' U g h (x : G ⧸ U), mul_inv_rev, mul_smul, A_mul' U h k (g⁻¹ • (x : G ⧸ U))]
  rw [← smul_add,
    Hcocy (Shapiro.A 0 G U g (x : G ⧸ U)) (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)))
      (Shapiro.A 0 G U k (h⁻¹ • g⁻¹ • (x : G ⧸ U))),
    smul_add, mul_smul]

end Work.SSGRoute.PT
