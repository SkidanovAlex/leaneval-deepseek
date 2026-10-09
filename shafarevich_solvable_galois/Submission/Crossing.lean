/-
Copyright (c) 2025. All rights reserved.

# Crossing a realization with an abelian group

`Submission/Work/FieldTheory/Crossing/` proves that realizability over `ℚ` is closed under
products with finite abelian groups: for a finite abelian group `A` and a finite group `G`,

* `Work.FieldTheory.Crossing.realizableOver_prod_commGroup` :
  `RealizableOver ℚ G → RealizableOver ℚ (G × A)`.

The proof builds, for a realization `L/ℚ` of `G` and every `n ≠ 0`, a cyclic extension `M/ℚ` of
degree `n` with `L ⊓ M = ⊥` (the degree-`n` subfield of `ℚ(ζ_p)` for a suitable prime `p ≡ 1 mod n`,
using that `ℚ(ζ_p) ⊓ ℚ(ζ_q) = ⊥` for `p ≠ q` and that only finitely many primes give a subfield
meeting `L` nontrivially), so that `L ⊔ M` realizes `G × ZMod n`; the general abelian `A` is then
handled by the structure theorem for finite abelian groups.

Here we

* restate that closure result in the `Submission` namespace, and
* record a **provable special case of the deep input** `ElementaryAbelianKernelStep`: if the
  elementary abelian normal subgroup `A` is a *direct factor* of `G`, then `G` is realizable as
  soon as `G ⧸ A` is (because then `G ≃* A × (G ⧸ A)`).

The remaining, genuinely hard case of `ElementaryAbelianKernelStep` is that of a *non-split*
extension: `A ⋊ (G ⧸ A) ≇ A × (G ⧸ A)`.  Even the split case with a nontrivial action is hard
(`S₃ = C₃ ⋊ C₂` is not a direct product, and its realization needs an embedding-problem argument).
-/
import Mathlib
import Submission.Shafarevich
import Submission.Work.FieldTheory.Crossing.Crossing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

open scoped Classical

/-- Realizability over `ℚ` is closed under products with finite abelian groups: if `G` is
realizable over `ℚ` and `A` is finite abelian, then so is `G × A`. -/
theorem RealizableOver.prod_commGroup {G : Type} [Group G] (A : Type) [CommGroup A] [Finite A]
    (h : RealizableOver ℚ G) : RealizableOver ℚ (G × A) :=
  Work.FieldTheory.Crossing.realizableOver_prod_commGroup G A h

/-- **A special case of `realizable_of_elementary_abelian_kernel`**: if the elementary abelian
normal subgroup `A ◁ G` is a direct factor of `G` (i.e. `G ≃* A × (G ⧸ A)`), then `G` is
realizable over `ℚ` as soon as `G ⧸ A` is, by crossing the realization of `G ⧸ A` with the
abelian group `A`.

This covers, for instance, all abelian `G`, and all `G` of the shape `A × H` with `G ⧸ A ≅ H`
realizable. -/
theorem realizable_of_elementary_abelian_kernel_direct_factor (G : Type) [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (hcomm : IsMulCommutative A)
    (e : G ≃* (A × (G ⧸ A))) (hquot : RealizableOver ℚ (G ⧸ A)) : RealizableOver ℚ G := by
  letI : CommGroup A := { mul_comm := hcomm.is_comm.comm }
  have h1 : RealizableOver ℚ ((G ⧸ A) × A) := RealizableOver.prod_commGroup A hquot
  exact h1.of_mulEquiv (MulEquiv.prodComm.trans e.symm)

end Submission
