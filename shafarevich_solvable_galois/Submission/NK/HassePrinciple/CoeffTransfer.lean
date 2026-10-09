/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The coefficient-ring transfer for `H²` (a building block of the limit passage)

Umbrella development: `Submission/Work/HassePrinciple/` (README §13.5, item (h) of §13.3).

The limit passage compares the level cohomology of this chapter, which is computed over the
coefficient ring `Coeff p = ULift (ZMod p)` (`NK.BrauerHasse.H2`), with the `μ_p`-coefficient
cohomology used by the Kummer layer of the chapter and by the sibling area
`Submission/Work/BrauerTwist/`, which is computed over `CoeffInt = ULift ℤ`.  The same
`Gal(L/K)`-module (a `p`-torsion module such as `ZMod p`, or the group `μ_p(L)`) has both module
structures, and the two cochain complexes have the same carriers and the same differentials.

This module records the resulting **vanishing transfer**: for a 2-cocycle `f` with values in a
group `V` carrying both a `k`-module and a `k'`-module structure compatible with the same
`G`-action, the class of `f` in `H²(G, V)` is zero over `k` if and only if it is zero over `k'`.
The proof uses only Mathlib's low-degree description: `H2π_eq_zero_iff` identifies the vanishing of
the class with the *ring-agnostic* cocycle condition `IsCoboundary₂ f`
(`isCoboundary₂_of_mem_coboundaries₂` and `coboundariesOfIsCoboundary₂`, whose statement involves
only `[AddCommGroup V] [SMul G V]`).

This is the degree-two analogue of the degree-one transfer
`NK.HassePrinciple.subsingleton_groupCohomology_one_of_mulCoboundary`
(`subsingleton_classGroupRep_one.lean`), which is what made `H¹` of the idèle class group available
in the chapter's coefficient ring.
-/

import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation

set_option autoImplicit false

namespace NK.HassePrinciple

/-- **The coefficient-ring transfer for `H²`.**  For a 2-cocycle `f : G × G → V` with values in
an abelian group `V` that carries both a `k`-module and a `k'`-module structure compatible with
the same `G`-action, the class of `f` in `H²(G, V)` is zero over `k` if and only if it is zero
over `k'`.

The mathematical content is that `H²` is the quotient of the 2-cocycles by the 2-coboundaries, and
both conditions (`IsCocycle₂`, `IsCoboundary₂`) mention only the `G`-action and the additive
structure. -/
theorem H2π_eq_zero_transfer {k k' G V : Type} [CommRing k] [CommRing k'] [Group G]
    [AddCommGroup V] [Module k V] [Module k' V] [DistribMulAction G V]
    [SMulCommClass G k V] [SMulCommClass G k' V]
    (f : G × G → V) (hf : groupCohomology.IsCocycle₂ f) :
    (groupCohomology.H2π (Rep.ofDistribMulAction k G V)
        (groupCohomology.cocyclesOfIsCocycle₂ hf) = 0) ↔
      (groupCohomology.H2π (Rep.ofDistribMulAction k' G V)
        (groupCohomology.cocyclesOfIsCocycle₂ hf) = 0) := by
  rw [groupCohomology.H2π_eq_zero_iff, groupCohomology.H2π_eq_zero_iff]
  constructor
  · intro h
    exact (groupCohomology.coboundariesOfIsCoboundary₂
      (groupCohomology.isCoboundary₂_of_mem_coboundaries₂ f h)).2
  · intro h
    exact (groupCohomology.coboundariesOfIsCoboundary₂
      (groupCohomology.isCoboundary₂_of_mem_coboundaries₂ f h)).2

end NK.HassePrinciple
