import Mathlib
import Submission.Work.Kunneth.Tensor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Koszul differential on a single summand

`Work.Kunneth.tpD C D n` is the Koszul differential `x ⊗ y ↦ d x ⊗ y + (-1)^p x ⊗ d y`
of the tensor product of two chain complexes of `ℤ`-modules, defined as the sum
`DirectSum.toModule ℤ (tpIdx (n+1)) (tpX C D n) (tpDpq C D n)` of its summands
(`Submission/Work/Kunneth/TensorDefs.lean`).  This file records the resulting
computation rule: restricted to the `pq`-th summand of `tpX C D (n+1)` via the structure
map `tpLof`, the whole differential is the `pq`-th summand `tpDpq C D n pq`.

The `attribute [-instance] AddCommGroup.toIntModule` line is the one required by the
chapter's instance convention (see the header of `TensorDefs.lean`): the two sides of the
identity live in the `isModule`-based `ℤ`-structure, and without removing the generic
structure the two `LinearMap`s are not recognized as having the same scalar structure.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The Koszul differential restricted to a summand is that summand's component.**
Composing the Koszul differential `tpD C D n` with the `pq`-th structure map
`tpLof C D (n+1) pq` of the direct sum returns the `(p,q)`-summand `tpDpq C D n pq` of the
differential.  This is the computation rule making `tpD` usable on generators. -/
theorem tpD_comp_tpLof (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (pq : Work.Kunneth.tpIdx (n + 1)) :
    (Work.Kunneth.tpD C D n).comp (Work.Kunneth.tpLof C D (n + 1) pq)
      = Work.Kunneth.tpDpq C D n pq := by
  ext x
  simp only [LinearMap.comp_apply, tpD, tpLof, DirectSum.toModule_lof]

end

end Work.Kunneth
