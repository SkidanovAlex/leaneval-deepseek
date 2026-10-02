import Mathlib
import Submission.Work.LineBundles.Defs
import Submission.Work.Gen.Coh_eq_zero_of_pathComponents

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The component patching for singular cohomology

`Work.LineBundles.Patching n`: a cohomology class `δ ∈ H^n(B;ℤ)` whose restriction to **every**
path component of `B` vanishes is zero.

The subspace `Work.LineBundles.pathComp B c` is, by definition, the set of points `x` whose
`0`-simplex `(TopCat.toSSetObj₀Equiv).symm x` of the singular simplicial set of `B` has `π₀`-class
`c`; the same set is the underlying space of `Work.Gen.pathComp B c`, and
`Work.LineBundles.pathCompIncl B c` is the same continuous map as `Work.Gen.pathCompIncl B c`.  The
statement is therefore (definitionally) the theorem `Work.Gen.Coh_eq_zero_of_pathComponents` proved
in `Submission/Work/Gen/Coh_eq_zero_of_pathComponents.lean`, whose proof is the chain-level
decomposition `C_*(B) = ⊕_c C_*(B_c)`: every singular simplex has path-connected image, hence lies
in a single path component, and the faces of a simplex stay in the same component, so the
componentwise primitives of a cocycle can be glued (`Work.Gen.assemble`) to a global primitive.
-/

namespace Work.LineBundles.Patch

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- The two constructions of the inclusion of a path component agree (definitionally). -/
theorem pathCompIncl_eq_gen (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of B))) :
    Work.Gen.pathCompIncl B c = pathCompIncl B c := rfl

/-- **The component patching** (see `Work.LineBundles.Patching`): a cohomology class in degree `n`
whose restriction to every path component vanishes is zero.

The path component of a `π₀`-class `c` is the subspace
`Work.LineBundles.pathComp B c = {x : B | SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm x) = c}`. -/
theorem patching (n : ℕ) : Work.LineBundles.Patching n := by
  intro B _ δ hδ
  refine Work.Gen.Coh_eq_zero_of_pathComponents (X := B) δ ?_
  intro c
  exact hδ c

end

end Work.LineBundles.Patch
