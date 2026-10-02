import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Gen

/-! ## The path components of a space, as subspaces

The component of a point `x : X` is the subspace of points whose `0`-simplex lies in the same
connected component of the singular simplicial set.  For the singular simplicial set of a space
this coincides with the usual path component.

This module only contains the definitions, so that the module `Submission/Work/Gen/Coh_eq_zero_of_pathComponents.lean`
(and the other consumers) can use them without a circular import. -/

/-- **The path component of a point, as a topological space** (the subspace of `X` consisting of
the points whose `0`-simplex has the given `π₀`-class). -/
noncomputable def pathComp (X : Type) [TopologicalSpace X]
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) : TopCat :=
  TopCat.of {x : X // SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x) = c}

/-- The inclusion of a path component into the ambient space. -/
noncomputable def pathCompIncl (X : Type) [TopologicalSpace X]
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) : C(pathComp X c, TopCat.of X) :=
  ⟨fun x => x.1, continuous_subtype_val⟩

/-- The point of a path component given by a point of the ambient space lying in it. -/
noncomputable def pathCompPt (X : Type) [TopologicalSpace X]
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) (x : X)
    (hx : SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x) = c) :
    (pathComp X c : Type) := ⟨x, hx⟩

end Work.Gen
