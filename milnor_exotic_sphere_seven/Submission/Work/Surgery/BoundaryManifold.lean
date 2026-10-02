import Submission.Work.Surgery.BoundaryInstances
import Submission.Work.Surgery.bnd_incl_contMDiff
import Submission.Work.Surgery.bnd_diffeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The boundary manifold: functoriality

This file re-exports the instances of `Submission/Work/Surgery/BoundaryInstances.lean` together
with the delegated functoriality statements:

* `Work.Surgery.bnd_incl_contMDiff` — the inclusion `∂M → M` of the boundary is smooth;
* `Work.Surgery.bnd_diffeomorph` — a diffeomorphism of manifolds with boundary restricts to a
  diffeomorphism of their boundaries.

Import `Submission.Work.Surgery.Boundary` for the chart construction itself, and
`Submission.Work.Surgery.BoundaryInstances` for the instances alone (no delegated dependencies).
-/
