import Mathlib
import Submission.Work.Stems.Collar.Defs
import Submission.Work.Stems.Collar.collar_collapse

/-!
# The double collar collapses onto the identity, at the other basepoint

`Submission.Work.Stems.Collar.collar_collapse` proves that for a path `p : Path x y` the
composite `collar p.symm ∘ collar p` is homotopic to the identity of `Ω^M X x`, i.e. the
collar maps exhibit a homotopy equivalence between the based `M`-cubes at `x` and at `y`.

The present lemma is the mirror statement at the basepoint `y`: the composite
`collar p ∘ collar p.symm` is homotopic to the identity of `Ω^M X y`.

There is nothing to reprove: the collar construction is symmetric in its endpoints, so the
statement is exactly `collar_collapse` applied to the reversed path `p.symm : Path y x`,
together with the trivial identification `(p.symm).symm = p`.
-/

open scoped Topology unitInterval Topology.Homotopy
open Set Function

namespace Work.Stems.Collar

theorem collar_collapse_symm {M : Type*} [Fintype M] [Nonempty M] {X : Type*}
    [TopologicalSpace X] {x y : X} (p : Path x y) :
    Nonempty (ContinuousMap.Homotopy
      ((Work.Stems.Collar.collar p).comp (Work.Stems.Collar.collar p.symm))
      (ContinuousMap.id (GenLoop M X y))) := by
  -- Reverse the path: `collar_collapse (p.symm)` lives over the basepoint `y` and concerns
  -- `collar (p.symm).symm ∘ collar p.symm`; rewriting `(p.symm).symm` to `p` gives the goal.
  simpa [Path.symm_symm] using
    (Work.Stems.Collar.collar_collapse (M := M) (X := X) p.symm)

end Work.Stems.Collar
