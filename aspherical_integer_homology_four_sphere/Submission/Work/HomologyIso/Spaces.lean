/-
# `HomologyIso/`: the space-level inputs of the per-cusp decomposition

This file collects the two topological ingredients through which the *geometry* enters the
computation of the first two slots of the Mayer–Vietoris sequence of `M̂ = A ∪ B`:

* `Work.HomologyIso.intHomology_iso_of_homotopyEquiv` — a homotopy equivalence of spaces induces
  an isomorphism on integral homology in every degree;
* the homotopy equivalences of `Work.Space.Split` (`A ∩ B ≃ₕ ⊔_v ∂[-1,1]² × T²_v`,
  `B ≃ₕ ⊔_v T²_v`), which turn the two slots into finite disjoint unions, so that
  `Work.HomologyIso.intHomology_sigma` and the per-cusp computations apply.

## Why this is needed

`H_k(A ∩ B)` and `H_k(B)` are the homology of *spaces*, while the computations of the
Ratcliffe–Tschantz data are those of five cusps.  The homotopy equivalences

```
A ∩ B  ≃ₕ  ⊔_v (∂[-1,1]² × T²_v),        B  ≃ₕ  ⊔_v T²_v,
```

of `Work.Space.Split.retrAB_homotopyEquiv` and `Work.Space.Split.retrB_homotopyEquiv` are the
only place where the topology of `M̂` is used: they reduce the two slots to a *finite* disjoint
union of cusp pieces, which `Work.HomologyIso.intHomology_sigma` splits off.
-/
import Submission.Work.HomologyIso.Main
import Submission.Work.Homology.All
import Submission.Work.Cohomology.localHomology
import Submission.Work.Space.Split.retrAB_homotopyEquiv
import Submission.Work.Space.Split.retrB_homotopyEquiv
import Submission.Work.Space.Split.retrA_homotopyEquiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.HomologyIso

noncomputable section

variable [rt : Work.Space.RTData]

/-- **A homotopy equivalence induces an isomorphism on integral homology**, with the map induced
by its forward map (so this is a statement about a *specific* isomorphism, not only about
nonemptiness). -/
theorem intHomology_iso_of_homotopyEquiv {X Y : TopCat} (e : ContinuousMap.HomotopyEquiv X Y)
    (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k X ≅ LeanEval.Topology.intHomology k Y) := by
  haveI := Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv e k
  exact ⟨asIso (homologyMap (Work.Cohomology.chainMap ℤ X Y (TopCat.ofHom e.toFun)) k)⟩

/-- **`H_k(A) ≅ H_k(M̄)`** — the thickened hyperbolic piece `A` is homotopy equivalent to the
compact piece `M̄` (`Work.Space.Split.retrA_homotopyEquiv`). -/
theorem homology_A_iso (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k (TopCat.of ↥(Aset (rt := rt))) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar)) := by
  obtain ⟨e⟩ := Work.Space.Split.retrA_homotopyEquiv rt.core
  obtain ⟨h⟩ := intHomology_iso_of_homotopyEquiv
    (X := TopCat.of ↥(Aset (rt := rt))) (Y := TopCat.of rt.core.Mbar) e k
  exact ⟨h⟩

end

end Work.HomologyIso
