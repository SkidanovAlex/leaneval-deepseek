import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Winding.winding_zero_of_unbounded_component
import Submission.Lib.Unif2.Commons.Topology.Winding.hasArg_homotopy_invariant
import Submission.Lib.Unif2.Work.Mori.not_hasArg_circle
import Submission.Lib.Unif2.Work.Mori.ArgumentPeriod
import Submission.Lib.Unif2.Work.Mori.WindingCircle

/-!
# Tools for the PLANAR-SC area

Convenience module re-exporting the (sorry-free, locally building) topology/harmonic-analysis tools
used by the lemmas of `Submission/Work/PlanarSC/`.

* `Commons.Topology.Winding.{HasArg, winding_zero_of_unbounded_component, hasArg_homotopy_invariant}`
  — the argument (winding) of a closed curve, its vanishing on the unbounded component of the
  complement of the curve, and its invariance under zero-free homotopies;
* `Work.Mori.not_hasArg_circle{,_of_norm_sub_lt}` — a round circle winds once around its centre;
* `Work.Mori.argumentPeriodHom{,_ne_zero,_ne_zero_of_mem_ball}` — the winding homomorphism
  `π₁(U,u) →+ ℝ` of a plane domain and its non-triviality for a circle about an exterior point;
* `Work.Mori.HasWindingCircle{,_of_isBounded_compl,_of_isPolar_compl}` — "`U` contains a circle about
  a point it misses".
-/
