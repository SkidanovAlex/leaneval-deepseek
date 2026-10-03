import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Winding.winding_zero_of_unbounded_component
import Submission.Lib.Unif2.Commons.Topology.Winding.hasArg_homotopy_invariant
import Submission.Lib.Unif2.Commons.Topology.Jordan.plane_separation
import Submission.Lib.Unif2.Commons.Topology.Jordan.bounded_component_exists
import Submission.Lib.Unif2.Commons.Topology.Jordan.at_most_one_bounded_component
import Submission.Lib.Unif2.Work.Mori.not_hasArg_circle
import Submission.Lib.Unif2.Work.SimplyConnected.Basic
import Submission.Lib.Unif2.Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton
import Submission.Lib.Unif2.Work.Mori.holomorphicOnX_opens_sub_const
import Submission.Lib.Unif2.Commons.Topology.Connected.frontier_component_compl_range

/-!
# Tools for the HornSC area (`Work.HornSC.sc_compl_component_unbounded`)

Convenience re-export of the (sorry-free, locally building) planarity / winding / holomorphic-log
toolbox used by the lemmas of `Submission/Work/HornSC/`:

* `Commons.Topology.Winding.HasArg` — "the closed curve `t ↦ f t - p` admits a continuous
  `1`-periodic argument function", i.e. has winding number zero about `p`;
* `Commons.Topology.Winding.hasArg_homotopy_invariant` — invariance of that vanishing under
  nowhere-zero homotopies;
* `Commons.Topology.Winding.winding_zero_of_unbounded_component` — a curve does not wind around a
  point of the *unbounded* component of the complement of its range;
* `Commons.Topology.Jordan.plane_separation` (and the "at most one bounded component" companion) —
  the Jordan separation theorem for injective circle maps;
* `Work.Mori.not_hasArg_circle{,_of_norm_sub_lt}` — a round circle winds once around its centre;
* `Work.SC.subsingleton_hom_additive_fundamentalGroup_of_simplyConnected` and
  `Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton` — a nowhere-zero holomorphic function on a
  simply connected domain has trivial argument monodromy (so every closed curve in the domain has
  zero winding about every point it misses).
-/
