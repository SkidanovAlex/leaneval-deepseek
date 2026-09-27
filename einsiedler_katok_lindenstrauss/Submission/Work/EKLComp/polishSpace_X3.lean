import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLComp.X3Topology.PolishOfLocallyCompact

/-!
# `X₃ = SL₃(ℝ)/SL₃(ℤ)` is a Polish space

`X₃` is the quotient of the topological group `G = SL₃(ℝ)` by its discrete subgroup
`Γ₃ = SL₃(ℤ)`.  Here we assemble the fact that `X₃` is Polish, i.e. that its topology is
second countable and admits a complete compatible metric.

The three ingredients are:

* `G` is locally compact: it is the closed subset `det = 1` of the finite dimensional real
  matrix space `(Fin 3 → Fin 3 → ℝ)`, a finite product of copies of `ℝ`;
* `G` is second countable (`Work.EKLContract.Lemmas.SL3Topology`); the quotient of a locally
  compact (resp. second countable) topological group by an arbitrary subgroup is locally compact
  (resp. second countable);
* a second countable, locally compact Hausdorff space is Polish
  (`Work.EKLComp.X3Topology.PolishOfLocallyCompact`).  That proof goes through the one-point
  compactification: for such a space the one-point compactification is compact Hausdorff and
  second countable, hence metrizable by Urysohn's metrization theorem and complete as a compact
  metric space; the space itself is an open subset of it, and open subsets of Polish spaces are
  Polish.  (The Hausdorff hypothesis is the `[T2Space X₃]` assumption below.)
-/

set_option linter.style.haveILetI false

namespace Work.EKLComp

open Work.EKLContract

/-- `SL₃(ℝ)` is locally compact, being the closed locus `det = 1` in the locally compact space of
`3 × 3` real matrices. -/
lemma locallyCompactSpace_SL3' : LocallyCompactSpace SL3 := by
  have : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  exact (isClosed_eq (continuous_id.matrix_det (n := Fin 3) (R := ℝ)) continuous_const).locallyCompactSpace

/-- `X₃ = SL₃(ℝ)/SL₃(ℤ)` is a Polish space. -/
theorem polishSpace_X3 [T2Space Work.EKLContract.X3] : PolishSpace Work.EKLContract.X3 := by
  haveI : LocallyCompactSpace SL3 := locallyCompactSpace_SL3'
  haveI : SecondCountableTopology SL3 := Work.EKLContract.Lemmas.SL3Topology.2
  exact X3Topology.PolishOfLocallyCompact X3

end Work.EKLComp
