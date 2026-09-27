import Mathlib
import Submission.Work.EQ.DefsCore

/-!
# `H0` and its components are second countable

`ChainData = (ℤ → ℂ × ℂ) × ℂ × ℂ` is a *countable* product of second countable spaces (the index
type `ℤ` is countable), hence second countable; consequently `0H = H0 a h`, as a subspace, and every
connected component of it is second countable, with no hypotheses at all.

This supplies the `SecondCountableTopology` instance required by
`Work.EQ.exists_uniformizing_cover` (via `Work.EQ.exists_chartedSpace_of_isLocalHomeomorph`) and,
combined with `Work.EQ.countable_regular_values`, the countability of the regular values
(Rychlik's Theorem 11, step (141)).
-/

namespace Work.EQ

open Filter _root_.Topology

theorem H0_secondCountable {a : ℝ} {h : ℂ → ℂ} : SecondCountableTopology (H0 a h) :=
  inferInstance

theorem H0_component_secondCountable {a : ℝ} {h : ℂ → ℂ} (P : H0 a h) :
    SecondCountableTopology ↥(connectedComponent P) :=
  inferInstance

end Work.EQ
