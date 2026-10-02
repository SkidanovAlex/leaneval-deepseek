import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.Source

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the first step of the source construction

`Work.PTGeometric.ConcreteLastMileSource` asks for the **ambient collapse-end data** of the
null-homotopy of the genuine collapse class of a multiple of the family (`LastMile.lean`), together
with the orientation datum of the situation.  The construction of that source has two halves:

1. *the smooth defining function of the core preimage*: if `Z` is the preimage of the core under the
   null-homotopy (a closed subset of the source on which the null-homotopy takes values in the
   manifold part of the Thom space), then `{f ≤ ε}` for a smooth `f ≥ 0` with `f ⁻¹' {0} = Z` is a
   compact neighbourhood of `Z` on which the ambient coordinates are defined, and `ε` can be chosen a
   regular value of `f` so that the boundary `{f = ε}` is smooth;
2. *the manifold structure of the sublevel set*, which is where the differential-topology input the
   workspace lacks is needed — see `README.md` §17.

The first step is Mathlib: `exists_contMDiff_zero_iff_one_iff_of_isClosed` (with `s = Z`, `t = ∅`)
gives a smooth `f` with `range f ⊆ [0,1]` and `f x = 0 ↔ x ∈ Z`.  This file records it in the form
the construction consumes, so that the residual of the last mile is exactly the *manifold structure*.

## Main results

* `Work.PTGeometric.exists_contMDiff_eq_zero_iff_closed`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The smooth defining function of a closed set in a compact smooth manifold with boundary.**

For a closed subset `Z` of a compact `T2` smooth `(N)`-manifold `M` with boundary (modelled on the
half-space), there is a `C^∞` function `f : M → ℝ` with `0 ≤ f`, `f ≤ 1`, and `f x = 0 ↔ x ∈ Z`.

In the source construction of the last mile, `Z` is the preimage of the core of the Thom space under
the null-homotopy, and `M ↦ {f ≤ ε}` is the compact smooth neighbourhood of `Z` on which the ambient
coordinates of the collapse are defined. -/
theorem exists_contMDiff_eq_zero_iff_closed (N : ℕ) [NeZero N] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace N) M] [IsManifold (𝓡∂ N) ∞ M]
    [CompactSpace M] [T2Space M] (Z : Set M) (hZ : IsClosed Z) :
    ∃ f : M → ℝ, ContMDiff (𝓡∂ N) (𝓘(ℝ, ℝ)) ∞ f ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧ (∀ x, f x = 0 ↔ x ∈ Z) := by
  haveI : SigmaCompactSpace M := CompactSpace.sigmaCompact
  obtain ⟨f, hf, hr, h0, -⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (𝓡∂ N) hZ isClosed_empty disjoint_bot_right
  exact ⟨f, hf, fun x => (hr (Set.mem_range_self x)).1,
    fun x => (hr (Set.mem_range_self x)).2, fun x => (h0 x).symm⟩

end

end Work.PTGeometric
