import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.setup
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.chi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Reading `mfderiv` in a chart of the source

The chart bookkeeping needed to apply Sard's theorem chartwise in `M` (item 3 of the plan) and to
pass between `IsSubmersionAt` and surjectivity of `mfderiv` at interior points (items 1 and 2).

## Proved here

`surjective_mfderiv_extChartAt`: the extended chart at a point of its source has *surjective*
manifold derivative — immediate from `isInvertible_mfderiv_extChartAt`.

## Proved here

* `surjective_mfderiv_extChartAt`: the extended chart at a point of its source has *surjective*
  manifold derivative — immediate from `isInvertible_mfderiv_extChartAt`.
* `surjective_mfderiv_iff_surjective_fderiv_extChartAt`: at an *interior* point `x`, surjectivity of
  `mfderiv I (𝓡 k) f x` is equivalent to surjectivity of the ordinary derivative of the chart
  expression `z ↦ f ((extChartAt I x).symm z)` at `z = (extChartAt I x) x`.  This is the bridge used
  to apply Sard's theorem chartwise in `M` (item 3) and to pass between `IsSubmersionAt` and
  surjectivity of `mfderiv` at interior points (items 1 and 2).

Two formalisation traps (worth knowing before touching this file):

1. `HasMFDerivAt` unfolds to a *conjunction* — `ContinuousAt f x ∧ HasFDerivWithinAt
   (writtenInExtChartAt I I' x f) f' (range I) ((extChartAt I x) x)` — and the unfolding is
   transparency-blocked in `MFDeriv/Basic.lean`; the proof below therefore sets
   `set_option backward.isDefEq.respectTransparency false` and uses `unfold HasMFDerivAt at h`
   followed by `exact h.2`.
2. `mfderiv`'s definition carries a classical `ite` guard with `TangentSpace`-annotated branches, so
   it should *not* be unfolded here; going through `MDifferentiableAt.hasMFDerivAt` avoids it
   entirely.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

/-- The extended chart at a point of its source has *surjective* manifold derivative (its `mfderiv`
is invertible, `isInvertible_mfderiv_extChartAt`). -/
theorem surjective_mfderiv_extChartAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {x : M} (hx : x ∈ (extChartAt I x).source) :
    Function.Surjective (mfderiv I 𝓘(ℝ, E) (⇑(extChartAt I x)) x) :=
  (isInvertible_mfderiv_extChartAt (I := I) hx).surjective

set_option backward.isDefEq.respectTransparency false

/-- **`mfderiv` read in the preferred chart of the source.**  (Statement and proof sketch; see the
module docstring for what remains.) -/
theorem surjective_mfderiv_iff_surjective_fderiv_extChartAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {k : ℕ}
    {f : M → EuclideanSpace ℝ (Fin k)} {x : M} (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I (𝓡 k) f x) :
    Function.Surjective (mfderiv I (𝓡 k) f x) ↔
      Function.Surjective
        (fderiv ℝ (fun z : E => f ((extChartAt I x).symm z)) ((extChartAt I x) x)) := by
  have hmem : (extChartAt I x) x ∈ interior (range I) := by
    rw [ModelWithCorners.isInteriorPoint_iff] at hx
    exact interior_mono (extChartAt_target_subset_range (I := I) x) hx
  have hnhds : range I ∈ 𝓝 ((extChartAt I x) x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hmem) interior_subset
  have hwritten : writtenInExtChartAt I (𝓡 k) x f =
      fun z : E => f ((extChartAt I x).symm z) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    rfl
  have h1 : HasFDerivWithinAt (fun z : E => f ((extChartAt I x).symm z)) (mfderiv I (𝓡 k) f x)
      (range I) ((extChartAt I x) x) := by
    have h := hf.hasMFDerivAt
    unfold HasMFDerivAt at h
    rw [hwritten] at h
    exact h.2
  have h2 : fderiv ℝ (fun z : E => f ((extChartAt I x).symm z)) ((extChartAt I x) x) =
      mfderiv I (𝓡 k) f x := (h1.hasFDerivAt hnhds).fderiv
  rw [h2]
  rfl

end

end Work.ThomBordism.Transversality.TransversalApproximation
