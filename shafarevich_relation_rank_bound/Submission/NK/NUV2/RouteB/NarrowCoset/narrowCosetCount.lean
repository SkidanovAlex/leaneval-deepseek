import Mathlib
import Submission.NK.NUV2.RouteB.NarrowCoset.Defs
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO
import Submission.NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces
import Submission.NK.NUV2.RouteB.latticeCosetCount_cone_isBigO

/-!
# Lattice point count in the *narrow* region

This file proves `NK.NUV2.RouteB.NarrowCoset.narrowCosetCount`: for a number field `K`, a
fractional ideal `I` (given as a unit of the monoid of fractional ideals, i.e. a nonzero one) and
a shift `v` of the mixed space, the number of points of the coset `v + I` of the ideal lattice
lying in the dilated narrow region `narrowDilate K Y` is

  `Y * narrowRegionVolume K / idealCovolume K I + O(Y^{1 - 1/[K:ℚ]})`.

The narrow region is `NarrowCone K ∩ {norm ≤ 1}`, where `NarrowCone K` is the fundamental cone cut
by the positivity conditions at the real places.  Consequently its frontier is contained in the
frontier of the truncated fundamental cone together with the finitely many hyperplanes `x_w = 0`
at the real places, so the boundary layer estimate of
`NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces` applies verbatim: the
`ε`-thickening of the frontier has volume `O(ε)`.  The general lattice point count with power
saving error term `NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO` then gives the claim.

The only work here is therefore the identification
`narrowRegion K = fundamentalCone.normLeOne K ∩ {x | ∀ w real, x_w < 0}` (written with the negated
coordinate functionals `negRealCoord`) together with boundedness and measurability of the region —
the latter two for the hypotheses of the counting theorem.
-/

set_option autoImplicit false

open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Classical Pointwise nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB.NarrowCoset

/-- The negated coordinate functional `x ↦ -x_w` at a real place `w` of `K`, viewed as a
continuous linear functional on the mixed space.  It cuts out (by the condition `< 0`) the
positivity condition `0 < x_w` which defines the *narrow* cone inside the fundamental cone. -/
noncomputable def negRealCoord (K : Type) [Field K] [NumberField K]
    (i : {w : InfinitePlace K // w.IsReal}) : mixedSpace K →L[ℝ] ℝ :=
  -(ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

@[simp]
lemma negRealCoord_apply (K : Type) [Field K] [NumberField K]
    (i : {w : InfinitePlace K // w.IsReal}) (x : mixedSpace K) :
    negRealCoord K i x = -(x.1 i) := by
  simp [negRealCoord]

/-- The narrow region is the truncated fundamental cone cut by the finitely many open half
spaces `x_w < 0` (negated coordinates) at the real places.  This is the form in which the
boundary-layer estimate is available. -/
lemma narrowRegion_eq_inter_halfspaces (K : Type) [Field K] [NumberField K] :
    narrowRegion K = fundamentalCone.normLeOne K ∩
      {x : mixedSpace K | ∀ i : {w : InfinitePlace K // w.IsReal}, negRealCoord K i x < 0} := by
  ext x
  simp only [narrowRegion, NarrowCone, narrowNormLeOne, Set.mem_inter_iff, Set.mem_ofPred_eq,
    negRealCoord_apply, neg_lt_zero]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h3⟩, fun i => h2 i.1 i.2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨⟨h1, fun w hw => h2 ⟨w, hw⟩⟩, h3⟩

/-- The narrow region is bounded (it is contained in `normLeOne K`). -/
lemma isBounded_narrowRegion (K : Type) [Field K] [NumberField K] :
    Bornology.IsBounded (narrowRegion K) := by
  refine (fundamentalCone.isBounded_normLeOne K).subset ?_
  intro x hx
  rw [fundamentalCone.mem_normLeOne]
  exact ⟨hx.1.1, hx.2⟩

/-- The narrow region is measurable. -/
lemma measurableSet_narrowRegion (K : Type) [Field K] [NumberField K] :
    MeasurableSet (narrowRegion K) := by
  rw [narrowRegion_eq_inter_halfspaces]
  refine (fundamentalCone.measurableSet_normLeOne K).inter ?_
  have h : {x : mixedSpace K | ∀ i : {w : InfinitePlace K // w.IsReal}, negRealCoord K i x < 0}
      = ⋂ i : {w : InfinitePlace K // w.IsReal}, {x : mixedSpace K | negRealCoord K i x < 0} := by
    ext x; simp
  rw [h]
  exact MeasurableSet.iInter fun i =>
    (isOpen_lt (negRealCoord K i).continuous continuous_const).measurableSet

/-- **Minkowski content of the frontier of the narrow region.**  The `ε`-neighbourhood of
`frontier (narrowRegion K)` has volume `≤ c * ε` for `0 < ε ≤ 1`.  This is the general
frontier estimate for the truncated fundamental cone cut by finitely many open half spaces
(`NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces`), applied to the negated
coordinate functionals at the real places, via `narrowRegion_eq_inter_halfspaces`. -/
lemma cthickening_frontier_narrowRegion_le (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε (frontier (narrowRegion K))) ≤ ENNReal.ofReal (c * ε) := by
  obtain ⟨c, hc, h⟩ := NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces K
    {w : InfinitePlace K // w.IsReal} (negRealCoord K)
  refine ⟨c, hc, fun ε hε hε1 => ?_⟩
  rw [narrowRegion_eq_inter_halfspaces]
  exact h ε hε hε1

theorem narrowCosetCount (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ)
    (v : NumberField.mixedEmbedding.mixedSpace K) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((Nat.card {x : NumberField.mixedEmbedding.idealLattice K I //
            v + (x : NumberField.mixedEmbedding.mixedSpace K) ∈
              NK.NUV2.RouteB.NarrowCoset.narrowDilate K Y} : ℝ)
        - Y * NK.NUV2.RouteB.NarrowCoset.narrowRegionVolume K /
            NK.NUV2.RouteB.NarrowCoset.idealCovolume K I)|
      ≤ C * Y ^ (1 - (Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K) : ℝ)⁻¹) := by
  obtain ⟨C, hC, h⟩ := NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO
    (mixedSpace K) (idealLattice K I) (narrowRegion K) (isBounded_narrowRegion K)
    (measurableSet_narrowRegion K) (cthickening_frontier_narrowRegion_le K) v
  exact ⟨C, hC, fun Y hY => h Y hY⟩

end NK.NUV2.RouteB.NarrowCoset
