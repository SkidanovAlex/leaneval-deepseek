import Mathlib
import Submission.NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO
import Submission.NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces
import Submission.NK.NUV2.RouteB.Dict.latticeCosetCount_halfspaces_isBigO
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Sharp half-space lattice-point count in the fundamental cone

For a number field `K`, a fractional ideal `I`, a shift `x₀` and finitely many continuous linear
functionals `f i`, the number of points of the coset `x₀ + I` (the ideal lattice of `I` in the
mixed space) that lie in the fundamental cone, satisfy `f i a < 0` and have norm `≤ X` is
asymptotic to

  `X * volume (normLeOne K ∩ {a | ∀ i, f i a < 0}) / covolume (idealLattice K I)`

with the *sharp* error term `O(X ^ (1 - 1/[K : ℚ]))`.

This is the version of `NK.NUV2.RouteB.Dict.latticeCosetCount_halfspaces_isBigO` in which the
exponent of the error term is exposed: the underlying general lattice-point count
`NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO` produces exactly the exponent
`1 - (finrank ℝ E)⁻¹`, and `finrank ℝ (mixedSpace K) = finrank ℚ K`
(`NumberField.mixedEmbedding.finrank`).
-/

namespace NK.NUV2.RouteB.Sharp3

open scoped Classical Pointwise nonZeroDivisors
open MeasureTheory

theorem halfspaceCosetCount_sharp (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ)
    (x₀ : NumberField.mixedEmbedding.mixedSpace K)
    (ι : Type) [Fintype ι] (f : ι → NumberField.mixedEmbedding.mixedSpace K →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      |((Nat.card {a : NumberField.mixedEmbedding.mixedSpace K //
          a - x₀ ∈ (NumberField.mixedEmbedding.idealLattice K I :
            Set (NumberField.mixedEmbedding.mixedSpace K)) ∧
          a ∈ NumberField.mixedEmbedding.fundamentalCone K ∧
          (∀ i : ι, f i a < 0) ∧
          NumberField.mixedEmbedding.norm a ≤ X}) : ℝ)
        - X * (MeasureTheory.volume
              (NumberField.mixedEmbedding.fundamentalCone.normLeOne K ∩
              {a : NumberField.mixedEmbedding.mixedSpace K | ∀ i : ι, f i a < 0})).toReal
            / ZLattice.covolume (NumberField.mixedEmbedding.idealLattice K I)|
      ≤ C * X ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  have hPmeas : MeasurableSet
      (NumberField.mixedEmbedding.fundamentalCone.normLeOne K ∩
        {a : NumberField.mixedEmbedding.mixedSpace K | ∀ i : ι, f i a < 0}) := by
    refine (NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K).inter ?_
    have hEq : {a : NumberField.mixedEmbedding.mixedSpace K | ∀ i : ι, f i a < 0}
        = ⋂ i : ι, {a : NumberField.mixedEmbedding.mixedSpace K | f i a < (0 : ℝ)} := by
      ext a; simp
    rw [hEq]
    exact MeasurableSet.iInter (fun i => measurableSet_Iio.preimage (f i).continuous.measurable)
  have hPbdd : Bornology.IsBounded
      (NumberField.mixedEmbedding.fundamentalCone.normLeOne K ∩
        {a : NumberField.mixedEmbedding.mixedSpace K | ∀ i : ι, f i a < 0}) :=
    (NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne K).subset Set.inter_subset_left
  have hbd : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε
        (frontier (NumberField.mixedEmbedding.fundamentalCone.normLeOne K ∩
          {a : NumberField.mixedEmbedding.mixedSpace K | ∀ i : ι, f i a < 0})))
        ≤ ENNReal.ofReal (c * ε) :=
    NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces K ι f
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO
      (NumberField.mixedEmbedding.mixedSpace K) (NumberField.mixedEmbedding.idealLattice K I)
      (NumberField.mixedEmbedding.fundamentalCone.normLeOne K ∩
        {a : NumberField.mixedEmbedding.mixedSpace K | ∀ i : ι, f i a < 0})
      hPbdd hPmeas hbd x₀
  refine ⟨C₁, hC₁pos, ?_⟩
  intro X hX
  rw [NK.NUV2.RouteB.Dict.natCard_halfspaces_coset_eq_dict I x₀ ι f hX]
  simpa only [NumberField.mixedEmbedding.finrank] using hC₁ X hX

end NK.NUV2.RouteB.Sharp3
