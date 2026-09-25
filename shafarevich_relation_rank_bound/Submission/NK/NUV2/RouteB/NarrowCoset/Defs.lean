import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs

/-!
# The narrow region and its dilates, as opaque definitions

For the lattice-point count in the *narrow* region (the fundamental cone cut by the positivity of
the real coordinates), it is convenient to hide the measure-theoretic notation behind definitions,
so that statements involving them do not need the `Classical`/`Pointwise` scoped instances.

* `narrowRegion K` is the region `narrowNormLeOne K` of `NK.NUV2.RouteB` (the fundamental cone
  intersected with the positivity conditions at the real places, truncated by the norm ball);
* `narrowDilate K Y` is its dilate by `Y^{1/[K:ℚ]}`, i.e. the intersection of the cone and the
  positivity region with the norm ball of radius `Y`;
* `narrowRegionVolume K` is its volume;
* `idealCovolume K I` is the covolume of the ideal lattice of `I`.
-/

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding MeasureTheory
open scoped Classical Pointwise nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB.NarrowCoset

/-- The narrow region: `fundamentalCone ∩ {positive at the real places} ∩ {norm ≤ 1}`. -/
noncomputable def narrowRegion (K : Type) [Field K] [NumberField K] : Set (mixedSpace K) :=
  NK.NUV2.RouteB.narrowNormLeOne K

/-- The volume of the narrow region. -/
noncomputable def narrowRegionVolume (K : Type) [Field K] [NumberField K] : ℝ :=
  (volume (narrowRegion K)).toReal

/-- The dilate `Y^{1/[K:ℚ]} • narrowRegion`, i.e. the cone cut by positivity within the norm ball
of radius `Y`. -/
noncomputable def narrowDilate (K : Type) [Field K] [NumberField K] (Y : ℝ) :
    Set (mixedSpace K) :=
  Y ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹) • narrowRegion K

/-- The covolume of the ideal lattice of a fractional ideal. -/
noncomputable def idealCovolume (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)ˣ) : ℝ :=
  ZLattice.covolume (idealLattice K I)

end NK.NUV2.RouteB.NarrowCoset
