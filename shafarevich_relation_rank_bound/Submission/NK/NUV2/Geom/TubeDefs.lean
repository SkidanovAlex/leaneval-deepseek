/-
Supporting definitions for the geometric (Minkowski-content) inputs of the ideal-counting
asymptotics in `Submission/Work/NUV2/Geom/`.

The point of this file is to `open scoped Classical` (the `MeasureSpace`/`PseudoEMetricSpace`
instances of the mixed space are noncomputable and need classical decidability), so that the
`ε`-thickenings of the relevant frontiers can be referred to by *name* from other files.
-/
import Mathlib

namespace NK.NUV2.Geom

set_option autoImplicit false
open MeasureTheory NumberField NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open scoped Classical

/-- The `ε`-thickening of the frontier of the truncated fundamental cone
`fundamentalCone.normLeOne K`, viewed inside the mixed space of `K`. -/
noncomputable def normLeOneFrontierTube (K : Type*) [Field K] [NumberField K] (ε : ℝ) :
    Set (mixedSpace K) :=
  Metric.cthickening ε (frontier (fundamentalCone.normLeOne K))

/-- The volume of `normLeOneFrontierTube K ε`. -/
noncomputable def normLeOneFrontierTubeVolume (K : Type*) [Field K] [NumberField K]
    (ε : ℝ) : ENNReal :=
  volume (normLeOneFrontierTube K ε)

/-- The `ε`-thickening of the frontier of the truncated fundamental cone intersected with the
open cone `{x | ∀ i, f i x < 0}` cut out by finitely many continuous linear functionals. -/
noncomputable def normLeOneInterHalfspacesFrontierTube (K : Type*) [Field K] [NumberField K]
    {ι : Type*} (f : ι → mixedSpace K →L[ℝ] ℝ) (ε : ℝ) : Set (mixedSpace K) :=
  Metric.cthickening ε
    (frontier (fundamentalCone.normLeOne K ∩ {x | ∀ i, f i x < 0}))

/-- The volume of the `ε`-thickening, inside `realSpace K`, of the image under `expMapBasis` of
the face `{x | x ∈ closure (paramSet K) ∧ x j = t}` of the closure of the parameter box.
These are the pieces into which the frontier of `expMapBasis '' paramSet K` decomposes. -/
noncomputable def faceTubeVolume (K : Type*) [Field K] [NumberField K]
    (j : InfinitePlace K) (t ε : ℝ) : ENNReal :=
  volume (Metric.cthickening ε
    (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = t}))

end NK.NUV2.Geom
