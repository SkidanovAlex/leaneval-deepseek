import Mathlib
import Submission.Work.Smooth.BoxGeneric.AeMain
import Submission.Work.Smooth.BoxGeneric.AeVertex

/-!
# The target of the chapter, packaged

This file packages the inputs of `Submission/Work/Smooth/BoxGeneric` into a single structure and
states the target `Work.BoxShrink.AeSlicedAll` (and its pointwise form `Work.BoxShrink.AeSliced`)
from it.  See the README of the chapter for the meaning of each field.

After the sharp form of the main theorem (`Submission/Work/Smooth/BoxGeneric/AeMain.lean`) the
inputs of the chapter are only two genericity statements plus the classical topology:

* `vertex` — `AeNoVertex`: the surface avoids the vertices of the box for almost every level;
* `classify` — `Work.Smooth.Morse.CompactOneManifoldInput`: the classification of compact
  `1`-manifolds (a compact locally-arc subset of the surface is a finite disjoint union of simple
  closed curves);
* `jordan` — `Work.Topology.Classical.JordanSchoenfliesSphere`, the sphere-side Jordan–Schoenflies
  theorem (which the sibling chapter `Submission/Work/Smooth/SphereJordan` derives from the planar
  Jordan–Schoenflies theorem).

The Sard input of the chapter (`SardCoord`) is *not* an input: it is a theorem
(`Work.Smooth.BoxGeneric.Sard.sardCoord`), proved from the two-dimensional Sard theorem of
`Submission/Work/Smooth/BoxGeneric/Sard/`.  Neither is the corner transversality input
`AeTransverseCorner` of the first version of the chapter: it is a theorem
(`Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector`), proved from Sard on the
smooth pieces of the box norm.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.BoxGeneric

/-- **The geometric inputs of the chapter** (everything but the classical topology).

* `vertex` — the box spheres avoid the vertices of the box almost everywhere;
* `classify` — the classification of compact `1`-manifolds.

Both are genericity statements about the surface: the second is a classical theorem of topology
which Mathlib does not contain, the first is the honest remaining gap of the chapter (see the
README, §5: it holds for a generic diffeomorphism but *not* for a pathological one). -/
structure BoxGenericGeomInput where
  /-- the box spheres avoid the vertices of the box -/
  vertex : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)), AeNoVertex ψ c σ
  /-- the classification of compact `1`-manifolds -/
  classify : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ

/-- **The complete input of the chapter**: the two geometric inputs and the classical
sphere-side Jordan–Schoenflies theorem. -/
structure BoxGenericInput where
  /-- the box spheres avoid the vertices of the box -/
  vertex : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)), AeNoVertex ψ c σ
  /-- the classification of compact `1`-manifolds -/
  classify : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ
  /-- the sphere-side Jordan–Schoenflies theorem -/
  jordan : Work.Topology.Classical.JordanSchoenfliesSphere

/-- The geometric part of the complete input. -/
def BoxGenericInput.toGeomInput (h : BoxGenericInput) : BoxGenericGeomInput :=
  ⟨h.vertex, h.classify⟩

/-! ## The target from the geometric inputs -/

/-- **The target `Work.BoxShrink.AeSlicedAll` from the geometric inputs and the sphere-side
Jordan–Schoenflies theorem.** -/
theorem aeSlicedAll_of_geomInput_of_jordanSchoenflies (hg : BoxGenericGeomInput)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_vertex_classify_of_jordanSchoenflies hg.vertex hg.classify hjordan

/-- **The target from the geometric inputs and the *planar* Jordan–Schoenflies theorem**
(`Work.Smooth.SphereJordan.PlaneHypothesis`, the classical input of the sibling chapters
`Submission/Work/Smooth/Jordan` and `Submission/Work/Smooth/SphereJordan`). -/
theorem aeSlicedAll_of_geomInput_of_planeHypothesis (hg : BoxGenericGeomInput)
    (hplane : Work.Smooth.SphereJordan.PlaneHypothesis) : Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_vertex_classify_of_planeHypothesis hg.vertex hg.classify hplane

/-- **The target from the geometric inputs and the classical input of the sibling chapter
`Work.Topology.SphereSlicing`** (`SliceInput standard`, i.e. the slicing by Jordan–Schoenflies of
the spheres in general position by the standard torus). -/
theorem aeSlicedAll_of_geomInput_of_classicalInput (hg : BoxGenericGeomInput)
    (hCI : Work.Topology.SphereSlicing.ClassicalInput Work.CoreTopology.standard) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_vertex_classify hg.vertex hg.classify fun ψ =>
    (Work.Topology.SphereSlicing.sliceInput_map_homeomorph_iff ψ.toHomeomorph).mpr hCI.1

/-- **The pointwise target** `Work.BoxShrink.AeSliced ψ c σ` from the geometric inputs and the
sphere-side Jordan–Schoenflies theorem. -/
theorem aeSliced_of_geomInput_of_jordanSchoenflies (hg : BoxGenericGeomInput)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Work.BoxShrink.AeSliced ψ c σ :=
  aeSlicedAll_of_geomInput_of_jordanSchoenflies hg hjordan ψ c σ

/-! ## The target from the complete input -/

/-- **The target of the chapter**: almost every box sphere meets the surface in general position,
i.e. the field `ae` of `Work.BoxShrink.FinalInput`.  In particular
`(fun ψ c σ => Work.Smooth.BoxGeneric.aeSliced_of_input h ψ c σ)` is a term of type
`Work.BoxShrink.AeSlicedAll`. -/
theorem aeSlicedAll_of_input (h : BoxGenericInput) : Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_geomInput_of_jordanSchoenflies h.toGeomInput h.jordan

/-- The pointwise form of the target: for every diffeomorphism, centre and coordinate
permutation. -/
theorem aeSliced_of_input (h : BoxGenericInput) (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Work.BoxShrink.AeSliced ψ c σ :=
  aeSlicedAll_of_input h ψ c σ

/-! ## The complete input of the chapter, with no vertex genericity -/

/-- **The complete classical input of the chapter**: the classification of compact
`1`-manifolds and the sphere-side Jordan–Schoenflies theorem.  There is no vertex genericity input:
the vertex strata of the box spheres are handled by the a.e.-tangency argument of
`Submission/Work/Smooth/BoxGeneric/AeVertex.lean` (see the README, §3.13 and §5.3). -/
structure BoxGenericClassicalInput where
  /-- the classification of compact `1`-manifolds -/
  classify : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ
  /-- the sphere-side Jordan–Schoenflies theorem -/
  jordan : Work.Topology.Classical.JordanSchoenfliesSphere

/-- **The target of the chapter from the complete classical input.**  In particular
`Work.Smooth.BoxGeneric.aeSlicedAll_of_classicalInput h` is a term of type
`Work.BoxShrink.AeSlicedAll` — the field `ae` of `Work.BoxShrink.FinalInput` — and
`(fun ψ c σ => Work.Smooth.BoxGeneric.aeSliced_of_classicalInput h ψ c σ)` is the same statement
pointwise. -/
theorem aeSlicedAll_of_classicalInput (h : BoxGenericClassicalInput) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_classify_of_jordanSchoenflies h.classify h.jordan

/-- The pointwise form of the target from the complete classical input. -/
theorem aeSliced_of_classicalInput (h : BoxGenericClassicalInput) (ψ : Submission.Diffeo)
    (c : R3) (σ : Equiv.Perm (Fin 3)) : Work.BoxShrink.AeSliced ψ c σ :=
  aeSlicedAll_of_classicalInput h ψ c σ


end Work.Smooth.BoxGeneric
