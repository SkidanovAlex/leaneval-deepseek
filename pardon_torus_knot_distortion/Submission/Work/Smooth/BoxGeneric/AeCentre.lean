import Mathlib
import Submission.Work.Smooth.BoxGeneric.AeMain
import Submission.Work.Smooth.BoxGeneric.Final
import Submission.Work.Smooth.BoxGeneric.Vertex.aeNoVertex_of_ae_centre
import Submission.Work.Smooth.BoxGeneric.Vertex.volume_carrier_eq_zero

/-!
# The target for almost every centre

The one genericity input of the chapter which is *not* a classical theorem and *not* a consequence
of smoothness is `Work.Smooth.BoxGeneric.AeNoVertex ψ c σ` (see the README, §5.3): the surface must
avoid the vertices of the box for almost every level.  It is not automatic — a smooth surface may
contain a segment of a vertex ray, and then the level sets are not `1`-manifolds for a
positive-measure set of levels — but it *is* automatic for almost every *centre*:

* `Work.Smooth.BoxGeneric.Vertex.volume_carrier_eq_zero` — the surface is null in `ℝ³`;
* `Work.Smooth.BoxGeneric.Vertex.aeNoVertex_of_ae_centre` — hence, by Fubini on the `(c,s)`-space,
  `AeNoVertex ψ c σ` holds for a.e. `c`;
* `Work.Smooth.BoxGeneric.aeNoVertex_ae_centre` below is the unconditional form (the nullity of the
  surface being itself a theorem);
* `Work.Smooth.BoxGeneric.aeSliced_ae_centre(_of_jordanSchoenflies)`: consequently the target
  `Work.BoxShrink.AeSliced ψ c σ` holds for almost every centre, from the two classical inputs
  (the classification of compact `1`-manifolds and Jordan–Schoenflies) and nothing else.

This is the sharpest *unconditional* form of the target available: `AeSlicedAll = ∀ c, …` is false
for an arbitrary centre (see the README, §5.3), while `∀ᵐ c, AeSliced ψ c σ` follows from the
classical inputs alone.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory

namespace Work.Smooth.BoxGeneric

noncomputable section

variable {ψ : Submission.Diffeo}

/-- **The vertex input holds for almost every centre** (unconditional form: the nullity of the
surface in `ℝ³` is a theorem, `Vertex.volume_carrier_eq_zero`). -/
theorem aeNoVertex_ae_centre (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ c ∂(MeasureTheory.volume : MeasureTheory.Measure R3), AeNoVertex ψ c σ :=
  Vertex.aeNoVertex_of_ae_centre σ (Vertex.volume_carrier_eq_zero ψ)

/-- **General position of the box spheres for almost every centre**, from the classification of
compact `1`-manifolds. -/
theorem aeTransverseBox_ae_centre (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    ∀ᵐ c ∂(MeasureTheory.volume : MeasureTheory.Measure R3), AeTransverseBox ψ c σ :=
  (aeNoVertex_ae_centre ψ σ).mono fun c hc => aeTransverseBox_of_regularBisector hc hclass

/-- **The target for almost every centre**, from the classification of compact `1`-manifolds and
the classical slicing input. -/
theorem aeSliced_ae_centre (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hslice : Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ)) :
    ∀ᵐ c ∂(MeasureTheory.volume : MeasureTheory.Measure R3), Work.BoxShrink.AeSliced ψ c σ :=
  (aeTransverseBox_ae_centre ψ σ hclass).mono fun c hc =>
    aeSliced_of_aeTransverseBox ψ c σ hc hslice

/-- **The target for almost every centre**, from the classification of compact `1`-manifolds and
the sphere-side Jordan–Schoenflies theorem. -/
theorem aeSliced_ae_centre_of_jordanSchoenflies (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) :
    ∀ᵐ c ∂(MeasureTheory.volume : MeasureTheory.Measure R3), Work.BoxShrink.AeSliced ψ c σ :=
  aeSliced_ae_centre ψ σ hclass (sliceInput_of_jordanSchoenflies hjordan ψ)

/-- **The target for almost every centre**, from the two classical inputs of the chapter, in the
packaged form: `BoxGenericGeomInput` (the classification of compact `1`-manifolds) and the
sphere-side Jordan–Schoenflies theorem. -/
theorem aeSliced_ae_centre_of_geomInput (hg : BoxGenericGeomInput)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) (ψ : Submission.Diffeo)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ c ∂(MeasureTheory.volume : MeasureTheory.Measure R3), Work.BoxShrink.AeSliced ψ c σ :=
  aeSliced_ae_centre_of_jordanSchoenflies ψ σ (hg.classify ψ) hjordan

/-- **The target from a concrete geometric condition on the surfaces.**

If each of the eight vertex rays of the box family meets the surface `ψ(standard torus)` in a
*countable* set of levels — which is what happens for a real-analytic surface (a line meets an
analytic surface discretely), and for generic `ψ` — then `Work.BoxShrink.AeSlicedAll` follows from
the classification of compact `1`-manifolds and the sphere-side Jordan–Schoenflies theorem.

This is the most concrete conditional form of the target: the hypothesis is a statement about the
*intersections of straight lines with the surface*, and it is exactly the vertex genericity
`AeNoVertex` in the form in which it can be verified. -/
theorem aeSlicedAll_of_ray_countable
    (hray : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ),
      (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) →
      ({s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier}).Countable)
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_vertex_classify_of_jordanSchoenflies
    (fun ψ c σ => aeNoVertex_of_countable ψ c σ (hray ψ c σ)) hclass hjordan

end

end Work.Smooth.BoxGeneric
