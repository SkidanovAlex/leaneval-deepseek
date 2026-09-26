import Submission.Work.Smooth.JordanSeparation.All
import Submission.Work.Smooth.SphereJordan.All
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.BoxGeneric.All
import Submission.Work.Smooth.Plane.All
import Submission.Work.Smooth.Morse.All
import Submission.Work.BoxShrink.Pinch.All
import Submission.Work.BoxShrink.Bubble.All

/-!
# `Submission.Work.Smooth.RepairImport.All` — the eight delivered chapters in one environment

This module exists for exactly one reason: the two chapters

* `Submission.Work.Smooth.JordanSeparation.All` (the planar Jordan separation theorem and its index
  theory) and
* `Submission.Work.Smooth.SphereJordan.All` (the sphere-side Jordan–Schoenflies theorem, the planar
  annulus theorem and the reduction of Pardon's cut-and-paste)

used to define the same declaration name **with different types**, so that no module could import
both.  Two declarations of the *same* name are merged by Lean when their types are syntactically
equal (`Lean.Environment.subsumesInfo`), and rejected otherwise — with

```
error: import Submission.Work.Smooth.JordanSeparation.exists_continuum_separating failed,
       environment already contains
       'Work.Smooth.JordanSeparation.isPreconnected_insert_of_mem_closure'
       from Submission.Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn
```

The repair is recorded in `README.md` in this directory: the copy of
`Work.Smooth.JordanSeparation.isPreconnected_insert_of_mem_closure` that lived in
`Submission/Work/Smooth/JordanSeparation/exists_continuum_separating.lean` (in the `Set ℂ`
specialisation) was deleted there — together with the equally duplicated
`Work.Smooth.JordanSeparation.compl_frontier_eq_of_isOpen` — and that file now imports
`Submission.Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn`, which keeps
the *general* form of both statements.  Every statement that used to be available from
`exists_continuum_separating.lean` is still available under the same name, at the same type (the
general `isPreconnected_insert_of_mem_closure` specialises to the deleted `Set ℂ` form, and
`compl_frontier_eq_of_isOpen` had the same statement in the two files), so no consumer changes.

## What a caller gets

Import this module and the eight chapters above are simultaneously in scope; the import is checked
by `lake build Submission.Work.Smooth.RepairImport.All`.  The eight chapters are exactly the
material the final assembly of Pardon's theorem consumes: the planar chapter
(`Submission/Work/Smooth/Plane`), the Morse/Sard chapter (`Submission/Work/Smooth/Morse`), the
almost-everywhere chapter (`Submission/Work/Smooth/BoxGeneric`), the two Jordan chapters
(`Submission/Work/Smooth/Jordan`, `Submission/Work/Smooth/JordanSeparation`), the sphere chapter
(`Submission/Work/Smooth/SphereJordan`) and the two shrinking chapters
(`Submission/Work/BoxShrink/Pinch`, `Submission/Work/BoxShrink/Bubble`).

`Work.Smooth.RepairImport.coimport` is a **compile-time certificate** of the co-import: it is a
conjunction whose eight conjuncts are one headline theorem of each chapter, so the proof term
mentions a result of every one of the eight chapters.  `Work.Smooth.RepairImport.seam` is the seam
lemma the caller is most likely to need: the planar Jordan–Schoenflies hypothesis of the sphere
chapter, together with the classification of compact `1`-manifolds, yields *both* the sphere-side
Jordan–Schoenflies theorem (sphere chapter) *and* the almost-everywhere field
`Work.BoxShrink.AeSlicedAll` (box-generic chapter) — two results that lay on opposite sides of the
import clash that this module repairs.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.RepairImport

/-- **The co-import certificate.**  One headline result of each of the eight chapters, in one
conjunction:

1. `Submission.Work.Smooth.JordanSeparation` — the planar Jordan separation theorem, unconditionally,
   for every `C¹` curve injective on one period;
2. `Submission.Work.Smooth.SphereJordan` — Jordan–Schoenflies on the round sphere from the planar
   Jordan–Schoenflies hypothesis;
3. `Submission.Work.Smooth.BoxGeneric` — almost every level of the box norm meets a surface in
   general position, from the classification of compact `1`-manifolds and the sphere-side theorem;
4. `Submission.Work.Smooth.SphereJordan` — the `cleans` field of `Work.BoxShrink.FinalInput` from
   the planar hypothesis and the three `3`-dimensional position inputs;
5. `Submission.Work.BoxShrink.Pinch` — Pardon's pinch datum gives the smooth half-sphere statement;
6. `Submission.Work.Smooth.Plane` — the cutting disc of the box is a convex planar set;
7. `Submission.Work.Smooth.Morse` — a regular level set of a `C¹` function on a torus is a local
   arc;
8. `Submission.Work.BoxShrink.Bubble` — the standard counterexample to the naive slice push-off.

The proof term uses the eight chapters *simultaneously*; in particular conjuncts `1` and `4` come
from the two chapters that could not be imported together before the repair. -/
theorem coimport :
    (∀ c : Work.Smooth.Jordan.SmoothPlaneCurve, c.IsSimple →
        Nonempty (Work.Smooth.Jordan.PlaneSeparation c.toPlaneCurve)) ∧
    (Work.Smooth.SphereJordan.PlaneHypothesis →
        Work.Topology.Classical.JordanSchoenfliesSphere) ∧
    ((∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ) →
        Work.Topology.Classical.JordanSchoenfliesSphere → Work.BoxShrink.AeSlicedAll) ∧
    (Work.Smooth.SphereJordan.PlaneHypothesis →
        Work.Smooth.SphereJordan.SurfaceDiscPushOff Work.CoreTopology.standard →
        Work.Smooth.SphereJordan.CurvesInterior Work.CoreTopology.standard →
        (∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
          Work.Smooth.SphereJordan.LocallyFlat D.e) →
        Work.BoxShrink.CleansDiscsAll) ∧
    (Work.BoxShrink.Bubble.PardonPinchInput → Work.BoxShrink.Pinch.SmoothHalfS) ∧
    (∀ (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.Smooth.Plane.IsConvexPlanar (Work.Smooth.Plane.PardonSlice s c σ u)) ∧
    (∀ (ψ : Submission.Diffeo) {g : R3 → ℝ}, ContDiff ℝ 1 g → ∀ t : ℝ,
        Work.Smooth.Morse.IsRegularValue ψ g t →
        Work.Smooth.Morse.IsLocalArc ψ (Work.Smooth.Morse.levelSet ψ g t)) ∧
    (¬ Work.BoxShrink.Bubble.SlicePushOff Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap 1 2) 0) :=
  ⟨Work.Smooth.JordanSeparation.jordanSeparation_of_isSimple,
   Work.Smooth.SphereJordan.jordanSchoenfliesSphere,
   Work.Smooth.BoxGeneric.aeSlicedAll_of_classify_of_jordanSchoenflies,
   Work.Smooth.SphereJordan.cleansDiscsAll_field_of_plane,
   Work.BoxShrink.Pinch.smoothHalfS_of_pardonPinchInput,
   Work.Smooth.Plane.isConvexPlanar_PardonSlice,
   fun ψ g hg t hreg => Work.Smooth.Morse.Regular.levelSet_isLocalArc_of_regularValue ψ hg hreg,
   Work.BoxShrink.Bubble.standard_counterexample.2.2⟩

/-- **The seam lemma.**  From the planar Jordan–Schoenflies hypothesis and the classification of
compact `1`-manifolds one gets, in one step and in one environment, both the sphere-side
Jordan–Schoenflies theorem (chapter `SphereJordan`) and the almost-everywhere general-position field
`Work.BoxShrink.AeSlicedAll` (chapter `BoxGeneric`).  Before the repair this combination could not
even be *stated*, let alone proved: the two conclusions are proved in modules that could not be
imported together. -/
theorem seam (hplane : Work.Smooth.SphereJordan.PlaneHypothesis)
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    Work.Topology.Classical.JordanSchoenfliesSphere ∧ Work.BoxShrink.AeSlicedAll :=
  ⟨Work.Smooth.SphereJordan.jordanSchoenfliesSphere hplane,
   Work.Smooth.BoxGeneric.aeSlicedAll_of_classify_of_planeHypothesis hclass hplane⟩

/-- The `cleans` field of `Work.BoxShrink.FinalInput` and the almost-everywhere field are
simultaneously available, from the same planar hypothesis. -/
theorem seam' (hplane : Work.Smooth.SphereJordan.PlaneHypothesis)
    (hpush : Work.Smooth.SphereJordan.SurfaceDiscPushOff Work.CoreTopology.standard)
    (hpos : Work.Smooth.SphereJordan.CurvesInterior Work.CoreTopology.standard)
    (hlf : ∀ D : Work.Topology.SphereSlicing.SliceDisc Work.CoreTopology.standard,
      Work.Smooth.SphereJordan.LocallyFlat D.e)
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    Work.BoxShrink.CleansDiscsAll ∧ Work.BoxShrink.AeSlicedAll :=
  ⟨Work.Smooth.SphereJordan.cleansDiscsAll_field_of_plane hplane hpush hpos hlf,
   Work.Smooth.BoxGeneric.aeSlicedAll_of_classify_of_planeHypothesis hclass hplane⟩

end Work.Smooth.RepairImport
