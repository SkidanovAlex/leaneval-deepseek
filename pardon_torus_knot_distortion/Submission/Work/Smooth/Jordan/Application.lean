import Submission.Work.Topology.Classical.All
import Submission.Smooth
import Submission.Work.Smooth.Jordan.JordanIndex

/-!
# Item 5 of the chapter: Pardon's innermost-disc inputs in the smooth setting

This file instantiates the two inputs of `Work.InnermostDisk` — Pardon's first innermost step
`InnermostDiscInput P S` and Pardon's geometric input `CleansInSphere P S` — for the tori
`P = ParamTorus.mapHomeomorph ψ` of the challenge (in particular for `ψ = ψ₀.toHomeomorph` with
`ψ₀ : Submission.Diffeo`, the smooth ambient diffeomorphism of the challenge) and for the boundary
`S = ∂PBox s c σ = {y | Submission.boxNorm c σ y = s}` of Pardon's box.

The classical content is the *same* as the one isolated in the sibling chapter
`Work.Topology.Classical`: `Work.Topology.Classical.ClassicalTopology`, i.e. Jordan–Schoenflies in
`S²` (with the standard position of finitely many disjoint Jordan curves) together with
Alexander's theorem and isotopy extension in the cut-and-paste.  Everything below is a composition
of already-proved results, and this file exists to give the consumer of *this* chapter a named
interface in the vocabulary of `Work.Smooth.Jordan`:

* `innermostDiscInput_of_classicalTopology` — item 5, first half, at any embedded sphere in general
  position;
* `cleansInSphere_of_classicalTopology` — item 5, second half, at any embedded sphere in general
  position;
* `cleansInSphere_BoxSphere_of_classicalTopology` and its `Diffeo` form
  `cleansInSphere_diffeoBoxSphere_of_classicalTopology` — the case of Pardon's application: the box
  boundary `S = ∂PBox s c σ` transverse to `F = ψ(F_standard)`.

The transversality hypothesis `TransverseSphere P S` (`S` meets `F` in finitely many disjoint
simple closed curves) is *not* droppable — a sphere may meet a torus in a surface — and it is the
general-position choice of Pardon's sweep; see `Submission/Work/Topology/SphereSlicing/README.md`.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

/-- **Pardon's first innermost input in the smooth setting** (item 5, first half): for every
homeomorphism `ψ` of `ℝ³`, every embedded sphere `S` in general position with respect to
`F = ψ(F_standard)`, and the classical topological input, there is an innermost essential
intersection curve. -/
theorem innermostDiscInput_of_classicalTopology (ψ : R3 ≃ₜ R3)
    (h : Work.Topology.Classical.ClassicalTopology) (S : Set R3)
    (hS : Work.InnermostDisk.IsEmbeddedSphere S)
    (hT : Work.Topology.SphereSlicing.TransverseSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) S) :
    Work.InnermostDisk.InnermostDiscInput (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) S :=
  Work.Topology.SphereSlicing.innermostDiscInput_of_sliceInput
    (Work.Topology.Classical.classicalInput_mapHomeomorph_of_classicalTopology ψ h).1 hS hT

/-- **Pardon's geometric input in the smooth setting** (item 5, second half): every essential loop
of `F = ψ(F_standard)` inside an embedded sphere in general position can be replaced by a simple
essential loop inside it bounding a disc whose interior misses `F`. -/
theorem cleansInSphere_of_classicalTopology (ψ : R3 ≃ₜ R3)
    (h : Work.Topology.Classical.ClassicalTopology) (S : Set R3)
    (hS : Work.InnermostDisk.IsEmbeddedSphere S)
    (hT : Work.Topology.SphereSlicing.TransverseSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) S) :
    Work.InnermostDisk.CleansInSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) S :=
  Work.InnermostDisk.cleansInSphere_of_inputs
    (innermostDiscInput_of_classicalTopology ψ h S hS hT)
    (Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve
      (Work.Topology.Classical.cleanOneCurve_mapHomeomorph_of_classicalTopology ψ h))

/-- **The box-boundary case of Pardon's application**: for the box boundary
`S = ∂PBox s c σ = {y | boxNorm c σ y = s}` (`s > 0`) transverse to `F = ψ(F_standard)`, every
essential loop of `F` inside `S` bounds a compressing disc. -/
theorem cleansInSphere_BoxSphere_of_classicalTopology (ψ : R3 ≃ₜ R3)
    (h : Work.Topology.Classical.ClassicalTopology) {s : ℝ} (hs : 0 < s) (c : R3)
    (σ : Equiv.Perm (Fin 3))
    (hT : Work.Topology.SphereSlicing.TransverseSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) (Work.Topology.SphereSlicing.BoxSphere s c σ)) :
    Work.InnermostDisk.CleansInSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ)
      (Work.Topology.SphereSlicing.BoxSphere s c σ) :=
  Work.Topology.Classical.cleansInSphere_mapHomeomorph_BoxSphere_of_classicalTopology
    h ψ hs c σ hT

/-- The same for the surface of the challenge: `F = ψ₀(F_standard)` for a **diffeomorphism** `ψ₀`
of `ℝ³` (`Submission.Diffeo`, e.g. `Submission.psiDiffeo Φ` of the ambient isotopy of the
challenge), i.e. `P = ParamTorus.mapHomeomorph ψ₀.toHomeomorph`. -/
theorem cleansInSphere_diffeoBoxSphere_of_classicalTopology (ψ₀ : Submission.Diffeo) :
    Work.Topology.Classical.ClassicalTopology → ∀ {s : ℝ}, 0 < s → ∀ (c : R3)
      (σ : Equiv.Perm (Fin 3)),
      Work.Topology.SphereSlicing.TransverseSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ₀.toHomeomorph)
        (Work.Topology.SphereSlicing.BoxSphere s c σ) →
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ₀.toHomeomorph)
        (Work.Topology.SphereSlicing.BoxSphere s c σ) :=
  fun h _ hs c σ hT => cleansInSphere_BoxSphere_of_classicalTopology ψ₀.toHomeomorph h hs c σ hT

end

end Work.Smooth.Jordan
