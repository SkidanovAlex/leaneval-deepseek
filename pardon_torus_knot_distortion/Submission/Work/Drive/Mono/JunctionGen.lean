import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData

/-!
# The stratified genericity of the sweep data at the junctions of the trace

`Work.Drive.Mono.JunctionGen` collects the *extra* geometric conditions on the tilt data which the
local models of the trace at the **junction points** consume.  The interior point types of the trace
(the level wall, the slab faces and the box sphere off the wall and the faces) are handled by the
proved local models, whose hypotheses come from the four clauses of
`Work.Drive.Final.TiltedGenericity`; the junctions are:

* **wall ∩ box sphere** (a point of the surface on the box sphere, strictly inside the slab, at the
  level): the trace is the "V" of the half of the level curve that runs into the box and the half of
  the box-sphere trace on the side `ℓ > lam`; the local model
  `Work.Drive.Mono.isLocallyEuclidean_trace_of_wallSphereJunction` needs the level to cross the box
  sphere *transversally* at `z` (conjunct (a) below);
* **wall ∩ slab face** (a point of the surface inside the box, on a slab face, at the level): the
  local model `Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction` needs the level curve to
  cross the face curve transversally, which is clause (ii) of `TiltedGenericity` at a
  non-exceptional level (no new condition);
* **slab face ∩ box sphere** (a point of the surface on the box sphere, on a slab face, strictly
  below the level): the two curves (the face curve and the box-sphere trace) cross transversally at
  `z` (conjunct (b) below);
* **triple points** (on the box sphere, on a slab face, and at the level) and **box edges/corners**
  (points of the box sphere at which two or three box coordinates are extremal): the trace has three
  branches there, and the trace curves of the junction types would not be a 1-manifold; these are
  finitely many points, and *their levels* go into the exceptional set (conjuncts (c), (d) below).

All four conjuncts are conditions on the *choice* of the tilt data (`v`, `h`, `ℓ` and the box), not
on the box alone; they are satisfied by generic data with the finitely many bad levels collected into
`exc`, which is why the residual of the tilted sweep is stated *existentially* over the data.

Read with `Submission/Work/Drive/Mono/NOTES_tiltedTraceDataWExists.md`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The stratified genericity of the tilt data at the junctions of the trace.**

* (a) at every non-exceptional level of the window, every surface point of the box sphere which is in
  the closed slab and at the level is a regular point of the sweep height, and the level curve of the
  sweep height crosses the box sphere transversally there (so that the trace near the point is the
  "V" of the two half-curves);
* (b) at every non-exceptional level of the window, every surface point of the box sphere which is on
  a slab face and strictly below the level has the face plane crossing the box sphere transversally
  there;
* (c) the levels of the surface points of the box sphere at which two or three box coordinates are
  extremal (the box edges and corners) are exceptional;
* (d) the levels of the surface points of the box sphere which lie on a slab face are exceptional
  (the triple points, at which three branches of the trace meet). -/
def JunctionGen (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 ∧
        fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| = h → ℓ z < lam →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      ℓ z ∈ (exc : Set ℝ)) ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ℓ z ∈ (exc : Set ℝ))

end

end Work.Drive.Mono
