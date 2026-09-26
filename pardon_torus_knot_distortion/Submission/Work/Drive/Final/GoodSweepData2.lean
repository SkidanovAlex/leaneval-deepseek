import Mathlib
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Mono.BoxGen

/-!
# `GoodSweepData2`: the data of a good tilted sweep, with the event types of the (L) route

Project lead, `NOTES_LEAD_grazes_L.md` (2026-09-26 04:45), task **L1**: the (L) field of
`Work.Drive.Final.TiltedSweepMono` is proved at data satisfying `GoodSweepData` together with

* `Work.Drive.Mono.BoxGen ψ c σ s` (box genericity: face regularity at `±s`, `CornerGen`,
  `VertexGen`, the box-norm level set locally Euclidean and the box sphere transverse to the
  surface — the a.e. statement `Work.Drive.Mono.ae_boxGen` is proved);
* `ℓ (e_{σ i}) ≠ 0` for every `i` (so that the *boundary* dents of `BoundaryDentDatum` can be found:
  they need a direction with `⟪v,·⟫ = 0` and `ℓ d ≠ 0`, which exists iff `ℓ` does not kill `v^⊥`);
* **no `IsEvent` on a slab face** (an event of the sweep is strictly inside the slab), so the face
  case of the gates is only about the new `IsFaceEvent`;
* **face-event nondegeneracy**: at every `IsFaceEvent` the *constrained* second derivative
  `fderiv (fderiv (sweepHeight - t·slabFnPar))` is nonzero on the face-tangent direction (`t` the
  tangency multiplier).  Without it the region can have infinitely many local components (the
  flat-function model of the review of `faceEventGates`);
* **triple-point regularity**: at every `IsTriplePoint` the sweep height is a submersion.  Without it
  a degenerate critical point gives three sectors, i.e. three local components, and two gates cannot
  cover them (the review of `tripleGates`).

Still to be added (the lead's L1 list): `EdgeFree` (the closed slab misses the edge trace), `CFree`
(`ℓ` has no critical point on the edge trace in the closed slab), `hfaceReg` (the face regularity of
the corrected `JunctionGen`), the `AllEvents` finset of events of the three types with
`exc = ℓ '' AllEvents`, and `offK` for all three types.  -/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- **The data of a good tilted sweep, first version with the event types of the (L) route.**  See
the module docstring for the clauses and for those still to be added. -/
def GoodSweepData2 (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  Work.Drive.Final.GoodSweepData ψ K s c σ u v h R ℓ exc lam0 lam1 ∧
  Work.Drive.Mono.BoxGen ψ c σ s ∧
  (∀ i : Fin 3, ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0) ∧
  (∀ p : ℝ × ℝ, Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p →
    |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| < h) ∧
  (∀ p : ℝ × ℝ, Work.Drive.Final.IsFaceEvent ψ s c σ u v h ℓ p →
    ∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p =
        t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p ∧
      ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p w = 0 →
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
          Work.Drive.EpsForm.sweepHeight ψ ℓ q - t * Work.Drive.Final.slabFnPar ψ c u v q)) p) w w
            ≠ 0) ∧
  (∀ p : ℝ × ℝ, Work.Drive.Final.IsTriplePoint ψ s c σ u v h p →
    fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0)

end

end Work.Drive.Final
