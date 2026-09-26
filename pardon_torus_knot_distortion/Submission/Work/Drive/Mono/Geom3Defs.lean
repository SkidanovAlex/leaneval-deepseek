import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.Geom2Defs
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Final.AnyEventDefs

/-!
# The interface of the `BoxGenE` producer of the third data package

The definitions shared by the deliverable `Work.Drive.Mono.goodSweepGeom3_holds`
(`Submission/Work/Drive/Mono/goodSweepGeom3_holds.lean`) and its delegated producer
`Work.Drive.Mono.geom3Data_exists` (`Submission/Work/Drive/Mono/geom3Data_exists.lean`):

* `Work.Drive.Mono.G3Extra` — the clauses of `Work.Drive.Final.GoodSweepData3` beyond
  `Work.Drive.Final.GoodSweepData2` (none of them mentions the exceptional set `exc`);
* `Work.Drive.Mono.Geom3Data` — `Work.Drive.Mono.Geom2DataPlus` together with `G3Extra` and the
  level count at *every* level of the window (the third conjunct of
  `Work.Drive.Mono.GoodDataPackage3`);
* `Work.Drive.Mono.Geom3DataExists` — the producer statement: for almost every cutting level `u`,
  with the crux hypotheses in force, there is tilt data satisfying `Geom3Data`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- **The clauses of `Work.Drive.Final.GoodSweepData3` beyond `Work.Drive.Final.GoodSweepData2`.**
These are the clauses of the corrected bundle that the earlier producer
(`Work.Drive.Mono.Geom2DataPlus`) does not deliver, and none of them mentions the exceptional set
`exc`:

* `Work.Drive.Mono.EdgeFree` — the closed slab misses the surface's part on the box edges;
* **SlabInBelt** — the surface's part of the closed slab stays strictly inside the box in the
  `σ 2` direction;
* the universal `Work.Drive.Mono.SlabBoxCrossReg` — at every triple point of a slab face with a
  vertical box face the two face curves cross transversally;
* **`GammaTransverse`** — at every point of the surface on the box sphere inside the closed slab the
  box-norm functional is a submersion and no multiple of its differential equals the differential of
  the sweep height;
* **`FaceRegClosed`** — the slab-face functional is a submersion on the surface's part of the closed
  slab;
* the **corner direction** — `ℓ (v × e_{σ i}) ≠ 0` for the two non-`σ 2` coordinates;
* `offK` for all three event types;
* *one event per level* for `Work.Drive.Final.IsAnyEvent`;
* `SphereCoverAt` at every level of the window. -/
def G3Extra (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) : Prop :=
  Work.Drive.Mono.EdgeFree ψ s c σ u v h ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
    z ∈ closure (Submission.PBox s c σ) → |Work.Drive.Final.slabFn c u v z| ≤ h →
    |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s) ∧
  Work.Drive.Mono.SlabBoxCrossReg ψ c σ s v (inner ℝ v c + u) h ∧
  (∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
    |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
    fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
    ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
      t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ) →
    |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h →
    fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p ≠ 0) ∧
  (∀ i : Fin 3, i ≠ 2 → ℓ (Work.Drive.Final.crossDir v (σ i)) ≠ 0) ∧
  (∀ p : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p →
    ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p) ∧
  (∀ p p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p →
    Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' →
    ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') →
    Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') ∧
  (∀ lam ∈ Set.Icc lam0 lam1, Work.Drive.Final.SphereCoverAt ψ s c σ u v h ℓ lam)

/-- **The datum delivered by the producer**: `Work.Drive.Mono.Geom2DataPlus` together with the
extra clauses `Work.Drive.Mono.G3Extra` and the level count at **every** level of the window (the
third conjunct of `Work.Drive.Mono.GoodDataPackage3`, produced by
`Work.Drive.Mono.levelCount_lt_min_all` from the non-grazing clauses of `Geom2Data`, the two crux
counts and `countConst · d < min p q`).  Neither `G3Extra` nor the unrestricted count mentions `exc`,
so both are transported unchanged when the exceptional set is enlarged. -/
def Geom3Data (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) (p q : ℕ) : Prop :=
  Geom2DataPlus ψ K s u c σ v h R ℓ exc lam0 lam1 p q ∧
  G3Extra ψ K s c σ u v h R ℓ lam0 lam1 ∧
  (∀ lam ∈ Set.Icc lam0 lam1,
    Set.encard (Set.range K.curve ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞))

/-- **The `BoxGenE` data producer of the corrected bundle, in the form delegated to
`Work.Drive.Mono.geom3Data_exists`.**  At every crux configuration — a knot `K` of distortion bound
`d` with `countConst · d < min p q`, an essential box `HasEssBox (torusOf ψ) r c σ` of size
`r < s < (1+ε) r`, the slicing of the box sphere at the level and the count `hS` of the knot on the
box sphere, and the box level `s` in general position for the junction route (`BoxGenE`) — for
almost every cutting level `u` with `|u| < ε r` and the plane count `hU` there are tilt data
`(v, h, R, ℓ, lam0, lam1, exc)` satisfying `Work.Drive.Mono.Geom2DataPlus` (the tilt data, the thin
slab, the window on the closed box, the face regularity, the trace arcs of the box sphere in the
closed slab, the non-grazing clauses of the knot, the level count off `exc`, `cornerSlab` and the
event clauses of `Work.Drive.Final.GoodSweepData2`) together with the extra clauses
`Work.Drive.Mono.G3Extra`.

The last hypothesis, `hsub : Set.range K.curve ⊆ (torusOf ψ).carrier`, ties the knot to the
surface: it is what makes the `offK` clauses (and their `IsAnyEvent` strengthening inside
`G3Extra`) reachable, through the proved tool
`Work.Drive.Mono.knot_deriv_of_sweepHeight_crit` (whose hypothesis is literally this
containment — a critical point of the sweep height on the surface is not on the knot because the
sweep height is constant along a lift of the knot).  In the caller
`Work.Drive.Mono.goodSweepGeom3_holds` it is derived from the crux hypothesis
`Set.range K.curve = Set.range (ClosedCurve.mapHomeomorph ψ.toHomeomorph (standardCurve p q)).γ`
and `Work.CoreTopology.ClosedCurve.range_subset_carrier`. -/
def Geom3DataExists : Prop :=
  ∀ (ψ : Submission.Diffeo) (K : Knot) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (d : ℝ) (hd : 0 ≤ d) (hbound : Work.Sweep.IsDistortionBound K d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c σ y = s})
    (hBG : Work.Drive.Mono.BoxGenE ψ c σ s)
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hsub : Set.range K.curve ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier),
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      |u| < Submission.eps * r →
      ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧
          (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
        ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
      ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
        Geom3Data ψ K s u c σ v h R ℓ exc lam0 lam1 p q


end

end Work.Drive.Mono
