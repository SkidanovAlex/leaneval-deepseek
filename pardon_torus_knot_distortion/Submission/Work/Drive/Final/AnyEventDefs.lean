import Mathlib
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.InnermostDisk.Defs
import Submission.Work.Drive.Final.GoodSweepData2

/-!
# The three event types of the tilted sweep, and the bundle of the (L) route

(Project lead, `Final/NOTES_LEAD_L4_L1.md` §1, §2, §4.)

The exceptional levels of the tilted sweep are the levels of one of

* `Work.Drive.Final.IsEvent` — a critical point of the sweep height in `PBox ∩ slabClosed`;
* `Work.Drive.Final.IsFaceEvent` — a tangency of the level with a **slab face** inside the box;
* `Work.Drive.Final.IsCornerEvent` — a point of the surface on the **box sphere** (`boxNorm = s`,
  i.e. on the cone of a vertical box face) which also lies on a **slab face**.

The third type replaces the `IsTriplePoint` (box *edge* ∩ slab face) of the earlier design: under
`Work.Drive.Mono.EdgeFree` a box-edge point of the surface lies strictly outside the closed slab, so
`IsTriplePoint` is **empty**; the honest third type is the corner, with *one* vertical face active.

This module carries only the vocabulary (the event types, the corner push direction, the sphere cover
of a level, the bundle `GoodSweepData3`, and the dent datum `AnyDentDatum` whose event may be of any
of the three types).  The producers and the geometric lemmas live in their own files.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

/-! ## The event types -/

/-- **A corner event** of the tilted sweep: a point of the surface in the closure of the box, on the
box sphere (`boxNorm c σ · = s`, i.e. on a vertical face's closure), and on a slab face.  This is the
third event type of the design; under `EdgeFree` it is the only boundary event besides `IsFaceEvent`. -/
def IsCornerEvent (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (p : ℝ × ℝ) : Prop :=
  Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ) ∧
    Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s ∧
    |slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h

/-- **Any event** of the tilted sweep: one of the three types. -/
def IsAnyEvent (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) : Prop :=
  IsEvent ψ s c σ u v h ℓ p ∨ IsFaceEvent ψ s c σ u v h ℓ p ∨ IsCornerEvent ψ s c σ u v h p

/-- **The corner push direction**: `v × e_k` in coordinates.  At a corner whose active vertical face
is the `σ k`-th (i.e. `k` is the free coordinate), `± v × e_{σ k}` is tangent to that vertical face
(its `σ k`-component vanishes) and tangent to the slab faces (`⟂ v`), which is what the corner dent
requires. -/
def crossDir (v : R3) (k : Fin 3) : R3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (if k = 0 then ![(0 : ℝ), v.ofLp 2, -(v.ofLp 1)]
     else if k = 1 then ![-(v.ofLp 2), (0 : ℝ), v.ofLp 0]
     else ![v.ofLp 1, -(v.ofLp 0), (0 : ℝ)])

/-! ## The sphere cover of a level -/

/-- **The level frontier is covered by embedded spheres, disjoint on the surface.**  This is the
geometric input `SphereCoverAt` of the design: the frontier of the level's removed set is a finite
union of embedded spheres, any two of which meet at most off the surface.  (The `LevelSphereDecomposition`
of the `DataPackage` route asks for ambient disjointness; the pinch variant used here asks only for
`Disjoint` of the traces on the carrier, which is all the slicing argument consumes.) -/
def SphereCoverAt (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Prop :=
  ∃ (n : ℕ) (Ss : Fin n → Set R3),
    (∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i)) ∧
    (∀ i j : Fin n, i ≠ j →
      Disjoint (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
        (Ss j ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) ∧
    frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, Ss i

/-! ## The bundle `GoodSweepData3` -/

/-- **The bundle of the (L) route** (lead's `NOTES_LEAD_L4_L1.md` §2): `GoodSweepData2` (the event
structure and the pinch genericity of the earlier design; its `IsTriplePoint` clause is vacuous under
`EdgeFree`) together with

* `Work.Drive.Mono.EdgeFree` — the closed slab misses the surface on the box edges;
* **SlabInBelt** — the surface's part of the closed slab stays strictly inside the box in the `σ 2`
  direction;
* the *universal* `Work.Drive.Mono.SlabBoxCrossReg` — at every triple point of a slab face with a
  vertical box face the two face curves cross transversally (the "one arm" condition that no pointwise
  clause can supply for flat `C^∞` data);
* **GammaTransverse** — at every point of the surface on the box sphere inside the closed slab, the
  box-norm functional is a submersion and *no* multiple of its differential equals the differential of
  the sweep height (`JunctionGenC` (a) without the "`∉ exc`" restriction; this is what makes the corner
  germ finite);
* **FaceRegClosed** — the slab-face functional is a submersion on the surface's part of the closed
  slab;
* **corner direction** — `ℓ (v × e_{σ i}) ≠ 0` for the two non-`σ 2` coordinates, so that the corner
  dent direction exists;
* **offK** for all three event types;
* **one event per level** for `IsAnyEvent` (route I);
* **`SphereCoverAt`** at every level of the window (H381's item 2, the pinch variant). -/
def GoodSweepData3 (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  Work.Drive.Final.GoodSweepData2 ψ K s c σ u v h R ℓ exc lam0 lam1 ∧
  Work.Drive.Mono.EdgeFree ψ s c σ u v h ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
    z ∈ closure (Submission.PBox s c σ) → |slabFn c u v z| ≤ h →
    |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s) ∧
  Work.Drive.Mono.SlabBoxCrossReg ψ c σ s v (inner ℝ v c + u) h ∧
  (∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
    |slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
    fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
    ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
      t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ) →
    |slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h →
    fderiv ℝ (slabFnPar ψ c u v) p ≠ 0) ∧
  (∀ i : Fin 3, i ≠ 2 → ℓ (crossDir v (σ i)) ≠ 0) ∧
  (∀ p : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p →
    ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p) ∧
  (∀ p p' : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p → IsAnyEvent ψ s c σ u v h ℓ p' →
    ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') →
    Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') ∧
  (∀ lam ∈ Set.Icc lam0 lam1, SphereCoverAt ψ s c σ u v h ℓ lam)

/-! ## The dent datum at an event of any type -/

/-- **The datum of a dent at an event of any of the three types** (the lead's `AnyDentDatum`).  It
mirrors `Work.Drive.Final.DentDatum`, with three differences forced by the fact that a face or corner
event lies on the *boundary* of the box:

* `isEvent : IsAnyEvent …` instead of `IsEvent …`;
* the cutoff is **non-negative** (`χ_nonneg`) — needed for the sign of the level shift to be
  controlled;
* instead of `support_subset` (which is impossible at a boundary point), the datum carries a
  **prescribed neighbourhood** `U ∋ centre` with `ball_sub : closedBall centre (r + δ) ⊆ U`, together
  with `box_pres` — the deformation preserves the open box *near the centre* (a point of the ball is
  in `PBox` iff its image is).  `knotAvoids` keeps the knot out of the support. -/
structure AnyDentDatum (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (U : Set R3) where
  /-- the cutoff function of the dent -/
  χ : ℝ → ℝ
  χ_cont : Continuous χ
  χ_zero_apply : χ 0 = 1
  χ_eq_zero : ∀ t : ℝ, 1 ≤ t → χ t = 0
  χ_le_one : ∀ t : ℝ, |χ t| ≤ 1
  /-- the cutoff is non-negative -/
  χ_nonneg : ∀ t : ℝ, 0 ≤ χ t
  /-- the cutoff is `1` on a neighbourhood of the centre -/
  χ_eq_one_near : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → χ t = 1
  χ_diff : Differentiable ℝ χ
  κ : ℝ
  κ_pos : 0 < κ
  χ_deriv_bound : ∀ t : ℝ, |deriv χ t| ≤ κ
  /-- the parameter-plane point of the event -/
  p : ℝ × ℝ
  /-- the event is an event of one of the three types -/
  isEvent : IsAnyEvent ψ s c σ u v h ℓ p
  /-- the (physical) centre of the dent -/
  centre : R3
  centre_eq : centre = Work.BoxShrink.Pinch.par ψ p
  /-- the direction of the push -/
  d : R3
  d_norm : ‖d‖ = 1
  d_orth_v : inner ℝ v d = 0
  push_pos : 0 < ℓ d
  /-- the radius of the dent -/
  r : ℝ
  r_pos : 0 < r
  /-- the depth of the dent -/
  a' : ℝ
  a'_pos : 0 < a'
  /-- the room of the box around the dent -/
  δ : ℝ
  δ_pos : 0 < δ
  /-- the depth is bounded by the room -/
  a'_le_δ : a' ≤ δ
  /-- the room around the centre is inside the prescribed neighbourhood `U` -/
  ball_sub : ∀ z : R3, ‖z - centre‖ ≤ r + δ → z ∈ U
  /-- the deformation preserves the open box near the centre -/
  box_pres : ∀ z : R3, ‖z - centre‖ ≤ r → (z ∈ Submission.PBox s c σ ↔
    dentDeform χ centre d r a' z ∈ Submission.PBox s c σ)
  /-- the knot avoids the support of the dent -/
  knotAvoids : ∀ t : ℝ, r ≤ ‖K.curve t - centre‖

/-- The deformation of an `AnyDentDatum`. -/
def AnyDentDatum.deform {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) : R3 → R3 :=
  dentDeform D.χ D.centre D.d D.r D.a'

/-- **The region of the dent, in its *preimage* form** (the lead's `Ω₁`,
`NOTES_LEAD_L4_L1.md` §0.1): the points of the surface lying in the interior of the *preimage* of
the level's removed set under the dent.  In the core this is the region at the *shifted* level
`ℓ D.centre - a'·ℓ d` — the handle attached, `⊇ X (ℓ D.centre)`.  This is the region the no-jump
argument runs on; the *image* form used earlier is circular (its strip clause needs the support ball
as an error set, and the essential loop then has to avoid the neck). -/
def dentOutRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) {K : Knot} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) : Set R3 :=
  (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ interior (D.deform ⁻¹'
    Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))

end

end Work.Drive.Final
