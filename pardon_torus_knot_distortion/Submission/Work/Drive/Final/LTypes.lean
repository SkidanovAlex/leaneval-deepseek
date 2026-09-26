import Mathlib
import Submission.Work.Drive.Final.DentDatum
import Submission.Work.Drive.Final.GoodSweepData

/-!
# The event types of the (L) route: face events, triple points, and boundary dents

(Project lead, `NOTES_LEAD_grazes_L.md`, 2026-09-26 04:45; tasks L1--L3.)

The exceptional levels of the tilted sweep are the levels of

* `Work.Drive.Final.IsEvent` — a critical point of the sweep height inside `PBox ∩ slabClosed`
  (the *interior* and *face* cases are proved: `Work.Drive.Final.eventGates`, with its two cases
  `interiorCaseGates` / `faceCaseGates`);
* `Work.Drive.Final.IsFaceEvent` — a point of the surface inside the box and **on a slab face** at
  which the level functional is *tangent* to the face (the level curve `{ℓ = ℓ p}` is tangent to the
  face curve `{|⟪v,·⟫ - (⟪v,c⟫+u)| = h}`): here the level trace degenerates without the sweep height
  being critical, so the gates have to be re-proved;
* `Work.Drive.Final.IsTriplePoint` — a point of the surface on a **box edge** (two face constraints
  active) which also lies on a **slab face**: the level trace meets the edge exactly at the slab face,
  and the dent has to preserve the box (hence the extra fields of `BoundaryDentDatum`).

The definitions here are pure vocabulary (`IsFaceEvent`, `IsTriplePoint`, `BoundaryDentDatum`); the
gate lemmas (`faceEventGates`, `tripleGates`) and the producer of a boundary dent at a triple point
are proved in their own files.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- The slab height functional `y ↦ ⟪v,y⟫ - (⟪v,c⟫ + u)`; the slab is `{|slabFn| ≤ h}`. -/
def slabFn (c : R3) (u : ℝ) (v : R3) : R3 → ℝ := fun y => inner ℝ v y - (inner ℝ v c + u)

/-- The slab height functional pulled back to the parameter plane. -/
def slabFnPar (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3) : ℝ × ℝ → ℝ :=
  fun q => slabFn c u v (Work.BoxShrink.Pinch.par ψ q)

@[simp] theorem slabFn_apply (c : R3) (u : ℝ) (v y : R3) :
    slabFn c u v y = inner ℝ v y - (inner ℝ v c + u) := rfl

@[simp] theorem slabFnPar_apply (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3) (q : ℝ × ℝ) :
    slabFnPar ψ c u v q = slabFn c u v (Work.BoxShrink.Pinch.par ψ q) := rfl

/-- **A face event** of the tilted sweep: a point of the surface, inside the box and on a slab face,
at which the level functional is *tangent* to the face — i.e. the differential of the sweep height is
a multiple of the differential of the slab height.  (`t = 0` is allowed: an ordinary event on a face
is a face event as well, and is already handled by `Work.Drive.Final.eventGates`, whose face case is
`Work.Drive.Final.faceCaseGates`.) -/
def IsFaceEvent (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) : Prop :=
  Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ ∧
    |slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h ∧
    ∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p =
      t • fderiv ℝ (slabFnPar ψ c u v) p

/-- **A triple point**: a point of the surface on a box *edge* (two face constraints active at the
box size `s`) which also lies on a **slab face**.  At such a point the level trace meets the edge
exactly at the slab face; the free direction of the edge is the one coordinate `k` with `k ≠ i, j`,
and a dent there must move along `d` with `d (σ k') = 0` for `k' ≠ k` (tangent to both active faces)
and `⟪v,d⟫ = 0` (tangent to the slab faces), so that the box is preserved. -/
def IsTriplePoint (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (p : ℝ × ℝ) : Prop :=
  (∃ i j : Fin 3, i ≠ j ∧
      |(Work.BoxShrink.Pinch.par ψ p) (σ i) - c (σ i)| = Submission.boxSide i * s ∧
      |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| = Submission.boxSide j * s) ∧
    |slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h

/-- **The datum of a dent at a boundary (triple) point.**  Same shape as `Work.Drive.Final.DentDatum`,
with the direction `d` tangent to the slab faces (`⟪v,d⟫ = 0`) and moving across the wall
(`0 < ℓ d`) — exactly as in the interior case, so that the proved `dent_slab_invariant` /
`dent_wall_shift` transport applies verbatim.

**Two fields the design note asks for are deliberately *not* here, and cannot be**: at a box edge
the free coordinate is a single index `k`, and

* `d (σ i) = 0` for every `i ≠ k` forces `d = ± e_{σ k}`, hence `⟪v,d⟫ = ± v (σ k)`, which vanishes
  only if `v (σ k) = 0` — false in general (for the tilt `v ≈ e_{σ 2}` it fails whenever the edge runs
  in the `σ 2` direction);
* consequently a dent tangent to *both* active box faces at once need not exist, and the deformation
  cannot be required to preserve `PBox` near the edge.

This is not a loss for the (L) argument: the region of the dented sweep is defined through the
*deformed removed set*, `P.carrier ∩ interior (D.deform '' tiltedLevelRemoved …)`, i.e. the side of
the *deformed* frontier (`Work.Drive.Final.dentRegion_union_strip`), so the dent moving the box near
the edge is intended.  The obstruction is recorded for the lead in
`Submission/Work/Drive/Final/NOTES_H330_L_state.md`. -/
structure BoundaryDentDatum (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) where
  /-- the cutoff function of the dent -/
  χ : ℝ → ℝ
  /-- the cutoff is continuous -/
  χ_cont : Continuous χ
  /-- the cutoff is `1` at the centre -/
  χ_zero_apply : χ 0 = 1
  /-- the cutoff vanishes beyond radius `1` -/
  χ_eq_zero : ∀ t : ℝ, 1 ≤ t → χ t = 0
  /-- the cutoff is bounded by `1` -/
  χ_le_one : ∀ t : ℝ, |χ t| ≤ 1
  /-- the parameter-plane point of the triple point -/
  p : ℝ × ℝ
  /-- the point is a triple point -/
  isTriple : IsTriplePoint ψ s c σ u v h p
  /-- the (physical) centre of the dent -/
  centre : R3
  /-- the centre is the image of the triple point -/
  centre_eq : centre = Work.BoxShrink.Pinch.par ψ p
  /-- the free coordinate direction of the edge (the one coordinate in which `d` may move) -/
  k : Fin 3
  /-- the radius of the dent -/
  r : ℝ
  /-- the radius is positive -/
  r_pos : 0 < r
  /-- the direction of the push -/
  d : R3
  /-- `d` is a direction -/
  d_norm : ‖d‖ = 1
  /-- `d` is tangent to the slab faces -/
  d_orth_v : inner ℝ v d = 0
  /-- the push crosses the wall -/
  push_pos : 0 < ℓ d
  /-- the depth of the dent -/
  a' : ℝ
  /-- the depth is positive -/
  a'_pos : 0 < a'
  /-- the room of the box around the dent -/
  δ : ℝ
  /-- the room is positive -/
  δ_pos : 0 < δ
  /-- the depth is bounded by the room -/
  a'_le_δ : a' ≤ δ
  /-- the radius of the dent is at most the distance from the centre to the knot (so that the dent
  fixes the knot pointwise); the producer chooses it via the proved
  `Work.Drive.Final.dent_knotAvoids_exists` -/
  knotAvoids : ∀ t : ℝ, r ≤ ‖K.curve t - centre‖

/-- The deformation of a `BoundaryDentDatum`. -/
def BoundaryDentDatum.deform {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (D : BoundaryDentDatum ψ K s c σ u v h R ℓ) : R3 → R3 :=
  dentDeform D.χ D.centre D.d D.r D.a'

end

end Work.Drive.Final
