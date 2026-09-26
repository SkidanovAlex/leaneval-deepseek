import Mathlib
import ChallengeDeps
import Submission.ChordFamily
import Submission.SecantDisk

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-!
# Layer A1 — the chord-family disk over a band arc, as a spanning square

`ChordFamily.lean` constructs the chord-family disk `chordFamilyDisk r d`
over a `BandArcData` and proves its edge conditions and its `O`-avoidance
corollary (interior avoids the knot when the arc avoids the trisecant set).
This module packages that square into the disk-interface consumed by the
Dehn-lemma bridge of `SecantDisk.lean`:

* `bandArcPathA h d` / `bandArcPathB h d` — the two knot arcs traced by the
  `a`- and `b`-branches of the arc datum (paths on the knot image between
  the collapsed endpoints; the `b`-path is typed with the `a`-endpoints,
  equal by the collapse conditions);
* **`bandArcDisk_bounds`** — if the arc avoids `O` at every interior
  parameter (`mobiusCover ⟨(a s, b s), offdiag⟩ ∉ trisecantSet r`), then
  `chordFamilyDisk r d` realises `PathsBoundDiskInteriorFree
  (range (knotMap r)) (bandArcPathA h d) (bandArcPathB h d)`: bottom and
  top edges are the two knot arcs, the vertical edges are pinned at the
  collapsed endpoint knot points, and every interior point of the square is
  mapped outside the knot.

Combined with `ChordFamily.bandArc_lift` (a class family `A` realises a
`BandArcData` with `arcClosedClass d = A`), any band-arc class family
avoiding `O` gives the spanning disk between its two knot arcs.
**`classBandArc_disk_bounds`** packages exactly that: a continuous class
family `A` (diagonal ends `u`,`v`, off-diagonal and `O`-avoiding interior)
yields a `BandArcData` (lift) and hence two knot arcs
`γ δ : Path (knotMap r u) (knotMap r v)` bounding a disk whose interior
avoids the knot — `PathsBoundDiskInteriorFree (range (knotMap r)) γ δ`.
-/

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-- The knot arc traced by the `a`-branch of a band-arc datum (a path on the
knot from the collapsed left endpoint to the collapsed right endpoint). -/
noncomputable def bandArcPathA {r : ℝ → Space} (h : IsSmoothKnot r) (d : BandArcData) :
    Path (knotMap r (d.a (0 : I))) (knotMap r (d.a (1 : I))) :=
  Path.mk (ContinuousMap.mk (fun s : I => knotMap r (d.a s)) (h.knotMap_continuous.comp d.cont_a))
    rfl rfl

/-- The knot arc traced by the `b`-branch, typed with the same endpoints as
the `a`-branch (the branches coincide at the ends of the arc). -/
noncomputable def bandArcPathB {r : ℝ → Space} (h : IsSmoothKnot r) (d : BandArcData) :
    Path (knotMap r (d.a (0 : I))) (knotMap r (d.a (1 : I))) :=
  Path.mk (ContinuousMap.mk (fun s : I => knotMap r (d.b s)) (h.knotMap_continuous.comp d.cont_b))
    (by simpa using congrArg (knotMap r) d.collapse_left.symm)
    (by simpa using congrArg (knotMap r) d.collapse_right.symm)

/-- **The chord-family disk over a band arc (Layer-A1 package).**  If the arc
avoids the trisecant set `O` at every interior parameter, the square
`chordFamilyDisk r d` is a disk bounded by the two knot arcs `bandArcPathA`
and `bandArcPathB` (bottom/top edges), with the vertical edges pinned at the
collapsed endpoints and with interior avoiding the knot — i.e.
`PathsBoundDiskInteriorFree (range (knotMap r)) (bandArcPathA h d)
(bandArcPathB h d)`.  This is the disk that Layer B's Dehn-lemma bridge
consumes. -/
theorem bandArcDisk_bounds {r : ℝ → Space} (h : IsSmoothKnot r) (d : BandArcData)
    (havoid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r) :
    PathsBoundDiskInteriorFree (Set.range (knotMap r)) (bandArcPathA h d) (bandArcPathB h d) := by
  refine ⟨ContinuousMap.mk (fun p : I × I => chordFamilyDisk r d p)
      (continuous_chordFamilyDisk h d), ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    change chordFamilyDisk r d (s, (0 : I)) = knotMap r (d.a s)
    exact chordFamilyDisk_t0 d s
  · intro s
    change chordFamilyDisk r d (s, (1 : I)) = knotMap r (d.b s)
    exact chordFamilyDisk_t1 d s
  · intro t
    change chordFamilyDisk r d ((0 : I), t) = knotMap r (d.a (0 : I))
    exact chordFamilyDisk_s0 d t
  · intro t
    change chordFamilyDisk r d ((1 : I), t) = knotMap r (d.a (1 : I))
    exact chordFamilyDisk_s1 d t
  · intro u v hu0 hu1 hv0 hv1
    exact chordFamilyDisk_interior_avoids_knot_of_avoids_O d havoid u v hu0 hu1 hv0 hv1


/-- **Class-level band arc realising the lifted disk (interface glue).**
  A class family `A : I → UnordCirclePairs` that is continuous, diagonal at
  the ends (`u`,`v`), off-diagonal and `O`-avoiding on the interior yields a
  `BandArcData`, hence two knot arcs `γ δ : Path (knotMap u) (knotMap v)`
  (the lifts of the `a`/`b` branches) bounding a disk whose interior avoids
  the knot.  This is the full chord-family disk construction in its
  class-level form: `PathsBoundDiskInteriorFree (range (knotMap r)) γ δ`. -/
theorem classBandArc_disk_bounds {r : ℝ → Space} (h : IsSmoothKnot r) {u v : AddCircle period}
    {A : I → UnordCirclePairs} (hA : Continuous A)
    (h0 : A (0 : I) = diagClass u) (h1 : A (1 : I) = diagClass v)
    (hopen : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → ¬ ∃ a : AddCircle period, A s = diagClass a)
    (havoid : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      (⟨A s, hopen s hs0 hs1⟩ : OpenMobius) ∉ trisecantSet r) :
    ∃ γ δ : Path (knotMap r u) (knotMap r v),
      PathsBoundDiskInteriorFree (Set.range (knotMap r)) γ δ := by
  rcases bandArc_lift (A := A) hA h0 h1 hopen with ⟨d, hda0, hdb0, hda1, hdb1, hcls⟩
  let γ : Path (knotMap r u) (knotMap r v) :=
    Path.mk (ContinuousMap.mk (fun s : I => knotMap r (d.a s)) (h.knotMap_continuous.comp d.cont_a))
      (by simpa using congrArg (knotMap r) hda0)
      (by simpa using congrArg (knotMap r) hda1)
  let δ : Path (knotMap r u) (knotMap r v) :=
    Path.mk (ContinuousMap.mk (fun s : I => knotMap r (d.b s)) (h.knotMap_continuous.comp d.cont_b))
      (by simpa using congrArg (knotMap r) hdb0)
      (by simpa using congrArg (knotMap r) hdb1)
  have havoid' : ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r := by
    intro s hs0 hs1 h
    have heq : mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ =
        (⟨A s, hopen s hs0 hs1⟩ : OpenMobius) := by
      apply Subtype.ext
      simpa [mobiusCover, unordOfOrdered, arcClosedClass] using hcls s
    apply havoid s hs0 hs1
    simpa [heq] using h
  refine ⟨γ, δ, ?_⟩
  refine ⟨ContinuousMap.mk (fun p : I × I => chordFamilyDisk r d p)
      (continuous_chordFamilyDisk h d), ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    change chordFamilyDisk r d (s, (0 : I)) = knotMap r (d.a s)
    exact chordFamilyDisk_t0 d s
  · intro s
    change chordFamilyDisk r d (s, (1 : I)) = knotMap r (d.b s)
    exact chordFamilyDisk_t1 d s
  · intro t
    change chordFamilyDisk r d ((0 : I), t) = knotMap r u
    simpa [hda0] using chordFamilyDisk_s0 d t
  · intro t
    change chordFamilyDisk r d ((1 : I), t) = knotMap r v
    simpa [hda1] using chordFamilyDisk_s1 d t
  · intro u' v' hu0 hu1 hv0 hv1
    exact chordFamilyDisk_interior_avoids_knot_of_avoids_O d havoid' u' v' hu0 hu1 hv0 hv1

end LeanEval.KnotTheory.Quadrisecant
