/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The chord graph is locally finite

`Dunwoody/Track.lean` defines the chord graph on the pattern points `MidV D` of `Λ''`: two pattern
points are adjacent when they are the two ends of a chord of a common face.  This file proves that
every pattern point has only finitely many chord neighbours,

    {m' | ChordAdj m m'}.Finite,

which is the local finiteness input for the finite generation of the track stabilisers
(`Dunwoody/TrackGraph.lean`).

## The argument

Every ordered chord pair is the translate of a chord of a *base* face: that is the theorem
`chordIdx_pair_surj` of `Dunwoody/chordAdjOrbits.lean`, which produces an index

    i : ChordIdx D = Σ r : P.rel, {pq : ℕ × ℕ // pq is a chord of the base face of r}

and a group element `c` with `c • (chordIdxPair i).1 = m` and `c • (chordIdxPair i).2 = m'`.

The point is that `c` is **determined** by `m` and by the first visit of the index: the pattern
points are `G × MidIdx D` with the action on the first factor, so `c • v = m` forces
`c = m.1 * v.1⁻¹`.  Hence the neighbour `m'` is the value at `i` of the *single* well defined
candidate

    i ↦ (m.1 * ((chordIdxPair i).1).1⁻¹) • (chordIdxPair i).2 ,

and the index set `ChordIdx D` is finite (a relator of the finite presentation together with a
chord of its base face).  The neighbours of `m` therefore form the range of a map on a finite type.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.TrackWall
import Submission.Work.ORDunwoody.Dunwoody.chordAdjOrbits

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley
open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-- The action of `G` on the pattern points is free, so a group element carrying a pattern point
`v` to a pattern point `m` is *uniquely* determined: it is `m.1 * v.1⁻¹`. -/
private lemma eq_mul_inv_of_smul_eq {m v : MidV D} {c : G} (h : c • v = m) :
    c = m.1 * v.1⁻¹ := by
  have h1 : c * v.1 = m.1 := congrArg Prod.fst h
  calc c = c * v.1 * v.1⁻¹ := by group
    _ = m.1 * v.1⁻¹ := by rw [h1]

/-- **The chord graph is locally finite.**  A pattern point has only finitely many chord
neighbours: they are the translates of the finitely many chords of the base faces, the translating
group element being determined by the point itself. -/
theorem chordAdj_neighbors_finite {G : Type u} [Group G] {V : Type u} [MulAction G V]
    [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} {m : Work.ORDunwoody.Dunwoody.MidV D} :
    {m' : Work.ORDunwoody.Dunwoody.MidV D |
      Work.ORDunwoody.Dunwoody.ChordAdj m m'}.Finite := by
  classical
  -- the candidate neighbour attached to an index, for the fixed point `m`
  let f : ChordIdx D → MidV D := fun i =>
    (m.1 * ((chordIdxPair i).1).1⁻¹) • (chordIdxPair i).2
  refine Set.Finite.subset (Set.finite_range f) ?_
  rintro m' hm'
  -- find a chord of a base face of which `(m, m')` is a translate
  obtain ⟨i, hi⟩ := chordIdx_pair_surj (D := D) (⟨(m, m'), hm'⟩ : chordAdjPair D)
  rw [MulAction.orbitRel_apply] at hi
  obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp hi
  -- the translate carries the two ends of the base chord to `m` and `m'`
  have hc' : (c • (chordIdxPair i).1, c • (chordIdxPair i).2) = (m, m') :=
    Subtype.ext_iff.mp hc
  have hc1 : c • (chordIdxPair i).1 = m := congrArg Prod.fst hc'
  have hc2 : c • (chordIdxPair i).2 = m' := congrArg Prod.snd hc'
  -- `c` is determined by `m` and by the first end of the base chord
  refine ⟨i, ?_⟩
  have hci : c = m.1 * ((chordIdxPair i).1).1⁻¹ := eq_mul_inv_of_smul_eq hc1
  show (m.1 * ((chordIdxPair i).1).1⁻¹) • (chordIdxPair i).2 = m'
  rw [← hci]
  exact hc2

end Work.ORDunwoody
