/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Finiteness of the orbits of the edges of the chord graph

The chord graph `chordGraph D` (`Dunwoody/Track.lean`) has the pattern points `MidV D` as vertices,
two of them being adjacent when they are joined by a chord of a face of `Λ''`.  This file proves
that the action of `G` on the *oriented edges* of the chord graph has finitely many orbits
(`chordAdjOrbits`), which is one of the cocompactness inputs of `DESIGN_N13.md` §10.5.

The action on the edges is the one registered in `Dunwoody/AdjPairAction.lean`
(`instMulActionChordAdj`).

## The argument

Every chord of a face is the translate of a chord of a *base* face, i.e. of a face based at the
identity: the face at `c` is the translate by `c` of the face at `1` (`faceVisits_smul`) and the
pairing into chords is translation invariant (`chords_smul`), a face being indexed by a relator
(`P.rel`, a finite set).  Therefore the *ordered* pairs of pattern points that are chords of some
face are covered by the finitely many chords of the finitely many base faces:

    ChordIdx D = Σ r : P.rel, {pq : ℕ × ℕ // pq or pq.swap is a chord of the base face of r}.

Sending such an index to the corresponding pair of visits of the base face gives a surjection of
`ChordIdx D` onto the orbits of the ordered chord pairs (`chordIdx_pair_surj`), whence the orbit
quotient of the ordered chord pairs is finite (`finite_orbits_chordAdjPair`).  The oriented edges
of the chord graph are the ordered chord pairs with distinct entries, and the inclusion is
injective and equivariant, so finiteness descends along it (`finite_orbits_of_injective`); this is
the target `chordAdjOrbits`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.AdjPairAction
import Submission.Work.ORDunwoody.finite_orbits_track
import Submission.Work.ORDunwoody.ChordWalk.cwc_chords_positions
import Submission.Work.ORDunwoody.finite_orbits_of_injective

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-! ## The chords of a base face

A face of `Λ''` is indexed by a relator `r ∈ P.rel` and a base point `c : G`
(`Dunwoody/FaceWalk.lean`).  The *base face* of `r` is the face at the identity, its visits are
the pattern points on its boundary walk and its chords are the pairs produced by
`Dunwoody.chords`. -/

/-- The chords of the base face of a relator. -/
abbrev baseChords (D : GeoData T t₀ P) (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) :
    List (ℕ × ℕ) :=
  chords (faceVisits D 1 (FreeGroup.toWord r.1))

/-- The chords of the base face of a relator, together with the same pairs read backwards: this is
the index set for the chords occurring in *all* the faces, since a chord of a face may be met in
either orientation. -/
abbrev baseChordSet (D : GeoData T t₀ P) (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) :
    Finset (ℕ × ℕ) :=
  (baseChords D r).toFinset ∪ ((baseChords D r).map Prod.swap).toFinset

theorem mem_baseChordSet_iff {r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}} {pq : ℕ × ℕ} :
    pq ∈ baseChordSet D r ↔ pq ∈ baseChords D r ∨ pq.swap ∈ baseChords D r := by
  rw [baseChordSet, Finset.mem_union, List.mem_toFinset, List.mem_toFinset, List.mem_map]
  constructor
  · rintro (h | ⟨x, hx, hxs⟩)
    · exact Or.inl h
    · refine Or.inr ?_
      rw [← hxs, Prod.swap_swap]
      exact hx
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨pq.swap, h, rfl⟩

/-- **The finite index set of the chords of the base faces**: a relator and a pair of positions in
the base face of that relator that is a chord of that face, in one of the two orientations. -/
abbrev ChordIdx (D : GeoData T t₀ P) : Type :=
  Σ r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}, {pq : ℕ × ℕ // pq ∈ baseChordSet D r}

/-- The pair of positions selected by an index. -/
def chordIdxPos (i : ChordIdx D) : ℕ × ℕ := i.2.1

theorem chordIdxPos_mem (i : ChordIdx D) :
    chordIdxPos i ∈ baseChords D i.1 ∨ (chordIdxPos i).swap ∈ baseChords D i.1 :=
  mem_baseChordSet_iff.mp i.2.2

/-- The first position of the chord selected by an index is a position of the base face. -/
theorem chordIdxPos_fst_lt (i : ChordIdx D) :
    (chordIdxPos i).1 < (faceVisits D 1 (FreeGroup.toWord i.1.1)).length := by
  rcases chordIdxPos_mem i with h | h
  · exact (Work.ORDunwoody.ChordWalk.cwc_chords_positions (D := D) h).2.1
  · exact (Work.ORDunwoody.ChordWalk.cwc_chords_positions (D := D) h).2.2.1

/-- The second position of the chord selected by an index is a position of the base face. -/
theorem chordIdxPos_snd_lt (i : ChordIdx D) :
    (chordIdxPos i).2 < (faceVisits D 1 (FreeGroup.toWord i.1.1)).length := by
  rcases chordIdxPos_mem i with h | h
  · exact (Work.ORDunwoody.ChordWalk.cwc_chords_positions (D := D) h).2.2.1
  · exact (Work.ORDunwoody.ChordWalk.cwc_chords_positions (D := D) h).2.1

/-- **The pair of pattern points attached to an index**: the two visits of the base face at the
selected pair of positions. -/
noncomputable def chordIdxPair (i : ChordIdx D) : MidV D × MidV D :=
  ((faceVisits D 1 (FreeGroup.toWord i.1.1))[(chordIdxPos i).1]'(chordIdxPos_fst_lt i),
   (faceVisits D 1 (FreeGroup.toWord i.1.1))[(chordIdxPos i).2]'(chordIdxPos_snd_lt i))

/-- The pair attached to an index is (the two ends of) a chord of the base face. -/
theorem chordAdj_chordIdxPair (i : ChordIdx D) :
    ChordAdj (chordIdxPair i).1 (chordIdxPair i).2 := by
  refine ⟨i.1, 1, (chordIdxPos i).1, (chordIdxPos i).2, ?_, ?_, ?_⟩
  · rcases chordIdxPos_mem i with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact List.getElem?_eq_getElem (chordIdxPos_fst_lt i)
  · exact List.getElem?_eq_getElem (chordIdxPos_snd_lt i)

/-! ## The ordered chord pairs -/

/-- The ordered pairs of pattern points that are chords of some face. -/
abbrev chordAdjPair (D : GeoData T t₀ P) : Type u :=
  {p : MidV D × MidV D // ChordAdj p.1 p.2}

noncomputable instance instMulActionChordAdjPair : MulAction G (chordAdjPair D) where
  smul g p := ⟨(g • p.1.1, g • p.1.2), ChordAdj_smul g p.2⟩
  one_smul p := Subtype.ext (Prod.ext (one_smul G p.1.1) (one_smul G p.1.2))
  mul_smul g h p := Subtype.ext (Prod.ext (mul_smul g h p.1.1) (mul_smul g h p.1.2))

/-- **Every ordered chord pair is a translate of one attached to an index.**  If `(m, m')` are the
two ends of a chord of the face at `c`, then the corresponding chord of the base face of the same
relator translates back to `(m, m')` (`faceVisits_smul`, `chords_smul`). -/
theorem chordIdx_pair_surj (x : chordAdjPair D) :
    ∃ i : ChordIdx D, MulAction.orbitRel G (chordAdjPair D) x
      (⟨chordIdxPair i, chordAdj_chordIdxPair i⟩ : chordAdjPair D) := by
  obtain ⟨⟨m, m'⟩, h⟩ := x
  obtain ⟨r, c, a, b, hpq, hm, hm'⟩ := h
  -- a face at `c` is the `c`-translate of the base face of the same relator
  have hfs : faceVisits D c (FreeGroup.toWord r.1) =
      (faceVisits D 1 (FreeGroup.toWord r.1)).map (fun v => c • v) := by
    have h0 := Work.ORDunwoody.faceVisits_smul (D := D) c 1 (FreeGroup.toWord r.1)
    rwa [mul_one] at h0
  have hpqL : (a, b) ∈ baseChords D r ∨ (b, a) ∈ baseChords D r := by
    rw [hfs, Work.ORDunwoody.chords_smul] at hpq
    exact hpq
  have hmem : (a, b) ∈ baseChordSet D r := by
    rw [mem_baseChordSet_iff]
    rcases hpqL with h | h
    · exact Or.inl h
    · exact Or.inr (by rwa [Prod.swap_prod_mk])
  have ha : a < (faceVisits D 1 (FreeGroup.toWord r.1)).length := by
    rcases hpqL with h | h
    · exact (Work.ORDunwoody.ChordWalk.cwc_chords_positions (D := D) h).2.1
    · exact (Work.ORDunwoody.ChordWalk.cwc_chords_positions (D := D) h).2.2.1
  have hb : b < (faceVisits D 1 (FreeGroup.toWord r.1)).length := by
    rcases hpqL with h | h
    · exact (Work.ORDunwoody.ChordWalk.cwc_chords_positions (D := D) h).2.2.1
    · exact (Work.ORDunwoody.ChordWalk.cwc_chords_positions (D := D) h).2.1
  -- the two visits of the base face are the `c`-preimages of `m` and `m'`
  have hma : c • (faceVisits D 1 (FreeGroup.toWord r.1))[a]'ha = m := by
    have h1 := hm
    rw [hfs, List.getElem?_map, List.getElem?_eq_getElem ha, Option.map_some] at h1
    exact Option.some.inj h1
  have hmb : c • (faceVisits D 1 (FreeGroup.toWord r.1))[b]'hb = m' := by
    have h1 := hm'
    rw [hfs, List.getElem?_map, List.getElem?_eq_getElem hb, Option.map_some] at h1
    exact Option.some.inj h1
  refine ⟨⟨r, ⟨(a, b), hmem⟩⟩, ?_⟩
  have hpair : chordIdxPair (⟨r, ⟨(a, b), hmem⟩⟩ : ChordIdx D) =
      ((faceVisits D 1 (FreeGroup.toWord r.1))[a]'ha,
        (faceVisits D 1 (FreeGroup.toWord r.1))[b]'hb) := rfl
  have hkey : c • chordIdxPair (⟨r, ⟨(a, b), hmem⟩⟩ : ChordIdx D) = (m, m') := by
    rw [hpair, Prod.smul_mk]
    exact Prod.ext hma hmb
  rw [MulAction.orbitRel_apply]
  exact MulAction.mem_orbit_iff.mpr ⟨c, Subtype.ext hkey⟩

/-- **Finiteness of the orbit quotient of the ordered chord pairs.** -/
theorem finite_orbits_chordAdjPair :
    Finite (MulAction.orbitRel.Quotient G (chordAdjPair D)) := by
  refine Finite.of_surjective
    (fun i : ChordIdx D => (Quotient.mk (MulAction.orbitRel G (chordAdjPair D))
      (⟨chordIdxPair i, chordAdj_chordIdxPair i⟩ : chordAdjPair D))) ?_
  intro q
  refine Quotient.inductionOn q (fun x => ?_)
  obtain ⟨i, hi⟩ := chordIdx_pair_surj x
  exact ⟨i, (Quotient.sound hi).symm⟩

/-! ## The target

The oriented edges of the chord graph are the ordered chord pairs with distinct entries; the
inclusion is injective and equivariant. -/

/-- The oriented edges of the chord graph, as ordered chord pairs. -/
def chordEdgeToPair :
    {p : MidV D × MidV D // (chordGraph D).Adj p.1 p.2} → chordAdjPair D :=
  fun e => ⟨e.1, e.2.1⟩

theorem chordEdgeToPair_injective : Function.Injective (chordEdgeToPair (D := D)) := by
  intro e1 e2 h
  refine Subtype.ext ?_
  exact congrArg (fun x : chordAdjPair D => x.1) h

theorem chordEdgeToPair_smul (g : G)
    (e : {p : MidV D × MidV D // (chordGraph D).Adj p.1 p.2}) :
    chordEdgeToPair (D := D) (g • e) = g • chordEdgeToPair (D := D) e := by
  refine Subtype.ext ?_
  rfl

theorem chordAdjOrbits {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} :
    Finite (MulAction.orbitRel.Quotient G
      {p : Work.ORDunwoody.Dunwoody.MidV D × Work.ORDunwoody.Dunwoody.MidV D //
        (Work.ORDunwoody.Dunwoody.chordGraph D).Adj p.1 p.2}) :=
  Work.ORDunwoody.finite_orbits_of_injective (X := chordAdjPair D)
    (finite_orbits_chordAdjPair (D := D))
    (chordEdgeToPair (D := D))
    (chordEdgeToPair_injective (D := D))
    (chordEdgeToPair_smul (D := D))

end Work.ORDunwoody.Dunwoody
