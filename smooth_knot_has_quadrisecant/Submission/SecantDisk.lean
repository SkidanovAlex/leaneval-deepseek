import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.TrisecantClosed

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-!
# Layer A1 — the topologically trivial secant (definitional layer)

Kuperberg (Definition in §"Topological non-triviality"): *a secant of a link
`L` with no extra interior intersections with `L` is topologically trivial if
its endpoints lie on the same component of `L`, and if it, together with one
of the two arcs of this component, bounds a disk whose interior does not
intersect `L`.  The disk may intersect itself and the secant.*

This module fixes the formal meaning of that definition for a smooth knot
`r`, at the level of the chord (two parameters `a b` of the knot circle) and
the arc:

1. **`ChordInteriorFree r a b`** — "no extra interior intersections": no
   knot point lies strictly inside the open chord from `knotMap r a` to
   `knotMap r b` (`∀ m, ¬ IsMiddleOnOpenChord r a b m`).  Symmetric in the
   endpoints (`ChordInteriorFree_symm`).
2. **`chordPath r a b`** — the straight segment from `knotMap r a` to
   `knotMap r b` as a continuous `Path` (via `chordMap`, the affine
   interpolation; `range chordPath = segment ℝ (knotMap r a) (knotMap r b)`;
   reversing the chord gives the chord of the swapped endpoints:
   `chordPath_symm_eq : (chordPath r a b).symm = chordPath r b a`).
3. **`PathsBoundDiskInteriorFree K γ δ`** — two paths `γ δ : Path a b` (the
   two halves of the boundary) *bound a (possibly singular) disk whose
   interior avoids `K`*: a continuous map `D : I × I → Space` with
   `D(·,0) = γ` (bottom edge) and `D(·,1) = δ` (top edge), the two side
   edges pinned at the common endpoints `a` and `b`, and every *interior*
   point of the square (`u v ∉ {0,1}`) mapped outside `K`.  The boundary
   loop of this square disk is "`γ` then `δ` reversed" (the pinned side
   edges are degenerate), so this is the "bounds a disk whose interior
   avoids `L`" condition for the chord-and-arc loop; the map may
   self-intersect and may meet the chord — only `K` is excluded from the
   interior.  Formulated on the square, every disk symmetry is an
   elementary reflection: `PathsBoundDiskInteriorFree_rev` (reflect across
   the vertical axis: both boundary paths reverse).
4. **`IsKnotArcPath r a b α`** — `α` is one of the two arcs of the knot
   from `knotMap r a` to `knotMap r b`: a simple path (injective) that
   stays on the knot image `Set.range (knotMap r)`.  Reversing an arc gives
   an arc of the swapped chord (`IsKnotArcPath_symm`).
5. **`ChordTrivialByArc r a b α` / `TrivialSecant r a b` /
   `NontrivialSecant r a b`** — the chord `(a,b)` is *topologically trivial*
   when it is interior-free and, with some knot arc `α` between its
   endpoints, the disk spanned by `α` and the chord has interior avoiding
   the knot; the existential over `α` is Kuperberg's "together with one of
   the two arcs".  **`TrivialSecant_swap`** (D1): triviality is symmetric
   in the endpoints — reverse the witnessing arc and reflect the square
   disk.

(For a knot — one component — the clause "endpoints lie on the same
component of `L`" is automatic and is not stated.)  Everything here is
elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- A chord of the knot between the parameters `a` and `b` has **no extra
interior intersections** with the knot: no knot point lies strictly inside
the open chord (Kuperberg's standing hypothesis on secants to which
triviality is attributed). -/
def ChordInteriorFree (r : ℝ → Space) (a b : AddCircle period) : Prop :=
  ∀ m : AddCircle period, ¬ IsMiddleOnOpenChord r a b m

/-- A chord-free interior is symmetric in the endpoints (the open segment is
symmetric). -/
lemma ChordInteriorFree_symm (r : ℝ → Space) (a b : AddCircle period)
    (h : ChordInteriorFree r a b) : ChordInteriorFree r b a := by
  intro m hm
  exact h m (by simpa [IsMiddleOnOpenChord, openSegment_symm] using hm)

/-- The chord map from the unit interval: the straight segment from
`knotMap r a` to `knotMap r b`. -/
noncomputable def chordMap (r : ℝ → Space) (a b : AddCircle period) : I → Space :=
  fun s : I => knotMap r a + (s : ℝ) • (knotMap r b - knotMap r a)

/-- The chord map starts at `knotMap r a`. -/
lemma chordMap_zero (r : ℝ → Space) (a b : AddCircle period) :
    chordMap r a b (0 : I) = knotMap r a := by
  simp [chordMap]

/-- The chord map ends at `knotMap r b`. -/
lemma chordMap_one (r : ℝ → Space) (a b : AddCircle period) :
    chordMap r a b (1 : I) = knotMap r b := by
  simp [chordMap]

/-- The chord map is continuous (it is affine in the interval parameter; the
knot endpoints are fixed points of space). -/
lemma continuous_chordMap (r : ℝ → Space) (a b : AddCircle period) :
    Continuous (chordMap r a b) := by
  unfold chordMap
  have hval : Continuous (fun s : I => (s : ℝ)) := continuous_subtype_val
  have hsl : Continuous (fun s : I => (s : ℝ) • (knotMap r b - knotMap r a)) :=
    hval.smul continuous_const
  exact continuous_const.add hsl

/-- The chord as a path in space from `knotMap r a` to `knotMap r b`. -/
noncomputable def chordPath (r : ℝ → Space) (a b : AddCircle period) :
    Path (knotMap r a) (knotMap r b) :=
  Path.mk (ContinuousMap.mk (chordMap r a b) (continuous_chordMap r a b))
    (by simpa using chordMap_zero r a b)
    (by simpa using chordMap_one r a b)

/-- The chord map agrees with the affine line map. -/
lemma chordMap_eq_lineMap (r : ℝ → Space) (a b : AddCircle period) (s : I) :
    chordMap r a b s = AffineMap.lineMap (knotMap r a) (knotMap r b) (s : ℝ) := by
  simp [chordMap, AffineMap.lineMap_apply]
  abel

/-- The range of the chord map is exactly the closed segment in space between
the two knot points. -/
lemma range_chordMap_eq_segment (r : ℝ → Space) (a b : AddCircle period) :
    Set.range (chordMap r a b) = segment ℝ (knotMap r a) (knotMap r b) := by
  ext w
  constructor
  · rintro ⟨s, hs⟩
    rw [← hs]
    exact (mem_segment_iff_lineMap).mpr ⟨s, chordMap_eq_lineMap r a b s⟩
  · intro hw
    rcases (mem_segment_iff_lineMap).mp hw with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (chordMap_eq_lineMap r a b s).trans hs.symm

/-- The range of the chord path is exactly the closed segment in space between
the two knot points. -/
lemma range_chordPath_eq_segment (r : ℝ → Space) (a b : AddCircle period) :
    Set.range (chordPath r a b : I → Space) = segment ℝ (knotMap r a) (knotMap r b) := by
  simpa [chordPath] using range_chordMap_eq_segment r a b

/-- Reversing the chord path gives the chord of the swapped endpoints. -/
lemma chordPath_symm_eq (r : ℝ → Space) (a b : AddCircle period) :
    (chordPath r a b).symm = chordPath r b a := by
  apply Path.ext
  funext t
  change chordMap r a b (unitInterval.symm t) = chordMap r b a t
  rw [chordMap_eq_lineMap, chordMap_eq_lineMap]
  have hσ : (unitInterval.symm t : ℝ) = 1 - (t : ℝ) := by simp
  rw [hσ, AffineMap.lineMap_apply_one_sub]

/-- Two paths `γ δ : Path a b` (the two halves of the boundary) **bound a
(possibly singular) disk whose interior avoids `K`**: a continuous map `D`
of the unit square with `D(·,0) = γ` (bottom edge) and `D(·,1) = δ` (top
edge), side edges pinned at the common endpoints, and every interior point
(`u v ∉ {0,1}`) mapped outside `K`.  The boundary loop of the square is the
loop "`γ` then `δ` reversed"; the map may self-intersect and may meet the
chord — only `K` is excluded from the interior. -/
def PathsBoundDiskInteriorFree {X : Type*} [TopologicalSpace X] (K : Set X) {a b : X}
    (γ δ : Path a b) : Prop :=
  ∃ D : C(I × I, X),
    (∀ s : I, D (s, (0 : I)) = γ s) ∧
    (∀ s : I, D (s, (1 : I)) = δ s) ∧
    (∀ t : I, D ((0 : I), t) = a) ∧
    (∀ t : I, D ((1 : I), t) = b) ∧
    ∀ (u v : I), (u : ℝ) ≠ 0 → (u : ℝ) ≠ 1 → (v : ℝ) ≠ 0 → (v : ℝ) ≠ 1 →
      D (u, v) ∉ K

/-- Reflecting a square disk across the vertical axis reverses both boundary
paths: if `γ` and `δ` bound a disk whose interior avoids `K`, then so do
`γ.symm` and `δ.symm`. -/
lemma PathsBoundDiskInteriorFree_rev {X : Type*} [TopologicalSpace X] (K : Set X) {a b : X}
    (γ δ : Path a b) (hγδ : PathsBoundDiskInteriorFree K γ δ) :
    PathsBoundDiskInteriorFree K γ.symm δ.symm := by
  rcases hγδ with ⟨D, hbot, htop, hleft, hright, hint⟩
  let refl : I × I → I × I := fun p => (unitInterval.symm p.1, p.2)
  have hcont : Continuous refl := by
    dsimp [refl]
    fun_prop
  refine ⟨D.comp (ContinuousMap.mk refl hcont), ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    change D (unitInterval.symm s, (0 : I)) = γ.symm s
    rw [hbot]
    rfl
  · intro s
    change D (unitInterval.symm s, (1 : I)) = δ.symm s
    rw [htop]
    rfl
  · intro t
    change D (unitInterval.symm (0 : I), t) = b
    have hσ0 : unitInterval.symm (0 : I) = (1 : I) := by
      apply Subtype.ext
      simp
    rw [hσ0]
    exact hright t
  · intro t
    change D (unitInterval.symm (1 : I), t) = a
    have hσ1 : unitInterval.symm (1 : I) = (0 : I) := by
      apply Subtype.ext
      simp
    rw [hσ1]
    exact hleft t
  · intro u v hu0 hu1 hv0 hv1
    change D (unitInterval.symm u, v) ∉ K
    have hs0 : (unitInterval.symm u : ℝ) ≠ 0 := by
      have hσ : (unitInterval.symm u : ℝ) = 1 - (u : ℝ) := by simp
      intro hs
      apply hu1
      linarith
    have hs1 : (unitInterval.symm u : ℝ) ≠ 1 := by
      have hσ : (unitInterval.symm u : ℝ) = 1 - (u : ℝ) := by simp
      intro hs
      apply hu0
      linarith
    exact hint (unitInterval.symm u) v hs0 hs1 hv0 hv1

/-- A path in the knot from `knotMap r a` to `knotMap r b` that is one of the
**two arcs of the knot**: simple (injective — no backtracking, hence no
winding around the circle) and staying on the knot image. -/
def IsKnotArcPath (r : ℝ → Space) (a b : AddCircle period)
    (α : Path (knotMap r a) (knotMap r b)) : Prop :=
  Function.Injective α ∧ ∀ t : I, α t ∈ Set.range (knotMap r)

/-- Reversing a simple knot path gives a simple knot path between the swapped
endpoints. -/
lemma IsKnotArcPath_symm {r : ℝ → Space} {a b : AddCircle period}
    {α : Path (knotMap r a) (knotMap r b)} (hα : IsKnotArcPath r a b α) :
    IsKnotArcPath r b a α.symm := by
  constructor
  · -- α.symm = α ∘ σ with σ the involutive flip, so injective
    have hσ : Function.Injective (fun t : I => unitInterval.symm t) := by
      intro t u htu
      apply Subtype.ext
      have h1 := congrArg (fun z : I => (z : ℝ)) htu
      simp at h1
      linarith
    change Function.Injective (fun t : I => α (unitInterval.symm t))
    exact Function.Injective.comp hα.1 hσ
  · intro t
    exact hα.2 (unitInterval.symm t)

/-- The chord `(a,b)` is a **topologically trivial secant along the knot arc
`α`**: it has no extra interior intersections with the knot, `α` is a simple
knot path between the endpoints, and the chord and `α` bound a disk whose
interior avoids the knot (bottom edge `α`, top edge the chord). -/
def ChordTrivialByArc (r : ℝ → Space) (a b : AddCircle period)
    (α : Path (knotMap r a) (knotMap r b)) : Prop :=
  ChordInteriorFree r a b ∧ IsKnotArcPath r a b α ∧
    PathsBoundDiskInteriorFree (Set.range (knotMap r)) α (chordPath r a b)

/-- A secant (chord of two parameters) is **topologically trivial** if,
together with one of the two arcs of the knot between its endpoints, it
bounds a disk whose interior avoids the knot (Kuperberg's definition; the
existential over the simple knot path `α` expresses "one of the two arcs"). -/
def TrivialSecant (r : ℝ → Space) (a b : AddCircle period) : Prop :=
  ∃ α : Path (knotMap r a) (knotMap r b), ChordTrivialByArc r a b α

/-- A secant is **topologically non-trivial** when it is not trivial. -/
def NontrivialSecant (r : ℝ → Space) (a b : AddCircle period) : Prop :=
  ¬ TrivialSecant r a b

/-- A trivial secant's chord has no extra interior intersections. -/
lemma ChordTrivialByArc.interior_free {r : ℝ → Space} {a b : AddCircle period}
    {α : Path (knotMap r a) (knotMap r b)} (ht : ChordTrivialByArc r a b α) :
    ChordInteriorFree r a b := ht.1

/-- The arc of a trivial secant is a simple path on the knot. -/
lemma ChordTrivialByArc.arc_simple {r : ℝ → Space} {a b : AddCircle period}
    {α : Path (knotMap r a) (knotMap r b)} (ht : ChordTrivialByArc r a b α) :
    Function.Injective α := ht.2.1.1

/-- Every point of the arc of a trivial secant lies on the knot. -/
lemma ChordTrivialByArc.arc_mem_knot {r : ℝ → Space} {a b : AddCircle period}
    {α : Path (knotMap r a) (knotMap r b)} (ht : ChordTrivialByArc r a b α) {t : I} :
    α t ∈ Set.range (knotMap r) := ht.2.1.2 t

/-- The chord and the arc of a trivial secant bound an interior-free disk. -/
lemma ChordTrivialByArc.disk {r : ℝ → Space} {a b : AddCircle period}
    {α : Path (knotMap r a) (knotMap r b)} (ht : ChordTrivialByArc r a b α) :
    PathsBoundDiskInteriorFree (Set.range (knotMap r)) α (chordPath r a b) := ht.2.2

/-- Unpacking a trivial secant: some arc of the knot realises the
disk-bounding. -/
lemma TrivialSecant.some_arc {r : ℝ → Space} {a b : AddCircle period}
    (ht : TrivialSecant r a b) :
    ∃ α : Path (knotMap r a) (knotMap r b), ChordTrivialByArc r a b α := ht

/-- Unpacking: a trivial secant is interior-free along the witnessing arc. -/
lemma TrivialSecant.interior_free {r : ℝ → Space} {a b : AddCircle period}
    (ht : TrivialSecant r a b) : ChordInteriorFree r a b := by
  rcases ht with ⟨α, hα⟩
  exact hα.1

/-- **ChordTrivialByArc is symmetric**: if the chord `(a,b)` is trivial along
the knot arc `α`, then the chord `(b,a)` is trivial along the reversed arc
`α.symm`.  (The disk is reflected across the vertical axis: bottom edge
becomes `α.symm`, top edge becomes the reversed chord, i.e. `chordPath r b
a` by `chordPath_symm_eq`.) -/
lemma ChordTrivialByArc_swap {r : ℝ → Space} {a b : AddCircle period}
    {α : Path (knotMap r a) (knotMap r b)} (ht : ChordTrivialByArc r a b α) :
    ChordTrivialByArc r b a α.symm := by
  refine ⟨ChordInteriorFree_symm r a b ht.1, IsKnotArcPath_symm ht.2.1, ?_⟩
  -- reflect the disk across the vertical axis: the two boundary paths become
  -- α.symm and (chordPath r a b).symm; the latter is the chord (b,a)
  have hrev := PathsBoundDiskInteriorFree_rev (Set.range (knotMap r)) α (chordPath r a b) ht.2.2
  rw [← chordPath_symm_eq r a b]
  exact hrev

/-- **Triviality is symmetric in the chord endpoints (D1).**  A chord is
topologically trivial iff the same chord traversed the other way is. -/
lemma TrivialSecant_swap (r : ℝ → Space) (a b : AddCircle period) :
    TrivialSecant r a b ↔ TrivialSecant r b a := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α.symm, ChordTrivialByArc_swap hα⟩
  · rintro ⟨β, hβ⟩
    exact ⟨β.symm, ChordTrivialByArc_swap hβ⟩

/-- **Nontriviality is symmetric in the chord endpoints.** -/
lemma NontrivialSecant_swap (r : ℝ → Space) (a b : AddCircle period) :
    NontrivialSecant r a b ↔ NontrivialSecant r b a := by
  unfold NontrivialSecant
  exact not_congr (TrivialSecant_swap r a b)


/-! ## D2 — triviality of trisecants and of the middle secant of a
quadrisecant (data level)

Kuperberg's Definition continues: *A quadrisecant `ad` with middle points `b`
and `c` is topologically trivial if any of the secants `ab`, `bc`, and `cd`
are.  Similarly for a trisecant.*  Of the six sub-chords of a collinear
four-tuple only the three *consecutive* ones can be interior-free (the other
three contain a middle point strictly inside), which is why only `ab`, `bc`,
`cd` occur.  At the parameter level (chord endpoints `p q`, trisecant middle
`m`, quadrisecant middles `z w`) this is:

1. **`TrisecantTrivial r p q m`** — the trisecant chord `(p,q)` with middle
   `m` is trivial when one of its two endpoint-to-middle sub-chords `(p,m)`
   or `(m,q)` is a trivial secant (the analogue of `ab`, `bc` for a
   trisecant).
2. **`QuadrisecantMiddleSecantTrivial r z w`** — a quadrisecant is trivial
   *at the middle secant* when the chord `(z,w)` between its two middle
   points is a trivial secant (Kuperberg's `bc`; this is the notion that
   defines `O'` on quadrisecants).

Both inherit the D1 endpoint symmetry (`TrivialSecant_swap`):
`TrisecantTrivial_swap_endpoints` (the chord endpoints commute) and
`QuadrisecantMiddleSecantTrivial_swap` (the two middles commute).  All
elementary; no new disk machinery.
-/

/-- A trisecant (chord `(p,q)` with strict middle `m`) is **topologically
trivial** when one of its two endpoint-to-middle sub-secants is a trivial
secant (Kuperberg: "similarly for a trisecant" — the analogue of `ab`, `bc`
for the trisecant `(p,q)` with middle `m`). -/
def TrisecantTrivial (r : ℝ → Space) (p q m : AddCircle period) : Prop :=
  TrivialSecant r p m ∨ TrivialSecant r m q

/-- Membership in `TrisecantTrivial`, unfolded. -/
lemma TrisecantTrivial_iff (r : ℝ → Space) (p q m : AddCircle period) :
    TrisecantTrivial r p q m ↔ TrivialSecant r p m ∨ TrivialSecant r m q := by
  rfl

/-- **The chord endpoints of a trisecant commute (D2).**  The trisecant
`(p,q)` with middle `m` is trivial iff the same chord traversed the other
way is: each sub-secant is symmetric under endpoint swap by D1. -/
lemma TrisecantTrivial_swap_endpoints (r : ℝ → Space) (p q m : AddCircle period) :
    TrisecantTrivial r p q m ↔ TrisecantTrivial r q p m := by
  unfold TrisecantTrivial
  constructor
  · rintro (hp | hmq)
    · right
      exact (TrivialSecant_swap r p m).mp hp
    · left
      exact (TrivialSecant_swap r m q).mp hmq
  · rintro (hq | hmp)
    · right
      exact (TrivialSecant_swap r m q).mpr hq
    · left
      exact (TrivialSecant_swap r p m).mpr hmp

/-- A quadrisecant is trivial **at the middle secant** when the chord between
its two middle points `z w` is a trivial secant (Kuperberg's `bc` for the
quadrisecant, the notion that puts a quadrisecant into `O'` only when this
fails). -/
def QuadrisecantMiddleSecantTrivial (r : ℝ → Space) (z w : AddCircle period) : Prop :=
  TrivialSecant r z w

/-- Membership in `QuadrisecantMiddleSecantTrivial`, unfolded. -/
lemma QuadrisecantMiddleSecantTrivial_iff (r : ℝ → Space) (z w : AddCircle period) :
    QuadrisecantMiddleSecantTrivial r z w ↔ TrivialSecant r z w := by
  rfl

/-- **The two middle points of a quadrisecant commute (D2).**  Triviality at
the middle secant is symmetric in the two middles (D1). -/
lemma QuadrisecantMiddleSecantTrivial_swap (r : ℝ → Space) (z w : AddCircle period) :
    QuadrisecantMiddleSecantTrivial r z w ↔ QuadrisecantMiddleSecantTrivial r w z := by
  unfold QuadrisecantMiddleSecantTrivial
  exact TrivialSecant_swap r z w

/-- **A trivial trisecant supplies the interior-free disk of one of its
sub-secants (the Fig.-3a ingredient).**  If the trisecant `(p,q)` with middle
`m` is topologically trivial, then one of its two endpoint-to-middle
sub-secants is a trivial secant, i.e. carries an explicit arc witness `β`
(or `γ`) with an interior-free disk (`ChordTrivialByArc`) — exactly the
"disk `D_T` which bounds a secant of `T` and an arc of `K`" that Kuperberg's
Fig.-3(a) modification consumes. -/
lemma trivial_subsecant_disk_of_trisecantTrivial {r : ℝ → Space} {p q m : AddCircle period}
    (ht : TrisecantTrivial r p q m) :
    (∃ β : Path (knotMap r p) (knotMap r m), ChordTrivialByArc r p m β) ∨
      (∃ γ : Path (knotMap r m) (knotMap r q), ChordTrivialByArc r m q γ) := by
  rcases ht with hp | hm
  · left
    exact hp
  · right
    exact hm

end LeanEval.KnotTheory.Quadrisecant
