import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.SecantSpace

open LeanEval.KnotTheory.Quadrisecant
open unitInterval

/-!
# Layer A (iii, continued) — closed chords and the compactification of trisecant data

Kuperberg's trisecant set `O` (see `TrisecantLocus.lean`, `trisecantSet r`) is
defined over the *open* Möbius band `OpenMobius` by a **strict** betweenness
condition (`IsMiddleOnChord`, i.e. the middle knot point lies in the *open*
segment).  Over the *compact* band `UnordCirclePairs` of all unordered pairs —
which includes the diagonal circle of degenerate secants — the strict
condition is *not* closed: a middle point may converge to an endpoint of its
chord.

This module analyses the closed-segment families over the compact band, and
records the precise way in which the naive "closed segment" formulation is
degenerate, so that the correct compactification is used in the structure
theory of `O`.

**The degeneracy, precisely.**  If `m` is allowed to range freely while we
merely ask that `knotMap m` lies on the **closed** segment between `knotMap a`
and `knotMap b`, then *every* pair qualifies: one of its endpoints is always on
its own closed segment (`left_mem_segment`).  Consequently the class-level set
`closedMiddleClassSet r` over `UnordCirclePairs` is the *whole* compact band
(`closedMiddleClassSet_eq_univ`), and `IsClosed` holds in the strongest
possible form (`isClosed_closedMiddleClassSet`).  So a "closed trisecant set"
cannot be defined by the closed segment alone; the middle point must be kept
as *attached data*, exactly as Kuperberg states ("for a sequence of
trisecants to converge we insist that the middle points converge as well").

**The correct closed objects (all proved closed below).**  The space of
trisecant data *with* its middle point attached is

    closedMiddleData r := { (a, b, m) | knotMap m ∈ segment (knotMap a) (knotMap b) }
      ⊆ (AddCircle period)³ ,

a closed subset of the compact cube (closedness by the unit-interval lift:
membership in the segment is the existence of `t ∈ [0,1]` with
`knotMap m = lineMap (knotMap a) (knotMap b) t`, an equality of continuous
maps, so the zero set is closed; a closed set of a compact space is compact,
and its image under the coordinate projection — dropping the coefficient `t`
— is compact hence closed).  Its open-strict analogue `openMiddleData r`
(where `knotMap m` lies in the *open* segment) is contained in it, so

    closure (openMiddleData r) ⊆ closedMiddleData r :

every limit of genuine strict trisecants still has its middle point on the
closed chord — the rigorous meaning of "degenerate trisecant" at the
boundary of `O`.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The parameter circle of a smooth knot. -/
abbrev KnotParam := AddCircle period

/-- A triple `(a, b, m)` of parameters (right-associative product). -/
abbrev KnotParamTriple := KnotParam × KnotParam × KnotParam

/-- The unit interval as a type, used as the affine-coefficient range. -/
abbrev CoeffInterval := I

/-- The closed-segment betweenness relation on the knot: the `m`-th point of
the knot lies on the closed chord from `a` to `b`. -/
def IsMiddleOnClosedChord (r : ℝ → Space) (a b m : KnotParam) : Prop :=
  knotMap r m ∈ segment ℝ (knotMap r a) (knotMap r b)

/-- The open-segment (strict) betweenness relation on the knot: `knotMap m`
lies strictly between `knotMap a` and `knotMap b`. -/
def IsMiddleOnOpenChord (r : ℝ → Space) (a b m : KnotParam) : Prop :=
  knotMap r m ∈ openSegment ℝ (knotMap r a) (knotMap r b)

/-- Membership of a segment point on the closed chord is equivalent to
expressing it through the affine line map over the unit interval. -/
lemma mem_segment_iff_lineMap {u v w : Space} :
    w ∈ segment ℝ u v ↔ ∃ t : I, w = AffineMap.lineMap u v (t : ℝ) := by
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨⟨t, ht⟩, h.symm⟩
  · rintro ⟨t, h⟩
    exact ⟨(t : ℝ), t.2, h.symm⟩

/-- The closed-chord middle point is on the chord of its own endpoint: the
endpoint itself is always a middle point for the *closed* chord. -/
lemma IsMiddleOnClosedChord_self_left (r : ℝ → Space) (a b : KnotParam) :
    IsMiddleOnClosedChord r a b a := by
  dsimp [IsMiddleOnClosedChord]
  exact left_mem_segment ℝ _ _

/-- Symmetrically, the right endpoint is a closed middle point. -/
lemma IsMiddleOnClosedChord_self_right (r : ℝ → Space) (a b : KnotParam) :
    IsMiddleOnClosedChord r a b b := by
  dsimp [IsMiddleOnClosedChord]
  exact right_mem_segment ℝ _ _

/-- A strict (open-segment) middle point is in particular a closed-segment
middle point. -/
lemma IsMiddleOnOpenChord_imp_closed (r : ℝ → Space) (a b m : KnotParam) :
    IsMiddleOnOpenChord r a b m → IsMiddleOnClosedChord r a b m := by
  intro h
  exact openSegment_subset_segment ℝ (knotMap r a) (knotMap r b) h

/-- Attached trisecant data with a *closed*-segment middle point: triples
`(a, b, m)` of parameters such that the `m`-th knot point lies on the closed
chord between `a` and `b`.  This is the compactification that keeps the
middle point attached (it is closed, see `isClosed_closedMiddleData`). -/
def closedMiddleData (r : ℝ → Space) : Set KnotParamTriple :=
  {p | IsMiddleOnClosedChord r p.1 p.2.1 p.2.2}

/-- Attached strict trisecant data: as `closedMiddleData` but the middle point
lies in the open segment (this is Kuperberg's trisecant space with the middle
point as data, before passing to unordered pairs). -/
def openMiddleData (r : ℝ → Space) : Set KnotParamTriple :=
  {p | IsMiddleOnOpenChord r p.1 p.2.1 p.2.2}

/-- The "lift" region in `(S¹)³ × [0,1]`: a triple of parameters together
with an affine coefficient `t` realizing the closed-chord membership. -/
def closedMiddleLift (r : ℝ → Space) : Set (KnotParamTriple × I) :=
  {z | knotMap r z.1.2.2 = AffineMap.lineMap (knotMap r z.1.1) (knotMap r z.1.2.1) (z.2 : ℝ)}

/-- The lift region is closed: it is the preimage of `{0}` under a continuous
map (equality of continuous functions). -/
lemma isClosed_closedMiddleLift {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsClosed (closedMiddleLift r) := by
  let F : KnotParamTriple × I → Space := fun z =>
    knotMap r z.1.2.2 - AffineMap.lineMap (knotMap r z.1.1) (knotMap r z.1.2.1) (z.2 : ℝ)
  have hkmc : Continuous (knotMap r) := h.knotMap_continuous
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hpre : closedMiddleLift r = F ⁻¹' {0} := by
    ext z
    simp [closedMiddleLift, F, sub_eq_zero]
  rw [hpre]
  exact (isClosed_singleton (x := (0 : Space))).preimage hF

/-- Membership in the attached closed-middle data, unfolded. -/
lemma mem_closedMiddleData_iff (r : ℝ → Space) {p : KnotParamTriple} :
    p ∈ closedMiddleData r ↔ IsMiddleOnClosedChord r p.1 p.2.1 p.2.2 := by
  simp [closedMiddleData]

/-- Membership in the lift region, unfolded. -/
lemma mem_closedMiddleLift_iff (r : ℝ → Space) {z : KnotParamTriple × I} :
    z ∈ closedMiddleLift r ↔
      knotMap r z.1.2.2 = AffineMap.lineMap (knotMap r z.1.1) (knotMap r z.1.2.1) (z.2 : ℝ) := by
  simp [closedMiddleLift]

/-- Forgetting the affine coefficient, the lift region projects onto exactly
the closed-middle data. -/
lemma closedMiddleData_eq_image_lift {r : ℝ → Space} :
    closedMiddleData r = (fun z : KnotParamTriple × I => z.1) '' closedMiddleLift r := by
  ext p
  constructor
  · intro hp
    have hp' : IsMiddleOnClosedChord r p.1 p.2.1 p.2.2 := (mem_closedMiddleData_iff r).mp hp
    rcases (mem_segment_iff_lineMap.mp hp') with ⟨t, ht⟩
    refine ⟨(p, t), ?_, rfl⟩
    exact (mem_closedMiddleLift_iff r).mpr ht
  · intro hp
    rcases hp with ⟨z, hz, hzp⟩
    subst p
    exact (mem_closedMiddleData_iff r).mpr (mem_segment_iff_lineMap.mpr ⟨z.2, hz⟩)

/-- The attached closed-middle data form a closed subset of the (compact)
parameter cube.  The cube is compact Hausdorff, the lift region is a closed
subset of the compact space `(S¹)³ × [0,1]` hence compact, and the coordinate
projection is continuous, so its image — the data set — is compact and closed.
-/
lemma isClosed_closedMiddleData {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsClosed (closedMiddleData r) := by
  rw [closedMiddleData_eq_image_lift]
  have hproj : Continuous (fun z : KnotParamTriple × I => z.1) := continuous_fst
  exact ((isClosed_closedMiddleLift h).isCompact.image hproj).isClosed

/-- Consequently the attached closed-middle data are compact. -/
lemma isCompact_closedMiddleData {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsCompact (closedMiddleData r) :=
  (isClosed_closedMiddleData h).isCompact

/-- Strict trisecant data are closed-middle data. -/
lemma openMiddleData_subset_closedMiddleData (r : ℝ → Space) :
    openMiddleData r ⊆ closedMiddleData r := by
  intro p hp
  exact IsMiddleOnOpenChord_imp_closed r p.1 p.2.1 p.2.2 hp

/-- The closure of the strict trisecant data lies inside the closed-middle
data: every limit of genuine strict trisecants still has its middle point on
the closed chord (the rigorous sense in which chords persist at the boundary
of the trisecant locus). -/
lemma closure_openMiddleData_subset_closedMiddleData {r : ℝ → Space} (h : IsSmoothKnot r) :
    closure (openMiddleData r) ⊆ closedMiddleData r :=
  closure_minimal (openMiddleData_subset_closedMiddleData r) (isClosed_closedMiddleData h)

/-- The set of unordered pairs whose closed chord meets the knot in a
closed-middle point, at the level of the parameter square. -/
def closedMiddlePairSet (r : ℝ → Space) : Set (KnotParam × KnotParam) :=
  {q | ∃ m : KnotParam, IsMiddleOnClosedChord r q.1 q.2 m}

/-- **Degeneracy of the un-attached closed formulation.**  If the middle point
is not attached as data, the closed-segment condition is vacuous over the
whole parameter square: every pair qualifies, since each endpoint of a chord
lies on that chord (`left_mem_segment`). -/
lemma closedMiddlePairSet_eq_univ (r : ℝ → Space) :
    closedMiddlePairSet r = Set.univ := by
  ext q
  constructor
  · intro h; trivial
  · intro _
    exact ⟨q.1, IsMiddleOnClosedChord_self_left r q.1 q.2⟩

/-- The un-attached pair set is (of course) closed — it is everything. -/
lemma isClosed_closedMiddlePairSet (r : ℝ → Space) :
    IsClosed (closedMiddlePairSet r) := by
  rw [closedMiddlePairSet_eq_univ]
  exact isClosed_univ

/-- An unordered pair (a class of the compact band, possibly a diagonal class)
carries a *closed*-middle knot point. -/
def HasMiddleOnClosedClass (r : ℝ → Space) (c : UnordCirclePairs) : Prop :=
  ∃ a b : KnotParam,
    (⟦(a, b)⟧ : UnordCirclePairs) = c ∧
      ∃ m : KnotParam, IsMiddleOnClosedChord r a b m

/-- The class-level closed-middle trisecant set over the compact band
`UnordCirclePairs`.  (`closedMiddleClassSet_eq_univ` below shows it is the
whole band — the closed segment alone cannot define a proper "closure of
`O`"; the middle point must be attached as data.) -/
def closedMiddleClassSet (r : ℝ → Space) : Set UnordCirclePairs :=
  {c | HasMiddleOnClosedClass r c}

/-- The un-attached closed-middle set is the whole compact band: every class
is represented by a pair `(a, b)` whose own endpoint `a` lies on the closed
chord from `a` to `b`. -/
lemma closedMiddleClassSet_eq_univ (r : ℝ → Space) :
    closedMiddleClassSet r = Set.univ := by
  ext c
  constructor
  · intro h; trivial
  · intro _
    rcases unordMap_surj c with ⟨q, hq⟩
    refine ⟨q.1, q.2, hq, q.1, IsMiddleOnClosedChord_self_left r q.1 q.2⟩

/-- **The closed-segment family is closed over the compact band** — in the
strongest possible form: the set is the entire (compact) `UnordCirclePairs`,
so closedness is immediate.  (This is the literal statement of the naive
"closed trisecant set"; its vacuity is the content of
`closedMiddleClassSet_eq_univ`, motivating the attached-data
compactification `closedMiddleData` above.) -/
theorem isClosed_closedMiddleClassSet (r : ℝ → Space) :
    IsClosed (closedMiddleClassSet r) := by
  rw [closedMiddleClassSet_eq_univ]
  exact isClosed_univ

end LeanEval.KnotTheory.Quadrisecant
