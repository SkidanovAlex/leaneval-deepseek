import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.SecantSpace
import Submission.QuadrisecantChord
import Submission.TrisecantLocus

open LeanEval.KnotTheory.Quadrisecant

/-!
# Layer A (v) — the structure of the trisecant locus `O`

Kuperberg's structure theorem for `O` (`TrisecantLocus.lean`, §3 of the
paper) says: for a knot in general position, `O` is the image of a
self-transverse smooth immersion of a 1-manifold, and a self-crossing of
that immersion is exactly a quadrisecant (a secant class with two middle
points).  That theorem needs generic-position/transversality infrastructure
that Mathlib does not yet contain, and — importantly — it is *false without
a genericity hypothesis* (a smooth knot containing a straight arc has a
two-dimensional family of trisecant pairs).  The structure theorem will
therefore have to be built on a formal notion of general position, plus the
smooth analysis of the collinearity map `(a,b,m) ↦ (K a − K b) × (K a − K m)`
on the compact cube of parameters.

This module records the *genericity-free structural foundations* that such a
theory and its later use rest on:

* **single middle points.**  A secant class carries a well-defined set of
  middle parameters `MiddlePointsOnClass r c ⊆ S¹` (`m` is a middle point of
  `c` iff it is a middle point of *any* representative chord — rep
  independence `middleOnChord_of_mobiusCover_eq`).  Its members are never
  the chord endpoints (`MiddlePointsOnClass_not_endpoint`).  The hypothesis
  of the contrapositive main theorem — no quadrisecants,
  `QuadrisecantFree r` — is equivalent to every class carrying *at most one*
  middle point (`quadrisecantFree_iff_atMostOneMiddle`): without double
  points, `O` is a *functional* locus (each point of `O` has a single
  attached middle parameter, the data that the 1-manifold theory keeps
  continuous).
* **`O` as an image of attached data.**  Over the ordered double cover,
  `OrderedTrisecantData r` packages each trisecant with its middle point;
  `O = trisecantSet r` is exactly its projection to the Möbius band
  (`trisecantSet_eq_orderedTrisecantData_image`).  This is the set that the
  "image of a 1-manifold" statement parametrizes.
* **the extremal contradictions (Kuperberg's Lemma-compact).**  A smooth
  knot can never have every point strictly between two others
  (`not_every_image_point_between`), nor can every parameter be the middle
  point of some trisecant (`not_every_middle_of_smooth_knot`); equivalently
  there is always a parameter that is not covered as a middle point
  (`exists_uncovered_middle`).  These are the two "contradiction by Lemma
  compact" endpoints of the once- and twice-winding analysis.

Everything here is elementary and verified (no axioms, no `sorry`).  The
remaining content of the layer — the general-position hypothesis and the
self-transverse-immersion statement — is a separate, future development
(recorded in ROADMAP.md under Layer A, "structure theorem", and in the
remarks below).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The hypothesis of the contrapositive main theorem: the knot has **no**
quadrisecant, equivalently (`quadrisecantChord_iff_exists_class`) no secant
class whose chord carries two strict middle points. -/
def QuadrisecantFree (r : ℝ → Space) : Prop :=
  ¬ QuadrisecantChord r

/-- **Representative independence of a fixed middle point**: whether a given
parameter `m` is a strict middle point of the chord depends only on the
unordered pair, not on the ordered representative of the class. -/
lemma middleOnChord_of_mobiusCover_eq {r : ℝ → Space} (p q : OrderedPairs)
    (hpq : mobiusCover p = mobiusCover q) {m : AddCircle period} :
    IsMiddleOnChord r p.1.1 p.1.2 m ↔ IsMiddleOnChord r q.1.1 q.1.2 m := by
  have hfib := mobiusCover_fiber p
  have hq : q ∈ ({p, swapOrdered p} : Set OrderedPairs) := by
    rw [← hfib]
    exact hpq.symm
  simp at hq
  rcases hq with rfl | hq
  · rfl
  · rw [hq]
    simpa [swapOrdered] using (IsMiddleOnChord_swap r p m).symm

/-- The set of middle parameters of a secant class `c` — the attached data
that the 1-manifold structure of `O` keeps track of. -/
def MiddlePointsOnClass (r : ℝ → Space) (c : OpenMobius) : Set (AddCircle period) :=
  {m | ∃ p : OrderedPairs, mobiusCover p = c ∧ IsMiddleOnChord r p.1.1 p.1.2 m}

/-- Membership in `MiddlePointsOnClass`, unfolded. -/
lemma mem_MiddlePointsOnClass_iff (r : ℝ → Space) (c : OpenMobius) (m : AddCircle period) :
    m ∈ MiddlePointsOnClass r c ↔
      ∃ p : OrderedPairs, mobiusCover p = c ∧ IsMiddleOnChord r p.1.1 p.1.2 m := by
  simp [MiddlePointsOnClass]

/-- A class is a trisecant (`∈ O`) iff its middle-point set is nonempty. -/
lemma HasMiddleOnClass_iff_middleSet_nonempty (r : ℝ → Space) (c : OpenMobius) :
    HasMiddleOnClass r c ↔ (MiddlePointsOnClass r c).Nonempty := by
  constructor
  · rintro ⟨m, p, hp, hm⟩
    exact ⟨m, ⟨p, hp, hm⟩⟩
  · rintro ⟨m, hm⟩
    rcases (mem_MiddlePointsOnClass_iff r c m).mp hm with ⟨p, hp, hmi⟩
    exact ⟨m, p, hp, hmi⟩

/-- A middle point of a secant class is never one of the chord endpoints
(any representative): strict betweenness excludes the endpoints and
`knotMap` is injective. -/
lemma MiddlePointsOnClass_not_endpoint {r : ℝ → Space} (h : IsSmoothKnot r) {c : OpenMobius}
    {p : OrderedPairs} (hp : mobiusCover p = c) {m : AddCircle period}
    (hm : m ∈ MiddlePointsOnClass r c) : m ≠ p.1.1 ∧ m ≠ p.1.2 := by
  rcases (mem_MiddlePointsOnClass_iff r c m).mp hm with ⟨q, hq, hmq⟩
  have hm' : IsMiddleOnChord r p.1.1 p.1.2 m := by
    exact (middleOnChord_of_mobiusCover_eq p q (by rw [hq, hp])).mpr hmq
  exact IsMiddleOnChord.ne_params h p.2 hm'

/-- A secant class has *at most one* middle point: any two parameters that
are middle points of its chord (through possibly different representatives)
coincide. -/
def AtMostOneMiddleOnClass (r : ℝ → Space) (c : OpenMobius) : Prop :=
  ∀ z w : AddCircle period,
    (∃ p : OrderedPairs, mobiusCover p = c ∧ IsMiddleOnChord r p.1.1 p.1.2 z) →
    (∃ p : OrderedPairs, mobiusCover p = c ∧ IsMiddleOnChord r p.1.1 p.1.2 w) → z = w

/-- The knot has at most one middle point on every secant class. -/
def AtMostOneMiddle (r : ℝ → Space) : Prop :=
  ∀ c : OpenMobius, AtMostOneMiddleOnClass r c

/-- **No quadrisecants ⇔ at most one middle point per secant class.**
  The double points of the trisecant locus are exactly the secant classes
  with two distinct middle points (TrisecantLocus), so under the
  no-quadrisecant hypothesis `O` is a *functional* locus: each point of `O`
  carries a single attached middle parameter (the continuous branch that the
  1-manifold argument follows). -/
theorem quadrisecantFree_iff_atMostOneMiddle {r : ℝ → Space} (h : IsSmoothKnot r) :
    QuadrisecantFree r ↔ AtMostOneMiddle r := by
  constructor
  · intro hqf c z w hz hw
    by_contra hzw
    rcases hz with ⟨pz, hpz, hzz⟩
    rcases hw with ⟨pw, hpw, hww⟩
    have hwpz : IsMiddleOnChord r pz.1.1 pz.1.2 w := by
      exact (middleOnChord_of_mobiusCover_eq pz pw (by rw [hpz, hpw])).mpr hww
    have hdouble : HasTwoMiddlePointsOnClass r c := ⟨z, w, hzw, pz, hpz, hzz, hwpz⟩
    exact hqf ((quadrisecantChord_iff_exists_class h).2 ⟨c, hdouble⟩)
  · intro hatmost hQ
    rcases (quadrisecantChord_iff_exists_class h).1 hQ with ⟨c, z, w, hzw, p, hp, hzp, hwp⟩
    have hz : ∃ p : OrderedPairs, mobiusCover p = c ∧ IsMiddleOnChord r p.1.1 p.1.2 z :=
      ⟨p, hp, hzp⟩
    have hw : ∃ p : OrderedPairs, mobiusCover p = c ∧ IsMiddleOnChord r p.1.1 p.1.2 w :=
      ⟨p, hp, hwp⟩
    exact hzw (hatmost c z w hz hw)

/-- **Attached trisecant data over the ordered double cover**: an ordered
chord `d.1` (two distinct parameters) together with a middle parameter
`d.2`, strictly inside its chord.  This is the set whose projection to the
Möbius band is `O` and whose "image of a 1-manifold" structure is the object
of the layer. -/
def OrderedTrisecantData (r : ℝ → Space) : Set (OrderedPairs × AddCircle period) :=
  {d | IsMiddleOnChord r d.1.1.1 d.1.1.2 d.2}

/-- Kuperberg's `O` is exactly the projection of the attached trisecant
data over the double cover to the Möbius band of secants: a class is a
trisecant iff some attached datum projects onto it. -/
lemma trisecantSet_eq_orderedTrisecantData_image (r : ℝ → Space) :
    (fun d : OrderedPairs × AddCircle period => mobiusCover d.1) '' OrderedTrisecantData r =
      trisecantSet r := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d.2, d.1, rfl, hd⟩
  · rintro ⟨m, p, hp, hm⟩
    refine ⟨(p, m), ?_, ?_⟩
    · exact hm
    · exact hp

/-- The set of parameters that occur as the middle point of some trisecant
of the knot ("middle-covered parameters"). -/
def MiddleCovered (r : ℝ → Space) : Set (AddCircle period) :=
  {m | ∃ a b : AddCircle period, a ≠ b ∧ IsMiddleOnChord r a b m}

/-- Membership in `MiddleCovered`, unfolded. -/
lemma mem_MiddleCovered_iff (r : ℝ → Space) (m : AddCircle period) :
    m ∈ MiddleCovered r ↔ ∃ a b : AddCircle period, a ≠ b ∧ IsMiddleOnChord r a b m := by
  simp [MiddleCovered]

/-- **The extremal contradiction (Kuperberg's Lemma-compact), parameter
form**: not every parameter of a smooth knot can be the middle point of some
trisecant.  (A parameter whose image point is an extremal point of the
compact knot image is never strictly between two other knot points —
`IsSmoothKnot.exists_point_not_strictly_between`, backed by the commons
extremal lemma.) -/
theorem not_every_middle_of_smooth_knot {r : ℝ → Space} (h : IsSmoothKnot r) :
    ¬ (∀ m : AddCircle period, m ∈ MiddleCovered r) := by
  intro hmid
  rcases IsSmoothKnot.exists_point_not_strictly_between h with ⟨q, hq, hprop⟩
  have hqrange : q ∈ Set.range (knotMap r) := by
    rw [knotMap_range]
    exact hq
  rcases hqrange with ⟨m, hmq⟩
  have hmidm : m ∈ MiddleCovered r := hmid m
  rcases (mem_MiddleCovered_iff r m).mp hmidm with ⟨a, b, hab, hmab⟩
  have hxa : knotMap r a ∈ r '' Set.Ico (0 : ℝ) period := by
    rw [← knotMap_range]
    exact ⟨a, rfl⟩
  have hxb : knotMap r b ∈ r '' Set.Ico (0 : ℝ) period := by
    rw [← knotMap_range]
    exact ⟨b, rfl⟩
  have hxyn : knotMap r a ≠ knotMap r b := by
    intro hx
    exact hab (knotMap_injective h hx)
  exact hprop (knotMap r a) (knotMap r b) hxa hxb hxyn (by simpa [IsMiddleOnChord, hmq] using hmab)

/-- Every smooth knot has a parameter that is *not* the middle point of any
trisecant — the extremal (uncovered) parameter, whose image is the extremal
point of Lemma-compact. -/
theorem exists_uncovered_middle {r : ℝ → Space} (h : IsSmoothKnot r) :
    ∃ m : AddCircle period, m ∉ MiddleCovered r := by
  by_contra hnone
  push Not at hnone
  exact not_every_middle_of_smooth_knot h hnone

/-- **The extremal contradiction, point form** (the exact endpoint of
Kuperberg's twice-winding argument): it is impossible that every point of
the knot image lies strictly between two other knot points; some point of
the compact image is extremal and never strictly between two others. -/
theorem not_every_image_point_between {r : ℝ → Space} (h : IsSmoothKnot r) :
    ¬ (∀ q : Space, q ∈ r '' Set.Ico (0 : ℝ) period →
      ∃ x y : Space, x ∈ r '' Set.Ico (0 : ℝ) period ∧
        y ∈ r '' Set.Ico (0 : ℝ) period ∧ x ≠ y ∧ q ∈ openSegment ℝ x y) := by
  intro hall
  rcases IsSmoothKnot.exists_point_not_strictly_between h with ⟨q, hq, hprop⟩
  rcases hall q hq with ⟨x, y, hx, hy, hxy, hqseg⟩
  exact hprop x y hx hy hxy hqseg

end LeanEval.KnotTheory.Quadrisecant
