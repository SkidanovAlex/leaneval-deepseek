import Mathlib
import ChallengeDeps
import Submission.TrisecantLocus
import Submission.TrisecantStructure
import Submission.TrisecantClosed

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# Layer A (v, continued) — the functional middle structure of the trisecant
data (double-point / fibre analysis under the no-quadrisecant hypothesis)

`TrisecantStructure.lean` proved the class-level functional structure: under
`QuadrisecantFree r` (`¬ QuadrisecantChord r`, i.e. the no-quadrisecant
contrapositive hypothesis of the main theorem) every secant class carries
**at most one** strict middle point
(`quadrisecantFree_iff_atMostOneMiddle`).  This module makes that structure
operative at the *data* level — which is what the once/twice winding
argument of the Kuperberg proof consumes:

1. **`middle_unique_of_quadrisecantFree`** — for an ordered chord `(a,b)`
   of distinct parameters, two strict middle parameters coincide.  This is
   the reason a family `{a,b}_t, m_t` along a curve `C ⊆ O` is
   *well-defined*: the middle `m_t` of a trisecant class is a function of
   the class, not a choice.
2. **`openMiddleData_unique_of_quadrisecantFree`** — the same uniqueness
   for the attached open data `openMiddleData r` of `TrisecantClosed.lean`
   (the torus-level cube `(a, (b, m))`): over fixed endpoints `(a,b)` the
   strict data contain at most one triple.
3. **`orderedTrisecantData_middle_unique`** — inside the attached data over
   the ordered double cover (`OrderedTrisecantData r` of
   `TrisecantStructure.lean`), two data with the *same* chord
   representative have the same middle.
4. **`orderedTrisecantData_fiber_swap`** — two attached data whose chords
   represent the *same* secant class have chords that are equal or swapped
   (the two ordered representatives) and equal middles: under
   `QuadrisecantFree` the projection of the attached data onto the Möbius
   band of secants is two-to-one and the middle is constant on each fibre —
   the data double cover of `O`.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- The no-quadrisecant hypothesis of the contrapositive main theorem is
literally the negation of the trusted `HasQuadrisecant` predicate (via the
chord formulation `hasQuadrisecant_iff_quadrisecantChord`). -/
lemma quadrisecantFree_iff_not_hasQuadrisecant {r : ℝ → Space} (h : IsSmoothKnot r) :
    QuadrisecantFree r ↔ ¬ HasQuadrisecant r := by
  unfold QuadrisecantFree
  exact (not_congr (hasQuadrisecant_iff_quadrisecantChord h)).symm

/-- **Uniqueness of the strict middle point of a chord (no-quadrisecant
case).**  For an ordered chord `(a,b)` of distinct parameters, two
parameters strictly between `knotMap a` and `knotMap b` coincide: a
quadrisecant would be exactly a chord with two distinct strict middle
points (`quadrisecantChord_iff_exists_class`), so `QuadrisecantFree` forces
the middle to be unique. -/
theorem middle_unique_of_quadrisecantFree {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {a b m₁ m₂ : AddCircle period} (hab : a ≠ b)
    (hm₁ : IsMiddleOnChord r a b m₁) (hm₂ : IsMiddleOnChord r a b m₂) :
    m₁ = m₂ := by
  have hatmost : AtMostOneMiddle r := (quadrisecantFree_iff_atMostOneMiddle h).mp hqf
  let p : OrderedPairs := ⟨(a, b), hab⟩
  exact hatmost (mobiusCover p) m₁ m₂
    ⟨p, rfl, (by simpa [p] using hm₁)⟩
    ⟨p, rfl, (by simpa [p] using hm₂)⟩

/-- **Uniqueness of the middle in the attached open data.**  Two triples of
`openMiddleData r` (strict data with the middle on the *open* chord) whose
endpoints agree are equal: the middle coordinate is a function of the
chord.  (The degenerate case `a = b` is covered separately: the open chord
is then a single point, so the middle is the endpoint itself.) -/
lemma openMiddleData_unique_of_quadrisecantFree {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {u v : KnotParamTriple}
    (hu : u ∈ openMiddleData r) (hv : v ∈ openMiddleData r)
    (ha : u.1 = v.1) (hb : u.2.1 = v.2.1) : u.2.2 = v.2.2 := by
  have hmu : IsMiddleOnOpenChord r u.1 u.2.1 u.2.2 := by
    simpa [openMiddleData] using hu
  have hmv : IsMiddleOnOpenChord r v.1 v.2.1 v.2.2 := by
    simpa [openMiddleData] using hv
  by_cases hne : u.1 = u.2.1
  · -- degenerate chord (the endpoints coincide): the open chord is a single
    -- point, so the strict middle is forced to be that endpoint
    have hku : knotMap r u.2.2 = knotMap r u.1 := by
      have hseg : knotMap r u.2.2 ∈ openSegment ℝ (knotMap r u.1) (knotMap r u.1) := by
        simpa [hne, IsMiddleOnOpenChord] using hmu
      simpa [openSegment_same] using hseg
    have hmu1 : u.2.2 = u.1 := knotMap_injective h hku
    have hkv : knotMap r v.2.2 = knotMap r v.1 := by
      have hveq : v.1 = v.2.1 := by
        rw [← ha, ← hb]
        exact hne
      have hsegv : knotMap r v.2.2 ∈ openSegment ℝ (knotMap r v.1) (knotMap r v.1) := by
        simpa [hveq, IsMiddleOnOpenChord] using hmv
      simpa [openSegment_same] using hsegv
    have hmv1 : v.2.2 = v.1 := knotMap_injective h hkv
    calc
      u.2.2 = u.1 := hmu1
      _ = v.1 := by rw [ha]
      _ = v.2.2 := hmv1.symm
  · exact middle_unique_of_quadrisecantFree h hqf hne
      (by simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using hmu)
      (by
        simpa [IsMiddleOnOpenChord, IsMiddleOnChord, ha, hb] using hmv)

/-- **Uniqueness of the middle inside the attached data over the ordered
double cover.**  Two data of `OrderedTrisecantData r` with the *same*
ordered chord representative have the same middle point. -/
lemma orderedTrisecantData_middle_unique {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {d e : OrderedPairs × AddCircle period}
    (hd : d ∈ OrderedTrisecantData r) (he : e ∈ OrderedTrisecantData r)
    (hchord : d.1 = e.1) : d.2 = e.2 := by
  have hmd : IsMiddleOnChord r d.1.1.1 d.1.1.2 d.2 := by
    simpa [OrderedTrisecantData] using hd
  have hme : IsMiddleOnChord r e.1.1.1 e.1.1.2 e.2 := by
    simpa [OrderedTrisecantData] using he
  have hme' : IsMiddleOnChord r d.1.1.1 d.1.1.2 e.2 := by
    simpa [hchord] using hme
  exact middle_unique_of_quadrisecantFree h hqf d.1.2 hmd hme'

/-- **The fibre of the attached data over a secant class (no-quadrisecant
case).**  Two attached strict trisecants whose chords represent the same
secant class have chords that are equal or swapped (the two ordered
representatives of the class) and have the *same* middle point: the
projection of `OrderedTrisecantData r` onto `O = trisecantSet r` is
two-to-one with constant middle on each fibre. -/
theorem orderedTrisecantData_fiber_swap {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {d e : OrderedPairs × AddCircle period}
    (hd : d ∈ OrderedTrisecantData r) (he : e ∈ OrderedTrisecantData r)
    (hclass : mobiusCover d.1 = mobiusCover e.1) :
    (d.1 = e.1 ∨ d.1 = swapOrdered e.1) ∧ d.2 = e.2 := by
  have hfib := mobiusCover_fiber d.1
  have hefib : e.1 ∈ ({d.1, swapOrdered d.1} : Set OrderedPairs) := by
    rw [← hfib]
    exact hclass.symm
  simp at hefib
  constructor
  · rcases hefib with hEq | hsw
    · left
      exact hEq.symm
    · right
      rw [hsw]
      exact (swapOrdered_involutive d.1).symm
  · rcases hefib with hEq | hsw
    · exact orderedTrisecantData_middle_unique h hqf hd he hEq.symm
    · -- e's chord is the swap of d's chord: the two middles coincide by
      -- uniqueness (both are strict middles of the same unordered chord)
      have hswd : IsMiddleOnChord r (swapOrdered d.1).1.1 (swapOrdered d.1).1.2 e.2 := by
        have hmem : IsMiddleOnChord r e.1.1.1 e.1.1.2 e.2 := by
          simpa [OrderedTrisecantData] using he
        rw [hsw] at hmem
        simpa using hmem
      have hmswap : IsMiddleOnChord r (swapOrdered d.1).1.1 (swapOrdered d.1).1.2 d.2 := by
        have hmd : IsMiddleOnChord r d.1.1.1 d.1.1.2 d.2 := by
          simpa [OrderedTrisecantData] using hd
        simpa [swapOrdered] using (IsMiddleOnChord_swap r d.1 d.2).mpr hmd
      exact middle_unique_of_quadrisecantFree h hqf (swapOrdered d.1).2 hmswap hswd

end LeanEval.KnotTheory.Quadrisecant
