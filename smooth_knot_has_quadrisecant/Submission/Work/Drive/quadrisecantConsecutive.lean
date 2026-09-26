import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.secantDiskAPI

/-!
# The six sub-secants of a quadrisecant: Kuperberg's "three consecutive" reduction

This module contains the *combinatorial* dictionary between the six-condition form of
`Work.Drive.exists_nontrivial_quadrisecant_of_generalPosition_noInflection` (all six sub-secants of
the four points are topologically non-trivial secants) and Kuperberg's Definition 3.2 ("a
quadrisecant is trivial if any of its three consecutive secants is trivial"), and it is the tool by
which the hypothesis "no non-trivial quadrisecant" is converted into Kuperberg's language.

## What is proved here

The six sub-secants of a quadrisecant are not independent.  If `z ≠ w` are two strict middles of
the chord `(a,b)`, then — in whichever of the two orders `a,w,z,b` or `a,z,w,b` holds along the
chord — **three** of the six sub-secants *automatically* contain another knot point strictly inside
(the chord itself contains `z`, and the two sub-secants adjacent to the *other* middle contain it),
hence are automatically non-trivial, because `NontrivialSecant` can fail only through
`TrivialSecant`, which requires the chord to be interior-free.  The remaining three are exactly the
*consecutive* sub-secants of Kuperberg's Definition 3.2.  This module proves that reduction, which is
the dictionary between the target's six-condition form and Kuperberg's language:

* `TrivialSecant.not_middle`, `nontrivialSecant_of_middle` — a strict middle makes the chord's
  secant non-trivial;
* `middle_dichotomy` — two distinct strict middles of a chord are ordered along the chord;
* `middle_transfer_left` — order transfer along the chord (the third automatic sub-secant);
* `six_nontrivial_of_consecutive`, `exists_trivial_consecutive_of_not_all_nontrivial` — the
  equivalence between "all six sub-secants non-trivial" and "the three consecutive sub-secants
  non-trivial", case by case.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- A topologically trivial secant has no extra interior intersection with the knot, so no knot
point lies strictly inside its chord: `TrivialSecant r a b` refutes `IsMiddleOnChord r a b z`. -/
lemma TrivialSecant.not_middle {r : ℝ → Space} {a b z : AddCircle period}
    (h : TrivialSecant r a b) : ¬ IsMiddleOnChord r a b z := by
  intro hz
  exact h.interior_free z (by simpa [IsMiddleOnChord, IsMiddleOnOpenChord] using hz)

/-- **A chord with a knot point strictly inside it is a non-trivial secant.**  `NontrivialSecant`
can only fail through `TrivialSecant`, which requires the chord to be interior-free. -/
lemma nontrivialSecant_of_middle {r : ℝ → Space} {a b z : AddCircle period}
    (h : IsMiddleOnChord r a b z) : NontrivialSecant r a b := by
  intro ht
  exact TrivialSecant.not_middle ht h

/-- **Ordering of two strict middles of a chord.**  If `z ≠ w` are both strictly inside the chord
from `a` to `b`, then one of them lies strictly between the endpoint `a` and the other: along the
chord the four points occur either as `a, w, z, b` or as `a, z, w, b`.  (Uses injectivity of
`knotMap r`, i.e. `IsSmoothKnot r`.) -/
lemma middle_dichotomy {r : ℝ → Space} (hr : IsSmoothKnot r) {a b z w : AddCircle period}
    (hz : IsMiddleOnChord r a b z) (hw : IsMiddleOnChord r a b w) (hne : z ≠ w) :
    IsMiddleOnChord r a z w ∨ IsMiddleOnChord r a w z := by
  rw [IsMiddleOnChord, openSegment_eq_image'] at hz hw
  obtain ⟨θz, hθz, hzeq⟩ := hz
  obtain ⟨θw, hθw, hweq⟩ := hw
  change knotMap r a + θz • (knotMap r b - knotMap r a) = knotMap r z at hzeq
  change knotMap r a + θw • (knotMap r b - knotMap r a) = knotMap r w at hweq
  have hθz0 : 0 < θz := hθz.1
  have hθw0 : 0 < θw := hθw.1
  have hcoeff : θz ≠ θw := by
    intro h
    apply hne
    apply knotMap_injective hr
    rw [← hzeq, ← hweq, h]
  have hzm : knotMap r z - knotMap r a = θz • (knotMap r b - knotMap r a) := by
    rw [← hzeq]; abel
  have hwm : knotMap r w - knotMap r a = θw • (knotMap r b - knotMap r a) := by
    rw [← hweq]; abel
  rcases lt_or_gt_of_ne hcoeff with hlt | hgt
  · -- `θz < θw`: the order along the chord is `a, z, w, b`
    refine Or.inr ?_
    rw [IsMiddleOnChord, openSegment_eq_image']
    refine ⟨θz / θw, ⟨by positivity, (div_lt_one hθw0).mpr hlt⟩, ?_⟩
    change knotMap r a + (θz / θw) • (knotMap r w - knotMap r a) = knotMap r z
    rw [hwm, smul_smul, div_mul_cancel₀ θz (ne_of_gt hθw0)]
    exact hzeq
  · -- `θw < θz`: the order along the chord is `a, w, z, b`
    refine Or.inl ?_
    rw [IsMiddleOnChord, openSegment_eq_image']
    refine ⟨θw / θz, ⟨by positivity, (div_lt_one hθz0).mpr hgt⟩, ?_⟩
    change knotMap r a + (θw / θz) • (knotMap r z - knotMap r a) = knotMap r w
    rw [hzm, smul_smul, div_mul_cancel₀ θw (ne_of_gt hθz0)]
    exact hweq

/-- **Order transfer along a chord.**  If `w` is strictly between the endpoint `a` and the strict
middle `z` of the chord `(a,b)`, then `z` is strictly between `w` and `b`.  This is the third
"automatic" sub-secant of a quadrisecant (the sub-secant from the far middle to the far endpoint
contains the near middle). -/
lemma middle_transfer_left {r : ℝ → Space} {a b z w : AddCircle period}
    (hzb : IsMiddleOnChord r a b z) (hzw : IsMiddleOnChord r a z w) :
    IsMiddleOnChord r w b z := by
  rw [IsMiddleOnChord, openSegment_eq_image'] at hzb hzw ⊢
  obtain ⟨θz, hθz, hzeq⟩ := hzb
  obtain ⟨θw, hθw, hweq⟩ := hzw
  change knotMap r a + θz • (knotMap r b - knotMap r a) = knotMap r z at hzeq
  change knotMap r a + θw • (knotMap r z - knotMap r a) = knotMap r w at hweq
  have hθz0 : 0 < θz := hθz.1
  have hθz1 : θz < 1 := hθz.2
  have hθw0 : 0 < θw := hθw.1
  have hθw1 : θw < 1 := hθw.2
  have hprod : θw * θz < 1 := by nlinarith
  have hden : (0:ℝ) < 1 - θw * θz := by linarith
  have hzsub : knotMap r z - knotMap r a = θz • (knotMap r b - knotMap r a) := by
    rw [← hzeq]; abel
  have hwsub : knotMap r w - knotMap r a = (θw * θz) • (knotMap r b - knotMap r a) := by
    rw [← hweq, hzsub, smul_smul]
    abel
  have hb : knotMap r b - knotMap r w = (1 - θw * θz) • (knotMap r b - knotMap r a) := by
    have h1 : knotMap r b - knotMap r w
        = (knotMap r b - knotMap r a) - (knotMap r w - knotMap r a) := by abel
    rw [h1, hwsub]
    module
  refine ⟨θz * (1 - θw) / (1 - θw * θz), ⟨?_, ?_⟩, ?_⟩
  · exact div_pos (by positivity) hden
  · rw [div_lt_one hden]; nlinarith
  · change knotMap r w + (θz * (1 - θw) / (1 - θw * θz)) • (knotMap r b - knotMap r w) = knotMap r z
    rw [hb, smul_smul, div_mul_cancel₀ (θz * (1 - θw)) (ne_of_gt hden)]
    have hw2 : knotMap r w = knotMap r a + (θw * θz) • (knotMap r b - knotMap r a) := by
      rw [← hwsub]; abel
    rw [hw2, ← hzeq]
    module

/-- **All six sub-secants are non-trivial as soon as the three consecutive ones are** (Kuperberg's
Definition 3.2, forward direction).  The chord `(a,b)` has the two distinct strict middles `z ≠ w`;
the disjunction records the two possible orders along the chord (`a, w, z, b`, in which the
consecutive sub-secants are `(a,w)`, `(w,z)`, `(z,b)`, and `a, z, w, b`, in which they are `(a,z)`,
`(z,w)`, `(w,b)`).  The three remaining sub-secants contain a middle strictly inside and are
therefore automatically non-trivial. -/
lemma six_nontrivial_of_consecutive {r : ℝ → Space} {a b z w : AddCircle period}
    (hz : IsMiddleOnChord r a b z) (hw : IsMiddleOnChord r a b w) (_hne : z ≠ w)
    (h : (IsMiddleOnChord r a z w ∧ NontrivialSecant r a w ∧ NontrivialSecant r w z ∧
          NontrivialSecant r z b) ∨
         (IsMiddleOnChord r a w z ∧ NontrivialSecant r a z ∧ NontrivialSecant r z w ∧
          NontrivialSecant r w b)) :
    NontrivialSecant r a b ∧ NontrivialSecant r a z ∧ NontrivialSecant r a w ∧
      NontrivialSecant r z w ∧ NontrivialSecant r z b ∧ NontrivialSecant r w b := by
  rcases h with ⟨hzw, h1, h2, h3⟩ | ⟨hwz, h1, h2, h3⟩
  · -- order `a, w, z, b`: the automatic sub-secants are `(a,b)`, `(a,z)`, `(w,b)`
    exact ⟨nontrivialSecant_of_middle hz, nontrivialSecant_of_middle hzw, h1,
      (NontrivialSecant_swap r w z).mp h2, h3,
      nontrivialSecant_of_middle (middle_transfer_left hz hzw)⟩
  · -- order `a, z, w, b`: the automatic sub-secants are `(a,b)`, `(a,w)`, `(z,b)`
    exact ⟨nontrivialSecant_of_middle hz, h1, nontrivialSecant_of_middle hwz, h2,
      nontrivialSecant_of_middle (middle_transfer_left hw hwz), h3⟩

/-- **Kuperberg's reduction, in the form in which the hypothesis "no non-trivial quadrisecant" is
consumed**: if a chord with two distinct strict middles has a trivial sub-secant among its six, then
one of the three consecutive sub-secants is trivial (in the order in which the middles occur along
the chord). -/
lemma exists_trivial_consecutive_of_not_all_nontrivial {r : ℝ → Space} (hr : IsSmoothKnot r)
    {a b z w : AddCircle period} (hz : IsMiddleOnChord r a b z) (hw : IsMiddleOnChord r a b w)
    (hne : z ≠ w)
    (h : ¬ (NontrivialSecant r a b ∧ NontrivialSecant r a z ∧ NontrivialSecant r a w ∧
      NontrivialSecant r z w ∧ NontrivialSecant r z b ∧ NontrivialSecant r w b)) :
    (IsMiddleOnChord r a z w ∧
        (TrivialSecant r a w ∨ TrivialSecant r w z ∨ TrivialSecant r z b)) ∨
      (IsMiddleOnChord r a w z ∧
        (TrivialSecant r a z ∨ TrivialSecant r z w ∨ TrivialSecant r w b)) := by
  rcases middle_dichotomy hr hz hw hne with hzw | hwz
  · refine Or.inl ⟨hzw, ?_⟩
    by_contra hcon
    rw [not_or, not_or] at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    exact h (six_nontrivial_of_consecutive hz hw hne (Or.inl ⟨hzw, h1, h2, h3⟩))
  · refine Or.inr ⟨hwz, ?_⟩
    by_contra hcon
    rw [not_or, not_or] at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    exact h (six_nontrivial_of_consecutive hz hw hne (Or.inr ⟨hwz, h1, h2, h3⟩))

end Work.Drive
