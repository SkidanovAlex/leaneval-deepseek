import Submission.Work.PinchFamily.CollarFamily
import Submission.Work.SurgeryInvariance.Loops

/-!
# The collar family as a `SweepLoops`, and hence as a `PinchSweep`

`Collar.lean` builds the three-piece family of the pinch from a collar, and
`collarRegion_localMoves` gives its local moves in the ε-form of `Work.PinchCounted.CountedStep`.
This module repackages the same family in the library's own sweep vocabulary: away from the two break
points `1/2, 3/4` the family is *locally constant* (so the loop content is transported), and at them
the two `SurgeryStepZero`s `surgeryStepZero_box_sdiff` / `surgeryStepZero_sdiff_halves` (and their
symmetries) apply.

Consequently the collar residual of this area gives the *family* residual of the previous chapter:

```
Work.PinchFamily.PinchCollarSpan  ⟹  Work.PinchCounted.CountedPinchSweep
```

which places this area's residuals above `CountedPinchSweep` in the ladder (`CountedPinchSweep`
itself gives `CountedPinch`, and `Sharp.lean` shows `CountedPinch` gives the push-off).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- The two break points of the collar family. -/
def collarExc : Finset ℝ := {1 / 2, 3 / 4}

theorem mem_collarExc {t : ℝ} : t ∈ collarExc ↔ t = 1 / 2 ∨ t = 3 / 4 := by
  simp [collarExc]

/-- **The collar family is locally constant away from the break points.** -/
theorem collarRegion_regular {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    {t : ℝ} (ht : t ∉ collarExc) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ r : ℝ, |r - t| < ε → r ∉ collarExc) ∧
      ∀ r : ℝ, |r - t| < ε →
        collarRegion P s c σ u Z r = collarRegion P s c σ u Z t := by
  have ht12 : t ≠ 1 / 2 := fun h => ht (mem_collarExc.mpr (Or.inl h))
  have ht34 : t ≠ 3 / 4 := fun h => ht (mem_collarExc.mpr (Or.inr h))
  have ha : 0 < |t - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr ht12)
  have hb : 0 < |t - 3 / 4| := abs_pos.mpr (sub_ne_zero.mpr ht34)
  refine ⟨min |t - 1 / 2| |t - 3 / 4| / 2, by positivity, ?_, ?_⟩
  · intro r hr
    have hr' := abs_lt.mp hr
    have hεa : min |t - 1 / 2| |t - 3 / 4| / 2 ≤ |t - 1 / 2| := by
      have := min_le_left |t - 1 / 2| |t - 3 / 4|; linarith
    have hεb : min |t - 1 / 2| |t - 3 / 4| / 2 ≤ |t - 3 / 4| := by
      have := min_le_right |t - 1 / 2| |t - 3 / 4|; linarith
    rw [mem_collarExc]
    rintro (h | h)
    · have h1 : |r - t| = |t - 1 / 2| := by rw [h, abs_sub_comm]
      linarith
    · have h1 : |r - t| = |t - 3 / 4| := by rw [h, abs_sub_comm]
      linarith
  · intro r hr
    have hr' := abs_lt.mp hr
    rcases lt_trichotomy t (1 / 2) with hlt | heq | hgt
    · -- the first piece
      have hε : min |t - 1 / 2| |t - 3 / 4| / 2 ≤ 1 / 2 - t := by
        have h2 : |t - 1 / 2| = -(t - 1 / 2) := abs_of_neg (by linarith : t - 1 / 2 < 0)
        rw [h2]
        have h3 := min_le_left (-(t - 1 / 2)) |t - 3 / 4|
        linarith
      have hr1 : r < 1 / 2 := by linarith [hr'.2, hε]
      rw [collarRegion_of_lt hr1, collarRegion_of_lt hlt]
    · exact absurd heq ht12
    · rcases lt_trichotomy t (3 / 4) with hlt34 | heq34 | hgt34
      · -- the middle piece
        have hε1 : min |t - 1 / 2| |t - 3 / 4| / 2 ≤ t - 1 / 2 := by
          have h2 : |t - 1 / 2| = t - 1 / 2 := abs_of_pos (by linarith : (0 : ℝ) < t - 1 / 2)
          rw [h2]
          have := min_le_left (t - 1 / 2) |t - 3 / 4|
          linarith
        have hε2 : min |t - 1 / 2| |t - 3 / 4| / 2 ≤ 3 / 4 - t := by
          have h2 : |t - 3 / 4| = -(t - 3 / 4) := abs_of_neg (by linarith : t - 3 / 4 < 0)
          rw [h2]
          have h3 := min_le_right |t - 1 / 2| (-(t - 3 / 4))
          linarith
        have hr1 : ¬ r < 1 / 2 := by intro hcon; linarith [hr'.1, hε1, hcon]
        have hr2 : r < 3 / 4 := by linarith [hr'.2, hε2]
        rw [collarRegion_of_mem hr1 hr2,
          collarRegion_of_mem (not_lt.mpr (le_of_lt hgt)) hlt34]
      · exact absurd heq34 ht34
      · -- the last piece
        have hε : min |t - 1 / 2| |t - 3 / 4| / 2 ≤ t - 3 / 4 := by
          have h2 : |t - 3 / 4| = t - 3 / 4 := abs_of_pos (by linarith : (0 : ℝ) < t - 3 / 4)
          rw [h2]
          have := min_le_right |t - 1 / 2| (t - 3 / 4)
          linarith
        have hr1 : ¬ r < 1 / 2 := by intro hcon; linarith [hr'.1, hε, hcon]
        have hr2 : ¬ r < 3 / 4 := by intro hcon; linarith [hr'.1, hε, hcon]
        rw [collarRegion_of_le hr1 hr2,
          collarRegion_of_le (by linarith) (by linarith)]

/-- **The local moves of the collar family at its break points.** -/
theorem collarRegion_surgery {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z) (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    {t : ℝ} (ht : t ∈ collarExc) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
      Work.SurgeryInvariance.SurgeryStepZero P (collarRegion P s c σ u Z t)
          (collarRegion P s c σ u Z r) ∨
        Work.SurgeryInvariance.RegionEquivalent P (collarRegion P s c σ u Z t)
          (collarRegion P s c σ u Z r) := by
  rcases mem_collarExc.mp ht with h | h
  · subst h
    refine ⟨1 / 8, by norm_num, fun r hr => ?_⟩
    have hr' := abs_lt.mp hr
    have ht1 : collarRegion P s c σ u Z (1 / 2) = box P s c σ \ Z :=
      collarRegion_of_mem (by norm_num) (by norm_num)
    by_cases hlt : r < 1 / 2
    · have hr1 : collarRegion P s c σ u Z r = box P s c σ := collarRegion_of_lt hlt
      exact Or.inl (by
        have := surgeryStepZero_box_sdiff (P := P) hZ hspan
        rw [ht1, hr1]
        exact this.symm)
    · have hr2 : r < 3 / 4 := by linarith [hr'.2]
      have hr1 : collarRegion P s c σ u Z r = box P s c σ \ Z :=
        collarRegion_of_mem hlt hr2
      exact Or.inr (by rw [ht1, hr1]; exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _)
  · subst h
    refine ⟨1 / 8, by norm_num, fun r hr => ?_⟩
    have hr' := abs_lt.mp hr
    have ht1 : collarRegion P s c σ u Z (3 / 4) = halves P s c σ u :=
      collarRegion_of_le (by norm_num) (by norm_num)
    by_cases hlt : r < 3 / 4
    · have hr2 : ¬ r < 1 / 2 := by linarith [hr'.1]
      have hr1 : collarRegion P s c σ u Z r = box P s c σ \ Z := collarRegion_of_mem hr2 hlt
      exact Or.inl (by
        have := surgeryStepZero_sdiff_halves (P := P) hZ hspan
        rw [ht1, hr1]
        exact this.symm)
    · have hr2 : ¬ r < 1 / 2 := by linarith [hr'.1]
      have hr1 : collarRegion P s c σ u Z r = halves P s c σ u :=
        collarRegion_of_le hr2 hlt
      exact Or.inr (by rw [ht1, hr1]; exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _)

/-- **The collar family is a loop-level sweep**: locally constant away from the two break points,
and the two `SurgeryStepZero`s at them. -/
def collarSweepLoops {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z) (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.SweepLoops P where
  region := collarRegion P s c σ u Z
  exc := collarExc
  regular := fun t ht => by
    obtain ⟨ε, hε, hnoexc, heq⟩ :=
      collarRegion_regular (P := P) (s := s) (c := c) (σ := σ) (u := u) (Z := Z) ht
    exact ⟨ε, hε, hnoexc, fun r hr => by
      rw [heq r hr]
      exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _⟩
  surgery := fun t ht => collarRegion_surgery (P := P) hZ hspan ht

/-- **The collar residual gives the family residual of the previous chapter.** -/
theorem countedPinchSweep_of_pinchCollarSpan (h : PinchCollarSpan) :
    Work.PinchCounted.CountedPinchSweep := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨Z, hZ, hspan⟩ :=
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact ⟨{ sweep := collarSweepLoops (P := Work.Smooth.Morse.torus ψ) hZ hspan
           zero := collarRegion_zero
           Z := ∅
           Z_open := Work.BoxShrink.Pinch.isOpenInCarrier_empty _
           Z_span := Work.BoxShrink.Pinch.windingSpan_empty _
           Z_disj := by simp
           one := by
             change collarRegion (Work.Smooth.Morse.torus ψ) s c σ u Z 1 =
               halves (Work.Smooth.Morse.torus ψ) s c σ u ∪ ∅
             rw [collarRegion_one, Set.union_empty] }⟩

end

end Work.PinchFamily
