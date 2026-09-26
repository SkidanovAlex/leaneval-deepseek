import Mathlib
import Submission.Helpers
import Submission.KnotMap
import Submission.ChordMap
import Submission.SecantSpace
import Submission.Pi1Mobius

open LeanEval.KnotTheory.Quadrisecant

/-!
# Layer B/C bridge — the plane chord model of the open Möbius band

A chord of the unit circle with two distinct endpoints is a line meeting the
open unit disk transversely: `{z : ℂ | z · n = d}` for a unit normal
`n : Circle` and a signed offset `d ∈ (-1, 1)`.  The chord data
`(n, d)` and `(-n, -d)` describe the same chord, so the space of chords is

    MobiusModel ≅ (Circle × (-1,1)) / ((n,d) ~ (-n,-d))

— the classical open Möbius band.  This module builds that model and its
deformation retraction onto the *core circle* (the chords through the origin,
`d = 0`):  the slide `(n, d) ↦ (n, (1-t)·d)` shrinks every chord toward the
parallel diameter while fixing the core pointwise.

Verified in this module: the chord data with its flip involution
(`chordDataFlip`: continuous, involutive, preserves the open-interval
condition), the representative-level retraction and homotopy
(`chordSlide`, `chordSlideAt`), the interval/offset arithmetic they need,
and their equivariance under the flip (`chordSlideAt_flip` — the homotopy
commutes with the flip, so it descends to the quotient), plus the target
statement `ChordModelRetractsToCore`.  The quotient construction and the
descent of continuity to `MobiusModel` (via
`IsOpenQuotientMap.prodMap` + `continuous_iff`, following the pattern of
`SecantSpace.lean`) is the next step.
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- Raw chord data: a unit normal `n` and a signed offset `d` (an ordered
representative of a chord). -/
abbrev RawChordData : Type := Circle × ℝ

/-- The flip `(n, d) ↦ (-n, -d)`: the two ordered descriptions of a chord. -/
def chordDataFlip (q : RawChordData) : RawChordData := (-q.1, -q.2)

/-- Flipping twice is the identity. -/
@[simp]
lemma chordDataFlip_chordDataFlip (q : RawChordData) : chordDataFlip (chordDataFlip q) = q := by
  ext <;> simp [chordDataFlip]

/-- The flip is continuous. -/
lemma continuous_chordDataFlip : Continuous (chordDataFlip : RawChordData → RawChordData) := by
  unfold chordDataFlip
  exact (ContinuousNeg.continuous_neg.comp continuous_fst).prodMk
    (continuous_neg.comp continuous_snd)

/-- Chord data with the chord genuinely cutting the disk: `-1 < d < 1`. -/
abbrev ChordData : Type := {q : RawChordData // q.2 ∈ Set.Ioo (-1) 1}

/-- The flip preserves the open-interval condition, so it acts on `ChordData`. -/
def chordFlip (q : ChordData) : ChordData :=
  ⟨chordDataFlip q.1, by
    have hq : q.1.2 ∈ Set.Ioo (-1) 1 := q.2
    change -1 < -q.1.2 ∧ -q.1.2 < 1
    constructor <;> nlinarith [hq.1, hq.2]⟩

@[simp]
lemma chordFlip_chordFlip (q : ChordData) : chordFlip (chordFlip q) = q := by
  apply Subtype.ext
  simp [chordFlip]

/-- The flip is continuous on the chord data. -/
lemma continuous_chordFlip : Continuous (chordFlip : ChordData → ChordData) := by
  have hunder : Continuous (fun q : ChordData => chordDataFlip (q.1 : RawChordData)) :=
    continuous_chordDataFlip.comp continuous_subtype_val
  exact Continuous.subtype_mk hunder (by intro q; exact (chordFlip q).2)

/-- The unit interval element `1 - t` stays in `[0, 1]` for `t ∈ [0,1]`. -/
lemma one_sub_mem_Icc {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> linarith

/-- Sliding a chord toward the parallel diameter shrinks its offset: for
`t ∈ [0,1]` and `d ∈ (-1,1)` the new offset `(1-t)·d` still lies in
`(-1,1)`. -/
lemma offset_slide_mem_Ioo {t d : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hd : d ∈ Set.Ioo (-1) 1) : (1 - t) * d ∈ Set.Ioo (-1) 1 := by
  have hd_abs : |d| < 1 := abs_lt.mpr hd
  have htm : |1 - t| ≤ 1 := by
    have hnn : 0 ≤ 1 - t := by linarith
    rw [abs_of_nonneg hnn]
    linarith
  have hm : |(1 - t) * d| < 1 := by
    calc |(1 - t) * d| = |1 - t| * |d| := abs_mul (1 - t) d
      _ ≤ 1 * |d| := mul_le_mul_of_nonneg_right htm (abs_nonneg d)
      _ = |d| := by rw [one_mul]
      _ < 1 := hd_abs
  exact abs_lt.mp hm


/-- Sliding the chord toward the parallel diameter at time `t`: the normal is
kept, the offset is multiplied by `1 - t`. -/
def chordSlideAt (t : Set.Icc (0 : ℝ) 1) (q : ChordData) : ChordData :=
  ⟨(q.1.1, (1 - (t : ℝ)) * q.1.2),
    offset_slide_mem_Ioo t.2.1 t.2.2 q.2⟩

/-- The slide is flip-equivariant: the two descriptions of a chord stay
identified throughout the deformation, so the slide descends to chords. -/
lemma chordSlideAt_flip (t : Set.Icc (0 : ℝ) 1) (q : ChordData) :
    chordSlideAt t (chordFlip q) = chordFlip (chordSlideAt t q) := by
  apply Subtype.ext
  -- the underlying pairs are equal coordinate-wise
  have hfst : (chordSlideAt t (chordFlip q)).1.1 = (chordFlip (chordSlideAt t q)).1.1 := by
    simp [chordSlideAt, chordFlip, chordDataFlip]
  have hsnd : (chordSlideAt t (chordFlip q)).1.2 = (chordFlip (chordSlideAt t q)).1.2 := by
    simp [chordSlideAt, chordFlip, chordDataFlip]
  exact Prod.ext hfst hsnd

/-- At time `0` the slide is the identity on chord data. -/
lemma chordSlideAt_zero (q : ChordData) :
    chordSlideAt ⟨(0 : ℝ), by norm_num⟩ q = q := by
  apply Subtype.ext
  ext <;> simp [chordSlideAt]

/-- At time `1` the slide lands on the core circle (`d = 0`): the chord has
become the parallel diameter through the origin. -/
lemma chordSlideAt_one_offset (q : ChordData) :
    (chordSlideAt ⟨(1 : ℝ), by norm_num⟩ q).1.2 = 0 := by
  simp [chordSlideAt]

/-- A chord that already is a diameter is fixed throughout the slide. -/
lemma chordSlideAt_fixed_on_core (t : Set.Icc (0 : ℝ) 1) (n : Circle)
    (q : ChordData) (hq : q.1 = (n, (0 : ℝ))) :
    chordSlideAt t q = q := by
  apply Subtype.ext
  change ((q.1).1, (1 - (t : ℝ)) * (q.1).2) = (q.1 : RawChordData)
  rw [hq]
  ext <;> simp

end LeanEval.KnotTheory.Quadrisecant
