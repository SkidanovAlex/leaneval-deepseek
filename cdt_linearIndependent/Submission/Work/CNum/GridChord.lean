import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.SmallBox

/-!
# `Work.CNum.GridChord` — the consecutive-grid chord bounds of the CNum certificate

The certificate `Fx` bounds the boundary function `circleLog` on each of the `1024` arcs by
`Gv k = max svUp + chord`, and `chord` is a function of the *chord lengths*
`dWup (ptOf k) (ptOf (k+1))`, `dVup (ptOf k) (ptOf (k+1))` in the two coordinate systems.  The
numeric content needed later is that all these chord lengths are bounded by `SC / 5`, i.e. that
five copies of `dWup`, resp. `dVup`, fit into one unit `SC = 2^30`.

Each `dWup`/`dVup` value is an integer mantissa computed from the interval enclosures `ptOf k`
(`Fx`); the statement is therefore decidable at the mantissa level and is discharged by kernel
evaluation.  The range `k ∈ [0, 1024)` is cut into `64` chunks of `16` consecutive indices (each a
separate `decide +kernel`), and the chunks are glued by `gridChordChk_sound`; the four extra
comparisons at the cusps `α` and `2π-α` are single kernel evaluations.
-/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! ## The `Bool` checker -/

/-- `5·dWup a b ≤ SC ∧ 5·dVup a b ≤ SC`, as a `Bool` (so that the kernel can evaluate it). -/
private def gridChordOKb (a b : Cpx) : Bool :=
  decide (5 * dWup a b ≤ SC) && decide (5 * dVup a b ≤ SC)

private lemma gridChordOKb_sound {a b : Cpx} (h : gridChordOKb a b = true) :
    5 * dWup a b ≤ SC ∧ 5 * dVup a b ≤ SC := by
  simpa only [gridChordOKb, Bool.and_eq_true, decide_eq_true_eq] using h

/-- `gridChordChk a n` checks the chord bounds at `ptOf a, …, ptOf (a+n)`. -/
private def gridChordChk (a : ℕ) : ℕ → Bool
  | 0 => true
  | (n + 1) => gridChordOKb (ptOf (a + n)) (ptOf (a + n + 1)) && gridChordChk a n

private lemma gridChordChk_sound : ∀ (a n : ℕ), gridChordChk a n = true →
    ∀ j, a ≤ j → j < a + n →
      5 * dWup (ptOf j) (ptOf (j + 1)) ≤ SC ∧ 5 * dVup (ptOf j) (ptOf (j + 1)) ≤ SC := by
  intro a n
  induction n with
  | zero => intro h j h1 h2; omega
  | succ n ih =>
    intro h j h1 h2
    simp only [gridChordChk, Bool.and_eq_true] at h
    obtain ⟨h1', h2'⟩ := h
    rcases lt_or_ge j (a + n) with hj | hj
    · exact ih h2' j h1 hj
    · have hje : j = a + n := by omega
      subst hje
      exact gridChordOKb_sound h1'

/-! ## The `64` chunks of the range `[0, 1024)` -/

private lemma gridChordChk_0 : gridChordChk 0 16 = true := by decide +kernel
private lemma gridChordChk_16 : gridChordChk 16 16 = true := by decide +kernel
private lemma gridChordChk_32 : gridChordChk 32 16 = true := by decide +kernel
private lemma gridChordChk_48 : gridChordChk 48 16 = true := by decide +kernel
private lemma gridChordChk_64 : gridChordChk 64 16 = true := by decide +kernel
private lemma gridChordChk_80 : gridChordChk 80 16 = true := by decide +kernel
private lemma gridChordChk_96 : gridChordChk 96 16 = true := by decide +kernel
private lemma gridChordChk_112 : gridChordChk 112 16 = true := by decide +kernel
private lemma gridChordChk_128 : gridChordChk 128 16 = true := by decide +kernel
private lemma gridChordChk_144 : gridChordChk 144 16 = true := by decide +kernel
private lemma gridChordChk_160 : gridChordChk 160 16 = true := by decide +kernel
private lemma gridChordChk_176 : gridChordChk 176 16 = true := by decide +kernel
private lemma gridChordChk_192 : gridChordChk 192 16 = true := by decide +kernel
private lemma gridChordChk_208 : gridChordChk 208 16 = true := by decide +kernel
private lemma gridChordChk_224 : gridChordChk 224 16 = true := by decide +kernel
private lemma gridChordChk_240 : gridChordChk 240 16 = true := by decide +kernel
private lemma gridChordChk_256 : gridChordChk 256 16 = true := by decide +kernel
private lemma gridChordChk_272 : gridChordChk 272 16 = true := by decide +kernel
private lemma gridChordChk_288 : gridChordChk 288 16 = true := by decide +kernel
private lemma gridChordChk_304 : gridChordChk 304 16 = true := by decide +kernel
private lemma gridChordChk_320 : gridChordChk 320 16 = true := by decide +kernel
private lemma gridChordChk_336 : gridChordChk 336 16 = true := by decide +kernel
private lemma gridChordChk_352 : gridChordChk 352 16 = true := by decide +kernel
private lemma gridChordChk_368 : gridChordChk 368 16 = true := by decide +kernel
private lemma gridChordChk_384 : gridChordChk 384 16 = true := by decide +kernel
private lemma gridChordChk_400 : gridChordChk 400 16 = true := by decide +kernel
private lemma gridChordChk_416 : gridChordChk 416 16 = true := by decide +kernel
private lemma gridChordChk_432 : gridChordChk 432 16 = true := by decide +kernel
private lemma gridChordChk_448 : gridChordChk 448 16 = true := by decide +kernel
private lemma gridChordChk_464 : gridChordChk 464 16 = true := by decide +kernel
private lemma gridChordChk_480 : gridChordChk 480 16 = true := by decide +kernel
private lemma gridChordChk_496 : gridChordChk 496 16 = true := by decide +kernel
private lemma gridChordChk_512 : gridChordChk 512 16 = true := by decide +kernel
private lemma gridChordChk_528 : gridChordChk 528 16 = true := by decide +kernel
private lemma gridChordChk_544 : gridChordChk 544 16 = true := by decide +kernel
private lemma gridChordChk_560 : gridChordChk 560 16 = true := by decide +kernel
private lemma gridChordChk_576 : gridChordChk 576 16 = true := by decide +kernel
private lemma gridChordChk_592 : gridChordChk 592 16 = true := by decide +kernel
private lemma gridChordChk_608 : gridChordChk 608 16 = true := by decide +kernel
private lemma gridChordChk_624 : gridChordChk 624 16 = true := by decide +kernel
private lemma gridChordChk_640 : gridChordChk 640 16 = true := by decide +kernel
private lemma gridChordChk_656 : gridChordChk 656 16 = true := by decide +kernel
private lemma gridChordChk_672 : gridChordChk 672 16 = true := by decide +kernel
private lemma gridChordChk_688 : gridChordChk 688 16 = true := by decide +kernel
private lemma gridChordChk_704 : gridChordChk 704 16 = true := by decide +kernel
private lemma gridChordChk_720 : gridChordChk 720 16 = true := by decide +kernel
private lemma gridChordChk_736 : gridChordChk 736 16 = true := by decide +kernel
private lemma gridChordChk_752 : gridChordChk 752 16 = true := by decide +kernel
private lemma gridChordChk_768 : gridChordChk 768 16 = true := by decide +kernel
private lemma gridChordChk_784 : gridChordChk 784 16 = true := by decide +kernel
private lemma gridChordChk_800 : gridChordChk 800 16 = true := by decide +kernel
private lemma gridChordChk_816 : gridChordChk 816 16 = true := by decide +kernel
private lemma gridChordChk_832 : gridChordChk 832 16 = true := by decide +kernel
private lemma gridChordChk_848 : gridChordChk 848 16 = true := by decide +kernel
private lemma gridChordChk_864 : gridChordChk 864 16 = true := by decide +kernel
private lemma gridChordChk_880 : gridChordChk 880 16 = true := by decide +kernel
private lemma gridChordChk_896 : gridChordChk 896 16 = true := by decide +kernel
private lemma gridChordChk_912 : gridChordChk 912 16 = true := by decide +kernel
private lemma gridChordChk_928 : gridChordChk 928 16 = true := by decide +kernel
private lemma gridChordChk_944 : gridChordChk 944 16 = true := by decide +kernel
private lemma gridChordChk_960 : gridChordChk 960 16 = true := by decide +kernel
private lemma gridChordChk_976 : gridChordChk 976 16 = true := by decide +kernel
private lemma gridChordChk_992 : gridChordChk 992 16 = true := by decide +kernel
private lemma gridChordChk_1008 : gridChordChk 1008 16 = true := by decide +kernel

/-- The chunk table, assembled from the individual kernel evaluations. -/
private lemma gridChordChk_range (i : ℕ) (hi : i < 64) : gridChordChk (16 * i) 16 = true := by
  interval_cases i <;> norm_num <;> simp only [gridChordChk_0, gridChordChk_16, gridChordChk_32, gridChordChk_48, gridChordChk_64, gridChordChk_80, gridChordChk_96, gridChordChk_112, gridChordChk_128, gridChordChk_144, gridChordChk_160, gridChordChk_176, gridChordChk_192, gridChordChk_208, gridChordChk_224, gridChordChk_240, gridChordChk_256, gridChordChk_272, gridChordChk_288, gridChordChk_304, gridChordChk_320, gridChordChk_336, gridChordChk_352, gridChordChk_368, gridChordChk_384, gridChordChk_400, gridChordChk_416, gridChordChk_432, gridChordChk_448, gridChordChk_464, gridChordChk_480, gridChordChk_496, gridChordChk_512, gridChordChk_528, gridChordChk_544, gridChordChk_560, gridChordChk_576, gridChordChk_592, gridChordChk_608, gridChordChk_624, gridChordChk_640, gridChordChk_656, gridChordChk_672, gridChordChk_688, gridChordChk_704, gridChordChk_720, gridChordChk_736, gridChordChk_752, gridChordChk_768, gridChordChk_784, gridChordChk_800, gridChordChk_816, gridChordChk_832, gridChordChk_848, gridChordChk_864, gridChordChk_880, gridChordChk_896, gridChordChk_912, gridChordChk_928, gridChordChk_944, gridChordChk_960, gridChordChk_976, gridChordChk_992, gridChordChk_1008]

/-- Every chord bound on the range `[0, 1024)`. -/
private lemma gridChordRange (j : ℕ) (hj : j < 1024) :
    5 * dWup (ptOf j) (ptOf (j + 1)) ≤ SC ∧ 5 * dVup (ptOf j) (ptOf (j + 1)) ≤ SC := by
  have hi : j / 16 < 64 := by omega
  have h := gridChordChk_range (j / 16) hi
  exact gridChordChk_sound (16 * (j / 16)) 16 h j (by omega) (by omega)

theorem GridChord :
    (∀ k : ℕ, k ≤ 1023 → 5 * Work.CNum.dWup (Work.CNum.ptOf k) (Work.CNum.ptOf (k + 1)) ≤ Work.ANum.SC)
    ∧ (∀ k : ℕ, k ≤ 1023 → 5 * Work.CNum.dVup (Work.CNum.ptOf k) (Work.CNum.ptOf (k + 1)) ≤ Work.ANum.SC)
    ∧ 5 * Work.CNum.dWup (Work.CNum.ptOf 244) Work.CNum.ptCuspA ≤ Work.ANum.SC
    ∧ 5 * Work.CNum.dWup (Work.CNum.ptOf 780) Work.CNum.ptCuspB ≤ Work.ANum.SC
    ∧ 5 * Work.CNum.dVup (Work.CNum.ptOf 245) Work.CNum.ptCuspA ≤ Work.ANum.SC
    ∧ 5 * Work.CNum.dVup (Work.CNum.ptOf 779) Work.CNum.ptCuspB ≤ Work.ANum.SC := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; exact (gridChordRange k (by omega)).1
  · intro k hk; exact (gridChordRange k (by omega)).2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end Work.CNum
