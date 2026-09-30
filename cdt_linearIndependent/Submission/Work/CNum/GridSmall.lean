import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.SmallBox

/-!
# `Work.CNum.GridSmall` — every boundary box and the two cusp boxes are `Small`

`Small p` (`Submission/Work/CNum/SmallBox.lean`) is the mantissa-level side condition
`absMax p.re ≤ 2^32 ∧ absMax p.im ≤ 2^32` under which the mantissa square root `sqUp`
stays inside its `70`-step binary-search range.

Every entry of the grid `ptOf j` (`j ≤ 1024`) and the two cusp values `ptCuspA`, `ptCuspB`
is a *closed* integer expression (`expI`, the Taylor table `csOf`, the interval square root
`IvS`, …).  `Small` is therefore decidable at the mantissa level, and the whole range is
discharged by kernel evaluation of a `Bool` checker; the range is cut into four chunks so
that no single `decide` invocation carries the entire table.
-/

namespace Work.CNum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! ## The decidable mantissa-level side condition -/

/-- `Small p`, unfolded into a `Bool` so that the kernel can evaluate it directly. -/
def gridSmallOKb (p : Cpx) : Bool :=
  decide (absMax p.re ≤ 2 ^ 32) && decide (absMax p.im ≤ 2 ^ 32)

lemma gridSmallOKb_sound {p : Cpx} (h : gridSmallOKb p = true) : Small p := by
  simp only [gridSmallOKb, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- `gridSmallChk a n` checks the side condition at `ptOf a, …, ptOf (a+n-1)`. -/
def gridSmallChk (a : ℕ) : ℕ → Bool
  | 0 => true
  | (n + 1) => gridSmallOKb (ptOf (a + n)) && gridSmallChk a n

lemma gridSmallChk_sound : ∀ (a n : ℕ), gridSmallChk a n = true →
    ∀ j, a ≤ j → j < a + n → Small (ptOf j) := by
  intro a n
  induction n with
  | zero => intro h j h1 h2; omega
  | succ n ih =>
    intro h j h1 h2
    simp only [gridSmallChk, Bool.and_eq_true] at h
    rcases h with ⟨h1', h2'⟩
    rcases lt_or_ge j (a + n) with hj | hj
    · exact ih h2' j h1 hj
    · have : j = a + n := by omega
      subst this
      exact gridSmallOKb_sound h1'

/-- splitting a `gridSmallChk` range (nanoda memory: each piece is its own small kernel check). -/
lemma gridSmallChk_add (a m : ℕ) : ∀ n, gridSmallChk a (m + n) = (gridSmallChk (a + m) n && gridSmallChk a m)
  | 0 => by simp [gridSmallChk]
  | n + 1 => by
      show gridSmallChk a ((m + n) + 1) = (gridSmallChk (a + m) (n + 1) && gridSmallChk a m)
      simp only [gridSmallChk, gridSmallChk_add a m n, Nat.add_assoc, Bool.and_assoc]

lemma gridSmallChk_blocks (a : ℕ) : ∀ q, (∀ i < q, gridSmallChk (a + 16 * i) 16 = true) → gridSmallChk a (16 * q) = true
  | 0, _ => rfl
  | q + 1, h => by
      rw [show 16 * (q + 1) = 16 * q + 16 by ring, gridSmallChk_add, h q (by omega),
        gridSmallChk_blocks a q (fun i hi => h i (by omega))]
      rfl

lemma gridSmallChk_0p0 : gridSmallChk 0 16 = true := by decide +kernel
lemma gridSmallChk_0p1 : gridSmallChk 16 16 = true := by decide +kernel
lemma gridSmallChk_0p2 : gridSmallChk 32 16 = true := by decide +kernel
lemma gridSmallChk_0p3 : gridSmallChk 48 16 = true := by decide +kernel
lemma gridSmallChk_0p4 : gridSmallChk 64 16 = true := by decide +kernel
lemma gridSmallChk_0p5 : gridSmallChk 80 16 = true := by decide +kernel
lemma gridSmallChk_0p6 : gridSmallChk 96 16 = true := by decide +kernel
lemma gridSmallChk_0p7 : gridSmallChk 112 16 = true := by decide +kernel
lemma gridSmallChk_0p8 : gridSmallChk 128 16 = true := by decide +kernel
lemma gridSmallChk_0p9 : gridSmallChk 144 16 = true := by decide +kernel
lemma gridSmallChk_0p10 : gridSmallChk 160 16 = true := by decide +kernel
lemma gridSmallChk_0p11 : gridSmallChk 176 16 = true := by decide +kernel
lemma gridSmallChk_0p12 : gridSmallChk 192 16 = true := by decide +kernel
lemma gridSmallChk_0p13 : gridSmallChk 208 16 = true := by decide +kernel
lemma gridSmallChk_0p14 : gridSmallChk 224 16 = true := by decide +kernel
lemma gridSmallChk_0p15 : gridSmallChk 240 16 = true := by decide +kernel
lemma gridSmallChk_0 : gridSmallChk 0 256 = true :=
  gridSmallChk_blocks 0 16 (fun i hi => match i, hi with
    | 0, _ => gridSmallChk_0p0
    | 1, _ => gridSmallChk_0p1
    | 2, _ => gridSmallChk_0p2
    | 3, _ => gridSmallChk_0p3
    | 4, _ => gridSmallChk_0p4
    | 5, _ => gridSmallChk_0p5
    | 6, _ => gridSmallChk_0p6
    | 7, _ => gridSmallChk_0p7
    | 8, _ => gridSmallChk_0p8
    | 9, _ => gridSmallChk_0p9
    | 10, _ => gridSmallChk_0p10
    | 11, _ => gridSmallChk_0p11
    | 12, _ => gridSmallChk_0p12
    | 13, _ => gridSmallChk_0p13
    | 14, _ => gridSmallChk_0p14
    | 15, _ => gridSmallChk_0p15
    | _ + 16, h => absurd h (by omega))
lemma gridSmallChk_1p0 : gridSmallChk 256 16 = true := by decide +kernel
lemma gridSmallChk_1p1 : gridSmallChk 272 16 = true := by decide +kernel
lemma gridSmallChk_1p2 : gridSmallChk 288 16 = true := by decide +kernel
lemma gridSmallChk_1p3 : gridSmallChk 304 16 = true := by decide +kernel
lemma gridSmallChk_1p4 : gridSmallChk 320 16 = true := by decide +kernel
lemma gridSmallChk_1p5 : gridSmallChk 336 16 = true := by decide +kernel
lemma gridSmallChk_1p6 : gridSmallChk 352 16 = true := by decide +kernel
lemma gridSmallChk_1p7 : gridSmallChk 368 16 = true := by decide +kernel
lemma gridSmallChk_1p8 : gridSmallChk 384 16 = true := by decide +kernel
lemma gridSmallChk_1p9 : gridSmallChk 400 16 = true := by decide +kernel
lemma gridSmallChk_1p10 : gridSmallChk 416 16 = true := by decide +kernel
lemma gridSmallChk_1p11 : gridSmallChk 432 16 = true := by decide +kernel
lemma gridSmallChk_1p12 : gridSmallChk 448 16 = true := by decide +kernel
lemma gridSmallChk_1p13 : gridSmallChk 464 16 = true := by decide +kernel
lemma gridSmallChk_1p14 : gridSmallChk 480 16 = true := by decide +kernel
lemma gridSmallChk_1p15 : gridSmallChk 496 16 = true := by decide +kernel
lemma gridSmallChk_1 : gridSmallChk 256 256 = true :=
  gridSmallChk_blocks 256 16 (fun i hi => match i, hi with
    | 0, _ => gridSmallChk_1p0
    | 1, _ => gridSmallChk_1p1
    | 2, _ => gridSmallChk_1p2
    | 3, _ => gridSmallChk_1p3
    | 4, _ => gridSmallChk_1p4
    | 5, _ => gridSmallChk_1p5
    | 6, _ => gridSmallChk_1p6
    | 7, _ => gridSmallChk_1p7
    | 8, _ => gridSmallChk_1p8
    | 9, _ => gridSmallChk_1p9
    | 10, _ => gridSmallChk_1p10
    | 11, _ => gridSmallChk_1p11
    | 12, _ => gridSmallChk_1p12
    | 13, _ => gridSmallChk_1p13
    | 14, _ => gridSmallChk_1p14
    | 15, _ => gridSmallChk_1p15
    | _ + 16, h => absurd h (by omega))
lemma gridSmallChk_2p0 : gridSmallChk 512 16 = true := by decide +kernel
lemma gridSmallChk_2p1 : gridSmallChk 528 16 = true := by decide +kernel
lemma gridSmallChk_2p2 : gridSmallChk 544 16 = true := by decide +kernel
lemma gridSmallChk_2p3 : gridSmallChk 560 16 = true := by decide +kernel
lemma gridSmallChk_2p4 : gridSmallChk 576 16 = true := by decide +kernel
lemma gridSmallChk_2p5 : gridSmallChk 592 16 = true := by decide +kernel
lemma gridSmallChk_2p6 : gridSmallChk 608 16 = true := by decide +kernel
lemma gridSmallChk_2p7 : gridSmallChk 624 16 = true := by decide +kernel
lemma gridSmallChk_2p8 : gridSmallChk 640 16 = true := by decide +kernel
lemma gridSmallChk_2p9 : gridSmallChk 656 16 = true := by decide +kernel
lemma gridSmallChk_2p10 : gridSmallChk 672 16 = true := by decide +kernel
lemma gridSmallChk_2p11 : gridSmallChk 688 16 = true := by decide +kernel
lemma gridSmallChk_2p12 : gridSmallChk 704 16 = true := by decide +kernel
lemma gridSmallChk_2p13 : gridSmallChk 720 16 = true := by decide +kernel
lemma gridSmallChk_2p14 : gridSmallChk 736 16 = true := by decide +kernel
lemma gridSmallChk_2p15 : gridSmallChk 752 16 = true := by decide +kernel
lemma gridSmallChk_2 : gridSmallChk 512 256 = true :=
  gridSmallChk_blocks 512 16 (fun i hi => match i, hi with
    | 0, _ => gridSmallChk_2p0
    | 1, _ => gridSmallChk_2p1
    | 2, _ => gridSmallChk_2p2
    | 3, _ => gridSmallChk_2p3
    | 4, _ => gridSmallChk_2p4
    | 5, _ => gridSmallChk_2p5
    | 6, _ => gridSmallChk_2p6
    | 7, _ => gridSmallChk_2p7
    | 8, _ => gridSmallChk_2p8
    | 9, _ => gridSmallChk_2p9
    | 10, _ => gridSmallChk_2p10
    | 11, _ => gridSmallChk_2p11
    | 12, _ => gridSmallChk_2p12
    | 13, _ => gridSmallChk_2p13
    | 14, _ => gridSmallChk_2p14
    | 15, _ => gridSmallChk_2p15
    | _ + 16, h => absurd h (by omega))
lemma gridSmallChk_3p0 : gridSmallChk 768 16 = true := by decide +kernel
lemma gridSmallChk_3p1 : gridSmallChk 784 16 = true := by decide +kernel
lemma gridSmallChk_3p2 : gridSmallChk 800 16 = true := by decide +kernel
lemma gridSmallChk_3p3 : gridSmallChk 816 16 = true := by decide +kernel
lemma gridSmallChk_3p4 : gridSmallChk 832 16 = true := by decide +kernel
lemma gridSmallChk_3p5 : gridSmallChk 848 16 = true := by decide +kernel
lemma gridSmallChk_3p6 : gridSmallChk 864 16 = true := by decide +kernel
lemma gridSmallChk_3p7 : gridSmallChk 880 16 = true := by decide +kernel
lemma gridSmallChk_3p8 : gridSmallChk 896 16 = true := by decide +kernel
lemma gridSmallChk_3p9 : gridSmallChk 912 16 = true := by decide +kernel
lemma gridSmallChk_3p10 : gridSmallChk 928 16 = true := by decide +kernel
lemma gridSmallChk_3p11 : gridSmallChk 944 16 = true := by decide +kernel
lemma gridSmallChk_3p12 : gridSmallChk 960 16 = true := by decide +kernel
lemma gridSmallChk_3p13 : gridSmallChk 976 16 = true := by decide +kernel
lemma gridSmallChk_3p14 : gridSmallChk 992 16 = true := by decide +kernel
lemma gridSmallChk_3p15 : gridSmallChk 1008 16 = true := by decide +kernel
lemma gridSmallChk_3last : gridSmallChk 1024 1 = true := by decide +kernel
lemma gridSmallChk_3 : gridSmallChk 768 257 = true := by
  rw [show (257 : ℕ) = 256 + 1 from rfl, gridSmallChk_add, gridSmallChk_3last,
    (gridSmallChk_blocks 768 16 (fun i hi => match i, hi with
    | 0, _ => gridSmallChk_3p0
    | 1, _ => gridSmallChk_3p1
    | 2, _ => gridSmallChk_3p2
    | 3, _ => gridSmallChk_3p3
    | 4, _ => gridSmallChk_3p4
    | 5, _ => gridSmallChk_3p5
    | 6, _ => gridSmallChk_3p6
    | 7, _ => gridSmallChk_3p7
    | 8, _ => gridSmallChk_3p8
    | 9, _ => gridSmallChk_3p9
    | 10, _ => gridSmallChk_3p10
    | 11, _ => gridSmallChk_3p11
    | 12, _ => gridSmallChk_3p12
    | 13, _ => gridSmallChk_3p13
    | 14, _ => gridSmallChk_3p14
    | 15, _ => gridSmallChk_3p15
    | _ + 16, h => absurd h (by omega)) : gridSmallChk 768 (16 * 16) = true)]
  rfl

theorem GridSmall : (∀ j : ℕ, j ≤ 1024 → Work.CNum.Small (Work.CNum.ptOf j)) ∧ Work.CNum.Small Work.CNum.ptCuspA ∧ Work.CNum.Small Work.CNum.ptCuspB := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rcases le_or_gt j 255 with h | h
    · exact gridSmallChk_sound 0 256 gridSmallChk_0 j (by omega) (by omega)
    rcases le_or_gt j 511 with h2 | h2
    · exact gridSmallChk_sound 256 256 gridSmallChk_1 j (by omega) (by omega)
    rcases le_or_gt j 767 with h3 | h3
    · exact gridSmallChk_sound 512 256 gridSmallChk_2 j (by omega) (by omega)
    · exact gridSmallChk_sound 768 257 gridSmallChk_3 j (by omega) (by omega)
  · exact gridSmallOKb_sound (by decide +kernel)
  · exact gridSmallOKb_sound (by decide +kernel)

end Work.CNum
