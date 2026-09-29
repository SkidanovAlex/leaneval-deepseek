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

/-- Chunk `0 … 255`. -/
lemma gridSmallChk_0 : gridSmallChk 0 256 = true := by decide +kernel
/-- Chunk `256 … 511`. -/
lemma gridSmallChk_1 : gridSmallChk 256 256 = true := by decide +kernel
/-- Chunk `512 … 767`. -/
lemma gridSmallChk_2 : gridSmallChk 512 256 = true := by decide +kernel
/-- Chunk `768 … 1024`. -/
lemma gridSmallChk_3 : gridSmallChk 768 257 = true := by decide +kernel

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
