/-
# `lam0_fm_box_five` — the support of the `nearP3sum` summand lies in the box `0 ≤ Re ≤ 1`,
`|Im| ≤ 5`.

This is a self-contained, `sorry`-free replacement for
`Work.ZeroFreeTables.lam0w.nearP3summand_mem_box_five` (which is currently a placeholder in a
colleague's file); the statement is identical apart from the name.  The `|Im| ≤ 5` and the lower
bound `0 ≤ Re` come from the `δ`-window (`δ < 1`, `|Im s| ≤ 4`), while the upper bound `Re ≤ 1`
is the (character-independent) fact `zeroMult_re_lt_one` that zeros of a completed `L`-function
have real part `< 1`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs
import Submission.Work.LinnikAreas.boxMaxZero

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.lam0w

theorem nearP3summand_mem_box_five_fm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {L a lam₁ δ : ℝ} (hδ1 : δ < 1) {s : ℂ} (hsim : |s.im| ≤ 4) (u : ℂ)
    (hu : Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u ≠ 0) :
    Work.LinnikContract.zeroMult χ u ≠ 0 ∧ 0 ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 5 := by
  have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := by
    intro h0
    exact hu (by simp [Work.ZeroFreeTables.P9.nearP3summand, h0])
  have hind : Work.ZeroFreeTables.P9.nearInd s δ u ≠ 0 := by
    intro h0
    exact hu (by simp [Work.ZeroFreeTables.P9.nearP3summand, h0])
  have hcond : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
    by_contra hc
    exact hind (by simp [Work.ZeroFreeTables.P9.nearInd, hc])
  set w : ℂ := (1 : ℂ) + (s.im : ℂ) * Complex.I - u with hw
  have hwre : w.re = 1 - u.re := by simp [hw]
  have hwim : w.im = s.im - u.im := by simp [hw]
  have hlt1 : ‖w‖ < 1 := by
    rw [hw]
    exact lt_of_le_of_lt hcond hδ1
  have h1 : |1 - u.re| < 1 := by
    rw [← hwre]
    exact lt_of_le_of_lt (Complex.abs_re_le_norm w) hlt1
  have hr0 : 0 ≤ u.re := by
    have h := (abs_lt.mp h1).2
    linarith
  have h2 : |s.im - u.im| < 1 := by
    rw [← hwim]
    exact lt_of_le_of_lt (Complex.abs_im_le_norm w) hlt1
  have hi5 : |u.im| ≤ 5 := by
    rw [abs_le]
    have hs4 := abs_le.mp hsim
    have h2' := abs_lt.mp h2
    constructor <;> linarith [hs4.1, hs4.2, h2'.1, h2'.2]
  have hr1 : u.re ≤ 1 :=
    le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm)
  exact ⟨hzm, hr0, hr1, hi5⟩

end Work.ZeroFreeTables.lam0w
