import Mathlib
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroFreeTables.P9

/-- If the `nearP3summand` at `u` is nonzero, then `u` is a genuine non-zero-multiplicity zero
of `L(·,χ)` lying in the box `0 ≤ Re ≤ 1`, `|Im| ≤ 4`.  The near indicator forces `u` into the
open unit disc around `1 + i·Im s`, which gives `0 < Re u` and `|u.im| ≤ |s.im| + 1 ≤ 4`, while
`zeroMult_re_lt_one` gives `Re u < 1`. -/
theorem nearP3summand_mem_box {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {L a lam₁ δ : ℝ} (hδ1 : δ < 1) {s : ℂ} (hsim : |s.im| ≤ 3) (u : ℂ)
    (hu : Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u ≠ 0) :
    Work.LinnikContract.zeroMult χ u ≠ 0 ∧ 0 ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 4 := by
  unfold nearP3summand at hu
  have h1 : (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u ≠ 0 :=
    (mul_ne_zero_iff.mp hu).1
  have hzmR : (Work.LinnikContract.zeroMult χ u : ℝ) ≠ 0 := (mul_ne_zero_iff.mp h1).1
  have hni : nearInd s δ u ≠ 0 := (mul_ne_zero_iff.mp h1).2
  have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := Nat.cast_ne_zero.mp hzmR
  -- the near indicator is nonzero, so the disc condition holds
  have hcond : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
    by_contra h
    unfold nearInd at hni
    rw [if_neg h] at hni
    exact hni rfl
  have hlt : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ < 1 := lt_of_le_of_lt hcond hδ1
  have hre : |1 - u.re| < 1 := by
    have h := lt_of_le_of_lt (Complex.abs_re_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)) hlt
    simpa using h
  have him : |s.im - u.im| < 1 := by
    have h := lt_of_le_of_lt (Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)) hlt
    simpa using h
  refine ⟨hzm, ?_, ?_, ?_⟩
  · have h' : 1 - u.re < 1 := (abs_lt.mp hre).2
    linarith
  · exact le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm)
  · have h1' : |u.im - s.im| < 1 := abs_sub_comm s.im u.im ▸ him
    have h2 : |u.im| ≤ |u.im - s.im| + |s.im| := by
      have := abs_add_le (u.im - s.im) s.im
      simpa using this
    linarith

end Work.ZeroFreeTables.P9
