import Mathlib
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroFreeTables.P9

/-- If the `nearP3summand` at `u` is nonzero, then `u` is a genuine non-zero-multiplicity zero
of `L(·,χ)` lying in the box `1 - δ ≤ Re ≤ 1`, `|Im| ≤ |Im s| + δ`.

The near indicator forces `u` into the closed disc of radius `δ` around `1 + i·Im s`, giving
`|1 - u.re| ≤ δ` (hence `1 - δ ≤ u.re`) and `|Im s - u.im| ≤ δ` (hence `|u.im| ≤ |s.im| + δ`),
while `zeroMult_re_lt_one` gives `Re u < 1`.  No hypothesis on `δ`, on `|Im s|` or on `χ` is
needed. -/
theorem NearP3summandMemBoxGen {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {L a lam₁ δ : ℝ} {s u : ℂ}
    (hu : Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u ≠ 0) :
    Work.LinnikContract.zeroMult χ u ≠ 0 ∧ 1 - δ ≤ u.re ∧ u.re ≤ 1
      ∧ |u.im| ≤ |s.im| + δ := by
  unfold nearP3summand at hu
  have h1 : (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u ≠ 0 :=
    (mul_ne_zero_iff.mp hu).1
  have hzmR : (Work.LinnikContract.zeroMult χ u : ℝ) ≠ 0 := (mul_ne_zero_iff.mp h1).1
  have hni : nearInd s δ u ≠ 0 := (mul_ne_zero_iff.mp h1).2
  have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := Nat.cast_ne_zero.mp hzmR
  have hcond : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
    by_contra h
    unfold nearInd at hni
    rw [if_neg h] at hni
    exact hni rfl
  have hre : |1 - u.re| ≤ δ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
    simpa using le_trans h hcond
  have him : |s.im - u.im| ≤ δ := by
    have h := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
    simpa using le_trans h hcond
  refine ⟨hzm, ?_, ?_, ?_⟩
  · have h' : 1 - u.re ≤ δ := (abs_le.mp hre).2
    linarith
  · exact le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm)
  · have h2 : |u.im| ≤ |u.im - s.im| + |s.im| := by
      have := abs_add_le (u.im - s.im) s.im
      simpa using this
    have h3 : |u.im - s.im| = |s.im - u.im| := abs_sub_comm _ _
    linarith [h2, h3 ▸ him]

end Work.ZeroFreeTables.P9
