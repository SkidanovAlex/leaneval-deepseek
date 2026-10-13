import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.NonlinRows.AkRhoJetBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.NonlinRows.AkRhoJetBasic (akRho akRho_abs_le akJet_mul_w)

/-- `z ↦ 2z²/(1+z)³` and its `z∂_z`-iterates vanish at `0`: for `i ≥ 1` this is because `z∂_z`
carries a factor `z`, and `SR0 0 = 0`. -/
lemma DzdIter_SR0_zero (i : ℕ) : Work.Elliptic.DzdIter i SR0 0 = 0 := by
  cases i with
  | zero => simp [Work.Elliptic.DzdIter_zero, SR0]
  | succ k => rw [Work.Elliptic.DzdIter_succ]; simp [Work.Elliptic.Dzd]

/-- The radial profile `SR0 z = 2z²/(1+z)³` has `z∂_z`-iterates of order `≤ 4` bounded by
`720·z²/(1+z)³`.

The `i`-th iterate is `z²·q_i(z)/(1+z)^(3+i)` with `Σ|coeff q_i| ≤ 720` (the coefficients `q_i`
are exactly `Work.FTS.NonlinRows.AkRhoJetBasic.akNum i`, whose jets are computed there).
Equivalently, with the Hardy weight `w z = (1+z)²/z²`, the product
`DzIter i (2z²/(1+z)³)·w` is the `akRho i` of `AkRhoJetBasic`, bounded by `720/(1+z)` there;
multiplying back by `z²/(1+z)²` gives the claim, with one constant `720` for all `i ≤ 4`. -/
theorem DzBoundR0 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 4 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR0 z|
      ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  refine ⟨720, by norm_num, fun i hi z hz => ?_⟩
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    rw [DzdIter_SR0_zero, abs_zero]
    norm_num
  · have hzm : z ≠ 0 := ne_of_gt hzpos
    have hzn : z ≠ -1 := by intro h; linarith
    have hwpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have hwne : Work.Spaces.w z ≠ 0 := ne_of_gt hwpos
    have hA : Work.Spaces.DzIter i (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z 0
        = akRho i z / Work.Spaces.w z :=
      (eq_div_iff hwne).mpr (akJet_mul_w i hi hzm hzn 0)
    rw [← Work.Elliptic.DzIter_rad SR0 i z 0]
    change |Work.Spaces.DzIter i (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z 0|
        ≤ 720 * z ^ 2 / (1 + z) ^ 3
    rw [hA, abs_div, abs_of_pos hwpos]
    calc |akRho i z| / Work.Spaces.w z
        ≤ (720 / (1 + z)) / Work.Spaces.w z :=
          div_le_div_of_nonneg_right (akRho_abs_le i hi hzpos.le) hwpos.le
      _ = 720 * z ^ 2 / (1 + z) ^ 3 := by
          rw [Work.Spaces.w]
          field_simp

end Work.FTS.StrongEps.ClassCRHS
