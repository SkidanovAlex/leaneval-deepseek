import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.L6FBound

/-- The angular factor is bounded by `2` for `0 < α ≤ 1` and `θ ∈ (0, π/2)`. -/
theorem angFac_le_two {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg' hθI
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hA : α + Real.sin (2 * θ) ≤ 2 := by linarith
  have hr : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
    Real.rpow_le_one hs0 hs1 (by linarith)
  have h := mul_le_mul hA hr (Real.rpow_nonneg hs0 _) (by norm_num : (0 : ℝ) ≤ 2)
  simpa using h

theorem mixed_le_WlInf6_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {P : ℝ → ℝ → ℝ} (hPsm : Work.FTS.EllipticEst.SmoothOpen P)
    (hPm : Work.Spaces.WlInfMem α 6 P) {i j : ℕ} (hij : i + j ≤ 6) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Work.Spaces.mixed j i P z θ| ≤ 2000 * Work.Spaces.WlInf α 6 P := by
  have hW : 0 ≤ Work.Spaces.WlInf α 6 P := Work.Spaces.WlInf_nonneg α 6 P hPm
  rcases eq_or_ne i 0 with hi | hi
  · -- pure radial slot `i = 0`: the level-six `D_z`-bound
    rw [hi, Work.Spaces.mixed_zero_right]
    have h := Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6 (α := α) hPsm hPm
      (b := j) (by omega) hz hθ
    linarith
  · -- genuinely mixed slot `1 ≤ i`: the level-six `Mixed_le_WlInf`-bound
    have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
    have h := mixed_le_WlInf6 (α := α) hα hPsm hPm hi1 (by omega) hz hθ
    refine le_trans h ?_
    calc 1000 * (Work.Spaces.WlInf α 6 P
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        ≤ 1000 * (Work.Spaces.WlInf α 6 P * 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (angFac_le_two hα hα1 hθ) hW) (by norm_num)
      _ = 2000 * Work.Spaces.WlInf α 6 P := by ring

end Work.FTS.StrongPersist.N6Trans.L6FBound
