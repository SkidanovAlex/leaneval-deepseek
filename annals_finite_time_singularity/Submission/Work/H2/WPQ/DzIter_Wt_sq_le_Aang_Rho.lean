import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.WPQ.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ

/-- The angular weight `W = w · w_θ` factors as `w · sin(2θ)^{-γ/2}`, so on the open
quadrant the square of `D_z^d g · W` is `(D_z^d g · w)² · sin(2θ)^{-γ}`.  Multiplying the
radial Hardy bound `(D_z^d g · w)² ≤ 100/(γ-1) · Aang` by the nonnegative factor
`sin(2θ)^{-γ}` therefore transfers it to the full weight `W`. -/
theorem DzIter_Wt_sq_le_Aang_Rho {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hhardy : ∀ d ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
        ≤ (100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g d z)
    {d : ℕ} (hd : d ≤ 3) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.DzIter d g z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g d z
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.H2.WPQ.sin_two_pos_of_Ioo hθ
  have hsn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs.le _
  have h2 : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    Work.FTS.H2.WPQ.Wt_sq_of_Ioo α z θ hθ
  have hL : (Work.Spaces.DzIter d g z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [mul_pow, h2, ← mul_assoc, ← mul_pow]
  rw [hL]
  exact mul_le_mul_of_nonneg_right (hhardy d hd z hzpos θ hθ) hsn

end Work.H2.WPQ
