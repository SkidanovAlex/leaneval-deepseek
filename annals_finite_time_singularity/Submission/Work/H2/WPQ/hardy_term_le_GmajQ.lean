import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.WPQ.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ

open scoped Real

/-- Each individual angular-Hardy term `(γ-1)⁻¹ Aang α g d z · (θ-factor)` with `d ≤ 3` is
dominated by the corresponding term of `GmajQ` (which sums `Aang α g d z` over `d < 4`), the
remaining `HkIntegrand` summand being nonnegative. -/
theorem hardy_term_le_GmajQ {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) {d : ℕ} (hd : d ≤ 3) :
    (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z
      * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
      ≤ Work.FTS.H2.WPQ.GmajQ α g z θ := by
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hidx : d ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hsum : Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ e ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g e z :=
    Finset.single_le_sum (fun i _ => Work.FTS.H2.WPQ.Aang_nonneg α g i z) hidx
  have hθf : 0 ≤ (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
    Work.FTS.H2.WPQ.theta_factor_nonneg hθ
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hkey : 0 ≤ (Work.Spaces.gam α - 1)⁻¹
      * ((∑ e ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g e z)
          - Work.FTS.H2.WPQ.Aang α g d z)
      * ((α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
    mul_nonneg (mul_nonneg hinv (sub_nonneg.mpr hsum)) hθf
  simp only [Work.FTS.H2.WPQ.GmajQ]
  nlinarith [hkey, hHk]

end Work.H2.WPQ
