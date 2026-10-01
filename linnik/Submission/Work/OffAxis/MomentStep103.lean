import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.tf72f_moment
import Submission.Work.ZeroFreeTables.tf72f_gap_mono
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc
import Submission.Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
import Submission.Work.OffAxis.MomentStep103GapQuant

namespace Work.OffAxis

open scoped Interval
open MeasureTheory

/-- **Moment step at the test function `tf72f (6/7)`.**

The hypothesis bounds the `F`-method gap
`Gap l = F(-6/7) - F(-l) - 2 (F 0 - F(6/7 - l))` by the slack `s`.  The quantitative
lower bound `MomentStep103GapQuant` (constant `104/66825 > 1/5000`) turns this into

  `(104/66825) * (6/7 - l) ≤ Gap l ≤ s ≤ ε/10000`,

hence `6/7 - l ≤ (66825/104) * (ε/10000) < ε/2`, i.e. `6/7 - ε/2 ≤ l`.  The first
disjunct `l ≤ 792/1000` is therefore immaterial: the second one always holds. -/
theorem MomentStep103 (ε s : ℝ) (hε : 0 < ε) (hs : 0 ≤ s) (hsε : s ≤ ε/10000) :
    ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ)*t) * Work.ZeroFreeTables.tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (l*t) * Work.ZeroFreeTables.tf72f (6/7) t)
      ≤ 2 * ((∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7-l)*t)) * Work.ZeroFreeTables.tf72f (6/7) t))
        + s →
      l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
  intro l hl0 hl67 h
  right
  -- quantitative gap lower bound
  have hq := MomentStep103GapQuant l hl0 (le_of_lt hl67)
  -- rewrite both gap endpoints as the single integrals of the hypothesis
  have h67 := Work.ZeroFreeTables.tf72fL_eq_Phi (6/7)
  have hl := Work.ZeroFreeTables.tf72fL_eq_Phi l
  have hz : (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - 6/7) * t)) * Work.ZeroFreeTables.tf72f (6/7) t)
      = ∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t := by
    apply intervalIntegral.integral_congr
    intro t _
    norm_num
  -- the hypothesis is exactly `Gap l ≤ s`
  have hgap : Work.ZeroFreeTables.tf72fPhi (6/7) - Work.ZeroFreeTables.tf72fPhi l ≤ s := by
    rw [← h67, ← hl, hz]
    linarith
  have hcs : (104/66825 : ℝ) * (6/7 - l) ≤ s := le_trans hq hgap
  have hεs : (104/66825 : ℝ) * (6/7 - l) ≤ ε/10000 := le_trans hcs hsε
  have h2 : (6/7 - l) ≤ (66825/104 : ℝ) * (ε/10000) := by
    have hpos : (0:ℝ) ≤ 66825/104 := by norm_num
    have hh := mul_le_mul_of_nonneg_left hεs hpos
    have hsimp : (66825/104 : ℝ) * ((104/66825) * (6/7 - l)) = 6/7 - l := by ring
    rwa [hsimp] at hh
  have h3 : (66825/104 : ℝ) * (ε/10000) ≤ ε/2 := by nlinarith [hε]
  linarith

end Work.OffAxis
