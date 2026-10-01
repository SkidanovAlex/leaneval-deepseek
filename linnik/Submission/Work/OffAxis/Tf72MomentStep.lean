import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc
import Submission.Work.ZeroFreeTables.tf72f_moment
import Submission.Work.ZeroFreeTables.tf72f_gap_mono
import Submission.Work.OffAxis.Tf72PhiGapQuant

open scoped Interval
open MeasureTheory

namespace Work.OffAxis

noncomputable section

/-- The two integrals appearing in the hypothesis, written through `tf72fPhi`. -/
private lemma phi_at_two_thirds :
    Work.ZeroFreeTables.tf72fPhi ((6:ℝ)/7)
      = (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ)*t) * Work.ZeroFreeTables.tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t) := by
  have h := Work.ZeroFreeTables.tf72fL_eq_Phi ((6:ℝ)/7)
  have hR' : (∫ t in (0:ℝ)..(7/3),
      Real.exp (-((6/7 - (6:ℝ)/7) * t)) * Work.ZeroFreeTables.tf72f (6/7) t)
      = ∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t := by
    apply intervalIntegral.integral_congr
    intro t _
    simp
  rw [hR'] at h
  exact h.symm

private lemma phi_at_l (l : ℝ) :
    Work.ZeroFreeTables.tf72fPhi l
      = (∫ t in (0:ℝ)..(7/3), Real.exp (l*t) * Work.ZeroFreeTables.tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3),
            Real.exp (-((6/7-l)*t)) * Work.ZeroFreeTables.tf72f (6/7) t) :=
  (Work.ZeroFreeTables.tf72fL_eq_Phi l).symm

theorem Tf72MomentStep (ε s : ℝ) (hε : 0 < ε) (hs : 0 ≤ s) (hsε : s ≤ ε/10000) :
    ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ)*t) * Work.ZeroFreeTables.tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (l*t) * Work.ZeroFreeTables.tf72f (6/7) t)
      ≤ 2 * ((∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7-l)*t)) * Work.ZeroFreeTables.tf72f (6/7) t))
        + s →
      l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
  intro l hl0 hl7 hhyp
  -- rewrite the hypothesis in terms of the gap functional `tf72fPhi`
  have hkey : Work.ZeroFreeTables.tf72fPhi (6/7) - Work.ZeroFreeTables.tf72fPhi l ≤ s := by
    rw [phi_at_two_thirds, phi_at_l]
    linarith [hhyp]
  -- contrapositive: if both disjuncts fail then `6/7 - l > ε/2`
  by_contra hcon
  push Not at hcon
  have hlt : l < 6/7 - ε/2 := hcon.2
  have hquant := Tf72PhiGapQuant l hl0 (le_of_lt hl7)
  have hA : (104/66825 : ℝ) * (6/7 - l) ≤ ε/10000 := le_trans hquant (le_trans hkey hsε)
  have hB : (104/66825 : ℝ) * (ε/2) < (104/66825 : ℝ) * (6/7 - l) :=
    mul_lt_mul_of_pos_left (by linarith [hlt]) (by norm_num)
  have hC : (104/66825 : ℝ) * (ε/2) < ε/10000 := lt_of_lt_of_le hB hA
  have hd : (0:ℝ) < 104/66825/2 - 1/10000 := by norm_num
  nlinarith [hC, hε, hd]

end

end Work.OffAxis
