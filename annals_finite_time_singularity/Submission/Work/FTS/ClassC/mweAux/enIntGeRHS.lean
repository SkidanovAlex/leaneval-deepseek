import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.ClassC.ModeEnergyWeighted
import Submission.Work.FTS.ClassC.ModeEnergyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.mweAux

theorem enIntGeRHS {α lam : ℝ} (hα : 0 < α) {a c : ℝ → ℝ} :
    ∀ z ∈ Set.Ioi (0:ℝ),
      α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        - c z * a z * (Work.Spaces.w z) ^ 2
      ≤ Work.FTS.ClassC.enInt α lam a c z := by
  intro z hz
  have hz0 : 0 < z := hz
  have hA : (0:ℝ) ≤ (a z) ^ 2 := sq_nonneg _
  have hW : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hαpos : (0:ℝ) ≤ α := le_of_lt hα
  have hα5 : (0:ℝ) ≤ α * (5 + α) := mul_nonneg hαpos (by linarith)
  have hα2 : (0:ℝ) ≤ α ^ 2 := sq_nonneg α
  -- the two `w²`-derivative bounds of `ModeEnergyDefs`
  have hbb : rwbb z ≤ 6 * (Work.Spaces.w z) ^ 2 :=
    le_trans (le_abs_self _) (abs_rwbb_le hz0)
  have hcc : -rwc z ≤ 3 * (Work.Spaces.w z) ^ 2 := by
    have h1 := abs_rwc_le hz0
    have h2 := neg_le_abs (rwc z)
    linarith
  -- multiply the two bounds by the nonnegative prefactors
  have hB : (α ^ 2 / 2) * rwbb z * (a z) ^ 2
      ≤ (α ^ 2 / 2) * (6 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 := by
    have h : rwbb z * (a z) ^ 2 ≤ (6 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 :=
      mul_le_mul_of_nonneg_right hbb hA
    have hα2' : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
    calc (α ^ 2 / 2) * rwbb z * (a z) ^ 2
        = (α ^ 2 / 2) * (rwbb z * (a z) ^ 2) := by ring
      _ ≤ (α ^ 2 / 2) * ((6 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2) :=
          mul_le_mul_of_nonneg_left h hα2'
      _ = (α ^ 2 / 2) * (6 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 := by ring
  have hC : -((α * (5 + α)) / 2) * rwc z * (a z) ^ 2
      ≤ ((α * (5 + α)) / 2) * (3 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 := by
    have h : (-rwc z) * (a z) ^ 2 ≤ (3 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 :=
      mul_le_mul_of_nonneg_right hcc hA
    have h5' : (0:ℝ) ≤ (α * (5 + α)) / 2 := by linarith
    calc -((α * (5 + α)) / 2) * rwc z * (a z) ^ 2
        = ((α * (5 + α)) / 2) * ((-rwc z) * (a z) ^ 2) := by ring
      _ ≤ ((α * (5 + α)) / 2) * ((3 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2) :=
          mul_le_mul_of_nonneg_left h h5'
      _ = ((α * (5 + α)) / 2) * (3 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 := by ring
  -- `rw z = (z w z)²` identifies the first term with `α² rw z (∂_z a)²`
  have hkey : α ^ 2 * rw z * (deriv a z) ^ 2
      = α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [rw_eq_w]; ring
  rw [enInt, ← hkey]
  nlinarith [hB, hC, hA, hW, hα5, hα2]

end Work.FTS.ClassC.mweAux
