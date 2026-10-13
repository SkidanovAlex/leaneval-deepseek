import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

theorem profileZeroFar_locData (α L β : ℝ) (hL : 1 ≤ L) {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ, 7 / 4 ≤ z → h z θ = 0) :
    ProfileZeroFar (max (2 * L) (7 / 4)) (locData α L β h) := by
  intro z θ hz
  have hz2L : 2 * L ≤ z := le_trans (le_max_left _ _) hz
  have hz74 : 7 / 4 ≤ z := le_trans (le_max_right _ _) hz
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdiv : 2 ≤ z / L := by
    rw [le_div_iff₀ hLpos]
    linarith
  have hchi : Work.Stability.chi (z / L) = 0 :=
    Work.Stability.chi_eq_zero (by rw [abs_of_nonneg (by linarith)]; exact hdiv)
  rw [locData_apply, hchi, hh z θ hz74]
  ring

end Work.FTS.LocData
