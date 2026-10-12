import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

open Finset

/-- The squared mass of the triangle profile is positive: the sum defining `triMass p`
contains the square `tri p 0² = (p+1)² > 0`. -/
theorem triMass_pos (p : ℕ) : 0 < Work.UBBInputs3.triMass p := by
  unfold Work.UBBInputs3.triMass
  have hmem : (0 : ℤ) ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  have hle : (Work.UBBInputs3.tri p 0) ^ 2
      ≤ ∑ s ∈ Finset.Icc (-(p : ℤ)) (p : ℤ), (Work.UBBInputs3.tri p s) ^ 2 :=
    Finset.single_le_sum (f := fun s => (Work.UBBInputs3.tri p s) ^ 2)
      (fun s _ => sq_nonneg _) hmem
  have htri : Work.UBBInputs3.tri p 0 = (p : ℝ) + 1 := by
    unfold Work.UBBInputs3.tri
    rw [Int.cast_zero, abs_zero, sub_zero, max_eq_right (by positivity)]
  rw [htri] at hle
  have : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
  linarith

theorem prof_norm (p : ℕ) :
    ∑ s ∈ Finset.Icc (-(p : ℤ)) (p : ℤ), (Work.UBBInputs3.prof p s) ^ 2 = 1 := by
  have hpos : 0 < Work.UBBInputs3.triMass p := triMass_pos p
  have hterm : ∀ s : ℤ, (Work.UBBInputs3.prof p s) ^ 2
      = (Work.UBBInputs3.tri p s) ^ 2 / Work.UBBInputs3.triMass p := by
    intro s
    simp only [Work.UBBInputs3.prof]
    rw [div_pow, Real.sq_sqrt (le_of_lt hpos)]
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

end Work.UBBInputs3.MatLoc
