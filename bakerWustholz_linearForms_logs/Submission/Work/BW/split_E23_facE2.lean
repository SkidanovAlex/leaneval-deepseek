import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem split_E23_facE2 (r : ℕ) (hr : 2 ≤ r) :
    ((r+1).factorial : ℝ) * (r.factorial : ℝ) * (r:ℝ) * (2:ℝ)^(6*r+6)
      ≤ (2:ℝ)^(7*r+7) * (r:ℝ)^(2*r+2) := by
  have h1 : ((r+1).factorial : ℝ) ≤ (2:ℝ)^(r+1) * (r:ℝ)^(r+1) := by
    have hc : ((r+1).factorial : ℝ) ≤ ((r+1:ℕ):ℝ)^(r+1) := by
      exact_mod_cast Nat.factorial_le_pow (r+1)
    have h2 : ((r+1:ℕ):ℝ) ≤ 2*(r:ℝ) := by
      have : ((r+1:ℕ):ℝ) = (r:ℝ)+1 := by push_cast; ring
      linarith [show (1:ℝ) ≤ (r:ℝ) by exact_mod_cast (by omega : 1 ≤ r)]
    calc ((r+1).factorial : ℝ) ≤ ((r+1:ℕ):ℝ)^(r+1) := hc
      _ ≤ (2*(r:ℝ))^(r+1) := pow_le_pow_left₀ (by positivity) h2 _
      _ = (2:ℝ)^(r+1) * (r:ℝ)^(r+1) := by rw [mul_pow]
  have h2 : (r.factorial : ℝ) * (r:ℝ) ≤ (r:ℝ)^(r+1) := by
    have hc : (r.factorial : ℝ) ≤ (r:ℝ)^r := by exact_mod_cast Nat.factorial_le_pow r
    calc (r.factorial : ℝ) * (r:ℝ) ≤ (r:ℝ)^r * (r:ℝ) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (r:ℝ)^(r+1) := by rw [pow_succ]
  have h3 : ((r+1).factorial : ℝ) * ((r.factorial : ℝ) * (r:ℝ)) * (2:ℝ)^(6*r+6)
      ≤ ((2:ℝ)^(r+1) * (r:ℝ)^(r+1)) * (r:ℝ)^(r+1) * (2:ℝ)^(6*r+6) := by
    apply mul_le_mul
    · exact mul_le_mul h1 h2 (by positivity) (by positivity)
    · exact le_refl _
    · positivity
    · positivity
  rw [show ((r+1).factorial : ℝ) * (r.factorial : ℝ) * (r:ℝ) * (2:ℝ)^(6*r+6)
      = ((r+1).factorial : ℝ) * ((r.factorial : ℝ) * (r:ℝ)) * (2:ℝ)^(6*r+6) by ring]
  refine le_trans h3 (le_of_eq ?_)
  calc ((2:ℝ)^(r+1) * (r:ℝ)^(r+1)) * (r:ℝ)^(r+1) * (2:ℝ)^(6*r+6)
      = ((2:ℝ)^(r+1) * (2:ℝ)^(6*r+6)) * ((r:ℝ)^(r+1) * (r:ℝ)^(r+1)) := by ring
    _ = (2:ℝ)^(7*r+7) * (r:ℝ)^(2*r+2) := by
        rw [show (2:ℝ)^(r+1) * (2:ℝ)^(6*r+6) = (2:ℝ)^(7*r+7) by
              rw [← pow_add, show r+1+(6*r+6) = 7*r+7 by ring],
            show (r:ℝ)^(r+1) * (r:ℝ)^(r+1) = (r:ℝ)^(2*r+2) by
              rw [← pow_add, show r+1+(r+1) = 2*r+2 by ring]]

end Work.BW
