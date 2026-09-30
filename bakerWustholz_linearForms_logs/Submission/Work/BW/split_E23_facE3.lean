import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The purely arithmetic (natural number) core inequality.  For `r ≥ 2`:
`(r+1)! (r-1)! 2^(6r+5) (2r) ≤ 2^(8r+7) r^(2r+1)`. -/
private lemma nat_core (r : ℕ) (hr : 2 ≤ r) :
    (r+1).factorial * (r-1).factorial * 2^(6*r+5) * (2*r)
      ≤ 2^(8*r+7) * r^(2*r+1) := by
  have h1 : (r+1).factorial ≤ (2*r)^(r+1) := by
    calc (r+1).factorial ≤ (r+1)^(r+1) := Nat.factorial_le_pow (r+1)
      _ ≤ (2*r)^(r+1) := Nat.pow_le_pow_left (by omega) (r+1)
  have h2 : (r-1).factorial ≤ r^(r-1) := by
    calc (r-1).factorial ≤ (r-1)^(r-1) := Nat.factorial_le_pow (r-1)
      _ ≤ r^(r-1) := Nat.pow_le_pow_left (by omega) (r-1)
  have h2a : (2:ℕ)^(r+1) * 2^(6*r+5) * 2 = 2^(7*r+7) := by
    calc (2:ℕ)^(r+1) * 2^(6*r+5) * 2
        = 2^((r+1)+(6*r+5)) * 2 := by rw [← pow_add]
      _ = 2^(((r+1)+(6*r+5))+1) := by rw [← pow_succ]
      _ = 2^(7*r+7) := by congr 1; omega
  have h3a : r^(r+1) * r^(r-1) * r = r^(2*r+1) := by
    calc r^(r+1) * r^(r-1) * r
        = r^((r+1)+(r-1)) * r := by rw [← pow_add]
      _ = r^(((r+1)+(r-1))+1) := by rw [← pow_succ]
      _ = r^(2*r+1) := by congr 1; omega
  calc (r+1).factorial * (r-1).factorial * 2^(6*r+5) * (2*r)
      = ((r+1).factorial * (r-1).factorial) * (2^(6*r+5) * (2*r)) := by ring
    _ ≤ ((2*r)^(r+1) * r^(r-1)) * (2^(6*r+5) * (2*r)) := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul h1 h2
    _ = (2^(r+1) * r^(r+1) * r^(r-1)) * (2^(6*r+5) * (2*r)) := by rw [mul_pow]
    _ = (2^(r+1) * 2^(6*r+5) * 2) * (r^(r+1) * r^(r-1) * r) := by ring
    _ = 2^(7*r+7) * r^(2*r+1) := by rw [h2a, h3a]
    _ ≤ 2^(8*r+7) * r^(2*r+1) := by
          apply Nat.mul_le_mul_right
          exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem split_E23_facE3 (r d : ℕ) (hr : 2 ≤ r) :
    ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5) * (2*(r:ℝ)*d)
      ≤ (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ) := by
  have hreal : ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5) * (2*(r:ℝ))
      ≤ (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) := by
    exact_mod_cast nat_core r hr
  calc ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5) * (2*(r:ℝ)*d)
      = (((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5) * (2*(r:ℝ))) * d := by ring
    _ ≤ ((2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1)) * d :=
          mul_le_mul_of_nonneg_right hreal (Nat.cast_nonneg d)
    _ = (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ) := by ring

end Work.BW
