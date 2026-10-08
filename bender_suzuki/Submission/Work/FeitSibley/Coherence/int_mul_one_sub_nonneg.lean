import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

theorem int_mul_one_sub_nonneg {B : ℤ} (h : 0 ≤ B * (1 - B)) :
    B = 0 ∨ B = 1 := by
  have hle : B * (1 - B) ≤ 0 := by
    rcases lt_or_ge B 1 with hB | hB
    · have h2 : (0:ℤ) ≤ 1 - B := by omega
      have hB' : B ≤ 0 := by omega
      have := mul_nonpos_of_nonpos_of_nonneg hB' h2
      linarith
    · have h2 : 1 - B ≤ 0 := by omega
      have := mul_nonpos_of_nonneg_of_nonpos (by omega : (0:ℤ) ≤ B) h2
      linarith
  have hzero : B * (1 - B) = 0 := le_antisymm hle h
  rcases mul_eq_zero.mp hzero with h1 | h2
  · exact Or.inl h1
  · right; omega

end Work.FeitSibley.Coherence
