import Mathlib

namespace Work.ORLyndon

theorem addOrderOf_intCast_zmod_mul (D l : ℕ) (hl : 1 ≤ l) (hD : D ≠ 0) :
    addOrderOf ((D : ℤ) : ZMod (l * D)) = l := by
  have h1 : ((D : ℤ) : ZMod (l * D)) = ((D : ℕ) : ZMod (l * D)) := by simp
  rw [h1]
  have hne : l * D ≠ 0 := by positivity
  rw [ZMod.addOrderOf_coe D hne]
  have hdvd : D ∣ l * D := Dvd.intro_left l rfl
  rw [Nat.gcd_eq_right hdvd]
  exact Nat.mul_div_left l (Nat.pos_of_ne_zero hD)

end Work.ORLyndon
