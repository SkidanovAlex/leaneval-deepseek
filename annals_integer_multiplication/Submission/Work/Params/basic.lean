import Mathlib
import Submission.Work.Params.defs

/-! Combinatorial/basic facts used throughout the `Params` area. -/

set_option autoImplicit false

namespace Work.Params

open HvdH

theorem D_sub : D - 1 = 1728 := by decide

theorem Ffac_pos : 0 < Ffac := by unfold Ffac; exact Nat.factorial_pos _

theorem Ffac_ne_zero : Ffac ≠ 0 := Nat.pos_iff_ne_zero.mp Ffac_pos

theorem Ffac_one_le : 1 ≤ Ffac := Nat.one_le_iff_ne_zero.mpr Ffac_ne_zero

theorem Ffac_two_le : 2 ≤ Ffac :=
  Nat.le_of_dvd Ffac_pos (by unfold Ffac; exact Nat.dvd_factorial (by norm_num) (by decide))

theorem Ffac_one_lt : 1 < Ffac := lt_of_lt_of_le one_lt_two Ffac_two_le

theorem Ffac_two_dvd : 2 ∣ Ffac := by
  unfold Ffac; exact Nat.dvd_factorial (by norm_num) (by decide)

/-- `(l.map f).prod ≡ (l.map g).prod` when `f x ≡ g x` pointwise. -/
theorem List.prod_map_modEq {l : List ℕ} {n : ℕ} {f g : ℕ → ℕ}
    (h : ∀ x ∈ l, f x ≡ g x [MOD n]) : (l.map f).prod ≡ (l.map g).prod [MOD n] := by
  induction l with
  | nil => exact Nat.ModEq.refl 1
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.ModEq.mul (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

end Work.Params
