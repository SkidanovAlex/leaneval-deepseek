import Mathlib
import Submission.Work.OROneRel.rightPowDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- Pointwise computation underlying `rightPow_neg_comp_rightPow`. -/
theorem rightPow_neg_apply_rightPow_of (t : α) (q : α → ℤ) (hq : q t = 0) (y : α) :
    rightPow t (-q) (rightPow t q (FreeGroup.of y)) = FreeGroup.of y := by
  classical
  rw [rightPow_of, map_mul, map_zpow]
  rw [rightPow_of, rightPow_of]
  show FreeGroup.of y * FreeGroup.of t ^ (-(-q) y) *
      (FreeGroup.of t * FreeGroup.of t ^ (-(-q) t)) ^ (-q y) = FreeGroup.of y
  rw [show (-(-q) t : ℤ) = 0 from by simp [hq]]
  rw [zpow_zero, mul_one]
  rw [show (-(-q) y : ℤ) = q y from by simp]
  rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

/-- Pointwise computation underlying `rightPow_comp_rightPow_neg`. -/
theorem rightPow_apply_rightPow_neg_of (t : α) (q : α → ℤ) (hq : q t = 0) (y : α) :
    rightPow t q (rightPow t (-q) (FreeGroup.of y)) = FreeGroup.of y := by
  classical
  rw [rightPow_of, map_mul, map_zpow]
  rw [rightPow_of, rightPow_of]
  show FreeGroup.of y * FreeGroup.of t ^ (-q y) *
      (FreeGroup.of t * FreeGroup.of t ^ (-q t)) ^ (-(-q) y) = FreeGroup.of y
  rw [hq, neg_zero, zpow_zero, mul_one]
  rw [show (-(-q) y : ℤ) = q y from by simp]
  rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

/-- `rightPow t (-q)` composed with `rightPow t q` is the identity when `q t = 0`. -/
theorem rightPow_neg_comp_rightPow (t : α) (q : α → ℤ) (hq : q t = 0) :
    (rightPow t (-q)).comp (rightPow t q) = MonoidHom.id (FreeGroup α) :=
  FreeGroup.ext_hom _ _ fun y => rightPow_neg_apply_rightPow_of t q hq y

/-- `rightPow t q` composed with `rightPow t (-q)` is the identity when `q t = 0`. -/
theorem rightPow_comp_rightPow_neg (t : α) (q : α → ℤ) (hq : q t = 0) :
    (rightPow t q).comp (rightPow t (-q)) = MonoidHom.id (FreeGroup α) :=
  FreeGroup.ext_hom _ _ fun y => rightPow_apply_rightPow_neg_of t q hq y

theorem rightPow_mulEquiv {α : Type u} (t : α) (q : α → ℤ) (hq : q t = 0) :
    ∃ e : FreeGroup α ≃* FreeGroup α, (e : FreeGroup α → FreeGroup α) = Work.OROneRel.rightPow t q := by
  classical
  have h1 : Function.LeftInverse (rightPow t (-q)) (rightPow t q) := fun u => by
    rw [← MonoidHom.comp_apply, rightPow_neg_comp_rightPow t q hq]
    rfl
  have h2 : Function.LeftInverse (rightPow t q) (rightPow t (-q)) := fun u => by
    rw [← MonoidHom.comp_apply, rightPow_comp_rightPow_neg t q hq]
    rfl
  exact ⟨MulEquiv.ofBijective (rightPow t q) ⟨h1.injective, h2.surjective⟩, rfl⟩

end Work.OROneRel
