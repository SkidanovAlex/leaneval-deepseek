import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.IntervalCases

namespace Commons.NumberTheory.GaussianInt

/-- The only integer solutions of `a ^ 2 + b ^ 2 = 1` are `(±1, 0)` and `(0, ±1)`. -/
lemma int_sq_add_sq_eq_one {a b : ℤ} (h : a ^ 2 + b ^ 2 = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have ha1 : -1 ≤ a := ((abs_le.mp ((sq_le_one_iff_abs_le_one a).mp ha))).1
  have ha2 : a ≤ 1 := ((abs_le.mp ((sq_le_one_iff_abs_le_one a).mp ha))).2
  have hb1 : -1 ≤ b := ((abs_le.mp ((sq_le_one_iff_abs_le_one b).mp hb))).1
  have hb2 : b ≤ 1 := ((abs_le.mp ((sq_le_one_iff_abs_le_one b).mp hb))).2
  interval_cases a <;> interval_cases b <;> simp_all

/-- The units of `ℤ[i]` are exactly `±1, ±i`. -/
theorem units_classification (z : GaussianInt) :
    IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = (⟨0, 1⟩ : GaussianInt) ∨ z = (⟨0, -1⟩ : GaussianInt) := by
  constructor
  · intro hz
    rw [← Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) z] at hz
    have hz' : z.re ^ 2 + z.im ^ 2 = 1 := by
      rw [Zsqrtd.norm_def] at hz
      nlinarith [hz]
    rcases int_sq_add_sq_eq_one hz' with ⟨hr, hi⟩ | ⟨hr, hi⟩ | ⟨hr, hi⟩ | ⟨hr, hi⟩
    · left; ext <;> simp_all
    · right; left; ext <;> simp_all
    · right; right; left; ext <;> simp_all
    · right; right; right; ext <;> simp_all
  · rintro (rfl | rfl | rfl | rfl)
    · exact isUnit_one
    · exact IsUnit.neg isUnit_one
    · exact (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) _).mp (by decide)
    · exact (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) _).mp (by decide)

end Commons.NumberTheory.GaussianInt