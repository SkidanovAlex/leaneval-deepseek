import Mathlib
import Submission.Work.WilC5.ExpLog

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

/-! ## The definable order on `ℝ` -/

/-- The definable order `leE x y := ∃ z, z * z = y - x` on `ℝ` is the usual order. -/
theorem leE_real (a b : ℝ) : leE a b ↔ a ≤ b := by
  rw [leE, subE_real, isSquare_real, sub_nonneg]

/-! ## The graph of the definable logarithm on `ℝ` -/

/-- **The relation `logDefSet` on `ℝ` is the graph of the vdDMM logarithm**: `logDefSet x y` holds
exactly when `x > 0` and `y = log x`, or `x ≤ 0` and `y = 0`. -/
theorem logDefSet_real (x y : ℝ) :
    logDefSet x y ↔ (0 < x ∧ y = Real.log x) ∨ (x ≤ 0 ∧ y = 0) := by
  have h1 : (leE zeroE x ∧ ¬ leE x zeroE) ↔ 0 < x := by
    rw [leE_real, leE_real, zeroE_real]
    exact ⟨fun h => not_le.mp h.2, fun h => ⟨le_of_lt h, not_le.mpr h⟩⟩
  rw [logDefSet, h1, expE_real, oneE_real]
  constructor
  · rintro (⟨hx, hex⟩ | ⟨hx, hex⟩)
    · exact Or.inl ⟨hx, by rw [← Real.log_exp y, hex]⟩
    · exact Or.inr ⟨not_lt.mp hx, by rw [← Real.log_exp y, hex, Real.log_one]⟩
  · rintro (⟨hx, rfl⟩ | ⟨hx, rfl⟩)
    · exact Or.inl ⟨hx, Real.exp_log hx⟩
    · exact Or.inr ⟨not_lt.mpr hx, Real.exp_zero⟩

theorem LogFunReal (x : ℝ) :
    Work.WilC5.logFun x = (if 0 < x then Real.log x else 0) := by
  by_cases hx : 0 < x
  · -- `x > 0`: the unique solution of `logDefSet x ·` is `Real.log x`.
    have hex : ∃ y, logDefSet x y :=
      ⟨Real.log x, by rw [logDefSet_real]; exact Or.inl ⟨hx, rfl⟩⟩
    rw [logFun, dite_eq_left hex, ite_eq_left hx]
    have hspec := Classical.choose_spec hex
    rw [logDefSet_real] at hspec
    rcases hspec with ⟨_, hy⟩ | ⟨hle, hy⟩
    · exact hy
    · exact absurd hx (not_lt.mpr hle)
  · -- `x ≤ 0`: the unique solution of `logDefSet x ·` is `0`.
    have hx' : x ≤ 0 := not_lt.mp hx
    have hex : ∃ y, logDefSet x y :=
      ⟨0, by rw [logDefSet_real]; exact Or.inr ⟨hx', rfl⟩⟩
    rw [logFun, dite_eq_left hex, ite_eq_right hx]
    have hspec := Classical.choose_spec hex
    rw [logDefSet_real] at hspec
    rcases hspec with ⟨hp, hy⟩ | ⟨_, hy⟩
    · exact absurd hp hx
    · exact hy

end Work.WilC5
