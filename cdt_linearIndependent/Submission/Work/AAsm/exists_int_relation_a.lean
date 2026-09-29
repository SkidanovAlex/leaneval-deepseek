import Mathlib

namespace Work.AAsm

/-- For `L = a + b*Z` with `a b : ℚ`, the three numbers `1`, `L/2`, `Z/4` satisfy a
nontrivial integer linear relation in which the coefficient of `L/2` is nonzero.
Explicit witnesses are `B = 2 * a.den * b.den`, `A = -b.den * a.num`, `C = -4 * a.den * b.num`,
for which `A + B*(L/2) + C*(Z/4) = 0` holds identically. -/
theorem exists_int_relation_a {L Z : ℝ} (a b : ℚ) (h : L = (a : ℝ) + (b : ℝ) * Z) :
    ∃ A B C : ℤ, B ≠ 0 ∧ (A : ℝ) + (B : ℝ) * (L / 2) + (C : ℝ) * (Z / 4) = 0 := by
  refine ⟨-((b.den : ℤ) * a.num), 2 * (a.den : ℤ) * (b.den : ℤ),
          -(4 * (a.den : ℤ) * b.num), ?_, ?_⟩
  · have ha : (0 : ℤ) < (a.den : ℤ) := by exact_mod_cast a.den_pos
    have hb : (0 : ℤ) < (b.den : ℤ) := by exact_mod_cast b.den_pos
    have : (0 : ℤ) < 2 * (a.den : ℤ) * (b.den : ℤ) := by nlinarith
    exact ne_of_gt this
  · have ha_cast : (a : ℝ) = (a.num : ℝ) / (a.den : ℝ) := Rat.cast_def a
    have hb_cast : (b : ℝ) = (b.num : ℝ) / (b.den : ℝ) := Rat.cast_def b
    rw [h, ha_cast, hb_cast]
    have hq1 : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_nz
    have hq2 : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_nz
    push_cast
    field_simp
    ring

end Work.AAsm
