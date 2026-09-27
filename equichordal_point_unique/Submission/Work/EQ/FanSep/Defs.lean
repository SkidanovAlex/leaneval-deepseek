import Mathlib
import Submission.Work.EQ.DefsCore

/-!
# Shared helpers for the uniform fan separation (`Work.EQ.fan_sep`)

The stable fan `fan a h ε` is built from the germ `germC a h` by the inverse branches
`invBranch a s`.  On the real axis the inverse branch acts as `x ↦ -x ± 1`; the two sign
conventions used throughout the estimate are recorded here.
-/

namespace Work.EQ

open Complex

noncomputable section

/-- The sign of a branch label as a real number: `true ↦ 1`, `false ↦ -1`. -/
def sgnB (s : Bool) : ℝ := if s then 1 else -1

/-- The sign of a nonzero real number as a real number (`sgnR 0 = -1` by convention, so it is
only used for nonzero arguments). -/
def sgnR (x : ℝ) : ℝ := if 0 < x then 1 else -1

/-- Action of the inverse branch on the real axis (the "axis walk"): `x ↦ -x ± 1`. -/
def axStep (a : ℝ) (s : Bool) (x : ℝ) : ℝ := -x + sgnB s * sgnR (x + a / 2)

@[simp] lemma sgnB_true : sgnB true = 1 := rfl
@[simp] lemma sgnB_false : sgnB false = -1 := rfl
lemma sgnB_sq (s : Bool) : sgnB s * sgnB s = 1 := by cases s <;> simp [sgnB]
lemma sgnB_cases (s : Bool) : sgnB s = 1 ∨ sgnB s = -1 := by cases s <;> simp [sgnB]
lemma abs_sgnB (s : Bool) : |sgnB s| = 1 := by cases s <;> simp [sgnB]

lemma sgnR_eq_one {x : ℝ} (h : 0 < x) : sgnR x = 1 := by rw [sgnR, if_pos h]
lemma sgnR_eq_neg_one {x : ℝ} (h : x < 0) : sgnR x = -1 := by
  rw [sgnR, if_neg (not_lt.mpr h.le)]
lemma sgnR_sq (x : ℝ) : sgnR x * sgnR x = 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sgnR_eq_neg_one h]; ring
  · rw [h, sgnR, if_neg (lt_irrefl 0)]; ring
  · rw [sgnR_eq_one h]; ring
lemma sgnR_cases (x : ℝ) : sgnR x = 1 ∨ sgnR x = -1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · exact Or.inr (sgnR_eq_neg_one h)
  · subst h
    exact Or.inr (by rw [sgnR, if_neg (lt_irrefl 0)])
  · exact Or.inl (sgnR_eq_one h)
lemma abs_sgnR (x : ℝ) : |sgnR x| = 1 := by
  rcases sgnR_cases x with h | h <;> rw [h] <;> norm_num
lemma sgnR_ne_zero (x : ℝ) : sgnR x ≠ 0 := by
  rcases sgnR_cases x with h | h <;> rw [h] <;> norm_num

theorem sgnR_mul_self {x : ℝ} (hx : x ≠ 0) : sgnR x * x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sgnR_eq_neg_one h, abs_of_neg h]; ring
  · exact absurd h hx
  · rw [sgnR_eq_one h, abs_of_pos h]; ring

theorem div_abs_self {x : ℝ} (hx : x ≠ 0) : x / |x| = sgnR x := by
  rw [div_eq_iff (abs_ne_zero.mpr hx)]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sgnR_eq_neg_one h, abs_of_neg h]; ring
  · exact absurd h hx
  · rw [sgnR_eq_one h, abs_of_pos h]; ring

end

end Work.EQ
