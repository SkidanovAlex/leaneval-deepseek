import Mathlib

namespace Work.LinnikAreas.Density4

theorem natDiv_cast_mul_le (N m : ℕ) (c : ℝ) :
    c * ((N / m : ℕ) : ℝ) ≤ c * ((N : ℝ) / (m : ℝ)) + |c| := by
  rcases eq_or_ne m 0 with hm | hm
  · subst hm; simp
  · -- decompose `N = m * (N / m) + N % m`
    set q : ℕ := N / m with hq
    set r : ℕ := N % m with hr
    have hNc : (N : ℝ) = (m : ℝ) * (q : ℝ) + (r : ℝ) := by
      have h := Nat.div_add_mod N m
      rw [← hq, ← hr] at h
      rw [← h]
      push_cast
      ring
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    have hrlt : (r : ℝ) < (m : ℝ) := by
      rw [hr]; exact_mod_cast Nat.mod_lt N (Nat.pos_of_ne_zero hm)
    have hrm_nn : 0 ≤ (r : ℝ) / (m : ℝ) :=
      div_nonneg (Nat.cast_nonneg r) (le_of_lt hmpos)
    have hrm_lt : (r : ℝ) / (m : ℝ) < 1 := (div_lt_one hmpos).mpr hrlt
    have hy : (N : ℝ) / (m : ℝ) = (q : ℝ) + (r : ℝ) / (m : ℝ) := by
      rw [hNc, add_div, mul_div_cancel_left₀ _ hmne]
    -- the floor error is at most one
    have hb : |(q : ℝ) - (N : ℝ) / (m : ℝ)| ≤ 1 := by
      rw [hy, show (q : ℝ) - ((q : ℝ) + (r : ℝ) / (m : ℝ)) = -((r : ℝ) / (m : ℝ)) by ring,
        abs_neg, abs_of_nonneg hrm_nn]
      exact le_of_lt hrm_lt
    have key : c * ((q : ℝ) - (N : ℝ) / (m : ℝ)) ≤ |c| := by
      calc c * ((q : ℝ) - (N : ℝ) / (m : ℝ))
          ≤ |c * ((q : ℝ) - (N : ℝ) / (m : ℝ))| := le_abs_self _
        _ = |c| * |(q : ℝ) - (N : ℝ) / (m : ℝ)| := abs_mul _ _
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg c)
        _ = |c| := by ring
    linarith [key]

end Work.LinnikAreas.Density4
