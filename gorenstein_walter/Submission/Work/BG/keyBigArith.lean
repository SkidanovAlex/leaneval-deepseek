import Mathlib

namespace Work.BG

theorem keyBigArith (N k : ℕ) (x : ℤ) (hx0 : x ≠ 0) (hx1 : x ≠ -1)
    (h : (N : ℂ) * (1 + 1 / ((x : ℤ) : ℂ) - 4 / (((x : ℤ) : ℂ) + 1)) = 2 * ((k : ℂ)) ^ 2) :
    (N : ℤ) * (x - 1) ^ 2 = 2 * (k : ℤ) ^ 2 * x * (x + 1) := by
  -- The bracketed factor equals (x-1)^2 / (x*(x+1)).
  have hx0C : ((x : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hx1C : ((x : ℤ) : ℂ) + 1 ≠ 0 := by
    have : ((x : ℤ) : ℂ) ≠ -1 := by exact_mod_cast hx1
    intro hh
    exact this (by linear_combination hh)
  have h1 : (1 + 1 / ((x : ℤ) : ℂ) - 4 / (((x : ℤ) : ℂ) + 1)) *
      (((x : ℤ) : ℂ) * (((x : ℤ) : ℂ) + 1)) = (((x : ℤ) : ℂ) - 1) ^ 2 := by
    field_simp
    ring
  -- Clear the denominators in the hypothesis.
  have key : (N : ℂ) * (((x : ℤ) : ℂ) - 1) ^ 2
      = 2 * ((k : ℂ)) ^ 2 * ((x : ℤ) : ℂ) * (((x : ℤ) : ℂ) + 1) := by
    calc (N : ℂ) * (((x : ℤ) : ℂ) - 1) ^ 2
        = (N : ℂ) * ((1 + 1 / ((x : ℤ) : ℂ) - 4 / (((x : ℤ) : ℂ) + 1)) *
            (((x : ℤ) : ℂ) * (((x : ℤ) : ℂ) + 1))) := by rw [h1]
      _ = ((N : ℂ) * (1 + 1 / ((x : ℤ) : ℂ) - 4 / (((x : ℤ) : ℂ) + 1))) *
            (((x : ℤ) : ℂ) * (((x : ℤ) : ℂ) + 1)) := by ring
      _ = (2 * ((k : ℂ)) ^ 2) * (((x : ℤ) : ℂ) * (((x : ℤ) : ℂ) + 1)) := by rw [h]
      _ = 2 * ((k : ℂ)) ^ 2 * ((x : ℤ) : ℂ) * (((x : ℤ) : ℂ) + 1) := by ring
  -- Conclude the integer equality by injectivity of ℤ → ℂ.
  exact_mod_cast key

end Work.BG
