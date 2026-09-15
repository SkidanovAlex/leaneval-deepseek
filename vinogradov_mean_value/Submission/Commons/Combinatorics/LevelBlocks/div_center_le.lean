import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Cast.Order.Field

namespace Commons.Combinatorics.LevelBlocks

/-- For `0 < b`, the real number `a/b` lies in the interval `[a/b, a/b+1)`
where the floor `a/b` is the natural-number division. -/
lemma nat_div_bounds {a b : ℕ} (hb : 0 < b) :
    (((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ)) ∧
      ((a : ℝ) / (b : ℝ) ≤ ((a / b : ℕ) : ℝ) + 1) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  refine ⟨Nat.cast_div_le, ?_⟩
  rw [div_le_iff₀ hbR]
  have hlt : a < (a / b + 1) * b :=
    (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self _)
  have hcast : (a : ℝ) < (((a / b : ℕ) : ℝ) + 1) * (b : ℝ) := by
    exact_mod_cast hlt
  exact le_of_lt hcast

/-- Core real estimate: if `c ≤ y ≤ c+1` then `y/n` is within `1/(2n)` of the
center of the block `[c/n, (c+1)/n]`, namely `(c+1/2)/n`. -/
lemma div_center_aux {y : ℝ} {n : ℕ} (hn : 0 < n) (c : ℕ)
    (h1 : (c : ℝ) ≤ y) (h2 : y ≤ (c : ℝ) + 1) :
    |y / (n : ℝ) - (c : ℝ) / (n : ℝ) - 1 / (2 * (n : ℝ))| ≤ 1 / (2 * (n : ℝ)) := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkey : y / (n : ℝ) - (c : ℝ) / (n : ℝ) - 1 / (2 * (n : ℝ))
      = (y - (c : ℝ) - 1 / 2) / (n : ℝ) := by
    field_simp
  rw [hkey, abs_div, abs_of_pos hN]
  have hb : |y - (c : ℝ) - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  calc |y - (c : ℝ) - 1 / 2| / (n : ℝ)
      ≤ (1 / 2) / (n : ℝ) := div_le_div_of_nonneg_right hb (le_of_lt hN)
    _ = 1 / (2 * (n : ℝ)) := by field_simp

theorem div_center_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : ℕ) :
    |((2 * i + 1 : ℕ) : ℝ) / (2 * m)
      - ((((n * (2 * i + 1)) / (2 * m)) : ℕ) : ℝ) / n - 1 / (2 * (n : ℝ))|
      ≤ 1 / (2 * (n : ℝ)) := by
  have hb : 0 < 2 * m := by omega
  have hbounds := nat_div_bounds (a := n * (2 * i + 1)) (b := 2 * m) hb
  have hmain := div_center_aux (y := ((n * (2 * i + 1) : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ))
    (n := n) hn ((n * (2 * i + 1)) / (2 * m)) hbounds.1 hbounds.2
  have hrw : ((n * (2 * i + 1) : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) / (n : ℝ)
      = ((2 * i + 1 : ℕ) : ℝ) / (2 * (m : ℝ)) := by
    have hnum : ((n * (2 * i + 1) : ℕ) : ℝ) = (n : ℝ) * ((2 * i + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have hden : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [hnum, hden]
    have hnR : (n : ℝ) ≠ 0 := by
      have h : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact ne_of_gt h
    have hmR : (m : ℝ) ≠ 0 := by
      have h : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact ne_of_gt h
    field_simp
  rw [hrw] at hmain
  exact hmain

end Commons.Combinatorics.LevelBlocks