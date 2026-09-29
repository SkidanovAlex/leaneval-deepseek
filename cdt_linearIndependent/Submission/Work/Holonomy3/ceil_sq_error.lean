import Mathlib

namespace Work.Holonomy3

/-- For `z ≥ 0`, writing `Z = ⌈z⌉`, the quantity `Z * (Z - 1) - z ^ 2` is bounded by `Z` in
absolute value.  (It lies in the interval `[-Z, Z]`.) -/
lemma ceil_pred_mul_sub_sq_abs_le (z : ℝ) (hz : 0 ≤ z) :
    |(Nat.ceil z : ℝ) * ((Nat.ceil z : ℝ) - 1) - z ^ 2| ≤ (Nat.ceil z : ℝ) := by
  have hge : z ≤ (Nat.ceil z : ℝ) := Nat.le_ceil z
  have hlt : (Nat.ceil z : ℝ) < z + 1 := Nat.ceil_lt_add_one hz
  have hZ0 : (0 : ℝ) ≤ (Nat.ceil z : ℝ) := le_trans hz hge
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((Nat.ceil z : ℝ) - z), sq_nonneg z]

/-- The error in replacing a squared difference by the corresponding difference of the ceilings. -/
lemma ceil_sq_error {d : ℕ} {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hyd : y ≤ (d : ℝ)) :
    |((Nat.ceil y : ℝ) * ((Nat.ceil y : ℝ) - 1) - (Nat.ceil x : ℝ) * ((Nat.ceil x : ℝ) - 1))
      - (y ^ 2 - x ^ 2)| ≤ 5 * (d : ℝ) + 2 := by
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hx := ceil_pred_mul_sub_sq_abs_le x hx0
  have hy := ceil_pred_mul_sub_sq_abs_le y hy0
  have heq : ((Nat.ceil y : ℝ) * ((Nat.ceil y : ℝ) - 1) - (Nat.ceil x : ℝ) * ((Nat.ceil x : ℝ) - 1))
      - (y ^ 2 - x ^ 2)
      = ((Nat.ceil y : ℝ) * ((Nat.ceil y : ℝ) - 1) - y ^ 2)
        - ((Nat.ceil x : ℝ) * ((Nat.ceil x : ℝ) - 1) - x ^ 2) := by ring
  rw [heq]
  have hYd : (Nat.ceil y : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.ceil_le.mpr hyd)
  have hXd : (Nat.ceil x : ℝ) ≤ (d : ℝ) :=
    by exact_mod_cast (Nat.ceil_le.mpr (le_trans hxy hyd))
  have htri : |((Nat.ceil y : ℝ) * ((Nat.ceil y : ℝ) - 1) - y ^ 2)
        - ((Nat.ceil x : ℝ) * ((Nat.ceil x : ℝ) - 1) - x ^ 2)|
      ≤ |(Nat.ceil y : ℝ) * ((Nat.ceil y : ℝ) - 1) - y ^ 2|
        + |(Nat.ceil x : ℝ) * ((Nat.ceil x : ℝ) - 1) - x ^ 2| := by
    have h := abs_add_le ((Nat.ceil y : ℝ) * ((Nat.ceil y : ℝ) - 1) - y ^ 2)
      (-((Nat.ceil x : ℝ) * ((Nat.ceil x : ℝ) - 1) - x ^ 2))
    rwa [sub_eq_add_neg, abs_neg] at h
  calc |((Nat.ceil y : ℝ) * ((Nat.ceil y : ℝ) - 1) - y ^ 2)
        - ((Nat.ceil x : ℝ) * ((Nat.ceil x : ℝ) - 1) - x ^ 2)|
      ≤ |(Nat.ceil y : ℝ) * ((Nat.ceil y : ℝ) - 1) - y ^ 2|
        + |(Nat.ceil x : ℝ) * ((Nat.ceil x : ℝ) - 1) - x ^ 2| := htri
    _ ≤ (Nat.ceil y : ℝ) + (Nat.ceil x : ℝ) := add_le_add hy hx
    _ ≤ (d : ℝ) + (d : ℝ) := add_le_add hYd hXd
    _ ≤ 5 * (d : ℝ) + 2 := by
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith

end Work.Holonomy3
