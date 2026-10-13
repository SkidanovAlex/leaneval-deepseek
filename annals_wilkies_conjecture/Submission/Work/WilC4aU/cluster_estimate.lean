import Mathlib
import Submission.Work.WilC4aU.Defs

namespace Work.WilC4aU

/-- Numeric core of the C4aU countability argument.  If two fibre values, at scales `x` and
`2 * x`, satisfy the asymptotic bounds `|y / x^q - a| < δ` and `|y' / (2x)^q - a| < δ` with
`δ = min (|a|/2) (ε₁ * |a| / (8 * 2^q))`, and the ratio of the two values is within `ε₁ / 2` of
`lam`, then `lam` is within `ε₁` of `2^q`. -/
theorem cluster_estimate {q : ℚ} {a ε₁ x y y' lam : ℝ} (ha : a ≠ 0) (hε₁ : 0 < ε₁)
    (hx : 0 < x)
    (h1 : |y / x ^ (q : ℝ) - a| < min (|a| / 2) (ε₁ * |a| / (8 * (2 : ℝ) ^ (q : ℝ))))
    (h2 : |y' / (2 * x) ^ (q : ℝ) - a| < min (|a| / 2) (ε₁ * |a| / (8 * (2 : ℝ) ^ (q : ℝ))))
    (h3 : |y' / y - lam| < ε₁ / 2) : |lam - (2 : ℝ) ^ (q : ℝ)| < ε₁ := by
  -- Write `D = 2 ^ q`, `c = x ^ q`, and the two normalised fibres `u = y / x ^ q`,
  -- `v = y' / (2 x) ^ q`.  The ratio is `y' / y = D * (v / u)`, and both `u` and `v`
  -- are within `ε₁ |a| / (8 D)` of `a` while `|u| > |a| / 2`; hence `|v / u - 1|`
  -- is at most `ε₁ / (2 D)`, and the claim follows by the triangle inequality.
  set D : ℝ := (2 : ℝ) ^ (q : ℝ) with hDdef
  set c : ℝ := x ^ (q : ℝ) with hcdef
  set u : ℝ := y / c with hudef
  set v : ℝ := y' / (2 * x) ^ (q : ℝ) with hvdef
  have hc : 0 < c := by rw [hcdef]; exact Real.rpow_pos_of_pos hx _
  have hcne : c ≠ 0 := ne_of_gt hc
  have hD : 0 < D := by rw [hDdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hDne : D ≠ 0 := ne_of_gt hD
  have haa : 0 < |a| := abs_pos.mpr ha
  have h1a : |u - a| < |a| / 2 := lt_of_lt_of_le h1 (min_le_left _ _)
  have h2a : |v - a| < |a| / 2 := lt_of_lt_of_le h2 (min_le_left _ _)
  have h1b : |u - a| < ε₁ * |a| / (8 * D) := lt_of_lt_of_le h1 (min_le_right _ _)
  have h2b : |v - a| < ε₁ * |a| / (8 * D) := lt_of_lt_of_le h2 (min_le_right _ _)
  -- `|u| > |a| / 2`, by the reverse triangle inequality.
  have htri : |a| ≤ |u| + |u - a| := by
    have h : a = u + (a - u) := by ring
    calc |a| = |u + (a - u)| := by rw [← h]
      _ ≤ |u| + |a - u| := abs_add_le _ _
      _ = |u| + |u - a| := by rw [abs_sub_comm]
  have hu_gt : |a| / 2 < |u| := by linarith
  have hu_abs : 0 < |u| := lt_trans (half_pos haa) hu_gt
  have hu_ne : u ≠ 0 := abs_pos.mp hu_abs
  -- `|v - u| < ε₁ |a| / (4 D)`.
  have hvu : |v - u| < ε₁ * |a| / (4 * D) := by
    have h1b' : |a - u| < ε₁ * |a| / (8 * D) := by rw [abs_sub_comm]; exact h1b
    have hsum : ε₁ * |a| / (8 * D) + ε₁ * |a| / (8 * D) = ε₁ * |a| / (4 * D) := by
      field_simp
      ring
    calc |v - u| ≤ |v - a| + |a - u| := abs_sub_le v a u
      _ < ε₁ * |a| / (8 * D) + ε₁ * |a| / (8 * D) := add_lt_add h2b h1b'
      _ = ε₁ * |a| / (4 * D) := hsum
  have h2x : (2 * x) ^ (q : ℝ) = D * c := by
    rw [hDdef, hcdef]
    exact Real.mul_rpow (by norm_num) (le_of_lt hx)
  -- Rewrite `y = u * c`, `y' = v * D * c`.
  have hy_eq : y = u * c := by rw [hudef]; field_simp
  have hy'_eq : y' = v * (2 * x) ^ (q : ℝ) := by rw [hvdef]; field_simp
  have hy'_eq2 : y' = v * D * c := by rw [hy'_eq, h2x]; ring
  have hkey : y' / y - D = D * (v - u) / u := by
    rw [hy'_eq2, hy_eq]
    field_simp
  have habs : |y' / y - D| = D * |v - u| / |u| := by
    rw [hkey, abs_div, abs_mul, abs_of_pos hD]
  have hstep1 : D * |v - u| < ε₁ * |a| / 4 := by
    have h := mul_lt_mul_of_pos_left hvu hD
    have heq : D * (ε₁ * |a| / (4 * D)) = ε₁ * |a| / 4 := by
      field_simp
    linarith
  have hstep2 : ε₁ * |a| / 4 < (ε₁ / 2) * |u| := by
    have h := mul_lt_mul_of_pos_left hu_gt (half_pos hε₁)
    have heq : (ε₁ / 2) * (|a| / 2) = ε₁ * |a| / 4 := by ring
    linarith
  have hbound : D * |v - u| / |u| < ε₁ / 2 := by
    rw [div_lt_iff₀ hu_abs]
    linarith
  have hmid : |y' / y - D| < ε₁ / 2 := by rw [habs]; exact hbound
  -- Combine with `h3` by the triangle inequality.
  have hsplit : (lam - y' / y) + (y' / y - D) = lam - D := by ring
  calc |lam - D| = |(lam - y' / y) + (y' / y - D)| := by rw [hsplit]
    _ ≤ |lam - y' / y| + |y' / y - D| := abs_add_le _ _
    _ = |y' / y - lam| + |y' / y - D| := by rw [abs_sub_comm lam (y' / y)]
    _ < ε₁ / 2 + ε₁ / 2 := add_lt_add h3 hmid
    _ = ε₁ := by ring

end Work.WilC4aU
