import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A separation bound for `|log n - log m|`

`Work.BMF.mr_direct.inv_three_mul_le_abs_log_sub`: for natural numbers `1 ≤ n, m ≤ B`
with `0 < B` and `n ≠ m`, the logarithms are separated by

`1 / (3 * B) ≤ |Real.log n - Real.log m|`.

The point is that two *distinct* integers of size at most `B` have logarithms that differ
by at least a constant multiple of `1/B`.  Since `log x` has derivative `1/x ≥ 1/B` on
`[1, B]`, and the minimal gap between two distinct integers in `[1, B]` is `1`, the estimate
is the mean value theorem applied to the interval between the two integers.

Concretely, if `b < a` then `log a - log b = log (a/b) = log (1 + (a-b)/b)`, and since
`log (1 + x) ≥ x / (1 + x)` for `x > 0`, we get `log a - log b ≥ (a - b)/a ≥ 1/a ≥ 1/(3B)`.
-/

namespace Work.BMF.mr_direct

/-- For `x > 0`, `x / (1 + x) ≤ log (1 + x)`.

Indeed, applying `log y ≤ y - 1` (`Real.log_le_sub_one_of_pos`) to `y = (1 + x)⁻¹` gives
`- log (1 + x) ≤ (1 + x)⁻¹ - 1`, i.e. `log (1 + x) ≥ 1 - (1 + x)⁻¹ = x / (1 + x)`. -/
private lemma one_sub_inv_le_log_one_add (x : ℝ) (hx : 0 < x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have hpos : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have hxeq : x / (1 + x) = 1 - (1 + x)⁻¹ := by
    have hne : (1 + x) ≠ 0 := ne_of_gt hpos
    field_simp
    ring
  rw [hxeq]
  linarith

/-- If `b < a` are naturals with `b ≥ 1`, `(a : ℝ) ≤ B` and `0 < B`, then
`1 / (3 * B) ≤ log a - log b`. -/
private lemma key {a b : ℕ} {B : ℝ} (hb1 : 1 ≤ b) (hnB : (a:ℝ) ≤ B) (hB : 0 < B)
    (hba : b < a) : 1/(3*B) ≤ Real.log a - Real.log b := by
  have ha_pos : (0:ℝ) < (a:ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have hb_pos : (0:ℝ) < (b:ℝ) := by
    have : 0 < b := by omega
    exact_mod_cast this
  have ha_ne : (a:ℝ) ≠ 0 := ne_of_gt ha_pos
  have hb_ne : (b:ℝ) ≠ 0 := ne_of_gt hb_pos
  have hdecomp : Real.log (a:ℝ) - Real.log (b:ℝ) = Real.log ((a:ℝ)/(b:ℝ)) :=
    (Real.log_div ha_ne hb_ne).symm
  rw [hdecomp]
  have hna : (a:ℝ) = (b:ℝ) + ((a - b : ℕ):ℝ) := by
    have h : (a:ℝ) = ((b + (a - b) : ℕ):ℝ) := by
      congr 1
      omega
    rw [h]; push_cast; ring
  have hratio : (a:ℝ)/(b:ℝ) = 1 + ((a-b:ℕ):ℝ)/(b:ℝ) := by
    rw [hna]
    rw [add_div, div_self hb_ne]
  have hx_pos : 0 < ((a-b:ℕ):ℝ)/(b:ℝ) := by
    apply div_pos _ hb_pos
    have : 0 < a - b := by omega
    exact_mod_cast this
  have hkey := one_sub_inv_le_log_one_add (((a-b:ℕ):ℝ)/(b:ℝ)) hx_pos
  have hxval : (((a-b:ℕ):ℝ)/(b:ℝ)) / (1 + ((a-b:ℕ):ℝ)/(b:ℝ)) = ((a-b:ℕ):ℝ)/(a:ℝ) := by
    rw [← hratio]
    field_simp
  rw [hratio]
  calc 1/(3*B) ≤ 1/(a:ℝ) := by
        apply one_div_le_one_div_of_le ha_pos
        linarith
    _ ≤ ((a-b:ℕ):ℝ)/(a:ℝ) := by
        rw [div_le_div_iff_of_pos_right ha_pos]
        have : 1 ≤ a - b := by omega
        exact_mod_cast this
    _ = (((a-b:ℕ):ℝ)/(b:ℝ)) / (1 + ((a-b:ℕ):ℝ)/(b:ℝ)) := hxval.symm
    _ ≤ Real.log (1 + ((a-b:ℕ):ℝ)/(b:ℝ)) := hkey

theorem inv_three_mul_le_abs_log_sub {n m : ℕ} {B : ℝ} (hn1 : 1 ≤ n) (hm1 : 1 ≤ m)
    (hnB : (n : ℝ) ≤ B) (hmB : (m : ℝ) ≤ B) (hB : 0 < B) (hnm : n ≠ m) :
    1 / (3 * B) ≤ |Real.log n - Real.log m| := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · -- `n < m`: the absolute value is `log m - log n`
    have h := key (a := m) (b := n) hn1 hmB hB hlt
    have hneg : Real.log (n:ℝ) - Real.log (m:ℝ) < 0 := by
      have h1 : (n:ℝ) < (m:ℝ) := by exact_mod_cast hlt
      have hn_pos : (0:ℝ) < (n:ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      have hm_pos : (0:ℝ) < (m:ℝ) := by
        have : 0 < m := by omega
        exact_mod_cast this
      have : Real.log (n:ℝ) < Real.log (m:ℝ) := (Real.log_lt_log_iff hn_pos hm_pos).mpr h1
      linarith
    rw [abs_of_neg hneg]
    linarith
  · -- `m < n`: the absolute value is `log n - log m`
    have h := key (a := n) (b := m) hm1 hnB hB hgt
    have hpos : 0 < Real.log (n:ℝ) - Real.log (m:ℝ) := by
      have h1 : (m:ℝ) < (n:ℝ) := by exact_mod_cast hgt
      have hn_pos : (0:ℝ) < (n:ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      have hm_pos : (0:ℝ) < (m:ℝ) := by
        have : 0 < m := by omega
        exact_mod_cast this
      have : Real.log (m:ℝ) < Real.log (n:ℝ) := (Real.log_lt_log_iff hm_pos hn_pos).mpr h1
      linarith
    rw [abs_of_pos hpos]
    exact h

end Work.BMF.mr_direct
