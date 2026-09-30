import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tent majorant and its Fourier coefficients

This file sets up the vocabulary for the counting-function bound (Lemma N2 of Heath-Brown's
"a new `k`-th derivative estimate for exponential sums via Vinogradov's mean value").

* `nint x` is the distance from `x` to the nearest integer.
* `tent B x = max (1 - nint x / B) 0` is the tent/hat function of width `B`, which for
  `0 < B ≤ 1/2` equals the Fourier series `∑_r ĉ_r e(rx)` with the non-negative coefficients
  `tentCoeff B r`.
* `eZ t = exp (2 * π * I * t)`.
-/

namespace Work.BMF

/-- Distance from `x` to the nearest integer. -/
noncomputable def nint (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- The tent (hat) function of width `B`: `max (1 - nint x / B) 0`. -/
noncomputable def tent (B x : ℝ) : ℝ := max (1 - nint x / B) 0

/-- The `r`-th Fourier coefficient of the tent of width `B`. -/
noncomputable def tentCoeff (B : ℝ) (r : ℤ) : ℝ :=
  if r = 0 then B
  else Real.sin (Real.pi * (r : ℝ) * B) ^ 2 / (Real.pi ^ 2 * (r : ℝ) ^ 2 * B)

/-- The additive character `e(t) = exp (2 * π * I * t)`. -/
noncomputable def eZ (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

lemma nint_nonneg (x : ℝ) : 0 ≤ nint x := abs_nonneg _

lemma nint_le_half (x : ℝ) : nint x ≤ 1 / 2 := abs_sub_round x

lemma nint_le_abs (x : ℝ) (z : ℤ) : nint x ≤ |x - (z : ℝ)| := round_le x z

lemma nint_add_intCast (x : ℝ) (z : ℤ) : nint (x + z) = nint x := by
  unfold nint
  rw [round_add_intCast, Int.cast_add]
  congr 1
  ring

lemma nint_eq_min_fract (x : ℝ) : nint x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x

lemma nint_neg (x : ℝ) : nint (-x) = nint x := by
  rw [nint_eq_min_fract, nint_eq_min_fract]
  rcases eq_or_ne (Int.fract x) 0 with h | h
  · have hx : x = (⌊x⌋ : ℝ) := by
      have h' := Int.fract_add_floor x; rw [h, zero_add] at h'; exact h'.symm
    rw [hx, ← Int.cast_neg, Int.fract_intCast, Int.fract_intCast]
  · rw [Int.fract_neg h, show 1 - (1 - Int.fract x) = Int.fract x by ring]
    exact min_comm _ _

lemma nint_sub_intCast (x : ℝ) (z : ℤ) : nint (x - z) = nint x := by
  rw [sub_eq_add_neg, ← Int.cast_neg, nint_add_intCast]

lemma nint_eq_zero_iff (x : ℝ) : nint x = 0 ↔ ∃ z : ℤ, x = (z : ℝ) := by
  constructor
  · intro h
    have : x - (round x : ℝ) = 0 := abs_eq_zero.mp h
    exact ⟨round x, by linarith⟩
  · rintro ⟨z, rfl⟩
    rw [nint, round_intCast]; simp

lemma nint_abs (x : ℝ) : nint |x| = nint x := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, nint_neg]

/-- The tent is non-negative. -/
lemma tent_nonneg (B x : ℝ) : 0 ≤ tent B x := le_max_right _ _

/-- `tent B x = 0` once `nint x ≥ B` (for `B > 0`). -/
lemma tent_eq_zero_of_le {B x : ℝ} (hB : 0 < B) (h : B ≤ nint x) : tent B x = 0 := by
  have : 1 - nint x / B ≤ 0 := by
    rw [sub_nonpos, one_le_div hB]; linarith
  exact max_eq_right this

/-- On `nint x ≤ B` the tent is the linear function `1 - nint x / B`. -/
lemma tent_eq_of_le {B x : ℝ} (hB : 0 < B) (h : nint x ≤ B) : tent B x = 1 - nint x / B := by
  have : 0 ≤ 1 - nint x / B := by
    rw [sub_nonneg, div_le_one hB]; exact h
  exact max_eq_left this

/-- The tent is at most one. -/
lemma tent_le_one {B x : ℝ} (hB : 0 < B) : tent B x ≤ 1 := by
  rcases le_total B (nint x) with h | h
  · rw [tent_eq_zero_of_le hB h]; norm_num
  · rw [tent_eq_of_le hB h]
    have : 0 ≤ nint x / B := div_nonneg (nint_nonneg x) hB.le
    linarith

/-- On the inner half of the interval the tent is at least `1/2`. -/
lemma tent_ge_half {B x : ℝ} (hB : 0 < B) (h : nint x ≤ B / 2) : 1 / 2 ≤ tent B x := by
  rw [tent_eq_of_le hB (le_trans h (by linarith))]
  have : nint x / B ≤ 1 / 2 := by
    rw [div_le_iff₀ hB]; linarith
  linarith

/-- The tent is positive exactly when `nint x < B`. -/
lemma tent_pos_iff {B x : ℝ} (hB : 0 < B) : 0 < tent B x ↔ nint x < B := by
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    rw [tent_eq_zero_of_le hB hc] at h
    exact lt_irrefl _ h
  · intro h
    rw [tent_eq_of_le hB h.le]
    have : nint x / B < 1 := (div_lt_one hB).mpr h
    linarith

/-- The Fourier coefficients of the tent are non-negative (for `B ≥ 0`). -/
lemma tentCoeff_nonneg {B : ℝ} (hB : 0 ≤ B) (r : ℤ) : 0 ≤ tentCoeff B r := by
  unfold tentCoeff
  split_ifs with h
  · exact hB
  · positivity

/-- The Fourier coefficients of the tent are even. -/
lemma tentCoeff_neg (B : ℝ) (r : ℤ) : tentCoeff B (-r) = tentCoeff B r := by
  unfold tentCoeff
  rcases eq_or_ne r 0 with h | h
  · subst h; simp
  · have h' : -r ≠ 0 := neg_ne_zero.mpr h
    rw [if_neg h, if_neg h', Int.cast_neg]
    rw [show Real.pi * -(r : ℝ) * B = -(Real.pi * (r : ℝ) * B) by ring, Real.sin_neg, neg_sq,
      show Real.pi ^ 2 * (-(r : ℝ)) ^ 2 * B = Real.pi ^ 2 * (r : ℝ) ^ 2 * B by ring]

end Work.BMF
