/-
**AR-C4** (BG 1981, p. 215): the "`1 < 3/5 + 2/5`" arithmetic.

If `1 + a + b + c = 0` and `d₁ + d₂ + d₃ + d₄ = 0` with all `|·| ≥ 5`, then
`1 + 1/a + 1/b + 1/c ≠ 1/d₁ + … + 1/d₄`.

Route (as in `NOTES_LEAD_gw_design16.md`): the left side is `> 3/5` and the right side is
`< 3/5`.

* Left: `a + b + c = -1` rules out three negative summands (each `≤ -5` would give
  `a + b + c ≤ -15`), so at most two of `a, b, c` are negative; a negative summand `x`
  contributes `1/x ≥ -1/5` (as `|x| ≥ 5`) and a non-negative one contributes `1/x > 0`.
  At most two negatives therefore leave `1 + 1/a + 1/b + 1/c > 1 - 2/5 = 3/5`
  (with the `1/c > 0` of the third summand supplying strictness in the two-negative case).
* Right: `d₁ + … + d₄ = 0` forces one of the `dᵢ` to be negative; that summand is `< 0`
  and each of the remaining three is `≤ 1/5`, so the sum is `< 3/5`.
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs

namespace Work.BG

/-! ## Elementary bounds on `1/x` for `|x| ≥ 5` -/

/-- An integer of absolute value `≥ 5` that is negative is at most `-5`. -/
lemma arithC4_le_neg_five_of_abs {x : ℤ} (h : 5 ≤ |x|) (hx : x < 0) : x ≤ -5 := by
  rw [abs_of_neg hx] at h; omega

/-- An integer of absolute value `≥ 5` that is non-negative is at least `5`. -/
lemma arithC4_five_le_of_nonneg_abs {x : ℤ} (h : 5 ≤ |x|) (hx : 0 ≤ x) : 5 ≤ x := by
  rwa [abs_of_nonneg hx] at h

/-- For a negative integer with `|x| ≥ 5` one has `1/x ≥ -1/5`. -/
lemma arithC4_neg_one_fifth_le_one_div {x : ℤ} (h : 5 ≤ |x|) (hx : x < 0) :
    (-(1 / 5) : ℚ) ≤ 1 / (x : ℚ) := by
  have hx' : x ≤ -5 := arithC4_le_neg_five_of_abs h hx
  have hxq : (x : ℚ) ≤ -5 := by exact_mod_cast hx'
  have hm : (5 : ℚ) ≤ -(x : ℚ) := by linarith
  have h1 : (1 : ℚ) / (-(x : ℚ)) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hm
  have h2 : (1 : ℚ) / (-(x : ℚ)) = -(1 / (x : ℚ)) := by
    rw [one_div_neg_eq_neg_one_div]
  linarith

/-- For a non-negative integer with `|x| ≥ 5` one has `1/x > 0`. -/
lemma arithC4_one_div_pos_of_abs {x : ℤ} (h : 5 ≤ |x|) (hx : 0 ≤ x) :
    (0 : ℚ) < 1 / (x : ℚ) := by
  have h5 : 5 ≤ x := arithC4_five_le_of_nonneg_abs h hx
  have : (0 : ℚ) < (x : ℚ) := by exact_mod_cast (by omega : 0 < x)
  exact one_div_pos.mpr this

/-- For any integer with `|x| ≥ 5` one has `1/x ≤ 1/5`. -/
lemma arithC4_one_div_le_fifth_of_abs {x : ℤ} (h : 5 ≤ |x|) : (1 : ℚ) / (x : ℚ) ≤ 1 / 5 := by
  rcases lt_or_ge x 0 with hx | hx
  · have hlt : (1 : ℚ) / (x : ℚ) < 0 := div_neg_of_pos_of_neg one_pos (by exact_mod_cast hx)
    linarith
  · have h5 : 5 ≤ x := arithC4_five_le_of_nonneg_abs h hx
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h5)

/-! ## The two bounds -/

/-- Left side: `1 + 1/a + 1/b + 1/c > 3/5`. -/
lemma arithC4_lhs_bound (a b c : ℤ) (ha : 5 ≤ |a|) (hb : 5 ≤ |b|) (hc : 5 ≤ |c|)
    (hsum : 1 + a + b + c = 0) :
    (3 : ℚ) / 5 < 1 + 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) := by
  rcases lt_or_ge a 0 with ha0 | ha0 <;> rcases lt_or_ge b 0 with hb0 | hb0 <;>
    rcases lt_or_ge c 0 with hc0 | hc0
  · -- three negatives: impossible, `a + b + c ≤ -15`
    exfalso
    have h1 := arithC4_le_neg_five_of_abs ha ha0
    have h2 := arithC4_le_neg_five_of_abs hb hb0
    have h3 := arithC4_le_neg_five_of_abs hc hc0
    omega
  · -- two negatives, third positive
    have hA := arithC4_neg_one_fifth_le_one_div ha ha0
    have hB := arithC4_neg_one_fifth_le_one_div hb hb0
    have hC := arithC4_one_div_pos_of_abs hc hc0
    linarith
  · have hA := arithC4_neg_one_fifth_le_one_div ha ha0
    have hB := arithC4_one_div_pos_of_abs hb hb0
    have hC := arithC4_neg_one_fifth_le_one_div hc hc0
    linarith
  · -- one negative, two positive
    have hA := arithC4_neg_one_fifth_le_one_div ha ha0
    have hB := arithC4_one_div_pos_of_abs hb hb0
    have hC := arithC4_one_div_pos_of_abs hc hc0
    linarith
  · have hA := arithC4_one_div_pos_of_abs ha ha0
    have hB := arithC4_neg_one_fifth_le_one_div hb hb0
    have hC := arithC4_neg_one_fifth_le_one_div hc hc0
    linarith
  · have hA := arithC4_one_div_pos_of_abs ha ha0
    have hB := arithC4_neg_one_fifth_le_one_div hb hb0
    have hC := arithC4_one_div_pos_of_abs hc hc0
    linarith
  · have hA := arithC4_one_div_pos_of_abs ha ha0
    have hB := arithC4_one_div_pos_of_abs hb hb0
    have hC := arithC4_neg_one_fifth_le_one_div hc hc0
    linarith
  · -- no negatives: impossible, `a + b + c ≥ 15`
    exfalso
    have h1 := arithC4_five_le_of_nonneg_abs ha ha0
    have h2 := arithC4_five_le_of_nonneg_abs hb hb0
    have h3 := arithC4_five_le_of_nonneg_abs hc hc0
    omega

/-- Right side: `1/d₁ + … + 1/d₄ < 3/5`. -/
lemma arithC4_rhs_bound (d1 d2 d3 d4 : ℤ) (h1 : 5 ≤ |d1|) (h2 : 5 ≤ |d2|) (h3 : 5 ≤ |d3|)
    (h4 : 5 ≤ |d4|) (hsum : d1 + d2 + d3 + d4 = 0) :
    1 / (d1 : ℚ) + 1 / (d2 : ℚ) + 1 / (d3 : ℚ) + 1 / (d4 : ℚ) < (3 : ℚ) / 5 := by
  -- some summand is negative (otherwise all are `≥ 5` and the sum is `≥ 20`)
  have hneg : d1 < 0 ∨ d2 < 0 ∨ d3 < 0 ∨ d4 < 0 := by
    by_contra h
    simp only [not_lt, not_or] at h
    have e1 := arithC4_five_le_of_nonneg_abs h1 h.1
    have e2 := arithC4_five_le_of_nonneg_abs h2 h.2.1
    have e3 := arithC4_five_le_of_nonneg_abs h3 h.2.2.1
    have e4 := arithC4_five_le_of_nonneg_abs h4 h.2.2.2
    omega
  rcases hneg with hd | hd | hd | hd
  · have hA : (1 : ℚ) / (d1 : ℚ) < 0 :=
      div_neg_of_pos_of_neg one_pos (by exact_mod_cast hd)
    have hB := arithC4_one_div_le_fifth_of_abs h2
    have hC := arithC4_one_div_le_fifth_of_abs h3
    have hD := arithC4_one_div_le_fifth_of_abs h4
    linarith
  · have hA : (1 : ℚ) / (d2 : ℚ) < 0 :=
      div_neg_of_pos_of_neg one_pos (by exact_mod_cast hd)
    have hB := arithC4_one_div_le_fifth_of_abs h1
    have hC := arithC4_one_div_le_fifth_of_abs h3
    have hD := arithC4_one_div_le_fifth_of_abs h4
    linarith
  · have hA : (1 : ℚ) / (d3 : ℚ) < 0 :=
      div_neg_of_pos_of_neg one_pos (by exact_mod_cast hd)
    have hB := arithC4_one_div_le_fifth_of_abs h1
    have hC := arithC4_one_div_le_fifth_of_abs h2
    have hD := arithC4_one_div_le_fifth_of_abs h4
    linarith
  · have hA : (1 : ℚ) / (d4 : ℚ) < 0 :=
      div_neg_of_pos_of_neg one_pos (by exact_mod_cast hd)
    have hB := arithC4_one_div_le_fifth_of_abs h1
    have hC := arithC4_one_div_le_fifth_of_abs h2
    have hD := arithC4_one_div_le_fifth_of_abs h3
    linarith

/-! ## AR-C4 -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem arithC4 : Work.GW2.C16.ArithC4Prop := by
  intro a b c d1 d2 d3 d4 ha hb hc hd1 hd2 hd3 hd4 hsum1 hsum2 heq
  have hl := arithC4_lhs_bound a b c ha hb hc hsum1
  have hr := arithC4_rhs_bound d1 d2 d3 d4 hd1 hd2 hd3 hd4 hsum2
  rw [heq] at hl
  linarith

end Work.BG
