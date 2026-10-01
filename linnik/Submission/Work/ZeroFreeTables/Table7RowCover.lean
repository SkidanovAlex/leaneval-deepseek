/-
# ZeroFreeTables — Table7RowCover

`Work.ZeroFreeTables.Table7RowCover`: the rows of Heath-Brown's Table 7 (`hbTable7`) cover the
whole range `797/10000 ≤ λ₁ ≤ 696/1000` for the target curve `(12/11)·log(1/λ₁)`:

for every `λ₁ ∈ [797/10000, 696/1000]` there is a row `p = (λ₁ᵖ, λ₂ᵖ)` of `tableR hbTable7` with
`λ₁ ≤ λ₁ᵖ` and `(12/11)·log(1/λ₁) ≤ λ₂ᵖ`.

This is the *upper* half of the `λ₁`-cover whose lower half (`λ₁ ≤ 797/10000`) is
`Work.ZeroFreeTables.TentRowCover`: below `797/10000` the tent rows are used, above it the rows of
Table 7.  The printed first row of Table 7 is `λ₁ = 0.10`, and `797/10000` is the smallest value
for which the row `(0.10, 2.76)` still dominates `(12/11)·log(1/λ₁)` — indeed
`(12/11)·log(1/0.0797) ≈ 2.759439 ≤ 2.76`, slack `5.6·10⁻⁴` — which is what fixes the hypothesis
`797/10000 ≤ λ₁` of the statement.

## The proof

Write `L_i`, `M_i` for the first and second component of the `(i+1)`-st row of `hbTable7`
(`i = 0, …, 15`, i.e. `L_i = (10+2i)/100` for `i ≤ 5`, `L_i = (20+5(i-5))/100` for `6 ≤ i ≤ 15`)
and put `L_{-1} := 797/10000`.  The `L_i` are increasing and the `M_i` decreasing, so a `λ₁` with
`L_{i-1} ≤ λ₁ ≤ L_i` is covered by row `i` as soon as

  `(12/11)·log(1/L_{i-1}) ≤ M_i`      (`t7Chain_{i+1}` below),

because `log(1/λ₁) ≤ log(1/L_{i-1})` (`t7Step`, from `0 < L_{i-1} ≤ λ₁`).  Since
`696/1000 ≤ 70/100 = L₁₅`, the last row `(0.70, 0.79)` of Table 7 covers everything above
`L₁₄ = 0.65`; the final row `(0.745, 0.745)` of the table is not needed here (it serves the
`λ₁ < 696/1000` clause of `HBTable7`).

The cover is performed below by a `by_cases` waterfall on `λ₁ ≤ L_i`, `i = 0, …, 14`, each branch
exhibiting the corresponding row (`t7Mem_{i+1}`), the last branch being the row `(0.70, 0.79)`.

The 16 chain conditions are the transcendental comparisons `(12/11)·log(1/L_{i-1}) ≤ M_i`, each
with a rational slack between `5.6·10⁻⁴` (`i = 0`) and `3.2·10⁻¹` (`i = 15`).  They are reduced by
`log_le_of_partialSum_le` to the rational inequalities `1/L_{i-1} ≤ ∑_{j<n} ((11/12)M_i)^j/j!`:
partial Taylor sums of `exp` are lower bounds for `exp` (`Real.sum_le_exp_of_nonneg`), and the
comparison is a computation in exact rational arithmetic closed by `norm_num`.  The number `n` of
terms is chosen so that the Taylor error is far below the slack: `n = 10` for `i = 0` (the tight
case), down to `n = 2` for `i ≥ 13`.  The choice `c = (11/12)·M_i` makes the final multiplication
by `12/11` exact.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.T7Cert
import Submission.Work.ZeroFreeTables.HBProps

namespace Work.ZeroFreeTables

/-! ## The logarithm/Taylor comparison -/

/-- If `c ≥ 0` and the `n`-th partial Taylor sum of `exp` at `c` dominates `r > 0`, then
`log r ≤ c`. -/
private lemma log_le_of_partialSum_le {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (n : ℕ)
    (h : r ≤ ∑ i ∈ Finset.range n, c ^ i / ((i.factorial : ℕ) : ℝ)) :
    Real.log r ≤ c :=
  (Real.log_le_iff_le_exp hr).mpr (h.trans (Real.sum_le_exp_of_nonneg hc n))

/-! ## The 16 chain conditions `(12/11)·log(1/L_{i-1}) ≤ M_i`

Each is `log_le_of_partialSum_le` at `r = 1/L_{i-1}`, `c = (11/12)·M_i`, `n` terms, followed by
`linarith`: `(12/11)·((11/12)·M_i) = M_i`. -/

/-- Chain condition at `L_{-1} = 797/10000`, for the row `(0.10, 2.76)`. -/
private lemma t7Chain1 : (12/11 : ℝ) * Real.log (1 / ((797:ℝ)/10000)) ≤ 276/100 := by
  have h : Real.log (1 / ((797:ℝ)/10000)) ≤ 253/100 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 10 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₀ = 1/10`, for the row `(0.12, 2.56)`. -/
private lemma t7Chain2 : (12/11 : ℝ) * Real.log (1 / ((10:ℝ)/100)) ≤ 256/100 := by
  have h : Real.log (1 / ((10:ℝ)/100)) ≤ 176/75 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 6 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₁ = 12/100`, for the row `(0.14, 2.39)`. -/
private lemma t7Chain3 : (12/11 : ℝ) * Real.log (1 / ((12:ℝ)/100)) ≤ 239/100 := by
  have h : Real.log (1 / ((12:ℝ)/100)) ≤ 2629/1200 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 6 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₂ = 14/100`, for the row `(0.16, 2.25)`. -/
private lemma t7Chain4 : (12/11 : ℝ) * Real.log (1 / ((14:ℝ)/100)) ≤ 225/100 := by
  have h : Real.log (1 / ((14:ℝ)/100)) ≤ 33/16 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 5 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₃ = 16/100`, for the row `(0.18, 2.12)`. -/
private lemma t7Chain5 : (12/11 : ℝ) * Real.log (1 / ((16:ℝ)/100)) ≤ 212/100 := by
  have h : Real.log (1 / ((16:ℝ)/100)) ≤ 583/300 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 5 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₄ = 18/100`, for the row `(0.20, 2.01)`. -/
private lemma t7Chain6 : (12/11 : ℝ) * Real.log (1 / ((18:ℝ)/100)) ≤ 201/100 := by
  have h : Real.log (1 / ((18:ℝ)/100)) ≤ 737/400 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 4 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₅ = 20/100`, for the row `(0.25, 1.77)`. -/
private lemma t7Chain7 : (12/11 : ℝ) * Real.log (1 / ((20:ℝ)/100)) ≤ 177/100 := by
  have h : Real.log (1 / ((20:ℝ)/100)) ≤ 649/400 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 6 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₆ = 25/100`, for the row `(0.30, 1.58)`. -/
private lemma t7Chain8 : (12/11 : ℝ) * Real.log (1 / ((25:ℝ)/100)) ≤ 158/100 := by
  have h : Real.log (1 / ((25:ℝ)/100)) ≤ 869/600 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 4 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₇ = 30/100`, for the row `(0.35, 1.42)`. -/
private lemma t7Chain9 : (12/11 : ℝ) * Real.log (1 / ((30:ℝ)/100)) ≤ 142/100 := by
  have h : Real.log (1 / ((30:ℝ)/100)) ≤ 781/600 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 4 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₈ = 35/100`, for the row `(0.40, 1.29)`. -/
private lemma t7Chain10 : (12/11 : ℝ) * Real.log (1 / ((35:ℝ)/100)) ≤ 129/100 := by
  have h : Real.log (1 / ((35:ℝ)/100)) ≤ 473/400 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 3 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₉ = 40/100`, for the row `(0.45, 1.18)`. -/
private lemma t7Chain11 : (12/11 : ℝ) * Real.log (1 / ((40:ℝ)/100)) ≤ 118/100 := by
  have h : Real.log (1 / ((40:ℝ)/100)) ≤ 649/600 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 3 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₁₀ = 45/100`, for the row `(0.50, 1.08)`. -/
private lemma t7Chain12 : (12/11 : ℝ) * Real.log (1 / ((45:ℝ)/100)) ≤ 108/100 := by
  have h : Real.log (1 / ((45:ℝ)/100)) ≤ 99/100 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 3 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₁₁ = 50/100`, for the row `(0.55, 1.00)`. -/
private lemma t7Chain13 : (12/11 : ℝ) * Real.log (1 / ((50:ℝ)/100)) ≤ 100/100 := by
  have h : Real.log (1 / ((50:ℝ)/100)) ≤ 11/12 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 3 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₁₂ = 55/100`, for the row `(0.60, 0.92)`. -/
private lemma t7Chain14 : (12/11 : ℝ) * Real.log (1 / ((55:ℝ)/100)) ≤ 92/100 := by
  have h : Real.log (1 / ((55:ℝ)/100)) ≤ 253/300 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 2 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₁₃ = 60/100`, for the row `(0.65, 0.85)`. -/
private lemma t7Chain15 : (12/11 : ℝ) * Real.log (1 / ((60:ℝ)/100)) ≤ 85/100 := by
  have h : Real.log (1 / ((60:ℝ)/100)) ≤ 187/240 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 2 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-- Chain condition at `L₁₄ = 65/100`, for the row `(0.70, 0.79)`. -/
private lemma t7Chain16 : (12/11 : ℝ) * Real.log (1 / ((65:ℝ)/100)) ≤ 79/100 := by
  have h : Real.log (1 / ((65:ℝ)/100)) ≤ 869/1200 :=
    log_le_of_partialSum_le (by norm_num) (by norm_num) 2 (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num)
  linarith

/-! ## Membership of the individual rows of Table 7

Each row of `tableR hbTable7` is exhibited as a member with its own lemma, so that the (somewhat
expensive) unfolding of the 17-element list happens once per row rather than once per branch of
the covering case analysis. -/

private lemma t7Mem1 : (((10:ℝ)/100), ((276:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem2 : (((12:ℝ)/100), ((256:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem3 : (((14:ℝ)/100), ((239:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem4 : (((16:ℝ)/100), ((225:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem5 : (((18:ℝ)/100), ((212:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem6 : (((20:ℝ)/100), ((201:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem7 : (((25:ℝ)/100), ((177:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem8 : (((30:ℝ)/100), ((158:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem9 : (((35:ℝ)/100), ((142:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem10 : (((40:ℝ)/100), ((129:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem11 : (((45:ℝ)/100), ((118:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem12 : (((50:ℝ)/100), ((108:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem13 : (((55:ℝ)/100), ((100:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem14 : (((60:ℝ)/100), ((92:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem15 : (((65:ℝ)/100), ((85:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]
private lemma t7Mem16 : (((70:ℝ)/100), ((79:ℝ)/100)) ∈ tableR hbTable7 := by norm_num [tableR, hbTable7]

/-! ## The covering step -/

/-- **The covering step.**  If `0 < bn ≤ λ₁` and `(12/11)·log(1/bn) ≤ c`, then
`(12/11)·log(1/λ₁) ≤ c`: indeed `1/λ₁ ≤ 1/bn` because `bn ≤ λ₁` and both are positive, and
`Real.log` is monotone on the positives. -/
private lemma t7Step {lam1 bn c : ℝ} (hbn : 0 < bn) (hlb : bn ≤ lam1)
    (hc : (12 / 11) * Real.log (1 / bn) ≤ c) :
    (12 / 11) * Real.log (1 / lam1) ≤ c := by
  have hpos : 0 < lam1 := lt_of_lt_of_le hbn hlb
  have hlog : Real.log (1 / lam1) ≤ Real.log (1 / bn) :=
    Real.log_le_log (one_div_pos.mpr hpos) (one_div_le_one_div_of_le hbn hlb)
  have h2 : (12 / 11) * Real.log (1 / lam1) ≤ (12 / 11) * Real.log (1 / bn) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  linarith

/-! ## The cover -/

theorem Table7RowCover (lam1 : ℝ) (h1 : 797 / 10000 ≤ lam1) (h2 : lam1 ≤ 696 / 1000) :
    ∃ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable7,
      lam1 ≤ p.1 ∧ (12 / 11) * Real.log (1 / lam1) ≤ p.2 := by
  -- the waterfall: row `k` is used when `L_{k-1} ≤ λ₁ ≤ L_k`
  by_cases hb1 : lam1 ≤ 10 / 100
  · exact ⟨((10:ℝ)/100, (276:ℝ)/100), t7Mem1, hb1, t7Step (by norm_num) h1 t7Chain1⟩
  by_cases hb2 : lam1 ≤ 12 / 100
  · exact ⟨((12:ℝ)/100, (256:ℝ)/100), t7Mem2, hb2,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb1)) t7Chain2⟩
  by_cases hb3 : lam1 ≤ 14 / 100
  · exact ⟨((14:ℝ)/100, (239:ℝ)/100), t7Mem3, hb3,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb2)) t7Chain3⟩
  by_cases hb4 : lam1 ≤ 16 / 100
  · exact ⟨((16:ℝ)/100, (225:ℝ)/100), t7Mem4, hb4,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb3)) t7Chain4⟩
  by_cases hb5 : lam1 ≤ 18 / 100
  · exact ⟨((18:ℝ)/100, (212:ℝ)/100), t7Mem5, hb5,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb4)) t7Chain5⟩
  by_cases hb6 : lam1 ≤ 20 / 100
  · exact ⟨((20:ℝ)/100, (201:ℝ)/100), t7Mem6, hb6,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb5)) t7Chain6⟩
  by_cases hb7 : lam1 ≤ 25 / 100
  · exact ⟨((25:ℝ)/100, (177:ℝ)/100), t7Mem7, hb7,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb6)) t7Chain7⟩
  by_cases hb8 : lam1 ≤ 30 / 100
  · exact ⟨((30:ℝ)/100, (158:ℝ)/100), t7Mem8, hb8,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb7)) t7Chain8⟩
  by_cases hb9 : lam1 ≤ 35 / 100
  · exact ⟨((35:ℝ)/100, (142:ℝ)/100), t7Mem9, hb9,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb8)) t7Chain9⟩
  by_cases hb10 : lam1 ≤ 40 / 100
  · exact ⟨((40:ℝ)/100, (129:ℝ)/100), t7Mem10, hb10,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb9)) t7Chain10⟩
  by_cases hb11 : lam1 ≤ 45 / 100
  · exact ⟨((45:ℝ)/100, (118:ℝ)/100), t7Mem11, hb11,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb10)) t7Chain11⟩
  by_cases hb12 : lam1 ≤ 50 / 100
  · exact ⟨((50:ℝ)/100, (108:ℝ)/100), t7Mem12, hb12,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb11)) t7Chain12⟩
  by_cases hb13 : lam1 ≤ 55 / 100
  · exact ⟨((55:ℝ)/100, (100:ℝ)/100), t7Mem13, hb13,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb12)) t7Chain13⟩
  by_cases hb14 : lam1 ≤ 60 / 100
  · exact ⟨((60:ℝ)/100, (92:ℝ)/100), t7Mem14, hb14,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb13)) t7Chain14⟩
  by_cases hb15 : lam1 ≤ 65 / 100
  · exact ⟨((65:ℝ)/100, (85:ℝ)/100), t7Mem15, hb15,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb14)) t7Chain15⟩
  -- `65/100 < λ₁ ≤ 696/1000 < 70/100`: the last row used is `(0.70, 0.79)`
  · exact ⟨((70:ℝ)/100, (79:ℝ)/100), t7Mem16, by linarith,
      t7Step (by norm_num) (le_of_lt (not_le.mp hb15)) t7Chain16⟩

end Work.ZeroFreeTables
