/-
# ZeroFreeTables — t23coverAux

Numeric aid lemmas for covering the ranges of `RowCover` (`t23Defs`) by the row data of
Tables 2/3, together with the description of the two covering chains (see the module comment at
the end of this file).

Every comparison in the two chains has the shape `k·log(1/c) ≤ v` with *rational* `c, v`, and is
reduced (via `Real.log_le_iff_le_exp`) to a rational inequality between a power of `1/c` and a
scaled Taylor polynomial of `Real.exp`:

* `two_log_inv_le`      : `2·log(1/c) ≤ v`       from  `(1/c)^2 ≤ (∑_{i<10} (v/8)^i/i!)^8`,
* `three_halves_log_inv_le` : `(3/2)·log(1/c) ≤ v` from  `(1/c)^3 ≤ (∑_{i<10} (v/4)^i/i!)^8`.

Both right-hand sides are decided by `norm_num [Finset.sum_range_succ]` alone.  The scaling by
`8` keeps the rational arithmetic small (numbers of a few hundred bits) while the relative error
of the Taylor polynomial is below `10⁻⁷`, far less than the `10⁻⁵` slack available in the chains.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- `Real.exp v` is at least a scaled Taylor polynomial raised to the scaling power. -/
theorem exp_ge_scaled (v : ℝ) (hv : 0 ≤ v) :
    (∑ i ∈ Finset.range 10, (v / 8) ^ i / ((i.factorial : ℕ) : ℝ)) ^ 8 ≤ Real.exp v := by
  have h : (∑ i ∈ Finset.range 10, (v / 8) ^ i / ((i.factorial : ℕ) : ℝ)) ≤ Real.exp (v / 8) :=
    Real.sum_le_exp_of_nonneg (by positivity) 10
  have h2 := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ ∑ i ∈ Finset.range 10, (v / 8) ^ i / ((i.factorial : ℕ) : ℝ)) h 8
  rw [show (Real.exp (v / 8)) ^ 8 = Real.exp v by rw [← Real.exp_nat_mul]; ring_nf] at h2
  exact h2

/-- `2 log (1/c) ≤ v` from the rational inequality `(1/c)² ≤ (∑_{i<10} (v/8)^i/i!)^8`. -/
theorem two_log_inv_le {c v : ℝ} (hc : 0 < c) (hv : 0 ≤ v)
    (h : (1 / c) ^ 2
      ≤ (∑ i ∈ Finset.range 10, (v / 8) ^ i / ((i.factorial : ℕ) : ℝ)) ^ 8) :
    2 * Real.log (1 / c) ≤ v := by
  have hlog : Real.log ((1 / c) ^ 2) ≤ v := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact h.trans (exp_ge_scaled v hv)
  have h3 : Real.log ((1 / c) ^ 2) = 2 * Real.log (1 / c) := Real.log_pow (1 / c) 2
  linarith

/-- `(3/2) log (1/c) ≤ v` from the rational inequality `(1/c)³ ≤ (∑_{i<10} (v/4)^i/i!)^8`. -/
theorem three_halves_log_inv_le {c v : ℝ} (hc : 0 < c) (hv : 0 ≤ v)
    (h : (1 / c) ^ 3
      ≤ (∑ i ∈ Finset.range 10, (v / 4) ^ i / ((i.factorial : ℕ) : ℝ)) ^ 8) :
    (3 / 2) * Real.log (1 / c) ≤ v := by
  have hbridge : (∑ i ∈ Finset.range 10, ((2 * v) / 8) ^ i / ((i.factorial : ℕ) : ℝ))
      = (∑ i ∈ Finset.range 10, (v / 4) ^ i / ((i.factorial : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (2 * v) / 8 = v / 4 by ring]
  have hlog : Real.log ((1 / c) ^ 3) ≤ 2 * v := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h2 := exp_ge_scaled (2 * v) (by linarith)
    rw [hbridge] at h2
    exact h.trans h2
  have h3 : Real.log ((1 / c) ^ 3) = 3 * Real.log (1 / c) := Real.log_pow (1 / c) 3
  linarith

/-- `log (1/x) ≤ log (1/c)` for `0 < c ≤ x`. -/
theorem log_inv_le_log_inv {c x : ℝ} (hc : 0 < c) (hcx : c ≤ x) :
    Real.log (1 / x) ≤ Real.log (1 / c) :=
  Real.log_le_log (by have h := lt_of_lt_of_le hc hcx; positivity)
    (one_div_le_one_div_of_le hc hcx)

/-- Transport of the `2 log` bound from the left endpoint `c` of a window to any `x ≥ c`. -/
theorem cover_min_log {c x v : ℝ} (hc : 0 < c) (hcx : c ≤ x)
    (hlog : 2 * Real.log (1 / c) ≤ v) : 2 * Real.log (1 / x) ≤ v := by
  linarith [log_inv_le_log_inv hc hcx]

/-- Transport of the `(3/2) log` bound from the left endpoint `c` of a window to any `x ≥ c`. -/
theorem cover_max_log {c x v : ℝ} (hc : 0 < c) (hcx : c ≤ x)
    (hlog : (3 / 2) * Real.log (1 / c) ≤ v) : (3 / 2) * Real.log (1 / x) ≤ v := by
  linarith [log_inv_le_log_inv hc hcx]

/-- `4·e ≤ v` for the rows with a large `v`. -/
theorem four_exp_one_le {v : ℝ} (h : (10.8732 : ℝ) ≤ v) : 4 * Real.exp 1 ≤ v := by
  have h1 := Real.exp_one_lt_d9
  linarith

/-! ## Membership in the row lists -/

theorem mem_t23_of_mem_rowA {p : ℝ × ℝ × ℝ} (h : p ∈ rowA) : p ∈ t23rows := by
  simp [t23rows, List.mem_append, h]

theorem mem_t23_of_mem_rowB {p : ℝ × ℝ × ℝ} (h : p ∈ rowB) : p ∈ t23rows := by
  simp [t23rows, List.mem_append, h]

theorem mem_t23_of_mem_rowC {p : ℝ × ℝ × ℝ} (h : p ∈ rowC) : p ∈ t23rows := by
  simp [t23rows, List.mem_append, h]

theorem mem_t23_of_mem_rowD {p : ℝ × ℝ × ℝ} (h : p ∈ rowD) : p ∈ t23rows := by
  simp [t23rows, List.mem_append, h]

theorem mem_t23_of_mem_rowE {p : ℝ × ℝ × ℝ} (h : p ∈ rowE) : p ∈ t23rows := by
  simp [t23rows, List.mem_append, h]

theorem mem_t23_of_mem_rowF {p : ℝ × ℝ × ℝ} (h : p ∈ rowF) : p ∈ t23rows := by
  simp [t23rows, List.mem_append, h]

/-!
## The two covering chains

`RowCover` has two conjuncts; each is proved by cutting the relevant `x`-range into consecutive
windows `[c, b]` and using, in each window, a single row `p = (λ, b, v)` of the tables whose `v`
dominates the required bound at the *left* endpoint `c` of the window:

* (first conjunct) `x ∈ (0, 1/5]`, bound `min (4·e) (2 log (1/x))`.  Either the row has
  `4·e ≤ v` (then no lower bound on `x` is needed), or `2 log (1/c) ≤ v`, so that
  `min (4e) (2 log (1/x)) ≤ 2 log (1/x) ≤ 2 log (1/c) ≤ v`.
* (second conjunct) `x ∈ [1/1000, 2/5]`, bound `max ((3/2) log (1/x)) (1294/1000)`; every row of
  the tables has `v ≥ 1.69 > 1294/1000`, so only `(3/2) log (1/c) ≤ v` matters.

The left endpoint `c` of a window is the `b`-value of the preceding row, so each step needs
`2 log (1/b_prev) ≤ v_new` (first conjunct) resp. `(3/2) log (1/b_prev) ≤ v_new` (second
conjunct).  The data of `t23rows`/`rowG` were designed exactly for these chains, so the chains
are essentially forced and their slacks can be as small as `10⁻⁵`; this is why one must use the
*exact* `norm_num` arithmetic of `two_log_inv_le`/`three_halves_log_inv_le` and not any rounded
decimal.

**Second conjunct.**  Every window's bound is `N(x) = max ((3/2)·log (1/x)) (1294/1000)`; the
rows used, in order (the first five lie in `t23rows`, the last four in `rowG`):

| window              | row `(λ, b, v)`          | comparison needed at the left end |
|---------------------|--------------------------|-----------------------------------|
| `[1/1000, 17/2500]` | `(113/40, 0.0068, 10.9)` | `(3/2)·log 1000 ≤ 10.9` |
| `[17/2500, 13/500]` | `(27/10, 0.026, 7.867)`  | `(3/2)·log (2500/17) ≤ 7.867` |
| `[13/500, 3/40]`    | `(51/20, 0.075, 5.491)`  | `(3/2)·log (500/13) ≤ 5.491` |
| `[3/40, 18/125]`    | `(12/5, 0.144, 4.001)`   | `(3/2)·log (40/3) ≤ 4.001` |
| `[18/125, 1/5]`     | `(23/10, 0.2, 3.244)`    | `(3/2)·log (125/18) ≤ 3.244` |
| `[1/5, 1/4]`        | `(9/4, 1/4, 2.73)`       | `(3/2)·log 5 ≤ 2.73` |
| `[1/4, 3/10]`       | `(43/20, 3/10, 2.33)`    | `(3/2)·log 4 ≤ 2.33` |
| `[3/10, 7/20]`      | `(21/10, 7/20, 1.99)`    | `(3/2)·log (10/3) ≤ 1.99` |
| `[7/20, 2/5]`       | `(41/20, 2/5, 1.69)`     | `(3/2)·log (20/7) ≤ 1.69` |

All nine comparisons hold with room to spare and are instances of `three_halves_log_inv_le`
followed by `norm_num [Finset.sum_range_succ]`; e.g.

```lean
example : (3 / 2) * Real.log (1 / (1 / 1000 : ℝ)) ≤ (10.9 : ℝ) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]
```

and the windows are used through `cover_max_log`, so that in the window `[c, b]` with row
`p = (λ, b, v)` the conclusion `p.2.2 = v` follows from `x ≥ c`; the second component
`1294/1000 ≤ v` is a `norm_num` fact about the row.

**First conjunct** (for reference; proved in `t23cover.lean`).  The two rows with `4·e ≤ v` are
`(113/40, 0.0068, 10.9)` and `(2.8, 0.006, 11.071)`, so the window `(0, 17/2500]` needs no lower
bound at all; from `17/2500` on, the chain of `b`-values
`51/5000, 29/2000, 1/50, 13/500, 2649/100000, 7/200, 11/250, 27/500, 8/125, 3211/50000, 3/40,
7503/100000, 43/500, 97/1000, 107/1000, 2141/20000, 117/1000, 11701/100000, 63/500, 3161/25000,
27/200, 13527/100000, 18/125, 151/1000, 3777/25000, 79/500, 15803/100000, 41/250, 411/2500,
17/100, 17017/100000, 7/40, 2193/12500, 9/50, 3603/20000, 23/125, 9217/50000, 47/250, 588/3125,
24/125, 39/200, 99/500, 1/5` covers the rest, each row's `v` satisfying `2 log (1/b_prev) ≤ v`.
-/

end Work.ZeroFreeTables
