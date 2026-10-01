/-
# ZeroFreeTables — t23ExpBounds

Shared infrastructure for the row certificates of Tables 2 and 3
(`Work.ZeroFreeTables.t23RowA` … `t23RowF`, assembled as `Work.ZeroFreeTables.t23cert`).

## What the row certificates are

Every row `(λ, b, v)` of `rowA … rowF` (or `rowG`) must certify

`(1/15)·(G (v/λ) − G ((v−b)/λ)) < 8/9 − CertSlack·(16λ/15)`,  `CertSlack = 1/4 + 1/500000 + 4/1000`,

where `G x = ∫₀² g(u)e^{xu}du` (`hb72G`).  By `t23Gclosed.hb72G_closed`,

`G x = (120·e^{2x}·(x−1)² − 32x⁵ + 80x³ + 120x² − 120)/x⁶  (x ≠ 0)`,

and since `x > 1` on the row data, the coefficient `120·(x−1)²/x⁶` of `e^{2x}` is **positive**.
Hence an upper bound for the expression follows from an **upper** bound `hi1` for `e^{2(v/λ)}`
and a **lower** bound `lo2` for `e^{2((v−b)/λ)}`.

## Recipe (copy the shape of the two worked examples below)

For a row `(λ, b, v)` (all from the lists in `t23Defs`):

```
  rw [show (v:ℝ) / (λ:ℝ) = (p:ℝ)/q by norm_num,                -- the two arguments of hb72G
      show ((v:ℝ) - (b:ℝ)) / (λ:ℝ) = (p':ℝ)/q' by norm_num]
  rw [hb72G_closed (by norm_num : ((p:ℝ)/q) ≠ 0),
      hb72G_closed (by norm_num : ((p':ℝ)/q') ≠ 0)]
  rw [show 2 * ((p:ℝ)/q) = (r:ℝ)/s by norm_num,               -- the exponents, as ONE rational
      show 2 * ((p':ℝ)/q') = (r':ℝ)/s' by norm_num]
  -- bounds for the exponentials (numbers from the table below)
  obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := (r:ℝ)/s) (lo := ..) (hi := <hi1>)
      (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := (r':ℝ)/s') (lo := <lo2>) (hi := ..)
      (by norm_num) (by norm_num)
      (by norm_num [expErr, Finset.sum_range_succ]) (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [h1hi, h2lo]
```

When `2v/λ > 4` the row is a **split** row: `exp_bounds_quart` is applied to `2v/λ − 4`
(valid: `2v/λ ≤ 8`), and the bridge `exp_le_of_quart_sub` / `le_exp_of_quart_sub` converts
the bound on `e^(2v/λ−4)` into one on `e^(2v/λ)` using `e⁴ ≤ 54.5981501` (`exp4_le`) resp.
`54.5981500 ≤ e⁴` (`le_exp4`):

```
  obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (r:ℝ)/s - 4) (lo := ..) (hi := <hi1'>) ...
  have h1hi : Real.exp ((r:ℝ)/s) ≤ (<hi1>:ℝ) :=
    exp_le_of_quart_sub (by norm_num) h1quart (by norm_num)
```

The `hi1`/`lo2` in the table below are five-decimal rationals chosen so that
`exp_bounds_quart`'s rational hypotheses are discharged by `norm_num`, and so that the final
numerical inequality closes with `linarith`.  For a split row, `<hi1'>` (resp. `<lo2'>`) is the
quart bound on `2v/λ − 4` and `<hi1>` (resp. `<lo2>`) the final bound on `2v/λ`.

## The numbers (five-decimal roundings; all 40 rows verified by exact rational arithmetic)

| batch | row | λ | b | v | 2v/λ | kind | hi1 (or hi1') | hi1 final | 2(v−b)/λ | kind | lo2 (or lo2') | lo2 final |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| rowA | 1 | 2.3 | 0.2 | 3.244 | 2.820870 | quart | 16.79145 |  | 2.646957 | quart | 14.11102 |  |
| rowA | 2 | 2.3 | 0.198 | 3.273 | 2.846087 | quart | 17.22027 |  | 2.673913 | quart | 14.49658 |  |
| rowA | 3 | 2.3 | 0.195 | 3.305 | 2.873913 | quart | 17.70617 |  | 2.704348 | quart | 14.94456 |  |
| rowA | 4 | 2.3 | 0.192 | 3.341 | 2.905217 | quart | 18.26922 |  | 2.738261 | quart | 15.46007 |  |
| rowA | 5 | 2.3 | 0.188 | 3.382 | 2.940870 | quart | 18.93231 |  | 2.777391 | quart | 16.07702 |  |
| rowA | 6 | 2.3 | 0.184 | 3.428 | 2.980870 | quart | 19.70495 |  | 2.820870 | quart | 16.79144 |  |
| rowB | 1 | 2.35 | 0.18 | 3.481 | 2.962553 | quart | 19.34731 |  | 2.809362 | quart | 16.59931 |  |
| rowB | 2 | 2.35 | 0.175 | 3.542 | 3.014468 | quart | 20.37825 |  | 2.865532 | quart | 17.55839 |  |
| rowB | 3 | 2.35 | 0.17 | 3.611 | 3.073191 | quart | 21.61077 |  | 2.928511 | quart | 18.69975 |  |
| rowB | 4 | 2.35 | 0.164 | 3.69 | 3.140426 | quart | 23.11371 |  | 3.000851 | quart | 20.10263 |  |
| rowB | 5 | 2.35 | 0.158 | 3.78 | 3.217021 | quart | 24.95368 |  | 3.082553 | quart | 21.81402 |  |
| rowB | 6 | 2.4 | 0.151 | 3.883 | 3.235833 | quart | 25.42756 |  | 3.110000 | quart | 22.42104 |  |
| rowC | 1 | 2.4 | 0.144 | 4.001 | 3.334167 | quart | 28.055 |  | 3.214167 | quart | 24.88254 |  |
| rowC | 2 | 2.4 | 0.135 | 4.136 | 3.446667 | quart | 31.39557 |  | 3.334167 | quart | 28.05499 |  |
| rowC | 3 | 2.4 | 0.126 | 4.291 | 3.575833 | quart | 35.72438 |  | 3.470833 | quart | 32.16353 |  |
| rowC | 4 | 2.45 | 0.117 | 4.469 | 3.648163 | quart | 38.40407 |  | 3.552653 | quart | 34.9058 |  |
| rowC | 5 | 2.45 | 0.107 | 4.674 | 3.815510 | quart | 45.39992 |  | 3.728163 | quart | 41.60262 |  |
| rowC | 6 | 2.5 | 0.097 | 4.909 | 3.927200 | quart | 50.76464 |  | 3.849600 | quart | 46.97426 |  |
| rowD | 1 | 2.5 | 0.086 | 5.18 | 4.144000 | split | 1.15489 | 63.05486 | 4.075200 | split | 1.07809 | 58.86171 |
| rowD | 2 | 2.55 | 0.075 | 5.491 | 4.306667 | split | 1.35889 | 74.19289 | 4.247843 | split | 1.28125 | 69.95387 |
| rowD | 3 | 2.55 | 0.064 | 5.849 | 4.587451 | split | 1.7994 | 98.24392 | 4.537255 | split | 1.7113 | 93.43381 |
| rowD | 4 | 2.6 | 0.054 | 6.259 | 4.814615 | split | 2.25831 | 123.29955 | 4.773077 | split | 2.16642 | 118.28252 |
| rowD | 5 | 2.6 | 0.044 | 6.728 | 5.175385 | split | 3.23939 | 176.86471 | 5.141538 | split | 3.13158 | 170.97847 |
| rowD | 6 | 2.65 | 0.035 | 7.262 | 5.480755 | split | 4.39627 | 240.02821 | 5.454340 | split | 4.28165 | 233.77016 |
| rowE | 1 | 2.7 | 0.026 | 7.867 | 5.827407 | split | 6.21775 | 339.47765 | 5.808148 | split | 6.09914 | 333.00176 |
| rowE | 2 | 2.7 | 0.02 | 8.5 | 6.296296 | split | 9.93731 | 542.55875 | 6.281481 | split | 9.79117 | 534.57976 |
| rowE | 3 | 2.745 | 0.0145 | 9.24 | 6.732240 | split | 15.36728 | 839.02507 | 6.721676 | split | 15.20578 | 830.20745 |
| rowE | 4 | 2.78 | 0.0102 | 10 | 7.194245 | split | 24.39175 | 1331.74443 | 7.186906 | split | 24.2134 | 1322.00684 |
| rowE | 5 | 2.825 | 0.0068 | 10.9 | 7.716814 | split | 41.13315 | 2245.7939 | 7.712000 | split | 40.93559 | 2235.00748 |
| rowE | 6 | 2.8 | 0.006 | 11.071 | 7.907857 | split | 49.79215 | 2718.55928 | 7.903571 | split | 49.5792 | 2706.93259 |
| rowF | 1 | 2.3 | 0.18816 | 3.346 | 2.909565 | quart | 18.34882 |  | 2.745948 | quart | 15.57937 |  |
| rowF | 2 | 2.3 | 0.18434 | 3.389 | 2.946957 | quart | 19.0479 |  | 2.786661 | quart | 16.22674 |  |
| rowF | 3 | 2.35 | 0.18015 | 3.433 | 2.921702 | quart | 18.57288 |  | 2.768383 | quart | 15.93284 |  |
| rowF | 4 | 2.35 | 0.17544 | 3.489 | 2.969362 | quart | 19.47949 |  | 2.820051 | quart | 16.7777 |  |
| rowF | 5 | 2.35 | 0.17017 | 3.547 | 3.018723 | quart | 20.46515 |  | 2.873898 | quart | 17.70589 |  |
| rowF | 6 | 2.35 | 0.1644 | 3.619 | 3.080000 | quart | 21.75841 |  | 2.940085 | quart | 18.91745 |  |
| rowF | 7 | 2.35 | 0.15803 | 3.694 | 3.143830 | quart | 23.19252 |  | 3.009336 | quart | 20.27393 |  |
| rowF | 8 | 2.4 | 0.15108 | 3.784 | 3.153333 | quart | 23.41399 |  | 3.027433 | quart | 20.64417 |  |
| rowF | 9 | 2.4 | 0.13527 | 4.008 | 3.340000 | quart | 28.21913 |  | 3.227275 | quart | 25.21086 |  |
| rowF | 10 | 2.4 | 0.12644 | 4.146 | 3.455000 | quart | 31.65829 |  | 3.349633 | quart | 28.49228 |  |
| rowF | 11 | 2.45 | 0.11701 | 4.295 | 3.506122 | quart | 33.31883 |  | 3.410604 | quart | 30.28353 |  |
| rowF | 12 | 2.45 | 0.10705 | 4.473 | 3.651429 | quart | 38.52967 |  | 3.564041 | quart | 35.30557 |  |
| rowF | 13 | 2.55 | 0.07503 | 5.184 | 4.065882 | split | 1.06811 | 58.31684 | 4.007035 | split | 1.00706 | 54.98361 |
| rowF | 14 | 2.55 | 0.06422 | 5.501 | 4.314510 | split | 1.36959 | 74.77709 | 4.264141 | split | 1.30231 | 71.10371 |
| rowF | 15 | 2.7 | 0.02649 | 7.303 | 5.409630 | split | 4.09444 | 223.54885 | 5.390007 | split | 4.01487 | 219.20447 |
| rowF | 16 | 2.8 | 0.00626 | 10.235 | 7.310714 | split | 27.4047 | 1496.24593 | 7.306243 | split | 27.28242 | 1489.56965 |
-/

import Mathlib
import Submission.Work.ZeroFreeTables.t23Gclosed

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## Two-sided rational bounds for `e⁴` -/

/-- `e⁴ ≤ 54.5981501`. -/
theorem exp4_le : Real.exp 4 ≤ (54.5981501 : ℝ) := by
  have h : Real.exp 4 = (Real.exp 1) ^ 4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h]
  calc (Real.exp 1)^4 ≤ (2.7182818286:ℝ)^4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_d9) 4
    _ ≤ 54.5981501 := by norm_num

/-- `54.5981500 ≤ e⁴`. -/
theorem le_exp4 : (54.5981500 : ℝ) ≤ Real.exp 4 := by
  have h : Real.exp 4 = (Real.exp 1) ^ 4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h]
  calc (54.5981500:ℝ) ≤ (2.7182818283:ℝ)^4 := by norm_num
    _ ≤ (Real.exp 1)^4 := pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 4

/-! ## Splitting off `e⁴`: bounds on `[0,8]` from bounds on `[0,4]` -/

/-- Upper bound for `e^y`, `4 ≤ y`, from an upper bound for `e^(y−4)`. -/
theorem exp_le_of_quart_sub {y hi' hi : ℝ} (h' : Real.exp (y - 4) ≤ hi')
    (h : 54.5981501 * hi' ≤ hi) : Real.exp y ≤ hi := by
  have he : Real.exp y = Real.exp 4 * Real.exp (y - 4) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  have hi'0 : 0 ≤ hi' := le_trans (Real.exp_pos _).le h'
  exact le_trans (mul_le_mul exp4_le h' (Real.exp_pos _).le (by norm_num)) h

/-- Lower bound for `e^y`, `4 ≤ y`, from a lower bound for `e^(y−4)`. -/
theorem le_exp_of_quart_sub {y lo' lo : ℝ} (h' : lo' ≤ Real.exp (y - 4))
    (hlo' : 0 ≤ lo') (h : lo ≤ 54.5981500 * lo') : lo ≤ Real.exp y := by
  have he : Real.exp y = Real.exp 4 * Real.exp (y - 4) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  exact le_trans h (mul_le_mul le_exp4 h' hlo' (Real.exp_pos 4).le)

end Work.ZeroFreeTables
