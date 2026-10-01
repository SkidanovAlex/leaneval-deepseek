/-
# ZeroFreeTables — TentRowAux

Generic machinery for certifying the rows `tentRows` of HB88's tent table
(`TentRowCerts`).

A row `(X, b, c)` carries the sharp certificate

`b·e^{Xc}·((Xc - 2) + (Xc + 2)·e^{-Xc}) < X·(X/2 - A₀)·c³`,  `A₀ = 11/24 + 4·10⁻⁴`,

i.e. `TentRowCert (X, b, c)`.  Two observations reduce this to rational arithmetic:

* the exact identity `e^{Xc}·((Xc - 2) + (Xc + 2)·e^{-Xc}) = e^{Xc}·(Xc - 2) + (Xc + 2)`
  (`Real.exp_neg` + `field_simp`), so only an *upper* bound on `e^{Xc}` is needed;
* an upper bound on `e^{Xc}` comes from the twelve-term Taylor bound `Real.exp_bound'` at
  `Xc/16 ≤ 1`, raised to the 8th power (`Real.exp_nat_mul`) and then squared.

The result is `TentRowCert_of_poly`: given the single rational bound
`B ≥ ∑_{m<12} (Xc/16)^m/m! + (Xc/16)^12·13/(12!·12)` and the fully rational inequality
`b·(B¹⁶·(Xc - 2) + (Xc + 2)) < X·(X/2 - A₀)·c³`, the row certificate follows.  Both side
conditions are closed by `norm_num` once `X`, `b`, `c`, `B` are numerals, so each row of the
table is a one-line application.

## Recipe for a row

For a row `(X, b, c)` of `Work.ZeroFreeTables.tentRows` the constant `B = n/10^12` tabulated
below satisfies `∑_{m<12}(Xc/16)^m/m! + (Xc/16)^12·13/(12!·12) ≤ B`, and the rational
inequality `b·(B¹⁶·(Xc - 2) + (Xc + 2)) < X·(X/2 - A₀)·c³` holds.  The certificate is then

```
theorem tentRowXX : TentRowCert ((X : ℝ), (bn : ℝ)/10^9, (cn : ℝ)/1000) := by
  refine TentRowCert_of_poly (X : ℝ) ((bn : ℝ)/10^9) ((cn : ℝ)/1000) ((n : ℝ)/10^12)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [A₀])
```

Table `i | X | b·10⁹ | c·10³ | n = B·10¹²` (rows in the order of `tentRows`):

```
 1 | 6/5   |   79700000 |  2840 | 1237384651244
 2 | 6/5   |   74094301 |  2932 | 1245952129145
 3 | 6/5   |   68101912 |  3038 | 1255896926764
 4 | 6/5   |   61795999 |  3157 | 1267155975604
 5 | 23/20 |   55409734 |  3292 | 1266950079487
 6 | 23/20 |   48960081 |  3447 | 1281143610821
 7 | 23/20 |   42475267 |  3624 | 1297546274791
 8 | 23/20 |   36113688 |  3824 | 1316333210077
 9 | 23/20 |   30064306 |  4047 | 1337601553827
10 | 11/10 |   24506098 |  4294 | 1343411803365
11 | 11/10 |   19540814 |  4577 | 1369805487729
12 | 11/10 |   15075767 |  4897 | 1400275145765
13 | 11/10 |   11243108 |  5253 | 1434969722951
14 | 11/10 |    8112629 |  5644 | 1474066635494
15 | 21/20 |    5668958 |  6075 | 1489844683110
16 | 21/20 |    3818746 |  6559 | 1537925414833
17 | 21/20 |    2450410 |  7095 | 1592984618182
18 | 21/20 |    1499186 |  7680 | 1655329363158
19 | 21/20 |     876931 |  8310 | 1725201318413
20 | 21/20 |     492221 |  8980 | 1802748599598
21 | 1     |     266337 |  9714 | 1835147757385
22 | 1     |     135902 | 10514 | 1929237794918
23 | 1     |      65275 | 11377 | 2036153522860
24 | 1     |      29593 | 12297 | 2156663820206
25 | 1     |      12733 | 13269 | 2291742625486
26 | 1     |       5224 | 14287 | 2442293361194
27 | 1     |       2055 | 15344 | 2609086082369
```
-/

import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentIf

open scoped Real BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- `Real.exp s = (Real.exp (s/2))^2`. -/
lemma exp_eq_sq_half (s : ℝ) : Real.exp s = Real.exp (s / 2) ^ 2 := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Upper Taylor bound for `Real.exp` on `[0, 8]`: twelve terms at `q/8`, raised to the 8th
power.  (Self-contained; the same estimate as `T7Cert.exp_upper`.) -/
lemma exp_half_upper (q B : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 8)
    (h : (∑ m ∈ Finset.range 12, (q/8)^m/(Nat.factorial m : ℝ))
        + (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)) ≤ B) :
    Real.exp q ≤ B ^ 8 := by
  have hb := Real.exp_bound' (x := q/8) (show (0:ℝ) ≤ q/8 by positivity)
    (show q/8 ≤ 1 by linarith) (n := 12) (by norm_num)
  have hB0 : 0 ≤ (∑ m ∈ Finset.range 12, (q/8)^m/(Nat.factorial m : ℝ))
      + (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)) := by positivity
  have h3 : Real.exp (q/8) ≤ (∑ m ∈ Finset.range 12, (q/8)^m/(Nat.factorial m : ℝ))
      + (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)) := by
    simpa only [Nat.cast_ofNat] using hb
  have h2 : Real.exp q = Real.exp (q/8)^8 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h2]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le h3 8) (pow_le_pow_left₀ hB0 h 8)

/-- **The master reduction.**  If the twelve-term Taylor estimate for `exp (X·c/16)` is bounded
by `B`, and the corresponding fully rational inequality holds, then `(X, b, c)` satisfies the
sharp row certificate. -/
lemma TentRowCert_of_poly (X b c B : ℝ) (hb0 : 0 ≤ b) (hs2 : 2 ≤ X * c) (hs16 : X * c ≤ 16)
    (hpoly : (∑ m ∈ Finset.range 12, ((X * c / 2)/8)^m/(Nat.factorial m : ℝ))
        + ((X * c / 2)/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)) ≤ B)
    (hmain : b * (B ^ 16 * (X * c - 2) + (X * c + 2)) < X * (X / 2 - A₀) * c ^ 3) :
    TentRowCert (X, b, c) := by
  have hq0 : 0 ≤ X * c / 2 := by linarith
  have hq8 : X * c / 2 ≤ 8 := by linarith
  have h1 : Real.exp (X * c / 2) ≤ B ^ 8 := exp_half_upper (X * c / 2) B hq0 hq8 hpoly
  have hE : Real.exp (X * c) ≤ B ^ 16 := by
    rw [exp_eq_sq_half (X * c)]
    calc Real.exp (X * c / 2) ^ 2 ≤ (B ^ 8) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le h1 2
      _ = B ^ 16 := by ring
  have hkey : Real.exp (X * c) * ((X * c - 2) + (X * c + 2) * Real.exp (-(X * c)))
      = Real.exp (X * c) * (X * c - 2) + (X * c + 2) := by
    rw [Real.exp_neg]
    field_simp
  have hinner : Real.exp (X * c) * (X * c - 2) + (X * c + 2)
      ≤ B ^ 16 * (X * c - 2) + (X * c + 2) := by
    have h1' : Real.exp (X * c) * (X * c - 2) ≤ B ^ 16 * (X * c - 2) :=
      mul_le_mul_of_nonneg_right hE (by linarith)
    linarith
  change b * Real.exp (X * c) * ((X * c - 2) + (X * c + 2) * Real.exp (-(X * c)))
      < X * (X / 2 - A₀) * c ^ 3
  rw [mul_assoc, hkey]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hinner hb0) hmain

end Work.ZeroFreeTables
