/-
# ZeroFreeTables — t23Gclosed

Infrastructure for the Tables 2/3 row certificates (`Work.ZeroFreeTables.t23cert_A` …).

Two tools are provided.

* `hb72G_closed`: the Laplace transform of HB Lemma 7.2's density
  `g(u) = (2-u)^3 (4+6u+u^2) = 32 - 40u^2 + 20u^3 - u^5` in closed form,

    `G x = ∫₀² g(u) e^{xu} du = (120 e^{2x} (x-1)^2 - 32x^5 + 80x^3 + 120x^2 - 120)/x^6`,

  so that the row data of Tables 2/3 (a rational evaluation of `G` at two nearby
  points) can be certified by rational arithmetic plus bounds on `e^{2x}`.

* `exp_bounds_quart`: two-sided rational Taylor bounds for `Real.exp` at a point
  `x ∈ [0,4]`, obtained from `Real.exp_bound` at `x/4` and the identity
  `exp x = (exp (x/4))⁴`.  The hypotheses are rational inequalities, so they are
  discharged by `norm_num [expErr, Finset.sum_range_succ]`.

## Recipe for a row `(λ, b, v)` of Tables 2 and 3

A row certificate is the single inequality

`(1/15)·(G (v/λ) − G ((v−b)/λ)) < 8/9 − (1/4 + 4·10⁻³)·(16λ/15)`.

Since `G x = (120 e^{2x} (x−1)² + P(x))/x⁶` with `P(x) = −32x⁵ + 80x³ + 120x² − 120`, and the
coefficient `120(x−1)²/x⁶` of `e^{2x}` is *positive* while that of `e^{2(x−b)/λ}` is negative,
it suffices to bound `e^{2v/λ}` **above** by a rational `hi1` and `e^{2(v−b)/λ}` **below** by a
rational `lo2`; the remaining inequality is then rational arithmetic.  In practice one takes
`hi1` (resp. `lo2`) to be `e^{2v/λ}` (resp. `e^{2(v−b)/λ}`) rounded up (resp. down) to 5 decimal
places — the margin of the rows is about `10⁻²`, so this is amply precise.  Concretely:

```
  -- write the two arguments of `hb72G` as fractions
  rw [show (3.244:ℝ)/2.3 = (3244:ℝ)/2300 by norm_num,
      show ((3.244:ℝ) - 0.2)/2.3 = (3044:ℝ)/2300 by norm_num]
  -- closed form of `G`
  rw [hb72G_closed (by norm_num : ((3244:ℝ)/2300) ≠ 0),
      hb72G_closed (by norm_num : ((3044:ℝ)/2300) ≠ 0)]
  -- normalise the exponents `2·(v/λ)`
  rw [show 2 * ((3244:ℝ)/2300) = (1622:ℝ)/575 by norm_num,
      show 2 * ((3044:ℝ)/2300) = (1522:ℝ)/575 by norm_num]
  -- two-sided bounds for the two exponentials
  obtain ⟨h1lo, h1hi⟩ := exp_bounds_quart (x := (1622:ℝ)/575) (lo := 16.79144) (hi := 16.79145)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨h2lo, h2hi⟩ := exp_bounds_quart (x := (1522:ℝ)/575) (lo := 14.11102) (hi := 14.11103)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  -- rational arithmetic
  norm_num
  linarith [h1hi, h2lo]
```

`t23cert_A_row1` below is exactly this for the first row of `rowA`.  The rows of `rowA` are
`(2.3, 0.2, 3.244)`, `(2.3, 0.198, 3.273)`, `(2.3, 0.195, 3.305)`, `(2.3, 0.192, 3.341)`,
`(2.3, 0.188, 3.382)`, `(2.3, 0.184, 3.428)`; note `λ = 2.3 = 23/10` throughout, so the
exponents `2v/λ` are `2·v·10/23`, and for the six rows the successful bounds are

| row | `v`   | `b`     | `2v/λ` | `hi1` | `2(v−b)/λ` | `lo2` |
|-----|-------|---------|---------|----------|-------|----------|
| 1 | 3.244 | 0.2   | 1622/575  | 16.79145 | 1522/575  | 14.11102 |
| 2 | 3.273 | 0.198 | 3273/1150 | 17.22027 | 123/46    | 14.49658 |
| 3 | 3.305 | 0.195 | 661/230   | 17.70617 | 311/115   | 14.94456 |
| 4 | 3.341 | 0.192 | 3341/1150 | 18.26922 | 3149/1150 | 15.46007 |
| 5 | 3.382 | 0.188 | 1691/575  | 18.93231 | 1597/575  | 16.07702 |
| 6 | 3.428 | 0.184 | 1714/575  | 19.70495 | 1622/575  | 16.79144 |
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.integral_pow_mul_exp

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## The closed form of `G x = ∫₀² g(u) e^{xu} du` -/

/-- The integral of `g(u)·e^{xu}` over `[0,2]` split into the four monomial integrals. -/
theorem hb72G_split (x : ℝ) :
    (∫ u in (0:ℝ)..2, hb72g u * Real.exp (x*u))
      = 32 * (∫ u in (0:ℝ)..2, u^0 * Real.exp (x*u))
        - 40 * (∫ u in (0:ℝ)..2, u^2 * Real.exp (x*u))
        + 20 * (∫ u in (0:ℝ)..2, u^3 * Real.exp (x*u))
        - (∫ u in (0:ℝ)..2, u^5 * Real.exp (x*u)) := by
  rw [show (fun u : ℝ => hb72g u * Real.exp (x*u)) = (fun u : ℝ =>
      32 * (u^0 * Real.exp (x*u)) - 40 * (u^2 * Real.exp (x*u))
        + 20 * (u^3 * Real.exp (x*u)) - (u^5 * Real.exp (x*u))) from by
    funext u; unfold hb72g; ring]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  all_goals try exact (by fun_prop : Continuous _).intervalIntegrable 0 2

/-- Closed form of `G x = ∫₀² g(u) e^{xu} du` for `x ≠ 0`. -/
theorem hb72G_closed {x : ℝ} (hx : x ≠ 0) :
    hb72G x = (120 * Real.exp (2*x) * (x-1)^2 - 32*x^5 + 80*x^3 + 120*x^2 - 120) / x^6 := by
  have hkey : 32 * (∫ u in (0:ℝ)..2, u^0 * Real.exp (x*u))
      - 40 * (∫ u in (0:ℝ)..2, u^2 * Real.exp (x*u))
      + 20 * (∫ u in (0:ℝ)..2, u^3 * Real.exp (x*u))
      - (∫ u in (0:ℝ)..2, u^5 * Real.exp (x*u))
      = (120 * Real.exp (2*x) * (x-1)^2 - 32*x^5 + 80*x^3 + 120*x^2 - 120) / x^6 := by
    rw [integral_pow_mul_exp 0 hx, integral_pow_mul_exp 2 hx, integral_pow_mul_exp 3 hx,
      integral_pow_mul_exp 5 hx]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    field_simp
    ring
  rw [hb72G, hb72G_split]
  exact hkey

/-! ## Two-sided rational Taylor bounds for `Real.exp` on `[0,4]` -/

/-- The Lagrange remainder bound for the 12-term Taylor polynomial of `Real.exp` at `x/4`:
`|x/4|^12 · 13/(12!·12)`. -/
def expErr (x : ℝ) : ℝ :=
  (x / 4) ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)))

/-- Two-sided rational bounds for `Real.exp x`, `0 ≤ x ≤ 4`, from the Taylor polynomial of
`exp` at `x/4` (12 terms, Lagrange remainder) and `exp x = (exp (x/4))⁴`. -/
theorem exp_bounds_quart {x lo hi : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4)
    (hlo : lo ≤ ((∑ m ∈ Finset.range 12, (x / 4) ^ m / (Nat.factorial m : ℝ)) - expErr x) ^ 4)
    (hhi : ((∑ m ∈ Finset.range 12, (x / 4) ^ m / (Nat.factorial m : ℝ)) + expErr x) ^ 4 ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have hb := Real.exp_bound (x := x/4) (n := 12)
    (by rw [abs_of_nonneg (by positivity)]; linarith) (by norm_num)
  have herr : |x/4| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)))
      = expErr x := by
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x/4)]
    rfl
  rw [herr] at hb
  have hS1 : (1:ℝ) ≤ ∑ m ∈ Finset.range 12, (x / 4) ^ m / (Nat.factorial m : ℝ) := by
    have h := Finset.single_le_sum (f := fun m : ℕ => (x/4)^m / (Nat.factorial m : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (by norm_num : (0:ℕ) < 12))
    simpa using h
  have herrle : expErr x ≤ 1/1000 := by
    have hpow : (x / 4) ^ 12 ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have hc : (Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)) ≤ 1/1000 := by norm_num
    have hc0 : (0:ℝ) ≤ (Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)) := by norm_num
    unfold expErr
    calc (x / 4) ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * ((12 : ℕ) : ℝ)))
        ≤ 1 * (1/1000) := mul_le_mul hpow hc hc0 (by norm_num)
      _ = 1/1000 := by norm_num
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hSp : 0 ≤ (∑ m ∈ Finset.range 12, (x / 4) ^ m / (Nat.factorial m : ℝ)) - expErr x := by
    linarith
  have h2 : (Real.exp (x/4))^4
      ≤ ((∑ m ∈ Finset.range 12, (x / 4) ^ m / (Nat.factorial m : ℝ)) + expErr x)^4 :=
    pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) 4
  have h1 : ((∑ m ∈ Finset.range 12, (x / 4) ^ m / (Nat.factorial m : ℝ)) - expErr x)^4
      ≤ (Real.exp (x/4))^4 :=
    pow_le_pow_left₀ hSp (by linarith) 4
  have hexp : Real.exp x = (Real.exp (x/4))^4 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  exact ⟨by rw [hexp]; exact le_trans hlo h1, by rw [hexp]; exact le_trans h2 hhi⟩



/-! ## Worked example: the first row of `rowA` -/

/-- Row `(λ, b, v) = (2.3, 0.2, 3.244)` of `rowA`, certified with
`e^{2·3.244/2.3} ≤ 16.79145` and `e^{2·3.044/2.3} ≥ 14.11102`. -/
theorem t23cert_A_row1 :
    (1 / 15) * (hb72G ((3.244:ℝ) / 2.3) - hb72G (((3.244:ℝ) - 0.2) / 2.3))
      < 8 / 9 - (1 / 4 + 4 * (1 / 4000)) * (16 * (2.3:ℝ) / 15) := by
  rw [show (3.244:ℝ)/2.3 = (3244:ℝ)/2300 by norm_num,
      show ((3.244:ℝ) - 0.2)/2.3 = (3044:ℝ)/2300 by norm_num]
  rw [hb72G_closed (by norm_num : ((3244:ℝ)/2300) ≠ 0),
      hb72G_closed (by norm_num : ((3044:ℝ)/2300) ≠ 0)]
  rw [show 2 * ((3244:ℝ)/2300) = (1622:ℝ)/575 by norm_num,
      show 2 * ((3044:ℝ)/2300) = (1522:ℝ)/575 by norm_num]
  obtain ⟨h1lo, h1hi⟩ := exp_bounds_quart (x := (1622:ℝ)/575) (lo := 16.79144) (hi := 16.79145)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨h2lo, h2hi⟩ := exp_bounds_quart (x := (1522:ℝ)/575) (lo := 14.11102) (hi := 14.11103)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [h1hi, h2lo]

end Work.ZeroFreeTables
