/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise bound on the angular polynomials `Bᵢ`

This file proves `Work.FTS.Nonlinear.Pieces.RNP26.Bang_bound`:

  `|Bang i x α| ≤ 10^6 * (α + 4x(1-x))`  for `x ∈ [0,1]`, `0 < α ≤ 1`, `1 ≤ i ≤ 4`.

The polynomials `Bang i · α` split as

  `Bang i x α = 4x(1-x)·V_i(x) + ∑_{k=1}^{i} (α/3)^k·P_{i,k}(x)`

(`V_i` and the `P_{i,k}` are the explicit polynomials of `BangDefs`).  The estimate is
therefore purely elementary:

* every coefficient of every `V_i`, `P_{i,k}` is `< 10^5` in absolute value and every degree
  is `≤ 5`, so `|V_i(x)| ≤ 6·10^5` and `|P_{i,k}(x)| ≤ 6·10^5` for `x ∈ [0,1]`
  (lemma `abs_poly6_le`: `|∑ a_j x^j| ≤ ∑ |a_j| ≤ 6·10^5`);
* consequently `|4x(1-x)V_i(x)| ≤ 10^6·4x(1-x)` (`abs_four_mul_le`), using `4x(1-x) ≥ 0`;
* and, since `0 < α ≤ 1` and `k ≥ 1`, `(α/3)^k ≤ α/3`, so each `α`-term contributes at most
  `(α/3)·6·10^5 = 2·10^5·α` (`abs_rpow3_mul_le`), and there are at most four of them.

The numerical constants are extremely generous (`10^6` against coefficient sums of at most
`1.4·10^5`), which is why no sharp cancellation is needed anywhere.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.Nonlinear.Pieces.RNP26.BangDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.Nonlinear.Pieces.RNP26

set_option autoImplicit false

/-- **Polynomial bound.**  A polynomial of degree `≤ 5` all of whose coefficients are at most
`10^5` in absolute value is bounded by `6·10^5` on `[0,1]`. -/
private lemma abs_poly6_le (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (a0 a1 a2 a3 a4 a5 : ℝ)
    (h0 : |a0| ≤ 10 ^ 5) (h1 : |a1| ≤ 10 ^ 5) (h2 : |a2| ≤ 10 ^ 5)
    (h3 : |a3| ≤ 10 ^ 5) (h4 : |a4| ≤ 10 ^ 5) (h5 : |a5| ≤ 10 ^ 5) :
    |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 + a5 * x ^ 5| ≤ 6 * 10 ^ 5 := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hxa : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hp : ∀ k : ℕ, |x ^ k| ≤ 1 := by
    intro k
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hxa
  have e1 : |a1 * x| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a1| * |x| ≤ 10 ^ 5 * 1 := mul_le_mul h1 hxa (abs_nonneg x) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have e2 : |a2 * x ^ 2| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a2| * |x ^ 2| ≤ 10 ^ 5 * 1 := mul_le_mul h2 (hp 2) (abs_nonneg _) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have e3 : |a3 * x ^ 3| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a3| * |x ^ 3| ≤ 10 ^ 5 * 1 := mul_le_mul h3 (hp 3) (abs_nonneg _) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have e4 : |a4 * x ^ 4| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a4| * |x ^ 4| ≤ 10 ^ 5 * 1 := mul_le_mul h4 (hp 4) (abs_nonneg _) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have e5 : |a5 * x ^ 5| ≤ 10 ^ 5 := by
    rw [abs_mul]
    calc |a5| * |x ^ 5| ≤ 10 ^ 5 * 1 := mul_le_mul h5 (hp 5) (abs_nonneg _) (by norm_num)
      _ = 10 ^ 5 := by norm_num
  have s1 := abs_add_le a0 (a1 * x)
  have s2 := abs_add_le (a0 + a1 * x) (a2 * x ^ 2)
  have s3 := abs_add_le (a0 + a1 * x + a2 * x ^ 2) (a3 * x ^ 3)
  have s4 := abs_add_le (a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3) (a4 * x ^ 4)
  have s5 := abs_add_le (a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4) (a5 * x ^ 5)
  have hsplit : |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 + a5 * x ^ 5|
      ≤ |a0| + |a1 * x| + |a2 * x ^ 2| + |a3 * x ^ 3| + |a4 * x ^ 4| + |a5 * x ^ 5| := by
    linarith
  linarith

/-- The contribution of the `k = 0` part `4x(1-x)·V`: since `4x(1-x) ≥ 0` on `[0,1]`,
`|4x(1-x)V| = 4x(1-x)|V| ≤ 4x(1-x)·6·10^5 ≤ 10^6·4x(1-x)`. -/
private lemma abs_four_mul_le (x V : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hV : |V| ≤ 6 * 10 ^ 5) :
    |4 * x * (1 - x) * V| ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith [hx.1, hx.2]
  rw [abs_mul, abs_of_nonneg h4]
  calc 4 * x * (1 - x) * |V| ≤ 4 * x * (1 - x) * (6 * 10 ^ 5) :=
        mul_le_mul_of_nonneg_left hV h4
    _ ≤ 4 * x * (1 - x) * 10 ^ 6 := mul_le_mul_of_nonneg_left (by norm_num) h4
    _ = 10 ^ 6 * (4 * x * (1 - x)) := by ring

/-- The contribution of one `α`-term: for `0 < α ≤ 1` and `k ≥ 1` one has `(α/3)^k ≤ α/3`,
whence `|(α/3)^k·P| ≤ (α/3)·6·10^5 = 2·10^5·α` whenever `|P| ≤ 6·10^5`. -/
private lemma abs_rpow3_mul_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (hk : 1 ≤ k)
    (P : ℝ) (hP : |P| ≤ 6 * 10 ^ 5) : |(α / 3) ^ k * P| ≤ (α / 3) * (6 * 10 ^ 5) := by
  have ht0 : 0 ≤ α / 3 := by linarith
  have ht1 : α / 3 ≤ 1 := by linarith
  have hpow : (α / 3) ^ k ≤ α / 3 := by
    have := pow_le_pow_of_le_one ht0 ht1 hk
    simpa using this
  rw [abs_mul, abs_pow, abs_of_nonneg ht0]
  exact mul_le_mul hpow hP (abs_nonneg P) ht0

/-- `|a + b + c| ≤ |a| + |b| + |c|`. -/
private lemma abs_sum3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  linarith

/-- `|a + b + c + d| ≤ |a| + |b| + |c| + |d|`. -/
private lemma abs_sum4_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  linarith

/-- `|a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e|`. -/
private lemma abs_sum5_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  linarith

/-- **Bound on the angular polynomials `Bᵢ`.**  For `1 ≤ i ≤ 4`, `x ∈ [0,1]` and
`0 < α ≤ 1`,
  `|Bᵢ(x,α)| ≤ 10^6 (α + 4x(1-x))`.

Proof by the four cases `i = 1,2,3,4`: split `Bang i x α` into its `4x(1-x)·Vᵢ` part and its
(at most four) `(α/3)^k·P_{i,k}` parts, bound the `k = 0` part with `abs_four_mul_le` and each
`α`-part with `abs_rpow3_mul_le` (the polynomial bounds `|Vᵢ|, |P_{i,k}| ≤ 6·10^5` come from
`abs_poly6_le` and `norm_num` on the coefficients), and add up. -/
theorem Bang_bound (i : ℕ) (hi1 : 1 ≤ i) (hi4 : i ≤ 4) (x α : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Work.FTS.Nonlinear.Pieces.RNP26.Bang i x α| ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by
  interval_cases i
  · rw [Work.FTS.Nonlinear.Pieces.RNP26.Bang_one]
    have hA : |4 * x * (1 - x) * 1| ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
      have hV : |(1 : ℝ)| ≤ 6 * 10 ^ 5 := by norm_num
      exact abs_four_mul_le x 1 hx hV
    have hB : |(α / 3) * (-4 + 10 * x - 6 * x ^ 2)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-4 : ℝ) + 10 * x - 6 * x ^ 2| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx (-4) 10 (-6) 0 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 1 (le_refl 1) ((-4 : ℝ) + 10 * x - 6 * x ^ 2) hP
      rw [pow_one] at hk
      linarith
    calc |4 * x * (1 - x) * 1 + (α / 3) * (-4 + 10 * x - 6 * x ^ 2)|
        ≤ |4 * x * (1 - x) * 1| + |(α / 3) * (-4 + 10 * x - 6 * x ^ 2)| := abs_add_le _ _
      _ ≤ 10 ^ 6 * (4 * x * (1 - x)) + 2 * 10 ^ 5 * α := add_le_add hA hB
      _ ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by nlinarith [hα.le]
  · rw [Work.FTS.Nonlinear.Pieces.RNP26.Bang_two]
    have hA : |4 * x * (1 - x) * (-4 + 8 * x)| ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
      have hV : |(-4 : ℝ) + 8 * x| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx (-4) 8 0 0 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        simpa using h
      exact abs_four_mul_le x (-4 + 8 * x) hx hV
    have hB1 : |(α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-56 : ℝ) * x + 128 * x ^ 2 - 72 * x ^ 3| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 (-56) 128 (-72) 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 1 (le_refl 1)
        ((-56 : ℝ) * x + 128 * x ^ 2 - 72 * x ^ 3) hP
      rw [pow_one] at hk
      linarith
    have hB2 : |(α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(16 : ℝ) - 64 * x + 84 * x ^ 2 - 36 * x ^ 3| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 16 (-64) 84 (-36) 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 2 (by norm_num)
        ((16 : ℝ) - 64 * x + 84 * x ^ 2 - 36 * x ^ 3) hP
      linarith
    calc |4 * x * (1 - x) * (-4 + 8 * x) + (α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)
            + (α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3)|
        ≤ |4 * x * (1 - x) * (-4 + 8 * x)| + |(α / 3) * (-56 * x + 128 * x ^ 2 - 72 * x ^ 3)|
            + |(α / 3) ^ 2 * (16 - 64 * x + 84 * x ^ 2 - 36 * x ^ 3)| := abs_sum3_le _ _ _
      _ ≤ 10 ^ 6 * (4 * x * (1 - x)) + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α :=
          add_le_add (add_le_add hA hB1) hB2
      _ ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by nlinarith [hα.le]
  · rw [Work.FTS.Nonlinear.Pieces.RNP26.Bang_three]
    have hA : |4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)|
        ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
      have hV : |(16 : ℝ) - 96 * x + 96 * x ^ 2| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 16 (-96) 96 0 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      exact abs_four_mul_le x (16 - 96 * x + 96 * x ^ 2) hx hV
    have hB1 : |(α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)|
        ≤ 2 * 10 ^ 5 * α := by
      have hP : |(288 : ℝ) * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4|
          ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 288 (-1536) 2304 (-1056) 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 1 (le_refl 1)
        ((288 : ℝ) * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4) hP
      rw [pow_one] at hk
      linarith
    have hB2 : |(α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)|
        ≤ 2 * 10 ^ 5 * α := by
      have hP : |(480 : ℝ) * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4|
          ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 480 (-1776) 2160 (-864) 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 2 (by norm_num)
        ((480 : ℝ) * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4) hP
      linarith
    have hB3 : |(α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4)|
        ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-64 : ℝ) + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4|
          ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx (-64) 352 (-720) 648 (-216) 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 3 (by norm_num)
        ((-64 : ℝ) + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4) hP
      linarith
    calc |4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)
            + (α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)
            + (α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)
            + (α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4)|
        ≤ |4 * x * (1 - x) * (16 - 96 * x + 96 * x ^ 2)|
            + |(α / 3) * (288 * x - 1536 * x ^ 2 + 2304 * x ^ 3 - 1056 * x ^ 4)|
            + |(α / 3) ^ 2 * (480 * x - 1776 * x ^ 2 + 2160 * x ^ 3 - 864 * x ^ 4)|
            + |(α / 3) ^ 3 * (-64 + 352 * x - 720 * x ^ 2 + 648 * x ^ 3 - 216 * x ^ 4)| :=
          abs_sum4_le _ _ _ _
      _ ≤ 10 ^ 6 * (4 * x * (1 - x)) + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α :=
          add_le_add (add_le_add (add_le_add hA hB1) hB2) hB3
      _ ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by nlinarith [hα.le]
  · rw [Work.FTS.Nonlinear.Pieces.RNP26.Bang_four]
    have hA : |4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)|
        ≤ 10 ^ 6 * (4 * x * (1 - x)) := by
      have hV : |(-64 : ℝ) + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx (-64) 896 (-2304) 1536 0 0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      exact abs_four_mul_le x (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3) hx hV
    have hB1 : |(α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4
          - 19200 * x ^ 5)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-1408 : ℝ) * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4
          - 19200 * x ^ 5| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 (-1408) 15616 (-45696) 50688 (-19200)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 1 (le_refl 1)
        ((-1408 : ℝ) * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4 - 19200 * x ^ 5) hP
      rw [pow_one] at hk
      linarith
    have hB2 : |(α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4
          - 20160 * x ^ 5)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-3072 : ℝ) * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4
          - 20160 * x ^ 5| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 (-3072) 24000 (-58560) 57792 (-20160)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 2 (by norm_num)
        ((-3072 : ℝ) * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4 - 20160 * x ^ 5) hP
      linarith
    have hB3 : |(α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4
          - 8640 * x ^ 5)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(-3328 : ℝ) * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4
          - 8640 * x ^ 5| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 0 (-3328) 17152 (-32832) 27648 (-8640)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 3 (by norm_num)
        ((-3328 : ℝ) * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4 - 8640 * x ^ 5) hP
      linarith
    have hB4 : |(α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
          - 1296 * x ^ 5)| ≤ 2 * 10 ^ 5 * α := by
      have hP : |(256 : ℝ) - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
          - 1296 * x ^ 5| ≤ 6 * 10 ^ 5 := by
        have h := abs_poly6_le x hx 256 (-1792) 4992 (-6912) 4752 (-1296)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        convert h using 2 <;> ring
      have hk := abs_rpow3_mul_le α hα hα1 4 (by norm_num)
        ((256 : ℝ) - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4 - 1296 * x ^ 5) hP
      linarith
    calc |4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)
            + (α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4
                - 19200 * x ^ 5)
            + (α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4
                - 20160 * x ^ 5)
            + (α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4
                - 8640 * x ^ 5)
            + (α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
                - 1296 * x ^ 5)|
        ≤ |4 * x * (1 - x) * (-64 + 896 * x - 2304 * x ^ 2 + 1536 * x ^ 3)|
            + |(α / 3) * (-1408 * x + 15616 * x ^ 2 - 45696 * x ^ 3 + 50688 * x ^ 4
                - 19200 * x ^ 5)|
            + |(α / 3) ^ 2 * (-3072 * x + 24000 * x ^ 2 - 58560 * x ^ 3 + 57792 * x ^ 4
                - 20160 * x ^ 5)|
            + |(α / 3) ^ 3 * (-3328 * x + 17152 * x ^ 2 - 32832 * x ^ 3 + 27648 * x ^ 4
                - 8640 * x ^ 5)|
            + |(α / 3) ^ 4 * (256 - 1792 * x + 4992 * x ^ 2 - 6912 * x ^ 3 + 4752 * x ^ 4
                - 1296 * x ^ 5)| :=
          abs_sum5_le _ _ _ _ _
      _ ≤ 10 ^ 6 * (4 * x * (1 - x)) + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α + 2 * 10 ^ 5 * α
            + 2 * 10 ^ 5 * α :=
          add_le_add (add_le_add (add_le_add (add_le_add hA hB1) hB2) hB3) hB4
      _ ≤ 10 ^ 6 * (α + 4 * x * (1 - x)) := by nlinarith [hα.le]

end Work.FTS.Nonlinear.Pieces.RNP26
