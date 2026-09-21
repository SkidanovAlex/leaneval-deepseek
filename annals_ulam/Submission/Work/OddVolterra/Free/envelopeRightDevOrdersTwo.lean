import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddVolterra.Free.envelopeLeft_gap_dev_orders_two
import Submission.Work.OddCurve.LowSlope.radial_derivs_le_of_profile

/-!
# The right-branch deviation at orders `k ≤ 2`

`Work.OddVolterra.Free.envelopeRightDevOrdersTwo`: for a chord curve `c` which is `C²`-close
(error `η ≤ 1/100`) to `profileX` on the slope window `[7/10, 1]` and a bump `p` whose first three
jets at `σ ∈ [7/10, 1]` are bounded by `ε`, the right branch `envelopeRight p c` of the envelope
profile and the semicircle differ, at the point `c σ` and at orders `k ≤ 2`, by at most
`C (η + ε)`.

The proof decomposes both sides along the slope variable.  Writing
`A τ = τ * c τ + p τ`, `B τ = τ * profileX τ` and `D = A - B`, the right branch is
`envelopeRight p c (c σ) = A σ`, and the chain rule/inverse-function rules give

  `(envelopeRight p c)'(c σ) = A' σ / c' σ`,
  `(envelopeRight p c)''(c σ) = (A''σ c'σ - A'σ c''σ)/(c'σ)³`,

while on the semicircle side `B σ = semicircle (profileX σ)`, `B'σ / profileX'σ =
semicircle' (profileX σ)` and `(B''σ profileX'σ - B'σ profileX''σ)/(profileX'σ)³ =
semicircle''(profileX σ)`.  Since `A^{(k)} = B^{(k)} + D^{(k)}` and the derivatives of `D` are
bounded by `η + ε` (they are `σ(c-φ) + p`, `(c-φ) + σ(c'-φ') + p'` and
`2(c'-φ') + σ(c''-φ'') + p''` up to the elementary identities
`profileX τ + τ profileX'τ = profileX τ³` and
`2 profileX'τ² - profileX τ profileX''τ = profileX τ⁶`), the three estimates reduce to
elementary real inequalities involving the lower bounds `1/4 ≤ |c'σ|`, `4/15 ≤ |profileX'σ|`
and the Lipschitz bounds for the semicircle and its first two derivatives on `[1/2, 9/10]`.
-/

namespace Work.OddVolterra.Free

open Set Filter
open scoped Topology ContDiff

noncomputable section

set_option maxHeartbeats 8000000

namespace RightDevAux

/-! ## Elementary bounds for the semicircle on `[1/2, 9/10]` -/

/-- `√(1-t²) ≥ 43/100` on `[1/2, 9/10]`. -/
lemma semicircle_ge_43 {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) (9 / 10)) :
    (43 : ℝ) / 100 ≤ Work.OddEnvelope.semicircle t := by
  have h1 : t ^ 2 ≤ 81 / 100 := by nlinarith [ht.1, ht.2]
  have h2 : 0 ≤ 1 - t ^ 2 := by nlinarith
  rw [Work.OddEnvelope.semicircle, Real.le_sqrt (by norm_num) h2]
  nlinarith

/-- `√(1-t²) ≤ 1` on `[1/2, 9/10]`. -/
lemma semicircle_le_one {t : ℝ} (_ht : t ∈ Set.Icc (1 / 2 : ℝ) (9 / 10)) :
    Work.OddEnvelope.semicircle t ≤ 1 := by
  rw [Work.OddEnvelope.semicircle, Real.sqrt_le_one]
  nlinarith [sq_nonneg t]

/-- **Lipschitz bound for the semicircle** on `[1/2, 9/10]`. -/
lemma semicircle_lipschitz {x y : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10))
    (hy : y ∈ Set.Icc (1 / 2 : ℝ) (9 / 10)) :
    |Work.OddEnvelope.semicircle x - Work.OddEnvelope.semicircle y| ≤ 3 * |x - y| := by
  have hpx : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hpy : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hsx := semicircle_ge_43 hx
  have hsy := semicircle_ge_43 hy
  have hpos : 0 < Work.OddEnvelope.semicircle x + Work.OddEnvelope.semicircle y := by linarith
  have hfac : (Work.OddEnvelope.semicircle x - Work.OddEnvelope.semicircle y)
      * (Work.OddEnvelope.semicircle x + Work.OddEnvelope.semicircle y) = y ^ 2 - x ^ 2 := by
    have e1 : Work.OddEnvelope.semicircle x ^ 2 = 1 - x ^ 2 := by
      rw [Work.OddEnvelope.semicircle]; exact Real.sq_sqrt hpx
    have e2 : Work.OddEnvelope.semicircle y ^ 2 = 1 - y ^ 2 := by
      rw [Work.OddEnvelope.semicircle]; exact Real.sq_sqrt hpy
    calc (Work.OddEnvelope.semicircle x - Work.OddEnvelope.semicircle y)
          * (Work.OddEnvelope.semicircle x + Work.OddEnvelope.semicircle y)
        = Work.OddEnvelope.semicircle x ^ 2 - Work.OddEnvelope.semicircle y ^ 2 := by ring
      _ = (1 - x ^ 2) - (1 - y ^ 2) := by rw [e1, e2]
      _ = y ^ 2 - x ^ 2 := by ring
  have hkey : Work.OddEnvelope.semicircle x - Work.OddEnvelope.semicircle y
      = (y ^ 2 - x ^ 2) / (Work.OddEnvelope.semicircle x + Work.OddEnvelope.semicircle y) := by
    rw [eq_div_iff (ne_of_gt hpos)]
    exact hfac
  rw [hkey, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hdiff : |y ^ 2 - x ^ 2| ≤ 9 / 5 * |x - y| := by
    have hfac2 : y ^ 2 - x ^ 2 = (y - x) * (y + x) := by ring
    rw [hfac2, abs_mul, abs_sub_comm y x]
    have hxy : |y + x| ≤ 9 / 5 := by
      rw [abs_le]
      constructor <;> [linarith [hx.1, hy.1]; linarith [hx.2, hy.2]]
    have := mul_le_mul_of_nonneg_left hxy (abs_nonneg (x - y))
    linarith [this]
  have hsum : (86 : ℝ) / 100 ≤ Work.OddEnvelope.semicircle x + Work.OddEnvelope.semicircle y := by
    linarith
  -- 9/5 ≤ 3 * (86/100)
  have hstep : (9 / 5 : ℝ) * |x - y| ≤ (3 * ((86 : ℝ) / 100)) * |x - y| :=
    mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
  have hstep2 : (3 * ((86 : ℝ) / 100)) * |x - y|
      ≤ 3 * |x - y| * (Work.OddEnvelope.semicircle x + Work.OddEnvelope.semicircle y) := by
    calc (3 * ((86 : ℝ) / 100)) * |x - y| = 3 * |x - y| * ((86 : ℝ) / 100) := by ring
      _ ≤ 3 * |x - y| * (Work.OddEnvelope.semicircle x + Work.OddEnvelope.semicircle y) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  linarith [hdiff, hstep, hstep2]

/-- **Lipschitz bound for the first derivative of the semicircle** on `[1/2, 9/10]`. -/
lemma semicircle_deriv_lipschitz {x y : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10))
    (hy : y ∈ Set.Icc (1 / 2 : ℝ) (9 / 10)) :
    |deriv Work.OddEnvelope.semicircle x - deriv Work.OddEnvelope.semicircle y|
      ≤ 25 * |x - y| := by
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [Work.OddEnvelope.Semicircle.deriv_semicircle hxI,
    Work.OddEnvelope.Semicircle.deriv_semicircle hyI]
  have hpx : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hpy : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hsx := semicircle_ge_43 hx
  have hsy := semicircle_ge_43 hy
  have hsx0 : 0 < Work.OddEnvelope.semicircle x := by linarith
  have hsy0 : 0 < Work.OddEnvelope.semicircle y := by linarith
  have hfac : (y * Work.OddEnvelope.semicircle x - x * Work.OddEnvelope.semicircle y)
      * (y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y)
        = y ^ 2 - x ^ 2 := by
    have e1 : Work.OddEnvelope.semicircle x ^ 2 = 1 - x ^ 2 := by
      rw [Work.OddEnvelope.semicircle]; exact Real.sq_sqrt hpx
    have e2 : Work.OddEnvelope.semicircle y ^ 2 = 1 - y ^ 2 := by
      rw [Work.OddEnvelope.semicircle]; exact Real.sq_sqrt hpy
    calc (y * Work.OddEnvelope.semicircle x - x * Work.OddEnvelope.semicircle y)
          * (y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y)
        = y ^ 2 * Work.OddEnvelope.semicircle x ^ 2
            - x ^ 2 * Work.OddEnvelope.semicircle y ^ 2 := by ring
      _ = y ^ 2 * (1 - x ^ 2) - x ^ 2 * (1 - y ^ 2) := by rw [e1, e2]
      _ = y ^ 2 - x ^ 2 := by ring
  have hsum : (43 : ℝ) / 100
      ≤ y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y := by
    have h1 : (1 / 2 : ℝ) * (43 / 100) ≤ y * Work.OddEnvelope.semicircle x :=
      mul_le_mul hy.1 hsx (by norm_num) (by linarith [hy.1])
    have h2 : (1 / 2 : ℝ) * (43 / 100) ≤ x * Work.OddEnvelope.semicircle y :=
      mul_le_mul hx.1 hsy (by norm_num) (by linarith [hx.1])
    linarith
  have hsumpos : 0 < y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y := by
    linarith
  have hkey : (-x) / Work.OddEnvelope.semicircle x - (-y) / Work.OddEnvelope.semicircle y
      = (y * Work.OddEnvelope.semicircle x - x * Work.OddEnvelope.semicircle y)
        / (Work.OddEnvelope.semicircle x * Work.OddEnvelope.semicircle y) := by
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos (mul_pos hsx0 hsy0), div_le_iff₀ (mul_pos hsx0 hsy0)]
  -- the numerator
  have hnum : |y * Work.OddEnvelope.semicircle x - x * Work.OddEnvelope.semicircle y|
      ≤ (9 / 5) * (100 / 43) * |x - y| := by
    have hdiv : y * Work.OddEnvelope.semicircle x - x * Work.OddEnvelope.semicircle y
        = (y ^ 2 - x ^ 2)
          / (y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y) := by
      rw [eq_div_iff (ne_of_gt hsumpos)]
      exact hfac
    rw [hdiv, abs_div, abs_of_pos hsumpos, div_le_iff₀ hsumpos]
    have hsq : |y ^ 2 - x ^ 2| ≤ 9 / 5 * |x - y| := by
      have hfac2 : y ^ 2 - x ^ 2 = (x - y) * (-(y + x)) := by ring
      rw [hfac2, abs_mul, abs_neg]
      have hxy : |y + x| ≤ 9 / 5 := by
        rw [abs_le]
        constructor <;> [linarith [hx.1, hy.1]; linarith [hx.2, hy.2]]
      have := mul_le_mul_of_nonneg_left hxy (abs_nonneg (x - y))
      linarith [this]
    have h3 : (9 / 5 : ℝ) * |x - y| ≤ (9 / 5 * (100 / 43) * |x - y|)
        * (y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y) := by
      have h1 : (1 : ℝ) ≤ (100 / 43)
          * (y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y) := by
        nlinarith [hsum]
      calc (9 / 5 : ℝ) * |x - y| ≤ (9 / 5 : ℝ) * |x - y| * (100 / 43)
            * (y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y) := by
            nlinarith [abs_nonneg (x - y), h1]
        _ = (9 / 5 * (100 / 43) * |x - y|)
            * (y * Work.OddEnvelope.semicircle x + x * Work.OddEnvelope.semicircle y) := by ring
    linarith [hsq, h3]
  have hden : ((43 : ℝ) / 100) * (43 / 100) ≤ Work.OddEnvelope.semicircle x
      * Work.OddEnvelope.semicircle y :=
    mul_le_mul hsx hsy (by norm_num) (le_of_lt hsx0)
  have hstep : (9 / 5 * (100 / 43) : ℝ) * |x - y| ≤ (25 * ((43 : ℝ) / 100 * (43 / 100))) * |x - y| :=
    mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
  have hstep2 : (25 * ((43 : ℝ) / 100 * (43 / 100))) * |x - y|
      ≤ 25 * |x - y| * (Work.OddEnvelope.semicircle x * Work.OddEnvelope.semicircle y) := by
    calc (25 * ((43 : ℝ) / 100 * (43 / 100))) * |x - y|
        = 25 * |x - y| * ((43 : ℝ) / 100 * (43 / 100)) := by ring
      _ ≤ 25 * |x - y| * (Work.OddEnvelope.semicircle x * Work.OddEnvelope.semicircle y) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  linarith [hnum, hstep, hstep2]

/-- Reciprocal-cube differences: `|1/p³ - 1/q³| ≤ 500 |p - q|` for `p,q ∈ [43/100, 1]`. -/
lemma abs_inv_cube_sub_le' {p q : ℝ} (hp : 43 / 100 ≤ p) (hp1 : p ≤ 1)
    (hq : 43 / 100 ≤ q) (hq1 : q ≤ 1) :
    |1 / p ^ 3 - 1 / q ^ 3| ≤ 500 * |p - q| := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hden : 0 < p ^ 3 * q ^ 3 := mul_pos (pow_pos hp0 3) (pow_pos hq0 3)
  have hkey : 1 / p ^ 3 - 1 / q ^ 3 = (q ^ 3 - p ^ 3) / (p ^ 3 * q ^ 3) := by
    field_simp
  rw [hkey, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hcube : |q ^ 3 - p ^ 3| ≤ 3 * |p - q| := by
    have h := LeftGapAux.abs_cube_sub_cube_le (x := q) (y := p)
      (by rw [abs_of_pos hq0]; exact hq1) (by rw [abs_of_pos hp0]; exact hp1)
    rw [abs_sub_comm q p] at h
    exact h
  have hden' : (1 : ℝ) / 160 ≤ p ^ 3 * q ^ 3 := by
    have h1 : ((43 : ℝ) / 100) ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (by norm_num) hp 3
    have h2 : ((43 : ℝ) / 100) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq 3
    nlinarith [h1, h2]
  have hstep : (3 : ℝ) * |p - q| ≤ 500 * |p - q| * (p ^ 3 * q ^ 3) := by
    have h1 : (3 : ℝ) ≤ 500 * (p ^ 3 * q ^ 3) := by nlinarith [hden']
    calc (3 : ℝ) * |p - q| ≤ (500 * (p ^ 3 * q ^ 3)) * |p - q| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = 500 * |p - q| * (p ^ 3 * q ^ 3) := by ring
  linarith [hcube, hstep]

/-- **Lipschitz bound for the second derivative of the semicircle** on `[1/2, 9/10]`. -/
lemma semicircle_deriv2_lipschitz {x y : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10))
    (hy : y ∈ Set.Icc (1 / 2 : ℝ) (9 / 10)) :
    |deriv (deriv Work.OddEnvelope.semicircle) x
        - deriv (deriv Work.OddEnvelope.semicircle) y| ≤ 2000 * |x - y| := by
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [LeftGapAux.deriv_deriv_semicircle hxI, LeftGapAux.deriv_deriv_semicircle hyI]
  have hsx := semicircle_ge_43 hx
  have hsy := semicircle_ge_43 hy
  have hsx1 := semicircle_le_one hx
  have hsy1 := semicircle_le_one hy
  have h1 : |1 / Work.OddEnvelope.semicircle x ^ 3 - 1 / Work.OddEnvelope.semicircle y ^ 3|
      ≤ 500 * |Work.OddEnvelope.semicircle x - Work.OddEnvelope.semicircle y| :=
    abs_inv_cube_sub_le' hsx hsx1 hsy hsy1
  have h2 : |Work.OddEnvelope.semicircle x - Work.OddEnvelope.semicircle y| ≤ 3 * |x - y| :=
    semicircle_lipschitz hx hy
  have h3 : |-(1 / Work.OddEnvelope.semicircle x ^ 3)
      - -(1 / Work.OddEnvelope.semicircle y ^ 3)|
      = |1 / Work.OddEnvelope.semicircle x ^ 3 - 1 / Work.OddEnvelope.semicircle y ^ 3| := by
    rw [show -(1 / Work.OddEnvelope.semicircle x ^ 3)
        - -(1 / Work.OddEnvelope.semicircle y ^ 3)
        = -(1 / Work.OddEnvelope.semicircle x ^ 3 - 1 / Work.OddEnvelope.semicircle y ^ 3)
      from by ring, abs_neg]
  rw [h3]
  have h4 : 500 * (3 * |x - y|) ≤ 2000 * |x - y| := by
    have := mul_le_mul_of_nonneg_left (show (3 : ℝ) * |x - y| ≤ 4 * |x - y| from by
      nlinarith [abs_nonneg (x - y)]) (by norm_num : (0 : ℝ) ≤ 500)
    linarith [this]
  linarith [h1, h2, h4]

/-- Reciprocal-cube differences for `a, b` with `|a|,|b| ∈ [1/4, 3/2]`. -/
lemma abs_inv_cube_sub_le_general {a b : ℝ} (ha : 1 / 4 ≤ |a|) (ha' : |a| ≤ 3 / 2)
    (hb : 1 / 4 ≤ |b|) (hb' : |b| ≤ 3 / 2) :
    |1 / a ^ 3 - 1 / b ^ 3| ≤ 30000 * |a - b| := by
  have ha0 : 0 < |a| := by linarith
  have hb0 : 0 < |b| := by linarith
  have han : a ≠ 0 := abs_pos.mp ha0
  have hbn : b ≠ 0 := abs_pos.mp hb0
  have hden : 0 < |a| ^ 3 * |b| ^ 3 := mul_pos (pow_pos ha0 3) (pow_pos hb0 3)
  have hkey : 1 / a ^ 3 - 1 / b ^ 3 = (b ^ 3 - a ^ 3) / (a ^ 3 * b ^ 3) := by
    field_simp
  rw [hkey, abs_div, abs_mul, abs_pow, abs_pow, div_le_iff₀ hden]
  have hcube : |b ^ 3 - a ^ 3| ≤ 7 * |a - b| := by
    have hfac : b ^ 3 - a ^ 3 = (b - a) * (b ^ 2 + b * a + a ^ 2) := by ring
    rw [hfac, abs_mul, abs_sub_comm b a]
    have hq : |b ^ 2 + b * a + a ^ 2| ≤ 7 := by
      have hb2 : |b ^ 2| ≤ 9 / 4 := by
        rw [abs_of_nonneg (sq_nonneg b)]
        nlinarith [abs_le.mp hb']
      have ha2 : |a ^ 2| ≤ 9 / 4 := by
        rw [abs_of_nonneg (sq_nonneg a)]
        nlinarith [abs_le.mp ha']
      have hba : |b * a| ≤ 9 / 4 := by
        rw [abs_mul]
        nlinarith [abs_le.mp ha', abs_le.mp hb', abs_nonneg a, abs_nonneg b]
      have h4 : |b ^ 2 + b * a + a ^ 2| ≤ |b ^ 2| + |b * a| + |a ^ 2| := by
        have h5 := abs_add_le (b ^ 2) (b * a)
        have h6 := abs_add_le (b ^ 2 + b * a) (a ^ 2)
        linarith [h5, h6, abs_nonneg (b ^ 2 + b * a)]
      linarith [hb2, ha2, hba, h4]
    have := mul_le_mul_of_nonneg_left hq (abs_nonneg (a - b))
    linarith [this]
  have hden' : (1 : ℝ) / 4096 ≤ |a| ^ 3 * |b| ^ 3 := by
    have h1 : ((1 : ℝ) / 4) ^ 3 ≤ |a| ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
    have h2 : ((1 : ℝ) / 4) ^ 3 ≤ |b| ^ 3 := pow_le_pow_left₀ (by norm_num) hb 3
    nlinarith [h1, h2]
  have hstep : 7 * |a - b| ≤ 30000 * |a - b| * (|a| ^ 3 * |b| ^ 3) := by
    have h1 : (7 : ℝ) ≤ 30000 * (|a| ^ 3 * |b| ^ 3) := by nlinarith [hden']
    calc 7 * |a - b| ≤ (30000 * (|a| ^ 3 * |b| ^ 3)) * |a - b| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = 30000 * |a - b| * (|a| ^ 3 * |b| ^ 3) := by ring
  linarith [hcube, hstep]

/-- `|a+b+c+d+e+f| ≤ |a|+|b|+|c|+|d|+|e|+|f|`. -/
lemma abs_le_sum_six (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  have h5 := abs_add_le (a + b + c + d + e) f
  linarith [h1, h2, h3, h4, h5, abs_nonneg (a + b), abs_nonneg (a + b + c),
    abs_nonneg (a + b + c + d), abs_nonneg (a + b + c + d + e)]

/-- **Order `0`.** -/
lemma dev_zero {σ u u₀ w η ε : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 1) (hη0 : 0 ≤ η)
    (hε0 : 0 ≤ ε) (hη : |u - u₀| ≤ η) (hw : |w| ≤ ε)
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) (9 / 10)) (hu₀ : u₀ ∈ Set.Icc (1 / 2 : ℝ) (9 / 10))
    (hsemi : Work.OddEnvelope.semicircle u₀ = σ * u₀) :
    |σ * u + w - Work.OddEnvelope.semicircle u| ≤ 4 * (η + ε) := by
  have he : σ * u + w - Work.OddEnvelope.semicircle u
      = σ * (u - u₀) + (Work.OddEnvelope.semicircle u₀ - Work.OddEnvelope.semicircle u) + w := by
    rw [hsemi]; ring
  rw [he]
  have h1 : |σ * (u - u₀)| ≤ η := by
    rw [abs_mul, abs_of_nonneg hσ0]
    calc σ * |u - u₀| ≤ 1 * η := mul_le_mul hσ2 hη (abs_nonneg _) (by norm_num)
      _ = η := by ring
  have h2 : |Work.OddEnvelope.semicircle u₀ - Work.OddEnvelope.semicircle u| ≤ 3 * η := by
    rw [abs_sub_comm]
    calc |Work.OddEnvelope.semicircle u - Work.OddEnvelope.semicircle u₀|
        ≤ 3 * |u - u₀| := semicircle_lipschitz hu hu₀
      _ ≤ 3 * η := mul_le_mul_of_nonneg_left hη (by norm_num)
  have h3 := abs_add_le (σ * (u - u₀)
    + (Work.OddEnvelope.semicircle u₀ - Work.OddEnvelope.semicircle u)) w
  have h4 := abs_add_le (σ * (u - u₀))
    (Work.OddEnvelope.semicircle u₀ - Work.OddEnvelope.semicircle u)
  linarith [h1, h2, h3, h4, hw, hη0, hε0]

/-- **Order `1`.** -/
lemma dev_one {σ u u₀ v v₀ w₁ η ε : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 1) (hη0 : 0 ≤ η)
    (hε0 : 0 ≤ ε) (hη : |u - u₀| ≤ η) (hη₁ : |v - v₀| ≤ η) (hw₁ : |w₁| ≤ ε)
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) (9 / 10)) (hu₀ : u₀ ∈ Set.Icc (1 / 2 : ℝ) (9 / 10))
    (hu₀pos : 0 < u₀) (hu₀le1 : u₀ ≤ 1) (hv : 1 / 4 ≤ |v|) (hv₀ : 4 / 15 ≤ |v₀|)
    (hv₀hi : |v₀| ≤ 1) (hB' : u₀ + σ * v₀ = u₀ ^ 3) (hN : u₀ + σ * v₀ = -v₀ / σ)
    (hsemi : Work.OddEnvelope.semicircle u₀ = σ * u₀) :
    |(u + σ * v + w₁) / v - (-u / Work.OddEnvelope.semicircle u)| ≤ 100 * (η + ε) := by
  have hvne : v ≠ 0 := by intro h; rw [h, abs_zero] at hv; norm_num at hv
  have hv₀ne : v₀ ≠ 0 := by intro h; rw [h, abs_zero] at hv₀; norm_num at hv₀
  have huI' : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hu₀I' : u₀ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu₀.1], by linarith [hu₀.2]⟩
  have hB'abs : |u₀ + σ * v₀| ≤ 1 := by
    rw [hB', abs_of_nonneg (pow_nonneg (le_of_lt hu₀pos) 3)]
    exact pow_le_one₀ (le_of_lt hu₀pos) hu₀le1
  have hmid : (u₀ + σ * v₀) / v₀ = -u₀ / Work.OddEnvelope.semicircle u₀ := by
    rw [hN, hsemi]
    field_simp
  let D : ℝ := (u - u₀) + σ * (v - v₀) + w₁
  have hDbound : |D| ≤ 2 * η + ε := by
    have h1 := abs_add_le ((u - u₀) + σ * (v - v₀)) w₁
    have h2 := abs_add_le (u - u₀) (σ * (v - v₀))
    have h3 : |σ * (v - v₀)| ≤ η := by
      rw [abs_mul, abs_of_pos hσ0]
      calc σ * |v - v₀| ≤ 1 * η := mul_le_mul hσ2 hη₁ (abs_nonneg _) (by norm_num)
        _ = η := by ring
    show |(u - u₀) + σ * (v - v₀) + w₁| ≤ 2 * η + ε
    linarith [h1, h2, h3, hw₁]
  have hkey : (u + σ * v + w₁) / v - (u₀ + σ * v₀) / v₀
      = (D * v₀ - (u₀ + σ * v₀) * (v - v₀)) / (v * v₀) := by
    have hnum : u + σ * v + w₁ = (u₀ + σ * v₀) + D := by
      show u + σ * v + w₁ = (u₀ + σ * v₀) + ((u - u₀) + σ * (v - v₀) + w₁)
      ring
    rw [hnum]
    field_simp
    ring
  have hA : |(u + σ * v + w₁) / v - (u₀ + σ * v₀) / v₀| ≤ 15 * (3 * η + ε) := by
    rw [hkey, abs_div, abs_mul]
    have hden : (0 : ℝ) < |v| * |v₀| := mul_pos (abs_pos.mpr hvne) (abs_pos.mpr hv₀ne)
    rw [div_le_iff₀ hden]
    have hnum : |D * v₀ - (u₀ + σ * v₀) * (v - v₀)| ≤ 3 * η + ε := by
      have h2 : |D * v₀ - (u₀ + σ * v₀) * (v - v₀)|
          ≤ |D * v₀| + |(u₀ + σ * v₀) * (v - v₀)| := LeftGapAux.abs_sub_le_abs_add _ _
      have h3 : |D * v₀| ≤ (2 * η + ε) * 1 := by
        rw [abs_mul]
        exact mul_le_mul hDbound hv₀hi (abs_nonneg _) (by linarith)
      have h4 : |(u₀ + σ * v₀) * (v - v₀)| ≤ 1 * η := by
        rw [abs_mul]
        exact mul_le_mul hB'abs hη₁ (abs_nonneg _) (by norm_num)
      linarith [h2, h3, h4]
    have hden2 : (1 : ℝ) / 15 ≤ |v| * |v₀| := by
      have h6 : (1 / 4 : ℝ) * (4 / 15) ≤ |v| * |v₀| :=
        mul_le_mul hv hv₀ (by norm_num) (by linarith [abs_nonneg v])
      linarith [h6]
    have h3η : (0 : ℝ) ≤ 3 * η + ε := by linarith
    have hbig : 3 * η + ε ≤ 15 * (3 * η + ε) * (|v| * |v₀|) := by
      have h7 : (1 : ℝ) ≤ 15 * (|v| * |v₀|) := by linarith [hden2]
      have h8 := mul_le_mul_of_nonneg_left h7 h3η
      linarith [h8]
    linarith [hnum, hbig]
  have hB : |(u₀ + σ * v₀) / v₀ - (-u / Work.OddEnvelope.semicircle u)| ≤ 25 * η := by
    have hgoal : (u₀ + σ * v₀) / v₀ - (-u / Work.OddEnvelope.semicircle u)
        = deriv Work.OddEnvelope.semicircle u₀ - deriv Work.OddEnvelope.semicircle u := by
      rw [hmid, Work.OddEnvelope.Semicircle.deriv_semicircle hu₀I',
        Work.OddEnvelope.Semicircle.deriv_semicircle huI']
    rw [hgoal]
    calc |deriv Work.OddEnvelope.semicircle u₀ - deriv Work.OddEnvelope.semicircle u|
        ≤ 25 * |u₀ - u| := semicircle_deriv_lipschitz hu₀ hu
      _ ≤ 25 * η := by
          rw [abs_sub_comm]
          exact mul_le_mul_of_nonneg_left hη (by norm_num)
  have hsplit : (u + σ * v + w₁) / v - (-u / Work.OddEnvelope.semicircle u)
      = ((u + σ * v + w₁) / v - (u₀ + σ * v₀) / v₀)
        + ((u₀ + σ * v₀) / v₀ - (-u / Work.OddEnvelope.semicircle u)) := by ring
  have hsum := abs_add_le ((u + σ * v + w₁) / v - (u₀ + σ * v₀) / v₀)
    ((u₀ + σ * v₀) / v₀ - (-u / Work.OddEnvelope.semicircle u))
  rw [hsplit]
  linarith [hsum, hA, hB, hη0, hε0]

/-- **Order `2`.** -/
lemma dev_two {σ u u₀ v v₀ v₂ v₂₀ w₁ w₂ η ε : ℝ}
    (hσ0 : 0 < σ) (hσle : σ ≤ 1) (hη0 : 0 ≤ η) (hη100 : η ≤ 1 / 100) (hε0 : 0 ≤ ε)
    (hη : |u - u₀| ≤ η) (hη₁ : |v - v₀| ≤ η) (hη₂ : |v₂ - v₂₀| ≤ η)
    (hw₁ : |w₁| ≤ ε) (hw₂ : |w₂| ≤ ε)
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) (9 / 10)) (hu₀ : u₀ ∈ Set.Icc (1 / 2 : ℝ) (9 / 10))
    (hu₀pos : 0 < u₀) (hu₀le1 : u₀ ≤ 1)
    (hv : 1 / 4 ≤ |v|) (hvhi : |v| ≤ 3 / 2) (hv₂hi : |v₂| ≤ 3 / 2)
    (hv₀ : 4 / 15 ≤ |v₀|) (hv₀hi : |v₀| ≤ 1) (hv₂₀hi : |v₂₀| ≤ 1)
    (hB' : u₀ + σ * v₀ = u₀ ^ 3) (hB'' : 2 * v₀ ^ 2 - u₀ * v₂₀ = u₀ ^ 6)
    (hv₀eq : v₀ = -σ * u₀ ^ 3) (hsemi : Work.OddEnvelope.semicircle u₀ = σ * u₀) :
    |(2 * v ^ 2 - u * v₂ + w₂ * v - w₁ * v₂) / v ^ 3
        - (-(1 / Work.OddEnvelope.semicircle u ^ 3))| ≤ 1000000 * (η + ε) := by
  have hvne : v ≠ 0 := by intro h; rw [h, abs_zero] at hv; norm_num at hv
  have hv₀ne : v₀ ≠ 0 := by intro h; rw [h, abs_zero] at hv₀; norm_num at hv₀
  have hu₀ne : u₀ ≠ 0 := ne_of_gt hu₀pos
  have huI' : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hu₀I' : u₀ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu₀.1], by linarith [hu₀.2]⟩
  -- the auxiliary quantities
  let d₁ : ℝ := v - v₀
  let d₂ : ℝ := v₂ - v₂₀
  let B' : ℝ := u₀ + σ * v₀
  let B'' : ℝ := 2 * v₀ + σ * v₂₀
  let D' : ℝ := (u - u₀) + σ * d₁ + w₁
  let D'' : ℝ := 2 * d₁ + σ * d₂ + w₂
  let E : ℝ := D'' * v₀ + B'' * d₁ + D'' * d₁ - D' * v₂₀ - B' * d₂ - D' * d₂
  have hd₁ : |d₁| ≤ η := hη₁
  have hd₂ : |d₂| ≤ η := hη₂
  have hB'abs : |B'| ≤ 1 := by
    show |u₀ + σ * v₀| ≤ 1
    rw [hB', abs_of_nonneg (pow_nonneg (le_of_lt hu₀pos) 3)]
    exact pow_le_one₀ (le_of_lt hu₀pos) hu₀le1
  have hD'bound : |D'| ≤ 2 * η + ε := by
    have h1 := abs_add_le ((u - u₀) + σ * d₁) w₁
    have h2 := abs_add_le (u - u₀) (σ * d₁)
    have h3 : |σ * d₁| ≤ η := by
      rw [abs_mul, abs_of_pos hσ0]
      calc σ * |d₁| ≤ 1 * η := mul_le_mul hσle hd₁ (abs_nonneg _) (by norm_num)
        _ = η := by ring
    show |(u - u₀) + σ * d₁ + w₁| ≤ 2 * η + ε
    linarith [h1, h2, h3, hw₁]
  have hD''bound : |D''| ≤ 3 * η + ε := by
    have h1 := abs_add_le (2 * d₁ + σ * d₂) w₂
    have h2 := abs_add_le (2 * d₁) (σ * d₂)
    have h3 : |2 * d₁| ≤ 2 * η := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h := mul_le_mul_of_nonneg_left hd₁ (by norm_num : (0 : ℝ) ≤ 2)
      linarith [h]
    have h4 : |σ * d₂| ≤ η := by
      rw [abs_mul, abs_of_pos hσ0]
      calc σ * |d₂| ≤ 1 * η := mul_le_mul hσle hd₂ (abs_nonneg _) (by norm_num)
        _ = η := by ring
    show |2 * d₁ + σ * d₂ + w₂| ≤ 3 * η + ε
    linarith [h1, h2, h3, h4, hw₂]
  have hB''abs : |B''| ≤ 3 := by
    have h1 := abs_add_le (2 * v₀) (σ * v₂₀)
    have h2 : |2 * v₀| ≤ 2 * 1 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left hv₀hi (by norm_num)
    have h3 : |σ * v₂₀| ≤ 1 * 1 := by
      rw [abs_mul, abs_of_pos hσ0]
      exact mul_le_mul hσle hv₂₀hi (abs_nonneg _) (by norm_num)
    show |2 * v₀ + σ * v₂₀| ≤ 3
    linarith [h1, h2, h3]
  -- the algebraic identity `env₂ = (u₀^6 + E)/v³`
  have hAE : 2 * v ^ 2 - u * v₂ + w₂ * v - w₁ * v₂ = u₀ ^ 6 + E := by
    have h1 : 2 * v ^ 2 - u * v₂ + w₂ * v - w₁ * v₂ = (B'' * v₀ - B' * v₂₀) + E := by
      dsimp only [E, D'', D', B'', B']
      ring
    have h2 : B'' * v₀ - B' * v₂₀ = u₀ ^ 6 := by
      dsimp only [B'', B']
      have h3 : (2 * v₀ + σ * v₂₀) * v₀ - (u₀ + σ * v₀) * v₂₀
          = 2 * v₀ ^ 2 - u₀ * v₂₀ := by ring
      rw [h3]; exact hB''
    rw [h1, h2]
  have hEbound : |E| ≤ 12 * (η + ε) := by
    have hEform : E = D'' * v₀ + B'' * d₁ + D'' * d₁ + (-(D' * v₂₀)) + (-(B' * d₂))
        + (-(D' * d₂)) := by
      dsimp only [E]; ring
    rw [hEform]
    have h6 := abs_le_sum_six (D'' * v₀) (B'' * d₁) (D'' * d₁) (-(D' * v₂₀)) (-(B' * d₂))
      (-(D' * d₂))
    have t1 : |D'' * v₀| ≤ (3 * η + ε) * 1 := by
      rw [abs_mul]
      exact mul_le_mul hD''bound hv₀hi (abs_nonneg _) (by linarith)
    have t2 : |B'' * d₁| ≤ 3 * η := by
      rw [abs_mul]
      exact mul_le_mul hB''abs hd₁ (abs_nonneg _) (by norm_num)
    have t3 : |D'' * d₁| ≤ (3 * η + ε) * η := by
      rw [abs_mul]
      exact mul_le_mul hD''bound hd₁ (abs_nonneg _) (by linarith)
    have t4 : |-(D' * v₂₀)| ≤ (2 * η + ε) * 1 := by
      rw [abs_neg, abs_mul]
      exact mul_le_mul hD'bound hv₂₀hi (abs_nonneg _) (by linarith)
    have t5 : |-(B' * d₂)| ≤ 1 * η := by
      rw [abs_neg, abs_mul]
      exact mul_le_mul hB'abs hd₂ (abs_nonneg _) (by norm_num)
    have t6 : |-(D' * d₂)| ≤ (2 * η + ε) * η := by
      rw [abs_neg, abs_mul]
      exact mul_le_mul hD'bound hd₂ (abs_nonneg _) (by linarith)
    have hfin : (3 * η + ε) * 1 + 3 * η + (3 * η + ε) * η + (2 * η + ε) * 1 + 1 * η
        + (2 * η + ε) * η ≤ 12 * (η + ε) := by
      have h7 : η * η ≤ η * (1 / 100) := mul_le_mul_of_nonneg_left hη100 hη0
      have h8 : ε * η ≤ ε * (1 / 100) := mul_le_mul_of_nonneg_left hη100 hε0
      nlinarith [h7, h8]
    linarith [h6, t1, t2, t3, t4, t5, t6, hfin]
  -- the decomposition
  have hsplit : (2 * v ^ 2 - u * v₂ + w₂ * v - w₁ * v₂) / v ^ 3
      - (-(1 / Work.OddEnvelope.semicircle u ^ 3))
      = (E / v ^ 3 + u₀ ^ 6 * (1 / v ^ 3 - 1 / v₀ ^ 3))
        + (u₀ ^ 6 / v₀ ^ 3 - (-(1 / Work.OddEnvelope.semicircle u ^ 3))) := by
    rw [hAE]
    field_simp
    ring
  have hb1 : |E / v ^ 3| ≤ 1000 * (η + ε) := by
    rw [abs_div, abs_pow]
    have hv3 : (0 : ℝ) < |v| ^ 3 := pow_pos (abs_pos.mpr hvne) 3
    rw [div_le_iff₀ hv3]
    have h1 : |E| ≤ 12 * (η + ε) := hEbound
    have h2 : 12 * (η + ε) ≤ (1000 * (η + ε)) * |v| ^ 3 := by
      have h4 : (1 : ℝ) ≤ 64 * |v| ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hv 3
        norm_num at h
        linarith [h]
      have h5 : 0 ≤ 12 * (η + ε) := by linarith
      have h6 := mul_le_mul_of_nonneg_left h4 h5
      linarith [h6]
    linarith [h1, h2]
  have hb2 : |u₀ ^ 6 * (1 / v ^ 3 - 1 / v₀ ^ 3)| ≤ 30000 * η := by
    rw [abs_mul]
    have hP1 : |u₀ ^ 6| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg (le_of_lt hu₀pos) 6)]
      exact pow_le_one₀ (le_of_lt hu₀pos) hu₀le1
    have h5 : |1 / v ^ 3 - 1 / v₀ ^ 3| ≤ 30000 * |v - v₀| :=
      abs_inv_cube_sub_le_general hv hvhi (by linarith [hv₀]) (by linarith [hv₀hi])
    have h6 : |1 / v ^ 3 - 1 / v₀ ^ 3| ≤ 30000 * η := by
      calc |1 / v ^ 3 - 1 / v₀ ^ 3| ≤ 30000 * |v - v₀| := h5
        _ ≤ 30000 * η := mul_le_mul_of_nonneg_left hη₁ (by norm_num)
    calc |u₀ ^ 6| * |1 / v ^ 3 - 1 / v₀ ^ 3| ≤ 1 * (30000 * η) :=
          mul_le_mul hP1 h6 (abs_nonneg _) (by norm_num)
      _ = 30000 * η := by ring
  have hb3 : |u₀ ^ 6 / v₀ ^ 3 - (-(1 / Work.OddEnvelope.semicircle u ^ 3))| ≤ 2000 * η := by
    have h1 : u₀ ^ 6 / v₀ ^ 3 = deriv (deriv Work.OddEnvelope.semicircle) u₀ := by
      rw [LeftGapAux.deriv_deriv_semicircle hu₀I', hv₀eq, hsemi]
      field_simp
    have h2 : -(1 / Work.OddEnvelope.semicircle u ^ 3)
        = deriv (deriv Work.OddEnvelope.semicircle) u := by
      rw [LeftGapAux.deriv_deriv_semicircle huI']
    rw [h1, h2]
    calc |deriv (deriv Work.OddEnvelope.semicircle) u₀
          - deriv (deriv Work.OddEnvelope.semicircle) u| ≤ 2000 * |u₀ - u| :=
          semicircle_deriv2_lipschitz hu₀ hu
      _ ≤ 2000 * η := by
          rw [abs_sub_comm]
          exact mul_le_mul_of_nonneg_left hη (by norm_num)
  rw [hsplit]
  have hX : |E / v ^ 3 + u₀ ^ 6 * (1 / v ^ 3 - 1 / v₀ ^ 3)| ≤ 1000 * (η + ε) + 30000 * η := by
    have h7 := abs_add_le (E / v ^ 3) (u₀ ^ 6 * (1 / v ^ 3 - 1 / v₀ ^ 3))
    linarith [h7, hb1, hb2]
  have hsum := abs_add_le (E / v ^ 3 + u₀ ^ 6 * (1 / v ^ 3 - 1 / v₀ ^ 3))
    (u₀ ^ 6 / v₀ ^ 3 - (-(1 / Work.OddEnvelope.semicircle u ^ 3)))
  linarith [hsum, hX, hb3, hη0, hε0]

/-- **Numeric bounds for `profileX` and its first two derivatives** on the slope window
`[7/10, 1]`. -/
lemma profileX_bounds (σ : ℝ) (h1 : 7 / 10 ≤ σ) (h2 : σ ≤ 1) :
    2 / 3 ≤ Work.OddEnvelope.profileX σ ∧
    Work.OddEnvelope.profileX σ ≤ 83 / 100 ∧
    4 / 15 ≤ |deriv Work.OddEnvelope.profileX σ| ∧
    |deriv Work.OddEnvelope.profileX σ| ≤ 1 ∧
    |deriv (deriv Work.OddEnvelope.profileX) σ| ≤ 1 := by
  have hσ0 : 0 < σ := by linarith
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
  have h1σ : 0 < 1 + σ ^ 2 := by positivity
  have hpos : 0 < Work.OddEnvelope.profileX σ := Work.OddEnvelope.profileX_pos σ
  have hlt1 : Work.OddEnvelope.profileX σ < 1 := Work.OddEnvelope.profileX_lt_one hσ0
  have hsq : Work.OddEnvelope.profileX σ ^ 2 = 1 / (1 + σ ^ 2) :=
    Work.OddEnvelope.profileX_sq σ
  have hge : 2 / 3 ≤ Work.OddEnvelope.profileX σ := by
    rw [Work.OddEnvelope.profileX, le_div_iff₀ (Real.sqrt_pos.mpr h1σ)]
    have h3 : Real.sqrt (1 + σ ^ 2) ≤ (3 : ℝ) / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith
    nlinarith
  have hle : Work.OddEnvelope.profileX σ ≤ 83 / 100 := by
    rw [Work.OddEnvelope.profileX, div_le_iff₀ (Real.sqrt_pos.mpr h1σ)]
    have h3 : (100 : ℝ) / 83 ≤ Real.sqrt (1 + σ ^ 2) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith
    nlinarith
  have hd1 : deriv Work.OddEnvelope.profileX σ = -σ * Work.OddEnvelope.profileX σ ^ 3 :=
    (Work.OddEnvelope.Close.profileX_deriv_formulas σ).1
  have hd2 : deriv (deriv Work.OddEnvelope.profileX) σ
      = (2 * σ ^ 2 - 1) * Work.OddEnvelope.profileX σ ^ 5 :=
    (Work.OddEnvelope.Close.profileX_deriv_formulas σ).2.1
  have hratio : (2 : ℝ) / 5 ≤ σ / (1 + σ ^ 2) := by
    rw [le_div_iff₀ h1σ]
    nlinarith [sq_nonneg (2 * σ - 1), sq_nonneg (σ - 2)]
  have hprod : σ * Work.OddEnvelope.profileX σ ^ 2 = σ / (1 + σ ^ 2) := by
    rw [hsq]; ring
  have hdlo : 4 / 15 ≤ |deriv Work.OddEnvelope.profileX σ| := by
    rw [hd1, show -σ * Work.OddEnvelope.profileX σ ^ 3
        = -(σ * Work.OddEnvelope.profileX σ ^ 3) from by ring, abs_neg,
      abs_of_pos (mul_pos hσ0 (pow_pos hpos 3))]
    have hsplit : σ * Work.OddEnvelope.profileX σ ^ 3
        = (σ * Work.OddEnvelope.profileX σ ^ 2) * Work.OddEnvelope.profileX σ := by ring
    rw [hsplit, hprod]
    have := mul_le_mul hratio hge (by norm_num) (le_of_lt (div_pos hσ0 h1σ))
    linarith [this]
  have hdhi : |deriv Work.OddEnvelope.profileX σ| ≤ 1 :=
    LeftGapAux.profileX_deriv_abs_le_one hσ0
  have hv2 : |deriv (deriv Work.OddEnvelope.profileX) σ| ≤ 1 := by
    rw [hd2, abs_mul]
    have h3 : |2 * σ ^ 2 - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have h4 : |Work.OddEnvelope.profileX σ ^ 5| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg (le_of_lt hpos) 5)]
      exact pow_le_one₀ (le_of_lt hpos) (le_of_lt hlt1)
    have := mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
    linarith [this]
  exact ⟨hge, hle, hdlo, hdhi, hv2⟩

end RightDevAux

end

theorem envelopeRightDevOrdersTwo (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε η σ : ℝ} {p c : ℝ → ℝ},
      0 ≤ η → η ≤ 1 / 100 →
      Work.OddEnvelope.IsChordCurve c →
      ContDiffOn ℝ (⊤ : ℕ∞) p (Set.Ioi 0) →
      7 / 10 ≤ σ → σ ≤ 1 →
      (∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
        |c s - Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv c s - deriv Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv (deriv c) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ η) →
      (|p σ| ≤ ε ∧ |deriv p σ| ≤ ε ∧ |deriv (deriv p) σ| ≤ ε) →
      ∀ k : ℕ, k ≤ 2 →
        |iteratedDeriv k (Work.OddEnvelope.envelopeRight p c) (c σ) -
          iteratedDeriv k Work.OddEnvelope.semicircle (c σ)| ≤ C * (η + ε) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro ε η σ p c hη0 hη100 hc hp hσ1 hσ2 hclos hpjet k hk
  have hσ0 : 0 < σ := by linarith
  set u : ℝ := c σ with hu
  set u₀ : ℝ := Work.OddEnvelope.profileX σ with hu₀
  set v : ℝ := deriv c σ with hv
  set v₀ : ℝ := deriv Work.OddEnvelope.profileX σ with hv₀
  set v₂ : ℝ := deriv (deriv c) σ with hv₂
  set v₂₀ : ℝ := deriv (deriv Work.OddEnvelope.profileX) σ with hv₂₀
  set w : ℝ := p σ with hw
  set w₁ : ℝ := deriv p σ with hw₁
  set w₂ : ℝ := deriv (deriv p) σ with hw₂
  obtain ⟨hu₀ge0, hu₀le0, hv₀lo0, hv₀hi0, hv₂₀hi0⟩ := RightDevAux.profileX_bounds σ hσ1 hσ2
  have hclosσ := hclos σ hσ1 hσ2
  have hδ : |u - u₀| ≤ η := hclosσ.1
  have hδ₁ : |v - v₀| ≤ η := hclosσ.2.1
  have hδ₂ : |v₂ - v₂₀| ≤ η := hclosσ.2.2
  have hw0 : |w| ≤ ε := hpjet.1
  have hw0₁ : |w₁| ≤ ε := hpjet.2.1
  have hw0₂ : |w₂| ≤ ε := hpjet.2.2
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg w) hw0
  have hu₀pos : 0 < u₀ := Work.OddEnvelope.profileX_pos σ
  have hu₀le1 : u₀ ≤ 1 := le_of_lt (Work.OddEnvelope.profileX_lt_one hσ0)
  have hu₀ge : 2 / 3 ≤ u₀ := hu₀ge0
  have hu₀le : u₀ ≤ 83 / 100 := hu₀le0
  have hv₀lo : 4 / 15 ≤ |v₀| := hv₀lo0
  have hv₀hi : |v₀| ≤ 1 := hv₀hi0
  have hv₂₀hi : |v₂₀| ≤ 1 := hv₂₀hi0
  have hu₀Icc : u₀ ∈ Set.Icc (1 / 2 : ℝ) (9 / 10) := ⟨by linarith, by linarith⟩
  have huIcc : u ∈ Set.Icc (1 / 2 : ℝ) (9 / 10) := by
    have h := abs_le.mp hδ
    exact ⟨by linarith [h.1, hu₀Icc.1, hη100], by linarith [h.2, hu₀Icc.2, hη100]⟩
  have huI : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hc.pos hσ0, by linarith [huIcc.2]⟩
  have huI' : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [huIcc.1], by linarith [huIcc.2]⟩
  have hu₀I' : u₀ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu₀Icc.1], by linarith [hu₀Icc.2]⟩
  have hvlo : 1 / 4 ≤ |v| := by
    have h := abs_abs_sub_abs_le_abs_sub v v₀
    have h2 : -(|v| - |v₀|) ≤ |v - v₀| := le_trans (neg_le_abs (|v| - |v₀|)) h
    linarith [h2, hv₀lo, hδ₁]
  have hvhi : |v| ≤ 3 / 2 := by
    have h := abs_add_le v₀ (v - v₀)
    have e : v₀ + (v - v₀) = v := by ring
    rw [e] at h
    linarith [h, hv₀hi, hδ₁, hη100]
  have hv₂hi : |v₂| ≤ 3 / 2 := by
    have h := abs_add_le v₂₀ (v₂ - v₂₀)
    have e : v₂₀ + (v₂ - v₂₀) = v₂ := by ring
    rw [e] at h
    linarith [h, hv₂₀hi, hδ₂, hη100]
  have hvne : v ≠ 0 := by
    intro h; rw [h, abs_zero] at hvlo; norm_num at hvlo
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [h, abs_zero] at hv₀lo; norm_num at hv₀lo
  have hf := Work.OddEnvelope.Close.profileX_deriv_formulas σ
  have hB'id : u₀ + σ * v₀ = u₀ ^ 3 := hf.2.2.1
  have hB''id : 2 * v₀ ^ 2 - u₀ * v₂₀ = u₀ ^ 6 := hf.2.2.2
  have hv₀eq : v₀ = -σ * u₀ ^ 3 := hf.1
  have hBsemi : Work.OddEnvelope.semicircle u₀ = σ * u₀ :=
    (Work.OddEnvelope.mul_profileX_eq_semicircle hσ0).symm
  have hN : u₀ + σ * v₀ = -v₀ / σ := by
    rw [hB'id, hv₀eq]
    field_simp
  have hslope : Work.OddEnvelope.slopeRight c u = σ :=
    (LeftGapAux.slopeRight_eq_of_chord hc hσ0 (rfl : c σ = c σ)).symm
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl
  · simp only [iteratedDeriv_zero]
    have henv : Work.OddEnvelope.envelopeRight p c u = σ * u + w := by
      simp only [Work.OddEnvelope.envelopeRight]
      rw [hslope, ← hw]
    rw [henv]
    have hmain := RightDevAux.dev_zero (σ := σ) (u := u) (u₀ := u₀) (w := w) (η := η) (ε := ε)
      hσ0.le hσ2 hη0 hε0 hδ hw0 huIcc hu₀Icc hBsemi
    linarith [hmain, hη0, hε0]
  · simp only [iteratedDeriv_one]
    have hd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, deriv (Work.OddEnvelope.envelopeRight p c) t
        = Work.OddEnvelope.kSlope p c (Work.OddEnvelope.slopeRight c t) :=
      Work.OddEnvelope.Smoothness.envelopeRight_deriv_Cinf hc.smooth hc.deriv_neg hp
        (fun t ht => hc.surj ht)
    have hderiv : deriv (Work.OddEnvelope.envelopeRight p c) u = (u + σ * v + w₁) / v := by
      rw [hd u huI, hslope]
      simp only [Work.OddEnvelope.kSlope]
      rw [← hu, ← hv, ← hw₁]
    have hsemi : deriv Work.OddEnvelope.semicircle u = -u / Work.OddEnvelope.semicircle u := by
      rw [Work.OddEnvelope.Semicircle.deriv_semicircle huI']
    rw [hderiv, hsemi]
    have hmain := RightDevAux.dev_one (σ := σ) (u := u) (u₀ := u₀) (v := v) (v₀ := v₀) (w₁ := w₁)
      (η := η) (ε := ε) hσ0 hσ2 hη0 hε0 hδ hδ₁ hw0₁ huIcc hu₀Icc hu₀pos hu₀le1 hvlo hv₀lo
      hv₀hi hB'id hN hBsemi
    linarith [hmain, hη0, hε0]
  · have e1 : iteratedDeriv 2 (Work.OddEnvelope.envelopeRight p c)
        = deriv (deriv (Work.OddEnvelope.envelopeRight p c)) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    have e2 : iteratedDeriv 2 Work.OddEnvelope.semicircle
        = deriv (deriv Work.OddEnvelope.semicircle) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e1, e2]
    have henv2 : deriv (deriv (Work.OddEnvelope.envelopeRight p c)) u
        = (2 * v ^ 2 - u * v₂ + w₂ * v - w₁ * v₂) / v ^ 3 := by
      rw [LeftGapAux.deriv_deriv_envelopeRight hc hp huI, hslope]
    have hsemi2 : deriv (deriv Work.OddEnvelope.semicircle) u
        = -(1 / Work.OddEnvelope.semicircle u ^ 3) := by
      rw [LeftGapAux.deriv_deriv_semicircle huI']
    rw [henv2, hsemi2]
    have hmain := RightDevAux.dev_two (σ := σ) (u := u) (u₀ := u₀) (v := v) (v₀ := v₀) (v₂ := v₂)
      (v₂₀ := v₂₀) (w₁ := w₁) (w₂ := w₂) (η := η) (ε := ε) hσ0 hσ2 hη0 hη100 hε0 hδ hδ₁ hδ₂
      hw0₁ hw0₂ huIcc hu₀Icc hu₀pos hu₀le1 hvlo hvhi hv₂hi hv₀lo hv₀hi hv₂₀hi hB'id hB''id hv₀eq hBsemi
    linarith [hmain, hη0, hε0]

end Work.OddVolterra.Free
