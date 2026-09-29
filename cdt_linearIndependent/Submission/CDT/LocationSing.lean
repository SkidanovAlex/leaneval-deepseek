import Mathlib

/-!
# Location of the singularities of the C-side operator `LL` (paper, §"Location of the singularities")

Let `a, b ∉ {±1}` be odd integers, `a = 2m+1`, `b = 2n+1`, and suppose `|m/n - 1| < ε` with
`ε < 10⁻⁶`.  The singularities of the order-four operator `LL` away from `0, 4, ∞` are the
`y := x + x/(x-1) = x²/(x-1)` images of the four numbers `x = (a ± √(a²-1))(b ± √(b²-1))`
(Definition `yplus` of the paper).

This module proves the analytic content of the paper's §"Location of the singularities":

**`location_singularities`**: for `0 < ε < 10⁻⁶`, `m, n ≥ 1` with `m ≠ n` and `|m/n - 1| < ε`, and any
choice of signs `s, t ∈ {±1}`, the point `x = (√(m+1) + s√m)²(√(n+1) + t√n)²` satisfies
`|y(x)| ≤ ε⁴/16` (the "small" point `x = (a-√(a²-1))(b-√(b²-1))`) or `1/(2ε) < |y(x)|` (the three
other points).

## The key identities

For `t ≥ 0` put `sqP t := (√(t+1) + √t)²` and `sqM t := (√(t+1) - √t)² = (sqP t)⁻¹`.  For
`a = 2t+1` (`t ≥ 0`) one has `a + √(a²-1) = sqP t` and `a - √(a²-1) = sqM t` (indeed
`a² - 1 = 4t(t+1)` and `sqP t = 2t+1+2√(t²+t)`).

`|m/n - 1| < ε < 1` forces `m` and `n` to have the same sign, so (for the paper's application)
`a` and `b` are both `> 1` or both `< -1`; in the latin case the four `x`-values for `(m,n)` are the
same as those for the *positive* parameters `(-m-1, -n-1)`.  Writing `P := max(m,n)`,
`Q := min(m,n)` and `A := sqP P`, `B := sqM P`, `C := sqP Q`, `D := sqM Q` (`A·B = C·D = 1`), the
four `x`-values are `A·C`, `A·D`, `B·C`, `B·D`, and:

* `x = A·C > 1`, `|y| = A²C²/(AC-1) ≥ AC`;
* `x = A·D = A/C > 1`, `|y| = A²/(C(A-C))`;
* `x = B·D = 1/(AC) < 1`, `|y| = B²D²/(1-BD)`;
* `x = B·C = C/A < 1`, `|y| = 1/(η(η-1)) = |y(η)|/η³` with `η := A/C > 1`.

## The estimates

With `d := P - Q` and the hypothesis `d < P·ε` (which follows from `|m/n - 1| < ε` in *both* cases
`m > n` and `n > m`), one has `d(1-ε) < Qε`, and

* `A ≥ 4P+1`, `C ≤ 4Q+2`, `A - C ≤ 2d(2 + 1/(2Q+1))`;
* `AC ≥ 16PQ > 1/ε` (first point `> 1/ε`) and `BD = 1/(AC) ≤ ε²/(16(1-ε)) < ε²/8`;
* `C(A-C) ≤ ε(16PQ + 12P) < εA²` (second point `> 1/ε`), and `η - 1 = (A-C)/C ≤ 3ε/(1-ε)`, so
  `η ≤ 1+3ε` and the fourth point is `> 1/(2ε)`.

The paper states the conclusion with `1/ε` in place of `1/(2ε)`.  That stronger claim is **false** as
stated: `|y(B·C)| = |y(A·C⁻¹)| = |y(η)|/η³` and `|y(η)| ≈ n/d ≈ 1/ε` while `η ≈ 1 + d/n`, so for
large `n` (e.g. `ε = 10⁻⁶`, `n = 10¹⁴`, `m = n + 10⁸ - 1`) one computes `|y(B·C)| ≈ 999999 < 1/ε`.
The correct uniform statement is `1/(2ε)`, which is what the contour argument requires.
-/

namespace Submission.CDT.LocationSing

noncomputable section

set_option maxHeartbeats 2000000

open Real

/-- The larger root parameter `(√(t+1) + √t)²`: for `a = 2t+1` (`t ≥ 0`) this is `a + √(a²-1)`. -/
def sqP (t : ℝ) : ℝ := (Real.sqrt (t + 1) + Real.sqrt t) ^ 2

/-- The smaller root parameter `(√(t+1) - √t)²`: for `a = 2t+1` (`t ≥ 0`) this is `a - √(a²-1)`;
it is the reciprocal of `sqP t`. -/
def sqM (t : ℝ) : ℝ := (Real.sqrt (t + 1) - Real.sqrt t) ^ 2

/-- The symmetrization `y = x + x/(x-1) = x²/(x-1)`. -/
def ymap (x : ℝ) : ℝ := x ^ 2 / (x - 1)

/-- The four `x`-values `(√(m+1) + s√m)²(√(n+1) + t√n)²`, `s, t ∈ {±1}`. -/
def Xval (m n : ℕ) (s t : ℝ) : ℝ :=
  (Real.sqrt ((m : ℝ) + 1) + s * Real.sqrt (m : ℝ)) ^ 2 *
    (Real.sqrt ((n : ℝ) + 1) + t * Real.sqrt (n : ℝ)) ^ 2

/-! ## 1. Elementary properties of `sqP` and `sqM` -/

lemma sqP_pos (t : ℝ) (ht : 0 ≤ t) : 0 < sqP t := by
  have h : 0 < Real.sqrt (t + 1) := Real.sqrt_pos.mpr (by linarith)
  have h2 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  unfold sqP
  exact pow_pos (by linarith) 2

lemma sqP_mul_sqM (t : ℝ) (ht : 0 ≤ t) : sqP t * sqM t = 1 := by
  have h : (Real.sqrt (t + 1)) ^ 2 - (Real.sqrt t) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ t + 1), Real.sq_sqrt ht]
    ring
  calc sqP t * sqM t
      = (((Real.sqrt (t + 1) + Real.sqrt t)) * ((Real.sqrt (t + 1) - Real.sqrt t))) ^ 2 := by
        unfold sqP sqM; ring
    _ = ((Real.sqrt (t + 1)) ^ 2 - (Real.sqrt t) ^ 2) ^ 2 := by ring
    _ = 1 := by rw [h]; ring

lemma sqM_pos (t : ℝ) (ht : 0 ≤ t) : 0 < sqM t := by
  have h1 : Real.sqrt t < Real.sqrt (t + 1) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  unfold sqM
  exact pow_pos (by linarith : 0 < Real.sqrt (t + 1) - Real.sqrt t) 2

lemma sqM_mul_sqP (t : ℝ) (ht : 0 ≤ t) : sqM t * sqP t = 1 := by
  rw [mul_comm]; exact sqP_mul_sqM t ht

lemma sqM_eq_inv (t : ℝ) (ht : 0 ≤ t) : sqM t = (sqP t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (sqM_mul_sqP t ht)

/-- `sqP t = 2t+1+2√(t(t+1))`. -/
lemma sqP_eq (t : ℝ) (ht : 0 ≤ t) : sqP t = 2 * t + 1 + 2 * Real.sqrt (t * (t + 1)) := by
  have h1 : (Real.sqrt (t + 1)) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
  have h2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have h3 : Real.sqrt (t * (t + 1)) = Real.sqrt t * Real.sqrt (t + 1) :=
    Real.sqrt_mul ht (t + 1)
  unfold sqP
  rw [h3]
  nlinarith [h1, h2]

lemma four_mul_add_one_le_sqP (t : ℝ) (ht : 0 ≤ t) : 4 * t + 1 ≤ sqP t := by
  rw [sqP_eq t ht]
  have h : t ≤ Real.sqrt (t * (t + 1)) := by
    have h2 : Real.sqrt ((t : ℝ) * t) ≤ Real.sqrt (t * (t + 1)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_mul_self ht] at h2
  linarith

lemma sqrt_mul_self_le (t : ℝ) (ht : 0 ≤ t) : Real.sqrt (t * (t + 1)) ≤ t + 1 / 2 := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith⟩

lemma sqP_le (t : ℝ) (ht : 0 ≤ t) : sqP t ≤ 4 * t + 2 := by
  rw [sqP_eq t ht]
  have := sqrt_mul_self_le t ht
  linarith

lemma one_le_sqP (t : ℝ) (ht : 0 ≤ t) : 1 ≤ sqP t := by
  have h := four_mul_add_one_le_sqP t ht
  have h2 : (0 : ℝ) ≤ 4 * t := by linarith
  linarith

/-- `sqP` is strictly increasing on `[0,∞)`. -/
lemma sqP_lt_sqP {t u : ℝ} (ht : 0 ≤ t) (htu : t < u) : sqP t < sqP u := by
  have hu : 0 ≤ u := le_of_lt (lt_of_le_of_lt ht htu)
  have h1 : Real.sqrt t < Real.sqrt u := Real.sqrt_lt_sqrt ht htu
  have h2 : Real.sqrt (t + 1) < Real.sqrt (u + 1) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have h3 : 0 ≤ Real.sqrt t + Real.sqrt (t + 1) := by positivity
  have h4 : 0 ≤ Real.sqrt u + Real.sqrt (u + 1) := by positivity
  have h5 : 0 < (Real.sqrt u - Real.sqrt t) + (Real.sqrt (u + 1) - Real.sqrt (t + 1)) := by
    linarith
  unfold sqP
  nlinarith [sq_nonneg (Real.sqrt u + Real.sqrt (u + 1) - Real.sqrt t - Real.sqrt (t + 1))]

/-! ## 2. The difference bound `sqP P - sqP Q ≤ 2(P-Q)(2 + 1/(2Q+1))` -/

lemma sqP_sub_sqP_le (P Q : ℕ) (hQ : 1 ≤ Q) (hPQ : Q < P) :
    sqP (P : ℝ) - sqP (Q : ℝ) ≤
      2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1)) := by
  have hP0 : (0 : ℝ) ≤ (P : ℝ) := by positivity
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQP : (Q : ℝ) < (P : ℝ) := by exact_mod_cast hPQ
  have hd0 : (0 : ℝ) < (P : ℝ) - (Q : ℝ) := by linarith
  have hX : 0 < (P : ℝ) * ((P : ℝ) + 1) := by nlinarith
  have hY : 0 < (Q : ℝ) * ((Q : ℝ) + 1) := by nlinarith
  have hsqX : Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) ^ 2 = (P : ℝ) * ((P : ℝ) + 1) :=
    Real.sq_sqrt hX.le
  have hsqY : Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1)) ^ 2 = (Q : ℝ) * ((Q : ℝ) + 1) :=
    Real.sq_sqrt hY.le
  have hdiff : Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) - Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1))
      = (((P : ℝ) * ((P : ℝ) + 1)) - ((Q : ℝ) * ((Q : ℝ) + 1))) /
        (Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) + Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1))) := by
    rw [eq_div_iff (by positivity : Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) +
      Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1)) ≠ 0)]
    nlinarith [hsqX, hsqY]
  have hden : (P : ℝ) + (Q : ℝ) ≤
      Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) + Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1)) := by
    have h1 : (P : ℝ) ≤ Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) := by
      have := Real.sqrt_le_sqrt (show ((P : ℝ) * (P : ℝ)) ≤ (P : ℝ) * ((P : ℝ) + 1) by nlinarith)
      rwa [Real.sqrt_mul_self hP0] at this
    have h2 : (Q : ℝ) ≤ Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1)) := by
      have := Real.sqrt_le_sqrt (show ((Q : ℝ) * (Q : ℝ)) ≤ (Q : ℝ) * ((Q : ℝ) + 1) by nlinarith)
      rwa [Real.sqrt_mul_self hQ0] at this
    linarith
  have hnum : ((P : ℝ) * ((P : ℝ) + 1)) - ((Q : ℝ) * ((Q : ℝ) + 1))
      = ((P : ℝ) - (Q : ℝ)) * ((P : ℝ) + (Q : ℝ) + 1) := by ring
  have hbound : Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) - Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1))
      ≤ ((P : ℝ) - (Q : ℝ)) * (1 + 1 / (2 * (Q : ℝ) + 1)) := by
    rw [hdiff, hnum, div_le_iff₀ (by positivity : 0 < Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) +
      Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1)))]
    have h2Q : 0 < 2 * (Q : ℝ) + 1 := by linarith
    have hcast : (Q : ℝ) + 1 ≤ (P : ℝ) := by
      have : Q + 1 ≤ P := hPQ
      exact_mod_cast this
    have hA : ((P : ℝ) + (Q : ℝ) + 1) ≤ (1 + 1 / (2 * (Q : ℝ) + 1)) * ((P : ℝ) + (Q : ℝ)) := by
      have hle : (1 : ℝ) ≤ ((P : ℝ) + (Q : ℝ)) / (2 * (Q : ℝ) + 1) := by
        rw [one_le_div h2Q]; linarith
      have hsplit : (1 + 1 / (2 * (Q : ℝ) + 1)) * ((P : ℝ) + (Q : ℝ))
          = ((P : ℝ) + (Q : ℝ)) + ((P : ℝ) + (Q : ℝ)) / (2 * (Q : ℝ) + 1) := by
        rw [add_mul, one_mul, one_div_mul_eq_div]
      rw [hsplit]; linarith
    have hc : (0 : ℝ) ≤ 1 + 1 / (2 * (Q : ℝ) + 1) := by positivity
    have step1 : ((P : ℝ) - (Q : ℝ)) * ((P : ℝ) + (Q : ℝ) + 1)
        ≤ ((P : ℝ) - (Q : ℝ)) * ((1 + 1 / (2 * (Q : ℝ) + 1)) * ((P : ℝ) + (Q : ℝ))) :=
      mul_le_mul_of_nonneg_left hA hd0.le
    have step2 : ((P : ℝ) - (Q : ℝ)) * ((1 + 1 / (2 * (Q : ℝ) + 1)) * ((P : ℝ) + (Q : ℝ)))
        ≤ ((P : ℝ) - (Q : ℝ)) *
          ((1 + 1 / (2 * (Q : ℝ) + 1)) *
            (Real.sqrt ((P : ℝ) * ((P : ℝ) + 1)) + Real.sqrt ((Q : ℝ) * ((Q : ℝ) + 1)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden hc) hd0.le
    linarith [step1, step2]
  rw [sqP_eq (P : ℝ) hP0, sqP_eq (Q : ℝ) hQ0]
  linarith

/-! ## 3. The four local bounds -/

/-- The "large · large" point `A·C > 1` has `|y| ≥ A·C > 1/ε`. -/
lemma ymap_large_large {A C ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hAC : 1 / ε < A * C) :
    1 / ε < |ymap (A * C)| := by
  have h0 : (1 : ℝ) < A * C := lt_trans ((one_lt_div hε).mpr hε1) hAC
  have hpos : 0 < A * C := by linarith
  have hx : 0 < A * C - 1 := by linarith
  have hval : |ymap (A * C)| = (A * C) ^ 2 / (A * C - 1) := by
    unfold ymap
    rw [abs_of_pos (div_pos (pow_pos hpos 2) hx)]
  rw [hval, lt_div_iff₀ hx]
  have h1 : (1 / ε) * (A * C - 1) < (1 / ε) * (A * C) :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  have h2 : (1 / ε) * (A * C) < (A * C) * (A * C) := by
    nlinarith [hpos, hAC]
  linarith

/-- The "large ÷ small" point `A/C > 1` has `|y| = A²/(C(A-C))`; the arithmetic hypothesis
`C(A-C) < εA²` gives `|y| > 1/ε`. -/
lemma ymap_large_small {A C ε : ℝ} (hε : 0 < ε) (hC : 0 < C) (hCA : C < A)
    (hkey : C * (A - C) < ε * A ^ 2) : 1 / ε < |ymap (A / C)| := by
  have hAc : 0 < A - C := by linarith
  have hAp : 0 < A := by linarith
  have hACp : 0 < A / C := div_pos hAp hC
  have hx0 : 0 < A / C - 1 := by
    rw [sub_pos, one_lt_div hC]; exact hCA
  have hid : (A / C) ^ 2 / (A / C - 1) = A ^ 2 / (C * (A - C)) := by
    field_simp
  have hval : |ymap (A / C)| = A ^ 2 / (C * (A - C)) := by
    unfold ymap
    rw [abs_of_pos (div_pos (pow_pos hACp 2) hx0), hid]
  rw [hval, div_lt_div_iff₀ (by positivity : (0 : ℝ) < ε)
    (by positivity : (0 : ℝ) < C * (A - C))]
  linarith [hkey]

/-- The "small · small" point `B·D = 1/(AC) < ε²/8` (with `B·D ≥ 0`) has `|y| ≤ 2(BD)² < ε⁴/16`. -/
lemma ymap_small_small {ε B D : ℝ} (hε : 0 < ε) (hε4 : ε < 1 / 2) (hBDnn : 0 ≤ B * D)
    (hBD : B * D < ε ^ 2 / 8) : |ymap (B * D)| ≤ ε ^ 4 / 16 := by
  have h1 : B * D < 1 / 2 := by nlinarith [hBD, hε, hε4]
  have hden : 0 < 1 - B * D := by linarith
  have hnum : (B * D) ^ 2 / (B * D - 1) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  have hval : |ymap (B * D)| = (B * D) ^ 2 / (1 - B * D) := by
    have hden2 : B * D - 1 ≠ 0 := by linarith
    unfold ymap
    rw [abs_of_nonpos hnum]
    field_simp
    ring
  rw [hval, div_le_iff₀ hden]
  have hε4pos : (0 : ℝ) < ε ^ 4 := pow_pos hε 4
  have hsq : (B * D) ^ 2 ≤ ε ^ 4 / 64 := by
    nlinarith [hBD, hBDnn, hε, sq_nonneg (ε ^ 2 / 8 - B * D)]
  have hr : ε ^ 4 / 64 ≤ (ε ^ 4 / 16) * (1 - B * D) := by nlinarith [h1, hε4pos]
  linarith

/-- The reciprocal point: `|y(1/x)| = |y(x)|/x³`, so for `1 < x ≤ 1+3ε` and `|y(x)| > 1/ε`
(`ε < 1/12`) the reciprocal has `|y| > 1/(2ε)`. -/
lemma ymap_small_large {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (hε2 : ε < 1 / 12)
    (hy : 1 / ε < |ymap x|) (hx2 : x ≤ 1 + 3 * ε) : 1 / (2 * ε) < |ymap x⁻¹| := by
  have hxpos : 0 < x := by linarith
  have hxm1 : 0 < x - 1 := by linarith
  have hyval : |ymap x| = x ^ 2 / (x - 1) := by
    unfold ymap; rw [abs_of_pos (div_pos (pow_pos hxpos 2) hxm1)]
  have hinv : |ymap x⁻¹| = |ymap x| / x ^ 3 := by
    have h : ymap x⁻¹ = -((x ^ 2 / (x - 1)) / x ^ 3) := by
      unfold ymap
      rw [inv_eq_one_div]
      have hx0 : x ≠ 0 := by linarith
      have hx1 : x - 1 ≠ 0 := by linarith
      have h1x : 1 - x ≠ 0 := by linarith
      field_simp
      ring
    rw [h, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2 / (x - 1) / x ^ 3), hyval]
  have hx3le : x ^ 3 ≤ (1 + 3 * ε) ^ 3 := pow_le_pow_left₀ hxpos.le hx2 3
  have h3 : (1 + 3 * ε) ^ 3 < 2 := by
    have h4 : 1 + 3 * ε < 5 / 4 := by linarith
    have h5 : (0 : ℝ) < 1 + 3 * ε := by linarith
    nlinarith [h4, h5, sq_nonneg (1 + 3 * ε), sq_nonneg (5 / 4 - (1 + 3 * ε))]
  rw [hinv]
  have hstep1 : 1 / (2 * ε) < (1 / ε) / x ^ 3 := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε) (by positivity : (0 : ℝ) < x ^ 3)]
    have h2 : (1 / ε) * (2 * ε) = 2 := by field_simp
    rw [one_mul, h2]
    linarith
  have hstep2 : (1 / ε) / x ^ 3 ≤ |ymap x| / x ^ 3 :=
    div_le_div_of_nonneg_right hy.le (by positivity : (0 : ℝ) ≤ x ^ 3)
  linarith

/-! ## 4. The core estimate for `P > Q ≥ 1` -/

theorem location_core (P Q : ℕ) (hQ : 1 ≤ Q) (hPQ : Q < P) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε < 1 / 10 ^ 6) (hd : ((P : ℝ) - (Q : ℝ)) < (P : ℝ) * ε) :
    (1 / ε < |ymap (sqP (P : ℝ) * sqP (Q : ℝ))|) ∧
    (1 / ε < |ymap (sqP (P : ℝ) * sqM (Q : ℝ))|) ∧
    (1 / (2 * ε) < |ymap (sqM (P : ℝ) * sqP (Q : ℝ))|) ∧
    (|ymap (sqM (P : ℝ) * sqM (Q : ℝ))| ≤ ε ^ 4 / 16) := by
  have hP0 : (0 : ℝ) ≤ (P : ℝ) := by positivity
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQP : (Q : ℝ) < (P : ℝ) := by exact_mod_cast hPQ
  have hd0 : (0 : ℝ) < (P : ℝ) - (Q : ℝ) := by linarith
  have hd1 : (1 : ℝ) ≤ (P : ℝ) - (Q : ℝ) := by
    have h : Q + 1 ≤ P := hPQ
    have h' : ((Q : ℝ) + 1) ≤ (P : ℝ) := by exact_mod_cast h
    linarith
  have hQleP : (Q : ℝ) ≤ (P : ℝ) - 1 := by linarith
  have hε1 : ε < 1 := by linarith [hε]
  have hε4 : ε < 1 / 2 := by linarith [hε]
  have hε12 : ε < 1 / 12 := by linarith [hε]
  -- basic size bounds
  have hAlow : 4 * (P : ℝ) + 1 ≤ sqP (P : ℝ) := four_mul_add_one_le_sqP _ hP0
  have hCup : sqP (Q : ℝ) ≤ 4 * (Q : ℝ) + 2 := sqP_le _ hQ0
  have hClow : 4 * (Q : ℝ) ≤ sqP (Q : ℝ) := by
    have := four_mul_add_one_le_sqP (Q : ℝ) hQ0; linarith
  have hCA : sqP (Q : ℝ) < sqP (P : ℝ) := sqP_lt_sqP hQ0 hQP
  have hA2 : 16 * (P : ℝ) ^ 2 + 8 * (P : ℝ) + 1 ≤ (sqP (P : ℝ)) ^ 2 := by
    have h := hAlow
    nlinarith [hAlow, sq_nonneg ((P : ℝ)), sq_nonneg (sqP (P : ℝ))]
  -- `P·ε > 1` and hence `P > 1/ε`
  have hPlow : 1 / ε < (P : ℝ) := by rw [div_lt_iff₀ hε0]; nlinarith [hd, hd1, hε0]
  -- `Q > (1-ε)/ε`
  have hQlow : (1 - ε) / ε < (Q : ℝ) := by
    have hdle : ((P : ℝ) - (Q : ℝ)) * (1 - ε) < (Q : ℝ) * ε := by nlinarith [hd, hd0, hε0]
    have h1 : (1 : ℝ) * (1 - ε) ≤ ((P : ℝ) - (Q : ℝ)) * (1 - ε) :=
      mul_le_mul_of_nonneg_right hd1 (by linarith)
    rw [div_lt_iff₀ hε0]; nlinarith [hdle, h1]
  -- `d/Q < ε/(1-ε)`
  have hdQ : ((P : ℝ) - (Q : ℝ)) / (Q : ℝ) < ε / (1 - ε) := by
    have hQpos : 0 < (Q : ℝ) := by linarith
    have h1ε : 0 < 1 - ε := by linarith
    have hdle : ((P : ℝ) - (Q : ℝ)) * (1 - ε) < (Q : ℝ) * ε := by nlinarith [hd, hd0, hε0]
    rw [div_lt_div_iff₀ hQpos h1ε]; linarith
  -- the key inequality of the "large ÷ small" bound
  have hkeyAD : sqP (Q : ℝ) * (sqP (P : ℝ) - sqP (Q : ℝ)) < ε * (sqP (P : ℝ)) ^ 2 := by
    have hstep : sqP (Q : ℝ) * (sqP (P : ℝ) - sqP (Q : ℝ))
        ≤ (4 * (Q : ℝ) + 2) * (2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1))) :=
      mul_le_mul hCup (sqP_sub_sqP_le P Q hQ hPQ) (by positivity) (by positivity)
    have hprod : (4 * (Q : ℝ) + 2) * (2 + 1 / (2 * (Q : ℝ) + 1)) = 8 * (Q : ℝ) + 6 := by
      field_simp
      ring
    have hstep' : sqP (Q : ℝ) * (sqP (P : ℝ) - sqP (Q : ℝ))
        ≤ ε * (16 * ((P : ℝ) * (Q : ℝ)) + 12 * (P : ℝ)) := by
      have h4 : 2 * ((P : ℝ) - (Q : ℝ)) * (8 * (Q : ℝ) + 6)
          ≤ 2 * ((P : ℝ) * ε) * (8 * (Q : ℝ) + 6) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [hd]
      have h5 : 2 * ((P : ℝ) * ε) * (8 * (Q : ℝ) + 6)
          = ε * (16 * ((P : ℝ) * (Q : ℝ)) + 12 * (P : ℝ)) := by ring
      have h6 : (4 * (Q : ℝ) + 2) * (2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1)))
          = 2 * ((P : ℝ) - (Q : ℝ)) * ((4 * (Q : ℝ) + 2) * (2 + 1 / (2 * (Q : ℝ) + 1))) := by
        ring
      rw [h6, hprod] at hstep
      linarith [hstep, h4, h5]
    have hcmp : 16 * ((P : ℝ) * (Q : ℝ)) + 12 * (P : ℝ) < (sqP (P : ℝ)) ^ 2 := by
      nlinarith [hA2, hQleP, hP0]
    nlinarith [hstep', hcmp, hε0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) large · large
    refine ymap_large_large hε0 hε1 ?_
    have h1 : 16 * ((P : ℝ) * (Q : ℝ)) ≤ sqP (P : ℝ) * sqP (Q : ℝ) := by
      nlinarith [hAlow, hClow, hP0, hQ0]
    have h3 : (P : ℝ) ≤ (P : ℝ) * (Q : ℝ) := by nlinarith [hQ1, hP0]
    have h4 : 1 / ε < (P : ℝ) * (Q : ℝ) := lt_of_lt_of_le hPlow h3
    have hp : (0 : ℝ) < 1 / ε := by positivity
    have h5 : 1 / ε < 16 * ((P : ℝ) * (Q : ℝ)) := by nlinarith [h4, hp]
    linarith
  · -- (2) large ÷ small
    have hsm : sqM (Q : ℝ) = (sqP (Q : ℝ))⁻¹ := sqM_eq_inv _ hQ0
    rw [hsm, inv_eq_one_div, mul_one_div]
    exact ymap_large_small hε0 (sqP_pos _ hQ0) hCA hkeyAD
  · -- (3) small ÷ large
    have hAD : 1 / ε < |ymap (sqP (P : ℝ) / sqP (Q : ℝ))| :=
      ymap_large_small hε0 (sqP_pos _ hQ0) hCA hkeyAD
    have hratio : sqP (P : ℝ) / sqP (Q : ℝ) ≤ 1 + 3 * ε := by
      have hCpos : 0 < sqP (Q : ℝ) := sqP_pos _ hQ0
      rw [div_le_iff₀ hCpos]
      have hfac : 2 + 1 / (2 * (Q : ℝ) + 1) ≤ 3 := by
        have h2Q : 0 < 2 * (Q : ℝ) + 1 := by linarith
        have hle : (1 : ℝ) / (2 * (Q : ℝ) + 1) ≤ 1 := by
          rw [div_le_one h2Q]; linarith
        linarith
      have hd2 : 2 * ((P : ℝ) - (Q : ℝ)) ≤ 4 * ε * (Q : ℝ) := by
        have hQpos : 0 < (Q : ℝ) := by linarith
        have h1ε : 0 < 1 - ε := by linarith
        have hdle : ((P : ℝ) - (Q : ℝ)) * (1 - ε) < (Q : ℝ) * ε := by nlinarith [hd, hd0, hε0]
        nlinarith [hdle, hε0, hε1]
      have hstep : sqP (P : ℝ) - sqP (Q : ℝ) ≤ 6 * ((P : ℝ) - (Q : ℝ)) := by
        have hc : (0 : ℝ) ≤ 2 * ((P : ℝ) - (Q : ℝ)) := by linarith
        have h := mul_le_mul_of_nonneg_left hfac hc
        have hb := sqP_sub_sqP_le P Q hQ hPQ
        nlinarith [hb, h]
      have h3 : 4 * ε * (Q : ℝ) ≤ ε * sqP (Q : ℝ) := by nlinarith [hClow, hε0]
      linarith
    have hbcs : sqM (P : ℝ) * sqP (Q : ℝ) = (sqP (P : ℝ) / sqP (Q : ℝ))⁻¹ := by
      rw [sqM_eq_inv _ hP0, inv_eq_one_div, inv_div]
      ring
    rw [hbcs]
    exact ymap_small_large ((one_lt_div (sqP_pos _ hQ0)).mpr hCA) hε0 hε12 hAD hratio
  · -- (4) small · small
    have hBD : sqM (P : ℝ) * sqM (Q : ℝ) < ε ^ 2 / 8 := by
      have hsmP : sqM (P : ℝ) = (sqP (P : ℝ))⁻¹ := sqM_eq_inv _ hP0
      have hsmQ : sqM (Q : ℝ) = (sqP (Q : ℝ))⁻¹ := sqM_eq_inv _ hQ0
      rw [hsmP, hsmQ]
      have hmul : (sqP (P : ℝ))⁻¹ * (sqP (Q : ℝ))⁻¹ = 1 / (sqP (P : ℝ) * sqP (Q : ℝ)) := by
        rw [inv_eq_one_div, inv_eq_one_div, div_mul_div_comm, one_mul]
      rw [hmul, div_lt_iff₀ (mul_pos (sqP_pos _ hP0) (sqP_pos _ hQ0))]
      have h1 : 16 * ((P : ℝ) * (Q : ℝ)) ≤ sqP (P : ℝ) * sqP (Q : ℝ) := by
        nlinarith [hAlow, hClow, hP0, hQ0]
      have h2 : (1 - ε) / ε * (1 / ε) < (Q : ℝ) * (P : ℝ) := by
        have h2a : (1 - ε) / ε * (1 / ε) < (Q : ℝ) * (1 / ε) :=
          mul_lt_mul_of_pos_right hQlow (by positivity)
        have h2b : (Q : ℝ) * (1 / ε) < (Q : ℝ) * (P : ℝ) :=
          mul_lt_mul_of_pos_left hPlow (by linarith)
        linarith
      have h3 : ε ^ 2 * ((1 - ε) / ε * (1 / ε)) = (1 - ε) := by field_simp
      nlinarith [h1, h2, h3, hε0, hε4, hP0, hQ0]
    exact ymap_small_small hε0 hε4 (mul_pos (sqM_pos _ hP0) (sqM_pos _ hQ0)).le hBD



/-! ## 5. The main theorem -/

/-- `(√(t+1) + s√t)²` is `sqP t` for `s = 1` and `sqM t` for `s = -1`. -/
lemma sq_sqrt_sign (t : ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (Real.sqrt (t + 1) + s * Real.sqrt t) ^ 2 = sqP t ∨
    (Real.sqrt (t + 1) + s * Real.sqrt t) ^ 2 = sqM t := by
  rcases hs with rfl | rfl
  · left; rw [one_mul]; rfl
  · right; unfold sqM; ring

/-- **Location of the singularities.**  Let `0 < ε < 10⁻⁶` and `m, n ≥ 1` with `m ≠ n` and
`|m/n - 1| < ε`.  Then each of the four numbers `x = (√(m+1) + s√m)²(√(n+1) + t√n)²`
(`s, t ∈ {±1}`), i.e. the `x`-coordinates `(a ± √(a²-1))(b ± √(b²-1))` of the singularities of the
C-side operator `LL` (`a = 2m+1`, `b = 2n+1`), satisfies `|y(x)| ≤ ε⁴/16` or `1/(2ε) < |y(x)|`,
where `y(x) = x + x/(x-1) = x²/(x-1)`. -/
theorem location_singularities (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 10 ^ 6)
    (hr : |(m : ℝ) / (n : ℝ) - 1| < ε)
    (s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    |ymap (Xval m n s t)| ≤ ε ^ 4 / 16 ∨ 1 / (2 * ε) < |ymap (Xval m n s t)| := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hhalf : 1 / (2 * ε) < 1 / ε := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε) hε0]
    linarith
  have key : ∀ u : ℝ,
      (u = sqP (m : ℝ) * sqP (n : ℝ) ∨ u = sqP (m : ℝ) * sqM (n : ℝ) ∨
       u = sqM (m : ℝ) * sqP (n : ℝ) ∨ u = sqM (m : ℝ) * sqM (n : ℝ)) →
      |ymap u| ≤ ε ^ 4 / 16 ∨ 1 / (2 * ε) < |ymap u| := by
    intro u hu
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · -- `m < n` : the larger parameter is `n`
      have hd : ((n : ℝ) - (m : ℝ)) < (n : ℝ) * ε := by
        have hEq : (m : ℝ) / (n : ℝ) - 1 = -(((n : ℝ) - (m : ℝ)) / (n : ℝ)) := by
          field_simp
          ring
        have h1 : ((n : ℝ) - (m : ℝ)) / (n : ℝ) < ε := by
          have habs : |(m : ℝ) / (n : ℝ) - 1| = ((n : ℝ) - (m : ℝ)) / (n : ℝ) := by
            rw [hEq, abs_neg, abs_of_nonneg]
            apply div_nonneg _ hnpos.le
            have hnm : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hlt
            linarith
          rw [← habs]; exact hr
        have h2 : ((n : ℝ) - (m : ℝ)) < (n : ℝ) * ε := by
          have h := mul_lt_mul_of_pos_right h1 hnpos
          rw [div_mul_cancel₀ _ (ne_of_gt hnpos)] at h
          linarith
        exact h2
      obtain ⟨hb1, hb2, hb3, hb4⟩ := location_core n m hm hlt ε hε0 hε hd
      rcases hu with rfl | rfl | rfl | rfl
      · exact Or.inr (lt_trans hhalf (by
          rw [mul_comm (sqP (n : ℝ)) (sqP (m : ℝ))] at hb1; exact hb1))
      · exact Or.inr (by
          rw [mul_comm (sqM (n : ℝ)) (sqP (m : ℝ))] at hb3; exact hb3)
      · exact Or.inr (lt_trans hhalf (by
          rw [mul_comm (sqP (n : ℝ)) (sqM (m : ℝ))] at hb2; exact hb2))
      · exact Or.inl (by
          rw [mul_comm (sqM (n : ℝ)) (sqM (m : ℝ))] at hb4; exact hb4)
    · -- `n < m` : the larger parameter is `m`
      have hd : ((m : ℝ) - (n : ℝ)) < (m : ℝ) * ε := by
        have hEq : (m : ℝ) / (n : ℝ) - 1 = ((m : ℝ) - (n : ℝ)) / (n : ℝ) := by
          field_simp
        have h1 : ((m : ℝ) - (n : ℝ)) / (n : ℝ) < ε := by
          have habs : |(m : ℝ) / (n : ℝ) - 1| = ((m : ℝ) - (n : ℝ)) / (n : ℝ) := by
            rw [hEq, abs_of_nonneg]
            apply div_nonneg _ hnpos.le
            have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hlt
            linarith
          rw [← habs]; exact hr
        have h2 : ((m : ℝ) - (n : ℝ)) < (n : ℝ) * ε := by
          have h := mul_lt_mul_of_pos_right h1 hnpos
          rw [div_mul_cancel₀ _ (ne_of_gt hnpos)] at h
          linarith
        have h3 : (n : ℝ) * ε ≤ (m : ℝ) * ε := by
          have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hlt
          nlinarith [hε0, hnm]
        linarith
      obtain ⟨hb1, hb2, hb3, hb4⟩ := location_core m n hn hlt ε hε0 hε hd
      rcases hu with rfl | rfl | rfl | rfl
      · exact Or.inr (lt_trans hhalf hb1)
      · exact Or.inr (lt_trans hhalf hb2)
      · exact Or.inr hb3
      · exact Or.inl hb4
  rcases sq_sqrt_sign (m : ℝ) hs with hm' | hm'
  · rcases sq_sqrt_sign (n : ℝ) ht with hn' | hn'
    · rw [Xval, hm', hn']; exact key _ (Or.inl rfl)
    · rw [Xval, hm', hn']; exact key _ (Or.inr (Or.inl rfl))
  · rcases sq_sqrt_sign (n : ℝ) ht with hn' | hn'
    · rw [Xval, hm', hn']; exact key _ (Or.inr (Or.inr (Or.inl rfl)))
    · rw [Xval, hm', hn']; exact key _ (Or.inr (Or.inr (Or.inr rfl)))

end

end Submission.CDT.LocationSing
