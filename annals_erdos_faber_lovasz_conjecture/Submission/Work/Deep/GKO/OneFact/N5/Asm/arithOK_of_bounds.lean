import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Asm.Params

/-!
# The pointwise arithmetic of the elementary one-factorization route (N5)

This file proves `ArithOK α n r ε β` (see `Asm.Params`) from the small-`n` inequalities
`hP1`--`hP6`, the floor bounds `hL1`, `hLlo` for `Lpar` and the numeric slack
`hβ8`, `hηα`, `hηs`, `hεα`.

Writing `N = (n:ℝ)`, `z = N^{1/12}` (so `z^8 = N^{2/3}`, `z^10 = N^{5/6}`, `z^12 = N`),
`x = β*ε`, `η = ηpar β ε = (x/64)^2`, `y = η*N`, `s = √(y*N)`, `A = α*N` and
`m = mpar n`, `L = Lpar β ε n`, the whole content of `ArithOK` becomes a handful of
elementary chains.

* `x*N ≥ 40 z^8` (hP1) and `x ≤ 512` (from `hβ8`) control the second clause.
* The third clause is `3⌊5nm/L⌋ + y + 6z^8 + 5 ≤ 7A/32`; it splits into
  `y ≤ 2` (then `L ≥ 1`), `2 ≤ y ≤ 15z^10` (then `L ≥ y/2` and the `150/η` and `7`
  terms of `hP2`), and `y ≥ 15z^10` (then `L ≥ y-1 ≥ 14z^10` and `hηα`).
* The fifth clause is `8⌊√((b+L)n)⌋ + 24 + m + L ≤ D0par`, and splits into
  `y ≤ 11.5 z^8` (using the `150/η` term of `hP2` to bound both `b` and `A`) and
  `y ≥ 11.5 z^8` (using `hηα`).
* The sixth and seventh clauses follow from the same two ingredients.

The five purely arithmetic certificates used here live in `cert2`, `cert3b`, `cert3c`,
`cert5A` and `cert5B`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Deep.GKO.OneFact.N5.Asm

/-- If `M ≤ y^2` and `0 ≤ y` then the integer square root of `M` is at most `y`. -/
theorem sqrt_nat_le_of_le_sq (M : ℕ) {y : ℝ} (hy : 0 ≤ y) (h : (M : ℝ) ≤ y ^ 2) :
    ((Nat.sqrt M : ℕ) : ℝ) ≤ y := by
  have h1 : ((Nat.sqrt M : ℕ) : ℝ) * ((Nat.sqrt M : ℕ) : ℝ) ≤ (M : ℝ) := by
    have := Nat.sqrt_le M
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ ((Nat.sqrt M : ℕ) : ℝ) := by positivity
  have h2 : ((Nat.sqrt M : ℕ) : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith [h1, h, h0]
  have h3 : |((Nat.sqrt M : ℕ) : ℝ)| ≤ |y| := sq_le_sq.mp h2
  rwa [abs_of_nonneg h0, abs_of_nonneg hy] at h3

/-- Concavity/endpoint arithmetic for clause 2 of `ArithOK`: with `N = z^12`, `c = z^8`, the quadratic `w ↦ w/4 - w^2/(4096*z^12)` is at least `4*c+3` on the interval `[40c, 512N]` given `w = x*N` with `xN >= 40c` (hP1) and `x <= 512` (from `ηpar β ε ≤ β*ε/8`). Since `w ≤ 512 z^12` is exactly the vertex of the concave quadratic, the minimum on the interval is at `w = 40 z^8`. -/
private theorem aob_cert2 (z w : ℝ) (hz : 1 ≤ z) (hw1 : 40 * z ^ 8 ≤ w) (hw2 : w ≤ 512 * z ^ 12) :
    4 * z ^ 8 + 3 ≤ w / 4 - w ^ 2 / (4096 * z ^ 12) := by
  have hz0 : (0:ℝ) < z := by linarith
  have hz4 : (1:ℝ) ≤ z ^ 4 := one_le_pow₀ hz
  have hz8 : (1:ℝ) ≤ z ^ 8 := one_le_pow₀ hz
  have hz12 : (1:ℝ) ≤ z ^ 12 := one_le_pow₀ hz
  -- the quadratic `f w = w / 4 - w ^ 2 / (4096 * z ^ 12)` is concave with vertex `512 * z ^ 12`,
  -- which upper-bounds `w`; hence its minimum on the interval sits at `w = 40 * z ^ 8`.
  have hsum : w + 40 * z ^ 8 ≤ 1024 * z ^ 12 := by nlinarith [hw2, hz8, hz12]
  have hbr : 0 ≤ 1 / 4 - (w + 40 * z ^ 8) / (4096 * z ^ 12) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity : (0:ℝ) < 4096 * z ^ 12)]
    nlinarith [hsum]
  have hw40 : 0 ≤ w - 40 * z ^ 8 := by linarith
  -- exact factorisation of the difference `f w - f (40 * z ^ 8)`
  have hfac : (w - 40 * z ^ 8) * (1 / 4 - (w + 40 * z ^ 8) / (4096 * z ^ 12))
      = w / 4 - w ^ 2 / (4096 * z ^ 12) - (10 * z ^ 8 - (25/64) * z ^ 4) := by
    field_simp
    ring
  have hprod : 0 ≤ (w - 40 * z ^ 8) * (1 / 4 - (w + 40 * z ^ 8) / (4096 * z ^ 12)) :=
    mul_nonneg hw40 hbr
  -- `f (40 * z ^ 8) = 10 * z ^ 8 - (25/64) * z ^ 4 ≥ 4 * z ^ 8 + 3` for `z ≥ 1`
  have hquad : 4 * z ^ 8 + 3 ≤ 10 * z ^ 8 - (25/64) * z ^ 4 := by
    have h8ge4 : z ^ 4 ≤ z ^ 8 := by
      have h : z ^ 8 = z ^ 4 * z ^ 4 := by ring
      nlinarith [hz4, sq_nonneg (z ^ 4 - 1)]
    nlinarith [h8ge4, hz4]
  linarith [hfac ▸ hprod, hquad]



/-- A concave quadratic `y ↦ 3*y^2 - s*y` (leading coefficient `-3 < 0`) attains its
minimum on an interval at an endpoint: if both endpoints satisfy `3*y^2 - s*y ≤ t`,
then every point of the interval does.  Concretely,
`(b-a)*(3*y^2 - s*y - t) = (b-y)*(3*a^2 - s*a - t) + (y-a)*(3*b^2 - s*b - t)
  - 3*(b-a)*(y-a)*(b-y)`,
and the last term has the sign making the whole right-hand side nonpositive. -/
private lemma aob_quad_endpoint_bound {a b s t y : ℝ} (ha : a ≤ y) (hy : y ≤ b) (hab : a ≤ b)
    (h1 : 3 * a ^ 2 - s * a ≤ t) (h2 : 3 * b ^ 2 - s * b ≤ t) :
    3 * y ^ 2 - s * y ≤ t := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · have hb0 : 0 < b - a := by linarith
    have hb1 : 0 ≤ b - y := by linarith
    have hb2 : 0 ≤ y - a := by linarith
    have key : (b - a) * (3 * y ^ 2 - s * y - t)
        = (b - y) * (3 * a ^ 2 - s * a - t) + (y - a) * (3 * b ^ 2 - s * b - t)
          - 3 * (b - a) * (y - a) * (b - y) := by ring
    have h1' : (b - y) * (3 * a ^ 2 - s * a - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb1 (by linarith)
    have h2' : (y - a) * (3 * b ^ 2 - s * b - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb2 (by linarith)
    have h3a : 0 ≤ (b - a) * (y - a) := mul_nonneg (le_of_lt hb0) hb2
    have h3' : 0 ≤ 3 * (b - a) * (y - a) * (b - y) := by
      have h := mul_nonneg h3a hb1
      nlinarith [h]
    have hle : (b - a) * (3 * y ^ 2 - s * y - t) ≤ 0 := by
      rw [key]
      linarith
    by_contra hcon
    push Not at hcon
    have hpos : 0 < (b - a) * (3 * y ^ 2 - s * y - t) := mul_pos hb0 (by linarith)
    linarith
  · subst heq
    have hy_eq : y = a := le_antisymm hy ha
    rw [hy_eq]
    exact h1

/-- Arithmetic for case `2 ≤ y ≤ 15*z^10` of clause 3 of `ArithOK` (`N = z^12`, `c = z^8`, `y = ηpar β ε * N`): the function `840*z^20 + (38*z^8+1)*y - 3*y^2 - 270*z^12` is nonnegative on `[2, 15*z^10]`; equivalently `y^2 - (38/3*z^8 + 1/3)*y ≤ 280*z^20 - 90*z^12`. The quadratic in `y` is concave, so it suffices to check `y = 2` and `y = 15*z^10`. -/
private theorem aob_cert3b (z y : ℝ) (hz : 1 ≤ z) (hy1 : 2 ≤ y) (hy2 : y ≤ 15 * z ^ 10) :
    3 * y ^ 2 + 270 * z ^ 12 ≤ 840 * z ^ 20 + (38 * z ^ 8 + 1) * y := by
  have hz8 : (1 : ℝ) ≤ z ^ 8 := one_le_pow₀ hz
  have hz10 : (1 : ℝ) ≤ z ^ 10 := one_le_pow₀ hz
  -- the two monotonicities in `z ≥ 1` used for the endpoint evaluations
  have hz12_20 : z ^ 12 ≤ z ^ 20 := pow_le_pow_right₀ hz (by norm_num)
  have hz12_18 : z ^ 12 ≤ z ^ 18 := pow_le_pow_right₀ hz (by norm_num)
  have hz10_0 : (0 : ℝ) ≤ z ^ 10 := by positivity
  have hz20_0 : (0 : ℝ) ≤ z ^ 20 := by positivity
  -- `y = 2`: `3*2^2 - (38*z^8+1)*2 ≤ 840*z^20 - 270*z^12`, i.e.
  -- `10 + 270*z^12 ≤ 76*z^8 + 840*z^20`
  have h2 : 3 * 2 ^ 2 - (38 * z ^ 8 + 1) * 2 ≤ 840 * z ^ 20 - 270 * z ^ 12 := by
    nlinarith [hz8, hz12_20, hz20_0]
  -- `y = 15*z^10`: `3*(15*z^10)^2 - (38*z^8+1)*(15*z^10) ≤ 840*z^20 - 270*z^12`, i.e.
  -- `270*z^12 ≤ 165*z^20 + 570*z^18 + 15*z^10`
  have hb : 3 * (15 * z ^ 10) ^ 2 - (38 * z ^ 8 + 1) * (15 * z ^ 10)
      ≤ 840 * z ^ 20 - 270 * z ^ 12 := by
    nlinarith [hz12_18, hz10_0, hz20_0]
  have hab : (2 : ℝ) ≤ 15 * z ^ 10 := by linarith
  have hmain := aob_quad_endpoint_bound (a := 2) (b := 15 * z ^ 10) (s := 38 * z ^ 8 + 1)
    (t := 840 * z ^ 20 - 270 * z ^ 12) hy1 hy2 hab h2 hb
  linarith



/-- Arithmetic for case `y ≥ 15*z^10` of clause 3 of `ArithOK` (`N = z^12`, `c = z^8`, `y = ηpar β ε * N`, `s = sqrt (y*N)`): from `y ≥ 15*z^10` we get `s ≥ sqrt 15 * z^11`, which dominates `(30/7)*z^10 + (45/14)*z^2 + 6*z^8 + 5` since `z ≥ 1`. -/
private theorem aob_cert3c (z y s : ℝ) (hz : 1 ≤ z) (hy : 15 * z ^ 10 ≤ y) (hs : s ^ 2 = y * z ^ 12) (hs0 : 0 ≤ s) :
    (30 / 7 : ℝ) * z ^ 10 + (45 / 14 : ℝ) * z ^ 2 + 6 * z ^ 8 + 5 ≤ 6 * s := by
  have hz0 : 0 ≤ z := by linarith
  have hz11 : 0 ≤ z ^ 11 := pow_nonneg hz0 11
  have hz12 : 0 ≤ z ^ 12 := pow_nonneg hz0 12
  -- ## Step 1: `s ≥ sqrt 15 * z^11`
  have hstep1 : Real.sqrt 15 * z ^ 11 ≤ s := by
    have hu : 0 ≤ Real.sqrt 15 * z ^ 11 := mul_nonneg (Real.sqrt_nonneg 15) hz11
    have hmain : 15 * z ^ 22 ≤ y * z ^ 12 := by
      have h := mul_le_mul_of_nonneg_right hy hz12
      calc (15 : ℝ) * z ^ 22 = 15 * z ^ 10 * z ^ 12 := by ring
        _ ≤ y * z ^ 12 := h
    refine (mul_self_le_mul_self_iff hu hs0).mpr ?_
    have h15 : (Real.sqrt 15) ^ 2 = 15 := Real.sq_sqrt (by norm_num)
    have hz22 : (z ^ 11) ^ 2 = z ^ 22 := by rw [← pow_mul]
    have hlhs : (Real.sqrt 15 * z ^ 11) * (Real.sqrt 15 * z ^ 11) = 15 * z ^ 22 := by
      calc (Real.sqrt 15 * z ^ 11) * (Real.sqrt 15 * z ^ 11)
          = (Real.sqrt 15) ^ 2 * (z ^ 11) ^ 2 := by ring
        _ = 15 * z ^ 22 := by rw [h15, hz22]
    rw [hlhs]
    have hss : s * s = y * z ^ 12 := by nlinarith [hs]
    rw [hss]
    exact hmain
  -- ## Step 2: `6 * sqrt 15 * z^11` dominates the left-hand side
  have hc : (259 : ℝ) / 84 ≤ Real.sqrt 15 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h6c : (259 : ℝ) / 14 ≤ 6 * Real.sqrt 15 := by linarith
  have hA : (259 / 14 : ℝ) * z ^ 11 ≤ 6 * (Real.sqrt 15 * z ^ 11) := by
    have h := mul_le_mul_of_nonneg_right h6c hz11
    calc (259 / 14 : ℝ) * z ^ 11 ≤ (6 * Real.sqrt 15) * z ^ 11 := h
      _ = 6 * (Real.sqrt 15 * z ^ 11) := by ring
  have hsum : (30 / 7 : ℝ) * z ^ 10 + (45 / 14 : ℝ) * z ^ 2 + 6 * z ^ 8 + 5
      ≤ (259 / 14) * z ^ 11 := by
    have h1 : 1 ≤ z ^ 11 := one_le_pow₀ hz
    have h10 : z ^ 10 ≤ z ^ 11 := pow_le_pow_right₀ hz (by norm_num)
    have h2 : z ^ 2 ≤ z ^ 11 := pow_le_pow_right₀ hz (by norm_num)
    have h8 : z ^ 8 ≤ z ^ 11 := pow_le_pow_right₀ hz (by norm_num)
    linarith
  linarith



/-- Arithmetic for case `y ≤ 11.5*z^8` of clause 5 of `ArithOK` (`N = z^12`, `c = z^8`, `y = ηpar β ε * N`, `s = sqrt (y*N)`): multiply by the positive `y`; the left side `8.93*sqrt(y*z^12)*y + y^2 + (6*z^8+28)*y` is increasing in `y`, so the worst case is `y = 11.5*z^8`, where it becomes `348.3*z^18 + 132.25*z^16 + 69*z^16 + 322*z^8 ≤ (6400/7)*z^20` because `z ≥ 1`. -/
private theorem aob_cert5A (z y s : ℝ) (hz : 1 ≤ z) (hy1 : 1 ≤ y) (hy2 : y ≤ 11.5 * z ^ 8)
    (hs : s ^ 2 = y * z ^ 12) (hs0 : 0 ≤ s) :
    8.93 * s + y + 6 * z ^ 8 + 28 ≤ (6400 / 7 : ℝ) * z ^ 20 / y := by
  have hy0 : (0:ℝ) < y := by linarith
  have hz0 : (0:ℝ) ≤ z := by linarith
  -- `s = sqrt (y * z^12)`
  have hs_eq : s = Real.sqrt (y * z ^ 12) := by
    rw [← Real.sqrt_sq hs0, hs]
  -- `y * z^12 ≤ 11.5 * z^20 ≤ z^20 * 11.5`
  have hle1 : y * z ^ 12 ≤ 11.5 * z ^ 20 := by
    have h := mul_le_mul_of_nonneg_right hy2 (pow_nonneg hz0 12)
    nlinarith [h]
  -- hence `s ≤ sqrt 11.5 * z^10`
  have hs1 : Real.sqrt (y * z ^ 12) ≤ Real.sqrt 11.5 * z ^ 10 := by
    have h1 : Real.sqrt (y * z ^ 12) ≤ Real.sqrt (11.5 * z ^ 20) := Real.sqrt_le_sqrt hle1
    have h2 : Real.sqrt (11.5 * z ^ 20) = Real.sqrt 11.5 * z ^ 10 := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 11.5)]
      have h3 : Real.sqrt (z ^ 20) = z ^ 10 := by
        rw [show z ^ 20 = (z ^ 10) ^ 2 by ring, Real.sqrt_sq (pow_nonneg hz0 10)]
      rw [h3]
    linarith [h2.le]
  have hsq : s ≤ Real.sqrt 11.5 * z ^ 10 := by rw [hs_eq]; exact hs1
  -- `sqrt 11.5 ≤ 3.4`, since `11.5 ≤ 3.4^2`
  have hs34 : Real.sqrt 11.5 ≤ 3.4 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  -- term-by-term bounds at the worst case `y = 11.5 * z^8`
  have hy2' : y ^ 2 ≤ (11.5 * z ^ 8) ^ 2 := pow_le_pow_left₀ (le_of_lt hy0) hy2 2
  have hA : 8.93 * s * y ≤ 8.93 * (Real.sqrt 11.5 * z ^ 10) * (11.5 * z ^ 8) := by
    have hsy : s * y ≤ (Real.sqrt 11.5 * z ^ 10) * (11.5 * z ^ 8) :=
      mul_le_mul hsq hy2 (le_of_lt hy0) (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hz0 10))
    nlinarith [mul_le_mul_of_nonneg_left hsy (by norm_num : (0:ℝ) ≤ 8.93)]
  have hA' : 8.93 * (Real.sqrt 11.5 * z ^ 10) * (11.5 * z ^ 8)
      ≤ 8.93 * (3.4 * z ^ 10) * (11.5 * z ^ 8) := by
    have h1 : Real.sqrt 11.5 * z ^ 10 ≤ 3.4 * z ^ 10 :=
      mul_le_mul_of_nonneg_right hs34 (pow_nonneg hz0 10)
    have h2 : (Real.sqrt 11.5 * z ^ 10) * (11.5 * z ^ 8) ≤ (3.4 * z ^ 10) * (11.5 * z ^ 8) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 8.93)]
  have hC : (6 * z ^ 8 + 28) * y ≤ (6 * z ^ 8 + 28) * (11.5 * z ^ 8) :=
    mul_le_mul_of_nonneg_left hy2 (by positivity)
  -- `z ≥ 1` turns the lower powers into `z^20`
  have hz8le : z ^ 8 ≤ z ^ 20 := pow_le_pow_right₀ hz (by norm_num)
  have hz16le : z ^ 16 ≤ z ^ 20 := pow_le_pow_right₀ hz (by norm_num)
  have hz18le : z ^ 18 ≤ z ^ 20 := pow_le_pow_right₀ hz (by norm_num)
  -- multiply the goal by the positive `y` and finish by the numeric comparison
  -- `348.26 + 132.25 + 69 + 322 = 871.51 < 6400/7 = 914.29`
  rw [le_div_iff₀ hy0]
  nlinarith [hA, hA', hy2', hC, hz8le, hz16le, hz18le]



/-- Arithmetic for case `y ≥ 11.5*z^8` of clause 5 of `ArithOK` (`N = z^12`, `c = z^8`, `y = ηpar β ε * N`, `s = sqrt (y*N)`): `s ≥ sqrt 11.5 * z^10` and `y ≥ 11.5*z^8`, so `y + 7.07*s ≥ 11.5*z^8 + 23.978*z^10 ≥ 6*z^8+28` since `z ≥ 1`. -/
private theorem aob_cert5B (z y s : ℝ) (hz : 1 ≤ z) (hy : 11.5 * z ^ 8 ≤ y) (hs : s ^ 2 = y * z ^ 12) (hs0 : 0 ≤ s) :
    6 * z ^ 8 + 28 ≤ y + 7.07 * s := by
  have hz8 : (1 : ℝ) ≤ z ^ 8 := one_le_pow₀ hz
  have hz10 : (0 : ℝ) ≤ z ^ 10 := by positivity
  have hz12 : (0 : ℝ) ≤ z ^ 12 := by positivity
  have hz108 : z ^ 8 ≤ z ^ 10 := pow_le_pow_right₀ hz (by norm_num)
  -- Step 1: `s ≥ sqrt 11.5 * z^10`, from `s^2 = y z^12 ≥ 11.5 z^20`.
  have hsq : (Real.sqrt 11.5 * z ^ 10) ^ 2 ≤ s ^ 2 := by
    rw [hs, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11.5)]
    have h1 : 11.5 * z ^ 20 ≤ y * z ^ 12 := by
      have h := mul_le_mul_of_nonneg_right hy hz12
      have he : 11.5 * z ^ 8 * z ^ 12 = 11.5 * z ^ 20 := by ring
      linarith [h, he]
    have he2 : 11.5 * (z ^ 10) ^ 2 = 11.5 * z ^ 20 := by ring
    linarith [h1, he2]
  have hk0 : (0 : ℝ) ≤ Real.sqrt 11.5 * z ^ 10 := by positivity
  have hs_ge : Real.sqrt 11.5 * z ^ 10 ≤ s := by
    nlinarith [sq_nonneg (s - Real.sqrt 11.5 * z ^ 10),
      sq_nonneg (s + Real.sqrt 11.5 * z ^ 10)]
  -- Step 2: the numeric constant `7.07 * sqrt 11.5 ≥ 23.9`.
  have hconst : (23.9 : ℝ) ≤ 7.07 * Real.sqrt 11.5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11.5), Real.sqrt_nonneg 11.5]
  have h7 : 7.07 * (Real.sqrt 11.5 * z ^ 10) ≤ 7.07 * s :=
    mul_le_mul_of_nonneg_left hs_ge (by norm_num)
  -- Step 3: assemble.
  nlinarith [hy, h7, hconst, hz8, hz10, hz108, hk0,
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 23.9) hz10]

theorem arithOK_of_bounds {α β ε : ℝ} (hα : 0 < α) (hβε : 0 < β * ε)
    (hβ8 : ηpar β ε ≤ β * ε / 8)
    (hηα : ηpar β ε + 8 * Real.sqrt (ηpar β ε) ≤ α / 4)
    (hηs : ηpar β ε ≤ α / 8)
    (hεα : ε ≤ α / 16)
    {n r : ℕ} (hn1 : 1 ≤ n)
    (hL1 : 1 ≤ Lpar β ε n)
    (hLlo : ηpar β ε * (n : ℝ) / 2 ≤ (Lpar β ε n : ℝ))
    (hP1 : 5 * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ β * ε * (n : ℝ) / 8)
    (hP2 : (150 / ηpar β ε + 7) * (n : ℝ) ^ ((2 : ℝ) / 3) + 2 ≤ 21 * α / 256 * (n : ℝ))
    (hP3 : 4 * (n : ℝ) ^ ((2 : ℝ) / 3) + 2 ≤ α * (n : ℝ))
    (hP4 : 8 * Real.sqrt (320 / α) * (n : ℝ) ^ ((5 : ℝ) / 6) + 7 * (n : ℝ) ^ ((2 : ℝ) / 3)
      + 25 ≤ α / 8 * (n : ℝ))
    (hP5 : Real.sqrt (320 / α) * (n : ℝ) ^ ((5 : ℝ) / 6) + 3 ≤ 31 * (β * ε) / 128 * (n : ℝ))
    (hP6 : 7 * (n : ℝ) ^ ((2 : ℝ) / 3) + 1 ≤ α / 16 * (n : ℝ))
    (hrα : α * (n : ℝ) ≤ (r : ℝ)) :
    ArithOK α n r ε β := by
  -- ## the `z`-parametrisation of `n`: `n = z^12`, `n^{2/3} = z^8`
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hN0' : (0 : ℝ) ≤ (n : ℝ) := by positivity
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = (n : ℝ) ^ ((1 : ℝ) / 12) := ⟨_, rfl⟩
  have hz1 : 1 ≤ z := by rw [hzdef]; exact Real.one_le_rpow hN1 (by norm_num)
  have hz0 : 0 < z := by linarith
  have hzne : z ≠ 0 := hz0.ne'
  have hzp : ∀ k : ℕ, z ^ k = (n : ℝ) ^ ((k : ℝ) / 12) := by
    intro k
    rw [hzdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0']
    congr 1
    ring
  have hz12 : (n : ℝ) = z ^ 12 := by rw [hzp 12]; norm_num
  have hz8 : (n : ℝ) ^ ((2 : ℝ) / 3) = z ^ 8 := by rw [hzp 8]; norm_num
  have hz8_1 : (1 : ℝ) ≤ z ^ 8 := one_le_pow₀ hz1
  have hz10_1 : (1 : ℝ) ≤ z ^ 10 := one_le_pow₀ hz1
  have hz12_0 : (0 : ℝ) < z ^ 12 := by positivity
  have hz12_20 : z ^ 12 ≤ z ^ 20 := pow_le_pow_right₀ hz1 (by norm_num)
  -- ## the integer parameters, as real bounds
  have hm : ((mpar n : ℕ) : ℝ) ≤ 4 * z ^ 8 + 3 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * (n : ℝ) ^ ((2 : ℝ) / 3) by positivity)
    unfold mpar tpar
    push_cast
    linarith [h, hz8]
  have hm0 : (0 : ℝ) ≤ ((mpar n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hηn0 : 0 ≤ ηpar β ε * (n : ℝ) := by unfold ηpar; positivity
  have hL : ((Lpar β ε n : ℕ) : ℝ) ≤ ηpar β ε * (n : ℝ) := Nat.floor_le hηn0
  have hLlow : ηpar β ε * (n : ℝ) - 1 < ((Lpar β ε n : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (ηpar β ε * (n : ℝ))
    unfold Lpar
    linarith [h]
  have hsp : ((spar α n : ℕ) : ℝ) ≤ α * (n : ℝ) / 64 :=
    Nat.floor_le (div_nonneg (mul_nonneg hα.le hN0') (by norm_num))
  have hsp1 : α * (n : ℝ) / 64 < ((spar α n : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hD : (r : ℝ) / 2 - 2 * (n : ℝ) ^ ((2 : ℝ) / 3) < ((D0par n r : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hd : ((dpar n r : ℕ) : ℝ) ≤ (r : ℝ) / 2 + 2 * (n : ℝ) ^ ((2 : ℝ) / 3) :=
    Nat.floor_le (by positivity)
  have hbp : ((bpar α n : ℕ) : ℝ) * (((spar α n : ℕ) : ℝ) + 1)
      ≤ (n : ℝ) * ((mpar n : ℕ) : ℝ) := by
    have h := Nat.div_mul_le_self (n * mpar n) (spar α n + 1)
    have h' : (((n * mpar n / (spar α n + 1)) * (spar α n + 1) : ℕ) : ℝ)
        ≤ ((n * mpar n : ℕ) : ℝ) := Nat.cast_le.mpr h
    push_cast at h'
    exact h'
  have hq : ((5 * n * mpar n / Lpar β ε n : ℕ) : ℝ) * ((Lpar β ε n : ℕ) : ℝ)
      ≤ 5 * (n : ℝ) * ((mpar n : ℕ) : ℝ) := by
    have h := Nat.div_mul_le_self (5 * n * mpar n) (Lpar β ε n)
    have h' : (((5 * n * mpar n / Lpar β ε n) * Lpar β ε n : ℕ) : ℝ)
        ≤ ((5 * n * mpar n : ℕ) : ℝ) := Nat.cast_le.mpr h
    push_cast at h'
    exact h'
  -- ## `x = β ε`, `η = x^2/4096`
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, β * ε = x := ⟨_, rfl⟩
  have hx0 : 0 < x := hxdef ▸ hβε
  have hxne : x ≠ 0 := hx0.ne'
  have hη : ηpar β ε = x ^ 2 / 4096 := by unfold ηpar; rw [hxdef]; ring
  have hsqη : Real.sqrt (x ^ 2 / 4096) = x / 64 := by
    rw [show x ^ 2 / 4096 = (x / 64) ^ 2 by ring]
    exact Real.sqrt_sq (div_pos hx0 (by norm_num)).le
  rw [hη, hxdef] at hβ8
  rw [hη, hsqη] at hηα
  rw [hxdef, hz8, hz12] at hP1
  rw [hη, hz8, hz12] at hP2
  rw [hz8, hz12] at hP3
  rw [hz12] at hrα hsp hsp1 hbp hq
  rw [hη, hz12] at hL hLlow hLlo
  rw [hz8] at hD hd
  -- ## `y = η n`, `s = √(y n) = x n / 64`, `A = α n`, `W = z^20 / y`
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, x ^ 2 / 4096 * z ^ 12 = y := ⟨_, rfl⟩
  rw [hydef] at hL hLlow hLlo
  have hLr1 : (1 : ℝ) ≤ ((Lpar β ε n : ℕ) : ℝ) := by exact_mod_cast hL1
  have hy1 : 1 ≤ y := le_trans hLr1 hL
  have hy00 : 0 < y := by linarith
  have hyne : y ≠ 0 := hy00.ne'
  have hx512 : x ≤ 512 := by nlinarith [hβ8, hx0]
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, x * z ^ 12 / 64 = s := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [← hsdef]; exact div_nonneg (mul_nonneg hx0.le hz12_0.le) (by norm_num)
  have hs2 : s ^ 2 = y * z ^ 12 := by rw [← hsdef, ← hydef]; ring
  have hyz0 : 0 ≤ y * z ^ 12 := by positivity
  have hsy8 : y ≤ 8 * s := by
    have h := mul_le_mul_of_nonneg_right hβ8 hz12_0.le
    rw [← hydef, ← hsdef]
    linarith [h]
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, α * z ^ 12 = A := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, 4096 * z ^ 8 / x ^ 2 = W := ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [← hWdef]; exact div_pos (by positivity) (pow_pos hx0 2)
  have hWy : W * y = z ^ 20 := by
    rw [← hWdef, ← hydef]
    first | (field_simp; ring) | field_simp | ring
  have hP2W : 150 * W + 7 * z ^ 8 + 2 ≤ 21 * A / 256 := by
    have e : 150 / (x ^ 2 / 4096) * z ^ 8 = 150 * W := by
      rw [← hWdef]
      first | (field_simp; ring) | field_simp | ring
    have e2 : 21 * α / 256 * z ^ 12 = 21 * A / 256 := by rw [← hAdef]; ring
    have e3 : (150 / (x ^ 2 / 4096) + 7) * z ^ 8 = 150 / (x ^ 2 / 4096) * z ^ 8 + 7 * z ^ 8 := by
      ring
    linarith [hP2, e, e2, e3]
  have hA_hP2 : (12800 / 7) * W + (256 / 3) * z ^ 8 + 512 / 21 ≤ A := by linarith [hP2W]
  have hA_hP2full : 400 * W + (56 / 3) * z ^ 8 + 16 / 3 ≤ 7 * A / 32 := by linarith [hA_hP2]
  have hA_hηα : 4 * y + 32 * s ≤ A := by
    have h := mul_le_mul_of_nonneg_right hηα hz12_0.le
    rw [← hydef, ← hsdef, ← hAdef]
    linarith [h]
  have hA3 : 4 * z ^ 8 + 2 ≤ A := by rw [← hAdef]; exact hP3
  have hr : A ≤ (r : ℝ) := by rw [← hAdef]; exact hrα
  have hεN : ε * z ^ 12 ≤ A / 16 := by
    have h := mul_le_mul_of_nonneg_right hεα hz12_0.le
    rw [← hAdef]
    linarith [h]
  have hspA : ((spar α n : ℕ) : ℝ) ≤ A / 64 := by rw [← hAdef]; exact hsp
  have hspA1 : A / 64 < ((spar α n : ℕ) : ℝ) + 1 := by rw [← hAdef]; exact hsp1
  -- ## the number of bad classes
  have hbp245 : ((bpar α n : ℕ) : ℝ) ≤ 0.245 * y := by
    have hb0 : (0 : ℝ) ≤ ((bpar α n : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : ((bpar α n : ℕ) : ℝ) * ((200 / 7) * W)
        ≤ ((bpar α n : ℕ) : ℝ) * (((spar α n : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hspA1, hA_hP2, hz8_1]) hb0
    have h2 : z ^ 12 * ((mpar n : ℕ) : ℝ) ≤ z ^ 12 * (7 * z ^ 8) :=
      mul_le_mul_of_nonneg_left (by linarith [hm, hz8_1]) hz12_0.le
    have h3 : W * ((200 / 7) * ((bpar α n : ℕ) : ℝ)) ≤ W * (7 * y) := by
      linarith [h1, h2, hbp, hWy]
    have h4 := le_of_mul_le_mul_left h3 hW0
    linarith [h4]
  -- ## the integer square root of clauses 5 and 6
  have hsqrtb : ∀ b : ℕ, b ≤ bpar α n →
      ((Nat.sqrt ((b + Lpar β ε n) * n) : ℕ) : ℝ) ≤ (8.93 / 8) * s := by
    intro b hb
    apply sqrt_nat_le_of_le_sq _ (by positivity)
    have hb' : (b : ℝ) ≤ 0.245 * y := le_trans (by exact_mod_cast hb) hbp245
    push_cast
    rw [hz12, mul_pow, hs2]
    have h1 : ((b : ℝ) + ((Lpar β ε n : ℕ) : ℝ)) * z ^ 12 ≤ (1.245 * y) * z ^ 12 :=
      mul_le_mul_of_nonneg_right (by linarith [hb', hL]) hz12_0.le
    linarith [h1, hyz0]
  -- ## the chain for clause 5
  have hchain : 8.93 * s + y + 6 * z ^ 8 + 28 ≤ A / 2 := by
    rcases le_or_gt y (11.5 * z ^ 8) with hy | hy
    · have hc : 8.93 * s + y + 6 * z ^ 8 + 28 ≤ (6400 / 7 : ℝ) * z ^ 20 / y :=
        aob_cert5A z y s hz1 hy1 hy hs2 hs0
      have e : (6400 / 7 : ℝ) * z ^ 20 / y = (6400 / 7) * W := by
        rw [← hWy, mul_div_assoc, mul_div_cancel_right₀ _ hyne]
      linarith [hc, e, hA_hP2, hz8_1]
    · have hc : 6 * z ^ 8 + 28 ≤ y + 7.07 * s := aob_cert5B z y s hz1 hy.le hs2 hs0
      linarith [hc, hA_hηα]
  have hcl7 : y + 6 * z ^ 8 + 4 ≤ 3 * A / 8 := by
    linarith [hA_hηα, hs0, hA_hP2, hW0, hz8_1]
  -- ## the seven clauses
  unfold ArithOK
  rw [hz12, hxdef]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- clause 2
    have hw1 : 40 * z ^ 8 ≤ x * z ^ 12 := by linarith [hP1]
    have hw2 : x * z ^ 12 ≤ 512 * z ^ 12 := mul_le_mul_of_nonneg_right hx512 hz12_0.le
    have hc := aob_cert2 z (x * z ^ 12) hz1 hw1 hw2
    have he : (x * z ^ 12) ^ 2 / (4096 * z ^ 12) = y := by
      rw [← hydef]
      first | (field_simp; ring) | field_simp | ring
    push_cast
    linarith [hc, he, hm, hL]
  · -- clause 3
    generalize 5 * n * mpar n / Lpar β ε n = q at hq ⊢
    have hmN : 5 * z ^ 12 * ((mpar n : ℕ) : ℝ) ≤ 20 * z ^ 20 + 15 * z ^ 12 := by
      have h := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 5 * z ^ 12)
      linarith [h]
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    have hq3 : 3 * (q : ℝ) + y + 6 * z ^ 8 + 5 ≤ 7 * A / 32 := by
      rcases le_or_gt y 2 with hy2 | hy2
      · have hqq : (q : ℝ) ≤ (q : ℝ) * ((Lpar β ε n : ℕ) : ℝ) :=
          le_mul_of_one_le_right hq0 hLr1
        have hW2 : 200 * z ^ 20 ≤ 400 * W := by
          linarith [mul_le_mul_of_nonneg_left hy2 hW0.le, hWy]
        linarith [hA_hP2full, hqq, hq, hmN, hW2, hz12_20, hz8_1]
      · rcases le_or_gt y (15 * z ^ 10) with hy3 | hy3
        · have hc := aob_cert3b z y hz1 hy2.le hy3
          have hqy : (q : ℝ) * y ≤ 40 * z ^ 20 + 30 * z ^ 12 := by
            linarith [mul_le_mul_of_nonneg_left hLlo hq0, hq, hmN]
          suffices h : (3 * (q : ℝ) + y + 6 * z ^ 8 + 5) * y
              ≤ (400 * W + 56 / 3 * z ^ 8 + 16 / 3) * y by
            have := le_of_mul_le_mul_right h hy00
            linarith [hA_hP2full]
          linarith [hqy, hc, hWy]
        · have hLc : 14 * z ^ 10 ≤ ((Lpar β ε n : ℕ) : ℝ) := by
            linarith [hLlow, hz10_1, hy3]
          have hq14 : 3 * (q : ℝ) ≤ (30 / 7) * z ^ 10 + (45 / 14) * z ^ 2 := by
            have h1 : (q : ℝ) * (14 * z ^ 10) ≤ 20 * z ^ 20 + 15 * z ^ 12 := by
              linarith [mul_le_mul_of_nonneg_left hLc hq0, hq, hmN]
            have h2 : 14 * z ^ 10 * (3 * (q : ℝ))
                ≤ 14 * z ^ 10 * ((30 / 7) * z ^ 10 + (45 / 14) * z ^ 2) := by
              linarith [h1]
            exact le_of_mul_le_mul_left h2 (by positivity)
          have hc := aob_cert3c z y s hz1 hy3.le hs2 hs0
          linarith [hc, hq14, hsy8, hA_hηα]
    push_cast
    linarith [hεN, hspA, hm, hL, hD, hq3, hr]
  · -- clause 4
    have h : ((dpar n r : ℕ) : ℝ) + 1 ≤ (r : ℝ) := by linarith [hd, hA3, hr]
    exact_mod_cast h
  · -- clause 5
    intro b hb
    have h1 := hsqrtb b hb
    have key : 8 * (Nat.sqrt ((b + Lpar β ε n) * n) + 3) + (mpar n + Lpar β ε n)
        ≤ D0par n r := by
      have h : ((8 * (Nat.sqrt ((b + Lpar β ε n) * n) + 3) + (mpar n + Lpar β ε n) : ℕ) : ℝ)
          < ((D0par n r : ℕ) : ℝ) := by
        push_cast
        linarith [h1, hm, hL, hchain, hD, hr]
      exact_mod_cast h.le
    exact Nat.le_sub_of_add_le key
  · -- clause 6
    intro b hb
    have h1 := hsqrtb b hb
    have e6 : β / 2 * ε * z ^ 12 = x * z ^ 12 / 2 := by rw [← hxdef]; ring
    rw [e6]
    push_cast
    linarith [h1, hsdef, hP1, hz8_1]
  · -- clause 7
    intro b _
    have hle : mpar n + Lpar β ε n ≤ D0par n r := by
      have h : ((mpar n + Lpar β ε n : ℕ) : ℝ) < ((D0par n r : ℕ) : ℝ) := by
        push_cast
        linarith [hm, hL, hcl7, hD, hr, hA3]
      exact_mod_cast h.le
    rw [Nat.cast_sub hle]
    push_cast
    linarith [hεN, hm, hL, hD, hcl7, hr]

end Work.Deep.GKO.OneFact.N5.Asm
