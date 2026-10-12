import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cut comparison for the Bogoliubov zero point

`Work.BoseB6.bogZeroPoint A B = A − √(A²−B²)`.  The zero point of a mode pair with
diagonal coefficient `τ + x` and pairing coefficient `x` is, after rationalising,

    𝒵(τ+x, x) · (2τ) = (√(τ² + 2τx) − τ)²,

so `𝒵(τ+x, x)` is a function of the single quantity `√(τ²+2τx)` which is monotone in `x`.
The auxiliary lemmas below make this precise in the two ranges relevant here
(`0 ≤ x ≤ y`, and `y ≤ x ≤ 0` with `2|y| ≤ τ`), and the main theorem
`Work.BoseBogFS.zpCutMul_le` is the resulting cut comparison `𝒵(τ+ζw, ζw) ≤ 𝒵(τ+w, w)`.
-/

namespace Work.BoseBogFS

/-- The degenerate zero point: `𝒵(x,x) = x − √(x²−x²) = x`. -/
lemma bogZeroPoint_self (x : ℝ) : Work.BoseB6.bogZeroPoint x x = x := by
  simp [Work.BoseB6.bogZeroPoint]

/-- Rationalised zero point: for `0 ≤ τ² + 2τx`,

    𝒵(τ+x, x) · (2τ) = (√(τ² + 2τx) − τ)² .

(For `τ = 0` this reads `0 = (√0 − 0)²`, which is correct; the identity is the
"`𝒵(τ+x,x) = (u−τ)²/(2τ)`" of the paper, before dividing by `2τ`.) -/
lemma bogZeroPoint_mul_two (τ x : ℝ) (hx : 0 ≤ τ ^ 2 + 2 * τ * x) :
    Work.BoseB6.bogZeroPoint (τ + x) x * (2 * τ) =
      (Real.sqrt (τ ^ 2 + 2 * τ * x) - τ) ^ 2 := by
  have harg : (τ + x) ^ 2 - x ^ 2 = τ ^ 2 + 2 * τ * x := by ring
  set s := Real.sqrt (τ ^ 2 + 2 * τ * x) with hs
  have hs2 : s ^ 2 = τ ^ 2 + 2 * τ * x := by rw [hs]; exact Real.sq_sqrt hx
  unfold Work.BoseB6.bogZeroPoint
  rw [harg, ← hs]
  nlinarith [hs2]

/-- Monotonicity of the zero point for nonnegative arguments: if `0 ≤ x ≤ y` then
`𝒵(τ+x, x) ≤ 𝒵(τ+y, y)`.  Here `√(τ²+2τx) ≥ τ`, and the map
`u ↦ (u−τ)²/(2τ)` is increasing on `[τ, ∞)`. -/
lemma zp_le_of_nonneg {τ x y : ℝ} (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Work.BoseB6.bogZeroPoint (τ + x) x ≤ Work.BoseB6.bogZeroPoint (τ + y) y := by
  rcases eq_or_lt_of_le hτ with hτ0 | hτpos
  · rw [← hτ0, zero_add, zero_add, bogZeroPoint_self x, bogZeroPoint_self y]
    exact hxy
  · have hy : 0 ≤ y := le_trans hx hxy
    have hxarg : 0 ≤ τ ^ 2 + 2 * τ * x := by nlinarith [sq_nonneg τ, mul_nonneg hτ hx]
    have hyarg : 0 ≤ τ ^ 2 + 2 * τ * y := by nlinarith [sq_nonneg τ, mul_nonneg hτ hy]
    have hle : τ ^ 2 + 2 * τ * x ≤ τ ^ 2 + 2 * τ * y := by
      nlinarith [mul_le_mul_of_nonneg_left hxy hτ]
    set v := Real.sqrt (τ ^ 2 + 2 * τ * x) with hv
    set u := Real.sqrt (τ ^ 2 + 2 * τ * y) with hu
    have hvτ : τ ≤ v := by
      rw [hv]
      calc τ = Real.sqrt (τ ^ 2) := (Real.sqrt_sq hτ).symm
        _ ≤ Real.sqrt (τ ^ 2 + 2 * τ * x) :=
            Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hτ hx])
    have huτ : τ ≤ u := by
      rw [hu]
      calc τ = Real.sqrt (τ ^ 2) := (Real.sqrt_sq hτ).symm
        _ ≤ Real.sqrt (τ ^ 2 + 2 * τ * y) :=
            Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hτ hy])
    have hvu : v ≤ u := by
      rw [hv, hu]; exact Real.sqrt_le_sqrt hle
    have hsq : (v - τ) ^ 2 ≤ (u - τ) ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr hvτ) (sub_le_sub_right hvu τ) 2
    have h2τ : 0 < 2 * τ := by linarith
    have hmain : Work.BoseB6.bogZeroPoint (τ + x) x * (2 * τ) ≤
        Work.BoseB6.bogZeroPoint (τ + y) y * (2 * τ) := by
      rw [bogZeroPoint_mul_two τ x hxarg, bogZeroPoint_mul_two τ y hyarg]
      simpa [hv, hu] using hsq
    exact le_of_mul_le_mul_right hmain h2τ

/-- Monotonicity of the zero point for nonpositive arguments: if `y ≤ x ≤ 0` and `2|y| ≤ τ`
(so that both `τ² + 2τx`, `τ² + 2τy` are nonnegative and both square roots are `≤ τ`), then
`𝒵(τ+x, x) ≤ 𝒵(τ+y, y)`.  Here the map `u ↦ (u−τ)²/(2τ)` is decreasing on `[0, τ]`, and
`|x| ≤ |y|` makes the two arguments well defined. -/
lemma zp_le_of_nonpos {τ x y : ℝ} (hτ : 0 ≤ τ) (hy : 2 * |y| ≤ τ) (hx0 : x ≤ 0)
    (hyx : y ≤ x) :
    Work.BoseB6.bogZeroPoint (τ + x) x ≤ Work.BoseB6.bogZeroPoint (τ + y) y := by
  rcases eq_or_lt_of_le hτ with hτ0 | hτpos
  · have hy0 : y = 0 := by
      have h : |y| = 0 := by linarith [abs_nonneg y]
      exact abs_eq_zero.mp h
    have hx0' : x = 0 := by
      rw [hy0] at hyx
      exact le_antisymm hx0 hyx
    rw [← hτ0, hy0, hx0']
  · have hxabs : |x| ≤ |y| := by
      rw [abs_of_nonpos hx0, abs_of_nonpos (le_trans hyx hx0)]
      linarith
    have hx2 : 2 * |x| ≤ τ := by linarith
    have hxarg : 0 ≤ τ ^ 2 + 2 * τ * x := by
      have h1 : 2 * τ * |x| ≤ τ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hx2 hτ]
      nlinarith [neg_abs_le x, h1]
    have hyarg : 0 ≤ τ ^ 2 + 2 * τ * y := by
      have h1 : 2 * τ * |y| ≤ τ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hy hτ]
      nlinarith [neg_abs_le y, h1]
    have hle : τ ^ 2 + 2 * τ * y ≤ τ ^ 2 + 2 * τ * x := by
      nlinarith [mul_le_mul_of_nonneg_left hyx hτ]
    set v := Real.sqrt (τ ^ 2 + 2 * τ * x) with hv
    set u := Real.sqrt (τ ^ 2 + 2 * τ * y) with hu
    have huv : u ≤ v := by
      rw [hu, hv]; exact Real.sqrt_le_sqrt hle
    have hvτ : v ≤ τ := by
      rw [hv]
      calc Real.sqrt (τ ^ 2 + 2 * τ * x) ≤ Real.sqrt (τ ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hτ hx0])
        _ = τ := Real.sqrt_sq hτ
    have huτ : u ≤ τ := by
      rw [hu]
      calc Real.sqrt (τ ^ 2 + 2 * τ * y) ≤ Real.sqrt (τ ^ 2) :=
            Real.sqrt_le_sqrt
              (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hτ (le_trans hyx hx0)])
        _ = τ := Real.sqrt_sq hτ
    have hsq : (v - τ) ^ 2 ≤ (u - τ) ^ 2 := by
      have h1 : (τ - v) ^ 2 ≤ (τ - u) ^ 2 :=
        pow_le_pow_left₀ (sub_nonneg.mpr hvτ) (sub_le_sub_left huv τ) 2
      have e2 : (v - τ) ^ 2 = (τ - v) ^ 2 := by ring
      have e1 : (u - τ) ^ 2 = (τ - u) ^ 2 := by ring
      calc (v - τ) ^ 2 = (τ - v) ^ 2 := e2
        _ ≤ (τ - u) ^ 2 := h1
        _ = (u - τ) ^ 2 := e1.symm
    have hmain : Work.BoseB6.bogZeroPoint (τ + x) x * (2 * τ) ≤
        Work.BoseB6.bogZeroPoint (τ + y) y * (2 * τ) := by
      rw [bogZeroPoint_mul_two τ x hxarg, bogZeroPoint_mul_two τ y hyarg]
      simpa [hv, hu] using hsq
    exact le_of_mul_le_mul_right hmain (by linarith)

/-- **Cut comparison for the Bogoliubov zero point** (`𝒵 = Work.BoseB6.bogZeroPoint`,
`𝒵(A,B) = A − √(A²−B²)` with the Lean convention `√x = 0` for `x < 0`).

For `τ ≥ 0`, `ζ ∈ [0,1]` and a pairing coefficient `w` with **either** `0 ≤ w` **or**
`2|w| ≤ τ`,

    𝒵(τ + ζ·w, ζ·w) ≤ 𝒵(τ + w, w) .

The two alternatives are both needed: the single alternative `0 ≤ w` fails for `w < 0` with
`|w| > τ/2` (e.g. `τ = 1`, `w = -1`, `ζ = 1/2`: LHS `= 1/2`, RHS `= 0`), and the single
alternative `2|w| ≤ τ` is what covers that regime.

Proof: for `τ > 0` and `τ² + 2τx ≥ 0`, `𝒵(τ+x,x) = (√(τ²+2τx) − τ)²/(2τ)` (rationalise:
`x = (u²−τ²)/(2τ)` with `u = √(τ²+2τx)`), so the claim is `(√(τ²+2τζw) − τ)² ≤
(√(τ²+2τw) − τ)²`.  If `0 ≤ w` then `0 ≤ ζw ≤ w` and both square roots are `≥ τ`; if `w < 0`
(with `τ ≥ 2|w|` so that both `τ²+2τx` are `≥ 0`) then `w ≤ ζw ≤ 0` and both square roots are
`≤ τ`.  `τ = 0` is the degenerate case (`𝒵(x,x) = x`). -/
theorem zpCutMul_le {τ w ζ : ℝ} (hτ : 0 ≤ τ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hw : 0 ≤ w ∨ 2 * |w| ≤ τ) :
    Work.BoseB6.bogZeroPoint (τ + ζ * w) (ζ * w) ≤ Work.BoseB6.bogZeroPoint (τ + w) w := by
  rcases hw with hwge | hwabs
  · exact zp_le_of_nonneg hτ (mul_nonneg hζ0 hwge)
      (by simpa using mul_le_mul_of_nonneg_right hζ1 hwge)
  · rcases le_or_gt w 0 with hwle | hwgt
    · exact zp_le_of_nonpos hτ hwabs (mul_nonpos_of_nonneg_of_nonpos hζ0 hwle)
        (by simpa using mul_le_mul_of_nonpos_right hζ1 hwle)
    · exact zp_le_of_nonneg hτ (mul_nonneg hζ0 hwgt.le)
        (by simpa using mul_le_mul_of_nonneg_right hζ1 hwgt.le)

end Work.BoseBogFS
