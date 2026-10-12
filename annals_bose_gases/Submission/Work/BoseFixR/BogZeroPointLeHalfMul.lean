import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

/-!
## `bogZeroPoint (A1+B) B ≤ (1/2 + 64√ε) B²/A1`

Sharp-per-mode bound on FS's zero-point constant `𝒜 − √(𝒜²−ℬ²)`, valid on the
small-`ε` window `|B| ≤ 16π√ε·A1` (`ε ≤ 10⁻⁸`).  The point is the exact identity

  `bogZeroPoint A B · (A + √(A²−B²)) = B²`,

i.e. `bogZeroPoint (A1+B) B = B²/d` with `d = (A1+B) + √((A1+B)²−B²)`, together
with the lower bound `d ≥ A1(2 − 48π√ε)`, which is `≥ A1/(1/2+64√ε)` on the window.

The two ingredients are the elementary estimates
`√(1−2y) ≥ 1−2y` (`y ≤ 1/2`) and the arithmetic fact
`(1/2+64s)(2−48πs) ≥ 1` for `0 ≤ s ≤ 10⁻⁴`.
-/

/-- `√(1 − 2y) ≥ 1 − 2y` for `0 ≤ y ≤ 1/2`. -/
private lemma one_sub_two_le_sqrt {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    1 - 2 * y ≤ Real.sqrt (1 - 2 * y) := by
  have h0 : 0 ≤ 1 - 2 * y := by linarith
  rw [Real.le_sqrt h0 h0]
  nlinarith [hy0, hy]

/-- `(1/2+64s)(2−48πs) ≥ 1` for `0 ≤ s ≤ 10⁻⁴`. -/
private lemma halfMul_num {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 10 ^ 4) :
    1 ≤ (1 / 2 + 64 * s) * (2 - 48 * Real.pi * s) := by
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hps : Real.pi * s ≤ 4 * (1 / 10 ^ 4) := by nlinarith [hpi, hs0, hs1, hpi0]
  nlinarith [hps, hs0, hpi, hpi0]

/-- Arithmetic core: on the window `|B| ≤ 16πs·A1` (`0 ≤ s ≤ 10⁻⁴`, `A1 > 0`) the
denominator `(A1+B) + √((A1+B)²−B²)` is at least `A1/(1/2+64s)`. -/
private lemma arith_core {A1 B s : ℝ} (hA1 : 0 < A1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 10 ^ 4)
    (hB : |B| ≤ 16 * Real.pi * s * A1) :
    A1 ≤ (1 / 2 + 64 * s) * ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2)) := by
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  set y : ℝ := 16 * Real.pi * s with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 2 := by
    rw [hy]; nlinarith [Real.pi_le_four, hs0, hs1, hpi0]
  have hBy : |B| ≤ y * A1 := hB
  have hBlow : -(y * A1) ≤ B := by
    have := neg_abs_le B; linarith [hBy]
  have harg : (A1 + B) ^ 2 - B ^ 2 = A1 ^ 2 + 2 * A1 * B := by ring
  have hsq : A1 ^ 2 * (1 - 2 * y) ≤ A1 ^ 2 + 2 * A1 * B := by
    nlinarith [hBlow, hA1]
  have hspr : A1 * Real.sqrt (1 - 2 * y) ≤ Real.sqrt (A1 ^ 2 + 2 * A1 * B) := by
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (sq_nonneg A1), Real.sqrt_sq hA1.le] at h1
  have hlow : A1 * (1 - 2 * y) ≤ A1 * Real.sqrt (1 - 2 * y) :=
    mul_le_mul_of_nonneg_left (one_sub_two_le_sqrt hy0 hy1) hA1.le
  have hd : A1 * (1 - y) + A1 * (1 - 2 * y) ≤
      (A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2) := by
    rw [harg]
    have h1 : A1 * (1 - y) ≤ A1 + B := by linarith [hBlow]
    linarith [h1, hspr]
  have heq : A1 * (1 - y) + A1 * (1 - 2 * y) = A1 * (2 - 48 * Real.pi * s) := by
    rw [hy]; ring
  rw [heq] at hd
  have hnum : 1 ≤ (1 / 2 + 64 * s) * (2 - 48 * Real.pi * s) := halfMul_num hs0 hs1
  have hc0 : 0 ≤ 1 / 2 + 64 * s := by positivity
  calc A1 = A1 * 1 := by ring
    _ ≤ A1 * ((1 / 2 + 64 * s) * (2 - 48 * Real.pi * s)) :=
        mul_le_mul_of_nonneg_left hnum hA1.le
    _ = (1 / 2 + 64 * s) * (A1 * (2 - 48 * Real.pi * s)) := by ring
    _ ≤ (1 / 2 + 64 * s) * ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2)) :=
        mul_le_mul_of_nonneg_left hd hc0

theorem BogZeroPointLeHalfMul {A1 B ε : ℝ} (hA1 : 0 < A1) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 10 ^ 8)
    (hB : |B| ≤ 16 * Real.pi * Real.sqrt ε * A1) :
    Work.BoseB6.bogZeroPoint (A1 + B) B ≤ (1 / 2 + 64 * Real.sqrt ε) * B ^ 2 / A1 := by
  have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hs1 : Real.sqrt ε ≤ 1 / 10 ^ 4 := by
    have h2 : ε ≤ ((1 : ℝ) / 10 ^ 4) ^ 2 := by
      have : ((1 : ℝ) / 10 ^ 4) ^ 2 = 1 / 10 ^ 8 := by norm_num
      rw [this]; exact hε1
    calc Real.sqrt ε ≤ Real.sqrt (((1 : ℝ) / 10 ^ 4) ^ 2) := Real.sqrt_le_sqrt h2
      _ = 1 / 10 ^ 4 := Real.sqrt_sq (by norm_num)
  have hhalf : 16 * Real.pi * Real.sqrt ε * A1 ≤ A1 / 2 := by
    have hp : 16 * Real.pi * Real.sqrt ε ≤ 1 / 2 := by
      nlinarith [Real.pi_le_four, hs1, hs0, Real.pi_pos]
    nlinarith [hp, hA1]
  have hApos : 0 < A1 + B := by
    have := neg_abs_le B; nlinarith [hB, this, hhalf, hA1]
  have habs : |B| ≤ A1 + B := by
    have := neg_abs_le B; nlinarith [hB, this, hhalf, hA1]
  have hkey := arith_core hA1 hs0 hs1 hB
  have hsq : (Real.sqrt ((A1 + B) ^ 2 - B ^ 2)) ^ 2 = (A1 + B) ^ 2 - B ^ 2 :=
    Real.sq_sqrt (by linarith [Work.BoseB6.sq_le_sq_of_abs_le habs])
  have hid : Work.BoseB6.bogZeroPoint (A1 + B) B *
      ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2)) = B ^ 2 := by
    unfold Work.BoseB6.bogZeroPoint
    rw [sub_mul]
    nlinarith [hsq]
  have hz0 : 0 ≤ Work.BoseB6.bogZeroPoint (A1 + B) B :=
    Work.BoseB6.bogZeroPoint_nonneg hApos.le habs
  rw [le_div_iff₀ hA1]
  calc Work.BoseB6.bogZeroPoint (A1 + B) B * A1
      ≤ Work.BoseB6.bogZeroPoint (A1 + B) B *
          ((1 / 2 + 64 * Real.sqrt ε) * ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2))) :=
        mul_le_mul_of_nonneg_left hkey hz0
    _ = (1 / 2 + 64 * Real.sqrt ε) *
          (Work.BoseB6.bogZeroPoint (A1 + B) B *
            ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2))) := by ring
    _ = (1 / 2 + 64 * Real.sqrt ε) * B ^ 2 := by rw [hid]

end Work.BoseFixR
