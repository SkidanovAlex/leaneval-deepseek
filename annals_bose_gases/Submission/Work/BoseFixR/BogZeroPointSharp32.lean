import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

/-!
## The sharp per-mode Bogoliubov zero point with constant `32`

`bogZeroPoint (A1+B) B ≤ (1/2 + 32√ε) B²/A1` on the window `|B| ≤ 16π√ε·A1`,
`0 ≤ ε ≤ 10⁻⁸`, `0 ≤ A1`.

Ingredients:

* the exact identity `bogZeroPoint A B · (A + √(A²−B²)) = B²`;
* the denominator lower bound `d = (A1+B) + √((A1+B)²−B²) ≥ A1(2 − 32πs − 512π²s²)`,
  obtained from `A1 + B ≥ A1(1−y)`, `√(A1²+2A1B) ≥ A1√(1−2y)` and the
  elementary `√(1−2y) ≥ 1 − y − 2y²` with `y = 16πs`;
* the arithmetic fact `(1/2+32s)(2 − 32πs − 512π²s²) ≥ 1` for `0 ≤ s ≤ 10⁻⁴`.
-/

/-- `√(1 − 2y) ≥ 1 − y − 2y²` for `0 ≤ y ≤ 1/2`.
Indeed `1 − y − 2y² = (1−2y)(1+y)` and
`(1−y−2y²)² − (1−2y) = y²(4y²+4y−3) ≤ 0` on `[0,1/2]`. -/
private lemma one_sub_sub_sq_le_sqrt {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    1 - y - 2 * y ^ 2 ≤ Real.sqrt (1 - 2 * y) := by
  have h1 : 0 ≤ 1 - 2 * y := by linarith
  have h2 : 0 ≤ 1 - y - 2 * y ^ 2 := by nlinarith [sq_nonneg y]
  rw [Real.le_sqrt h2 h1]
  nlinarith [hy0, hy, sq_nonneg y]

/-- `(1/2+32s)(2 − 32πs − 512π²s²) ≥ 1` for `0 ≤ s ≤ 10⁻⁴`.
The crude bound `32πs + 512π²s² ≤ 101.4 s` (from `π ≤ 3.15`) reduces this to
`(1/2+32s)(2 − 101.4s) = 1 + 13.3s − 3244.8s² ≥ 1`. -/
private lemma mul_num32 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 10 ^ 4) :
    1 ≤ (1 / 2 + 32 * s) * (2 - 32 * Real.pi * s - 512 * Real.pi ^ 2 * s ^ 2) := by
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have hpi2 : Real.pi ^ 2 ≤ 9.93 := by nlinarith [hpi, hpi0]
  have hA1 : 32 * Real.pi * s ≤ 100.8 * s := by nlinarith [hpi, hs0]
  have hA2 : 512 * Real.pi ^ 2 * s ^ 2 ≤ 0.6 * s := by nlinarith [hpi2, hs0, hs1]
  have hA : 32 * Real.pi * s + 512 * Real.pi ^ 2 * s ^ 2 ≤ 101.4 * s := by linarith
  have hfac : 0 ≤ 1 / 2 + 32 * s := by positivity
  have hstep : 1 ≤ (1 / 2 + 32 * s) * (2 - 101.4 * s) := by nlinarith [hs0, hs1]
  calc 1 ≤ (1 / 2 + 32 * s) * (2 - 101.4 * s) := hstep
    _ ≤ (1 / 2 + 32 * s) * (2 - (32 * Real.pi * s + 512 * Real.pi ^ 2 * s ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hfac
    _ = (1 / 2 + 32 * s) * (2 - 32 * Real.pi * s - 512 * Real.pi ^ 2 * s ^ 2) := by ring

/-- Arithmetic core: on the window `|B| ≤ 16πs·A1` (`0 ≤ s ≤ 10⁻⁴`, `A1 > 0`) the
denominator `(A1+B) + √((A1+B)²−B²)` is at least `A1/(1/2+32s)`. -/
private lemma arith_core {A1 B s : ℝ} (hA1 : 0 < A1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 10 ^ 4)
    (hB : |B| ≤ 16 * Real.pi * s * A1) :
    A1 ≤ (1 / 2 + 32 * s) * ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2)) := by
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  set y : ℝ := 16 * Real.pi * s with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 2 := by rw [hy]; nlinarith [Real.pi_le_four, hs0, hs1, hpi0]
  have hBy : |B| ≤ y * A1 := hB
  have hBlow : -(y * A1) ≤ B := by
    have := neg_abs_le B; linarith [hBy]
  have harg : (A1 + B) ^ 2 - B ^ 2 = A1 ^ 2 + 2 * A1 * B := by ring
  have hsq : A1 ^ 2 * (1 - 2 * y) ≤ A1 ^ 2 + 2 * A1 * B := by
    nlinarith [hBlow, hA1]
  have hspr : A1 * Real.sqrt (1 - 2 * y) ≤ Real.sqrt (A1 ^ 2 + 2 * A1 * B) := by
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (sq_nonneg A1), Real.sqrt_sq hA1.le] at h1
  have hlow : A1 * (1 - y - 2 * y ^ 2) ≤ A1 * Real.sqrt (1 - 2 * y) :=
    mul_le_mul_of_nonneg_left (one_sub_sub_sq_le_sqrt hy0 hy1) hA1.le
  have hd : A1 * (1 - y) + A1 * (1 - y - 2 * y ^ 2) ≤
      (A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2) := by
    rw [harg]
    have h1 : A1 * (1 - y) ≤ A1 + B := by linarith [hBlow]
    linarith [h1, hspr, hlow]
  have heq : A1 * (1 - y) + A1 * (1 - y - 2 * y ^ 2) =
      A1 * (2 - 32 * Real.pi * s - 512 * Real.pi ^ 2 * s ^ 2) := by
    rw [hy]; ring
  rw [heq] at hd
  have hnum : 1 ≤ (1 / 2 + 32 * s) * (2 - 32 * Real.pi * s - 512 * Real.pi ^ 2 * s ^ 2) :=
    mul_num32 hs0 hs1
  have hc0 : 0 ≤ 1 / 2 + 32 * s := by positivity
  calc A1 = A1 * 1 := by ring
    _ ≤ A1 * ((1 / 2 + 32 * s) * (2 - 32 * Real.pi * s - 512 * Real.pi ^ 2 * s ^ 2)) :=
        mul_le_mul_of_nonneg_left hnum hA1.le
    _ = (1 / 2 + 32 * s) *
          (A1 * (2 - 32 * Real.pi * s - 512 * Real.pi ^ 2 * s ^ 2)) := by ring
    _ ≤ (1 / 2 + 32 * s) * ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2)) :=
        mul_le_mul_of_nonneg_left hd hc0

/-- **Sharp per-mode Bogoliubov zero point, constant `32`.**  For `0 ≤ A1`, `0 ≤ ε ≤ 10⁻⁸`
and `|B| ≤ 16π√ε·A1`,

  `𝒵 = (A1+B) − √((A1+B)² − B²) ≤ (1/2 + 32√ε)·B²/A1`.

This is the sharpened form of `Work.BoseFixR.BogZeroPointLeHalfMul` (same proof skeleton,
constant `64` there, `32` here).  The constant `32` (not `64`) is what the far-leg slot
`Work.BoseFixR.farSlotSharp` needs.

Proof route.  With `s = √ε`, `y = 16πs` and `d = (A1+B) + √((A1+B)²−B²)` one has the exact
identity `bogZeroPoint (A1+B) B · d = B²`.  From `B ≥ −y·A1`:
`A1 + B ≥ A1(1−y)` and `(A1+B)² − B² = A1² + 2A1B ≥ A1²(1−2y)`, so by
`√(1−2y) ≥ 1 − y − 2y²` (`0 ≤ y ≤ 1/4`) one gets `d ≥ A1(2 − 32πs − 512π²s²)`.  Finally
`(1/2+32s)(2 − 32πs − 512π²s²) ≥ 1` for `0 ≤ s ≤ 10⁻⁴` (e.g. from `Real.pi_lt_d2`), and
`0 ≤ bogZeroPoint (A1+B) B` (`Work.BoseB6.bogZeroPoint_nonneg`); multiply `A1 ≤ (1/2+32s)·d`
by `𝒵 ≥ 0` and use the identity.  For `A1 = 0` the hypothesis gives `B = 0` and both sides
vanish. -/
theorem BogZeroPointSharp32 {A1 B ε : ℝ} (hA1 : 0 ≤ A1) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 10 ^ 8) (hB : |B| ≤ 16 * Real.pi * Real.sqrt ε * A1) :
    Work.BoseB6.bogZeroPoint (A1 + B) B ≤ (1 / 2 + 32 * Real.sqrt ε) * B ^ 2 / A1 := by
  rcases lt_or_eq_of_le hA1 with hpos | hzero
  · have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
    have hs1 : Real.sqrt ε ≤ 1 / 10 ^ 4 := by
      have h2 : ε ≤ ((1 : ℝ) / 10 ^ 4) ^ 2 := by
        have : ((1 : ℝ) / 10 ^ 4) ^ 2 = 1 / 10 ^ 8 := by norm_num
        rw [this]; exact hε1
      calc Real.sqrt ε ≤ Real.sqrt (((1 : ℝ) / 10 ^ 4) ^ 2) := Real.sqrt_le_sqrt h2
        _ = 1 / 10 ^ 4 := Real.sqrt_sq (by norm_num)
    have hhalf : 16 * Real.pi * Real.sqrt ε * A1 ≤ A1 / 4 := by
      have hp : 16 * Real.pi * Real.sqrt ε ≤ 1 / 4 := by
        nlinarith [Real.pi_le_four, hs1, hs0, Real.pi_pos]
      nlinarith [hp, hpos]
    have hApos : 0 < A1 + B := by
      have := neg_abs_le B; nlinarith [hB, hhalf, this, hpos]
    have habs : |B| ≤ A1 + B := by
      have := neg_abs_le B; nlinarith [hB, hhalf, this, hpos]
    have hkey := arith_core hpos hs0 hs1 hB
    have hsq : (Real.sqrt ((A1 + B) ^ 2 - B ^ 2)) ^ 2 = (A1 + B) ^ 2 - B ^ 2 :=
      Real.sq_sqrt (by linarith [Work.BoseB6.sq_le_sq_of_abs_le habs])
    have hid : Work.BoseB6.bogZeroPoint (A1 + B) B *
        ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2)) = B ^ 2 := by
      unfold Work.BoseB6.bogZeroPoint
      rw [sub_mul]
      nlinarith [hsq]
    have hz0 : 0 ≤ Work.BoseB6.bogZeroPoint (A1 + B) B :=
      Work.BoseB6.bogZeroPoint_nonneg hApos.le habs
    rw [le_div_iff₀ hpos]
    calc Work.BoseB6.bogZeroPoint (A1 + B) B * A1
        ≤ Work.BoseB6.bogZeroPoint (A1 + B) B *
            ((1 / 2 + 32 * Real.sqrt ε) * ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2))) :=
          mul_le_mul_of_nonneg_left hkey hz0
      _ = (1 / 2 + 32 * Real.sqrt ε) *
            (Work.BoseB6.bogZeroPoint (A1 + B) B *
              ((A1 + B) + Real.sqrt ((A1 + B) ^ 2 - B ^ 2))) := by ring
      _ = (1 / 2 + 32 * Real.sqrt ε) * B ^ 2 := by rw [hid]
  · have hB0 : B = 0 := by
      have h : |B| ≤ 0 := by
        have h' := hB
        rw [← hzero] at h'
        simpa using h'
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg B))
    subst hB0
    subst hzero
    simp [Work.BoseB6.bogZeroPoint]

end Work.BoseFixR
