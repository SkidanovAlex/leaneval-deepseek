import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.CloseCondFSCompat
import Submission.Work.BoseFixR.RB5FSArith2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/RB5FSArith2FS.lean` — the far-leg arithmetic at the corrected
close threshold `closeThresholdFS`

`Work.BoseFixR.RB5FSArith2` proves the scalar far-leg bound

  `ErrRes v μ ρ + |ρ−μ|·256π(a v)𝓜 + errLHY v μ ≤ 4π(a v)(ρ−μ)²ℓ³`

under FS's old far condition `FarCond v μ ρ` (`closeThreshold v μ = μK_ℓ^{-2} ≤ |ρ−μ|`).
The corrected interface (`BoseBoxFock/Defs.lean`, design `F9`) uses the *smaller* threshold
`closeThresholdFS v μ = closeThreshold v μ/(2¹⁴π)`, i.e. a **larger** far region (by the
factor `c := 2¹⁴π ≈ 5.15·10⁴`), and the far-leg targets (`Work.BoseBoxFock.RB5FS`,
`Work.BoseFixR.RB5FSHonestFix`) are stated with it.  This file reproves the arithmetic
with `FarCondFS`.

**Why the old proof does not transfer.**  Its two children consume the far condition
only through `μX³ ≤ |ρ−μ|` (`X = (μa³)^{1/323}`, `μX³ = closeThreshold`), which is now
available only in the weakened form `μX³ ≤ c|ρ−μ|` — the margin `(ρ−μ)²` shrinks by `c²`:

* the net `|ρ−μ|·256π(a v)𝓜` row is still fine, because the same `c` sits on the *other*
  side there;
* the `ErrRes` rows are fine as well: their `(ρ+μ)`-powers carry the slack
  `10³⁰⁰·X^{289/8} ≤ 10^{-100}`, which beats `c²` by 90 orders of magnitude;
* the LHY margin is **not**: the coarse `ErrLHYBudget` bound `errLHY ≤ π(a v)μ²ℓ³X⁶`
  loses exactly the factor `c²` (paying it would need `πc² ≤ 4π`).  The definition
  `errLHY = 8π·lhyC·μ²aℓ³√(dil) = 8π·lhyC·μ²aℓ³·X^{323/2}` is used instead, whose
  correction factor `8·lhyC·X^{311/2}` is `≤ 10^{-298}` on the diluteness window.

The arithmetic splits into the two scalar rows `ErrResRegimeAFSNet` and
`ErrResRegimeAFSLHY` (the `FarCondFS` siblings of `ErrResRegimeA`); the regime `2μ ≤ ρ`
needs no new arithmetic, because there `|ρ−μ| ≥ μ ≥ closeThreshold`, i.e. the old
`FarCond` holds and `RB5FSArith2` applies verbatim.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false
-- the numeric slacks below are `10^{300}·10^{-400} ≤ 10^{-100}`, so `norm_num` has to be
-- allowed to evaluate powers of `10` with exponent up to `4000`
set_option exponentiation.threshold 5000

/-! ## 0. The two interface bridges -/

/-- The corrected close threshold is the old one divided by the universal factor `2¹⁴π`:
`closeThreshold = (2¹⁴π)·closeThresholdFS`. -/
lemma closeThreshold_eq_mul_closeThresholdFS (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) :
    closeThreshold v μ = ((2 : ℝ) ^ 14 * Real.pi) * Work.BoseBoxFock.closeThresholdFS v μ := by
  have hne : ((2 : ℝ) ^ 14 * Real.pi) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  rw [Work.BoseBoxFock.closeThresholdFS, closeThreshold]
  field_simp

/-- `√(dil v μ) = X^{323/2}` (`X = fsX v μ = (μa³)^{1/323}`): the form in which the LHY
margin is paid at the corrected threshold. -/
lemma sqrt_dil_eq_fsX_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < a v) :
    Real.sqrt (dil v μ) = (fsX v μ) ^ (323 / 2 : ℝ) := by
  have ht0 : 0 < dil v μ := by rw [dil]; positivity
  rw [fsX, Work.BoseBox.fsXp, Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
  congr 1
  norm_num

/-! ## 1. The scalar rows of the corrected far regime -/

/-- **The square of the corrected far condition.**  `μ²X⁶ ≤ (2¹⁴π)²(ρ−μ)²`: the factor
`(2¹⁴π)² ≈ 2.65·10⁹` which the old `μX³ ≤ |ρ−μ|` did not carry, and which the slack
`10³⁰⁰·X^{289/8} ≤ 10^{-100}` has to absorb below. -/
private lemma muSqX6_le {μ ρ X : ℝ} (hμ : 0 < μ) (hX0 : 0 < X)
    (hfar : μ * X ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ|) :
    μ ^ 2 * X ^ 6 ≤ ((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2 := by
  have hnn : (0 : ℝ) ≤ μ * X ^ 3 := by positivity
  have h2 := pow_le_pow_left₀ hnn hfar 2
  rw [show (μ * X ^ 3) ^ 2 = μ ^ 2 * X ^ 6 by ring, mul_pow, sq_abs] at h2
  exact h2

/-- `X^a = X^b · X^6` when `a = b + 6`. -/
private lemma rpow_split_six {X a b : ℝ} (hX0 : 0 < X) (h : a = b + 6) :
    X ^ a = X ^ b * X ^ 6 := by
  rw [h, Real.rpow_add hX0, Real.rpow_ofNat]

/-- `X^a = X^b · X^3` when `a = b + 3`. -/
private lemma rpow_split_three {X a b : ℝ} (hX0 : 0 < X) (h : a = b + 3) :
    X ^ a = X ^ b * X ^ 3 := by
  rw [h, Real.rpow_add hX0, Real.rpow_ofNat]

/-- **The `ErrRes` and `n₊` rows at the corrected threshold.**  With the `A`- and `L³`-factors
stripped off, the two `ErrRes` monomials and the `n₊`-slot row are dominated by `3π(ρ−μ)²`.
Each is in fact `≤ (ρ−μ)²`: the powers `X^{337/4}`, `X^{337/8}`, `X^{337/4}` are split as
`X^{313/4}X⁶`, `X^{289/8}X⁶`, `X^{325/4}X³`, and the resulting `μ²X⁶ ≤ (2¹⁴π)²(ρ−μ)²`,
`μX³ ≤ (2¹⁴π)|ρ−μ|` are paid by the slack `10³⁰⁰X^{289/8} ≤ 10^{-100}`. -/
private lemma errResRegimeAFSNet_core {μ ρ X : ℝ}
    (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2 * μ)
    (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hfar : μ * X ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ|)
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ))) :
    (10 : ℝ) ^ 300 * ((ρ + μ) * (X ^ (337 / 4 : ℝ) * μ)
        + (ρ + μ) ^ (3 / 2 : ℝ) * (X ^ (337 / 8 : ℝ) * Real.sqrt μ))
      + 256 * Real.pi * |ρ - μ| * (X ^ (337 / 4 : ℝ) * μ)
      ≤ 3 * Real.pi * (ρ - μ) ^ 2 := by
  have hS2 : μ ^ 2 * X ^ 6 ≤ ((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2 :=
    muSqX6_le hμ hX0 hfar
  -- the absolute bounds on the constants
  have hc2 : ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ (10 : ℝ) ^ 10 := by
    have hp : Real.pi < 4 := Real.pi_lt_four
    have h14 : ((2 : ℝ) ^ 14 : ℝ) = 16384 := by norm_num
    have h1 : (2 : ℝ) ^ 14 * Real.pi ≤ (10 : ℝ) ^ 5 := by
      rw [h14]; nlinarith [hp, Real.pi_pos]
    calc ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ ((10 : ℝ) ^ 5) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = (10 : ℝ) ^ 10 := by norm_num
  have hc8 : 256 * Real.pi * ((2 : ℝ) ^ 14 * Real.pi) ≤ (10 : ℝ) ^ 8 := by
    have hp : Real.pi < 4 := Real.pi_lt_four
    have h14 : ((2 : ℝ) ^ 14 : ℝ) = 16384 := by norm_num
    rw [h14]; nlinarith [hp, Real.pi_pos]
  have h10 : (0 : ℝ) < (10 : ℝ) ^ 300 := by norm_num
  -- the three slack bounds
  have hnum1 : 3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ 1 := by
    have hmono : X ^ (313 / 4 : ℝ) ≤ X ^ (289 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num)
    have hs : (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ)) :=
      le_trans (mul_le_mul_of_nonneg_left hmono h10.le) hslack
    calc 3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2
        = 3 * ((10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ)) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 := by ring
      _ ≤ 3 * (10 : ℝ) ^ (-(100 : ℤ)) * (10 : ℝ) ^ 10 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hc2
            (by positivity) (by positivity)
      _ ≤ 1 := by norm_num
  have hnum2 : 6 * (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ 1 := by
    calc 6 * (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2
        = 6 * ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 := by ring
      _ ≤ 6 * (10 : ℝ) ^ (-(100 : ℤ)) * (10 : ℝ) ^ 10 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hslack (by norm_num)) hc2
            (by positivity) (by positivity)
      _ ≤ 1 := by norm_num
  have hnum3 : 256 * Real.pi * ((2 : ℝ) ^ 14 * Real.pi) * X ^ (325 / 4 : ℝ) ≤ 1 := by
    have hmono : X ^ (325 / 4 : ℝ) ≤ X ^ (289 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num)
    have hone : (1 : ℝ) ≤ (10 : ℝ) ^ 300 := one_le_pow₀ (by norm_num)
    have h1 : X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ)) := by
      calc X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) := by
            nlinarith [Real.rpow_nonneg hX0.le (289 / 8 : ℝ), hone]
        _ ≤ (10 : ℝ) ^ (-(100 : ℤ)) := hslack
    calc 256 * Real.pi * ((2 : ℝ) ^ 14 * Real.pi) * X ^ (325 / 4 : ℝ)
        ≤ 256 * Real.pi * ((2 : ℝ) ^ 14 * Real.pi) * X ^ (289 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ (10 : ℝ) ^ 8 * (10 : ℝ) ^ (-(100 : ℤ)) :=
          mul_le_mul hc8 h1 (Real.rpow_nonneg hX0.le _) (by positivity)
      _ ≤ 1 := by norm_num
  -- `(ρ+μ)^{3/2}√μ ≤ 6μ²`
  have hM2 : (ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt μ ≤ 6 * μ ^ 2 := by
    have h0 : (0 : ℝ) ≤ ρ + μ := by linarith
    have h3 : ρ + μ ≤ 3 * μ := by linarith
    have h1 : (ρ + μ) ^ (3 / 2 : ℝ) = Real.sqrt ((ρ + μ) ^ 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (ρ + μ) 3, ← Real.rpow_mul h0]
      norm_num
    have h2 : Real.sqrt ((ρ + μ) ^ 3) * Real.sqrt μ = Real.sqrt ((ρ + μ) ^ 3 * μ) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (ρ + μ) ^ 3)]
    rw [h1, h2]
    have hcube : (ρ + μ) ^ 3 ≤ (3 * μ) ^ 3 := pow_le_pow_left₀ h0 h3 3
    have hmain : (ρ + μ) ^ 3 * μ ≤ 27 * μ ^ 4 := by
      calc (ρ + μ) ^ 3 * μ ≤ (3 * μ) ^ 3 * μ := mul_le_mul_of_nonneg_right hcube hμ.le
        _ = 27 * μ ^ 4 := by ring
    refine le_trans (Real.sqrt_le_sqrt hmain) ?_
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 27) (μ ^ 4)]
    have h4 : Real.sqrt (μ ^ 4) = μ ^ 2 := by
      rw [show (μ : ℝ) ^ 4 = (μ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [h4]
    have h27 : Real.sqrt 27 ≤ 6 := by
      rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
    nlinarith [sq_nonneg μ, Real.sqrt_nonneg 27]
  -- the three termwise bounds
  have ht1 : (10 : ℝ) ^ 300 * ((ρ + μ) * (X ^ (337 / 4 : ℝ) * μ)) ≤ (ρ - μ) ^ 2 := by
    have h3 : ρ + μ ≤ 3 * μ := by linarith
    calc (10 : ℝ) ^ 300 * ((ρ + μ) * (X ^ (337 / 4 : ℝ) * μ))
        = (10 : ℝ) ^ 300 * ((ρ + μ) * ((X ^ (313 / 4 : ℝ) * X ^ 6) * μ)) := by
          rw [rpow_split_six hX0 (by norm_num : (337 : ℝ) / 4 = 313 / 4 + 6)]
      _ ≤ (10 : ℝ) ^ 300 * ((3 * μ) * ((X ^ (313 / 4 : ℝ) * X ^ 6) * μ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ)) * (μ ^ 2 * X ^ 6) := by ring
      _ ≤ (3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ))
            * (((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2) :=
          mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = (3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2)
            * (ρ - μ) ^ 2 := by ring
      _ ≤ 1 * (ρ - μ) ^ 2 := mul_le_mul_of_nonneg_right hnum1 (sq_nonneg _)
      _ = (ρ - μ) ^ 2 := by ring
  have ht2 : (10 : ℝ) ^ 300 * ((ρ + μ) ^ (3 / 2 : ℝ) * (X ^ (337 / 8 : ℝ) * Real.sqrt μ))
      ≤ (ρ - μ) ^ 2 := by
    calc (10 : ℝ) ^ 300 * ((ρ + μ) ^ (3 / 2 : ℝ) * (X ^ (337 / 8 : ℝ) * Real.sqrt μ))
        = (10 : ℝ) ^ 300 * (((ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt μ) * X ^ (337 / 8 : ℝ)) := by ring
      _ ≤ (10 : ℝ) ^ 300 * ((6 * μ ^ 2) * X ^ (337 / 8 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hM2 (Real.rpow_nonneg hX0.le _)
      _ = (10 : ℝ) ^ 300 * ((6 * μ ^ 2) * (X ^ (289 / 8 : ℝ) * X ^ 6)) := by
          rw [rpow_split_six hX0 (by norm_num : (337 : ℝ) / 8 = 289 / 8 + 6)]
      _ = (6 * (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)) * (μ ^ 2 * X ^ 6) := by ring
      _ ≤ (6 * (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ))
            * (((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2) :=
          mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = (6 * (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2)
            * (ρ - μ) ^ 2 := by ring
      _ ≤ 1 * (ρ - μ) ^ 2 := mul_le_mul_of_nonneg_right hnum2 (sq_nonneg _)
      _ = (ρ - μ) ^ 2 := by ring
  have ht3 : 256 * Real.pi * |ρ - μ| * (X ^ (337 / 4 : ℝ) * μ) ≤ (ρ - μ) ^ 2 := by
    have hnn : (0 : ℝ) ≤ |ρ - μ| := abs_nonneg _
    calc 256 * Real.pi * |ρ - μ| * (X ^ (337 / 4 : ℝ) * μ)
        = 256 * Real.pi * |ρ - μ| * ((X ^ (325 / 4 : ℝ) * X ^ 3) * μ) := by
          rw [rpow_split_three hX0 (by norm_num : (337 : ℝ) / 4 = 325 / 4 + 3)]
      _ = (256 * Real.pi * X ^ (325 / 4 : ℝ)) * (|ρ - μ| * (μ * X ^ 3)) := by ring
      _ ≤ (256 * Real.pi * X ^ (325 / 4 : ℝ))
            * (|ρ - μ| * (((2 : ℝ) ^ 14 * Real.pi) * |ρ - μ|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hfar hnn
      _ = (256 * Real.pi * ((2 : ℝ) ^ 14 * Real.pi) * X ^ (325 / 4 : ℝ)) * (ρ - μ) ^ 2 := by
          rw [← sq_abs]; ring
      _ ≤ 1 * (ρ - μ) ^ 2 := mul_le_mul_of_nonneg_right hnum3 (sq_nonneg _)
      _ = (ρ - μ) ^ 2 := by ring
  nlinarith [ht1, ht2, ht3, Real.pi_gt_three, sq_nonneg (ρ - μ)]

/-- **The `ErrRes`/`n₊` budget at the corrected far threshold** (`FarCondFS` sibling of
`ErrResRegimeA`): the two monomials of `10³⁰⁰·(...)` and the `n₊`-slot row fit into `3π` of
the margin `4πA(ρ−μ)²L³`. -/
theorem ErrResRegimeAFSNet {A μ ρ L M X : ℝ}
    (hA : 0 < A) (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2 * μ)
    (hL : 0 < L) (hM : 0 < M) (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hfar : μ * X ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ|)
    (hML : M = X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ))) :
    (10 : ℝ) ^ 300 * ((ρ + μ) * A * M
        + (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M))
      + |ρ - μ| * (256 * Real.pi * A * M)
      ≤ 3 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by
  have hsqrt : Real.sqrt (L ^ 3 * M) = L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ := by
    rw [hML]
    have hsq : X ^ (337 / 4 : ℝ) = (X ^ (337 / 8 : ℝ)) ^ 2 := by
      rw [sq, ← Real.rpow_add hX0]; norm_num
    have hs1 : Real.sqrt (X ^ (337 / 4 : ℝ)) = X ^ (337 / 8 : ℝ) := by
      rw [hsq, Real.sqrt_sq (Real.rpow_nonneg hX0.le _)]
    have hs2 : Real.sqrt (L ^ 6 * (X ^ (337 / 4 : ℝ) * μ))
        = L ^ 3 * Real.sqrt (X ^ (337 / 4 : ℝ) * μ) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ L ^ 6),
          show L ^ 6 = (L ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ L ^ 3)]
    have hs3 : Real.sqrt (X ^ (337 / 4 : ℝ) * μ) = X ^ (337 / 8 : ℝ) * Real.sqrt μ := by
      rw [Real.sqrt_mul (Real.rpow_nonneg hX0.le _), hs1]
    calc Real.sqrt (L ^ 3 * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
        = Real.sqrt (L ^ 6 * (X ^ (337 / 4 : ℝ) * μ)) := by
          rw [show L ^ 3 * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
                = L ^ 6 * (X ^ (337 / 4 : ℝ) * μ) by ring]
      _ = L ^ 3 * Real.sqrt (X ^ (337 / 4 : ℝ) * μ) := hs2
      _ = L ^ 3 * (X ^ (337 / 8 : ℝ) * Real.sqrt μ) := by rw [hs3]
      _ = L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ := by ring
  rw [hsqrt, hML]
  have hAL : (0 : ℝ) ≤ A * L ^ 3 := by positivity
  calc (10 : ℝ) ^ 300 * ((ρ + μ) * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
          + (ρ + μ) ^ (3 / 2 : ℝ) * A * (L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ))
        + |ρ - μ| * (256 * Real.pi * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
      = (A * L ^ 3) * ((10 : ℝ) ^ 300 * ((ρ + μ) * (X ^ (337 / 4 : ℝ) * μ)
            + (ρ + μ) ^ (3 / 2 : ℝ) * (X ^ (337 / 8 : ℝ) * Real.sqrt μ))
          + 256 * Real.pi * |ρ - μ| * (X ^ (337 / 4 : ℝ) * μ)) := by ring
    _ ≤ (A * L ^ 3) * (3 * Real.pi * (ρ - μ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (errResRegimeAFSNet_core hμ hρ hρ2 hX0 hX1 hfar hslack) hAL
    _ = 3 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by ring

/-- **The LHY margin at the corrected far threshold.**  In the form of the definition,
`errLHY = 8π·lhyC·μ²aℓ³√(dil) = 8π·lhyC·μ²aℓ³·X^{323/2}`, the LHY row fits into `π` of the
margin `4πA(ρ−μ)²L³`: `μ²X^{323/2} = X^{311/2}·μ²X⁶ ≤ X^{311/2}(2¹⁴π)²(ρ−μ)²` and
`8·lhyC·X^{311/2}(2¹⁴π)² ≤ 10^{-87} ≤ 1` by the slack. -/
theorem ErrResRegimeAFSLHY {A μ ρ L X : ℝ}
    (hA : 0 < A) (hμ : 0 < μ) (hL : 0 < L) (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hfar : μ * X ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ|)
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ))) :
    8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * X ^ (323 / 2 : ℝ)
      ≤ Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by
  have hl0 : (0 : ℝ) ≤ Work.UBB.lhyC := by
    rw [Work.UBB.lhyC]; positivity
  have hS2 : μ ^ 2 * X ^ 6 ≤ ((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2 :=
    muSqX6_le hμ hX0 hfar
  have hnum : 8 * Work.UBB.lhyC * X ^ (311 / 2 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ 1 := by
    have hl : Work.UBB.lhyC ≤ 100 := lhyC_le_hundred
    have hc2 : ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ (10 : ℝ) ^ 10 := by
      have hp : Real.pi < 4 := Real.pi_lt_four
      have h14 : ((2 : ℝ) ^ 14 : ℝ) = 16384 := by norm_num
      have h1 : (2 : ℝ) ^ 14 * Real.pi ≤ (10 : ℝ) ^ 5 := by
        rw [h14]; nlinarith [hp, Real.pi_pos]
      calc ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ ((10 : ℝ) ^ 5) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h1 2
        _ = (10 : ℝ) ^ 10 := by norm_num
    have hone : (1 : ℝ) ≤ (10 : ℝ) ^ 300 := one_le_pow₀ (by norm_num)
    have h1 : X ^ (311 / 2 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ)) := by
      calc X ^ (311 / 2 : ℝ) ≤ X ^ (289 / 8 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num)
        _ ≤ (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) := by
            nlinarith [Real.rpow_nonneg hX0.le (289 / 8 : ℝ), hone]
        _ ≤ (10 : ℝ) ^ (-(100 : ℤ)) := hslack
    calc 8 * Work.UBB.lhyC * X ^ (311 / 2 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2
        = 8 * Work.UBB.lhyC * X ^ (311 / 2 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 := rfl
      _ ≤ 8 * 100 * (10 : ℝ) ^ (-(100 : ℤ)) * (10 : ℝ) ^ 10 := by
          gcongr
      _ ≤ 1 := by norm_num
  calc 8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * X ^ (323 / 2 : ℝ)
      = Real.pi * A * L ^ 3 * (8 * Work.UBB.lhyC * (X ^ (311 / 2 : ℝ) * (μ ^ 2 * X ^ 6))) := by
        rw [rpow_split_six hX0 (by norm_num : (323 : ℝ) / 2 = 311 / 2 + 6)]
        ring
    _ ≤ Real.pi * A * L ^ 3
          * (8 * Work.UBB.lhyC * (X ^ (311 / 2 : ℝ)
              * (((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by linarith [hl0])
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX0.le _)
        exact hS2
    _ = Real.pi * A * L ^ 3
          * ((8 * Work.UBB.lhyC * X ^ (311 / 2 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2)
              * (ρ - μ) ^ 2) := by ring
    _ ≤ Real.pi * A * L ^ 3 * (1 * (ρ - μ) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnum (sq_nonneg _)) (by positivity)
    _ = Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by ring

/-! ## 2. The assembled statement -/

theorem RB5FSArith2FS {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < BoseGases.a v)
    {ε₀ μ ρ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hρ : 0 ≤ ρ) (hfar : Work.BoseBoxFock.FarCondFS v μ ρ) :
    Work.BoseFixR.ErrRes v μ ρ
      + |ρ - μ| * (16 * Real.pi * BoseGases.a v) * (16 * Work.BoseFixR.bigMV v μ)
      + Work.BoseFixR.errLHY v μ
      ≤ 4 * Real.pi * BoseGases.a v * (ρ - μ) ^ 2 * Work.BoseFixR.ell v μ ^ 3 := by
  have hAdm' : Work.BoseBoxFix.Adm v ε₀ μ := hAdm
  obtain ⟨hμ, hdilε₀, -⟩ := hAdm
  have hdil : dil v μ ≤ (10 : ℝ) ^ (-(4000 : ℤ)) := le_trans hdilε₀ hε₀
  have ht0 : 0 < dil v μ := by rw [dil]; positivity
  have ht1 : dil v μ ≤ 1 := le_trans hdil (by norm_num)
  have hell : 0 < ell v μ := by
    rw [ell, sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact mul_pos (Work.BoseBox.fsXp_pos ht0) (Real.rpow_pos_of_pos (by positivity) _)
  -- FS's `X = (μa³)^{1/323}`
  set X := fsX v μ with hXdef
  have hX0 : 0 < X := by
    rw [hXdef, fsX, Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos ht0 _
  have hX1 : X ≤ 1 := by
    rw [hXdef, fsX, Work.BoseBox.fsXp]
    calc (dil v μ) ^ (1 / 323 : ℝ) ≤ 1 ^ (1 / 323 : ℝ) :=
          Real.rpow_le_rpow ht0.le ht1 (by norm_num)
      _ = 1 := by norm_num
  -- the FS identity `𝓜 = X^{337/4}·μℓ³`
  have hML : bigMV v μ = X ^ (337 / 4 : ℝ) * (μ * ell v μ ^ 3) := by
    rw [hXdef]; exact BigMVRatio hav hμ
  have hM0 : 0 < bigMV v μ := by rw [hML]; positivity
  -- the numeric slack `10³⁰⁰·X^{289/8} ≤ 10^{-100}`
  have hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ)) := by
    have hb : X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(400 : ℤ)) := by
      rw [hXdef]; exact FsXPowBound hav hμ hdil
    calc (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)
        ≤ (10 : ℝ) ^ 300 * (10 : ℝ) ^ (-(400 : ℤ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (10 : ℝ) ^ (-(100 : ℤ)) := by norm_num
  -- reassociate the `n₊`-slot error into the children's normal form
  have hkey : Work.BoseFixR.ErrRes v μ ρ
        + |ρ - μ| * (16 * Real.pi * BoseGases.a v) * (16 * bigMV v μ)
        + Work.BoseFixR.errLHY v μ
      = (10 : ℝ) ^ 300 * ((ρ + μ) * BoseGases.a v * bigMV v μ
            + (ρ + μ) ^ (3 / 2 : ℝ) * BoseGases.a v
                * Real.sqrt (ell v μ ^ 3 * bigMV v μ))
          + |ρ - μ| * (256 * Real.pi * BoseGases.a v * bigMV v μ)
          + Work.BoseFixR.errLHY v μ := by
    rw [ErrRes]
    ring
  rw [hkey]
  rcases le_total ρ (2 * μ) with hc | hc
  · -- ## regime A: `ρ ≤ 2μ` (the region opened by the corrected threshold)
    have hcl : closeThreshold v μ = μ * (dil v μ) ^ (3 / 323 : ℝ) := by
      rw [closeThreshold, Kl_inv_sq v hμ hav]
    have hX3 : X ^ 3 = (dil v μ) ^ (3 / 323 : ℝ) := by
      rw [hXdef, fsX, Work.BoseBox.fsXp, ← Real.rpow_natCast (dil v μ ^ (1 / 323 : ℝ)) 3,
        ← Real.rpow_mul ht0.le]
      congr 1
      norm_num
    -- the corrected threshold compared with `μX³ = closeThreshold`
    have hfarX : μ * X ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ| := by
      have hmul := mul_le_mul_of_nonneg_right hfar
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 14 * Real.pi)
      have h1 : closeThreshold v μ ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ| := by
        rw [closeThreshold_eq_mul_closeThresholdFS v μ]
        calc ((2 : ℝ) ^ 14 * Real.pi) * Work.BoseBoxFock.closeThresholdFS v μ
            = Work.BoseBoxFock.closeThresholdFS v μ * ((2 : ℝ) ^ 14 * Real.pi) := by ring
          _ ≤ |ρ - μ| * ((2 : ℝ) ^ 14 * Real.pi) := hmul
          _ = (2 : ℝ) ^ 14 * Real.pi * |ρ - μ| := by ring
      rw [hX3, ← hcl]
      exact h1
    have hnet := ErrResRegimeAFSNet (A := BoseGases.a v) (μ := μ) (ρ := ρ) (L := ell v μ)
        (M := bigMV v μ) (X := X) hav hμ hρ hc hell hM0 hX0 hX1 hfarX hML hslack
    have hlhy := ErrResRegimeAFSLHY (A := BoseGases.a v) (μ := μ) (ρ := ρ) (L := ell v μ)
        (X := X) hav hμ hell hX0 hX1 hfarX hslack
    have hsq : Real.sqrt (dil v μ) = X ^ (323 / 2 : ℝ) := by
      rw [hXdef]
      exact sqrt_dil_eq_fsX_rpow hμ hav
    have hE : Work.BoseFixR.errLHY v μ
        = 8 * Real.pi * lhyC * BoseGases.a v * μ ^ 2 * ell v μ ^ 3 * X ^ (323 / 2 : ℝ) := by
      rw [errLHY, ell3, hsq]
      ring
    linarith [hnet, hlhy, hE.le]
  · -- ## regime B: `2μ ≤ ρ` — there `closeThreshold ≤ μ ≤ |ρ−μ|`, i.e. the old `FarCond`
    have hFar : Work.BoseFixR.FarCond v μ ρ := by
      rw [FarCond, closeThreshold, Kl_inv_sq v hμ hav,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ - μ)]
      have hdt : (dil v μ) ^ (3 / 323 : ℝ) ≤ 1 := Real.rpow_le_one ht0.le ht1 (by norm_num)
      have h1 := mul_le_mul_of_nonneg_left hdt hμ.le
      linarith [h1, hc]
    rw [← hkey]
    exact RB5FSArith2 hav hε₀ hAdm' hρ hFar

end Work.BoseFixR
