import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixR.RB5FSArith2FS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/farArithExtra.lean` — the far-leg arithmetic with a state energy `E`

The frozen far-leg bound `Work.BoseFixR.RB5FSArith2FS` pays the residual `ErrRes`, the
`n₊`-slot row `|ρ−μ|·256πA𝓜` and the LHY margin out of the pair-condensate slack
`4πA(ρ−μ)²L³`, but *without* a contribution of the state's own energy `E`.

Here the same interface is consumed with an extra summand `E ≤ 4A(ρ−μ)²L³` (the crude
energy bound of the localised word), so the three rows above must fit into the *remaining*
margin `4(π−1)A(ρ−μ)²L³ ≈ 8.567·A(ρ−μ)²L³` instead of the whole `4π`.  The sibling's
own public rows are too coarse for that (`ErrResRegimeAFSNet` pays `3π ≈ 9.42`, and the
LHY row a further `π`, leaving nothing for `E`).  The present file re-proves the rows with
the crude (and very lossy, but sufficient) bound `(1/25)·A(ρ−μ)²L³`:

with `X ≤ 1` and `10³⁰⁰X^{289/8} ≤ 10^{−100}` (hence `X^q ≤ 10^{−400}` for every
`q ≥ 289/8`), `M = X^{337/4}(μL³)`, so `√(L³M) = L³X^{337/8}√μ`, and `μX³ ≤ 2¹⁴π|ρ−μ|`:

* **regime A** (`ρ ≤ 2μ`): `ρ+μ ≤ 3μ`, `(ρ+μ)^{3/2}√μ ≤ 6μ²`, and `μ²X^6 ≤ (2¹⁴π)²(ρ−μ)²`;
  splitting `X^{337/4} = X^{313/4}X^6`, `X^{337/8} = X^{289/8}X^6`, `X^{337/4} = X^{325/4}X³`
  and `X^{323/2} = X^{311/2}X^6` every row becomes `(tiny)·(A(ρ−μ)²L³)`;
* **regime B** (`2μ ≤ ρ`): `μ ≤ |ρ−μ|` and `ρ ≤ 2|ρ−μ|`, so `ρ+μ ≤ 3|ρ−μ|` and the rows
  are bounded directly by powers of `X` times `A(ρ−μ)²L³`.

Finally `(1/25) + 4 = 101/25 < 4π` closes the target.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
-- the numeric slacks are `10^{300}·10^{-400} ≤ 10^{-100}`, so `norm_num` must be able to
-- evaluate powers of `10` with exponent up to `4000`
set_option exponentiation.threshold 5000
set_option maxHeartbeats 1000000

/-! ## 0. Numerical and elementary preliminaries -/

/-- `(2¹⁴π)² ≤ 10¹⁰`: the only numerical bound on `π` needed at the cube. -/
private lemma two14pi_sq_le_ten10 : ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ (10 : ℝ) ^ 10 := by
  have hp : Real.pi < 4 := Real.pi_lt_four
  have h14 : ((2 : ℝ) ^ 14 : ℝ) = 16384 := by norm_num
  have h1 : (2 : ℝ) ^ 14 * Real.pi ≤ (10 : ℝ) ^ 5 := by rw [h14]; nlinarith [hp, Real.pi_pos]
  calc ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ ((10 : ℝ) ^ 5) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ = (10 : ℝ) ^ 10 := by norm_num

/-- `2¹⁴π ≤ 10⁵`. -/
private lemma two14pi_le_ten5 : (2 : ℝ) ^ 14 * Real.pi ≤ (10 : ℝ) ^ 5 := by
  have hp : Real.pi < 4 := Real.pi_lt_four
  have h14 : ((2 : ℝ) ^ 14 : ℝ) = 16384 := by norm_num
  rw [h14]; nlinarith [hp, Real.pi_pos]

/-- `0 ≤ lhyC`. -/
private lemma lhyC_nonneg : (0 : ℝ) ≤ Work.UBB.lhyC := by
  rw [Work.UBB.lhyC]; positivity

/-- `3^{3/2} = 3√3 ≤ 6`. -/
private lemma three_rpow_three_halves_le_six : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 6 := by
  have h1 : (3 : ℝ) ^ (3 / 2 : ℝ) = 3 * Real.sqrt 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h1]
  have h2 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  linarith

/-- **The single numeric slack.**  From `10³⁰⁰·X^{289/8} ≤ 10^{−100}` we get `X^q ≤ 10^{−400}`
for every exponent `q ≥ 289/8` (`0 < X ≤ 1` makes `X ↦ X^q` antitone). -/
private lemma Xpow_le_ten_neg400 {X q : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ)))
    (hq : (289 / 8 : ℝ) ≤ q) : X ^ q ≤ 1 / (10 : ℝ) ^ 400 := by
  have hsl : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ 1 / (10 : ℝ) ^ 100 := by
    simpa only [show (10 : ℝ) ^ (-(100 : ℤ)) = 1 / (10 : ℝ) ^ 100 by norm_num] using hslack
  have h400 : X ^ (289 / 8 : ℝ) ≤ 1 / (10 : ℝ) ^ 400 := by
    have h : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ 300 * (1 / (10 : ℝ) ^ 400) := by
      rw [show (10 : ℝ) ^ 300 * (1 / (10 : ℝ) ^ 400) = 1 / (10 : ℝ) ^ 100 by norm_num]
      exact hsl
    exact le_of_mul_le_mul_left h (by norm_num)
  exact le_trans (Real.rpow_le_rpow_of_exponent_ge hX0 hX1 hq) h400

/-- The same slack in the form `10³⁰⁰·X^q ≤ 10^{−100}` for `q ≥ 289/8`. -/
private lemma ten300_Xpow_le {X q : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ)))
    (hq : (289 / 8 : ℝ) ≤ q) : (10 : ℝ) ^ 300 * X ^ q ≤ 1 / (10 : ℝ) ^ 100 := by
  have hsl : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ 1 / (10 : ℝ) ^ 100 := by
    simpa only [show (10 : ℝ) ^ (-(100 : ℤ)) = 1 / (10 : ℝ) ^ 100 by norm_num] using hslack
  exact le_trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hX0 hX1 hq) (by positivity)) hsl

/-- **The square of the far condition.**  `μ²X⁶ ≤ (2¹⁴π)²(ρ−μ)²`. -/
private lemma muSqX6_le {μ ρ X : ℝ} (hμ : 0 < μ) (hX0 : 0 < X)
    (hfar : μ * X ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ|) :
    μ ^ 2 * X ^ 6 ≤ ((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2 := by
  have hnn : (0 : ℝ) ≤ μ * X ^ 3 := by positivity
  have h2 := pow_le_pow_left₀ hnn hfar 2
  rw [show (μ * X ^ 3) ^ 2 = μ ^ 2 * X ^ 6 by ring, mul_pow, sq_abs] at h2
  exact h2

/-- `(ρ+μ)^{3/2}√μ ≤ 6μ²` in the near regime `ρ+μ ≤ 3μ`. -/
private lemma s32_sqrt_le {ρ μ : ℝ} (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hpm : ρ + μ ≤ 3 * μ) :
    (ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt μ ≤ 6 * μ ^ 2 := by
  have h0 : (0 : ℝ) ≤ ρ + μ := by linarith
  have h1 : (ρ + μ) ^ (3 / 2 : ℝ) = Real.sqrt ((ρ + μ) ^ 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (ρ + μ) 3, ← Real.rpow_mul h0]
    norm_num
  have h2 : Real.sqrt ((ρ + μ) ^ 3) * Real.sqrt μ = Real.sqrt ((ρ + μ) ^ 3 * μ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (ρ + μ) ^ 3)]
  rw [h1, h2]
  have hcube : (ρ + μ) ^ 3 ≤ (3 * μ) ^ 3 := pow_le_pow_left₀ h0 hpm 3
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

/-- The square root of the window mass: `√(L³𝓜) = L³X^{337/8}√μ` when `𝓜 = X^{337/4}(μL³)`. -/
private lemma sqrt_L3M_eq {L M X μ : ℝ} (hL : 0 < L) (hX0 : 0 < X) (hμ : 0 < μ)
    (hML : M = X ^ (337 / 4 : ℝ) * (μ * L ^ 3)) :
    Real.sqrt (L ^ 3 * M) = L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ := by
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

/-! ## 1. The three rows fit into `(1/25)·A(ρ−μ)²L³` -/

/-- **The far rows at the corrected threshold, with room for the state energy.**  The three
monomials (the two `10³⁰⁰`-rows of the localised error budget and the `n₊`-slot row) and the
LHY row `8π·lhyC·Aμ²L³X^{323/2}` are together dominated by `(1/25)·A(ρ−μ)²L³`; this leaves
`4A(ρ−μ)²L³` for `E` inside the margin `4πA(ρ−μ)²L³`. -/
private lemma farRows_le_fraction {A μ ρ L M X : ℝ}
    (hA : 0 < A) (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hL : 0 < L)
    (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hfar : μ * X ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ|)
    (hML : M = X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ))) :
    (10 : ℝ) ^ 300 * ((ρ + μ) * A * M
        + (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M))
      + |ρ - μ| * (256 * Real.pi * A * M)
      + 8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * X ^ (323 / 2 : ℝ)
      ≤ (1 / 25) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
  have hsqrt : Real.sqrt (L ^ 3 * M) = L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ :=
    sqrt_L3M_eq hL hX0 hμ hML
  rw [hsqrt, hML]
  -- the shared elementary facts
  have hsl : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ 1 / (10 : ℝ) ^ 100 := by
    simpa only [show (10 : ℝ) ^ (-(100 : ℤ)) = 1 / (10 : ℝ) ^ 100 by norm_num] using hslack
  have hs2 : μ ^ 2 * X ^ 6 ≤ ((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2 :=
    muSqX6_le hμ hX0 hfar
  have hlhyC : Work.UBB.lhyC ≤ 100 := lhyC_le_hundred
  have hlhyC0 : (0 : ℝ) ≤ Work.UBB.lhyC := lhyC_nonneg
  -- the eight numerical slacks
  have hA1 : 3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ 1 / 100 := by
    have h := ten300_Xpow_le hX0 hX1 hslack (q := 313 / 4) (by norm_num)
    calc 3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2
        = 3 * ((10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ)) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 := by ring
      _ ≤ 3 * (1 / (10 : ℝ) ^ 100) * (10 : ℝ) ^ 10 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h (by norm_num)) two14pi_sq_le_ten10
            (by positivity) (by positivity)
      _ ≤ 1 / 100 := by norm_num
  have hA2 : 6 * ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ 1 / 100 := by
    calc 6 * ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2
        ≤ 6 * (1 / (10 : ℝ) ^ 100) * (10 : ℝ) ^ 10 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsl (by norm_num)) two14pi_sq_le_ten10
            (by positivity) (by positivity)
      _ ≤ 1 / 100 := by norm_num
  have hA3 : 256 * Real.pi * X ^ (325 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ≤ 1 / 100 := by
    have h := Xpow_le_ten_neg400 hX0 hX1 hslack (q := 325 / 4) (by norm_num)
    have h1 : X ^ (325 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ≤ (1 / (10 : ℝ) ^ 400) * (10 : ℝ) ^ 5 :=
      mul_le_mul h two14pi_le_ten5 (by positivity) (by positivity)
    have hp : 256 * Real.pi ≤ (10 : ℝ) ^ 4 := by
      have := Real.pi_lt_four; nlinarith [Real.pi_pos]
    calc 256 * Real.pi * X ^ (325 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi)
        = (256 * Real.pi) * (X ^ (325 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi)) := by ring
      _ ≤ (10 : ℝ) ^ 4 * ((1 / (10 : ℝ) ^ 400) * (10 : ℝ) ^ 5) :=
          mul_le_mul hp h1 (by positivity) (by positivity)
      _ ≤ 1 / 100 := by norm_num
  have hA4 : 8 * Real.pi * Work.UBB.lhyC * X ^ (311 / 2 : ℝ)
      * ((2 : ℝ) ^ 14 * Real.pi) ^ 2 ≤ 1 / 100 := by
    have h := Xpow_le_ten_neg400 hX0 hX1 hslack (q := 311 / 2) (by norm_num)
    have h1 : X ^ (311 / 2 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2
        ≤ (1 / (10 : ℝ) ^ 400) * (10 : ℝ) ^ 10 :=
      mul_le_mul h two14pi_sq_le_ten10 (by positivity) (by positivity)
    have hp : 8 * Real.pi * Work.UBB.lhyC ≤ (10 : ℝ) ^ 5 := by
      nlinarith [Real.pi_lt_four, Real.pi_pos, hlhyC, hlhyC0]
    calc 8 * Real.pi * Work.UBB.lhyC * X ^ (311 / 2 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2
        = (8 * Real.pi * Work.UBB.lhyC) * (X ^ (311 / 2 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2) := by
          ring
      _ ≤ (10 : ℝ) ^ 5 * ((1 / (10 : ℝ) ^ 400) * (10 : ℝ) ^ 10) :=
          mul_le_mul hp h1 (by positivity) (by positivity)
      _ ≤ 1 / 100 := by norm_num
  have hB1 : 3 * ((10 : ℝ) ^ 300 * X ^ (337 / 4 : ℝ)) ≤ 1 / 100 := by
    have h := ten300_Xpow_le hX0 hX1 hslack (q := 337 / 4) (by norm_num)
    linarith
  have hB2 : (10 : ℝ) ^ 300 * (3 : ℝ) ^ (3 / 2 : ℝ) * X ^ (337 / 8 : ℝ) ≤ 1 / 100 := by
    have h := ten300_Xpow_le hX0 hX1 hslack (q := 337 / 8) (by norm_num)
    calc (10 : ℝ) ^ 300 * (3 : ℝ) ^ (3 / 2 : ℝ) * X ^ (337 / 8 : ℝ)
        = (3 : ℝ) ^ (3 / 2 : ℝ) * ((10 : ℝ) ^ 300 * X ^ (337 / 8 : ℝ)) := by ring
      _ ≤ 6 * (1 / (10 : ℝ) ^ 100) :=
          mul_le_mul three_rpow_three_halves_le_six h (by positivity) (by norm_num)
      _ ≤ 1 / 100 := by norm_num
  have hB3 : 256 * Real.pi * X ^ (337 / 4 : ℝ) ≤ 1 / 100 := by
    have h := Xpow_le_ten_neg400 hX0 hX1 hslack (q := 337 / 4) (by norm_num)
    have hp : 256 * Real.pi ≤ (10 : ℝ) ^ 4 := by
      have := Real.pi_lt_four; nlinarith [Real.pi_pos]
    calc 256 * Real.pi * X ^ (337 / 4 : ℝ) ≤ (10 : ℝ) ^ 4 * (1 / (10 : ℝ) ^ 400) :=
          mul_le_mul hp h (by positivity) (by positivity)
      _ ≤ 1 / 100 := by norm_num
  have hB4 : 8 * Real.pi * Work.UBB.lhyC * X ^ (323 / 2 : ℝ) ≤ 1 / 100 := by
    have h := Xpow_le_ten_neg400 hX0 hX1 hslack (q := 323 / 2) (by norm_num)
    have hp : 8 * Real.pi * Work.UBB.lhyC ≤ (10 : ℝ) ^ 5 := by
      nlinarith [Real.pi_lt_four, Real.pi_pos, hlhyC, hlhyC0]
    calc 8 * Real.pi * Work.UBB.lhyC * X ^ (323 / 2 : ℝ)
        ≤ (10 : ℝ) ^ 5 * (1 / (10 : ℝ) ^ 400) :=
          mul_le_mul hp h (by positivity) (by positivity)
      _ ≤ 1 / 100 := by norm_num
  rcases le_total ρ (2 * μ) with hρ2 | hρ2
  · -- ## regime A: `ρ ≤ 2μ`
    have hpm : ρ + μ ≤ 3 * μ := by linarith
    have hm2 : (ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt μ ≤ 6 * μ ^ 2 := s32_sqrt_le hμ hρ hpm
    have hsp1 : X ^ (337 / 4 : ℝ) = X ^ (313 / 4 : ℝ) * X ^ 6 := by
      rw [show ((337 : ℝ) / 4) = 313 / 4 + 6 by norm_num, Real.rpow_add hX0, Real.rpow_ofNat]
    have hsp2 : X ^ (337 / 8 : ℝ) = X ^ (289 / 8 : ℝ) * X ^ 6 := by
      rw [show ((337 : ℝ) / 8) = 289 / 8 + 6 by norm_num, Real.rpow_add hX0, Real.rpow_ofNat]
    have hsp3 : X ^ (337 / 4 : ℝ) = X ^ (325 / 4 : ℝ) * X ^ 3 := by
      rw [show ((337 : ℝ) / 4) = 325 / 4 + 3 by norm_num, Real.rpow_add hX0, Real.rpow_ofNat]
    have hsp4 : X ^ (323 / 2 : ℝ) = X ^ (311 / 2 : ℝ) * X ^ 6 := by
      rw [show ((323 : ℝ) / 2) = 311 / 2 + 6 by norm_num, Real.rpow_add hX0, Real.rpow_ofNat]
    have b1 : (10 : ℝ) ^ 300 * ((ρ + μ) * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
        ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
      rw [hsp1]
      calc (10 : ℝ) ^ 300 * ((ρ + μ) * A * (X ^ (313 / 4 : ℝ) * X ^ 6 * (μ * L ^ 3)))
          ≤ (10 : ℝ) ^ 300 * ((3 * μ) * A * (X ^ (313 / 4 : ℝ) * X ^ 6 * (μ * L ^ 3))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right hpm (by positivity)
        _ = (3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ)) * (μ ^ 2 * X ^ 6) * (A * L ^ 3) := by ring
        _ ≤ (3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ))
              * (((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2) * (A * L ^ 3) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hs2 (by positivity)
        _ = (3 * (10 : ℝ) ^ 300 * X ^ (313 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2)
              * (A * (ρ - μ) ^ 2 * L ^ 3) := by ring
        _ ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) :=
            mul_le_mul_of_nonneg_right hA1 (by positivity)
    have b2 : (10 : ℝ) ^ 300
          * ((ρ + μ) ^ (3 / 2 : ℝ) * A * (L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ))
        ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
      rw [hsp2]
      calc (10 : ℝ) ^ 300
            * ((ρ + μ) ^ (3 / 2 : ℝ) * A * (L ^ 3 * (X ^ (289 / 8 : ℝ) * X ^ 6) * Real.sqrt μ))
          = ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ))
              * ((ρ + μ) ^ (3 / 2 : ℝ) * Real.sqrt μ) * (A * L ^ 3 * X ^ 6) := by ring
        _ ≤ ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)) * (6 * μ ^ 2) * (A * L ^ 3 * X ^ 6) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hm2 (by positivity)
        _ = (6 * ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ))) * (μ ^ 2 * X ^ 6) * (A * L ^ 3) := by ring
        _ ≤ (6 * ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)))
              * (((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2) * (A * L ^ 3) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hs2 (by positivity)
        _ = (6 * ((10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ)) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2)
              * (A * (ρ - μ) ^ 2 * L ^ 3) := by ring
        _ ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) :=
            mul_le_mul_of_nonneg_right hA2 (by positivity)
    have b3 : |ρ - μ| * (256 * Real.pi * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
        ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
      rw [hsp3]
      calc |ρ - μ| * (256 * Real.pi * A * (X ^ (325 / 4 : ℝ) * X ^ 3 * (μ * L ^ 3)))
          = (256 * Real.pi * X ^ (325 / 4 : ℝ)) * (|ρ - μ| * (μ * X ^ 3)) * (A * L ^ 3) := by ring
        _ ≤ (256 * Real.pi * X ^ (325 / 4 : ℝ))
              * (|ρ - μ| * ((2 : ℝ) ^ 14 * Real.pi * |ρ - μ|)) * (A * L ^ 3) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hfar (abs_nonneg _)
        _ = (256 * Real.pi * X ^ (325 / 4 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi))
              * (A * (ρ - μ) ^ 2 * L ^ 3) := by
            rw [← sq_abs]; ring
        _ ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) :=
            mul_le_mul_of_nonneg_right hA3 (by positivity)
    have b4 : 8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * X ^ (323 / 2 : ℝ)
        ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
      rw [hsp4]
      calc 8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * (X ^ (311 / 2 : ℝ) * X ^ 6)
          = (8 * Real.pi * Work.UBB.lhyC * X ^ (311 / 2 : ℝ)) * (μ ^ 2 * X ^ 6)
              * (A * L ^ 3) := by ring
        _ ≤ (8 * Real.pi * Work.UBB.lhyC * X ^ (311 / 2 : ℝ))
              * (((2 : ℝ) ^ 14 * Real.pi) ^ 2 * (ρ - μ) ^ 2) * (A * L ^ 3) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hs2 (by positivity)
        _ = (8 * Real.pi * Work.UBB.lhyC * X ^ (311 / 2 : ℝ) * ((2 : ℝ) ^ 14 * Real.pi) ^ 2)
              * (A * (ρ - μ) ^ 2 * L ^ 3) := by ring
        _ ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) :=
            mul_le_mul_of_nonneg_right hA4 (by positivity)
    linarith [b1, b2, b3, b4]
  · -- ## regime B: `2μ ≤ ρ`
    have hpos : 0 < ρ - μ := by linarith
    have hd : |ρ - μ| = ρ - μ := abs_of_pos hpos
    have hdpos : 0 < |ρ - μ| := abs_pos.mpr (by linarith)
    have hμd : μ ≤ |ρ - μ| := by rw [hd]; linarith
    have hpm3 : ρ + μ ≤ 3 * |ρ - μ| := by rw [hd]; linarith
    have b1 : (10 : ℝ) ^ 300 * ((ρ + μ) * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
        ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
      calc (10 : ℝ) ^ 300 * ((ρ + μ) * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
          = (10 : ℝ) ^ 300 * X ^ (337 / 4 : ℝ) * ((ρ + μ) * (μ * (A * L ^ 3))) := by ring
        _ ≤ (10 : ℝ) ^ 300 * X ^ (337 / 4 : ℝ)
              * ((3 * |ρ - μ|) * (|ρ - μ| * (A * L ^ 3))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hpm3 (mul_le_mul_of_nonneg_right hμd (by positivity))
              (by positivity) (by positivity)
        _ = (3 * ((10 : ℝ) ^ 300 * X ^ (337 / 4 : ℝ))) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
            rw [← sq_abs]; ring
        _ ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) :=
            mul_le_mul_of_nonneg_right hB1 (by positivity)
    have b2 : (10 : ℝ) ^ 300
          * ((ρ + μ) ^ (3 / 2 : ℝ) * A * (L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ))
        ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
      have hm3 : (ρ + μ) ^ (3 / 2 : ℝ) ≤ (3 * |ρ - μ|) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hpm3 (by norm_num)
      have hsqμ : Real.sqrt μ ≤ Real.sqrt |ρ - μ| := Real.sqrt_le_sqrt hμd
      have hkey : (3 * |ρ - μ|) ^ (3 / 2 : ℝ) * Real.sqrt |ρ - μ|
          = (3 : ℝ) ^ (3 / 2 : ℝ) * |ρ - μ| ^ 2 := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (abs_nonneg _), Real.sqrt_eq_rpow,
          mul_assoc, ← Real.rpow_add hdpos, show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num,
          Real.rpow_ofNat]
      calc (10 : ℝ) ^ 300
            * ((ρ + μ) ^ (3 / 2 : ℝ) * A * (L ^ 3 * X ^ (337 / 8 : ℝ) * Real.sqrt μ))
          = ((10 : ℝ) ^ 300 * X ^ (337 / 8 : ℝ))
              * ((ρ + μ) ^ (3 / 2 : ℝ) * (Real.sqrt μ * (A * L ^ 3))) := by ring
        _ ≤ ((10 : ℝ) ^ 300 * X ^ (337 / 8 : ℝ))
              * ((3 * |ρ - μ|) ^ (3 / 2 : ℝ) * (Real.sqrt |ρ - μ| * (A * L ^ 3))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hm3 (mul_le_mul_of_nonneg_right hsqμ (by positivity))
              (by positivity) (by positivity)
        _ = ((10 : ℝ) ^ 300 * (3 : ℝ) ^ (3 / 2 : ℝ) * X ^ (337 / 8 : ℝ))
              * (A * (ρ - μ) ^ 2 * L ^ 3) := by
            have hstep : (3 * |ρ - μ|) ^ (3 / 2 : ℝ) * (Real.sqrt |ρ - μ| * (A * L ^ 3))
                = ((3 : ℝ) ^ (3 / 2 : ℝ) * |ρ - μ| ^ 2) * (A * L ^ 3) := by
              rw [← mul_assoc, hkey]
            rw [hstep, sq_abs]; ring
        _ ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) :=
            mul_le_mul_of_nonneg_right hB2 (by positivity)
    have b3 : |ρ - μ| * (256 * Real.pi * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
        ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
      calc |ρ - μ| * (256 * Real.pi * A * (X ^ (337 / 4 : ℝ) * (μ * L ^ 3)))
          = (256 * Real.pi * X ^ (337 / 4 : ℝ)) * (|ρ - μ| * (μ * (A * L ^ 3))) := by ring
        _ ≤ (256 * Real.pi * X ^ (337 / 4 : ℝ)) * (|ρ - μ| * (|ρ - μ| * (A * L ^ 3))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hμd (by positivity))
              (abs_nonneg _)
        _ = (256 * Real.pi * X ^ (337 / 4 : ℝ)) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
            rw [← sq_abs]; ring
        _ ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) :=
            mul_le_mul_of_nonneg_right hB3 (by positivity)
    have b4 : 8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * X ^ (323 / 2 : ℝ)
        ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
      calc 8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * X ^ (323 / 2 : ℝ)
          = (8 * Real.pi * Work.UBB.lhyC * X ^ (323 / 2 : ℝ)) * (μ ^ 2 * (A * L ^ 3)) := by ring
        _ ≤ (8 * Real.pi * Work.UBB.lhyC * X ^ (323 / 2 : ℝ))
              * (|ρ - μ| ^ 2 * (A * L ^ 3)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ μ) hμd 2)
              (by positivity)
        _ = (8 * Real.pi * Work.UBB.lhyC * X ^ (323 / 2 : ℝ)) * (A * (ρ - μ) ^ 2 * L ^ 3) := by
            rw [sq_abs]; ring
        _ ≤ (1 / 100) * (A * (ρ - μ) ^ 2 * L ^ 3) :=
            mul_le_mul_of_nonneg_right hB4 (by positivity)
    linarith [b1, b2, b3, b4]

/-! ## 2. The target -/

theorem farArithExtra {A μ ρ L M X E : ℝ}
    (hA : 0 < A) (hμ : 0 < μ) (hρ : 0 ≤ ρ)
    (hL : 0 < L) (hM : 0 < M) (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hfar : μ * X ^ 3 ≤ (2 : ℝ) ^ 14 * Real.pi * |ρ - μ|)
    (hML : M = X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ (-(100 : ℤ)))
    (hE : E ≤ 4 * A * (ρ - μ) ^ 2 * L ^ 3) :
    (10 : ℝ) ^ 300 * ((ρ + μ) * A * M
        + (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M))
      + |ρ - μ| * (256 * Real.pi * A * M)
      + 8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * X ^ (323 / 2 : ℝ)
      + E
      ≤ 4 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by
  have hrows := farRows_le_fraction hA hμ hρ hL hX0 hX1 hfar hML hslack
  have hm : (0 : ℝ) ≤ A * (ρ - μ) ^ 2 * L ^ 3 := by positivity
  have hfin : (1 / 25) * (A * (ρ - μ) ^ 2 * L ^ 3) + 4 * A * (ρ - μ) ^ 2 * L ^ 3
      ≤ 4 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by
    have hc : (101 / 25 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    have heq : (1 / 25) * (A * (ρ - μ) ^ 2 * L ^ 3) + 4 * A * (ρ - μ) ^ 2 * L ^ 3
        = (101 / 25) * (A * (ρ - μ) ^ 2 * L ^ 3) := by ring
    rw [heq]
    calc (101 / 25) * (A * (ρ - μ) ^ 2 * L ^ 3)
        ≤ (4 * Real.pi) * (A * (ρ - μ) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_right hc hm
      _ = 4 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by ring
  calc (10 : ℝ) ^ 300 * ((ρ + μ) * A * M
          + (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M))
        + |ρ - μ| * (256 * Real.pi * A * M)
        + 8 * Real.pi * Work.UBB.lhyC * A * μ ^ 2 * L ^ 3 * X ^ (323 / 2 : ℝ)
        + E
      ≤ (1 / 25) * (A * (ρ - μ) ^ 2 * L ^ 3) + 4 * A * (ρ - μ) ^ 2 * L ^ 3 :=
        add_le_add hrows hE
    _ ≤ 4 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := hfin

end Work.BoseFixR
