import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

/-- **Arithmetic core of `regularTBlock`.**

Let `g = G·χ ≥ 0`, and suppose
* `g ≤ (50/49)·W` (so that `W` dominates the pair interaction `G·χ`),
* `(49/50)·g ≤ Δ ≤ W` (the pair-square coefficient sits between the two regulators),
* `(25/49)·((1/50+γ)·n² + 3·n) ≤ A` (the ledger hypothesis `hSc`, cleared of denominators).

Then the pair square `(1/2)(1+γ)·g·(n+1)·n` is paid by `W·A + (1/2)·Δ·(n²−n)`.

The two regimes are treated separately: for `n ≥ 1` the whole credit `Δ·(n²−n)` is
available (`n²−n ≥ 0`), for `0 ≤ n ≤ 1` one uses `Δ ≤ W` and `n²−n ≤ 0`. -/
private lemma core {n γ W g Δ A : ℝ}
    (hn0 : 0 ≤ n) (hW : 0 ≤ W) (hg0 : 0 ≤ g) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 50)
    (hgW : g ≤ (50 / 49) * W) (hreg2 : (49 / 50) * g ≤ Δ) (hΔW : Δ ≤ W)
    (hAW : (25 / 49) * ((1 / 50 + γ) * n ^ 2 + 3 * n) ≤ A) :
    (1 / 2) * (1 + γ) * g * (n + 1) * n ≤ W * A + (1 / 2) * Δ * (n ^ 2 - n) := by
  have hgn : (1 / 2) * g ≤ (25 / 49) * W := by nlinarith
  have h51 : 0 ≤ 51 - 50 * γ := by nlinarith
  have hA3 : W * ((25 / 49) * ((1 / 50 + γ) * n ^ 2 + 3 * n)) ≤ W * A :=
    mul_le_mul_of_nonneg_left hAW hW
  rcases le_or_gt 1 n with h1 | h1
  · -- regime `n ≥ 1`: the pair-square credit `Δ·(n²−n)` is nonnegative
    have hdnn : (0 : ℝ) ≤ (1 / 2) * (n ^ 2 - n) := by
      have h := mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ n - 1)
      nlinarith [h]
    have hfac2 : (0 : ℝ) ≤ (1 / 50 + γ) * n ^ 2 + 3 * n := by
      have h1' : (0 : ℝ) ≤ 1 / 50 + γ := by linarith
      have h := mul_nonneg h1' (sq_nonneg n)
      nlinarith [h]
    have step2 : (1 / 2) * g * ((1 / 50 + γ) * n ^ 2 + 3 * n)
        ≤ (25 / 49) * W * ((1 / 50 + γ) * n ^ 2 + 3 * n) :=
      mul_le_mul_of_nonneg_right hgn hfac2
    have step3 : (49 / 100) * g * (n ^ 2 - n) ≤ (1 / 2) * Δ * (n ^ 2 - n) := by
      have h := mul_le_mul_of_nonneg_right hreg2 hdnn
      linarith
    have hfac3 : 0 ≤ g * n * (51 - 50 * γ) :=
      mul_nonneg (mul_nonneg hg0 hn0) h51
    have key : (1 / 2) * (1 + γ) * g * (n + 1) * n
        ≤ (1 / 2) * g * ((1 / 50 + γ) * n ^ 2 + 3 * n) + (49 / 100) * g * (n ^ 2 - n) := by
      nlinarith [hfac3]
    nlinarith [hA3, step2, step3, key]
  · -- regime `0 ≤ n ≤ 1`: use `Δ ≤ W` against the *negative* pair-square credit
    have hdnn : (0 : ℝ) ≤ (1 / 2) * (n - n ^ 2) := by
      have h := mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ 1 - n)
      nlinarith [h]
    have hstep3 : (1 / 2) * W * (n ^ 2 - n) ≤ (1 / 2) * Δ * (n ^ 2 - n) := by
      have h := mul_le_mul_of_nonneg_right hΔW hdnn
      linarith
    have hfac2 : (0 : ℝ) ≤ (1 + γ) * n * (n + 1) := by
      have h1' : (0 : ℝ) ≤ 1 + γ := by linarith
      have h := mul_nonneg (mul_nonneg h1' hn0) (by linarith : (0 : ℝ) ≤ n + 1)
      linarith [h]
    have step2 : (1 / 2) * (1 + γ) * g * n * (n + 1)
        ≤ (25 / 49) * (1 + γ) * W * n * (n + 1) := by
      have h := mul_le_mul_of_nonneg_right hgn hfac2
      linarith
    have hfac3 : 0 ≤ W * n * (51 - 50 * γ) :=
      mul_nonneg (mul_nonneg hW hn0) h51
    have key : (25 / 49) * (1 + γ) * W * n * (n + 1)
        ≤ W * ((25 / 49) * ((1 / 50 + γ) * n ^ 2 + 3 * n)) + (1 / 2) * W * (n ^ 2 - n) := by
      nlinarith [hfac3]
    nlinarith [hA3, step2, hstep3, key]

theorem regularTBlock {T V a W χ G Δ n γ band : ℝ}
    (hn0 : 0 ≤ n) (hW : 0 ≤ W) (hχ : 0 ≤ χ) (ha : 0 ≤ a) (hG0 : 0 ≤ G)
    (hG8 : G ≤ 8 * Real.pi * a)
    (hreg1 : (49 / 50) * (8 * Real.pi * a) * χ ≤ W)
    (hreg2 : (49 / 50) * G * χ ≤ Δ) (hΔW : Δ ≤ W)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 50)
    (hband : band * V ^ 2 ≤ (1 / 100) * n * T * W)
    (hSc : 0 ≤ (49 / 25) * ((1 / 4) * (n - T) ^ 2 - (1 / 2) * T ^ 2 - n - T / 2 - (1 / 4)
            - (1 / 100) * n * T - n * T / 18)
          - ((1 / 50 + γ) * n ^ 2 + 3 * n)) :
    (1 / 18) * n * T * W + (1 / 2) * (1 + γ) * G * χ * (n + 1) * n + band * V ^ 2
      ≤ (1 / 4) * (n - T) ^ 2 * W - (1 / 2) * T ^ 2 * W - (W / 2) * (2 * n + T) - W / 4
        + (1 / 2) * Δ * (n ^ 2 - n) := by
  -- cleared ledger hypothesis
  have hAW : (25 / 49) * ((1 / 50 + γ) * n ^ 2 + 3 * n)
      ≤ (1 / 4) * (n - T) ^ 2 - (1 / 2) * T ^ 2 - n - T / 2 - (1 / 4)
        - (1 / 100) * n * T - n * T / 18 := by
    nlinarith [hSc]
  -- the pair interaction is dominated by `W`
  have hgW : G * χ ≤ (50 / 49) * W := by
    have h1 : G * χ ≤ (8 * Real.pi * a) * χ := mul_le_mul_of_nonneg_right hG8 hχ
    have h2 : (8 * Real.pi * a) * χ ≤ (50 / 49) * W := by
      have hp := Real.pi_pos
      nlinarith [hreg1]
    linarith
  have hreg2' : (49 / 50) * (G * χ) ≤ Δ := by nlinarith [hreg2]
  have hg0 : 0 ≤ G * χ := mul_nonneg hG0 hχ
  have hcore := core hn0 hW hg0 hγ0 hγ hgW hreg2' hΔW hAW
  -- the right-hand side is `W·A + W·(nT/100 + nT/18) + (1/2)Δ(n²−n)`
  have hrhs : (1 / 4) * (n - T) ^ 2 * W - (1 / 2) * T ^ 2 * W - (W / 2) * (2 * n + T) - W / 4
      + (1 / 2) * Δ * (n ^ 2 - n)
      = W * ((1 / 4) * (n - T) ^ 2 - (1 / 2) * T ^ 2 - n - T / 2 - (1 / 4)
          - (1 / 100) * n * T - n * T / 18)
        + W * ((1 / 100) * n * T + n * T / 18) + (1 / 2) * Δ * (n ^ 2 - n) := by ring
  nlinarith [hband, hcore, hrhs]

end Work.BoseSWE
