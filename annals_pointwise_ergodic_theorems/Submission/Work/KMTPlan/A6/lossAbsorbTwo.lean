/-
# The bookkeeping of the two loss weights (area A6)

This file proves `Work.KMTPlan.A6.LossAbsorbProp`: the elementary real arithmetic that lets the
exponential gain `2^{-c·max(l₁,l₂)}` and the polynomial loss `lossWeight A ρ l₁ l₂ k₁ k₂` of the two
parts of the frozen-`t` slice estimate (the good/adelic part of `AdelicFormProp` and the bad part of
`BadPartProp`) be absorbed into a single weight
`lossWeight (2A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂ · 2^{-((min c₀ c₁)/2)·max(l₁,l₂)}`.

The key point is that the loss weight is a *single* power:

  `lossWeight c ρ l₁ l₂ k₁ k₂ = ((1 + lmaxR) · 2^{ρ·lmaxR})^c`,

with the base `X = (1 + lmaxR) · 2^{ρ·lmaxR} ≥ 1` (`lmaxR = max(max l₁ l₂)(max k₁ k₂) ≥ 0`,
`ρ > 0`).  Hence `lossWeight A₀ ^ 2 = lossWeight (2A₀)`, the weight is monotone in its exponent `c`,
and the two elementary inequalities of the proposition reduce to
`2^{-c₀M} ≤ 2^{-((min c₀ c₁)/2)M}`, `2^{-c₁M} ≤ 2^{-((min c₀ c₁)/2)M}` (valid because
`min c₀ c₁ ≤ c₀, c₁`) together with `lossWeight A₀ ^ 2 ≤ lossWeight (2A₀ + A₁ + 1)` and
`lossWeight A₁ ≤ lossWeight (2A₀ + A₁ + 1)` (valid because `A₀, A₁ ≥ 0`).

Nothing here is postulated.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs

namespace Work.KMTPlan.A6

open Work.KMTAreas.A7

/-- `lmaxR ≥ 0` (it is the coercion of the integer `lmax`). -/
private lemma lmaxR_nonneg (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR]
  have h : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
    unfold Work.Analysis.EndVar.lmax
    omega
  exact_mod_cast h

/-- **The loss weight is a single power**: `lossWeight c ρ … = X^c` with
`X = (1 + lmaxR) · 2^{ρ·lmaxR} ≥ 1`. -/
private lemma lossWeight_eq_rpow (c ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight c ρ l₁ l₂ k₁ k₂
      = ((1 + lmaxR l₁ l₂ k₁ k₂) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) ^ c := by
  have hL := lmaxR_nonneg l₁ l₂ k₁ k₂
  have h1 : (0 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) := Real.rpow_nonneg (by norm_num) _
  rw [lossWeight, Real.mul_rpow h1 h2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show c * ρ * lmaxR l₁ l₂ k₁ k₂ = (ρ * lmaxR l₁ l₂ k₁ k₂) * c from by ring]

/-- The loss weight is nonnegative. -/
private lemma lossWeight_nonneg (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    0 ≤ lossWeight A ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight_eq_rpow]
  exact Real.rpow_nonneg
    (mul_nonneg (by linarith [lmaxR_nonneg l₁ l₂ k₁ k₂]) (Real.rpow_nonneg (by norm_num) _)) _

/-- **The square of the weight is the weight at the doubled exponent**. -/
private lemma lossWeight_sq (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight A ρ l₁ l₂ k₁ k₂ ^ 2 = lossWeight (2 * A) ρ l₁ l₂ k₁ k₂ := by
  have hX0 : (0 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) :=
    mul_nonneg (by linarith [lmaxR_nonneg l₁ l₂ k₁ k₂]) (Real.rpow_nonneg (by norm_num) _)
  rw [lossWeight_eq_rpow A ρ l₁ l₂ k₁ k₂, lossWeight_eq_rpow (2 * A) ρ l₁ l₂ k₁ k₂]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
  congr 1
  push_cast
  ring

/-- **The loss weight is monotone in its exponent** (`c ↦ X^c` with `X ≥ 1`). -/
private lemma lossWeight_mono' {c c' ρ : ℝ} (hcc : c ≤ c') (hρ : 0 ≤ ρ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight c ρ l₁ l₂ k₁ k₂ ≤ lossWeight c' ρ l₁ l₂ k₁ k₂ := by
  have hL := lmaxR_nonneg l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hρ hL)
  have hX1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) :=
    le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1) (mul_le_mul h1 h2 (by norm_num) (by linarith))
  rw [lossWeight_eq_rpow c ρ l₁ l₂ k₁ k₂, lossWeight_eq_rpow c' ρ l₁ l₂ k₁ k₂]
  exact Real.rpow_le_rpow_of_exponent_le hX1 hcc

/-- The explicit form of `LossAbsorbProp`. -/
private lemma lossAbsorb_main (A₀ A₁ c₀ c₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (ρ : ℝ) (hρ : 0 < ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (2 : ℝ) ^ (-(c₀ * max (l₁ : ℝ) (l₂ : ℝ))) * lossWeight A₀ ρ l₁ l₂ k₁ k₂ ^ 2
        ≤ (2 : ℝ) ^ (-((min c₀ c₁) / 2) * max (l₁ : ℝ) (l₂ : ℝ))
            * lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂ ∧
      lossWeight A₁ ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(c₁ * max (l₁ : ℝ) (l₂ : ℝ)))
        ≤ (2 : ℝ) ^ (-((min c₀ c₁) / 2) * max (l₁ : ℝ) (l₂ : ℝ))
            * lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂ := by
  have hρ' : 0 ≤ ρ := le_of_lt hρ
  have hM : (0 : ℝ) ≤ max (l₁ : ℝ) (l₂ : ℝ) := by positivity
  have hminpos : 0 < min c₀ c₁ := lt_min hc₀ hc₁
  have hmin₀ : min c₀ c₁ / 2 ≤ c₀ := by
    have h1 := min_le_left c₀ c₁
    have : min c₀ c₁ / 2 ≤ min c₀ c₁ := by linarith
    linarith
  have hmin₁ : min c₀ c₁ / 2 ≤ c₁ := by
    have h1 := min_le_right c₀ c₁
    have : min c₀ c₁ / 2 ≤ min c₀ c₁ := by linarith
    linarith
  constructor
  · -- the good part: `lossWeight A₀ ^ 2 = lossWeight (2A₀) ≤ lossWeight (2A₀ + A₁ + 1)`,
    -- and `2^{-c₀M} ≤ 2^{-((min c₀ c₁)/2)M}` since `min c₀ c₁ ≤ 2c₀`
    have hW : lossWeight A₀ ρ l₁ l₂ k₁ k₂ ^ 2
        ≤ lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂ := by
      calc lossWeight A₀ ρ l₁ l₂ k₁ k₂ ^ 2
          = lossWeight (2 * A₀) ρ l₁ l₂ k₁ k₂ := lossWeight_sq A₀ ρ l₁ l₂ k₁ k₂
        _ ≤ lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂ :=
            lossWeight_mono' (by linarith) hρ' l₁ l₂ k₁ k₂
    have hpow : (2 : ℝ) ^ (-(c₀ * max (l₁ : ℝ) (l₂ : ℝ)))
        ≤ (2 : ℝ) ^ (-((min c₀ c₁) / 2) * max (l₁ : ℝ) (l₂ : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have h : (min c₀ c₁) / 2 * max (l₁ : ℝ) (l₂ : ℝ)
          ≤ c₀ * max (l₁ : ℝ) (l₂ : ℝ) := mul_le_mul_of_nonneg_right hmin₀ hM
      linarith
    exact mul_le_mul hpow hW (pow_nonneg (lossWeight_nonneg A₀ ρ l₁ l₂ k₁ k₂) 2)
      (Real.rpow_nonneg (by norm_num) _)
  · -- the bad part: `lossWeight A₁ ≤ lossWeight (2A₀ + A₁ + 1)`
    have hW : lossWeight A₁ ρ l₁ l₂ k₁ k₂
        ≤ lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂ :=
      lossWeight_mono' (by linarith) hρ' l₁ l₂ k₁ k₂
    have hpow : (2 : ℝ) ^ (-(c₁ * max (l₁ : ℝ) (l₂ : ℝ)))
        ≤ (2 : ℝ) ^ (-((min c₀ c₁) / 2) * max (l₁ : ℝ) (l₂ : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have h : (min c₀ c₁) / 2 * max (l₁ : ℝ) (l₂ : ℝ)
          ≤ c₁ * max (l₁ : ℝ) (l₂ : ℝ) := mul_le_mul_of_nonneg_right hmin₁ hM
      linarith
    calc lossWeight A₁ ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(c₁ * max (l₁ : ℝ) (l₂ : ℝ)))
        ≤ lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂
            * (2 : ℝ) ^ (-((min c₀ c₁) / 2) * max (l₁ : ℝ) (l₂ : ℝ)) :=
          mul_le_mul hW hpow (Real.rpow_nonneg (by norm_num) _) (lossWeight_nonneg _ _ _ _ _ _)
      _ = (2 : ℝ) ^ (-((min c₀ c₁) / 2) * max (l₁ : ℝ) (l₂ : ℝ))
            * lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂ := by ring

theorem lossAbsorbTwo : Work.KMTPlan.A6.LossAbsorbProp := by
  intro A₀ A₁ c₀ c₁ hA₀ hA₁ hc₀ hc₁ ρ hρ l₁ l₂ k₁ k₂
  exact lossAbsorb_main A₀ A₁ c₀ c₁ hA₀ hA₁ hc₀ hc₁ ρ hρ l₁ l₂ k₁ k₂

end Work.KMTPlan.A6
