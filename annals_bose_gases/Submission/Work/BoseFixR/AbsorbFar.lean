import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixR.Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/AbsorbFar.lean` — FS §11, the *far* absorption

`Arith.lean` states the §11 arithmetic in the abstract variables
`(a, ℓ, t, μ, R, C)`: the target is

`ℓ³Λ(a,K,η₀,μ) = −4πμ²aℓ³ + 4π·lhyC·μ²aℓ³√t − 4πμ²aℓ³·K·t^{1/2+η₀}`
(`Arith.Lambda_ell3`), the §9 far bound is

`FarBound = −4πμ²aℓ³ + 8π·lhyC·μ²aℓ³√t`
(`Arith.FarBound_eq`), and the §8 error is `errAbs a ℓ t μ R C₄`
(`Arith.errKafz_eq_errAbs`).

This module proves the comparison `AbsorbFar` of the *far* case:

`ℓ³Λ + errAbs ≤ FarBound` whenever `K ≥ bigK a R C₄ C₆` and `t = μa³ ≤ 1`,
`η₀ < 2/323`.

## The arithmetic

Dividing the inequality by the positive factor `μ²aℓ³√t` (and using
`t^{1/2+η₀} = √t·t^{η₀}`) it becomes

`C₄·(t^{9/646} + t^{2/323} + (R/a)²√t + t^{1/1615}) ≤ 4π·lhyC + 4πK·t^{η₀}`.

Since `t ≤ 1`, each monomial is dominated by `t^{η₀}` — this is exactly where the
two smallness hypotheses on `η₀` are used:

* `9/646 > 2/323 > η₀` (`hη₂`) for the `K_ℓ^{-3} = (μa³)^{9/646}` and
  `X² = (μa³)^{2/323}` terms;
* `1/1615 ≥ η₀` (`hη₃`) for the `X^{1/5} = (μa³)^{1/1615}` term;
* `1/2 > η₀` for the range term `(R/a)²√t`.

So the left-hand side is at most `C₄(3 + (R/a)²)·t^{η₀}`, and
`C₄(3 + (R/a)²) ≤ 4πK` is precisely what `bigK`'s numerator supplies (the
remaining `C₆(2 + (R/a)²) + 24π·lhyC + 1` is discarded — it is needed only by the
*close* absorption `AbsorbClose`). The constant `4π·lhyC` on the right is then
pure slack.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS §11, far case.** The target `ℓ³Λ(a,K,η₀,μ)` plus the §8 error is at most
the §9 far bound, whenever `K` dominates the assembly's error constant `bigK` and
the diluteness `t` is at most `1`. -/
theorem AbsorbFar {a ℓ t μ R C₄ C₆ K η₀ : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hμ : 0 < μ) (hR : 0 ≤ R) (hC₄ : 0 ≤ C₄)
    (hC₆ : 0 ≤ C₆) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323) (hη₃ : η₀ ≤ 1 / 1615)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : Work.BoseFixR.bigK a R C₄ C₆ ≤ K) :
    (-4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        + 4 * Real.pi * Work.UBB.lhyC * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
        - 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * K * t ^ (1 / 2 + η₀))
      + Work.BoseFixR.errAbs a ℓ t μ R C₄
    ≤ -4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        + 8 * Real.pi * Work.UBB.lhyC * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t := by
  -- exponents: `η₀` is below all four error exponents.
  have he_646 : η₀ ≤ 9 / 646 := by
    have h : (2 : ℝ) / 323 ≤ 9 / 646 := by norm_num
    linarith
  have he_half : η₀ ≤ 1 / 2 := by
    have h : (1 : ℝ) / 1615 ≤ 1 / 2 := by norm_num
    linarith
  -- every monomial of the error bracket is at most `t ^ η₀` (`t ≤ 1`).
  have h9 : t ^ (9 / 646 : ℝ) ≤ t ^ η₀ := rpow_le_rpow_of_le ht ht1 he_646
  have h2 : t ^ (2 / 323 : ℝ) ≤ t ^ η₀ := rpow_le_rpow_of_le ht ht1 hη₂.le
  have h1615 : t ^ (1 / 1615 : ℝ) ≤ t ^ η₀ := rpow_le_rpow_of_le ht ht1 hη₃
  have hs : Real.sqrt t ≤ t ^ η₀ := by
    rw [Real.sqrt_eq_rpow]
    exact rpow_le_rpow_of_le ht ht1 he_half
  have hRsq : (0 : ℝ) ≤ (R / a) ^ 2 := sq_nonneg _
  have hbracket : t ^ (9 / 646 : ℝ) + t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t
        + t ^ (1 / 1615 : ℝ) ≤ (3 + (R / a) ^ 2) * t ^ η₀ := by
    have hr2 : (R / a) ^ 2 * Real.sqrt t ≤ (R / a) ^ 2 * t ^ η₀ :=
      mul_le_mul_of_nonneg_left hs hRsq
    nlinarith
  -- `bigK`'s numerator, and the discarded (nonnegative) rest of it.
  have hnum : 4 * Real.pi * bigK a R C₄ C₆
      = C₄ * (3 + (R / a) ^ 2) + C₆ * (2 + (R / a) ^ 2)
        + 24 * Real.pi * Work.UBB.lhyC + 1 := by
    rw [bigK, ← mul_div_assoc,
      mul_div_cancel_left₀ _ (by positivity : (4 : ℝ) * Real.pi ≠ 0)]
  have hrest : 0 ≤ C₆ * (2 + (R / a) ^ 2) + 24 * Real.pi * Work.UBB.lhyC + 1 := by
    have h1 : 0 ≤ C₆ * (2 + (R / a) ^ 2) := mul_nonneg hC₆ (by positivity)
    have h2 : 0 ≤ 24 * Real.pi * Work.UBB.lhyC := by
      have := Work.UBB.lhyC_pos; positivity
    linarith
  have h4K : 4 * Real.pi * bigK a R C₄ C₆ ≤ 4 * Real.pi * K := by
    have h := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    linarith
  have hC4K : C₄ * (3 + (R / a) ^ 2) ≤ 4 * Real.pi * K := by
    linarith [h4K, hnum, hrest]
  -- hence the whole error bracket is dominated by `4π·lhyC + 4πK t^{η₀}`.
  have hbracket' : C₄ * (t ^ (9 / 646 : ℝ) + t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t
        + t ^ (1 / 1615 : ℝ)) ≤ 4 * Real.pi * Work.UBB.lhyC + 4 * Real.pi * K * t ^ η₀ := by
    have h1 : C₄ * (t ^ (9 / 646 : ℝ) + t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t
          + t ^ (1 / 1615 : ℝ)) ≤ C₄ * ((3 + (R / a) ^ 2) * t ^ η₀) :=
      mul_le_mul_of_nonneg_left hbracket hC₄
    have h2 : C₄ * (3 + (R / a) ^ 2) * t ^ η₀ ≤ 4 * Real.pi * K * t ^ η₀ :=
      mul_le_mul_of_nonneg_right hC4K (Real.rpow_nonneg ht.le η₀)
    have h3 : 0 ≤ 4 * Real.pi * Work.UBB.lhyC := by
      have := Work.UBB.lhyC_pos; positivity
    nlinarith [h1, h2, h3]
  -- multiply by the positive normalisation `μ²aℓ³√t` and use `t^{1/2+η₀} = √t t^{η₀}`.
  have hfac : (0 : ℝ) ≤ μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbracket' hfac
  have hpow : t ^ (1 / 2 + η₀) = Real.sqrt t * t ^ η₀ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_add ht]
  rw [errAbs, hpow]
  nlinarith [hmul]

end Work.BoseFixR
