/-
# `Submission.Work.FIPiChain.P3S3.S3minusC_integral_le`

The **integral (averaged) form** of the §8 estimate for the `μ(c)`-signed `S₃⁻`:

  `|S₃⁻| ≤ ∫_1^C ( Σ_{ℓ ≤ N} w(ℓ)·|XrhoC(a,N,ℓ;s,z,sz)| ) ds/s`

(no dyadic splitting needed: rather than bounding the inner `ℓ`-sum pointwise by `J·E`, we keep
it inside the integral).  The proof follows `Submission.Work.FIChain.abs_S3minusC_le` Steps 1–3:

* Step 1: the `μ(b)`-sum over divisors of `ℓ` is bounded by `w(ℓ)` (hypothesis `hw`), so
  `|S₃⁻| ≤ Σ_ℓ w(ℓ)·|S3minusInnerC(a,N,ℓ,z,sz,C)|`;
* Step 2: `|S3minusInnerC| ≤ ∫_1^C |XrhoC| ds/s` (`abs_S3minusInnerC_le_integral`);
* Step 3: linearity of the integral — `Σ_ℓ w(ℓ)·∫ |XrhoC_ℓ|/s = ∫ (Σ_ℓ w(ℓ)|XrhoC_ℓ|)/s`
  (`integral_finsetSum` + `integral_const_mul` + `sum_div`).
-/
import Mathlib
import Submission.Work.FIPiChain.Defs
import Submission.Work.FIChain.abs_S3minusC_le

set_option maxHeartbeats 1600000

namespace Work.FIPiChain.P3S3

open Finset MeasureTheory
open scoped Interval BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The per-`ℓ` integrability of `s ↦ |XrhoC|/s` on `(1,C]`, from the uniform-in-`s` bound
`|XrhoC| ≤ Σ_{n ≤ N} τ(n)|a(ℓn)|` of `Work.FIChain.abs_XrhoC_le`. -/
theorem XrhoC_div_intervalIntegrable (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ) (hC : 1 ≤ C) :
    IntervalIntegrable (fun s : ℝ => |Work.FITop.XrhoC a N ℓ s z sz| / s)
      volume (1 : ℝ) C :=
  Submission.ASP.intervalIntegrable_div_Ioc (Work.FIChain.measurable_XrhoC a N ℓ z sz).abs
    (by norm_num) hC (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |a (ℓ * n)|)
    (fun s _ => by simpa using Work.FIChain.abs_XrhoC_le a N ℓ s z sz)

theorem S3minusC_integral_le (a lam w : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ)
    (hC : 1 ≤ C) (ha : ∀ n : ℕ, ¬ Squarefree n → a n = 0)
    (hw0 : ∀ ℓ : ℕ, 0 ≤ w ℓ)
    (hw : ∀ ℓ : ℕ, 1 ≤ ℓ →
      |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)| * |Submission.ASP.rhoOf lam ℓ| ≤ w ℓ) :
    |Work.FIChain.S3minusC a lam N z sy sz C|
      ≤ ∫ s in (1 : ℝ)..C,
          (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z sz|) / s := by
  classical
  -- Step 1: pull the divisor-sum weights out of the absolute value
  have h1 : |Work.FIChain.S3minusC a lam N z sy sz C|
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FIChain.S3minusInnerC a N ℓ z sz C| := by
    rw [Work.FIChain.S3minusC]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ℓ hℓ => ?_))
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hw ℓ (Finset.mem_Icc.mp hℓ).1) (abs_nonneg _)
  -- Step 2: each inner `c`-sum by the integral of `|XrhoC|/s`
  have h2 : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FIChain.S3minusInnerC a N ℓ z sz C|)
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ *
          (∫ s in (1 : ℝ)..C, |Work.FITop.XrhoC a N ℓ s z sz| / s) :=
    Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left
      (Work.FIChain.abs_S3minusInnerC_le_integral a N ℓ z sz C hC ha) (hw0 ℓ))
  -- Step 3: linearity of the integral (sum over `ℓ` moved inside)
  have h3 : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ *
        (∫ s in (1 : ℝ)..C, |Work.FITop.XrhoC a N ℓ s z sz| / s))
      = ∫ s in (1 : ℝ)..C,
          (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z sz|) / s := by
    calc (∑ ℓ ∈ Finset.Icc 1 N, w ℓ *
          (∫ s in (1 : ℝ)..C, |Work.FITop.XrhoC a N ℓ s z sz| / s))
        = ∑ ℓ ∈ Finset.Icc 1 N,
            ∫ s in (1 : ℝ)..C, w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s) :=
          Finset.sum_congr rfl (fun ℓ _ =>
            (intervalIntegral.integral_const_mul (w ℓ)
              (fun s : ℝ => |Work.FITop.XrhoC a N ℓ s z sz| / s)).symm)
      _ = ∫ s in (1 : ℝ)..C,
            ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (|Work.FITop.XrhoC a N ℓ s z sz| / s) :=
          (intervalIntegral.integral_finsetSum (fun ℓ _ =>
            (XrhoC_div_intervalIntegrable a N ℓ z sz C hC).const_mul (w ℓ))).symm
      _ = ∫ s in (1 : ℝ)..C,
            (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z sz|) / s :=
          intervalIntegral.integral_congr (fun s _ => by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun ℓ _ => by ring))
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

end

end Work.FIPiChain.P3S3
