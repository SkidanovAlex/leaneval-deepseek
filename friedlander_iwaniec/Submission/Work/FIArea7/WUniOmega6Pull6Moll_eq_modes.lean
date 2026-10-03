/-
# `Submission.Work.FIArea7.WUniOmega6Pull6Moll_eq_modes` — the Fourier-mode expansion of (17.10)

`Work.FIArea7.WUniOmega6Pull6Moll` is the `(b,e)`-sum of the pair sums whose logarithmic factor
`logFac6` has been replaced by its truncated Fourier series
`logFac6Series z₁ z₂ K = (2log2 + log4) + Σ_{k ∈ evenFreq K} (1/|k|)·c_k(z₁)·conj(c_k(z₂))`
(`Work.FIArea7.UniMollify6`).  This file records the purely algebraic consequence: the mollified
sum is the same `(b,e)`-sum of the *modes*

  `(2log2 + log4)·uniModePair Pa b e β 0 + Σ_{k ∈ evenFreq K} (1/|k|)·uniModePair Pa b e β k`,

i.e. the constant term of the series produces the `k = 0` mode (with `uniPow _ 0 = 1`, so that
`uniModePair Pa b e β 0` is the pair sum with no frequency factor) and each frequency `k` produces
the mode `uniModePair Pa b e β k`.  The `k`-sum is pulled out of the `(z₁,z₂)`-sums; all the
`(b,e)`-weights `μ(b)/b` are carried along unchanged.

This is the shape in which Proposition 17.2 (the uniform bound for a single mode) can be applied
term by term.
-/
import Mathlib
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea7.UniChain6

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Pulling a sum of two pieces out of an outer sum

The elementary rearrangement used twice below: the outer sum of the pointwise decomposition
`c·A i + Σ_k w k ·B i k` splits, and the `k`-sum is commuted with the `i`-sum. -/
private lemma sum_shift {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ℂ)
    (A : ι → ℂ) (B : ι → κ → ℂ) (w : κ → ℂ) :
    (∑ i ∈ s, (c * A i + ∑ k ∈ t, w k * B i k))
      = c * (∑ i ∈ s, A i) + ∑ k ∈ t, w k * (∑ i ∈ s, B i k) := by
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])

/-! ## 2. The expansion of the truncated series, pair by pair -/

/-- **The Fourier-mode expansion of a pair sum with the truncated series.**  For any pair
coefficient `X : GaussianInt → GaussianInt → ℂ` and any pair predicate `Pf`, the `(z₁,z₂)`-sum of
`X z₁ z₂ · logFac6Series z₁ z₂ K` (on the support `Pf`) is the constant term
`(2log2 + log4)` times the `k = 0` mode plus the `1/|k|`-weighted sum of the modes
`k ∈ evenFreq K`.

The kernel of the proof is pointwise: for a fixed pair, `logFac6Series` is the sum of a constant
and the frequency sum, so multiplying by `X` and distributing gives
`X·(2log2 + log4) + Σ_k X·(1/|k|)·c_k(z₁)conj(c_k(z₂))`; the two pieces are then summed
separately and the frequency sum is commuted with the `(z₁,z₂)`-sums
(`Work.FIArea7.sum_shift`).  The `k = 0` case uses `uniPow _ 0 = 1`. -/
private lemma sum_pair_expand (s : Finset GaussianInt) (K : ℕ)
    (Pf : GaussianInt → GaussianInt → Prop) [DecidableRel Pf] (X : GaussianInt → GaussianInt → ℂ) :
    (∑ z1 ∈ s, ∑ z2 ∈ s, (if Pf z1 z2 then X z1 z2 * logFac6Series z1 z2 K else 0))
      = (((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ)
          * (∑ z1 ∈ s, ∑ z2 ∈ s,
              (if Pf z1 z2 then X z1 z2 * (uniPow z1 0 * star (uniPow z2 0)) else 0))
        + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ)
            * (∑ z1 ∈ s, ∑ z2 ∈ s,
                (if Pf z1 z2 then X z1 z2 * (uniPow z1 k * star (uniPow z2 k)) else 0)) := by
  have hpoint : ∀ z1 z2, (if Pf z1 z2 then X z1 z2 * logFac6Series z1 z2 K else 0)
      = (((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ)
          * (if Pf z1 z2 then X z1 z2 * (uniPow z1 0 * star (uniPow z2 0)) else 0)
        + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ)
            * (if Pf z1 z2 then X z1 z2 * (uniPow z1 k * star (uniPow z2 k)) else 0) := by
    intro z1 z2
    by_cases h : Pf z1 z2
    · simp only [h, if_true]
      have h0 : uniPow z1 0 * star (uniPow z2 0) = 1 := by simp [uniPow]
      rw [h0, mul_one, logFac6Series, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl; intro k hk; ring
    · simp only [h, if_false]
      simp
  calc (∑ z1 ∈ s, ∑ z2 ∈ s, (if Pf z1 z2 then X z1 z2 * logFac6Series z1 z2 K else 0))
      = ∑ z1 ∈ s, ∑ z2 ∈ s,
          ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ)
              * (if Pf z1 z2 then X z1 z2 * (uniPow z1 0 * star (uniPow z2 0)) else 0)
            + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ)
                * (if Pf z1 z2 then X z1 z2 * (uniPow z1 k * star (uniPow z2 k)) else 0)) := by
          apply Finset.sum_congr rfl; intro z1 _
          apply Finset.sum_congr rfl; intro z2 _
          exact hpoint z1 z2
    _ = ∑ z1 ∈ s,
          ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ)
              * (∑ z2 ∈ s, (if Pf z1 z2 then X z1 z2 * (uniPow z1 0 * star (uniPow z2 0)) else 0))
            + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ)
                * (∑ z2 ∈ s, (if Pf z1 z2 then X z1 z2 * (uniPow z1 k * star (uniPow z2 k)) else 0))) := by
          apply Finset.sum_congr rfl; intro z1 _
          exact sum_shift s (evenFreq K) _ _
            (fun z2 k => (if Pf z1 z2 then X z1 z2 * (uniPow z1 k * star (uniPow z2 k)) else 0)) _
    _ = (((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ)
          * (∑ z1 ∈ s, ∑ z2 ∈ s,
              (if Pf z1 z2 then X z1 z2 * (uniPow z1 0 * star (uniPow z2 0)) else 0))
        + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ)
            * (∑ z1 ∈ s, ∑ z2 ∈ s,
                (if Pf z1 z2 then X z1 z2 * (uniPow z1 k * star (uniPow z2 k)) else 0)) := by
          exact sum_shift s (evenFreq K) _ _
            (fun z1 k => ∑ z2 ∈ s, (if Pf z1 z2 then X z1 z2 * (uniPow z1 k * star (uniPow z2 k)) else 0)) _

/-- The concrete pair sum of `WUniOmega6Pull6Moll` at fixed `(b,e)`, expanded into its Fourier
modes: the pair predicate is the coprimality/congruence condition of the pull-out, and the pair
coefficient is everything except the logarithmic factor. -/
private lemma inner_eq_modes (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) (K : ℕ) :
    (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
          (Work.FIArea7.reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
            * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
            * (betaPrime β z1 * star (betaPrime β z2))
            * logFac6Series z1 z2 K
         else 0))
      = (((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModePair Pa b e β 0
        + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModePair Pa b e β k := by
  simp only [uniModePair]
  exact sum_pair_expand _ K _ _

/-! ## 3. The mollified main term in terms of its modes -/

theorem WUniOmega6Pull6Moll_eq_modes (Pa : Work.FITop.Params) (X : ℕ)
    (β : GaussianInt → ℂ) (K : ℕ) :
    Work.FIArea7.WUniOmega6Pull6Moll Pa X β K
      = 2 * ∑ b ∈ Finset.Icc 1 (Work.FIArea7.uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
              * ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ)
                    * Work.FIArea7.uniModePair Pa b e β 0
                  + ∑ k ∈ Work.FIArea7.evenFreq K,
                      (1 / (|k| : ℝ) : ℂ) * Work.FIArea7.uniModePair Pa b e β k) := by
  rw [Work.FIArea7.WUniOmega6Pull6Moll]
  congr 1
  refine Finset.sum_congr rfl (fun b hb => Finset.sum_congr rfl (fun e he => ?_))
  exact congrArg (fun t : ℂ => (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) * t)
    (inner_eq_modes Pa b e β K)

end

end Work.FIArea7
