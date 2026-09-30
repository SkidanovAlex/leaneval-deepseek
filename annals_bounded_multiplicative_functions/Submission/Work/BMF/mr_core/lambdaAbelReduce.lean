import Mathlib
import Submission.Work.BMF.mr_core.bumpFnScaledAux
import Submission.Work.BMF.mr_core.floorIccSumEqIndicator
import Submission.Work.BMF.mr_core.integralMulIndicatorIci

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Abel summation for the smoothed von Mangoldt sum

This file proves `Work.BMF.mr_core.lambdaAbelReduce`, the "Abel reduction" of the
smoothed von Mangoldt sum

`∑_{n ≤ ⌈4A⌉} Λ(n) n^{iδ} φ(n/A)`

to an integral against the *ordinary* (unweighted) partial sums of `Λ(n) n^{iδ}`:

`- ∫_0^{⌈4A⌉} (φ'(t/A)/A) · ∑_{n ≤ ⌊t⌋} Λ(n) n^{iδ} dt`.

This is the classical partial-summation / Abel-summation identity, in the exact form needed for
the smoothed counting problem; the weight `t ↦ φ(t/A)` is the rescaled smooth bump
`Work.BMF.bumpFn` of `Submission/Work/BMF/smoothing_exists.lean`, which vanishes at
`t = ⌈4A⌉` (`bumpFn_div_ceil_eq_zero`), so the boundary term of the summation-by-parts
disappears.

The route:
* the staircase identity `floorIccSumEqIndicator` rewrites the partial sum
  `∑_{n ≤ ⌊t⌋} Λ(n) n^{iδ}` as a finite sum of indicators `∑_{n ≤ ⌈4A⌉} b n · 1_{n ≤ t}`;
* `integralMulIndicatorIci` computes `∫_0^{⌈4A⌉} f · 1_{n ≤ t} = ∫_n^{⌈4A⌉} f`;
* exchanging the finite sum with the integral (`intervalIntegral.integral_finsetSum`) and the
  fundamental theorem of calculus then give the result.

The auxiliary `abelStep` isolates the purely analytic part, stated for an arbitrary pair
`G`/`G' = dG` of a differentiable function and its derivative.
-/

namespace Work.BMF.mr_core

open MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-- **Abel summation, integral form.**  For a `C¹` function `G` with derivative `dG`, any `N : ℕ`
and any sequence `b`, the integral of `dG` against the staircase `∑_{n ∈ Icc 1 N} b n · 1_{n ≤ t}`
equals `∑_{n ∈ Icc 1 N} b n · (G N - G n)`. -/
private lemma abelStep (G dG : ℝ → ℂ) (hderiv : ∀ t : ℝ, HasDerivAt G (dG t) t)
    (hcont : Continuous dG) (N : ℕ) (b : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..(N : ℝ),
        dG t * (∑ n ∈ Finset.Icc 1 N, b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0)))
      = ∑ n ∈ Finset.Icc 1 N, b n * (G (N : ℝ) - G (n : ℝ)) := by
  have h1 : (∫ t in (0 : ℝ)..(N : ℝ),
        dG t * (∑ n ∈ Finset.Icc 1 N, b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0)))
      = ∫ t in (0 : ℝ)..(N : ℝ),
          ∑ n ∈ Finset.Icc 1 N, dG t * (b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Finset.mul_sum]
  rw [h1]
  have hInt : ∀ n ∈ Finset.Icc 1 N,
      IntervalIntegrable (fun t : ℝ => dG t * (b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0)))
        volume (0 : ℝ) (N : ℝ) := by
    intro n hn
    have heq : (fun t : ℝ => dG t * (b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0)))
        = Set.indicator {t : ℝ | (n : ℝ) ≤ t} (fun t => dG t * b n) := by
      funext t
      rw [Set.indicator_apply]
      by_cases h : (n : ℝ) ≤ t <;> simp [h]
    rw [heq]
    have hc : Continuous (fun t : ℝ => dG t * b n) := hcont.mul continuous_const
    have hii := hc.intervalIntegrable (μ := volume) (0 : ℝ) (N : ℝ)
    exact ⟨Integrable.indicator hii.1 measurableSet_Ici,
      Integrable.indicator hii.2 measurableSet_Ici⟩
  rw [intervalIntegral.integral_finsetSum
    (f := fun n t => dG t * (b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0))) hInt]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have h0n : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn'.2
  rw [show (∫ t in (0 : ℝ)..(N : ℝ),
        dG t * (b n * (if (n : ℝ) ≤ t then (1 : ℂ) else 0)))
      = ∫ t in (0 : ℝ)..(N : ℝ),
          b n * (dG t * (if (n : ℝ) ≤ t then (1 : ℂ) else 0)) from by
    apply intervalIntegral.integral_congr
    intro t _
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [integralMulIndicatorIci dG (0 : ℝ) (n : ℝ) (N : ℝ) h0n hnN]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G) (f' := dG)
    (fun x _ => hderiv x) (hcont.intervalIntegrable (μ := volume) _ _)]

theorem lambdaAbelReduce (A δ : ℝ) (hA0 : 0 < A) :
    (∑ n ∈ Finset.Icc 1 ⌈4 * A⌉₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (Complex.I * (δ : ℂ)) * ((Work.BMF.bumpFn (n / A)) : ℂ))
      = - ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
            (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
              (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  (n : ℂ) ^ (Complex.I * (δ : ℂ))) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((Work.BMF.bumpFn (t / A)) : ℂ))
      ((((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ)) t :=
    fun t => hasDerivAt_bumpFn_div A t
  have hcont : Continuous (fun t : ℝ => (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ)) :=
    continuous_deriv_bumpFn_div A
  have hstep := abelStep (fun t : ℝ => ((Work.BMF.bumpFn (t / A)) : ℂ))
      (fun t : ℝ => (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ)) hderiv hcont
      ⌈4 * A⌉₊
      (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (Complex.I * (δ : ℂ)))
  have hfloor : (∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ))))
      = ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
          (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
            (∑ n ∈ Finset.Icc 1 ⌈4 * A⌉₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (Complex.I * (δ : ℂ))
                * (if (n : ℝ) ≤ t then (1 : ℂ) else 0)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    beta_reduce
    rw [Set.uIcc_of_le (Nat.cast_nonneg (⌈4 * A⌉₊))] at ht
    obtain ⟨ht0, htN⟩ := Set.mem_Icc.mp ht
    rw [floorIccSumEqIndicator
      (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (Complex.I * (δ : ℂ))) ⌈4 * A⌉₊ t ht0 htN]
  have hGN : ((Work.BMF.bumpFn (((⌈4 * A⌉₊ : ℕ) : ℝ) / A)) : ℂ) = 0 := by
    rw [bumpFn_div_ceil_eq_zero hA0, Complex.ofReal_zero]
  have hval : (∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ))))
      = - ∑ n ∈ Finset.Icc 1 ⌈4 * A⌉₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (Complex.I * (δ : ℂ))
            * ((Work.BMF.bumpFn (n / A)) : ℂ) := by
    rw [hfloor, hstep]
    rw [hGN]
    simp only [zero_sub]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hval]
  simp

end

end Work.BMF.mr_core
