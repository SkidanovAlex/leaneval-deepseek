import Mathlib
import Submission.Work.A7Hi2.RealScaleDefs

/-!
# Summability of the linearised difference kernels on `ℤ`

`linDiffKernR K σ ρ U ω z = ∑_{n ∈ U} ±(bumpKernR K (σ n) z − bumpKernR K (ρ n) z)` is a finite
signed sum of sampled dilations of the Schwartz kernel `K`.  Each sampled dilation
`z ↦ (1/σ) K (z/σ)` decays faster than any power of `|z|` (it is `≤ C · s · |z|⁻²` by the Schwartz
decay `‖x‖ ^ k ‖K x‖ ≤ C` applied at `x = z/σ`), hence is summable on `ℤ`; a finite sum of summable
functions is summable, and the norm of the finite sum is controlled by the sum of the norms.
-/

set_option autoImplicit false

namespace Work.A7Hi2

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-- Each sampled dilation of a Schwartz function is summable on `ℤ`: the Schwartz decay
`‖x‖ ^ 2 * ‖K x‖ ≤ C` at `x = j / s` gives `‖bumpKernR K s j‖ ≤ C * s * |j|⁻²`, and `|j|⁻²` is
summable on `ℤ`. -/
private lemma summable_bumpKernR_auxSumm (K : SchwartzMap ℝ ℂ) {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun j : ℤ => ‖bumpKernR K s j‖) := by
  obtain ⟨C, _hCpos, hC⟩ := K.decay 2 0
  have hC' : ∀ x : ℝ, ‖x‖ ^ 2 * ‖(K : ℝ → ℂ) x‖ ≤ C := by
    intro x
    simpa using hC x
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hg : Summable (fun j : ℤ => (C * s) * (1 / (j : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left (C * s)
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with j hj
  have hjabs : 0 < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
  have hdec := hC' ((j : ℝ) / s)
  have hnorm : ‖(j : ℝ) / s‖ = |(j : ℝ)| / s := by
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs0]
  rw [hnorm] at hdec
  have hbump : ‖bumpKernR K s j‖ = (1 / s) * ‖(K : ℝ → ℂ) ((j : ℝ) / s)‖ := by
    rw [bumpKernR, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0]
  have hstep : (1 / s) * ‖(K : ℝ → ℂ) ((j : ℝ) / s)‖ ≤ C * s / |(j : ℝ)| ^ 2 := by
    have key : (|(j : ℝ)| / s) ^ 2 * ‖(K : ℝ → ℂ) ((j : ℝ) / s)‖ * (s / |(j : ℝ)| ^ 2)
        ≤ C * (s / |(j : ℝ)| ^ 2) :=
      mul_le_mul_of_nonneg_right hdec (div_nonneg hs0.le (sq_nonneg _))
    calc (1 / s) * ‖(K : ℝ → ℂ) ((j : ℝ) / s)‖
        = (|(j : ℝ)| / s) ^ 2 * ‖(K : ℝ → ℂ) ((j : ℝ) / s)‖ * (s / |(j : ℝ)| ^ 2) := by
          field_simp
      _ ≤ C * (s / |(j : ℝ)| ^ 2) := key
      _ = C * s / |(j : ℝ)| ^ 2 := by rw [mul_div_assoc]
  calc ‖(‖bumpKernR K s j‖ : ℝ)‖ = ‖bumpKernR K s j‖ := norm_norm _
    _ = (1 / s) * ‖(K : ℝ → ℂ) ((j : ℝ) / s)‖ := hbump
    _ ≤ C * s / |(j : ℝ)| ^ 2 := hstep
    _ = (C * s) * (1 / (j : ℝ) ^ 2) := by rw [sq_abs, div_eq_mul_one_div]

/-- Please keep all helpers `private`, or name them with the suffix `_auxSumm`, so this file does
not clash with the sibling file `Submission/Work/A7Hi2/linDiffKernR_symbol.lean`. -/
theorem linDiffKernR_summable (K : SchwartzMap ℝ ℂ) (σ ρ : ℕ → ℝ)
    (hσ1 : ∀ n, 1 ≤ σ n) (hρ1 : ∀ n, 1 ≤ ρ n) (U : Finset ℕ) (ω : ℕ → Bool) :
    Summable (fun j : ℤ => ‖linDiffKernR K σ ρ U ω j‖) := by
  have hterm : ∀ n ∈ U, Summable (fun j : ℤ =>
      ‖bumpKernR K (σ n) j‖ + ‖bumpKernR K (ρ n) j‖) := by
    intro n _
    exact (summable_bumpKernR_auxSumm K (hσ1 n)).add
      (summable_bumpKernR_auxSumm K (hρ1 n))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) (summable_sum hterm)
  rw [linDiffKernR]
  calc ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * diffKernR K (σ n) (ρ n) j‖
      ≤ ∑ n ∈ U, ‖Work.KMTAreas.ADev.bSign ω n * diffKernR K (σ n) (ρ n) j‖ :=
        norm_sum_le U _
    _ = ∑ n ∈ U, ‖diffKernR K (σ n) (ρ n) j‖ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul, Work.KMTAreas.ADev.norm_bSign, one_mul]
    _ ≤ ∑ n ∈ U, (‖bumpKernR K (σ n) j‖ + ‖bumpKernR K (ρ n) j‖) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [diffKernR]
        exact norm_sub_le _ _

end

end Work.A7Hi2
