import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.Comp.young_conv_lp
import Submission.Work.Diff.STE.CSq_comp_le
import Submission.Work.Diff.STE.Comp3.integral_prod_block_general

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

/-- `x ↦ (1 + x)^s` is monotone on the nonnegative half-line (in the form needed below, where
`1 + x` and `1 + y` are both nonnegative). -/
private lemma one_add_pow_le_one_add_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (s : ℕ) :
    (1 + a) ^ s ≤ (1 + b) ^ s :=
  pow_le_pow_left₀ (by linarith) (by linarith) s

/-- **(c): product bound for the shifted family `γ = ∂u`, with transparent constants.**

Let `c` be the coefficient family of the unknown and `γ := dmulV [i₀] c` the family of the first
derivative `∂_{i₀} u` of its Fourier series.  If `Λ` bounds the `ℓ¹` norm `∑_k ‖γ k‖`, if the
families `d i` are dominated by the multipliers of order `β i` *with respect to `γ`* and
`∑ i, β i = s`, then `∫ ‖∏ i, seriesFun (d i)‖² ≤ ((2π)^s (1 + Λ)^s)² (1 + CSq s γ)`.

`Λ` is an explicit parameter of the conclusion (no hidden constant, so the bound is uniform across
the trajectory family, which is what the Grönwall assembly needs).  This is
`Work.Diff.STE.Comp3.integral_prod_block_general` at `γ := dmulV [i₀] c`; it is the form in which
the Faà di Bruno blocks of the DeTurck nonlinearity arise (a block of size `β` on the `∂u`-slot is
a derivative of `u` of order `β + 1`, costing exactly `β`, so a term using `a` x-slots and `#A`
`u`-blocks costs `k + 1 - a - #A ≤ k`).  The work is the reduction producing the parent theorem's
hypotheses for `γ` from `hmom` on `c`: `summable_dmulV` (`ENormSq_seriesFun_le.lean:135`) gives the
moments of `γ` and the `ℓ¹` summability from `hmom`, `norm_sq_dmulV_le` gives
`‖k‖^{2s}‖γ k‖² ≤ (2π)² wt^{s+2}‖c k‖²` (summable via `hmom`), and `hΛ` gives
`(1 + ∑‖γ k‖)^s ≤ (1 + Λ)^s` by monotonicity (`Λ ≥ 0`).  (A twin at
`Diff/STE/flat/integral_prod_shifted_family_le` carries the same statement and was left `sorry` by
an elaboration test; proving this one supersedes it.) -/
theorem integral_prod_shifted_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 0 < s) (c : (ι → ℤ) → ℂ) (i₀ : ι)
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖)
    (Λ : ℝ) (hΛ : (∑' k : ι → ℤ, ‖Work.Diff.STE.dmulV [i₀] c k‖) ≤ Λ)
    {r : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (d : Fin r → (ι → ℤ) → ℂ) (β : Fin r → ℕ)
    (hβ : ∀ i, β i ≤ s) (hβsum : ∑ i, β i = s)
    (hd : ∀ i k, ‖d i k‖ ≤ (2 * Real.pi * ‖k‖) ^ (β i) * ‖Work.Diff.STE.dmulV [i₀] c k‖)
    (hsm : ∀ i, Summable fun k : ι → ℤ => ‖d i k‖ ^ (Work.Diff.STE.yExp s (β i))) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖∏ i, Work.Diff.STE.seriesFun (d i) x‖ ^ 2
      ≤ (((2 * Real.pi) ^ s * (1 + Λ) ^ s) ^ 2)
          * (1 + Work.Diff.STE.CSq s (Work.Diff.STE.dmulV [i₀] c)) := by
  classical
  -- Abbreviation for the shifted family `γ = ∂_{i₀} u`.
  set γ : (ι → ℤ) → ℂ := Work.Diff.STE.dmulV [i₀] c with hγ
  have hγk : ∀ k : ι → ℤ, γ k = Work.Diff.STE.dmulV [i₀] c k := fun k => rfl
  -- The moment (decay) hypotheses for `γ` are inherited from those for `c`.
  have hmomγ : ∀ N : ℕ, Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖γ k‖ :=
    fun N => Work.Diff.STE.summable_dmulV [i₀] c hmom N
  have hΛγ : Summable fun k : ι → ℤ => ‖γ k‖ := by
    have h := hmomγ 0
    simpa using h
  have hγΛ : (∑' k : ι → ℤ, ‖γ k‖) ≤ Λ := hΛ
  -- The weighted `ℓ²` hypothesis, dominated by the moments of `c` via `norm_sq_dmulV_le`.
  have hQγ : Summable fun k : ι → ℤ => (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (norm_nonneg k) _) (sq_nonneg _))
      (fun k => ?_)
      (((Work.Diff.STE.summable_wt_pow_mul_norm_sq c hmom (s + 1))).mul_left
        ((2 * Real.pi) ^ 2))
    have h1 : (‖k‖ : ℝ) ^ (2 * s) ≤ (Work.Diff.STE.wt k) ^ s := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) (Work.Diff.STE.sq_norm_le_wt k) s
    have h2 : ‖γ k‖ ^ 2 ≤ ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt k) ^ ([i₀]).length
        * ‖c k‖ ^ 2 := by
      rw [hγk]
      exact Work.Diff.STE.norm_sq_dmulV_le [i₀] c k
    calc (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ s * ‖γ k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ (Work.Diff.STE.wt k) ^ s
            * (((2 * Real.pi) ^ 2 * Work.Diff.STE.wt k) ^ ([i₀]).length * ‖c k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (Work.Diff.STE.wt_pos k).le s)
      _ = (2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (s + 1) * ‖c k‖ ^ 2) := by
          simp only [List.length_cons, List.length_nil]
          rw [pow_succ]
          ring
  -- The general block estimate, instantiated at `γ`.
  have hmain := Work.Diff.STE.Comp3.integral_prod_block_general s hs γ hmomγ hΛγ hQγ
    hr hrs d β hβ hβsum (fun i k => (hd i k)) hsm
  refine hmain.trans ?_
  -- Replace `1 + ∑ ‖γ k‖` by the (larger) explicit parameter `1 + Λ`.
  have hCSq0 : (0 : ℝ) ≤ 1 + Work.Diff.STE.CSq s γ := by
    have : (0 : ℝ) ≤ Work.Diff.STE.CSq s γ :=
      tsum_nonneg fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le s) (sq_nonneg _)
    linarith
  refine mul_le_mul_of_nonneg_right ?_ hCSq0
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) s)
  exact one_add_pow_le_one_add_pow (tsum_nonneg fun k => norm_nonneg _) hγΛ s

end Work.Diff.STE.flat
