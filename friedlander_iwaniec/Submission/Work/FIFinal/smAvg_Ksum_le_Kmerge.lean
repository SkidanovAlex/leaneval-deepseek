/-
# `Work.FIFinal.smAvg_Ksum_le_Kmerge`

The *smoothed* average of the `§7` inner sums `∑_{k ≤ N} |Ksum_k(y)|` is bounded by the
merged (`Kmerge`) sum, which is the shape to which the bilinear hypothesis (B′) applies.

The proof is the composite of two independent pieces:

* `Work.FIFinal.sum_abs_Ksum_le_KmergeD` — the *pointwise* bound
  `∑_{k ≤ N} |Ksum a lam N y (s·y) k| ≤ KmergeD a lam N s Δ y` (from `Ksum_abs_le_merge`
  in `Submission.ASP.S7b`, using the support hypothesis `λ_ν = 0` for `ν > Δ` to collapse
  the `ν₁`-range `[1,N]` to `[1,Δ]`);
* `Work.FIFinal.smAvg_KmergeD_le_Kmerge` — the *averaging* step, which pulls the `ν₁`-fibres
  out of the integral, substitutes `y = ν₁ u`, extends the window `[Y/ν₁, eY/ν₁] ⊆ [Y/Δ, eY]`
  (valid because `Kfac ≥ 0`), and reassembles `Kmerge`.

The target lemma is then just monotonicity of the integral applied to the pointwise bound,
followed by the averaging step.  (No hypothesis (B′) is needed: the output is still the
`Kmerge` integral rather than a numerical bound.)
-/
import Mathlib
import Submission.Work.FIChain.BprimeWindowIntegrated
import Submission.Work.FIChain.RhoWindowIntegrated2
import Submission.ASP.Defs
import Submission.ASP.S3v
import Submission.ASP.S7b
import Submission.ASP.S7c
import Submission.ASP.S7d
import Submission.ASP.S7e
import Submission.ASP.S8
import Submission.ASP.S8b
import Submission.Work.FIFinal.sum_abs_Ksum_le_KmergeD
import Submission.Work.FIFinal.smAvg_KmergeD_le_Kmerge

namespace Work.FIFinal

open Finset MeasureTheory
open scoped Interval

lemma smAvg_Ksum_le_Kmerge (a lam : ℕ → ℝ) (N : ℕ) {w : ℕ → ℝ} {s Y : ℝ} {J : ℕ} {Δ : ℕ}
    (hs : s = (2 : ℝ) ^ J) (hY : 0 < Y) (hΔ : 1 ≤ Δ)
    (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1)
    (ha : ∀ n, ¬ Squarefree n → a n = 0) :
    (∫ y in Y..(Real.exp 1 * Y),
        (∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k|) / y)
      ≤ ∫ z in Y / (Δ : ℝ)..(Real.exp 1 * Y), Submission.ASP.Kmerge a lam N s Δ z / z := by
  have hspos : 0 < s := by rw [hs]; positivity
  have hYle : Y ≤ Real.exp 1 * Y :=
    le_mul_of_one_le_left hY.le (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1))
  -- Step A: integrate the pointwise bound `∑_k |Ksum_k| ≤ KmergeD`.
  have stepA : (∫ y in Y..(Real.exp 1 * Y),
        (∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k|) / y)
      ≤ ∫ y in Y..(Real.exp 1 * Y), Submission.ASP.KmergeD a lam N s Δ y / y := by
    rw [intervalIntegral.integral_of_le hYle, intervalIntegral.integral_of_le hYle]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · change ∀ᵐ y ∂(volume.restrict (Set.Ioc Y (Real.exp 1 * Y))),
          (0 : ℝ)
            ≤ (∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k|) / y
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun y hy =>
        div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
          (le_of_lt (lt_trans hY hy.1)))
    · exact (Submission.ASP.intervalIntegrable_KmergeD_div a lam N hspos Δ hY hYle
        hlam_le1).1
    · change ∀ᵐ y ∂(volume.restrict (Set.Ioc Y (Real.exp 1 * Y))),
          (∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k|) / y
            ≤ Submission.ASP.KmergeD a lam N s Δ y / y
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun y hy =>
        div_le_div_of_nonneg_right
          (sum_abs_Ksum_le_KmergeD a lam N hspos hΔ hlam_supp ha y)
          (le_of_lt (lt_trans hY hy.1)))
  -- Step B: substitute `y = ν₁ u` in each fibre and extend the window to `[Y/Δ, eY]`.
  exact stepA.trans (smAvg_KmergeD_le_Kmerge a lam N hspos hY hΔ hlam_le1)

end Work.FIFinal
