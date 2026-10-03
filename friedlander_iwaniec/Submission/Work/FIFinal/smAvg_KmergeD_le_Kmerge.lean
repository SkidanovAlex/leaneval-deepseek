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

namespace Work.FIFinal

open Finset MeasureTheory
open scoped Interval

noncomputable section

/-- The `ν₁`-fibre `y ↦ Kfac ν₁ (y/ν₁)` averaged against `dy/y` over `[Y, eY]` is at most the
unsubstituted fibre `w ↦ Kfac ν₁ w` averaged against `dw/w` over `[Y/Δ, eY]`; summing over
`ν₁ ∈ [1,Δ]` gives the corresponding statement for `KmergeD ≤ Kmerge`. -/
lemma smAvg_KmergeD_le_Kmerge (a lam : ℕ → ℝ) (N : ℕ) {s : ℝ} {Δ : ℕ} {Y : ℝ}
    (hspos : 0 < s) (hY : 0 < Y) (hΔ : 1 ≤ Δ) (hlam_le1 : ∀ ν, |lam ν| ≤ 1) :
    (∫ y in Y..(Real.exp 1 * Y), Submission.ASP.KmergeD a lam N s Δ y / y)
      ≤ ∫ w in Y / (Δ : ℝ)..(Real.exp 1 * Y), Submission.ASP.Kmerge a lam N s Δ w / w := by
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hApos : 0 < Y / (Δ : ℝ) := div_pos hY hΔpos
  have heY : 0 < Real.exp 1 * Y := mul_pos (Real.exp_pos 1) hY
  have hYle : Y ≤ Real.exp 1 * Y := by
    simpa using mul_le_mul_of_nonneg_right
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hY.le
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)
  have hAeY : Y / (Δ : ℝ) ≤ Real.exp 1 * Y :=
    le_trans (by rw [div_le_iff₀ hΔpos]; nlinarith [hY.le, hΔ1, he1]) hYle
  have h1 : (∫ y in Y..(Real.exp 1 * Y), Submission.ASP.KmergeD a lam N s Δ y / y)
      = ∑ ν₁ ∈ Finset.Icc 1 Δ,
          ∫ y in Y..(Real.exp 1 * Y), Submission.ASP.Kfac a lam N s ν₁ (y / ν₁) / y := by
    rw [show (∫ y in Y..(Real.exp 1 * Y), Submission.ASP.KmergeD a lam N s Δ y / y)
        = ∫ y in Y..(Real.exp 1 * Y),
            ∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.Kfac a lam N s ν₁ (y / ν₁) / y from
      intervalIntegral.integral_congr (fun y _ => by
        simp only [Submission.ASP.KmergeD, Finset.sum_div])]
    exact intervalIntegral.integral_finsetSum
      (fun ν₁ _ => Submission.ASP.intervalIntegrable_Kfac_div_div a lam N hspos ν₁ hY hYle hlam_le1)
  rw [h1]
  have h2 : ∀ ν₁ ∈ Finset.Icc 1 Δ,
      (∫ y in Y..(Real.exp 1 * Y), Submission.ASP.Kfac a lam N s ν₁ (y / ν₁) / y)
        ≤ ∫ w in Y / (Δ : ℝ)..(Real.exp 1 * Y), Submission.ASP.Kfac a lam N s ν₁ w / w := by
    intro ν₁ hν₁
    obtain ⟨hν₁1, hν₁Δ⟩ := Finset.mem_Icc.mp hν₁
    have hν₁pos : (0 : ℝ) < (ν₁ : ℝ) := by exact_mod_cast (by omega : 0 < ν₁)
    have hν₁1' : (1 : ℝ) ≤ (ν₁ : ℝ) := by exact_mod_cast hν₁1
    have hν₁Δ' : (ν₁ : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hν₁Δ
    rw [Submission.ASP.integral_comp_div_div_div (Φ := Submission.ASP.Kfac a lam N s ν₁)
      hν₁pos Y (Real.exp 1 * Y)]
    refine intervalIntegral.integral_mono_interval ?_ ?_ ?_ ?_ ?_
    · rw [div_le_div_iff₀ hΔpos hν₁pos]; nlinarith [hY.le, hν₁Δ']
    · exact div_le_div_of_nonneg_right hYle hν₁pos.le
    · rw [div_le_iff₀ hν₁pos]; nlinarith [heY.le, hν₁1']
    · change ∀ᵐ w ∂(volume.restrict (Set.Ioc (Y / (Δ : ℝ)) (Real.exp 1 * Y))),
          (0 : ℝ) ≤ Submission.ASP.Kfac a lam N s ν₁ w / w
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun w hw =>
        div_nonneg (Submission.ASP.Kfac_nonneg a lam N s ν₁ w) (le_of_lt (lt_trans hApos hw.1)))
    · exact Submission.ASP.intervalIntegrable_Kfac_div a lam N hspos ν₁ hApos hAeY hlam_le1
  refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
  rw [show (∫ w in Y / (Δ : ℝ)..(Real.exp 1 * Y), Submission.ASP.Kmerge a lam N s Δ w / w)
      = ∫ w in Y / (Δ : ℝ)..(Real.exp 1 * Y),
          ∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.Kfac a lam N s ν₁ w / w from
    intervalIntegral.integral_congr (fun w _ => by
      simp only [Submission.ASP.Kmerge, Finset.sum_div])]
  exact (intervalIntegral.integral_finsetSum
    (fun ν₁ _ => Submission.ASP.intervalIntegrable_Kfac_div a lam N hspos ν₁ hApos hAeY
      hlam_le1)).symm

end

end Work.FIFinal
