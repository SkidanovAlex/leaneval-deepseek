import Mathlib
import Submission.Work.KMTContract.periodizeCoeEqTsum
import Submission.Work.KMTContract.Defs

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

noncomputable section

/-- **The cutoff is `1` on a small arc.**  If `2^k ≤ 1/2` and `|θ| ≤ 2^k/2`, then
`η_{≤k}` equals `1` at the circle point `θ`. -/
theorem mae_Phi_eq_one_of_small {k : ℤ} (hk : (2 : ℝ) ^ k ≤ 1 / 2) {θ : ℝ}
    (hθ : |θ| ≤ (2 : ℝ) ^ k / 2) :
    periodize (etaCut Work.KMTContract.kmtEta k) (θ : Work.Analysis.IonescuWainger.Circle) = 1 := by
  rw [Work.KMTContract.periodizeCoeEqTsum (etaCut Work.KMTContract.kmtEta k) θ]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hzero : ∀ n : ℤ, n ≠ 0 → etaCut Work.KMTContract.kmtEta k (θ + (n : ℝ)) = 0 := by
    intro n hn
    rw [etaCut]
    refine Work.KMTContract.kmtEta_zero ?_
    rw [abs_div, abs_of_pos hpos, one_le_div hpos]
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hn)
    have h2 : |(n : ℝ)| - |θ| ≤ |θ + (n : ℝ)| := by
      have h := abs_sub_abs_le_abs_sub (n : ℝ) (-θ)
      rw [sub_neg_eq_add] at h
      simpa [sub_eq_add_neg, add_comm] using h
    have h3 : (2 : ℝ) ^ k ≤ 1 - (2 : ℝ) ^ k / 2 := by linarith
    linarith [hpos, hθ]
  rw [tsum_eq_single 0 (fun n hn => hzero n hn)]
  simp only [Int.cast_zero, add_zero]
  rw [etaCut]
  refine Work.KMTContract.kmtEta_one ?_
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  linarith [hpos, hθ]

end

end Work.KMTPlan.A6
