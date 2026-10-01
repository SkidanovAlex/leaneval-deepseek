import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.Density4

/-- For a natural number `K ≥ 1`, the sum `selU (K:ℝ)` agrees with the
log-weighted Möbius reciprocal sum `logWeightedMuSum K`, because `⌊(K:ℝ)⌋₊ = K`
and `log(K/m) = log K - log m` for `m ≥ 1`. -/
lemma selU_natCast_eq_logWeightedMuSum (K : ℕ) (hK : 1 ≤ K) :
    selU (K:ℝ) = Commons.NumberTheory.Moebius.logWeightedMuSum K := by
  unfold selU Commons.NumberTheory.Moebius.logWeightedMuSum
  rw [Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  rw [Real.log_div (ne_of_gt hKpos) (ne_of_gt hmpos)]

/-- Telescoping of the log-weighted Möbius reciprocal sum. -/
lemma logWeightedMuSum_sub_eq_sum_Ico (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    Commons.NumberTheory.Moebius.logWeightedMuSum M - Commons.NumberTheory.Moebius.logWeightedMuSum N
      = ∑ i ∈ Finset.Ico N M, Commons.NumberTheory.Moebius.muRecipSum i *
          (Real.log ((i:ℝ) + 1) - Real.log (i:ℝ)) := by
  rw [← Finset.sum_Ico_sub (Commons.NumberTheory.Moebius.logWeightedMuSum) hNM]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  have hi1 : 1 ≤ i := le_trans hN hi.1
  have hs := Commons.NumberTheory.Moebius.logWeightedMuSum_succ hi1
  linarith

/-- Telescoping of `selU`: `selU M - selU N = Σ_{N ≤ i < M} muRecipSum i * log((i+1)/i)`.
Hint: `selU (K:ℝ) = ∑_{m ≤ K} (μ m/m)(log K - log m) = logWeightedMuSum K` for `K ≥ 1`
(use `Real.log_div`), and the imported file `Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound`
already proves `logWeightedMuSum_eq` / `logWeightedMuSum_succ`, which is exactly the telescoping step. -/
theorem selU_sub_eq_sum_Ico (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    Work.LinnikAreas.Density4.selU (M:ℝ) - Work.LinnikAreas.Density4.selU (N:ℝ)
      = ∑ i ∈ Finset.Ico N M,
          Commons.NumberTheory.Moebius.muRecipSum i * Real.log (((i:ℝ) + 1) / (i:ℝ)) := by
  have hM : 1 ≤ M := le_trans hN hNM
  rw [selU_natCast_eq_logWeightedMuSum M hM, selU_natCast_eq_logWeightedMuSum N hN]
  rw [logWeightedMuSum_sub_eq_sum_Ico N M hN hNM]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  have hi1 : 1 ≤ i := le_trans hN hi.1
  have hipos : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi1
  rw [Real.log_div (by positivity) (ne_of_gt hipos)]

end Work.LinnikAreas.Density4
