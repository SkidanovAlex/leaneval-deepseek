import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.Sat

/-- The `λ > 0` branch of `B(λ)`: the first term
`(1 - e^{-2Kλ})/(6K²λ)` is strictly positive, the second is non-negative.  (Same content as
`Work.LinnikContract.API.Bfun_pos`, reproved here so that this file is self-contained.) -/
private lemma Bfun_gt_zero_of_pos {K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam) :
    0 < Work.LinnikContract.Bfun K lam := by
  rw [Work.LinnikContract.Bfun, if_neg (ne_of_gt hlam)]
  have hden1 : 0 < 6 * K ^ 2 * lam := by positivity
  have hnum1 : 0 < 1 - Real.exp (-2 * K * lam) := by
    have hlt : Real.exp (-2 * K * lam) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith
    linarith
  have h1 : 0 < (1 - Real.exp (-2 * K * lam)) / (6 * K ^ 2 * lam) := div_pos hnum1 hden1
  have hnum2 : 0 ≤ 2 * K * lam - 1 + Real.exp (-2 * K * lam) := by
    have h := Real.add_one_le_exp (-(2 * K * lam))
    have harg : -2 * K * lam = -(2 * K * lam) := by ring
    rw [harg]
    linarith
  have h2 : 0 ≤ (2 * K * lam - 1 + Real.exp (-2 * K * lam)) / (2 * K ^ 2 * lam ^ 2) :=
    div_nonneg hnum2 (by positivity)
  linarith

/-- The `λ = 0` branch of `B(λ)`: `B(0) = 1/(3K) + 1 > 0` for `K > 0`. -/
private lemma Bfun_zero_gt_zero {K : ℝ} (hK : 0 < K) : 0 < Work.LinnikContract.Bfun K 0 := by
  rw [Work.LinnikContract.Bfun, if_pos rfl]
  have : 0 < 1 / (3 * K) := by positivity
  linarith

/-- `B(λ) > 0` for every `K > 0`, `λ ≥ 0`. -/
private lemma Bfun_gt_zero {K lam : ℝ} (hK : 0 < K) (hlam : 0 ≤ lam) :
    0 < Work.LinnikContract.Bfun K lam := by
  rcases eq_or_lt_of_le hlam with h | h
  · rw [← h]
    exact Bfun_zero_gt_zero hK
  · exact Bfun_gt_zero_of_pos hK h

/-- Non-degeneracy of the hypothesis list of AREA 5 (`PerCharCert`), *uniformly* in the parameters:
(i) there are `K, R, η, lam` with `0 < K ≤ 1`, `0 < R`, `0 < η`, `0 ≤ lam ≤ R` (take
`K = 3/10`, `R = 1`, `η = 1/10`, `lam = R = 1`, the extreme point of the interval) for which
`B(lam) > 0` and the right-hand side `K²(B(lam) + η)` of the conclusion is strictly positive — so
the per-character bound is a real inequality and not `boxAbs ≤ 0`;
(ii) in fact `K ^ 2 * (B lam + η) > 0` for *every* `K, lam, η` with `0 < K`, `0 ≤ lam`, `0 < η`
(use `Bfun_pos`/`linnikB_nonneg` for `lam > 0` and the branch `B(0) = 1/(3K) + 1` for `lam = 0`).

No `native_decide`. -/
theorem area5_hyps_sat :
    (∃ (K R η lam : ℝ), 0 < K ∧ K ≤ 1 ∧ 0 < R ∧ 0 < η ∧ 0 ≤ lam ∧ lam ≤ R ∧ lam = R ∧
      0 < Work.LinnikContract.Bfun K lam ∧
      0 < K ^ 2 * (Work.LinnikContract.Bfun K lam + η)) ∧
    (∀ (K lam η : ℝ), 0 < K → 0 ≤ lam → 0 < η →
      0 < K ^ 2 * (Work.LinnikContract.Bfun K lam + η)) := by
  refine ⟨⟨3/10, 1, 1/10, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, rfl, ?_, ?_⟩, ?_⟩
  · exact Bfun_gt_zero_of_pos (by norm_num) (by norm_num)
  · have hB : 0 < Work.LinnikContract.Bfun (3/10 : ℝ) 1 :=
      Bfun_gt_zero_of_pos (by norm_num) (by norm_num)
    have hK : (0 : ℝ) < (3/10) ^ 2 := by norm_num
    exact mul_pos hK (by linarith)
  · intro K lam η hK hlam hη
    exact mul_pos (pow_pos hK 2) (add_pos (Bfun_gt_zero hK hlam) hη)

end Work.LinnikContract.Sat
