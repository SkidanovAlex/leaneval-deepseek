import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem elim_core {n m d : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n) (hd : 1 ≤ d)
    {ψ M : ℝ} (hψ : 1 ≤ ψ) (hM : (n : ℝ) * Real.log n + Real.log d ≤ M)
    (hM2 : Real.log 2 ≤ M) :
    2 * (M + Real.log 2 + (m : ℝ) * Real.log (9 * (m : ℝ) * (d : ℝ) ^ 2) + (m : ℝ) * Real.log ψ)
      ≤ 64 * (n : ℝ) * ((n : ℝ) + 1) * ψ * M := by
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hmnR : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have hn1R : (1:ℝ) ≤ (n:ℝ) := by linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hψpos : (0:ℝ) < ψ := by linarith
  have hψnn : (0:ℝ) ≤ ψ := le_of_lt hψpos
  have hMnn : (0:ℝ) ≤ M := by linarith [Real.log_two_gt_d9]
  have hMlb : (1:ℝ)/2 ≤ M := by linarith [Real.log_two_gt_d9]
  have hlogn_nn : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_nonneg hn1R
  have hlogd_nn : (0:ℝ) ≤ Real.log (d:ℝ) := Real.log_nonneg hdR
  have hlogm_nn : (0:ℝ) ≤ Real.log (m:ℝ) := Real.log_nonneg hmR
  have hlog9_nn : (0:ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hnlogn_nn : (0:ℝ) ≤ (n:ℝ) * Real.log (n:ℝ) := mul_nonneg (le_of_lt hnpos) hlogn_nn
  have hMlogd : Real.log (d:ℝ) ≤ M := by linarith
  -- bound m log m
  have hmlogm : (m:ℝ) * Real.log (m:ℝ) ≤ M := by
    have h1 : Real.log (m:ℝ) ≤ Real.log (n:ℝ) := Real.log_le_log hmpos hmnR
    have h2 : (m:ℝ) * Real.log (m:ℝ) ≤ (m:ℝ) * Real.log (n:ℝ) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hmpos)
    have h3 : (m:ℝ) * Real.log (n:ℝ) ≤ (n:ℝ) * Real.log (n:ℝ) :=
      mul_le_mul_of_nonneg_right hmnR hlogn_nn
    linarith
  -- log 9 ≤ 4 M
  have hlog9_4M : Real.log 9 ≤ 4 * M := by
    have h : Real.log 9 ≤ Real.log ((2:ℝ)^4) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have h9 : (m:ℝ) * Real.log 9 ≤ 4 * (n:ℝ) * M := by
    have h1 : (m:ℝ) * Real.log 9 ≤ (n:ℝ) * Real.log 9 :=
      mul_le_mul_of_nonneg_right hmnR hlog9_nn
    have h2 : (n:ℝ) * Real.log 9 ≤ (n:ℝ) * (4 * M) :=
      mul_le_mul_of_nonneg_left hlog9_4M (le_of_lt hnpos)
    linarith
  have hdlog : (m:ℝ) * Real.log (d:ℝ) ≤ (n:ℝ) * M := by
    have h1 : (m:ℝ) * Real.log (d:ℝ) ≤ (n:ℝ) * Real.log (d:ℝ) :=
      mul_le_mul_of_nonneg_right hmnR hlogd_nn
    have h2 : (n:ℝ) * Real.log (d:ℝ) ≤ (n:ℝ) * M :=
      mul_le_mul_of_nonneg_left hMlogd (le_of_lt hnpos)
    linarith
  have hlogψ_le : Real.log ψ ≤ ψ := Real.log_le_self hψnn
  have hψb : (m:ℝ) * Real.log ψ ≤ (n:ℝ) * ψ := by
    have h1 : (m:ℝ) * Real.log ψ ≤ (m:ℝ) * ψ :=
      mul_le_mul_of_nonneg_left hlogψ_le (le_of_lt hmpos)
    have h2 : (m:ℝ) * ψ ≤ (n:ℝ) * ψ := mul_le_mul_of_nonneg_right hmnR hψnn
    linarith
  -- decompose the logarithm of the product
  have hlog : Real.log (9 * (m:ℝ) * (d:ℝ)^2)
      = Real.log 9 + Real.log (m:ℝ) + 2 * Real.log (d:ℝ) := by
    have hm0 : (m:ℝ) ≠ 0 := ne_of_gt hmpos
    have hd0 : ((d:ℝ)^2) ≠ 0 := by positivity
    rw [Real.log_mul (by positivity) hd0, Real.log_mul (by norm_num) hm0, Real.log_pow]
    push_cast
    ring
  rw [hlog]
  -- reduce the quadratic tail
  have key : 6*M + 12*(n:ℝ)*M + 2*(n:ℝ)*ψ ≤ 22 * (n:ℝ) * ψ * M := by
    have hnψ : (1:ℝ) ≤ (n:ℝ) * ψ := by nlinarith
    have h1 : 6*M ≤ 6*(n:ℝ)*ψ*M := by
      have h : 6*M*1 ≤ 6*M*((n:ℝ)*ψ) := mul_le_mul_of_nonneg_left hnψ (by linarith)
      have he : 6*M*((n:ℝ)*ψ) = 6*(n:ℝ)*ψ*M := by ring
      linarith
    have h2 : 12*(n:ℝ)*M ≤ 12*(n:ℝ)*ψ*M := by
      have h : M*1 ≤ M*ψ := mul_le_mul_of_nonneg_left hψ hMnn
      nlinarith [h]
    have h3 : 2*(n:ℝ)*ψ ≤ 4*(n:ℝ)*ψ*M := by
      have h : (2:ℝ) ≤ 4*M := by linarith
      have h4 : (n:ℝ)*ψ*2 ≤ (n:ℝ)*ψ*(4*M) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg (le_of_lt hnpos) hψnn)
      nlinarith [h4]
    linarith
  have key2 : 22 * (n:ℝ) * ψ * M ≤ 64 * (n:ℝ) * ((n:ℝ)+1) * ψ * M := by
    have h : (22:ℝ) ≤ 64 * ((n:ℝ)+1) := by linarith
    have h0 : (0:ℝ) ≤ (n:ℝ) * ψ * M := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h h0]
  nlinarith [hM2, h9, hmlogm, hdlog, hψb, key, key2]

end Work.BW
