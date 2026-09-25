import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.regionII.abdefs
import Submission.Work.RHContract.A.regionII.abnum
import Submission.Work.RHContract.A.regionII.theta_deficit_cert_173_501
import Submission.Work.RHContract.A.regionII.abS_le
import Submission.Work.RHContract.A.regionII.caC1_lower_A
import Submission.Work.RHContract.A.regionII.caNet2_lower_A
import Submission.Work.RHContract.A.regionII.num_checkA
import Submission.Work.RHContract.A.regionII.abA_le_abAbd
import Submission.Work.RHContract.A.regionII.caU_le_caUbd
import Submission.Work.RHContract.A.regionII.abJbd_le_abJ
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.Corpus

/-!
# Region II, part A (`30000 ≤ ξ < 10^5`): `caC1 + caNet2 ≥ (36/100)·u(ξ)`

The margin inequality of Region II is assembled from three ingredients:

* `caC1_lower_A`: `(498/1000)·abS n ξ ≤ caC1 ε` with `n = max ξ₂ 173`,
  where `abS = abJ − abA` is the explicit Abel lower bound for `Σ_{n<p≤ξ} 1/p²`
  (`abdefs.lean`, `abS_le`);
* `caNet2_lower_A`: `caNet2 ε ≥ −5·10^{-6}`;
* the numeric inequality `num_checkA`: `caUbd n + (498/1000)·abAbd n + 5·10^{-6} ≤ (498/1000)·abJbd`,
  together with the three transfers `abA n ≤ abAbd n`, `abJbd ≤ abJ ξ`,
  `(36/100)·u(ξ) ≤ caUbd n` (valid since `ξ ≥ 30000` and `n ≤ √(2.5ξ)+1`).

Indeed `abJ ξ ≥ abJbd` and `abA n ≤ abAbd n` give
`(498/1000)·abS n ξ ≥ (498/1000)·abJbd − (498/1000)·abAbd n`, and the numeric check turns
this into `≥ (36/100)·u(ξ) + 5·10^{-6}`, which the `caNet2` bound absorbs.
-/

namespace Work.RHContract.A.regionII

theorem caC1_add_caNet2_lower_A (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < 100000)
    (hθ : ∀ t : ℝ, 173 ≤ t → t ≤ 100000 → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t) :
    (36/100) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      ≤ Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε := by
  set z : ℕ := Work.RHPlan.caXi ε with hzdef
  set n : ℕ := max (Work.RHContract.Margin.caXi2 ε) 173 with hndef
  have hzr : (z : ℝ) = (Work.RHPlan.caXi ε : ℝ) := by rw [hzdef]
  have hz30000 : 30000 ≤ z := by
    have h : (30000 : ℝ) ≤ (z : ℝ) := by rw [hzr]; exact hlo
    exact_mod_cast h
  have hz1e5 : z ≤ 10 ^ 5 := by
    have h : (z : ℝ) < 10 ^ 5 := by rw [hzr]; norm_num at hhi ⊢; exact hhi
    have h2 : ((z : ℕ) : ℝ) ≤ ((10 ^ 5 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have hξ1530 : 1530 ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hx2 := Work.RHContract.A.caXi2_le_sqrt ε hε hξ1530
  have hx2' : (Work.RHContract.Margin.caXi2 ε : ℝ) ≤ Real.sqrt (2.5 * (z : ℝ)) + 1 := by
    have h := hx2
    rw [← hzr] at h
    exact h
  have hzle : (z : ℝ) ≤ 10 ^ 5 := by exact_mod_cast hz1e5
  have hn173 : 173 ≤ n := by rw [hndef]; exact le_max_right _ _
  have hn501 : n ≤ 501 := by
    rw [hndef]
    apply max_le _ (by norm_num)
    have hsqrt500 : Real.sqrt (2.5 * (10:ℝ)^5) = 500 := by
      rw [show (2.5 * (10:ℝ)^5) = 500^2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have h1 : 2.5 * (z : ℝ) ≤ 2.5 * (10:ℝ)^5 := by
      nlinarith [hzle]
    have h2 : Real.sqrt (2.5 * (z : ℝ)) + 1 ≤ 501 := by
      have h3 := Real.sqrt_le_sqrt h1
      rw [hsqrt500] at h3
      linarith
    have : (Work.RHContract.Margin.caXi2 ε : ℝ) ≤ 501 := le_trans hx2' h2
    exact_mod_cast this
  have hlink : (n : ℝ) ≤ Real.sqrt (2.5 * (z : ℝ)) + 1 := by
    rw [hndef]
    have hmax : ((max (Work.RHContract.Margin.caXi2 ε) 173 : ℕ) : ℝ)
        = max ((Work.RHContract.Margin.caXi2 ε : ℝ)) 173 := by
      rw [Nat.cast_max]; norm_num
    rw [hmax]
    apply max_le hx2' _
    have h30000 : (30000:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz30000
    have h1 : Real.sqrt (2.5 * (30000:ℝ)) ≤ Real.sqrt (2.5 * (z:ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : (173:ℝ) ≤ Real.sqrt (2.5 * (30000:ℝ)) + 1 := by
      have h3 : (273:ℝ) ≤ Real.sqrt (2.5 * 30000) := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      linarith
    linarith
  have hC1 := caC1_lower_A ε hε hlo hhi hθ
  have hN2 := caNet2_lower_A ε hε hlo hhi
  have hnum := num_checkA n hn173 hn501
  have hAbd := abA_le_abAbd n hn173 hn501
  have hJbd := abJbd_le_abJ z hz30000 hz1e5
  have hUbd := caU_le_caUbd z n hz30000 hz1e5 hn173 hn501 hlink
  have h1 : (498/1000) * Work.RHContract.A.RegionII.abA n
      ≤ (498/1000) * Work.RHContract.A.RegionII.abAbd n :=
    mul_le_mul_of_nonneg_left hAbd (by norm_num)
  have h2 : (498/1000) * Work.RHContract.A.RegionII.abJbd
      ≤ (498/1000) * Work.RHContract.A.RegionII.abJ z :=
    mul_le_mul_of_nonneg_left hJbd (by norm_num)
  have h3 : (36/100) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      = (36/100) * Work.RHContract.A.RegionII.caU (z : ℝ) := by rw [hzr]
  have hfin : (36/100) * Work.RHContract.A.RegionII.caU (z : ℝ) + 5/10^6
      ≤ (498/1000) * Work.RHContract.A.RegionII.abJ z
        - (498/1000) * Work.RHContract.A.RegionII.abA n := by
    have h5 : (498/1000) * Work.RHContract.A.RegionII.abJbd
          - (498/1000) * Work.RHContract.A.RegionII.abAbd n
        ≤ (498/1000) * Work.RHContract.A.RegionII.abJ z
          - (498/1000) * Work.RHContract.A.RegionII.abA n := by
      linarith [h1, h2]
    linarith [h5, hnum, hUbd]
  have hC1'' : (498/1000) * (Work.RHContract.A.RegionII.abJ z
        - Work.RHContract.A.RegionII.abA n) ≤ Work.RHContract.Margin.caC1 ε := by
    have h := hC1
    rw [← hndef, ← hzdef] at h
    exact h
  have hC1''' : (498/1000) * Work.RHContract.A.RegionII.abJ z
        - (498/1000) * Work.RHContract.A.RegionII.abA n ≤ Work.RHContract.Margin.caC1 ε := by
    have : (498/1000) * (Work.RHContract.A.RegionII.abJ z - Work.RHContract.A.RegionII.abA n)
        = (498/1000) * Work.RHContract.A.RegionII.abJ z
          - (498/1000) * Work.RHContract.A.RegionII.abA n := by ring
    rw [← this]
    exact hC1''
  have hgoal : (36/100) * Work.RHContract.A.RegionII.caU (z : ℝ)
      ≤ Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε := by
    linarith [hfin, hC1''', hN2]
  rw [h3]
  exact hgoal

end Work.RHContract.A.regionII
