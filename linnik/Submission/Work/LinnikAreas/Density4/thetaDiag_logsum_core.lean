import Mathlib
import Submission.Work.LinnikAreas.Density4.ThetaLogsumDefs
import Submission.Work.LinnikAreas.Density4.abel_identity
import Submission.Work.LinnikAreas.Density4.tgH_antitone
import Submission.Work.LinnikAreas.Density4.tgEta_eq_integral
import Submission.Work.LinnikAreas.Density4.tgG_le

namespace Work.LinnikAreas.Density4

open scoped BigOperators
noncomputable section
open MeasureTheory intervalIntegral

/-- `tgEta n ≥ 1/(2(n+1))` for `n ≥ 1`. -/
lemma tgEta_ge (n : ℕ) (hn : 1 ≤ n) : 1/(2*((n:ℝ)+1)) ≤ tgEta n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hx : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
  have h1 := Real.le_log_one_add_of_nonneg hx
  have hsimp : 2 * (1/(n:ℝ)) / (1/(n:ℝ) + 2) = 2/(2*(n:ℝ)+1) := by
    field_simp; ring
  rw [hsimp] at h1
  rw [tgEta]
  have h2 : ((n:ℝ)+1) * (2/(2*(n:ℝ)+1)) = 1 + 1/(2*(n:ℝ)+1) := by
    field_simp; ring
  have h3 : ((n:ℝ)+1) * (2/(2*(n:ℝ)+1)) ≤ ((n:ℝ)+1) * Real.log (1 + 1/(n:ℝ)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [h2] at h3
  have h4 : 1/(2*((n:ℝ)+1)) ≤ 1/(2*(n:ℝ)+1) := by
    apply one_div_le_one_div_of_le <;> linarith
  linarith

/-- The telescoping defect `κ_n = tgW n - tgW (n-1) - tgEta (n-1) ≤ 1/(2(n-1))` for `n ≥ 2`. -/
lemma tgKappa_le (n : ℕ) (hn : 2 ≤ n) :
    tgW (n:ℝ) - tgW ((n-1:ℕ):ℝ) - tgEta (n-1) ≤ 1/(2*(((n-1:ℕ)):ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm1
  have hlog : Real.log ((m:ℝ)+1) - Real.log (m:ℝ) = Real.log (1 + 1/(m:ℝ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  have hW : tgW (((m+1):ℕ):ℝ) - tgW ((m:ℕ):ℝ) = Real.log (1 + 1/(m:ℝ)) := by
    simp only [tgW]; push_cast; linarith [hlog]
  have heta : tgEta m = ((m:ℝ)+1) * Real.log (1 + 1/(m:ℝ)) - 1 := rfl
  simp only [Nat.add_sub_cancel]
  rw [hW, heta]
  have hx : (0:ℝ) ≤ 1/(m:ℝ) := by positivity
  have h1 := Real.le_log_one_add_of_nonneg hx
  have hsimp : 2 * (1/(m:ℝ)) / (1/(m:ℝ) + 2) = 2/(2*(m:ℝ)+1) := by field_simp; ring
  rw [hsimp] at h1
  have h3 : (m:ℝ) * (2/(2*(m:ℝ)+1)) ≤ (m:ℝ) * Real.log (1 + 1/(m:ℝ)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 1/(2*(m:ℝ)+1) ≤ 1/(2*(m:ℝ)) := by
    apply one_div_le_one_div_of_le <;> linarith
  have h5 : (m:ℝ) * (2/(2*(m:ℝ)+1)) = 1 - 1/(2*(m:ℝ)+1) := by
    field_simp; ring
  linarith

/-- Shift lemma: `∑_{n∈Ico 3 (N+1)} 1/(n-1) = ∑_{k∈Icc 1 (N-1)} 1/k - 1`. -/
lemma sum_Ico_shift_div (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Ico 3 (N+1), (1:ℝ)/(((n-1:ℕ):ℝ)))
      = (∑ k ∈ Finset.Icc 1 (N-1), (1:ℝ)/(k:ℝ)) - 1 := by
  have hA : (∑ n ∈ Finset.Ico 3 (N+1), (1:ℝ)/(((n-1:ℕ):ℝ)))
      = ∑ x ∈ Finset.Ico 2 N, (1:ℝ)/(x:ℝ) := by
    rw [← Finset.sum_Ico_add' (fun m : ℕ => (1:ℝ)/(((m-1:ℕ):ℝ))) (2:ℕ) N (1:ℕ)]
    apply Finset.sum_congr rfl; intro x hx
    simp only [Nat.add_sub_cancel]
  have hB : (∑ k ∈ Finset.Icc 1 (N-1), (1:ℝ)/(k:ℝ))
      = 1 + ∑ x ∈ Finset.Ico 2 N, (1:ℝ)/(x:ℝ) := by
    have hI : Finset.Icc 1 (N-1) = insert 1 (Finset.Ico 2 N) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
    norm_num
  rw [hA, hB]; ring

/-- Per-interval comparison. -/
lemma tgF_sub_integral_le (σ A : ℝ) (hσ1 : σ ≤ 1) (hA : 0 < A) (n : ℕ) (hn : 1 ≤ n) :
    tgF σ A (n:ℝ) - (∫ t in (n:ℝ)..((n:ℝ)+1), tgF σ A t)
      ≤ tgW (n:ℝ) * (tgH σ A (n:ℝ) - tgH σ A ((n:ℝ)+1))
          - tgEta n * tgH σ A ((n:ℝ)+1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hcontH : ContinuousOn (fun t : ℝ => t^(σ-1) * Real.exp (-t/A)) (Set.Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    · exact Real.continuous_exp.comp_continuousOn ((continuousOn_id.neg).div_const A)
  have hcontW : ContinuousOn (fun t : ℝ => Real.log t + 1) (Set.Ioi 0) := by
    refine (Real.continuousOn_log.mono ?_).add continuousOn_const
    intro x hx; exact (ne_of_lt hx).symm
  have hcontF : ContinuousOn (tgF σ A) (Set.Ioi 0) := by
    change ContinuousOn (fun t : ℝ => (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A))) (Set.Ioi 0)
    exact hcontW.mul hcontH
  have hmem : Set.uIcc (n:ℝ) ((n:ℝ)+1) ⊆ Set.Ioi 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact lt_of_lt_of_le hn0 hx.1
  have hintF : IntervalIntegrable (tgF σ A) volume (n:ℝ) ((n:ℝ)+1) :=
    (hcontF.mono hmem).intervalIntegrable
  set g : ℝ → ℝ := fun t =>
    tgW (n:ℝ) * (tgH σ A (n:ℝ) - tgH σ A ((n:ℝ)+1))
      - tgH σ A ((n:ℝ)+1) * (tgW t - tgW (n:ℝ)) with hgdef
  have hcontg : ContinuousOn g (Set.Ioi 0) := by
    apply ContinuousOn.sub
    · exact continuousOn_const
    · exact continuousOn_const.mul (hcontW.sub continuousOn_const)
  have hintg : IntervalIntegrable g volume (n:ℝ) ((n:ℝ)+1) := (hcontg.mono hmem).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (n:ℝ) ((n:ℝ)+1), tgF σ A (n:ℝ) - tgF σ A t ≤ g t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hn0 ht.1
    have hWt : 0 ≤ tgW t := by
      rw [show tgW t = Real.log t + 1 from rfl]
      have h1n : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have := Real.log_nonneg (by linarith : (1:ℝ) ≤ t); linarith
    have hHle : tgH σ A ((n:ℝ)+1) ≤ tgH σ A t := tgH_antitone σ A hσ1 hA ht0 (by linarith)
    have hkey : tgF σ A (n:ℝ) - tgF σ A t - g t
        = tgW t * (tgH σ A ((n:ℝ)+1) - tgH σ A t) := by
      simp only [tgF, tgW, tgH, hgdef]; ring
    have hnn : tgW t * (tgH σ A ((n:ℝ)+1) - tgH σ A t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hWt (by linarith)
    have : tgF σ A (n:ℝ) - tgF σ A t - g t ≤ 0 := by rw [hkey]; exact hnn
    linarith
  have hmono : (∫ t in (n:ℝ)..((n:ℝ)+1), tgF σ A (n:ℝ) - tgF σ A t)
      ≤ ∫ t in (n:ℝ)..((n:ℝ)+1), g t := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact intervalIntegrable_const.sub hintF
    · exact hintg
    · exact hpt
  have hA1 : (∫ t in (n:ℝ)..((n:ℝ)+1), tgF σ A (n:ℝ) - tgF σ A t)
      = tgF σ A (n:ℝ) - ∫ t in (n:ℝ)..((n:ℝ)+1), tgF σ A t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hintF,
        intervalIntegral.integral_const]
    simp
  have hcg2 : ContinuousOn (fun t : ℝ => tgH σ A ((n:ℝ)+1) * (tgW t - tgW (n:ℝ)))
      (Set.Ioi 0) := continuousOn_const.mul (hcontW.sub continuousOn_const)
  have hintg2 : IntervalIntegrable (fun t : ℝ => tgH σ A ((n:ℝ)+1) * (tgW t - tgW (n:ℝ)))
      volume (n:ℝ) ((n:ℝ)+1) := (hcg2.mono hmem).intervalIntegrable
  have hA2 : (∫ t in (n:ℝ)..((n:ℝ)+1), g t)
      = tgW (n:ℝ) * (tgH σ A (n:ℝ) - tgH σ A ((n:ℝ)+1))
          - tgH σ A ((n:ℝ)+1) * tgEta n := by
    have hgeq : g = fun t : ℝ =>
        (tgW (n:ℝ) * (tgH σ A (n:ℝ) - tgH σ A ((n:ℝ)+1)))
          - tgH σ A ((n:ℝ)+1) * (tgW t - tgW (n:ℝ)) := by
      funext t; rw [hgdef]
    rw [hgeq, intervalIntegral.integral_sub intervalIntegrable_const hintg2,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, tgEta_eq_integral]
    simp
  rw [hA1, hA2] at hmono
  rw [mul_comm (tgH σ A ((n:ℝ)+1)) (tgEta n)] at hmono
  exact hmono

theorem thetaDiag_logsum_core (σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 0 < A) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, (Real.log (n:ℝ) + 1) * ((n:ℝ)^(σ-1) * Real.exp (-(n:ℝ)/A)))
      ≤ (∫ t in (2:ℝ)..((N:ℝ)+1), (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A)))
        + Real.exp (-(1:ℝ)/A) * Real.log (N:ℝ) := by
  rcases Nat.lt_or_ge N 2 with hNlt | hN2
  · have hN1 : N = 1 := by omega
    subst hN1
    rw [Finset.Icc_eq_empty (by norm_num : ¬ (2:ℕ) ≤ 1), Finset.sum_empty,
        show (((1:ℕ)):ℝ)+1 = 2 from by norm_num, intervalIntegral.integral_same]
    simp
  set H : ℕ → ℝ := fun n => tgH σ A (n:ℝ) with hH
  set W : ℕ → ℝ := fun n => tgW (n:ℝ) with hW
  have hLHS : (∑ n ∈ Finset.Icc 2 N, (Real.log (n:ℝ) + 1) * ((n:ℝ)^(σ-1) * Real.exp (-(n:ℝ)/A)))
      = ∑ n ∈ Finset.Icc 2 N, W n * H n := by
    apply Finset.sum_congr rfl; intro n hn
    simp only [hH, hW, tgW, tgH]
  have hInt : (∫ t in (2:ℝ)..((N:ℝ)+1), (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A)))
      = ∫ t in (2:ℝ)..((N:ℝ)+1), tgF σ A t := by
    apply intervalIntegral.integral_congr; intro t ht; simp only [tgF]
  rw [hLHS, hInt]
  have hcontH : ContinuousOn (fun t : ℝ => t^(σ-1) * Real.exp (-t/A)) (Set.Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    · exact Real.continuous_exp.comp_continuousOn ((continuousOn_id.neg).div_const A)
  have hcontF : ContinuousOn (tgF σ A) (Set.Ioi 0) := by
    change ContinuousOn (fun t : ℝ => (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A))) (Set.Ioi 0)
    exact ((Real.continuousOn_log.mono (by intro x hx; exact (ne_of_lt hx).symm)).add continuousOn_const).mul hcontH
  have hadj : (∑ n ∈ Finset.Icc 2 N, ∫ t in (n:ℝ)..((n:ℝ)+1), tgF σ A t)
      = ∫ t in (2:ℝ)..((N:ℝ)+1), tgF σ A t := by
    have h := sum_integral_adjacent_intervals_Ico (f := tgF σ A)
        (μ := volume) (a := fun k : ℕ => (k:ℝ)) (m := 2) (n := N+1) (by omega) (fun k hk => ?_)
    · rw [show Finset.Ico 2 (N+1) = Finset.Icc 2 N from by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega] at h
      rw [show (↑(N+1):ℝ) = (N:ℝ)+1 from by push_cast; ring,
          show (((2:ℕ)):ℝ) = (2:ℝ) from by norm_num] at h
      rw [← h]
      apply Finset.sum_congr rfl; intro n hn
      rw [show ((n:ℝ)+1) = (↑(n+1):ℝ) from by push_cast; ring]
    · rw [Set.mem_Ico] at hk
      apply (hcontF.mono ?_).intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le (by push_cast; linarith)] at hx
      have hk2 : (0:ℝ) < (k:ℝ) := by
        have h2k : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
        linarith
      exact lt_of_lt_of_le hk2 hx.1
  rw [← hadj]
  have hper : ∀ n ∈ Finset.Icc 2 N,
      W n * H n - (∫ t in (n:ℝ)..((n:ℝ)+1), tgF σ A t)
        ≤ W n * (H n - H (n+1)) - tgEta n * H (n+1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h := tgF_sub_integral_le σ A hσ1 hA n (le_trans (by norm_num : 1 ≤ 2) hn.1)
    simpa only [hH, hW, tgF, tgW, tgH, Nat.cast_add, Nat.cast_one] using h
  have htgEtaN : 0 ≤ tgEta N := le_trans (by positivity) (tgEta_ge N hN)
  have hHN : 0 ≤ H (N+1) := by
    simp only [hH, tgH]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)
  have hstep1 : (∑ n ∈ Finset.Icc 2 N, (W n * (H n - H (n+1)) - tgEta n * H (n+1)))
      ≤ W 2 * H 2 - W N * H (N+1)
        + ∑ n ∈ Finset.Ico 3 (N+1), (W n - W (n-1) - tgEta (n-1)) * H n := by
    have h1 : (∑ n ∈ Finset.Icc 2 N, (W n * (H n - H (n+1)) - tgEta n * H (n+1)))
        = (∑ n ∈ Finset.Ico 2 (N+1), W n * (H n - H (n+1)))
          - ∑ n ∈ Finset.Ico 2 (N+1), tgEta n * H (n+1) := by
      rw [show Finset.Icc 2 N = Finset.Ico 2 (N+1) from by
          ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
      rw [Finset.sum_sub_distrib]
    have h2 : (∑ n ∈ Finset.Ico 2 (N+1), W n * (H n - H (n+1)))
        = W 2 * H 2 - W N * H (N+1)
          + ∑ n ∈ Finset.Ico 3 (N+1), (W n - W (n-1)) * H n := by
      rw [abel_identity W H (A := 2) (B := N) hN2]
    have h3 : (∑ n ∈ Finset.Ico 2 (N+1), tgEta n * H (n+1))
        = (∑ n ∈ Finset.Ico 3 (N+1), tgEta (n-1) * H n) + tgEta N * H (N+1) := by
      rw [show (∑ n ∈ Finset.Ico 2 (N+1), tgEta n * H (n+1))
          = ∑ n ∈ Finset.Ico 3 (N+2), tgEta (n-1) * H n from by
        rw [← Finset.sum_Ico_add' (fun m : ℕ => tgEta (m-1) * H m) (2:ℕ) (N+1) (1:ℕ)]
        apply Finset.sum_congr rfl; intro n hn; simp only [Nat.add_sub_cancel]]
      rw [Finset.sum_Ico_succ_top (by omega : 3 ≤ N+1)]
      simp only [Nat.add_sub_cancel]
    have h4 : (∑ n ∈ Finset.Ico 3 (N+1), (W n - W (n-1)) * H n)
        - ∑ n ∈ Finset.Ico 3 (N+1), tgEta (n-1) * H n
        = ∑ n ∈ Finset.Ico 3 (N+1), (W n - W (n-1) - tgEta (n-1)) * H n := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro n hn; ring
    have h5 : 0 ≤ tgEta N * H (N+1) := mul_nonneg htgEtaN hHN
    linarith [h1, h2, h3, h4, h5]
  set q : ℝ := (∑ k ∈ Finset.Icc 1 (N-1), (1:ℝ)/(k:ℝ)) - 1 with hq
  have hstep2 : W 2 * H 2 - W N * H (N+1)
        + ∑ n ∈ Finset.Ico 3 (N+1), (W n - W (n-1) - tgEta (n-1)) * H n
      ≤ W 2 * H 2 - W N * H (N+1) + (1/2) * H 2 * q := by
    have hH2nn : 0 ≤ H 2 := by
      simp only [hH, tgH]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _)
    have hHn0 : ∀ n, 0 ≤ H n := by
      intro n; simp only [hH, tgH]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)
    have hterm : ∀ n ∈ Finset.Ico 3 (N+1), (W n - W (n-1) - tgEta (n-1)) * H n
        ≤ (1/2) * H 2 * (1/(((n-1:ℕ)):ℝ)) := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hn2 : 2 ≤ n := by omega
      have hk : W n - W (n-1) - tgEta (n-1) ≤ 1/(2*(((n-1:ℕ)):ℝ)) := by
        have hk0 := tgKappa_le n hn2
        simpa only [hW, tgW, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hk0
      have hHn : H n ≤ H 2 := by
        simp only [hH, tgH]
        exact tgH_antitone σ A hσ1 hA (by norm_num) (by exact_mod_cast hn2)
      have h1 : (W n - W (n-1) - tgEta (n-1)) * H n ≤ (1/(2*(((n-1:ℕ)):ℝ))) * H n :=
        mul_le_mul_of_nonneg_right hk (hHn0 n)
      have h2 : (1/(2*(((n-1:ℕ)):ℝ))) * H n ≤ (1/(2*(((n-1:ℕ)):ℝ))) * H 2 :=
        mul_le_mul_of_nonneg_left hHn (by positivity)
      have h3 : (1/(2*(((n-1:ℕ)):ℝ))) * H 2 = (1/2) * H 2 * (1/(((n-1:ℕ)):ℝ)) := by ring
      linarith
    have hs := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hs
    rw [sum_Ico_shift_div N hN2] at hs
    rw [hq]
    linarith
  have hstep3 : W 2 * H 2 - W N * H (N+1) + (1/2) * H 2 * q
      ≤ Real.exp (-(1:ℝ)/A) * Real.log (N:ℝ) := by
    set w : ℝ := Real.exp (-(1:ℝ)/A) with hwdef
    set z : ℝ := (2:ℝ)^(σ-1) * w with hzdef
    have hw0 : 0 ≤ w := by rw [hwdef]; positivity
    have hw1 : w ≤ 1 := by
      rw [hwdef]; exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by norm_num) hA.le)
    have hz0 : 0 ≤ z := by rw [hzdef]; positivity
    have h2sig1 : (2:ℝ)^(σ-1) ≤ 1 := by
      rw [← Real.rpow_zero (2:ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hzle : z ≤ w := by
      rw [hzdef]
      calc (2:ℝ)^(σ-1) * w ≤ 1 * w := mul_le_mul_of_nonneg_right h2sig1 hw0
        _ = w := one_mul w
    have hH2 : H 2 = z * w := by
      rw [hzdef]
      simp only [hH, tgH, hwdef]
      push_cast
      rw [show -(2:ℝ)/A = -(1:ℝ)/A + -(1:ℝ)/A by ring, Real.exp_add]
      ring
    have hW2 : W 2 = Real.log 2 + 1 := by simp [hW, tgW]
    have hWN : W N = Real.log (N:ℝ) + 1 := by simp [hW, tgW]
    have hNpow : (2/((N:ℝ)+1)) * (2:ℝ)^(σ-1) ≤ ((N:ℝ)+1)^(σ-1) := by
      have hNp : (0:ℝ) < (N:ℝ)+1 := by positivity
      have h2 : (2:ℝ)^σ ≤ ((N:ℝ)+1)^σ := by
        have h2N : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
        exact Real.rpow_le_rpow (by norm_num) (by linarith) hσ.le
      have h1 : (2/((N:ℝ)+1)) * ((N:ℝ)+1) = 2 := by field_simp
      have h2r : (2:ℝ)^(σ-1) * 2 = (2:ℝ)^σ := by
        rw [show (2:ℝ)^σ = (2:ℝ)^(σ-1+1) by congr 1; ring,
            Real.rpow_add (by norm_num), Real.rpow_one]
      have hL : (2/((N:ℝ)+1) * (2:ℝ)^(σ-1)) * ((N:ℝ)+1) = (2:ℝ)^σ := by
        calc (2/((N:ℝ)+1) * (2:ℝ)^(σ-1)) * ((N:ℝ)+1)
            = ((2/((N:ℝ)+1)) * ((N:ℝ)+1)) * (2:ℝ)^(σ-1) := by ring
          _ = 2 * (2:ℝ)^(σ-1) := by rw [h1]
          _ = (2:ℝ)^(σ-1) * 2 := by ring
          _ = (2:ℝ)^σ := h2r
      have hR : ((N:ℝ)+1)^(σ-1) * ((N:ℝ)+1) = ((N:ℝ)+1)^σ := by
        rw [show ((N:ℝ)+1)^σ = ((N:ℝ)+1)^(σ-1+1) by congr 1; ring,
            Real.rpow_add hNp, Real.rpow_one]
      have key : (2/((N:ℝ)+1) * (2:ℝ)^(σ-1)) * ((N:ℝ)+1)
          ≤ ((N:ℝ)+1)^(σ-1) * ((N:ℝ)+1) := by rw [hL, hR]; exact h2
      exact le_of_mul_le_mul_right key hNp
    have hwp : w^N * w = Real.exp (-((N:ℝ)+1)/A) := by
      rw [hwdef, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    have hHN2 : (Real.log (N:ℝ)+1) * (z * (2/((N:ℝ)+1)) * w^N) ≤ W N * H (N+1) := by
      have hLN0 : 0 ≤ Real.log (N:ℝ)+1 := by
        have := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ) ≤ ↑N); linarith
      have hstep : z * (2/((N:ℝ)+1)) * w^N ≤ ((N:ℝ)+1)^(σ-1) * Real.exp (-((N:ℝ)+1)/A) := by
        rw [hzdef]
        have e : (2:ℝ)^(σ-1) * w * (2/((N:ℝ)+1)) * w^N
            = (2/((N:ℝ)+1)) * (2:ℝ)^(σ-1) * (w^N * w) := by ring
        rw [e, hwp]
        exact mul_le_mul_of_nonneg_right hNpow (Real.exp_nonneg _)
      rw [hWN]
      simp only [hH, tgH]
      push_cast
      exact mul_le_mul_of_nonneg_left hstep hLN0
    have hg : ((Real.log 2 + 1) + q/2) * w - (Real.log (N:ℝ)+1) * (2/((N:ℝ)+1)) * w^N
        ≤ Real.log (N:ℝ) := by
      have hg0 := tgG_le N hN2 w hw0 hw1
      rw [← hq] at hg0
      exact hg0
    have hLN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    rw [hW2, hWN, hH2]
    nlinarith [hHN2, hg, hz0, hzle, hw0, hLN]
  have hkey : (∑ n ∈ Finset.Icc 2 N, W n * H n)
      - (∑ n ∈ Finset.Icc 2 N, ∫ t in (n:ℝ)..((n:ℝ)+1), tgF σ A t)
      ≤ Real.exp (-(1:ℝ)/A) * Real.log (N:ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact le_trans (Finset.sum_le_sum hper) (le_trans hstep1 (le_trans hstep2 hstep3))
  linarith [hkey]

end

end Work.LinnikAreas.Density4
