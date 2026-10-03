import Mathlib

namespace Work.FIArea5.HeckeZFR

open Complex Metric MeromorphicOn MeasureTheory

noncomputable section

/-- Jensen's inequality with the divisor sum written as a real-valued `finsum`, matching the
shape used by `Lam_zeroCount`. -/
lemma sum_divisor_le_real {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0) (f_bound : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (closedBall c |r|)) u : ℝ)
      ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  rw [show (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (closedBall c |r|)) u : ℝ))
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor f (closedBall c |r|)) u : ℤ) : ℝ) from
    (map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor f (closedBall c |r|)).finiteSupport
        (isCompact_closedBall _ _))).symm]
  exact AnalyticOnNhd.sum_divisor_le r_pos r_lt_R hM h₁f h₂f f_bound

/-- Real-analysis budget: the `log‖Λ 0‖` defect and the passage from radius `2R` to radius `R`
cost only a constant factor. -/
lemma zeroCount_budget_aux (C K L : ℝ) (hC : 0 < C) (hK : 0 ≤ K) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 1 ≤ R →
      (C * (2 * R) * (Real.log (2 * R + 2) + K) - L) / Real.log 2 ≤
        c * R * (Real.log (R + 2) + K) := by
  refine ⟨(4 * C + max 0 (-L) / Real.log 3) / Real.log 2, ?_, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    refine div_nonneg ?_ h2.le
    have : 0 ≤ max 0 (-L) / Real.log 3 := div_nonneg (le_max_left _ _) h3.le
    linarith
  · intro R hR
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    set Y : ℝ := R * (Real.log (R + 2) + K) with hY
    have hY3 : Real.log 3 ≤ Y := by
      rw [hY]
      have h1 : Real.log 3 ≤ Real.log (R + 2) := Real.log_le_log (by norm_num) (by linarith)
      have h2 : 0 ≤ Real.log (R + 2) + K := by
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 2), hK]
      have h3 : (1 : ℝ) * (Real.log (R + 2) + K) ≤ R * (Real.log (R + 2) + K) :=
        mul_le_mul_of_nonneg_right hR h2
      linarith
    have hm0 : 0 ≤ max 0 (-L) := le_max_left _ _
    have hnegL : -L ≤ max 0 (-L) := le_max_right _ _
    have hmaxY : max 0 (-L) ≤ (max 0 (-L) / Real.log 3) * Y := by
      have h := mul_le_mul_of_nonneg_left hY3 (div_nonneg hm0 hlog3.le)
      rwa [div_mul_cancel₀ _ hlog3.ne'] at h
    have hlog2R : Real.log (2 * R + 2) ≤ 2 * Real.log (R + 2) := by
      have h1 : Real.log (2 * R + 2) ≤ Real.log (2 * (R + 2)) :=
        Real.log_le_log (by linarith) (by linarith)
      have h2 : Real.log (2 * (R + 2)) = Real.log 2 + Real.log (R + 2) :=
        Real.log_mul (by norm_num) (by linarith)
      have h3 : Real.log 2 ≤ Real.log (R + 2) := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hA : C * (2 * R) * (Real.log (2 * R + 2) + K) ≤ 4 * C * Y := by
      have hlogK : Real.log (2 * R + 2) + K ≤ 2 * (Real.log (R + 2) + K) := by
        linarith [hK, hlog2R]
      have hpos : 0 ≤ C * (2 * R) := by positivity
      have h1 : C * (2 * R) * (Real.log (2 * R + 2) + K)
          ≤ C * (2 * R) * (2 * (Real.log (R + 2) + K)) :=
        mul_le_mul_of_nonneg_left hlogK hpos
      rw [hY]
      nlinarith [h1]
    have hsum : C * (2 * R) * (Real.log (2 * R + 2) + K) - L
        ≤ 4 * C * Y + (max 0 (-L) / Real.log 3) * Y := by linarith [hA, hmaxY, hnegL]
    calc (C * (2 * R) * (Real.log (2 * R + 2) + K) - L) / Real.log 2
        ≤ (4 * C * Y + (max 0 (-L) / Real.log 3) * Y) / Real.log 2 :=
          div_le_div_of_nonneg_right hsum hlog2.le
      _ = ((4 * C + max 0 (-L) / Real.log 3) / Real.log 2) * Y := by ring
      _ = ((4 * C + max 0 (-L) / Real.log 3) / Real.log 2) * R
            * (Real.log (R + 2) + K) := by rw [hY]; ring

theorem Lam_zeroCount (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (h0 : Λ 0 ≠ 0)
    (C K : ℝ) (hC : 0 < C) (hK : 0 ≤ K)
    (hgrowth : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Λ z‖ ≤ C * R * (Real.log (R + 2) + K)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)) ≤
        c * R * (Real.log (R + 2) + K) := by
  obtain ⟨c, hc0, hc⟩ := zeroCount_budget_aux C K (Real.log ‖Λ 0‖) hC hK
  refine ⟨c, hc0, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  set A : ℝ := C * (2 * R) * (Real.log (2 * R + 2) + K) with hA
  have hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 |2 * R|) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hDiff).mono (Set.subset_univ _)
  have h2R1 : (1 : ℝ) ≤ 2 * R := by linarith
  have hbound : ∀ z ∈ Metric.sphere 0 |2 * R|, ‖Λ z‖ ≤ Real.exp A := by
    intro z hz
    have hzn : ‖z‖ = 2 * R := by
      rw [Metric.mem_sphere, dist_zero_right] at hz
      rw [hz, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * R)]
    have hzlog := hgrowth (2 * R) h2R1 z hzn
    rw [← hA] at hzlog
    rcases eq_or_lt_of_le (norm_nonneg (Λ z)) with h | h
    · rw [← h]; exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp h).mp hzlog
  have hA0 : 0 ≤ A := by
    rw [hA]
    have hlog : 0 ≤ Real.log (2 * R + 2) := Real.log_nonneg (by linarith)
    have h1 : 0 ≤ Real.log (2 * R + 2) + K := by linarith
    exact mul_nonneg (mul_nonneg hC.le (by linarith)) h1
  have hM1 : (1 : ℝ) ≤ Real.exp A := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hA0
  have hmain := sum_divisor_le_real (c := 0) (r := R) (R := 2 * R) (M := Real.exp A)
      (by rwa [abs_of_pos hRpos])
      (by rw [abs_of_pos hRpos, abs_of_pos (by linarith : (0 : ℝ) < 2 * R)]; linarith)
      hM1 hAn h0 hbound
  rw [abs_of_pos hRpos] at hmain
  have hlog : Real.log (Real.exp A / ‖Λ 0‖) / Real.log (2 * R / R)
      = (C * (2 * R) * (Real.log (2 * R + 2) + K) - Real.log ‖Λ 0‖) / Real.log 2 := by
    have hne : ‖Λ 0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have h2R : (2 * R) / R = 2 := mul_div_cancel_right₀ 2 (ne_of_gt hRpos)
    rw [h2R, Real.log_div (Real.exp_pos A).ne' hne, Real.log_exp, hA]
  calc ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)
      ≤ Real.log (Real.exp A / ‖Λ 0‖) / Real.log (2 * R / R) := hmain
    _ = (C * (2 * R) * (Real.log (2 * R + 2) + K) - Real.log ‖Λ 0‖) / Real.log 2 := hlog
    _ ≤ c * R * (Real.log (R + 2) + K) := hc R hR

end

end Work.FIArea5.HeckeZFR
