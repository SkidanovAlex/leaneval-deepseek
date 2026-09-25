import Mathlib
import Submission.Work.Beltrami.norm_beurlingIntegrand_le

noncomputable section

namespace Work.Beltrami

open MeasureTheory

/-- The indicator of a closed ball around `0` on `ℂ`, evaluated at `w`. -/
private lemma indicator_closedBall_zero (r : ℝ) (f : ℂ → ℝ) (w : ℂ) :
    (Metric.closedBall (0 : ℂ) r).indicator f w = if ‖w‖ ≤ r then f w else 0 := by
  by_cases h : ‖w‖ ≤ r
  · have hm : w ∈ Metric.closedBall (0 : ℂ) r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using h
    rw [Set.indicator_of_mem hm f, if_pos h]
  · have hm : w ∉ Metric.closedBall (0 : ℂ) r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using h
    rw [Set.indicator_of_notMem hm f, if_neg h]

/-- The Beurling majorant is nonnegative. -/
lemma beurlingBound_nonneg (α K L M R : ℝ) (z w : ℂ) :
    0 ≤ beurlingBound α K L M R z w := by
  unfold beurlingBound
  have h1 : 0 ≤ (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun w => ‖w‖ ^ (α - 2)) w :=
    Set.indicator_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg a) _) w
  have h2 : 0 ≤ (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun w => ‖w‖ ^ (-1 : ℝ)) w :=
    Set.indicator_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg a) _) w
  have h3 : 0 ≤ (Metric.closedBall (0 : ℂ) (max 1 (R + ‖z‖ + 2))).indicator
      (fun _ : ℂ => (1 : ℝ)) w :=
    Set.indicator_nonneg (fun a _ => by norm_num) w
  have h3' : 0 ≤ (8 * (|L| + |M| + 1)) *
      (Metric.closedBall (0 : ℂ) (max 1 (R + ‖z‖ + 2))).indicator (fun _ : ℂ => (1 : ℝ)) w :=
    mul_nonneg (by positivity) h3
  nlinarith [mul_nonneg (abs_nonneg K) h1, mul_nonneg (abs_nonneg L) h2, h3']

theorem norm_beurlingIntegrand_le_of_holder {α M K R : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (hK : 0 ≤ K)
    {g : ℂ → ℂ} (hMg : ∀ y : ℂ, ‖g y‖ ≤ M)
    (hKg : ∀ x y : ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ y : ℂ, R < ‖y‖ → g y = 0) {x z : ℂ} (hx : ‖x - z‖ < 1) (w : ℂ) :
    ‖Work.Beltrami.beurlingIntegrand g x w‖ ≤ Work.Beltrami.beurlingBound α K K M R z w := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [beurlingIntegrand]
    simp only [zero_pow (by norm_num : 2 ≠ 0), inv_zero, zero_smul, norm_zero]
    exact beurlingBound_nonneg α K K M R z 0
  · have habsK : |K| = K := abs_of_nonneg hK
    have hnorm : ‖beurlingIntegrand g x w‖
        = ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖ := by
      rw [beurlingIntegrand, norm_smul, norm_inv, norm_pow, pow_two, mul_inv]
    rw [hnorm]
    have hq0 : 0 ≤ ‖w‖⁻¹ := inv_nonneg.mpr (norm_nonneg w)
    have hrpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    by_cases hc : ‖w‖ ≤ 1 / 2
    · -- Case 1: `‖w‖ ≤ 1/2`, so `bumpC w = 1`: the Hölder term survives.
      have hbump : bumpC w = 1 := bumpC_eq_one hc
      have hmid : ‖w‖ ≤ max 1 (R + ‖z‖ + 2) :=
        le_trans (le_trans hc (by norm_num)) (le_max_left (1 : ℝ) (R + ‖z‖ + 2))
      have hB : beurlingBound α K K M R z w
          = |K| * (‖w‖ ^ (α - 2)) + |K| * (‖w‖ ^ (-1 : ℝ)) + 8 * (|K| + |M| + 1) := by
        rw [beurlingBound]
        rw [indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (α - 2)) w, if_pos hc,
            indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (-1 : ℝ)) w, if_pos hc,
            indicator_closedBall_zero (max 1 (R + ‖z‖ + 2)) (fun _ => (1 : ℝ)) w, if_pos hmid]
        ring
      rw [hB]
      have hinner : ‖g (x + w) - (bumpC w : ℂ) • g x‖ ≤ K * ‖w‖ ^ α := by
        have heq : g (x + w) - (bumpC w : ℂ) • g x = g (x + w) - g x := by
          rw [hbump, Complex.ofReal_one, one_smul]
        rw [heq]
        have h := hKg (x + w) x
        rwa [add_sub_cancel_left] at h
      have hmain : ‖w‖⁻¹ * ‖w‖⁻¹ * (K * ‖w‖ ^ α) = K * ‖w‖ ^ (α - 2) := by
        rw [Real.rpow_sub hrpos]
        rw [div_eq_mul_inv]
        rw [show ‖w‖ ^ (2:ℝ) = ‖w‖ * ‖w‖ from by rw [Real.rpow_two]; ring]
        rw [mul_inv]
        ring
      calc ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖
          ≤ ‖w‖⁻¹ * ‖w‖⁻¹ * (K * ‖w‖ ^ α) :=
            mul_le_mul_of_nonneg_left hinner (mul_nonneg hq0 hq0)
        _ = K * ‖w‖ ^ (α - 2) := hmain
        _ = |K| * ‖w‖ ^ (α - 2) := by rw [habsK]
        _ ≤ |K| * (‖w‖ ^ (α - 2)) + |K| * (‖w‖ ^ (-1 : ℝ)) + 8 * (|K| + |M| + 1) := by
            have ha : 0 ≤ |K| * ‖w‖ ^ (-1 : ℝ) :=
              mul_nonneg (abs_nonneg K) (Real.rpow_nonneg (norm_nonneg w) _)
            have hb : 0 ≤ 8 * (|K| + |M| + 1) := by positivity
            linarith
    · by_cases hd : ‖w‖ ≤ max 1 (R + ‖z‖ + 2)
      · -- Case 2: `1/2 < ‖w‖ ≤ max 1 (R + ‖z‖ + 2)`: use boundedness of `g`.
        have h2a : 1 / 2 < ‖w‖ := not_le.mp hc
        have hB : beurlingBound α K K M R z w = 8 * (|K| + |M| + 1) := by
          rw [beurlingBound]
          rw [indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (α - 2)) w, if_neg hc,
              indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (-1 : ℝ)) w, if_neg hc,
              indicator_closedBall_zero (max 1 (R + ‖z‖ + 2)) (fun _ => (1 : ℝ)) w, if_pos hd]
          ring
        rw [hB]
        have hinner : ‖g (x + w) - (bumpC w : ℂ) • g x‖ ≤ 2 * M := by
          have hb : |bumpC w| ≤ 1 := by
            rw [abs_le]; exact ⟨by linarith [bumpC_nonneg w], by linarith [bumpC_le_one w]⟩
          have hcoef : ‖((bumpC w : ℝ) : ℂ)‖ = |bumpC w| := RCLike.norm_ofReal (K := ℂ) _
          calc ‖g (x + w) - (bumpC w : ℂ) • g x‖
              ≤ ‖g (x + w)‖ + ‖(bumpC w : ℂ) • g x‖ := norm_sub_le _ _
            _ = ‖g (x + w)‖ + |bumpC w| * ‖g x‖ := by
                rw [norm_smul, hcoef]
            _ ≤ M + 1 * M := by
                have h1 : ‖g (x + w)‖ ≤ M := hMg _
                have h2 : |bumpC w| * ‖g x‖ ≤ 1 * M :=
                  mul_le_mul hb (hMg x) (norm_nonneg _) (by norm_num)
                linarith
            _ = 2 * M := by ring
        have hq2 : ‖w‖⁻¹ ≤ 2 := by
          rw [inv_le_iff_one_le_mul₀ hrpos]
          linarith
        have hqq : ‖w‖⁻¹ * ‖w‖⁻¹ ≤ 4 := by nlinarith [hq2, hq0]
        have hgoal : ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖ ≤ 8 * M := by
          calc ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖
              ≤ 4 * (2 * M) := mul_le_mul hqq hinner (norm_nonneg _) (by linarith)
            _ = 8 * M := by ring
        linarith [abs_nonneg K, le_abs_self M]
      · -- Case 3: `‖w‖ > max 1 (R + ‖z‖ + 2)`: the integrand vanishes.
        have h3a : max 1 (R + ‖z‖ + 2) < ‖w‖ := not_le.mp hd
        have hB : beurlingBound α K K M R z w = 0 := by
          rw [beurlingBound]
          rw [indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (α - 2)) w, if_neg hc,
              indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (-1 : ℝ)) w, if_neg hc,
              indicator_closedBall_zero (max 1 (R + ‖z‖ + 2)) (fun _ => (1 : ℝ)) w, if_neg hd]
          ring
        have hw1 : 1 ≤ ‖w‖ := le_trans (le_max_left (1 : ℝ) (R + ‖z‖ + 2)) (le_of_lt h3a)
        have hbump0 : bumpC w = 0 := bumpC_eq_zero hw1
        have hgw : g (x + w) = 0 := by
          apply hsupp
          have hRz : R + ‖z‖ + 2 < ‖w‖ := lt_of_le_of_lt (le_max_right (1 : ℝ) (R + ‖z‖ + 2)) h3a
          have hx1 : ‖x‖ < 1 + ‖z‖ := by
            have h := norm_add_le (x - z) z
            rw [sub_add_cancel] at h
            linarith
          have hwx : ‖w‖ - ‖x‖ ≤ ‖x + w‖ := by
            have h := norm_add_le (w + x) (-x)
            have h2 : (w + x) + (-x) = w := by abel
            rw [h2, norm_neg] at h
            rw [add_comm x w]
            linarith
          linarith
        have hzero : ‖g (x + w) - (bumpC w : ℂ) • g x‖ = 0 := by
          rw [hgw, hbump0]; simp
        rw [hB, hzero]; simp

end Work.Beltrami
