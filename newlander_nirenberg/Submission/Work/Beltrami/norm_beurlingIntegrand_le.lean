import Mathlib
import Submission.Work.Beltrami.beurlingVAux

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

private lemma inv_norm_mul_norm_le_one (w : ℂ) : ‖w‖⁻¹ * ‖w‖ ≤ 1 := by
  rcases eq_or_ne ‖w‖ 0 with h | h
  · rw [h]; norm_num
  · rw [inv_mul_cancel₀ h]

private lemma inv_norm_mul_inv_mul_le (w : ℂ) : ‖w‖⁻¹ * (‖w‖⁻¹ * ‖w‖) ≤ ‖w‖⁻¹ :=
  calc ‖w‖⁻¹ * (‖w‖⁻¹ * ‖w‖) ≤ ‖w‖⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (inv_norm_mul_norm_le_one w) (inv_nonneg.mpr (norm_nonneg w))
    _ = ‖w‖⁻¹ := mul_one _

theorem norm_beurlingIntegrand_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {α K L M R : ℝ} {g : ℂ → E} (hM : ∀ y : ℂ, ‖g y‖ ≤ M)
    (hLip : ∀ x y : ℂ, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hsupp : ∀ y : ℂ, R < ‖y‖ → g y = 0) {x w z : ℂ} (hx : ‖x - z‖ < 1) :
    ‖beurlingIntegrand g x w‖ ≤ beurlingBound α K L M R z w := by
  have hL0 : 0 ≤ L := by
    have h := hLip 0 1
    have h1 : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [h1, mul_one] at h
    exact le_trans (norm_nonneg (g 0 - g 1)) h
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0)
  have habsL : |L| = L := abs_of_nonneg hL0
  have habsM : |M| = M := abs_of_nonneg hM0
  have hnorm : ‖beurlingIntegrand g x w‖
      = ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖ := by
    rw [beurlingIntegrand, norm_smul, norm_inv, norm_pow, pow_two, mul_inv]
  rw [hnorm]
  -- General bound on the inner factor.
  have hinner : ‖g (x + w) - (bumpC w : ℂ) • g x‖ ≤ L * ‖w‖ + M := by
    have hsplit : g (x + w) - (bumpC w : ℂ) • g x
        = (g (x + w) - g x) + (g x - (bumpC w : ℂ) • g x) := by abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖g (x + w) - g x‖ ≤ L * ‖w‖ := by
      have h := hLip (x + w) x
      rwa [add_sub_cancel_left] at h
    have h3 : ‖g x - (bumpC w : ℂ) • g x‖ ≤ M := by
      have hkey : g x - (bumpC w : ℂ) • g x = ((1 - bumpC w : ℝ) : ℂ) • g x := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      have hcoe : ‖((1 - bumpC w : ℝ) : ℂ)‖ = |1 - bumpC w| := RCLike.norm_ofReal _
      rw [hkey, norm_smul, hcoe]
      have hχ : |1 - bumpC w| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [bumpC_le_one w], by linarith [bumpC_nonneg w]⟩
      calc |1 - bumpC w| * ‖g x‖ ≤ 1 * ‖g x‖ :=
            mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
        _ = ‖g x‖ := one_mul _
        _ ≤ M := hM x
    linarith
  by_cases hc : ‖w‖ ≤ 1 / 2
  · -- Case 1: `‖w‖ ≤ 1/2`, so `bumpC w = 1` and the `M`-term disappears.
    have hbump : bumpC w = 1 := bumpC_eq_one hc
    have hmid : ‖w‖ ≤ max 1 (R + ‖z‖ + 2) :=
      le_trans (le_trans hc (by norm_num)) (le_max_left (1:ℝ) (R + ‖z‖ + 2))
    have hB : beurlingBound α K L M R z w
        = |K| * (‖w‖ ^ (α - 2)) + |L| * (‖w‖ ^ (-1 : ℝ)) + 8 * (|L| + |M| + 1) := by
      rw [beurlingBound]
      rw [indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (α - 2)) w, if_pos hc,
          indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (-1 : ℝ)) w, if_pos hc,
          indicator_closedBall_zero (max 1 (R + ‖z‖ + 2)) (fun _ => (1 : ℝ)) w, if_pos hmid]
      ring
    rw [hB]
    have hinner1 : ‖g (x + w) - (bumpC w : ℂ) • g x‖ ≤ L * ‖w‖ := by
      have h2 : ‖g (x + w) - g x‖ ≤ L * ‖w‖ := by
        have h := hLip (x + w) x
        rwa [add_sub_cancel_left] at h
      have heq : g (x + w) - (bumpC w : ℂ) • g x = g (x + w) - g x := by
        rw [hbump, Complex.ofReal_one, one_smul]
      rwa [heq]
    calc ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖
        ≤ ‖w‖⁻¹ * ‖w‖⁻¹ * (L * ‖w‖) :=
          mul_le_mul_of_nonneg_left hinner1
            (mul_nonneg (inv_nonneg.mpr (norm_nonneg w)) (inv_nonneg.mpr (norm_nonneg w)))
      _ = L * (‖w‖⁻¹ * (‖w‖⁻¹ * ‖w‖)) := by ring
      _ ≤ L * ‖w‖⁻¹ := mul_le_mul_of_nonneg_left (inv_norm_mul_inv_mul_le w) hL0
      _ = |L| * ‖w‖⁻¹ := by rw [habsL]
      _ = |L| * (‖w‖ ^ (-1 : ℝ)) := by rw [Real.rpow_neg_one]
      _ ≤ |K| * (‖w‖ ^ (α - 2)) + |L| * (‖w‖ ^ (-1 : ℝ)) + 8 * (|L| + |M| + 1) := by
          have h1 : 0 ≤ |K| * (‖w‖ ^ (α - 2)) :=
            mul_nonneg (abs_nonneg K) (Real.rpow_nonneg (norm_nonneg w) _)
          have h2 : 0 ≤ 8 * (|L| + |M| + 1) := by positivity
          linarith
  · by_cases hd : ‖w‖ ≤ max 1 (R + ‖z‖ + 2)
    · -- Case 2: `1/2 < ‖w‖ ≤ max 1 (R + ‖z‖ + 2)`; only the constant term survives.
      have h2a : 1 / 2 < ‖w‖ := not_le.mp hc
      have hB : beurlingBound α K L M R z w = 8 * (|L| + |M| + 1) := by
        rw [beurlingBound]
        rw [indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (α - 2)) w, if_neg hc,
            indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (-1 : ℝ)) w, if_neg hc,
            indicator_closedBall_zero (max 1 (R + ‖z‖ + 2)) (fun _ => (1 : ℝ)) w, if_pos hd]
        ring
      rw [hB, habsL, habsM]
      have hq0 : 0 ≤ ‖w‖⁻¹ := inv_nonneg.mpr (norm_nonneg w)
      have hq2 : ‖w‖⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ (by linarith : (0 : ℝ) < ‖w‖)]
        linarith
      have hqq : ‖w‖⁻¹ * ‖w‖⁻¹ ≤ 4 := by
        have h := mul_le_mul hq2 hq2 hq0 (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith [h]
      have hstep : ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖ ≤ 2 * L + 4 * M := by
        have h1 : ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖
            ≤ ‖w‖⁻¹ * ‖w‖⁻¹ * (L * ‖w‖ + M) :=
          mul_le_mul_of_nonneg_left hinner (mul_nonneg hq0 hq0)
        have h2 : ‖w‖⁻¹ * ‖w‖⁻¹ * (L * ‖w‖ + M)
            = L * (‖w‖⁻¹ * (‖w‖⁻¹ * ‖w‖)) + M * (‖w‖⁻¹ * ‖w‖⁻¹) := by ring
        rw [h2] at h1
        have ha : L * (‖w‖⁻¹ * (‖w‖⁻¹ * ‖w‖)) ≤ L * ‖w‖⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_norm_mul_inv_mul_le w) hL0
        have hb : L * ‖w‖⁻¹ ≤ L * 2 := mul_le_mul_of_nonneg_left hq2 hL0
        have hcc : M * (‖w‖⁻¹ * ‖w‖⁻¹) ≤ M * 4 := mul_le_mul_of_nonneg_left hqq hM0
        linarith
      calc ‖w‖⁻¹ * ‖w‖⁻¹ * ‖g (x + w) - (bumpC w : ℂ) • g x‖ ≤ 2 * L + 4 * M := hstep
        _ ≤ 8 * (L + M + 1) := by linarith
    · -- Case 3: `‖w‖ > max 1 (R + ‖z‖ + 2)`: the integrand vanishes.
      have h3a : max 1 (R + ‖z‖ + 2) < ‖w‖ := not_le.mp hd
      have hB : beurlingBound α K L M R z w = 0 := by
        rw [beurlingBound]
        rw [indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (α - 2)) w, if_neg hc,
            indicator_closedBall_zero (1 / 2) (fun t => ‖t‖ ^ (-1 : ℝ)) w, if_neg hc,
            indicator_closedBall_zero (max 1 (R + ‖z‖ + 2)) (fun _ => (1 : ℝ)) w, if_neg hd]
        ring
      have hw1 : 1 ≤ ‖w‖ := le_trans (le_max_left (1:ℝ) (R + ‖z‖ + 2)) (le_of_lt h3a)
      have hbump0 : bumpC w = 0 := bumpC_eq_zero hw1
      have hgw : g (x + w) = 0 := by
        apply hsupp
        have hRz : R + ‖z‖ + 2 < ‖w‖ := lt_of_le_of_lt (le_max_right (1:ℝ) (R + ‖z‖ + 2)) h3a
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
