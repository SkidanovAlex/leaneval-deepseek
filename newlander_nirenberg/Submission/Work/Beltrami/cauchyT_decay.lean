import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.contDiff_cauchyT
import Submission.Work.Beltrami.norm_cauchyT_le
import Submission.Work.Beltrami.hasFDerivAt_cauchyInt_smooth
import Submission.Work.Beltrami.cauchyInt_fderiv_apply

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff
open Work.Beltrami

/-!
# Decay of the Cauchy potential and of its real derivative

`cauchyT f` is the convolution of `f` with the locally integrable kernel `w ↦ w⁻¹`.  For a
continuous compactly supported `g` (with values in a normed space over `ℂ`) the function

  `z ↦ ∫ u, u⁻¹ • g (z + u)`

decays like `1/‖z‖`: for `‖z‖` large the kernel `u ↦ (u⁻¹)` is bounded by `2/‖z‖` on the support
of `u ↦ g (z + u)` (which lies at distance `‖z‖ - R` from the origin), while for bounded `z` a
crude estimate with `∫_{‖u‖ ≤ ρ} ‖u‖⁻¹ = 2πρ` suffices.

Both the Cauchy potential `cauchyT f` itself and its real derivative — the latter computed by
differentiating under the integral sign, `fderiv ℝ (cauchyInt f) z = ∫ u, u⁻¹ • fderiv ℝ f (z+u)`
(`hasFDerivAt_cauchyInt_c1`) — are of this form, which gives `cauchyT_decay`.
-/

noncomputable section

/-- **Decay of the Cauchy-type potential of an arbitrary (Banach-space valued) compactly
supported function.**  If `g : ℂ → E` is continuous with compact support, then
`z ↦ ∫ u, u⁻¹ • g (z + u)` is `O(1/‖z‖)`. -/
lemma integral_inv_smul_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : ℂ → E) (hg : Continuous g) (hc : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖∫ u, (u⁻¹ : ℂ) • g (z + u) ∂volume‖ ≤ C / (1 + ‖z‖) := by
  obtain ⟨R, hRp, hR⟩ := hc.exists_pos_le_norm
  obtain ⟨M₀, hM₀⟩ := hg.bounded_above_of_compact_support hc
  set M : ℝ := max M₀ 0 with hMdef
  have hMn : 0 ≤ M := le_max_right _ _
  have hM : ∀ x : ℂ, ‖g x‖ ≤ M := fun x => le_trans (hM₀ x) (le_max_left _ _)
  have hInt : Integrable g volume := hg.integrable_of_hasCompactSupport hc
  have hIntn : Integrable (fun u : ℂ => ‖g u‖) volume := hInt.norm
  have hRS : (0 : ℝ) ≤ R + (2 * R + 2) := by linarith
  refine ⟨max 1 (max (4 * (∫ u, ‖g u‖))
      (M * (2 * Real.pi * (R + (2 * R + 2))) * (1 + (2 * R + 2)))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z
  rcases le_or_gt (2 * R + 2) ‖z‖ with hz | hz
  · -- far from the support: the kernel is bounded by `2/‖z‖` there
    have hzpos : 0 < ‖z‖ := by linarith
    have hpt : ∀ u : ℂ, ‖(u⁻¹ : ℂ) • g (z + u)‖ ≤ (2 / ‖z‖) * ‖g (z + u)‖ := by
      intro u
      rcases eq_or_ne (g (z + u)) 0 with h0 | h0
      · rw [h0, smul_zero, norm_zero]; simp
      · have hlt : ‖z + u‖ < R := not_le.mp (fun hle => h0 (hR (z + u) hle))
        have hzu : ‖z‖ ≤ ‖z + u‖ + ‖u‖ := by
          have h := norm_sub_le (z + u) u
          rwa [add_sub_cancel_right] at h
        have hzu2 : ‖z‖ / 2 < ‖u‖ := by linarith
        have huinv : ‖u‖⁻¹ ≤ 2 / ‖z‖ := by
          have h1 : 1 / ‖u‖ ≤ 1 / (‖z‖ / 2) :=
            one_div_le_one_div_of_le (by linarith) hzu2.le
          simpa [one_div, inv_div] using h1
        rw [norm_smul, norm_inv]
        exact mul_le_mul_of_nonneg_right huinv (norm_nonneg _)
    have hIntshift : Integrable (fun u : ℂ => ‖g (z + u)‖) volume := by
      simpa [add_comm] using hIntn.comp_add_right z
    have hstep1 : ∫ u, ‖(u⁻¹ : ℂ) • g (z + u)‖ ≤ ∫ u, (2 / ‖z‖) * ‖g (z + u)‖ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => norm_nonneg _))
        (hIntshift.const_mul (2 / ‖z‖)) (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul] at hstep1
    have htrans : ∫ u, ‖g (z + u)‖ = ∫ u, ‖g u‖ := by
      rw [← integral_add_right_eq_self (fun u : ℂ => ‖g u‖) z]
      simp [add_comm]
    rw [htrans] at hstep1
    have hL : 0 ≤ ∫ u, ‖g u‖ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall (fun u => norm_nonneg (g u)))
    have h1 : 2 / ‖z‖ ≤ 4 / (1 + ‖z‖) := by
      rw [div_le_div_iff₀ hzpos (by linarith)]
      linarith
    have hlarge : ‖∫ u, (u⁻¹ : ℂ) • g (z + u)‖ ≤ 4 * (∫ u, ‖g u‖) / (1 + ‖z‖) := by
      refine le_trans (le_trans (norm_integral_le_integral_norm _) hstep1) ?_
      calc (2 / ‖z‖) * ∫ u, ‖g u‖ ≤ (4 / (1 + ‖z‖)) * ∫ u, ‖g u‖ :=
            mul_le_mul_of_nonneg_right h1 hL
        _ = 4 * (∫ u, ‖g u‖) / (1 + ‖z‖) := by ring
    refine le_trans hlarge (div_le_div_of_nonneg_right ?_ (by positivity))
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · -- near the support: dominate by a fixed multiple of `‖·‖⁻¹` on a fixed disc
    have hsmall : ‖∫ u, (u⁻¹ : ℂ) • g (z + u)‖ ≤ M * (2 * Real.pi * (R + (2 * R + 2))) := by
      set J : ℂ → ℝ := (Metric.ball 0 (R + (2 * R + 2))).indicator (fun w => ‖w‖⁻¹) with hJ
      have hJint : Integrable J volume := by
        rw [hJ]; exact Work.Beltrami.integrable_indicator_norm_inv 0 (R + (2 * R + 2))
      have hJval : ∫ u, J u = 2 * Real.pi * (R + (2 * R + 2)) := by
        rw [hJ, integral_indicator Metric.isOpen_ball.measurableSet]
        exact Work.Beltrami.integral_ball_norm_inv (R + (2 * R + 2)) hRS
      have hpt : ∀ u : ℂ, ‖(u⁻¹ : ℂ) • g (z + u)‖ ≤ M * J u := by
        intro u
        rcases eq_or_ne (g (z + u)) 0 with h0 | h0
        · rw [h0, smul_zero, norm_zero]
          exact mul_nonneg hMn (Set.indicator_nonneg (fun _ _ => by positivity) u)
        · have hlt : ‖z + u‖ < R := not_le.mp (fun hle => h0 (hR (z + u) hle))
          have hzu : ‖u‖ ≤ ‖z + u‖ + ‖z‖ := by
            have h := norm_sub_le (z + u) z
            rwa [add_sub_cancel_left] at h
          have hu : u ∈ Metric.ball 0 (R + (2 * R + 2)) := by
            rw [Metric.mem_ball, dist_zero_right]
            linarith
          rw [hJ, Set.indicator_of_mem hu, norm_smul, norm_inv, mul_comm]
          exact mul_le_mul_of_nonneg_right (hM (z + u)) (inv_nonneg.mpr (norm_nonneg u))
      have hIntball : Integrable (fun u : ℂ => M * J u) volume := hJint.const_mul M
      have hstep : ∫ u, ‖(u⁻¹ : ℂ) • g (z + u)‖ ≤ ∫ u, M * J u :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => norm_nonneg _))
          hIntball (Filter.Eventually.of_forall hpt)
      rw [integral_const_mul, hJval] at hstep
      exact le_trans (norm_integral_le_integral_norm _) hstep
    refine le_trans hsmall ?_
    have hBnn : 0 ≤ M * (2 * Real.pi * (R + (2 * R + 2))) :=
      mul_nonneg hMn (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hRS)
    have h2 : M * (2 * Real.pi * (R + (2 * R + 2))) ≤
        M * (2 * Real.pi * (R + (2 * R + 2))) * (1 + (2 * R + 2)) / (1 + ‖z‖) := by
      have hle : 1 ≤ (1 + (2 * R + 2)) / (1 + ‖z‖) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      calc M * (2 * Real.pi * (R + (2 * R + 2)))
          = M * (2 * Real.pi * (R + (2 * R + 2))) * 1 := by ring
        _ ≤ M * (2 * Real.pi * (R + (2 * R + 2))) * ((1 + (2 * R + 2)) / (1 + ‖z‖)) :=
            mul_le_mul_of_nonneg_left hle hBnn
        _ = M * (2 * Real.pi * (R + (2 * R + 2))) * (1 + (2 * R + 2)) / (1 + ‖z‖) := by ring
    exact le_trans h2 (div_le_div_of_nonneg_right
      (le_trans (le_max_right _ _) (le_max_right _ _)) (by positivity))

/-- The constant `-(1/π)`, seen as a complex number, has norm `1/π`. -/
private lemma norm_neg_inv_pi : ‖((-((Real.pi : ℝ))⁻¹ : ℝ) : ℂ)‖ = (Real.pi)⁻¹ := by
  rw [show ‖((-((Real.pi : ℝ))⁻¹ : ℝ) : ℂ)‖ = |(-((Real.pi : ℝ))⁻¹)| from RCLike.norm_ofReal _,
    abs_neg, abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]

/-- For smooth compactly supported `f`, the Cauchy potential `cauchyT f` and its real derivative
decay like `1/‖z‖` at infinity. -/
theorem cauchyT_decay (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖cauchyT f z‖ ≤ C / (1 + ‖z‖) ∧
      ‖fderiv ℝ (cauchyT f) z‖ ≤ C / (1 + ‖z‖) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hfcs : HasCompactSupport (fderiv ℝ f) := hc.fderiv ℝ
  obtain ⟨Cg, hCgp, hCg⟩ := integral_inv_smul_decay f hf.continuous hc
  obtain ⟨Cd, hCdp, hCd⟩ := integral_inv_smul_decay (fderiv ℝ f) hfdc hfcs
  refine ⟨max ((Real.pi)⁻¹ * Cg) ((Real.pi)⁻¹ * Cd),
    lt_of_lt_of_le (mul_pos (by positivity) hCgp) (le_max_left _ _), ?_⟩
  intro z
  have hcg : ‖cauchyInt f z‖ ≤ Cg / (1 + ‖z‖) := by
    simpa only [cauchyInt, smul_eq_mul] using hCg z
  have hcd : ‖∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u)‖ ≤ Cd / (1 + ‖z‖) := hCd z
  have hT : cauchyT f = fun y => ((-((Real.pi : ℝ))⁻¹ : ℝ) : ℂ) * cauchyInt f y :=
    funext fun y => cauchyT_eq_cauchyInt f y
  have hL : HasFDerivAt (cauchyInt f) (∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u)) z :=
    hasFDerivAt_cauchyInt_c1 f hf1 hc z
  have hfd : fderiv ℝ (cauchyT f) z = ((-((Real.pi : ℝ))⁻¹ : ℝ) : ℂ) •
      (∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u)) := by
    rw [hT]; exact (hL.const_mul _).fderiv
  constructor
  · calc ‖cauchyT f z‖ = ‖((-((Real.pi : ℝ))⁻¹ : ℝ) : ℂ) * cauchyInt f z‖ := by rw [hT]
      _ = ‖((-((Real.pi : ℝ))⁻¹ : ℝ) : ℂ)‖ * ‖cauchyInt f z‖ := norm_mul _ _
      _ = (Real.pi)⁻¹ * ‖cauchyInt f z‖ := by rw [norm_neg_inv_pi]
      _ ≤ (Real.pi)⁻¹ * (Cg / (1 + ‖z‖)) := mul_le_mul_of_nonneg_left hcg (by positivity)
      _ = ((Real.pi)⁻¹ * Cg) / (1 + ‖z‖) := by ring
      _ ≤ max ((Real.pi)⁻¹ * Cg) ((Real.pi)⁻¹ * Cd) / (1 + ‖z‖) :=
          div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc ‖fderiv ℝ (cauchyT f) z‖ = ‖((-((Real.pi : ℝ))⁻¹ : ℝ) : ℂ) •
          (∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u))‖ := by rw [hfd]
      _ = ‖((-((Real.pi : ℝ))⁻¹ : ℝ) : ℂ)‖ *
          ‖∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u)‖ := norm_smul _ _
      _ = (Real.pi)⁻¹ * ‖∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u)‖ := by rw [norm_neg_inv_pi]
      _ ≤ (Real.pi)⁻¹ * (Cd / (1 + ‖z‖)) := mul_le_mul_of_nonneg_left hcd (by positivity)
      _ = ((Real.pi)⁻¹ * Cd) / (1 + ‖z‖) := by ring
      _ ≤ max ((Real.pi)⁻¹ * Cg) ((Real.pi)⁻¹ * Cd) / (1 + ‖z‖) :=
          div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

end

end Work.Beltrami
