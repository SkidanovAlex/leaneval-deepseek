import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.StrongEps.E5G

theorem shift_modulus_of_holder {Y : ℕ → ℝ → ℝ → ℝ} {A z θ ρ : ℝ}
    (hA : 0 ≤ A) (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (hρ : 0 < ρ)
    (hρQ : Metric.closedBall (z, θ) ρ ⊆ Work.FTS.EllipticEst.Q0)
    (hholder : ∀ n : ℕ, ∀ q ∈ Metric.closedBall (z, θ) ρ,
      ∀ q' ∈ Metric.closedBall (z, θ) ρ,
      |Y n q.1 q.2 - Y n q'.1 q'.2| ≤ A * Real.sqrt ‖q - q'‖) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p : ℝ × ℝ, ‖p‖ ≤ δ →
      |Y n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - Y n z θ| ≤ η := by
  -- The two shifts are continuous at `p = 0` with value `(z, θ)`; a small parameter `p`
  -- therefore moves the base point inside the ball of Hölder-regularity and by a distance
  -- at most `(η/(A+1))²`, which is what the Hölder bound needs.
  intro η hη
  set F : ℝ × ℝ → ℝ × ℝ :=
    fun p => (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2) with hF
  have hθtan : Real.arctan (Real.tan θ) = θ :=
    Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2
  have hF0 : F 0 = (z, θ) := by
    simp only [hF, Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift,
      Prod.fst_zero, Prod.snd_zero, neg_zero, Real.exp_zero, mul_one, hθtan]
  have hcont : Continuous F := by
    rw [hF]
    refine Continuous.prodMk ?_ ?_
    · simp only [Work.FTS.StrongEps.zShift]
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_neg.comp continuous_fst))
    · simp only [Work.FTS.StrongEps.thShift]
      exact Real.continuous_arctan.comp
        (continuous_const.mul (Real.continuous_exp.comp (continuous_neg.comp continuous_snd)))
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ p : ℝ × ℝ, ‖p‖ ≤ δ →
      dist (F p) (F 0) < min ρ ((η / (A + 1)) ^ 2) := by
    have hτpos : 0 < min ρ ((η / (A + 1)) ^ 2) :=
      lt_min hρ (pow_pos (div_pos hη hA1) 2)
    have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (0 : ℝ × ℝ),
        F p ∈ Metric.ball (F 0) (min ρ ((η / (A + 1)) ^ 2)) :=
      hcont.continuousAt (Metric.ball_mem_nhds (F 0) hτpos)
    obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨δ₀ / 2, by linarith, fun p hp => ?_⟩
    have hp' : p ∈ Metric.ball (0 : ℝ × ℝ) δ₀ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      linarith
    exact Metric.mem_ball.mp (hδ₀sub hp')
  refine ⟨δ, hδpos, ?_⟩
  intro n p hp
  have hdist : dist (F p) (F 0) < min ρ ((η / (A + 1)) ^ 2) := hδ p hp
  have hq : F p ∈ Metric.closedBall (z, θ) ρ := by
    rw [Metric.mem_closedBall, ← hF0]
    exact le_trans hdist.le (min_le_left _ _)
  have hq' : (z, θ) ∈ Metric.closedBall (z, θ) ρ := by
    rw [Metric.mem_closedBall, dist_self]
    exact hρ.le
  have hb := hholder n (F p) hq (z, θ) hq'
  have hnorm : ‖F p - (z, θ)‖ ≤ (η / (A + 1)) ^ 2 := by
    rw [← hF0, ← dist_eq_norm]
    exact le_trans hdist.le (min_le_right _ _)
  have hsqrt : Real.sqrt ‖F p - (z, θ)‖ ≤ η / (A + 1) :=
    calc Real.sqrt ‖F p - (z, θ)‖ ≤ Real.sqrt ((η / (A + 1)) ^ 2) := Real.sqrt_le_sqrt hnorm
      _ = η / (A + 1) := Real.sqrt_sq (le_of_lt (div_pos hη hA1))
  have hcoef : A * (η / (A + 1)) ≤ η := by
    have h1 : A * (η / (A + 1)) = A * η / (A + 1) := by ring
    rw [h1, div_le_iff₀ hA1]
    nlinarith
  calc |Y n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - Y n z θ|
      = |Y n (F p).1 (F p).2 - Y n (z, θ).1 (z, θ).2| := by simp only [hF]
    _ ≤ A * Real.sqrt ‖F p - (z, θ)‖ := hb
    _ ≤ A * (η / (A + 1)) := mul_le_mul_of_nonneg_left hsqrt hA
    _ ≤ η := hcoef

end Work.FTS.StrongEps.E5G
