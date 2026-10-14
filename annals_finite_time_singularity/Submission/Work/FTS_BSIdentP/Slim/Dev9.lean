import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS_BSIdentP.Slim.Dev5
import Submission.Work.FTS_BSIdentP.Slim.Dev8
import Submission.Work.FTS_BSIdentP.Slim.DevStub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev9

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)
open Work.FTS.BSIdentP.Dev8 (rhoP_zero_pos rhoP_zero_eq_abs)

variable {τ : ℝ}

/-- `ψ/r` tends to the axis level when `z → z₀` with `z₀ > 0`. -/
theorem tendsto_div_fst_axis_pos {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hτ : τ = Physical.clockInv C t) {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) :
    Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (-z₀ * (A τ)⁻¹ *
        deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2))) := by
  have hw₀pos : 0 < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (rhoP_zero_pos (ne_of_gt hz₀)) _) hB
  have hE := (DevStub.tendsto_PhiOdd_div_cos_at_pi_div_two (τ := τ) hsm hπ hw₀pos).comp
    (Dev8.tendsto_pair_pos (α := α) (τ := τ) (B := B) hB hz₀)
  have hρ : Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 (Work.Cyl.rhoP 0 z₀)) := by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) ((0:ℝ), z₀) := by
      have : Continuous (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) := by
        have hf : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
        exact Real.continuous_sqrt.comp hf
      exact this.continuousAt
    exact hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
  have hmul : Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 * (A τ)⁻¹
        * (GG Φ τ (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP p.1 p.2) / Real.cos (Work.Cyl.thetaP p.1 p.2)))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Work.Cyl.rhoP 0 z₀ * (A τ)⁻¹ *
        (-(deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2))))) :=
    (hρ.mul_const (A τ)⁻¹).mul hE
  have hval : Work.Cyl.rhoP 0 z₀ * (A τ)⁻¹ *
        (-(deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2)))
      = -z₀ * (A τ)⁻¹ *
        deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2) := by
    rw [rhoP_zero_eq_abs z₀, abs_of_pos hz₀]; ring
  rw [hval] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (Dev5.merPsiT_div_fst (τ := τ) hτ hp).symm

/-- `ψ/r` tends to the axis level when `z → z₀` with `z₀ < 0`. -/
theorem tendsto_div_fst_axis_neg {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hτ : τ = Physical.clockInv C t) {z₀ : ℝ} (hz₀ : z₀ < 0)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) :
    Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (-z₀ * (A τ)⁻¹ *
        deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2))) := by
  have hw₀pos : 0 < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (rhoP_zero_pos (ne_of_lt hz₀)) _) hB
  have hE := (DevStub.tendsto_PhiOdd_div_cos_at_neg_pi_div_two (τ := τ) hsm hπ hw₀pos).comp
    (Dev8.tendsto_pair_neg (α := α) (τ := τ) (B := B) hB hz₀)
  have hρ : Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 (Work.Cyl.rhoP 0 z₀)) := by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) ((0:ℝ), z₀) := by
      have : Continuous (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) := by
        have hf : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
        exact Real.continuous_sqrt.comp hf
      exact this.continuousAt
    exact hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
  have hmul : Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 * (A τ)⁻¹
        * (GG Φ τ (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP p.1 p.2) / Real.cos (Work.Cyl.thetaP p.1 p.2)))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Work.Cyl.rhoP 0 z₀ * (A τ)⁻¹ *
        deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2))) :=
    (hρ.mul_const (A τ)⁻¹).mul hE
  have hval : Work.Cyl.rhoP 0 z₀ * (A τ)⁻¹ *
        deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2)
      = -z₀ * (A τ)⁻¹ *
        deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2) := by
    rw [rhoP_zero_eq_abs z₀, abs_of_neg hz₀]
  rw [hval] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (Dev5.merPsiT_div_fst (τ := τ) hτ hp).symm

/-- `ψ/r` tends to the axis level when `z → z₀ ≠ 0`. -/
theorem tendsto_div_fst_axis {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hτ : τ = Physical.clockInv C t) {z₀ : ℝ} (hz₀ : z₀ ≠ 0)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) :
    Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (-z₀ * (A τ)⁻¹ *
        deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
          (Real.pi / 2))) := by
  rcases lt_or_gt_of_ne hz₀ with h | h
  · exact tendsto_div_fst_axis_neg hτ h hsm hπ hB
  · exact tendsto_div_fst_axis_pos hτ h hsm hπ hB

end Work.FTS.BSIdentP.Dev9
