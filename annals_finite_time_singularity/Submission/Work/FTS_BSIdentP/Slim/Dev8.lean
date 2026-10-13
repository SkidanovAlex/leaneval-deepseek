import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS_BSIdentP.Slim.DevStub
import Submission.Work.FTS_BSIdentP.Slim.Dev5
import Submission.Work.FTS_BSIdentP.Slim.Dev7

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev8

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)

variable {τ : ℝ}

theorem rhoP_zero_pos {z : ℝ} (hz : z ≠ 0) : 0 < Work.Cyl.rhoP 0 z := by
  rw [Work.Cyl.rhoP, Real.sqrt_pos]
  have : 0 < z ^ 2 := by positivity
  simpa using this

theorem rhoP_zero_eq_abs (z : ℝ) : Work.Cyl.rhoP 0 z = |z| := by
  rw [Work.Cyl.rhoP, show (0:ℝ) ^ 2 + z ^ 2 = z ^ 2 from by ring, Real.sqrt_sq_eq_abs]

/-- The polar pair tends to `(|z₀|^p/b, π/2)` along `r → 0⁺`, `z → z₀ > 0`. -/
theorem tendsto_pair_pos {α : ℝ} {B : ℝ → ℝ} (hB : 0 < B τ) {z₀ : ℝ} (hz₀ : 0 < z₀) :
    Tendsto (fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
        Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.2 < Real.pi / 2}]
        (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ, Real.pi / 2)) := by
  have hz0 : (0:ℝ) ≠ 0 ∨ z₀ ≠ 0 := Or.inr (ne_of_gt hz₀)
  have hρ0 : 0 < Work.Cyl.rhoP 0 z₀ := rhoP_zero_pos (ne_of_gt hz₀)
  have hw : Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ)) := by
    have hcont : ContinuousAt
        (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (0, z₀) := by
      have h1 : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) (0, z₀) := by
        have : Continuous (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) := by
          have hf : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
          exact Real.continuous_sqrt.comp hf
        exact this.continuousAt
      exact (h1.rpow_const (Or.inl (ne_of_gt hρ0))).div_const (B τ)
    exact hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
  have hθ := Dev7.tendsto_thetaP_pi_div_two (z₀ := z₀) hz₀
  refine tendsto_nhdsWithin_iff.mpr ⟨Filter.Tendsto.prodMk_nhds hw hθ, ?_⟩
  have e1 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)),
      0 < Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hp p.2) _) hB
  have e2 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), 0 < Work.Cyl.thetaP p.1 p.2 :=
    hθ.eventually (Ioi_mem_nhds (by linarith [Real.pi_pos]))
  have e3 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)),
      Work.Cyl.thetaP p.1 p.2 < Real.pi / 2 := by
    filter_upwards with p
    exact Work.FTS.BSIdent.Cyl.thetaP_lt_pi_div_two p.1 p.2
  filter_upwards [e1, e2, e3] with p h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- The polar pair tends to `(|z₀|^p/b, -π/2)` along `r → 0⁺`, `z → z₀ < 0`. -/
theorem tendsto_pair_neg {α : ℝ} {B : ℝ → ℝ} (hB : 0 < B τ) {z₀ : ℝ} (hz₀ : z₀ < 0) :
    Tendsto (fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
        Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ -Real.pi / 2 < q.2 ∧ q.2 < 0}]
        (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ, -(Real.pi / 2))) := by
  have hρ0 : 0 < Work.Cyl.rhoP 0 z₀ := rhoP_zero_pos (ne_of_lt hz₀)
  have hw : Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ)) := by
    have hcont : ContinuousAt
        (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (0, z₀) := by
      have h1 : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) (0, z₀) := by
        have : Continuous (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) := by
          have hf : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
          exact Real.continuous_sqrt.comp hf
        exact this.continuousAt
      exact (h1.rpow_const (Or.inl (ne_of_gt hρ0))).div_const (B τ)
    exact hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
  have hθ := Dev7.tendsto_thetaP_neg_pi_div_two (z₀ := z₀) hz₀
  refine tendsto_nhdsWithin_iff.mpr ⟨Filter.Tendsto.prodMk_nhds hw hθ, ?_⟩
  have e1 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)),
      0 < Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hp p.2) _) hB
  have e2 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), -Real.pi / 2 < Work.Cyl.thetaP p.1 p.2 := by
    filter_upwards with p
    have := Work.FTS.BSIdent.Cyl.neg_pi_div_two_lt_thetaP p.1 p.2
    linarith [this]
  have e3 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), Work.Cyl.thetaP p.1 p.2 < 0 :=
    hθ.eventually (Iio_mem_nhds (by linarith [Real.pi_pos]))
  filter_upwards [e1, e2, e3] with p h1 h2 h3
  exact ⟨h1, h2, h3⟩

end Work.FTS.BSIdentP.Dev8
