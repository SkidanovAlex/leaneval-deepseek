import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Levels._stub
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev2
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev6
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev7
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev8
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev9
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev10
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev11

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev12

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdent.Weyl.Dev5 (GG)

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {C : Physical.PhysClock} {t : ℝ}
  {τ : ℝ}

/-- The axis level of the meridian stream function. -/
noncomputable def axisLevel (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam) (τ : ℝ)
    (z : ℝ) : ℝ :=
  -z * (A τ)⁻¹ * deriv (fun θ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
    (Real.pi / 2)

/-- Pull back a continuity statement along the polar path, `z₀ > 0`. -/
theorem tendsto_comp_pair_pos {Ct : ℝ → ℝ → ℝ} {z₀ b : ℝ} (hz₀ : 0 < z₀) (hB : 0 < B τ)
    (hcont : ContinuousAt (fun p : ℝ × ℝ => Ct p.1 p.2)
      (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ, Real.pi / 2))
    (hval : Ct (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) (Real.pi / 2) = b) :
    Tendsto (fun p : ℝ × ℝ =>
        Ct (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 b) := by
  have hpath : Tendsto (fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
      Work.Cyl.thetaP p.1 p.2)) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ, Real.pi / 2)) :=
    (Dev8.tendsto_pair_pos (α := α) (τ := τ) (B := B) hB hz₀).mono_right
      (nhdsWithin_le_nhds (s := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.2 < Real.pi / 2}))
  have h := hcont.tendsto.comp hpath
  rwa [hval] at h

/-- Pull back a continuity statement along the polar path, `z₀ < 0`. -/
theorem tendsto_comp_pair_neg {Ct : ℝ → ℝ → ℝ} {z₀ b : ℝ} (hz₀ : z₀ < 0) (hB : 0 < B τ)
    (hcont : ContinuousAt (fun p : ℝ × ℝ => Ct p.1 p.2)
      (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ, -(Real.pi / 2)))
    (hval : Ct (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) (-(Real.pi / 2)) = b) :
    Tendsto (fun p : ℝ × ℝ =>
        Ct (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 b) := by
  have hpath : Tendsto (fun p : ℝ × ℝ => (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ,
      Work.Cyl.thetaP p.1 p.2)) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ, -(Real.pi / 2))) :=
    (Dev8.tendsto_pair_neg (α := α) (τ := τ) (B := B) hB hz₀).mono_right
      (nhdsWithin_le_nhds (s := {q : ℝ × ℝ | 0 < q.1 ∧ -Real.pi / 2 < q.2 ∧ q.2 < 0}))
  have h := hcont.tendsto.comp hpath
  rwa [hval] at h

/-- The polar weight tends to `|z₀|^p/b`. -/
theorem tendsto_w_pair {z₀ : ℝ} (hz₀ : z₀ ≠ 0) (_hB : 0 < B τ) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ)) := by
  have hρ0 : 0 < Work.Cyl.rhoP 0 z₀ := Dev8.rhoP_zero_pos hz₀
  have hcont : ContinuousAt
      (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (0, z₀) := by
    have h1 : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) (0, z₀) := by
      have : Continuous (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2) := by
        have hf : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
        exact Real.continuous_sqrt.comp hf
      exact this.continuousAt
    exact (h1.rpow_const (Or.inl (ne_of_gt hρ0))).div_const (B τ)
  exact hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))

/-- The sections `r`, `z` of the polar path. -/
theorem tendsto_fst_pair {z₀ : ℝ} :
    Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0) := by
  have := (continuousAt_fst (p := ((0:ℝ), z₀))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
  simpa using this

theorem tendsto_snd_pair {z₀ : ℝ} :
    Tendsto (fun p : ℝ × ℝ => p.2) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 z₀) := by
  have := (continuousAt_snd (p := ((0:ℝ), z₀))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
  simpa using this

end Work.FTS.BSIdent.Weyl.Dev12
