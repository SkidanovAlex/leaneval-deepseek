import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Levels._stub
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev2
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev6
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev8
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev9
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev10
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev12

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev13

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdent.Weyl.Dev5 (GG)
open Work.FTS.BSIdent.Weyl.Dev8 (rhoP_zero_pos)

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {C : Physical.PhysClock} {t : ℝ}
  {τ : ℝ}

/-- The `(r,z)`-filter used for the axis limits. -/
theorem nhdsWithin_axis {z₀ : ℝ} (hz₀ : z₀ ≠ 0) :
    𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀) = 𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀) := by
  have hAC : {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}
      = {p : ℝ × ℝ | p.2 ≠ 0} ∩ {p : ℝ × ℝ | 0 < p.1} := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, and_comm]
  have hmem : {p : ℝ × ℝ | p.2 ≠ 0} ∈ 𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), z₀) :=
    nhdsWithin_le_nhds ((isOpen_ne.preimage continuous_snd).mem_nhds (by
      show ((0:ℝ), z₀) ∈ (fun p : ℝ × ℝ => p.2) ⁻¹' {y : ℝ | y ≠ 0}
      simpa using hz₀))
  rw [hAC, nhdsWithin_inter_of_mem hmem]

/-- The arithmetic core: the limit of `∂_rψ` from the three composed limits. -/
theorem tendsto_pdR_axis_core {z₀ : ℝ} (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) {z₀ : ℝ}
    (hz₀ : z₀ ≠ 0)
    (hw₀pos : 0 < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ)
    (hG : Tendsto (fun p : ℝ × ℝ => GG Φ τ
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0))
    (hDW : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ)
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0))
    (hDT : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ)
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
        (Real.pi / 2)))) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀))
      (𝓝 (Dev12.axisLevel α A B Φ τ z₀)) := by
  have hmono : 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] ((0:ℝ), z₀)
      ≤ 𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), z₀) :=
    nhdsWithin_mono _ (fun p hp => hp.1)
  have hr := (Dev12.tendsto_fst_pair (z₀ := z₀)).mono_left hmono
  have hz := (Dev12.tendsto_snd_pair (z₀ := z₀)).mono_left hmono
  have hw := (Dev12.tendsto_w_pair (α := α) (τ := τ) (B := B) (z₀ := z₀) hz₀ hB).mono_left hmono
  have hG := hG.mono_left hmono
  have hDW := hDW.mono_left hmono
  have hDT := hDT.mono_left hmono
  -- ### the two summands of the formula
  have h1 : Tendsto (fun p : ℝ × ℝ => 2 * p.1 * (A τ)⁻¹ * GG Φ τ
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀)) (𝓝 (2 * 0 * (A τ)⁻¹ * 0)) := by
    have hcoef : Tendsto (fun p : ℝ × ℝ => 2 * p.1 * (A τ)⁻¹)
        (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀)) (𝓝 (2 * 0 * (A τ)⁻¹)) :=
      ((tendsto_const_nhds (x := (2:ℝ))).mul hr).mul_const (A τ)⁻¹
    exact hcoef.mul hG
  have h2a : Tendsto (fun p : ℝ × ℝ => Work.FTS.Regularity.pExp α * p.1
        * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
        * Work.Cyl.pdR (GG Φ τ)
            (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀))
      (𝓝 (Work.FTS.Regularity.pExp α * 0 * (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α
        / B τ) * 0)) :=
    ((tendsto_const_nhds (x := Work.FTS.Regularity.pExp α)).mul hr |>.mul hw).mul hDW
  have h2b : Tendsto (fun p : ℝ × ℝ => (-p.2) * Work.Cyl.pdZ (GG Φ τ)
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀))
      (𝓝 ((-z₀) * deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
        (Real.pi / 2))) :=
    hz.neg.mul hDT
  have h2 : Tendsto (fun p : ℝ × ℝ => (A τ)⁻¹ *
        (Work.FTS.Regularity.pExp α * p.1 * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α
            / B τ)
          * Work.Cyl.pdR (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)
          + (-p.2) * Work.Cyl.pdZ (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀))
      (𝓝 ((A τ)⁻¹ * (Work.FTS.Regularity.pExp α * 0 * (Work.Cyl.rhoP 0 z₀
          ^ Work.FTS.Regularity.pExp α / B τ) * 0
        + (-z₀) * deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ)
            θ τ) (Real.pi / 2)))) :=
    tendsto_const_nhds.mul (h2a.add h2b)
  have hsum := h1.add h2
  -- ### compare with `∂_rψ`
  have hev : (fun p : ℝ × ℝ => 2 * p.1 * (A τ)⁻¹ * GG Φ τ
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2)
        + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * p.1
            * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
          * Work.Cyl.pdR (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)
          + (-p.2) * Work.Cyl.pdZ (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)))
      =ᶠ[𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀)]
      (fun p : ℝ × ℝ => Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (Dev6.pdR_merPsiT_eq (α := α) (τ := τ) hτ hsm hB hp.1 hp.2).symm
  have hval : 2 * 0 * (A τ)⁻¹ * 0
      + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * 0 * (Work.Cyl.rhoP 0 z₀
          ^ Work.FTS.Regularity.pExp α / B τ) * 0
        + (-z₀) * deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ)
            θ τ) (Real.pi / 2))
      = Dev12.axisLevel α A B Φ τ z₀ := by
    rw [Dev12.axisLevel]
    ring
  rw [hval] at hsum
  exact hsum.congr' hev


/-- The arithmetic core: the limit of `∂_zψ` from the three composed limits. -/
theorem tendsto_pdZ_axis_core {z₀ : ℝ} (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) {z₀ : ℝ}
    (hz₀ : z₀ ≠ 0)
    (hG : Tendsto (fun p : ℝ × ℝ => GG Φ τ
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0))
    (hDW : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ)
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0))
    (hDT : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ)
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
        (Real.pi / 2)))) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀)) (𝓝 0) := by
  have hmono : 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] ((0:ℝ), z₀)
      ≤ 𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), z₀) :=
    nhdsWithin_mono _ (fun p hp => hp.1)
  have hr := (Dev12.tendsto_fst_pair (z₀ := z₀)).mono_left hmono
  have hz := (Dev12.tendsto_snd_pair (z₀ := z₀)).mono_left hmono
  have hw := (Dev12.tendsto_w_pair (α := α) (τ := τ) (B := B) (z₀ := z₀) hz₀ hB).mono_left hmono
  have hG := hG.mono_left hmono
  have hDW := hDW.mono_left hmono
  have hDT := hDT.mono_left hmono
  have h1 : Tendsto (fun p : ℝ × ℝ => 2 * p.2 * (A τ)⁻¹ * GG Φ τ
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀)) (𝓝 (2 * z₀ * (A τ)⁻¹ * 0)) := by
    have hcoef : Tendsto (fun p : ℝ × ℝ => 2 * p.2 * (A τ)⁻¹)
        (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀)) (𝓝 (2 * z₀ * (A τ)⁻¹)) :=
      ((tendsto_const_nhds (x := (2:ℝ))).mul hz).mul_const (A τ)⁻¹
    exact hcoef.mul hG
  have h2a : Tendsto (fun p : ℝ × ℝ => Work.FTS.Regularity.pExp α * p.2
        * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
        * Work.Cyl.pdR (GG Φ τ)
            (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀))
      (𝓝 (Work.FTS.Regularity.pExp α * z₀ * (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α
        / B τ) * 0)) :=
    ((tendsto_const_nhds (x := Work.FTS.Regularity.pExp α)).mul hz |>.mul hw).mul hDW
  have h2b : Tendsto (fun p : ℝ × ℝ => p.1 * Work.Cyl.pdZ (GG Φ τ)
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀))
      (𝓝 (0 * deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ) θ τ)
        (Real.pi / 2))) :=
    hr.mul hDT
  have h2 : Tendsto (fun p : ℝ × ℝ => (A τ)⁻¹ *
        (Work.FTS.Regularity.pExp α * p.2 * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α
            / B τ)
          * Work.Cyl.pdR (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)
          + p.1 * Work.Cyl.pdZ (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)))
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀))
      (𝓝 ((A τ)⁻¹ * (Work.FTS.Regularity.pExp α * z₀ * (Work.Cyl.rhoP 0 z₀
          ^ Work.FTS.Regularity.pExp α / B τ) * 0
        + 0 * deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ)
            θ τ) (Real.pi / 2)))) :=
    tendsto_const_nhds.mul (h2a.add h2b)
  have hsum := h1.add h2
  have hev : (fun p : ℝ × ℝ => 2 * p.2 * (A τ)⁻¹ * GG Φ τ
        (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ) (Work.Cyl.thetaP p.1 p.2)
        + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * p.2
            * (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
          * Work.Cyl.pdR (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)
          + p.1 * Work.Cyl.pdZ (GG Φ τ)
              (Work.Cyl.rhoP p.1 p.2 ^ Work.FTS.Regularity.pExp α / B τ)
              (Work.Cyl.thetaP p.1 p.2)))
      =ᶠ[𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ p.2 ≠ 0}] (0, z₀)]
      (fun p : ℝ × ℝ => Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (Dev6.pdZ_merPsiT_eq (α := α) (τ := τ) hτ hsm hB hp.1 hp.2).symm
  have hval : 2 * z₀ * (A τ)⁻¹ * 0
      + (A τ)⁻¹ * (Work.FTS.Regularity.pExp α * z₀ * (Work.Cyl.rhoP 0 z₀
          ^ Work.FTS.Regularity.pExp α / B τ) * 0
        + 0 * deriv (fun θ => Φ (Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ)
            θ τ) (Real.pi / 2)) = 0 := by ring
  rw [hval] at hsum
  exact hsum.congr' hev

/-- `∂_rψ` tends to the axis level along `r → 0⁺`, `z → z₀ ≠ 0`. -/
theorem tendsto_pdR_axis {z₀ : ℝ} (hz₀ : z₀ ≠ 0) (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Dev12.axisLevel α A B Φ τ z₀)) := by
  have hw₀pos : 0 < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (rhoP_zero_pos hz₀) _) hB
  have hw₀1 : (-1:ℝ) < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ := by linarith
  rcases lt_or_gt_of_ne hz₀ with hneg | hpos
  · have hG := Dev12.tendsto_comp_pair_neg (α := α) (τ := τ) (B := B) (Ct := fun w θ => GG Φ τ w θ)
      hneg hB (Dev2.continuousAt_GG_neg_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.GG_neg_pi_div_two_eq_zero (τ := τ) (Φ := Φ) hw₀pos hπ)
    have hDW := Dev12.tendsto_comp_pair_neg (α := α) (τ := τ) (B := B)
      (Ct := fun w θ => Work.Cyl.pdR (GG Φ τ) w θ)
      hneg hB (Dev2.continuousAt_pdR_GG_neg_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.pdR_GG_neg_pi_div_two_eq_zero (τ := τ) (Φ := Φ) hw₀pos hπ)
    have hDT := Dev12.tendsto_comp_pair_neg (α := α) (τ := τ) (B := B)
      (Ct := fun w θ => Work.Cyl.pdZ (GG Φ τ) w θ)
      hneg hB (Dev2.continuousAt_pdZ_GG_neg_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.pdZ_GG_neg_pi_div_two_eq (τ := τ) (Φ := Φ) hw₀pos h0)
    have hmain := tendsto_pdR_axis_core (α := α) (A := A) (B := B) (Φ := Φ) (τ := τ) (z₀ := z₀)
      hτ hsm h0 hπ hB hz₀ hw₀pos hG hDW hDT
    rwa [nhdsWithin_axis hz₀] at hmain
  · have hG := Dev12.tendsto_comp_pair_pos (α := α) (τ := τ) (B := B) (Ct := fun w θ => GG Φ τ w θ)
      hpos hB (Dev2.continuousAt_GG_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.GG_pi_div_two_eq_zero (τ := τ) (Φ := Φ) hw₀pos hπ)
    have hDW := Dev12.tendsto_comp_pair_pos (α := α) (τ := τ) (B := B)
      (Ct := fun w θ => Work.Cyl.pdR (GG Φ τ) w θ)
      hpos hB (Dev2.continuousAt_pdR_GG_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.pdR_GG_pi_div_two_eq_zero (τ := τ) (Φ := Φ) hw₀pos hπ)
    have hDT := Dev12.tendsto_comp_pair_pos (α := α) (τ := τ) (B := B)
      (Ct := fun w θ => Work.Cyl.pdZ (GG Φ τ) w θ)
      hpos hB (Dev2.continuousAt_pdZ_GG_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.pdZ_GG_pi_div_two_eq (τ := τ) (Φ := Φ)
        (w₀ := Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ))
    have hmain := tendsto_pdR_axis_core (α := α) (A := A) (B := B) (Φ := Φ) (τ := τ) (z₀ := z₀)
      hτ hsm h0 hπ hB hz₀ hw₀pos hG hDW hDT
    rwa [nhdsWithin_axis hz₀] at hmain


/-- `∂_zψ` tends to `0` along `r → 0⁺`, `z → z₀ ≠ 0`. -/
theorem tendsto_pdZ_axis {z₀ : ℝ} (hz₀ : z₀ ≠ 0) (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0) := by
  have hw₀pos : 0 < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (rhoP_zero_pos hz₀) _) hB
  have hw₀1 : (-1:ℝ) < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ := by linarith
  rcases lt_or_gt_of_ne hz₀ with hneg | hpos
  · have hG := Dev12.tendsto_comp_pair_neg (α := α) (τ := τ) (B := B) (Ct := fun w θ => GG Φ τ w θ)
      hneg hB (Dev2.continuousAt_GG_neg_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.GG_neg_pi_div_two_eq_zero (τ := τ) (Φ := Φ) hw₀pos hπ)
    have hDW := Dev12.tendsto_comp_pair_neg (α := α) (τ := τ) (B := B)
      (Ct := fun w θ => Work.Cyl.pdR (GG Φ τ) w θ)
      hneg hB (Dev2.continuousAt_pdR_GG_neg_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.pdR_GG_neg_pi_div_two_eq_zero (τ := τ) (Φ := Φ) hw₀pos hπ)
    have hDT := Dev12.tendsto_comp_pair_neg (α := α) (τ := τ) (B := B)
      (Ct := fun w θ => Work.Cyl.pdZ (GG Φ τ) w θ)
      hneg hB (Dev2.continuousAt_pdZ_GG_neg_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.pdZ_GG_neg_pi_div_two_eq (τ := τ) (Φ := Φ) hw₀pos h0)
    have hmain := tendsto_pdZ_axis_core (α := α) (A := A) (B := B) (Φ := Φ) (τ := τ) (z₀ := z₀)
      hτ hsm h0 hπ hB hz₀ hG hDW hDT
    rwa [nhdsWithin_axis hz₀] at hmain
  · have hG := Dev12.tendsto_comp_pair_pos (α := α) (τ := τ) (B := B) (Ct := fun w θ => GG Φ τ w θ)
      hpos hB (Dev2.continuousAt_GG_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.GG_pi_div_two_eq_zero (τ := τ) (Φ := Φ) hw₀pos hπ)
    have hDW := Dev12.tendsto_comp_pair_pos (α := α) (τ := τ) (B := B)
      (Ct := fun w θ => Work.Cyl.pdR (GG Φ τ) w θ)
      hpos hB (Dev2.continuousAt_pdR_GG_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.pdR_GG_pi_div_two_eq_zero (τ := τ) (Φ := Φ) hw₀pos hπ)
    have hDT := Dev12.tendsto_comp_pair_pos (α := α) (τ := τ) (B := B)
      (Ct := fun w θ => Work.Cyl.pdZ (GG Φ τ) w θ)
      hpos hB (Dev2.continuousAt_pdZ_GG_pi_div_two (τ := τ) (Φ := Φ) hsm hw₀1)
      (Dev10.pdZ_GG_pi_div_two_eq (τ := τ) (Φ := Φ)
        (w₀ := Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ))
    have hmain := tendsto_pdZ_axis_core (α := α) (A := A) (B := B) (Φ := Φ) (τ := τ) (z₀ := z₀)
      hτ hsm h0 hπ hB hz₀ hG hDW hDT
    rwa [nhdsWithin_axis hz₀] at hmain

end Work.FTS.BSIdent.Weyl.Dev13
