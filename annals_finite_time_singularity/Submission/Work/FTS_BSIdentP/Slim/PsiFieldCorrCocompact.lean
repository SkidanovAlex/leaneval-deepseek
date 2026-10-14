import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS_BSIdentP.Slim.Dev10
import Submission.Work.FTS_BSIdentP.Slim.Dev11
import Submission.Work.FTS_BSIdentP.Slim.Dev5
import Submission.Work.FTS_BSIdentP.Slim.Dev7
import Submission.Work.FTS_BSIdentP.Slim.Dev8
import Submission.Work.FTS_BSIdentP.Slim.Dev9
import Submission.Work.FTS_BSIdentP.Slim.DevStub
import Submission.Work.FTS_BSIdentP.Slim.MerPsiDecay
import Submission.Work.FTS_BSIdentP.Slim.MerPsiOriginAux
import Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.ContinuousAxisLevel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Filter Set
open scoped Topology

open Work.FTS.BSIdent

theorem continuous_axisLevel {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    Continuous (Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ (Physical.clockInv C t)) := by
  set τ := Physical.clockInv C t with hτ
  have hp : 0 < Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  -- `z ↦ ρ(0,z) = √(z²)` is continuous
  have hρ : Continuous (fun z : ℝ => Work.Cyl.rhoP 0 z) := by
    have hfun : (fun z : ℝ => Work.Cyl.rhoP 0 z) = fun z : ℝ => Real.sqrt (z ^ 2) := by
      funext z; simp [Work.Cyl.rhoP]
    rw [hfun]
    exact Real.continuous_sqrt.comp (continuous_id.pow 2)
  -- hence so is the weight `z ↦ ρ(0,z)^{3α}/B(τ)`
  have hψ : Continuous (fun z : ℝ => Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) := by
    have h1 : Continuous (fun z : ℝ => Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (Real.continuousAt_rpow_const (Work.Cyl.rhoP 0 z) (Work.FTS.Regularity.pExp α)
        (Or.inr hp.le)).comp hρ.continuousAt
    exact h1.div_const (B τ)
  -- `∂_θΦ(·,π/2)` is continuous at `(w, π/2)` for every `w > 0`
  have hpdZ : ∀ w : ℝ, 0 < w → ContinuousAt (fun p : ℝ × ℝ =>
      deriv (fun θ' : ℝ => Φ p.1 θ' τ) p.2) (w, Real.pi / 2) := by
    intro w hw
    have hG := Work.FTS.BSIdentP.Dev2.continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw
      Work.FTS.BSIdentP.Dev2.abs_pi_div_two_lt
    simpa only [Work.Cyl.pdZ] using hG
  -- ## the slice derivative is continuous at every `z ≠ 0`
  have hg_ne : ∀ z : ℝ, z ≠ 0 → ContinuousAt (fun z : ℝ =>
      deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
        (Real.pi / 2)) z := by
    intro z hz
    have hw : 0 < Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos (Work.FTS.BSIdentP.Dev8.rhoP_zero_pos hz) _) hB
    have hinner : ContinuousAt (fun z : ℝ =>
        (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ, Real.pi / 2)) z :=
      hψ.continuousAt.prodMk continuousAt_const
    exact (hpdZ _ hw).tendsto.comp hinner
  -- ## the slice derivative is bounded on the punctured line
  have hbd : ∀ z : ℝ, z ≠ 0 →
      |deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
        (Real.pi / 2)| ≤ C₀ := by
    intro z hz
    set w : ℝ := Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ with hwdef
    have hw : 0 < w :=
      div_pos (Real.rpow_pos_of_pos (Work.FTS.BSIdentP.Dev8.rhoP_zero_pos hz) _) hB
    have hcont' : ContinuousAt (fun θ : ℝ => deriv (fun θ' : ℝ => Φ w θ' τ) θ)
        (Real.pi / 2) :=
      (hpdZ w hw).comp (continuousAt_const.prodMk continuousAt_id)
    have hlim : Tendsto (fun θ : ℝ => |deriv (fun θ' : ℝ => Φ w θ' τ) θ|)
        (𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2))
        (𝓝 |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)|) :=
      (hcont'.tendsto.mono_left nhdsWithin_le_nhds).abs
    have hbound : |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)| ≤ C₀ := by
      refine le_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin (s := Set.Iio (Real.pi / 2)),
        nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))]
        with θ hθ hθ0
      calc |deriv (fun θ' : ℝ => Φ w θ' τ) θ| ≤ C₀ * (1 + w) ^ (-lam) :=
            (hrate w θ hw.le hθ0.le hθ).2.2
        _ ≤ C₀ := by
            have h1 : (1 + w) ^ (-lam) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
            nlinarith [hC₀.le]
    simpa [hwdef] using hbound
  -- ## continuity of the product
  have hprod : Continuous (fun z : ℝ => -z * (A τ)⁻¹ *
      deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
        (Real.pi / 2)) := by
    rw [continuous_iff_continuousAt]
    intro z
    rcases eq_or_ne z 0 with hz | hz
    · -- at `z = 0` the bounded factor is killed by the factor `z`
      subst hz
      have hval : (-(0 : ℝ) * (A τ)⁻¹ * deriv (fun θ' : ℝ =>
          Φ (Work.Cyl.rhoP 0 0 ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
            (Real.pi / 2)) = 0 := by ring
      rw [ContinuousAt, hval]
      have hbdd : ∀ y : ℝ, ‖deriv (fun θ' : ℝ =>
          Φ (Work.Cyl.rhoP 0 y ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
            (Real.pi / 2)‖ ≤ max C₀ |deriv (fun θ' : ℝ =>
              Φ (Work.Cyl.rhoP 0 0 ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
                (Real.pi / 2)| := by
        intro y
        rcases eq_or_ne y 0 with hy | hy
        · subst hy; exact le_max_right _ _
        · rw [Real.norm_eq_abs]
          exact le_trans (hbd y hy) (le_max_left _ _)
      have h1 : Tendsto (fun y : ℝ => -y * (A τ)⁻¹) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h10 : Tendsto (fun y : ℝ => -y * (A τ)⁻¹) (𝓝 (0 : ℝ))
            (𝓝 (-(0 : ℝ) * (A τ)⁻¹)) :=
          (tendsto_id (α := ℝ)).neg.mul tendsto_const_nhds
        simpa using h10
      have h2 : Tendsto (fun y : ℝ => ‖-y * (A τ)⁻¹‖ *
          max C₀ |deriv (fun θ' : ℝ =>
            Φ (Work.Cyl.rhoP 0 0 ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
              (Real.pi / 2)|) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using h1.norm.mul tendsto_const_nhds
      have h4 : Tendsto (fun y : ℝ => ‖-y * (A τ)⁻¹ * deriv (fun θ' : ℝ =>
          Φ (Work.Cyl.rhoP 0 y ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
            (Real.pi / 2)‖) (𝓝 (0 : ℝ)) (𝓝 0) := by
        refine squeeze_zero
          (f := fun y : ℝ => ‖-y * (A τ)⁻¹ * deriv (fun θ' : ℝ =>
            Φ (Work.Cyl.rhoP 0 y ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
              (Real.pi / 2)‖)
          (g := fun y : ℝ => ‖-y * (A τ)⁻¹‖ * max C₀ |deriv (fun θ' : ℝ =>
            Φ (Work.Cyl.rhoP 0 0 ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
              (Real.pi / 2)|)
          (fun y => norm_nonneg _) (fun y => ?_) h2
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbdd y) (norm_nonneg _)
      exact tendsto_zero_iff_norm_tendsto_zero.mpr h4
    · exact (continuousAt_id.neg.mul continuousAt_const).mul (hg_ne z hz)
  exact hprod

end Work.FTS.BSIdentP.Levels
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.Dev13 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev13

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)
open Work.FTS.BSIdentP.Dev8 (rhoP_zero_pos)

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
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
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
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
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
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀))
      (𝓝 (Dev12.axisLevel α A B Φ τ z₀)) := by
  have hw₀pos : 0 < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (rhoP_zero_pos hz₀) _) hB
  have hw₀1 : (0:ℝ) < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ := by linarith
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
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) (hB : 0 < B τ) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0) := by
  have hw₀pos : 0 < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (rhoP_zero_pos hz₀) _) hB
  have hw₀1 : (0:ℝ) < Work.Cyl.rhoP 0 z₀ ^ Work.FTS.Regularity.pExp α / B τ := by linarith
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

end Work.FTS.BSIdentP.Dev13
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.Dev14 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev14

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

/-- The value of the `θ`-derivative of `GG` at `θ = 0`. -/
theorem pdZ_GG_zero_eq {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    Work.Cyl.pdZ (GG Φ τ) w₀ 0 = Work.Cyl.pdZ (fun w θ => Φ w θ τ) w₀ 0 := by
  have hθ0 : |(0:ℝ)| < Real.pi / 2 + 1 := by rw [abs_zero]; linarith [Real.pi_pos]
  have hC2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w₀, 0) :=
    Dev2.contDiffAt_Phi (τ := τ) (Φ := Φ) hsm (by linarith) hθ0
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => Φ w₀ θ' τ) 0 :=
    Work.Cyl.differentiableAt_slice_snd (fun w θ => Φ w θ τ) w₀ 0
      (hC2.differentiableAt (by norm_num))
  have hderiv : HasDerivAt (fun θ' : ℝ => Φ w₀ θ' τ)
      (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0) 0 := hd.hasDerivAt
  have hΦ0 : Φ w₀ 0 τ = 0 := h0 w₀ hw₀
  have hGG0 : GG Φ τ w₀ 0 = 0 := by
    rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl, hΦ0]
  have hslopeΦ : Tendsto (slope (fun θ' : ℝ => Φ w₀ θ' τ) 0) (𝓝[≠] (0:ℝ))
      (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := hderiv.tendsto_slope
  have hGGfun : (fun θ' : ℝ => GG Φ τ w₀ θ') = GG Φ τ w₀ := rfl
  have hslopeGG : Tendsto (slope (fun θ' : ℝ => GG Φ τ w₀ θ') 0) (𝓝[≠] (0:ℝ))
      (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := by
    have hslopeΦpos : Tendsto (slope (fun θ' : ℝ => Φ w₀ θ' τ) 0) (𝓝[>] (0:ℝ))
        (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) :=
      hslopeΦ.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
    have hpos : Tendsto (slope (fun θ' : ℝ => GG Φ τ w₀ θ') 0) (𝓝[>] (0:ℝ))
        (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := by
      refine hslopeΦpos.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [slope_fun_def, vsub_eq_sub, hGG0, hΦ0, sub_zero]
      rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) (le_of_lt hh)]
    have hrefl : Tendsto (fun h : ℝ => slope (fun θ' : ℝ => Φ w₀ θ' τ) 0 (-h)) (𝓝[<] (0:ℝ))
        (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := by
      have hmap : Tendsto (fun h : ℝ => -h) (𝓝[<] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hcont : ContinuousAt (fun h : ℝ => -h) 0 := continuous_neg.continuousAt
          have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (0:ℝ)))
          simpa using this
        · filter_upwards [self_mem_nhdsWithin] with h hh
          exact neg_pos.mpr (by simpa using hh)
      have hcomp := hslopeΦpos.comp hmap
      simpa [Function.comp_def] using hcomp
    have hneg : Tendsto (slope (fun θ' : ℝ => GG Φ τ w₀ θ') 0) (𝓝[<] (0:ℝ))
        (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := by
      refine hrefl.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hne : h ≠ 0 := ne_of_lt hh
      simp only [slope_fun_def, vsub_eq_sub, hGG0, hΦ0, sub_zero]
      rw [Dev5.GG_of_neg (Φ := Φ) (τ := τ) hh]
      field_simp
      simp only [neg_smul, smul_neg]
    have hset : (({0} : Set ℝ))ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi,
        Set.mem_Iio]
      constructor
      · intro hx
        rcases lt_or_gt_of_ne hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact ne_of_gt h
        · exact ne_of_lt h
    have hsplit : 𝓝[≠] (0:ℝ) = 𝓝[>] (0:ℝ) ⊔ 𝓝[<] (0:ℝ) := by
      show 𝓝[(({0} : Set ℝ))ᶜ] (0:ℝ) = 𝓝[>] (0:ℝ) ⊔ 𝓝[<] (0:ℝ)
      rw [hset, nhdsWithin_union]
    rw [hsplit]
    exact tendsto_sup.mpr ⟨hpos, hneg⟩
  have hfin : HasDerivAt (fun θ' : ℝ => GG Φ τ w₀ θ')
      (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0) 0 := hasDerivAt_iff_tendsto_slope.mpr hslopeGG
  show deriv (fun θ' : ℝ => GG Φ τ w₀ θ') 0 = deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0
  exact hfin.deriv

end Work.FTS.BSIdentP.Dev14
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.MerPsiOriginAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliaries for the vanishing of `ψ`, `∂_zψ`, `∂_rψ` at the origin

Part 2: the pointwise bounds for `∂_zψ` and `∂_rψ` on the whole half-plane `r > 0` (chain rule
on the open quadrant via `_dev6`, the values on `z = 0` via `_dev5`/`_dev11`, and the reduction
of `z < 0` to `z > 0` by oddness in `z`).  Consumed by
`Work.FTS.BSIdentP.Levels.merPsiT_origin_profiles`.
-/

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

set_option maxHeartbeats 2000000

/-- On `z > 0` the chain rule of `_dev6` writes `∂_zψ` and `∂_rψ` as combinations whose
coefficients are `O(ρ)` and whose profile factors are bounded by the rate hypothesis. -/
theorem abs_pdZ_pdR_merPsiT_le_of_pos {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hB : 0 < B (Physical.clockInv C t)) (hp : 0 ≤ Work.FTS.Regularity.pExp α)
    {C₀ lam : ℝ} (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (hval : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    (hwd : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1))
    (hth : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ|
        ≤ C₀ * (1 + w) ^ (-lam)) :
    ∀ r z : ℝ, 0 < r → 0 < z →
      |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1)
            * Work.Cyl.rhoP r z ∧
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1)
            * Work.Cyl.rhoP r z := by
  intro r z hr hz
  have hθpos : 0 < Work.Cyl.thetaP r z := Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hz
  have hθlt : Work.Cyl.thetaP r z < Real.pi / 2 := Work.FTS.BSIdent.Cyl.thetaP_lt_pi_div_two r z
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ Work.Cyl.rhoP r z := hρpos.le
  have hwpos : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
      / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos hρpos _) hB
  have hwnn : 0 ≤ Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
      / B (Physical.clockInv C t) := hwpos.le
  have hGv : |Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
            / B (Physical.clockInv C t)) ^ (-lam) := by
    rw [Work.FTS.BSIdentP.Dev5.GG_of_nonneg hθpos.le]
    exact hval _ _ hwpos.le hθpos.le hθlt
  have hGw : |Work.Cyl.pdR (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
            / B (Physical.clockInv C t)) ^ (-lam - 1) := by
    have hrew : Work.Cyl.pdR (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)
        = deriv (fun w' : ℝ => Φ w' (Work.Cyl.thetaP r z) (Physical.clockInv C t))
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t)) :=
      Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall
        (fun w' => Work.FTS.BSIdentP.Dev5.GG_of_nonneg (Φ := Φ)
          (τ := Physical.clockInv C t) hθpos.le))
    rw [hrew]
    exact hwd _ _ hwpos.le hθpos.le hθlt
  have hGt : |Work.Cyl.pdZ (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)|
      ≤ C₀ * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
          / B (Physical.clockInv C t)) ^ (-lam) := by
    have hrew : Work.Cyl.pdZ (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)
        = deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
            / B (Physical.clockInv C t)) θ' (Physical.clockInv C t)) (Work.Cyl.thetaP r z) := by
      rw [show Work.Cyl.pdZ (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
          (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
          (Work.Cyl.thetaP r z)
          = deriv (fun θ' : ℝ => Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t)
              (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
                / B (Physical.clockInv C t)) θ') (Work.Cyl.thetaP r z) from rfl]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hθpos] with θ' hθ'
      exact Work.FTS.BSIdentP.Dev5.GG_of_nonneg (Φ := Φ)
        (τ := Physical.clockInv C t) hθ'.le
    rw [hrew]
    exact hth _ _ hwpos.le hθpos.le hθlt
  have hZ : |z| ≤ Work.Cyl.rhoP r z := Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z
  have hR : |r| ≤ Work.Cyl.rhoP r z := by
    rw [abs_of_nonneg hr.le]
    exact Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le
  have hZneg : |-z| ≤ Work.Cyl.rhoP r z := by rwa [abs_neg]
  constructor
  · rw [Work.FTS.BSIdentP.Dev6.pdZ_merPsiT_eq (τ := Physical.clockInv C t) (α := α)
      (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hsm hB hr (ne_of_gt hz)]
    exact abs_chain_le (c := (A (Physical.clockInv C t))⁻¹)
      (p := Work.FTS.Regularity.pExp α) (C₀ := C₀) (lam := lam)
      (ρ := Work.Cyl.rhoP r z) (θ := Work.Cyl.thetaP r z)
      (w := Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
      (Z := z) (R := r)
      (Gv := Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      (Gw := Work.Cyl.pdR (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      (Gt := Work.Cyl.pdZ (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      hC₀ hlam hp hθpos.le hρnn hwnn hZ hR hGv hGw hGt
  · rw [Work.FTS.BSIdentP.Dev6.pdR_merPsiT_eq (τ := Physical.clockInv C t) (α := α)
      (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hsm hB hr (ne_of_gt hz)]
    exact abs_chain_le (c := (A (Physical.clockInv C t))⁻¹)
      (p := Work.FTS.Regularity.pExp α) (C₀ := C₀) (lam := lam)
      (ρ := Work.Cyl.rhoP r z) (θ := Work.Cyl.thetaP r z)
      (w := Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
      (Z := r) (R := -z)
      (Gv := Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      (Gw := Work.Cyl.pdR (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      (Gt := Work.Cyl.pdZ (Work.FTS.BSIdentP.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      hC₀ hlam hp hθpos.le hρnn hwnn hR hZneg hGv hGw hGt

/-- The two partials are odd/even in the axial variable, because `ψ` is odd. -/
theorem pdZ_merPsiT_odd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {r z : ℝ} (hr : 0 < r) :
    Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r (-z)
      = Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z :=
  (Work.FTS.BSIdent.Cyl.deriv_odd_eq (f := fun z' : ℝ =>
      Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z')
    (fun y => Work.FTS.BSIdent.Cyl.merPsiT_odd_z hB h0 (r := r) (z := y) hr) z).symm

theorem pdR_merPsiT_odd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {r z : ℝ} (hr : 0 < r) :
    Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r (-z)
      = -Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z := by
  have hev : (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' (-z))
      =ᶠ[𝓝 r] (fun r' : ℝ => -Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with r' hr'
    exact Work.FTS.BSIdent.Cyl.merPsiT_odd_z hB h0 (r := r') (z := z) hr'
  show deriv (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' (-z)) r = _
  rw [Filter.EventuallyEq.deriv_eq hev]
  exact Work.FTS.BSIdent.Cyl.deriv_neg_fun (g := fun r' : ℝ =>
    Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' z) r

/-- `|∂_zψ(r,z)| ≤ K ρ(r,z)` for all `r > 0`, all `z`. -/
theorem abs_pdZ_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hp : 0 ≤ Work.FTS.Regularity.pExp α)
    {C₀ lam : ℝ} (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (hval : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    (hwd : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1))
    (hth : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ|
        ≤ C₀ * (1 + w) ^ (-lam)) :
    ∀ r z : ℝ, 0 < r →
      |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1)
            * Work.Cyl.rhoP r z := by
  intro r z hr
  rcases lt_trichotomy z 0 with hlt | heq | hgt
  · have hpos := abs_pdZ_pdR_merPsiT_le_of_pos (α := α) (A := A) (B := B) (Φ := Φ) (C := C)
      (t := t) hsm hB hp hlam hC₀ hval hwd hth r (-z) hr (by linarith)
    rw [Work.Cyl.rhoP_neg] at hpos
    rw [← pdZ_merPsiT_odd (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
      (z := z) hB h0 hr]
    exact hpos.1
  · subst heq
    rw [Work.FTS.BSIdentP.Dev11.pdZ_merPsiT_zero_snd (τ := Physical.clockInv C t)
      (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hsm h0 hB hr]
    have hw1 : 0 < r ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) :=
      div_pos (Real.rpow_pos_of_pos hr _) hB
    have hd : |deriv (fun θ' : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α
        / B (Physical.clockInv C t)) θ' (Physical.clockInv C t)) 0| ≤ C₀ := by
      refine (hth (r ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t)) 0
        hw1.le le_rfl (by linarith [Real.pi_pos])).trans ?_
      have hp1 : (1 + r ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t)) ^ (-lam) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      calc C₀ * (1 + r ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t)) ^ (-lam)
          ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hp1 hC₀
        _ = C₀ := by ring
    rw [abs_mul, abs_mul, abs_of_nonneg hr.le, Work.FTS.BSIdentP.Dev11.rhoP_zero_snd hr]
    have h2 : 0 ≤ Work.FTS.Regularity.pExp α * (Real.pi / 2) :=
      mul_nonneg hp (by linarith [Real.pi_pos])
    have hK : |(A (Physical.clockInv C t))⁻¹| * C₀
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1) := by
      have h1 : (1:ℝ) ≤ 2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1 := by
        linarith [Real.pi_pos, h2]
      calc |(A (Physical.clockInv C t))⁻¹| * C₀
          = |(A (Physical.clockInv C t))⁻¹| * C₀ * 1 := by ring
        _ ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
              * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    calc |(A (Physical.clockInv C t))⁻¹| * r
          * |deriv (fun θ' : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α
              / B (Physical.clockInv C t)) θ' (Physical.clockInv C t)) 0|
        ≤ |(A (Physical.clockInv C t))⁻¹| * r * C₀ :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = |(A (Physical.clockInv C t))⁻¹| * C₀ * r := by ring
      _ ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1) * r :=
          mul_le_mul_of_nonneg_right hK hr.le
  · exact (abs_pdZ_pdR_merPsiT_le_of_pos (α := α) (A := A) (B := B) (Φ := Φ) (C := C)
      (t := t) hsm hB hp hlam hC₀ hval hwd hth r z hr hgt).1

/-- `|∂_rψ(r,z)| ≤ K ρ(r,z)` for all `r > 0`, all `z`. -/
theorem abs_pdR_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hp : 0 ≤ Work.FTS.Regularity.pExp α)
    {C₀ lam : ℝ} (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (hval : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    (hwd : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1))
    (hth : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ|
        ≤ C₀ * (1 + w) ^ (-lam)) :
    ∀ r z : ℝ, 0 < r →
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1)
            * Work.Cyl.rhoP r z := by
  intro r z hr
  rcases lt_trichotomy z 0 with hlt | heq | hgt
  · have hpos := abs_pdZ_pdR_merPsiT_le_of_pos (α := α) (A := A) (B := B) (Φ := Φ) (C := C)
      (t := t) hsm hB hp hlam hC₀ hval hwd hth r (-z) hr (by linarith)
    rw [Work.Cyl.rhoP_neg] at hpos
    rw [pdR_merPsiT_odd (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
      (z := z) hB h0 hr, abs_neg] at hpos
    exact hpos.2
  · subst heq
    rw [Work.FTS.BSIdentP.Dev5.pdR_merPsiT_zero_snd (τ := Physical.clockInv C t)
      (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hB h0 hr]
    have h2 : 0 ≤ Work.FTS.Regularity.pExp α * (Real.pi / 2) :=
      mul_nonneg hp (by linarith [Real.pi_pos])
    have hKnn : 0 ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
        * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1) := by
      have h3 : (0:ℝ) < 2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1 := by
        linarith [Real.pi_pos, h2]
      positivity
    rw [abs_zero]
    exact mul_nonneg hKnn (Work.Cyl.rhoP_nonneg r 0)
  · exact (abs_pdZ_pdR_merPsiT_le_of_pos (α := α) (A := A) (B := B) (Φ := Φ) (C := C)
      (t := t) hsm hB hp hlam hC₀ hval hwd hth r z hr hgt).2

end Work.FTS.BSIdentP.Levels
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.PsiFieldCorrCocompact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The corrected stream-function field of the ansatz decays at infinity

`Work.FTS.BSIdent.psiFieldCorr ψ L` is the globally defined replacement of the Lean field
`Cyl.psiField ψ` (which is discontinuous at the axis): on the axis `r = 0` it takes the value
`-(2 L z) • e_z`, off the axis it is `Cyl.psiField ψ`.  For the concrete meridian stream
function `ψ = merPsiT α A B Φ C t` and the axis level
`L = Dev12.axisLevel α A B Φ (clockInv C t) = -z A(τ)⁻¹ ∂_θΦ(ρ(0,z)^{3α}/B(τ), π/2)`,
this file proves the decay clause of the corrected bundle
(`Weyl.merPsi_corrected_bundle`): `psiFieldCorr ψ L x → 0` as `x → ∞`.

The pointwise bound is `‖psiFieldCorr ψ L x‖ ≤ K / (1 + ‖x‖)`, obtained by combining

* the sharp decay bounds for `ψ/r`, `∂_zψ`, `∂_rψ` off the plane `z = 0`
  (`Levels.merPsiT_decay_bounds_ne`, which uses the *first* power of `π/2 - θ` in the rate and
  only `2 ≤ 3αλ`);
* the values `ψ = 0`, `∂_rψ = 0`, `∂_zψ = (A τ)⁻¹ r ∂_θΦ(r^{3α}/B(τ),0)` on the plane `z = 0`
  (`Dev5.merPsiT_zero_snd`, `Dev5.pdR_merPsiT_zero_snd`, `Dev11.pdZ_merPsiT_zero_snd`),
  bounded by the rate at `θ = 0`;
* the bound `|∂_θΦ(w,π/2)| ≤ C₀ (1+w)^{-λ}` at the endpoint `θ = π/2`, which the rate
  hypothesis only gives for `θ < π/2`; it is obtained by continuity of the slice derivative
  (`Dev2.continuousAt_pdZ_Phi`) and `le_of_tendsto`.  This bounds the axis level `L` by
  `|z| (1 + |z|^{3α}/B)^{-λ} ≤ 2 max 1 (B^λ)/(1+|z|)`, using `2 ≤ 3αλ`
  (`rho_mul_rpow_weight_le_two`).
-/

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

set_option maxHeartbeats 1000000

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {C : Physical.PhysClock} {t : ℝ}

/-- The constant of the pointwise decay bound: `|A(τ)⁻¹| C₀ · 2 max 1 (B(τ)^λ)`. -/
noncomputable def corrDecayC (A B : ℝ → ℝ) (τ C₀ lam : ℝ) : ℝ :=
  |(A τ)⁻¹| * C₀ * (2 * max 1 ((B τ) ^ lam))

theorem corrDecayC_nonneg {A B : ℝ → ℝ} {τ C₀ lam : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ corrDecayC A B τ C₀ lam := by
  rw [corrDecayC]
  have h1 : (0 : ℝ) ≤ max 1 ((B τ) ^ lam) := le_trans zero_le_one (le_max_left _ _)
  exact mul_nonneg (mul_nonneg (abs_nonneg _) hC₀) (by linarith)

/-- **The derivative of the profile at the endpoint `θ = π/2`.**  The rate hypothesis bounds
`∂_θΦ` only for `θ < π/2`; at `θ = π/2` the bound follows by continuity, `∂_θΦ` being the
`θ`-derivative of a `C²` function. -/
theorem pdZ_Phi_pi_div_two_le {Φ : Work.FTS.BSIdent.Fam} {τ C₀ lam w : ℝ}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw : 0 < w)
    (hrate : ∀ θ : ℝ, 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' τ) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)| ≤ C₀ * (1 + w) ^ (-lam) := by
  have hcontP : ContinuousAt (fun p : ℝ × ℝ => deriv (fun z' : ℝ => Φ p.1 z' τ) p.2)
      (w, Real.pi / 2) := by
    have h := Work.FTS.BSIdentP.Dev2.continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm
      (w := w) (θ := Real.pi / 2) (by linarith) Work.FTS.BSIdentP.Dev2.abs_pi_div_two_lt
    simpa only [Work.Cyl.pdZ] using h
  have hcont' : ContinuousAt (fun θ : ℝ => deriv (fun θ' : ℝ => Φ w θ' τ) θ) (Real.pi / 2) :=
    hcontP.comp (continuousAt_const.prodMk continuousAt_id)
  have hlim : Filter.Tendsto (fun θ : ℝ => |deriv (fun θ' : ℝ => Φ w θ' τ) θ|)
      (𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2))
      (𝓝 |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)|) :=
    (hcont'.tendsto.mono_left nhdsWithin_le_nhds).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin (s := Set.Iio (Real.pi / 2)),
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))]
    with θ hθ hθ0
  exact hrate θ hθ0.le hθ

/-- **The axis level decays.**  For every `z`,
`|axisLevel α A B Φ τ z| ≤ |A(τ)⁻¹| C₀ · 2 max 1 (B(τ)^λ) / (1+|z|)`; at `z = 0` the level
vanishes, and for `z ≠ 0` the bound is the weighted rpow bound `rho_mul_rpow_weight_le_two`
applied to `ρ = |z|` together with the endpoint derivative bound. -/
theorem axisLevel_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {τ C₀ lam : ℝ}
    (hB : 0 < B τ) (hC₀ : 0 ≤ C₀) (hp : 0 < Work.FTS.Regularity.pExp α)
    (hlam : 0 < lam) (hpl : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hD : ∀ w : ℝ, 0 < w → |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)|
      ≤ C₀ * (1 + w) ^ (-lam)) (z : ℝ) :
    |Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ τ z|
      ≤ corrDecayC A B τ C₀ lam / (1 + |z|) := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    have h0 : Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ τ 0 = 0 := by
      rw [Work.FTS.BSIdentP.Dev12.axisLevel]; ring
    rw [h0, abs_zero]
    have hc := corrDecayC_nonneg (A := A) (B := B) (τ := τ) (C₀ := C₀) (lam := lam) hC₀
    positivity
  · have hwpos : 0 < Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos (Work.FTS.BSIdentP.Dev8.rhoP_zero_pos hz) _) hB
    have h2 : |deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ)
          θ' τ) (Real.pi / 2)|
        ≤ C₀ * (1 + Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam) :=
      hD _ hwpos
    have h1 : |Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ τ z|
        = |z| * |(A τ)⁻¹| * |deriv (fun θ' : ℝ =>
            Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ) (Real.pi / 2)| := by
      rw [Work.FTS.BSIdentP.Dev12.axisLevel, abs_mul, abs_mul, abs_neg]
    rw [h1]
    rw [Work.FTS.BSIdentP.Dev8.rhoP_zero_eq_abs z] at h2 ⊢
    have h3 : |z| * (1 + |z| ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)
        ≤ 2 * max 1 ((B τ) ^ lam) / (1 + |z|) :=
      Work.FTS.BSIdentP.Levels.rho_mul_rpow_weight_le_two
        (p := Work.FTS.Regularity.pExp α) (lam := lam) (b := B τ) (ρ := |z|)
        hp hlam hB (abs_nonneg z) hpl
    calc |z| * |(A τ)⁻¹| * |deriv (fun θ' : ℝ =>
            Φ (|z| ^ Work.FTS.Regularity.pExp α / B τ) θ' τ) (Real.pi / 2)|
        ≤ |z| * |(A τ)⁻¹| * (C₀ * (1 + |z| ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |(A τ)⁻¹| * C₀ * (|z| * (1 + |z| ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)) := by
          ring
      _ ≤ |(A τ)⁻¹| * C₀ * (2 * max 1 ((B τ) ^ lam) / (1 + |z|)) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (abs_nonneg _) hC₀)
      _ = corrDecayC A B τ C₀ lam / (1 + |z|) := by rw [corrDecayC]; ring

/-- **The values of `ψ`, `∂_zψ`, `∂_rψ` on the plane `θ = 0`.**  `ψ` and `∂_rψ` vanish there,
while `∂_zψ = (A τ)⁻¹ r ∂_θΦ(r^{3α}/B(τ), 0)`, which the rate at `θ = 0` and the weighted rpow
bound control by `corrDecayC/(1+r)`. -/
theorem merPsiT_zero_fst_bounds {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t τ C₀ lam : ℝ}
    (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hB : 0 < B τ)
    (hp : 0 < Work.FTS.Regularity.pExp α) (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (hpl : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate0 : ∀ w : ℝ, 0 < w →
      |deriv (fun θ' : ℝ => Φ w θ' τ) 0| ≤ C₀ * (1 + w) ^ (-lam))
    {r : ℝ} (hr : 0 < r) :
    |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r 0|
        ≤ corrDecayC A B τ C₀ lam / (1 + r) ∧
      Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r 0 = 0 ∧
      Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r 0 = 0 := by
  have hψ := Work.FTS.BSIdentP.Dev5.merPsiT_zero_snd (α := α) (A := A) (B := B) (Φ := Φ)
    (C := C) (t := t) (τ := τ) hτ hB h0 hr
  have hpdR := Work.FTS.BSIdentP.Dev5.pdR_merPsiT_zero_snd (α := α) (A := A) (B := B)
    (Φ := Φ) (C := C) (t := t) (τ := τ) hτ hB h0 hr
  have hpdZ := Work.FTS.BSIdentP.Dev11.pdZ_merPsiT_zero_snd (α := α) (A := A) (B := B)
    (Φ := Φ) (C := C) (t := t) (τ := τ) hτ hsm h0 hB hr
  refine ⟨?_, hψ, hpdR⟩
  rw [hpdZ]
  have hD : |deriv (fun θ : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0|
      ≤ C₀ * (1 + r ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam) :=
    hrate0 _ (div_pos (Real.rpow_pos_of_pos hr _) hB)
  have h3 : r * (1 + r ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)
      ≤ 2 * max 1 ((B τ) ^ lam) / (1 + r) :=
    Work.FTS.BSIdentP.Levels.rho_mul_rpow_weight_le_two
      (p := Work.FTS.Regularity.pExp α) (lam := lam) (b := B τ) (ρ := r) hp hlam hB hr.le hpl
  calc |(A τ)⁻¹ * r * deriv (fun θ : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0|
      = |(A τ)⁻¹| *
          (r * |deriv (fun θ : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0|) := by
        rw [abs_mul, abs_mul, abs_of_pos hr]; ring
    _ ≤ |(A τ)⁻¹| * (r * (C₀ * (1 + r ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hr.le) (abs_nonneg _)
    _ = |(A τ)⁻¹| * C₀ * (r * (1 + r ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)) := by ring
    _ ≤ |(A τ)⁻¹| * C₀ * (2 * max 1 ((B τ) ^ lam) / (1 + r)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (abs_nonneg _) hC₀)
    _ = corrDecayC A B τ C₀ lam / (1 + r) := by rw [corrDecayC]; ring

/-- **The norm of the stream-function field** from the three bounds: off the axis,
`psiField ψ x = (∂_zψ/r) • r e_r - (ψ/r + ∂_rψ) • e_z` in the orthogonal frame
`(radialVec, e_z)`, so `‖psiField ψ x‖ ≤ |∂_zψ| + |ψ|/r + |∂_rψ|`. -/
theorem psiField_norm_le {ψ : ℝ → ℝ → ℝ} {M : ℝ} {x : Work.FTS.BSIdent.R3}
    (hx : Work.Cyl.radial x ≠ 0)
    (h1 : |Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| ≤ M / (1 + ‖x‖))
    (h2 : |ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| / Work.Cyl.radial x ≤ M / (1 + ‖x‖))
    (h3 : |Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| ≤ M / (1 + ‖x‖)) :
    ‖Work.Cyl.psiField ψ x‖ ≤ 3 * M / (1 + ‖x‖) := by
  have hr : 0 < Work.Cyl.radial x := lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hx)
  have hnorm : ‖Work.Cyl.psiField ψ x‖
      ≤ |Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|
        + (|ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| / Work.Cyl.radial x
          + |Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|) := by
    rw [Work.Cyl.psiField, Work.Cyl.cylField]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, Work.FTS.BSIdent.Cyl.norm_radialVec_eq, abs_div,
        abs_of_pos hr]
      exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt hr))
    · rw [norm_smul, Real.norm_eq_abs, Work.FTS.BSIdent.Cyl.norm_eZ_eq, mul_one]
      have hsplit : (-(ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
            - Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x))
          = -((ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
            + Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)) := by ring
      rw [hsplit, abs_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos hr]
  calc ‖Work.Cyl.psiField ψ x‖
      ≤ |Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|
        + (|ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| / Work.Cyl.radial x
          + |Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|) := hnorm
    _ ≤ M / (1 + ‖x‖) + (M / (1 + ‖x‖) + M / (1 + ‖x‖)) := add_le_add h1 (add_le_add h2 h3)
    _ = 3 * M / (1 + ‖x‖) := by ring

theorem psiFieldCorr_cocompact {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => Work.FTS.BSIdent.psiFieldCorr
        (fun r z => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z)
        (Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ (Physical.clockInv C t)) x)
      (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hC₀nn : 0 ≤ C₀ := hC₀.le
  -- the sharp decay bounds off the plane `z = 0`
  obtain ⟨K₁, hK₁nn, hK₁⟩ :=
    merPsiT_decay_bounds_ne hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp hrate
  set cA : ℝ := corrDecayC A B (Physical.clockInv C t) C₀ lam with hcA
  have hcAnn : 0 ≤ cA := by rw [hcA]; exact corrDecayC_nonneg hC₀nn
  set K : ℝ := max (3 * K₁) (3 * cA) with hK
  have hKnn : 0 ≤ K := by rw [hK]; exact le_trans (by linarith) (le_max_left _ _)
  -- the endpoint derivative bound at `θ = π/2`
  have hDpi : ∀ w : ℝ, 0 < w →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) (Real.pi / 2)|
        ≤ C₀ * (1 + w) ^ (-lam) := by
    intro w hw
    exact pdZ_Phi_pi_div_two_le (τ := Physical.clockInv C t) hsm hw
      (fun θ hθ0 hθ1 => (hrate w θ hw.le hθ0 hθ1).2.2)
  -- the rate at `θ = 0`
  have hD0 : ∀ w : ℝ, 0 < w →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) 0| ≤ C₀ * (1 + w) ^ (-lam) :=
    fun w hw => (hrate w 0 hw.le le_rfl (by linarith [Real.pi_pos])).2.2
  -- the pointwise rate bound
  have hpoint : ∀ x : Work.FTS.BSIdent.R3, ‖Work.FTS.BSIdent.psiFieldCorr
        (fun r z => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z)
        (Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ (Physical.clockInv C t)) x‖
      ≤ K / (1 + ‖x‖) := by
    intro x
    by_cases hrad : Work.Cyl.radial x = 0
    · -- on the axis only the level `L (axial x)` survives
      rw [Work.FTS.BSIdent.psiFieldCorr_of_radial_eq hrad]
      have hL := axisLevel_le (α := α) (A := A) (B := B) (Φ := Φ)
        (τ := Physical.clockInv C t) (C₀ := C₀) (lam := lam) hB hC₀nn hp hlam hexp hDpi
        (Work.Cyl.axial x)
      rw [← hcA] at hL
      have hax : |Work.Cyl.axial x| = ‖x‖ := by
        have h01 : x 0 = 0 ∧ x 1 = 0 := (Work.Cyl.radial_eq_zero_iff x).mp hrad
        have hrho : Work.Cyl.rho x = |Work.Cyl.axial x| := by
          rw [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, h01.1, h01.2]
          rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + x 2 ^ 2 = x 2 ^ 2 from by ring,
            Real.sqrt_sq_eq_abs]
        rw [← hrho]
        exact Work.Cyl.rho_eq_norm x
      have hnorm : ‖(-(2 * Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ
            (Physical.clockInv C t) (Work.Cyl.axial x))) • Work.Cyl.eZ‖
          = 2 * |Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ (Physical.clockInv C t)
            (Work.Cyl.axial x)| := by
        rw [norm_smul, Real.norm_eq_abs, Work.FTS.BSIdent.Cyl.norm_eZ_eq, mul_one, abs_neg,
          abs_mul]
        norm_num
      rw [hnorm]
      calc 2 * |Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ (Physical.clockInv C t)
              (Work.Cyl.axial x)|
          ≤ 2 * (cA / (1 + |Work.Cyl.axial x|)) := mul_le_mul_of_nonneg_left hL (by norm_num)
        _ = 2 * cA / (1 + ‖x‖) := by rw [hax]; ring
        _ ≤ K / (1 + ‖x‖) := by
            rw [hK]
            exact div_le_div_of_nonneg_right
              (by linarith [le_max_right (3 * K₁) (3 * cA), hcAnn]) (by positivity)
    · -- off the axis: the three bounds for `∂_zψ`, `ψ/r`, `∂_rψ`
      rw [Work.FTS.BSIdent.psiFieldCorr_of_radial_ne hrad]
      change ‖Work.Cyl.psiField (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) x‖
        ≤ K / (1 + ‖x‖)
      have hr : 0 < Work.Cyl.radial x :=
        lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hrad)
      have hρ : Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = ‖x‖ :=
        (Work.FTS.BSIdent.rhoP_radial_axial x).trans (Work.Cyl.rho_eq_norm x)
      have hd : 0 ≤ 1 + ‖x‖ := by positivity
      have hK3nn : 0 ≤ K / 3 := div_nonneg hKnn (by norm_num)
      rcases eq_or_ne (Work.Cyl.axial x) 0 with hz | hz
      · -- the plane `z = 0`
        obtain ⟨hz1, hz2, hz3⟩ := merPsiT_zero_fst_bounds (α := α) (A := A) (B := B) (Φ := Φ)
          (C := C) (t := t) (τ := Physical.clockInv C t) rfl hsm hzeroPlane
          hB hp hlam hC₀nn hexp hD0 (r := Work.Cyl.radial x) hr
        rw [← hcA] at hz1
        have hρ0 : Work.Cyl.rhoP (Work.Cyl.radial x) 0 = ‖x‖ := by rw [← hz]; exact hρ
        have hrx : Work.Cyl.radial x = ‖x‖ := by
          rw [← Work.FTS.BSIdentP.Dev11.rhoP_zero_snd hr]; exact hρ0
        have hcAk : cA ≤ K / 3 := by rw [hK]; linarith [le_max_right (3 * K₁) (3 * cA)]
        have hA1 : |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t)
              (Work.Cyl.radial x) 0| ≤ K / 3 / (1 + ‖x‖) := by
          have hle : cA / (1 + Work.Cyl.radial x) ≤ K / 3 / (1 + ‖x‖) := by
            rw [hrx]
            exact div_le_div_of_nonneg_right hcAk hd
          exact hz1.trans hle
        have hA2 : |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t (Work.Cyl.radial x) 0|
              / Work.Cyl.radial x ≤ K / 3 / (1 + ‖x‖) := by
          rw [hz2]
          simp only [abs_zero, zero_div]
          exact div_nonneg hK3nn hd
        have hA3 : |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t)
              (Work.Cyl.radial x) 0| ≤ K / 3 / (1 + ‖x‖) := by
          rw [hz3]
          simp only [abs_zero]
          exact div_nonneg hK3nn hd
        refine (psiField_norm_le (M := K / 3) hrad ?_ ?_ ?_).trans (le_of_eq (by ring))
        · rw [hz]; exact hA1
        · rw [hz]; exact hA2
        · rw [hz]; exact hA3
      · -- off the plane `z = 0`
        obtain ⟨hk1, hk2, hk3⟩ := hK₁ (Work.Cyl.radial x) (Work.Cyl.axial x) hr hz
        rw [hρ] at hk1 hk2 hk3
        have hK1k : K₁ ≤ K / 3 := by rw [hK]; linarith [le_max_left (3 * K₁) (3 * cA)]
        refine (psiField_norm_le (M := K / 3) hrad ?_ ?_ ?_).trans (le_of_eq (by ring))
        · exact hk2.trans (div_le_div_of_nonneg_right hK1k hd)
        · exact hk1.trans (div_le_div_of_nonneg_right hK1k hd)
        · exact hk3.trans (div_le_div_of_nonneg_right hK1k hd)
  -- `K/(1+‖x‖) → 0` at cocompact, and squeeze
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h4 : Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => 1 + ‖x‖)
      (Filter.cocompact Work.FTS.BSIdent.R3) Filter.atTop :=
    Filter.tendsto_atTop_mono (f := fun x : Work.FTS.BSIdent.R3 => ‖x‖)
      (fun x => by linarith [norm_nonneg x]) tendsto_norm_cocompact_atTop
  have h5 : Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => K / (1 + ‖x‖))
      (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
    simpa [div_eq_mul_inv] using (h4.inv_tendsto_atTop).const_mul K
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall hpoint) h5

end Work.FTS.BSIdentP.Levels
end
