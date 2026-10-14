import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev10
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev11
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev12
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev7
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev8
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev9
import Submission.Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_aux
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.FireFix.Firing
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.PressureOn.weyl_pair
import Submission.Work.FTS.RegPkgGal.R7d.support_strip
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
-- ===== merged: Submission.Work.FTS.BSIdent.Liouville.Hid =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology Real

namespace Work.FTS.BSIdent

set_option autoImplicit false
set_option linter.unusedVariables false

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Fam} {C : Physical.PhysClock} {g : ℝ → ℝ → ℝ → ℝ} {t : ℝ}


end Work.FTS.BSIdent
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Package =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology Real NNReal

namespace Work.FTS.BSIdent

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **THE IDENTIFICATION `hid` OF `blowupAtTop_of_regPkg'`.**  On `Uax` and for `t ∈ (0,T)` the
reconstructed physical velocity `physVel (−physOmega α A B g C)` is the stream-function field
`psiField (merPsi α A B Φ C · · t)` of the fake-time solution. -/
theorem hid {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Physical.PhysClock} {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.Regularity.RegPkg (α : ℝ) S A B g)
    (hBS : Work.LWP.BiotSavartInverse)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp (α : ℝ))
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp (α : ℝ)) w θ
          + g w θ (Physical.clockInv C t))
    (hΨ : ∀ t ∈ Set.Ioo 0 C.T, ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z))
    (hC1 : ∀ t ∈ Set.Ioo 0 C.T, ContDiff ℝ 1
      (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)))
    (hdec : ∀ t ∈ Set.Ioo 0 C.T, ∃ D : ℝ, ∀ x : R3,
      ‖Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x‖ ≤ D / (1 + ‖x‖)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x := by
  intro t ht x hx
  -- the clock data and the integrability, from `RegPkg` on a strip containing `τ = clockInv C t`
  have htIco : t ∈ Set.Ico (0 : ℝ) C.T := ⟨ht.1.le, ht.2⟩
  have hτnn : 0 ≤ Physical.clockInv C t := Physical.clockInv_nonneg C htIco
  have hτmem : Physical.clockInv C t ∈ Set.Icc (0 : ℝ) (Physical.clockInv C t + 1) :=
    ⟨hτnn, by linarith⟩
  have hP := hreg (Physical.clockInv C t + 1) (by linarith)
  have hA : 0 < A (Physical.clockInv C t) := hP.hA _ hτmem
  have hB : 0 < B (Physical.clockInv C t) := hP.hB _ hτmem
  have hα : 0 < (α : ℝ) := hP.hα
  obtain ⟨hint, -⟩ := Physical.RegPkg.integrable_physVort_slice hP hτmem
  have hsm2 := hΨ t ht
  -- the interior `C²`-regularity of `Φ` is *derived* from the off-axis one of `merPsi`
  have hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ) :=
    fun w θ hw hθ hθ2 => Defs.contDiffAt_Phi_of_merPsi α A B Φ C t hα (ne_of_gt hA) hB hsm2 hw hθ hθ2
  exact hid_of_biotSavartInverse hBS hA hB (hlaw t ht) hsm hsm2 (hC1 t ht)
    (hdec t ht) hint.neg x hx


end Work.FTS.BSIdent
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels._dev13 =====
section

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
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels._dev14 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev14

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdent.Weyl.Dev5 (GG)

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

/-- The value of the `θ`-derivative of `GG` at `θ = 0`. -/
theorem pdZ_GG_zero_eq {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
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

end Work.FTS.BSIdent.Weyl.Dev14
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.weylPairPrinciple =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

/-- The Weyl/Liouville pair lemma, as a named input for route C of the identification.
This is verbatim the statement of `Work.FTS.PressureOn.weyl_pair`, which is proved in that area
(`Submission/Work/FTS/PressureOn/weyl_pair.lean`), so the principle follows by direct
instantiation. -/
theorem weylPairPrinciple : Work.FTS.BSIdent.WeylPairPrinciple :=
  Work.FTS.PressureOn.weyl_pair

end Work.FTS.BSIdent.Weyl
end
