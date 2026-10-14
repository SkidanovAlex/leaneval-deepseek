import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.ClassC.RopGen.sliceSecNonposBochner
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.interpOpenTrace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.RopGen

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-!
# `interpOpenTrace` — the assembly

Target (statement unchanged, see below): `∃ C, 0 < C ∧ InterpOpenTrace C`, i.e. the trace-class
single-function interpolation estimate of Elgindi's §7.

## The route: mollification transfer from the proved strip-class estimate

`InterpOpenTrace C` is proved by transferring the **proved** strip-class estimate
`Work.EllipticEst.Core.i0Aux.interpS_theta` (`= ∃ C, 0 < C ∧ InterpStrip C`) along the
*approximant*

  `Φ := zmoll G δ ε`  (the logarithmic-radial mollification of the doubly-odd-extension angular
                        mollification `thMoll`),

with `δ, ε ∈ (0, 1/2]`.  The datum `G` is recovered by lower semicontinuity (Fatou) on the left,
whereas the right-hand side is dominated:

```
α² ∫ mixIntS G
  ≤ α² (∫ mixIntS Φ + η)                        -- `Trace.mollFatou`   (η > 0 arbitrary)
  ≤ C₀ (α⁴ ∫ ddIntS Φ + ∫ ttIntS Φ + α² ∫ dIntS Φ)   -- `interpS_theta` at Φ (strip class)
  ≤ C₀ K (α⁴ ∫ ddIntS G + ∫ ttIntS G + α² ∫ dIntS G) -- `Trace.mollDom`   (dominations)
```
and `η → 0` gives `InterpOpenTrace (C₀ * K)`.

The two analytic pieces of the transfer are proved in the sibling modules
`Submission/Work/FTS/ClassC/RopGen/Trace/mollDom.lean` (the dominations of the four functionals
of `Φ`, together with the four outer integrabilities) and
`Submission/Work/FTS/ClassC/RopGen/Trace/mollFatou.lean` (the `+η` Fatou step); both are proved
in the `Work.FTS.ClassC.RopGen.Trace` namespace.  This file contains the (short) assembly, and
additionally two 1-D angular lemmas (`pairNonpos`, `sliceBound`) that record the slicewise
Agmon/completing-squares input used by the independent `AgmonIbpCut` route of the chapter.
-/



end

end Work.FTS.ClassC.RopGen

namespace Work.FTS.ClassC.RopGen

/-- **The trace-class single-function interpolation estimate exists.**

Proved by the mollification transfer from the proved strip-class estimate `interpS_theta`:
the strip estimate is applied to the approximant `Φ = zmoll G δ ε` (which is strip-admissible by
the proved `mollAdm`), its right-hand side is dominated by that of the datum (`Trace.mollDom`)
and its left-hand side dominates the datum's up to `η > 0` (`Trace.mollFatou`); `η → 0` closes
the argument. -/
theorem interpOpenTrace : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.PkgK5.K5c.InterpOpenTrace C := by
  obtain ⟨C₀, hC₀, hstrip⟩ := Work.EllipticEst.Core.i0Aux.interpS_theta
  obtain ⟨K, hK, hdom⟩ := Work.FTS.ClassC.RopGen.Trace.mollDom
  refine ⟨C₀ * K, by positivity, ?_⟩
  intro α G hα hα14 hsm h0 hpi htr0 htrpi hdz0 hdzpi hsh hmi hdd htt hd
  have htr : Work.FTS.EllSol.EllPkgAux.TraceClass G :=
    ⟨hsm, h0, hpi, htr0, htrpi, hdz0, hdzpi, hsh⟩
  have hfour : Work.FTS.EllSol.EllPkgAux.FourInts G := ⟨hmi, hdd, htt, hd⟩
  -- the four functionals of the approximant are honest
  have hfin : ∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε →
      MeasureTheory.IntegrableOn
        (fun z : ℝ =>
          Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz :=
    fun δ ε hp => (hdom G htr hfour δ ε hp).2.2.2.1
  have hfat := Work.FTS.ClassC.RopGen.Trace.mollFatou G htr hfour hfin
  set R : ℝ := α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
    + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
    + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z) with hR
  have key : ∀ η : ℝ, 0 < η →
      α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ C₀ * K * R + α ^ 2 * η := by
    intro η hη
    obtain ⟨δ, ε, hp, hle⟩ := hfat η hη
    obtain ⟨hd1, ht1, hz1, hmΦ, hdΦ, htΦ, hzΦ⟩ := hdom G htr hfour δ ε hp
    obtain ⟨hsmΦ, hv0, hvπ⟩ := Work.FTS.EllSol.EllPkgAux.mollAdm G htr hfour δ ε hp
    have hstripΦ := hstrip α (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) hα hα14 hsmΦ hv0 hvπ
      hmΦ hdΦ htΦ hzΦ
    have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
    have hα4 : 0 ≤ α ^ 4 := by positivity
    have hC0 : 0 ≤ C₀ := le_of_lt hC₀
    set M := ∫ z in Work.Spaces.Iz,
      Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z with hM
    have e1 : α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ α ^ 2 * (M + η) := by
      rw [hM]
      exact mul_le_mul_of_nonneg_left hle hα2
    have e2 : α ^ 2 * (M + η) = α ^ 2 * M + α ^ 2 * η := by ring
    have e3 : α ^ 2 * M ≤ C₀ * (α ^ 4 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.ddIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        + (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.ttIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        + α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.dIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)) := by
      rw [hM]; exact hstripΦ
    have e4 : C₀ * (α ^ 4 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.ddIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        + (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.ttIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        + α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.dIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z))
        ≤ C₀ * (α ^ 4 * (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
            + (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
            + α ^ 2 * (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z)) := by
      refine mul_le_mul_of_nonneg_left ?_ hC0
      refine add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul_of_nonneg_left hd1 hα4
      · exact ht1
      · exact mul_le_mul_of_nonneg_left hz1 hα2
    have e5 : C₀ * (α ^ 4 * (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))
        = C₀ * K * R := by
      rw [hR]; ring
    have h3 : α ^ 2 * M ≤ C₀ * K * R := le_trans e3 (le_trans e4 (le_of_eq e5))
    calc α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ α ^ 2 * (M + η) := e1
      _ = α ^ 2 * M + α ^ 2 * η := e2
      _ ≤ C₀ * K * R + α ^ 2 * η := by linarith [h3]
  have hfinal : α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C₀ * K * R := by
    by_contra hcon
    push_neg at hcon
    have hα2pos : 0 < α ^ 2 := by positivity
    have hpos : 0 < (α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        - C₀ * K * R) / (2 * α ^ 2) := by positivity
    have hk := key _ hpos
    have hsplit : α ^ 2 * ((α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        - C₀ * K * R) / (2 * α ^ 2))
        = (α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
          - C₀ * K * R) / 2 := by
      field_simp
    rw [hsplit] at hk
    linarith [hk]
  have hRK : C₀ * K * R = C₀ * K * (α ^ 4 * (∫ z in Work.Spaces.Iz,
        Work.EllipticEst.Core.ddIntS G z)
      + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
      + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z)) := by rw [hR]
  rw [hRK] at hfinal
  exact hfinal

end Work.FTS.ClassC.RopGen
end
-- ===== merged: Submission.Work.FTS.OpenPkg.AprioriOpen.Fields =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false
set_option maxHeartbeats 1000000






end Work.FTS.OpenPkg.AprioriOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.abs_Jeps_sub_Jeps_le_of_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

/-- **`J_ε` of a difference is the integral of the kernel against the difference.**  On the open
quadrant the two mollified values may be written as the log-coordinate convolutions of `X` resp.
`Y` against `Jker ρ ε` (`Jeps_eq_integral`); the kernel has compact support and both shifted
profiles are continuous (the shift stays in the open quadrant, where `X` and `Y` are continuous),
so both products are integrable and `integral_sub` splits the difference. -/
theorem Jeps_sub_Jeps_eq_integral {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {X Y : ℝ → ℝ → ℝ} {ε z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hε : 0 < ε)
    (hXc : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Work.FTS.StrongEps.Quad)
    (hYc : ContinuousOn (fun q : ℝ × ℝ => Y q.1 q.2) Work.FTS.StrongEps.Quad) :
    Work.FTS.StrongEps.Jeps ρ ε X z θ - Work.FTS.StrongEps.Jeps ρ ε Y z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (X (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            - Y (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  -- the shifted point stays in the open quadrant, whatever the shift `p`
  have hmem : ∀ p : ℝ × ℝ,
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)
        ∈ Work.FTS.StrongEps.Quad :=
    fun _ => ⟨Work.FTS.StrongEps.zShift_pos hz, Work.FTS.StrongEps.thShift_mem hθ⟩
  -- hence the shifted profiles are continuous on all of `ℝ²`
  have hcontX : Continuous fun p : ℝ × ℝ =>
      X (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    simpa only [Function.comp_def] using
      hXc.comp_continuous (Work.FTS.StrongEps.continuous_shift_pair z θ) hmem
  have hcontY : Continuous fun p : ℝ × ℝ =>
      Y (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    simpa only [Function.comp_def] using
      hYc.comp_continuous (Work.FTS.StrongEps.continuous_shift_pair z θ) hmem
  -- the products with the (compactly supported) kernel are integrable
  have hXint : Integrable fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p
        * X (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) :=
    ((Work.FTS.StrongEps.Jker_continuous hρ ε).mul hcontX).integrable_of_hasCompactSupport
      (Work.FTS.StrongEps.Jker_hasCompactSupport hρ hε).mul_right
  have hYint : Integrable fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p
        * Y (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) :=
    ((Work.FTS.StrongEps.Jker_continuous hρ ε).mul hcontY).integrable_of_hasCompactSupport
      (Work.FTS.StrongEps.Jker_hasCompactSupport hρ hε).mul_right
  rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε X hz hθ,
    Work.FTS.StrongEps.Jeps_eq_integral ρ ε Y hz hθ, ← integral_sub hXint hYint]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

theorem abs_Jeps_sub_Jeps_le_of_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {X Y : ℝ → ℝ → ℝ} {ε z θ η : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hε : 0 < ε)
    (hXc : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Work.FTS.StrongEps.Quad)
    (hYc : ContinuousOn (fun q : ℝ × ℝ => Y q.1 q.2) Work.FTS.StrongEps.Quad)
    (hη : ∀ q : ℝ × ℝ, ‖q‖ ≤ ε →
      |X (Work.FTS.StrongEps.zShift z q.1) (Work.FTS.StrongEps.thShift θ q.2)
        - Y (Work.FTS.StrongEps.zShift z q.1) (Work.FTS.StrongEps.thShift θ q.2)| ≤ η) :
    |Work.FTS.StrongEps.Jeps ρ ε X z θ - Work.FTS.StrongEps.Jeps ρ ε Y z θ| ≤ η := by
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := fun p => by
    simp only [Work.FTS.StrongEps.Jker]
    exact mul_nonneg (by positivity) (hρ.nonneg _)
  -- the difference is the integral of the kernel against the pointwise difference
  rw [Jeps_sub_Jeps_eq_integral hρ hz hθ hε hXc hYc]
  -- the pointwise difference is `≤ η` on the support of the kernel and the kernel vanishes off it
  have hpt : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖Work.FTS.StrongEps.Jker ρ ε p
        * (X (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          - Y (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))‖
        ≤ Work.FTS.StrongEps.Jker ρ ε p * η := by
    refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · have hpe : ‖p‖ ≤ ε := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hp
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
      exact mul_le_mul_of_nonneg_left (hη p hpe) (hJnn p)
    · rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul, norm_zero, zero_mul]
  -- the mass-one kernel turns the pointwise bound into the integral bound
  have hmain := norm_integral_le_of_norm_le
    ((Work.FTS.StrongEps.Jker_integrable hρ hε).mul_const η) hpt
  rw [integral_mul_const, Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ hε, one_mul,
    Real.norm_eq_abs] at hmain
  exact hmain

end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.BallAtLevel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false




end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OpenLinear =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The linear part of the scheme is minus the frozen operator**: `dynLin α g τ` is the pointwise
negative of `𝓛_Γ^T α (slice g τ)` (definitional, after unfolding `dynLin`). -/
theorem dynLin_eq_neg_LGammaT (α : ℝ) (g : Fam) (τ : ℝ) :
    Work.FTS.Galerkin.dynLin α g τ
      = fun z θ => - Work.Coercivity.LGammaT α (slice g τ) z θ := by
  funext z θ
  simp only [Work.FTS.Galerkin.dynLin]

/-- **The coercivity half of `hneg`, in the open class.**  Identical to `IP_dynLin_le` with
`UnifIPO`/`RegQo` in place of `UnifIP`/`RegQ`; the hypothesis `RegQo α 4 (𝓛_Γ^T x)` is the
open-class regularity of the operator's output (interface item (V′)). -/
theorem IP_dynLin_le_open {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {g : Fam} {τ : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hcoer : CoerAdmO α (slice g τ))
    (hregL : RegQo α 4 (Work.Coercivity.LGammaT α (slice g τ))) :
    IP α (Work.FTS.Galerkin.dynLin α g τ) (slice g τ)
      ≤ - cc * Work.Spaces.HkSq α 4 (slice g τ) := by
  have hregx : RegQo α 4 (slice g τ) := hcoer.regQoFour
  have hsmul := hIP.smul_fst α hα (-1) (Work.Coercivity.LGammaT α (slice g τ)) (slice g τ)
    hregL hregx
  have hfun : (fun z θ => (-1 : ℝ) * Work.Coercivity.LGammaT α (slice g τ) z θ)
      = Work.FTS.Galerkin.dynLin α g τ := by
    rw [dynLin_eq_neg_LGammaT]
    funext z θ
    ring
  rw [hfun] at hsmul
  have hcoer' := hIP.coer α hα (slice g τ) hcoer
  rw [hsmul]
  linarith

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.DefsO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The open-class analogue of `Transfer.LevelPkg`**: the algebraic package `CommSm α n IP`
together with, for every `f ∈ CoerAdmO α`, the two split packages of the transfer identities and
the two Cauchy–Schwarz bounds on the error pairings. -/
def LevelPkgO (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (CC : ℝ) : Prop :=
  Work.FTS.CoercivityFix.Transfer.CommSm α n IP ∧
    (∀ f : Fn, CoerAdmO α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
          (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f) ∧
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
          (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f) ∧
      |IP (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)|
          ≤ CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
              * Work.Spaces.HkNorm α n (Work.Spaces.Dth f) ∧
      |IP (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f)|
          ≤ CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
              * Work.Spaces.HkNorm α n (Work.Spaces.Dz f))

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivWithinAt_Jeps_slice_repair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12Sub4.GlwFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12Sub4

/-! ## Calculus of the log-coordinate angular weight `Glw`

`Glw ζ = κ(ζ) · K (arctan (e^ζ))` with `κ ζ = e^ζ/(1+e^{2ζ})` and `K θ = 3 sin θ cos²θ`.
Writing `θ = arctan (a)`, `a = e^ζ`, so that `sin θ = a/√(1+a²)` and `cos θ = 1/√(1+a²)`
(`Real.sin_arctan`, `Real.cos_arctan`), one gets the closed form

  `Glw ζ = 3 e^{2ζ} / (1 + e^{2ζ})^{5/2} = 3 e^{2ζ} / (√(1 + e^{2ζ}))^5`.

The statements below are the elementary consequences: continuity, positivity, and the
translation bounds used to control the mollifier shift `ζ ↦ ζ + q`. -/

/-- **Closed form of `Glw`**, written with `Real.sqrt` so that no fractional power (`rpow`) is
needed: `Glw ζ = 3 e^{2ζ} / (√(1 + e^{2ζ}))^5`. -/
theorem Glw_eq_sqrt (ζ : ℝ) :
    Glw ζ = 3 * Real.exp (2 * ζ) / (Real.sqrt (1 + Real.exp (2 * ζ))) ^ 5 := by
  have h1 : Real.exp (2 * ζ) = (Real.exp ζ) ^ 2 := by
    have := Real.exp_nat_mul (ζ) 2
    simpa using this
  unfold Glw Work.FTS.StrongEps.HkSqAux.kappa Work.Spaces.K
  rw [Real.sin_arctan, Real.cos_arctan]
  rw [h1]
  set s := Real.sqrt (1 + (Real.exp ζ) ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + (Real.exp ζ) ^ 2 := by
    rw [hsdef]; exact Real.sq_sqrt (by positivity)
  have hs : s ≠ 0 := by positivity
  have h2 : Real.exp ζ ≠ 0 := Real.exp_ne_zero ζ
  field_simp
  ring_nf
  rw [hs2]

theorem continuous_Glw : Continuous Glw := by
  unfold Glw Work.FTS.StrongEps.HkSqAux.kappa Work.Spaces.K
  apply Continuous.mul
  · apply Continuous.div
    · exact Real.continuous_exp
    · fun_prop
    · intro ζ; positivity
  · fun_prop

theorem Glw_pos (ζ : ℝ) : 0 < Glw ζ := by
  rw [Glw_eq_sqrt ζ]
  positivity

/-- The comparison of the two `sqrt`-factors of the closed form of `Glw`: for `t ≥ 1`,
`√(1+x) ≤ √(1+tx)`. -/
private lemma sqrt_one_add_le (x t : ℝ) (hx : 0 < x) (ht : 1 ≤ t) :
    Real.sqrt (1 + x) ≤ Real.sqrt (1 + t * x) := by
  apply Real.sqrt_le_sqrt
  nlinarith [hx, ht]

/-- **Upper bound for the shift with `t ≥ 1`**: `t (√(1+x))^5 ≤ t^4 (√(1+tx))^5`. -/
private lemma Glw_key_ge_one (x t : ℝ) (hx : 0 < x) (ht : 1 ≤ t) :
    t * (Real.sqrt (1 + x)) ^ 5 ≤ t ^ 4 * (Real.sqrt (1 + t * x)) ^ 5 := by
  have h1 : Real.sqrt (1 + x) ≤ Real.sqrt (1 + t * x) := sqrt_one_add_le x t hx ht
  have h2 : t * (Real.sqrt (1 + x)) ^ 5 ≤ t * (Real.sqrt (1 + t * x)) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 5) (by linarith)
  have h3 : t ≤ t ^ 4 := by
    have := pow_le_pow_right₀ ht (by norm_num : (1 : ℕ) ≤ 4)
    simpa using this
  have h4 : t * (Real.sqrt (1 + t * x)) ^ 5 ≤ t ^ 4 * (Real.sqrt (1 + t * x)) ^ 5 :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  linarith

/-- **Upper bound for the shift with `0 < t ≤ 1`**: `t (√(1+x))^5 ≤ (t^4)⁻¹ (√(1+tx))^5`. -/
private lemma Glw_key_le_one (x t : ℝ) (hx : 0 < x) (ht : 0 < t) (ht1 : t ≤ 1) :
    t * (Real.sqrt (1 + x)) ^ 5 ≤ (t ^ 4)⁻¹ * (Real.sqrt (1 + t * x)) ^ 5 := by
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have hsl : t * Real.sqrt (1 + x) ≤ Real.sqrt (1 + t * x) := by
    have h1 : t * Real.sqrt (1 + x) = Real.sqrt (t ^ 2 * (1 + x)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt ht)]
    rw [h1]
    apply Real.sqrt_le_sqrt
    nlinarith [hx, ht2, ht1]
  have hpow : (t * Real.sqrt (1 + x)) ^ 5 ≤ (Real.sqrt (1 + t * x)) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hsl 5
  rw [le_inv_mul_iff₀ (by positivity : (0 : ℝ) < t ^ 4)]
  rw [show t ^ 4 * (t * (Real.sqrt (1 + x)) ^ 5) = (t * Real.sqrt (1 + x)) ^ 5 by
    rw [mul_pow]; ring]
  exact hpow

/-- **Third conjunct of `GlwFacts`**: shifting the log-coordinate by `q` changes the angular
weight by at most a factor `e^{8|q|}`. -/
theorem Glw_shift_le (ζ q : ℝ) : Glw (ζ + q) ≤ Real.exp (8 * |q|) * Glw ζ := by
  rw [Glw_eq_sqrt (ζ + q), Glw_eq_sqrt ζ]
  set x := Real.exp (2 * ζ) with hxdef
  set t := Real.exp (2 * q) with htdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have htpos : 0 < t := by rw [htdef]; positivity
  have hexp : Real.exp (2 * (ζ + q)) = t * x := by
    rw [show (2 : ℝ) * (ζ + q) = 2 * ζ + 2 * q from by ring, Real.exp_add, ← hxdef, ← htdef]
    ring
  rw [hexp]
  have hsqx : 0 < (Real.sqrt (1 + x)) ^ 5 := by positivity
  have hsqt : 0 < (Real.sqrt (1 + t * x)) ^ 5 := by positivity
  by_cases hcase : 1 ≤ t
  · -- `q ≥ 0`: the ratio is at most `t`, and `e^{8q} = t^4`
    have hq0 : 0 ≤ q := by
      have h : 0 ≤ 2 * q := Real.one_le_exp_iff.mp (by rw [← htdef]; exact hcase)
      linarith
    have hE : Real.exp (8 * |q|) = t ^ 4 := by
      rw [abs_of_nonneg hq0]
      rw [show (8 : ℝ) * q = ((4 : ℕ) : ℝ) * (2 * q) from by push_cast; ring,
        Real.exp_nat_mul, ← htdef]
    rw [hE]
    have hkey := Glw_key_ge_one x t hxpos hcase
    rw [show t ^ 4 * (3 * x / (Real.sqrt (1 + x)) ^ 5)
          = (t ^ 4 * 3 * x) / (Real.sqrt (1 + x)) ^ 5 from by ring]
    rw [div_le_div_iff₀ hsqt hsqx]
    rw [show 3 * (t * x) * (Real.sqrt (1 + x)) ^ 5
          = (3 * x) * (t * (Real.sqrt (1 + x)) ^ 5) from by ring,
        show (t ^ 4 * 3 * x) * (Real.sqrt (1 + t * x)) ^ 5
          = (3 * x) * (t ^ 4 * (Real.sqrt (1 + t * x)) ^ 5) from by ring]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  · -- `q < 0`: the ratio is at most `t^{-4}`, and `e^{-8q} = (t^4)⁻¹`
    have ht1 : t < 1 := lt_of_not_ge hcase
    have hq0 : q < 0 := by
      have h : 2 * q < 0 := Real.exp_lt_one_iff.mp (by rw [← htdef]; exact ht1)
      linarith
    have hE : Real.exp (8 * |q|) = (t ^ 4)⁻¹ := by
      rw [abs_of_neg hq0]
      rw [show (8 : ℝ) * -q = -(((4 : ℕ) : ℝ) * (2 * q)) from by push_cast; ring, Real.exp_neg]
      congr 1
      rw [Real.exp_nat_mul, ← htdef]
    rw [hE]
    have hkey := Glw_key_le_one x t hxpos htpos (le_of_lt ht1)
    rw [show (t ^ 4)⁻¹ * (3 * x / (Real.sqrt (1 + x)) ^ 5)
          = ((t ^ 4)⁻¹ * 3 * x) / (Real.sqrt (1 + x)) ^ 5 from by ring]
    rw [div_le_div_iff₀ hsqt hsqx]
    rw [show 3 * (t * x) * (Real.sqrt (1 + x)) ^ 5
          = (3 * x) * (t * (Real.sqrt (1 + x)) ^ 5) from by ring,
        show ((t ^ 4)⁻¹ * 3 * x) * (Real.sqrt (1 + t * x)) ^ 5
          = (3 * x) * ((t ^ 4)⁻¹ * (Real.sqrt (1 + t * x)) ^ 5) from by ring]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Basic calculus of the log-coordinate angular weight
`Glw ζ = κ(ζ) · K(arctan (e^ζ))` (`Work.FTS.StrongEps.L12Sub4.Glw`, `κ = HkSqAux.kappa`).

Hints for the prover: the clean form is `Glw ζ = 3 · e^{2ζ} / (1 + e^{2ζ})^{5/2}` (from
`Real.sin_arctan`, `Real.cos_arctan`, `K θ = 3 sinθ cos²θ` and `κ ζ = sinθ cosθ` for `θ = arctan (e^ζ)`;
equivalently `Glw ζ = 3 sin²θ cos³θ`); with `x = e^{2ζ}` and `t = e^{2q}` the ratio is
`Glw (ζ+q)/Glw ζ = t (1+x)^{5/2}/(1+tx)^{5/2}` which lies between `e^{-8|q|}` and `e^{8|q|}` for
`|q| ≤ 1`, giving the third conjunct with room to spare; the fourth follows from
`|Glw(ζ+q) - Glw ζ| = Glw ζ |R - 1|` with `|R-1| ≤ 8|q|e^8`. -/
theorem GlwFacts :
    Continuous Glw ∧ (∀ ζ : ℝ, 0 < Glw ζ) ∧
      (∀ ζ q : ℝ, Glw (ζ + q) ≤ Real.exp (8 * |q|) * Glw ζ) ∧
      (∀ ζ q : ℝ, |q| ≤ 1 → |Glw (ζ + q) - Glw ζ| ≤ 8 * Real.exp 8 * |q| * Glw ζ) := by
  refine ⟨continuous_Glw, Glw_pos, Glw_shift_le, ?_⟩
  intro ζ q hq
  have hb : 0 < Glw ζ := Glw_pos ζ
  have h1 : Glw (ζ + q) ≤ Real.exp (8 * |q|) * Glw ζ := Glw_shift_le ζ q
  have h2 : Glw ζ ≤ Real.exp (8 * |q|) * Glw (ζ + q) := by
    have h := Glw_shift_le (ζ + q) (-q)
    rwa [show ζ + q + -q = ζ from by ring, abs_neg] at h
  -- the two-sided bound `e^{-8|q|} Glw ζ ≤ Glw (ζ+q) ≤ e^{8|q|} Glw ζ`
  have h3 : Real.exp (-(8 * |q|)) * Glw ζ ≤ Glw (ζ + q) := by
    have h := mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos (-(8 * |q|))))
    have he : Real.exp (-(8 * |q|)) * Real.exp (8 * |q|) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc Real.exp (-(8 * |q|)) * Glw ζ
        ≤ Real.exp (-(8 * |q|)) * (Real.exp (8 * |q|) * Glw (ζ + q)) := h
      _ = Glw (ζ + q) := by rw [← mul_assoc, he, one_mul]
  have hub : Glw (ζ + q) - Glw ζ ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := by
    nlinarith [h1]
  have h4 : 1 - Real.exp (-(8 * |q|)) ≤ Real.exp (8 * |q|) - 1 := by
    have h5 : 1 - Real.exp (-(8 * |q|)) ≤ 8 * |q| := by
      have := Real.add_one_le_exp (-(8 * |q|)); linarith
    have h6 : 8 * |q| ≤ Real.exp (8 * |q|) - 1 := by
      have := Real.add_one_le_exp (8 * |q|); linarith
    linarith
  have hdn : Glw ζ - Glw (ζ + q) ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := by
    calc Glw ζ - Glw (ζ + q) ≤ Glw ζ - Real.exp (-(8 * |q|)) * Glw ζ := by linarith
      _ = Glw ζ * (1 - Real.exp (-(8 * |q|))) := by ring
      _ ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := mul_le_mul_of_nonneg_left h4 (le_of_lt hb)
  have habs : |Glw (ζ + q) - Glw ζ| ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := by
    rw [abs_sub_le_iff]
    exact ⟨hub, hdn⟩
  have hexp : Real.exp (8 * |q|) - 1 ≤ 8 * |q| * Real.exp 8 := by
    have hs0 : (0 : ℝ) ≤ 8 * |q| := by positivity
    have hx1 : Real.exp (8 * |q|) - 1 ≤ 8 * |q| * Real.exp (8 * |q|) := by
      have h5 : 1 - Real.exp (-(8 * |q|)) ≤ 8 * |q| := by
        have := Real.add_one_le_exp (-(8 * |q|)); linarith
      have hm := mul_le_mul_of_nonneg_left h5 (le_of_lt (Real.exp_pos (8 * |q|)))
      have he : Real.exp (8 * |q|) * Real.exp (-(8 * |q|)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [hm, he]
    have hx2 : Real.exp (8 * |q|) ≤ Real.exp 8 :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg q, hq])
    calc Real.exp (8 * |q|) - 1 ≤ 8 * |q| * Real.exp (8 * |q|) := hx1
      _ ≤ 8 * |q| * Real.exp 8 := mul_le_mul_of_nonneg_left hx2 hs0
  calc |Glw (ζ + q) - Glw ζ| ≤ Glw ζ * (Real.exp (8 * |q|) - 1) := habs
    _ ≤ Glw ζ * (8 * |q| * Real.exp 8) := mul_le_mul_of_nonneg_left hexp (le_of_lt hb)
    _ = 8 * Real.exp 8 * |q| * Glw ζ := by ring

end Work.FTS.StrongEps.L12Sub4
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.L12Sub4

/-- **`L₁₂(h)(0)` in log coordinates.**  With `Glw ζ = κ(ζ) K(arctan (e^ζ))` the angular weight of
`L₁₂(·)(0)` in the log coordinate `ζ = log tan θ` (`κ = (arctan ∘ exp)'`, so that
`K(θ) dθ = Glw(ζ) dζ`),

  `L₁₂(h)(0) = ∫_s ∫_ζ Glw ζ · h (e^s) (arctan (e^ζ)) ds dζ`.

This is an **unconditional** identity of Bochner integrals (no integrability hypothesis): each step is
a change of variables which is valid as an identity of Bochner integrals even in the junk cases.

Hints: unfold `L12 = FM.L12 K` (`L12_zero_eq_double`, in `Defs`), replace `Iθ` by `Ioo 0 (π/2)`
(`setIntegral_congr_set` + `MeasureTheory.Ioo_ae_eq_Icc`), pull the factor `1/r` out of the angular
integral (`integral_const_mul`), apply the angular substitution
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` with `f = arctan ∘ exp`, `f' = κ` on
`Set.univ` (whose image is `Ioo 0 (π/2)` by `HkSqAux.range_arctan_exp`), then the radial substitution
with `f = f' = Real.exp` on `Set.univ` (`Real.range_exp`). -/
theorem L12ZeroLog (h : ℝ → ℝ → ℝ) :
    Work.Construction.L12 h 0
      = ∫ s, ∫ ζ, Glw ζ * h (Real.exp s) (Real.arctan (Real.exp ζ)) := by
  rw [L12_zero_eq_double]
  -- Angular substitution `θ = arctan (e^ζ)`: `K(θ) dθ = Glw(ζ) dζ`.
  have angular : ∀ z : ℝ, (∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ)
      = ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)) := by
    intro z
    have hinj : InjOn (fun ζ : ℝ => Real.arctan (Real.exp ζ)) Set.univ := by
      intro a _ b _ hh
      exact Real.exp_injective (Real.arctan_injective hh)
    have hderiv : ∀ ζ ∈ (Set.univ : Set ℝ),
        HasDerivWithinAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) (HkSqAux.kappa ζ)
          Set.univ ζ := by
      intro ζ _
      have hd : HasDerivAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ'))
          (1 / (1 + (Real.exp ζ) ^ 2) * Real.exp ζ) ζ := (Real.hasDerivAt_exp ζ).arctan
      have hκ : (1 / (1 + (Real.exp ζ) ^ 2) * Real.exp ζ) = HkSqAux.kappa ζ := by
        rw [HkSqAux.kappa]
        have h2 : Real.exp (2 * ζ) = (Real.exp ζ) ^ 2 := by rw [two_mul, Real.exp_add, pow_two]
        rw [h2, one_div, div_eq_mul_inv, mul_comm]
      exact (hκ ▸ hd).hasDerivWithinAt
    have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
      (f := fun ζ : ℝ => Real.arctan (Real.exp ζ)) (f' := HkSqAux.kappa)
      MeasurableSet.univ hderiv hinj (fun θ : ℝ => Work.Spaces.K θ * h z θ)
    rw [HkSqAux.range_arctan_exp] at hsub
    rw [setIntegral_univ] at hsub
    rw [hsub]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ζ => ?_))
    simp only []
    rw [abs_of_pos (HkSqAux.kappa_pos ζ), smul_eq_mul, Glw, mul_assoc]
  -- Replace the closed angular interval `Iθ = [0,π/2]` by the open one (null-set difference).
  have step1 : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h z θ / z)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ / z := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    exact setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := π / 2)).symm
  rw [step1]
  -- Pull the factor `1/z` out of the angular integral and substitute `θ = arctan (e^ζ)`.
  have step2 : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ / z)
      = ∫ z in Set.Ioi 0, (1 / z) * ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    calc ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ / z
        = ∫ θ in Set.Ioo 0 (π / 2), (1 / z) * (Work.Spaces.K θ * h z θ) := by
          refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
      _ = (1 / z) * ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.K θ * h z θ := by
          rw [MeasureTheory.integral_const_mul]
      _ = (1 / z) * ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)) := by rw [angular z]
  rw [step2]
  -- Radial substitution `z = e^s`: `dz/z = ds`.
  have step3 : (∫ z in Set.Ioi 0, (1 / z) * ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)))
      = ∫ s, ∫ ζ, Glw ζ * h (Real.exp s) (Real.arctan (Real.exp ζ)) := by
    have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
      (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.exp_injective.injOn)
      (fun z => (1 / z) * ∫ ζ, Glw ζ * h z (Real.arctan (Real.exp ζ)))
    rw [HkSqAux.range_exp] at hsub
    rw [setIntegral_univ] at hsub
    rw [hsub]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    simp only []
    rw [abs_of_pos (Real.exp_pos s), smul_eq_mul, one_div, ← mul_assoc,
      mul_inv_cancel₀ (Real.exp_ne_zero s), one_mul]
  rw [step3]

end Work.FTS.StrongEps.L12Sub4
end
