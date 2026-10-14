import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0Right
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.TT.Shim.FstarIterateIntegrable
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.WDp_le_of_pointwise
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongGlobal.Global
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t2SupF
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The restricted measures of `(0,∞)` and `[0,∞)` agree: they differ by the null point `0`. -/
theorem restrict_Ioi_eq_restrict_Iz :
    MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) = MeasureTheory.volume.restrict Work.Spaces.Iz := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))

/-! ## The `c = 0` piece: the Hardy inequality for `L₁₂ f` -/


/-! ## The integral of the majorant, for one order `j` -/


/-! ## The radial bound for `radA α f` -/


end Work.FTS.CoercivityFix.Transfer.E1Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1_pkg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer


end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeColl.pairChain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeColl


end Work.FTS.EllipticEst.AeColl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The a.e. trace and rate of `z ∂_z u` at the two angular endpoints

This module proves `Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0`: for a datum
`AeData α u G` with

* `hsl` : for a.e. `z > 0` the angular slice `θ ↦ (z ∂_z ∂_θ u(z,θ))² sin(2θ)^{-η}` is
  integrable on `Iθ` (the a.e.-in-`z` clause of the mixed honesty `ℋ⁰`), and
* `hsl2`: the `z`-integral of that slice energy is integrable on `Iz` (the outer clause),

the slice `θ ↦ z ∂_z u(z,θ)` tends to `0` at both endpoints `0⁺` and `(π/2)⁻` for a.e. `z > 0`,
and satisfies the two *marginal* Hardy-type rates
`(z ∂_z u(z,θ))² ≤ 4 · dist^{1+η} · ∫ (z ∂_z ∂_θ u)² σ` against the *truncated* energies.

Note that `Work.Spaces.Dz (Work.Spaces.pth u) z θ = z * ∂_z ∂_θ u(z,θ)` and
`Work.FTS.EllipticEst.sEta θ = sin(2θ)^{-η}` are definitionally the objects of the hypotheses,
so `hsl`/`hsl2` *are* the two clauses of the mixed honesty in `Dz`-form; no Clairaut rewrite is
needed (the two mixed partials agree on the open quadrant anyway, `Spaces.pz_pth_comm`).

The route is the one of `AngAWeak.aeGradTraceLeft` / `aeGradTraceRightMine` (the *global*-honesty
version), with the outer hypothesis `∫_z w² ∫_θ (z ∂_z∂_θ u)² σ < ∞` weakened to
`∫_z ∫_θ (z ∂_z∂_θ u)² σ < ∞`: the only place the weighted form was used was the local
integrability of `√sliceE` on a compact `[a,b] ⊆ (0,∞)` (there via the lower bound
`1 ≤ b⁴ w(s)²`), which the weaker hypothesis supplies directly (Cauchy–Schwarz on the finite
interval).  The two rates are the per-slice estimates `sliceRateTwoLeft` / `sliceRateTwoRight`
applied to the slice (module `GlueRate`), the additive constants being identified with `0` by the
trace vanishing.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AngAWeak

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

theorem aeGradTrace0 (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2
          * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    (hsl2 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2
          * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 < z ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (z * Work.Spaces.pz u z θ)^2 ≤ K * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t)^2
              * (Real.sin (2*t)) ^ (-(Work.Spaces.eta))))
      ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (z * Work.Spaces.pz u z θ)^2 ≤ K * (Real.pi/2 - θ) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo θ (Real.pi / 2), (z * Work.Spaces.pz (Work.Spaces.pth u) z t)^2
              * (Real.sin (2*t)) ^ (-(Work.Spaces.eta)))) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth h)
  -- `hsl`/`hsl2` are the mixed honesty in `Dz`-form, definitionally
  have hGae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ := hsl
  have hE : MeasureTheory.IntegrableOn (sliceE u) Iz := hsl2
  refine ⟨4, by norm_num, ?_⟩
  have htrL := aeGradTraceLeft_of_energy α u G h hGae hE
  have htrR := aeGradTraceRight_of_energy α u G h hGae hE
  filter_upwards [htrL, htrR, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hsl]
    with z hzL hzR hzpos hzsl
  have hintπ : MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) :=
    hzsl.mono_set Set.Ioo_subset_Icc_self
  obtain ⟨hrateL, hrateR⟩ :=
    Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueRate.sliceGradSq_rate_of_trace
      hS hzpos hintπ hzL hzR
  exact ⟨hzpos, hzL, hzR, hrateL, hrateR⟩

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HonGaps.estStepWeak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HonGaps.estStepWeak`: the induction step of Elgindi's `prop:Hk`, in the weak class

## What the lemma says

For every `k ≥ 3`, the level-`0` estimate `TT.EllWeak0` (the paper's `prop:L2` with the
`w² sin^{-η}` weights, i.e. Steps 1--2 of `prop:H2`) together with the level-`(k-1)` estimate
`TT.EllEstUnif (k-1)` for **all** data of the weak class `TT.EllWeakPos` (with a constant that is
uniform in `α ∈ (0,1/4]`) yields the level-`k` estimate `TT.EllEstUnif k`, again with an
`α`-uniform constant: Elgindi's §"General `ℋ^k` Case" (tex 986--1008).

## Where the mathematics lives

The statement of this file is *character for character* the statement of

> `Work.FTS.EllipticEst.TT.est_step_weak` (`Submission/Work/FTS/EllipticEst/TT/est_step_weak.lean`),

which is **fully proved** in this workspace, `sorry`-free, and rests only on
`[propext, Classical.choice, Quot.sound]` (verified with `#print axioms`).  Its proof is the
assembly `TT.ESW.Pieces.EllEstUnif_step_of_pieces` (the exact splitting of `HkSq` at level `k`,
the domination of the shifted level-`(k-1)` expression, the admissibility of the radially
differentiated data `EllWeakPos_DzIter_one_shift`, and the two top angular slots: `A_top_slot_bound`
and `ESW.bSlot_bound`, the latter fed by `Prop.Rtilde.SourceLe` and the one-dimensional far-region
bound `remov.EllUnifBslot.slice_ang_gen_live`).

There is therefore nothing to re-prove: this module simply re-exports that theorem under the
`HonGaps` name, so that consumers of the "honest" (weak-hypothesis) route can obtain the induction
step without naming the `TT` module.  The re-export is *not* a cycle hazard for the current tree:
the import closure of `TT.est_step_weak` (478 modules) contains no `AngAWeak`, no `Prop/Level0`,
no `Cores/propHk_fts` and no file of this `HonGaps` directory (in particular it avoids the
duplicate-`AngAWeak.Yslice` collision), so it can be imported alongside any of them.

## Traps worth recording for a consumer

* the two moment conditions of `EllWeakPos` are demanded only for `z > 0`
  (`TT.WeakDefs.EllWeakPos`), and the induction step above consumes exactly that class;
* the dependence on `k` is via `k - 1` on `ℕ`, i.e. for `k ≥ 3` (the `k = 2` base case is the
  paper's `prop:H2`, `TT.est_two_weak`, and is *not* reachable from this lemma);
* the hypothesis `∃ C, 0 < C ∧ EllWeak0 C` is part of the *statement* of the step (the paper's
  proof of the general case re-uses the level-`0` estimate on the radially shifted data); it is
  not used by the re-exported proof term in any way the consumer must check separately.
-/

namespace Work.FTS.EllipticEst.HonGaps


end Work.FTS.EllipticEst.HonGaps
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.RIFMain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1Ae/RIFMain` — the `I₁` expansion identity in the almost-everywhere class

This module assembles the target identity

`IP (z²∂_z²u) (∂_θ²u) = ∫_z w²∫_θ (z∂_z∂_θu)²σ - 2η·IP (z∂_zu) (z∂_zu)
   - 2η(1+η)·N - IP (cw·z∂_zu) (∂_θ²u)`

from the two `cut-off` identities `I1Ae.zibpChain` and `I1Ae.thetaChain` (each proved by the
"radial" resp. "angular" integration by parts with the two cut-offs `χ_n`, `ψ_ε`), the angular
cross identity `AeI1Fts.cross_joint_h` and the limiting lemmas of `I1Ae.RIFLimits`.

-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)

/-! ## The generic angular cut-off limit -/


/-! ## Joint integrability of a box-supported continuous function -/






end Work.FTS.EllipticEst.I1Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Straight_certs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary `∂_θ`-calculus for radial multiples of `sin 2θ` -/

/-- `∂_θ (sin 2θ) = 2 cos 2θ`. -/
theorem deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ
        ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))
  exact h.deriv



/-! ## The `∂_θ`-iterates of `C^∞` functions on the open quadrant

The two facts below are the `SmoothOpen`-closure of the `∂_θ`-iterates and their additivity; the
proofs are the standard ones (`C^∞`-slices are differentiable, `deriv` is additive there). -/

/-- `SmoothOpen` is closed under the `∂_θ`-iterates. -/
theorem SmoothOpen_pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `∂_θ`-iterates are additive on data which are `C^∞` on the open quadrant. -/
theorem pthIter_add_of_smoothOpen {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i : ℕ) : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter i f z θ + Work.Spaces.pthIter i g z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((SmoothOpen_pthIter hf n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((SmoothOpen_pthIter hg n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      rw [Work.Spaces.pthIter_succ]
      show deriv (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ') θ
        = deriv (fun θ' => Work.Spaces.pthIter n f z θ') θ
          + deriv (fun θ' => Work.Spaces.pthIter n g z θ') θ
      rw [heq.deriv_eq]
      exact deriv_add hd1 hd2

/-! ## The smoothness of `Gsing` and its two relations -/


/-! ## The `ℋ^k`-certificate of `Ḡ(α,F)·sin 2θ` at `α ≤ 1` -/


/-! ## The three analytic inputs of the assembly

`HkMem_Dz_a1` (the radial `D_z`-Agmon estimate), `L12_moment_eq_a1` (the moment identity which
identifies `L₁₂(F)`) and `HkMem_L12_sin_a1` (the Hardy estimate for `L₁₂(F)·sin 2θ`) are the
three further certificates consumed below. -/



/-! ## The target -/


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.Maj_aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open MeasureTheory Set Filter
open scoped Real

set_option autoImplicit false

/-! ## Measurability of the two indicator families -/




end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.Maj_integral_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut


end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.Maj_slice_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc.Subcut

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **Nonnegativity of the majorant.**  `Maj α C κN N f = C · (1_{UN N} · HkIntegrand + 1_{LN N} ·
∑_{b<4} slotW²)` and both summands are products of an indicator (taking the values `0, 1`) with a
square or with the `HkIntegrand`, which is a sum of squares.  Only `0 < C` is needed (`κN` does not
occur in `Maj`). -/
private theorem Maj_nonneg {α : ℝ} {f : Fn} {C κN : ℝ} (N : ℕ) (hC : 0 < C) (z θ : ℝ) :
    0 ≤ Work.FTS.GalBasis.cc.Maj α C κN N f z θ := by
  rw [Work.FTS.GalBasis.cc.Maj_eq_sum_form]
  refine mul_nonneg hC.le (add_nonneg ?_ ?_)
  · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
  · exact Finset.sum_nonneg fun b _ => mul_nonneg
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _)



end Work.FTS.GalBasis.cc.Subcut
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10aux.radialBounded_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.NRow10aux

set_option maxHeartbeats 1600000

/-!
## The pointwise majorant `HkIntegrand α 4 (r · g) ≤ K · HkIntegrand α 4 g` for radial `r`

`r` is a radial coefficient all of whose `D_z`-iterates up to order `4` are bounded by `1`
on `z ≥ 0` (this is exactly the hypothesis available for the radial factors of the
nonlinearity in the `NRow` estimates); `g` is arbitrary.  The claim is that the full `ℋ⁴`
integrand of the product `r · g` is pointwise dominated by a universal multiple of that of
`g` — in particular the constant does **not** depend on `α`.

The proof is the binomial expansion of `D_z^i (r·g)` resp. `D_z^j D_θ^i (r·g)`
(`Work.FTS.OpenPkg.leibniz_rad_Dz`, `Work.FTS.OpenPkg.leibniz_rad_mixed`; all angular
derivatives fall on `g` because `r` is radial), Cauchy–Schwarz on the resulting finite sums
(`sq_sum_le_card_mul_sum_sq`) together with `i.choose b ≤ 2^i ≤ 16`, and the fact that each
Leibniz summand is a genuine summand of `HkIntegrand α 4 g` (`sq_le_HkIntegrand_z`,
`sq_le_HkIntegrand_mixed`).

Unlike the sibling `starProdPt` (which needs `0 < α ≤ 1` to trade a surplus power of
`sin 2θ` against the angular weight `Wt`), the radial case needs **no** comparison between
the `η`-weight `w/ sin(2θ)^{η/2}` and the `γ`-weight `Wt α`: the slots of `r·g` have exactly
the same weights as those of `g`, so the estimate holds for every real `α`.
-/

/-- `i.choose b ≤ 2^i ≤ 16` for `i ≤ 4`, hence `(i.choose b)² ≤ 256`. -/
private theorem choose_sq_le_256 (i b : ℕ) (_hb : b ≤ i) (hi : i ≤ 4) :
    ((i.choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : 2 ^ i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi
  have h3 : ((i.choose b : ℕ) : ℝ) ≤ 16 := by
    have h : i.choose b ≤ 16 := by omega
    exact_mod_cast h
  nlinarith [h3, Nat.cast_nonneg (α := ℝ) (i.choose b)]

/-- A single pure `D_z`-slot of the `ℋ⁴`-integrand of the radial product `r · g`. -/
private theorem zslot_bound {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ b : ℕ, b ≤ 4 → |Work.Elliptic.DzdIter b r z| ≤ 1)
    (i : ℕ) (hi : i ≤ 4) :
    (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 6400 * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hlei := Work.FTS.OpenPkg.leibniz_rad_Dz r g hr hg i z (Set.mem_Ioi.mpr hz) θ
    (Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩)
  have hsum : Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 256 * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256 i b hbi hi
    have hRd : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ 1 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b r z)]
    have hG : (Work.Spaces.DzIter (i - b) g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i - b) (by omega)
    calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ 256 * 1 * Work.Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) (by norm_num)
      _ = 256 * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 5 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 5)
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
        ≤ ∑ _b ∈ Finset.range (i + 1), (256 * Work.Spaces.HkIntegrand α 4 g z θ) :=
          Finset.sum_le_sum hper
      _ = ((i + 1 : ℕ) : ℝ) * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by norm_num) hHk)
          exact_mod_cast (by omega : i + 1 ≤ 5)
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
                * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
      ≤ 5 * (5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 6400 * Work.Spaces.HkIntegrand α 4 g z θ := by ring

/-- A single mixed slot (`1 ≤ i`) of the `ℋ⁴`-integrand of the radial product `r · g`. -/
private theorem mslot_bound {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ b : ℕ, b ≤ 4 → |Work.Elliptic.DzdIter b r z| ≤ 1)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 6400 * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hj4 : j ≤ 4 := by omega
  have hlei := Work.FTS.OpenPkg.leibniz_rad_mixed r g hr hg j i hi z (Set.mem_Ioi.mpr hz) θ
    (Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩)
  have hsum : Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1),
          (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (j + 1),
      ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 256 * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256 j b hbj hj4
    have hRd : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ 1 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b r z)]
    have hG : (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i (j - b) hi (by omega)
    calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 256 * 1 * Work.Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) (by norm_num)
      _ = 256 * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 5 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 5)
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), (256 * Work.Spaces.HkIntegrand α 4 g z θ) :=
          Finset.sum_le_sum hper
      _ = ((j + 1 : ℕ) : ℝ) * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by norm_num) hHk)
          exact_mod_cast (by omega : j + 1 ≤ 5)
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
                * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2
      ≤ 5 * (5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 6400 * Work.Spaces.HkIntegrand α 4 g z θ := by ring

theorem radialBounded_majorant :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z) →
      Work.FTS.EllipticEst.SmoothOpen g →
      (∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter b r z| ≤ 1) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ
          ≤ K * Work.Spaces.HkIntegrand α 4 g z θ := by
  refine ⟨200000, by norm_num, ?_⟩
  intro α r g hr hg hbnd z θ hz hθ0 hθ1
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hR : ∀ b : ℕ, b ≤ 4 → |Work.Elliptic.DzdIter b r z| ≤ 1 :=
    fun b hb => hbnd b hb z (le_of_lt hz)
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  have hA : (∑ i ∈ Finset.range (4 + 1), (Work.Spaces.DzIter i
        (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1), (Work.Spaces.DzIter i
          (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (4 + 1), (6400 * Work.Spaces.HkIntegrand α 4 g z θ) :=
          Finset.sum_le_sum fun i hi =>
            zslot_bound hr hg hz hθ0 hθ1 hR i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hB : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 25 * (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
            (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 4
          · rw [if_pos hc]
            exact mslot_bound hr hg hz hθ0 hθ1 hR i j hc.1 hc.2
          · rw [if_neg hc]
            exact mul_nonneg (by norm_num) hHk
      _ = 25 * (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  linarith [hA, hB, hHk]

end Work.FTS.NonlinRows.NRow10aux
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WDp_le_WlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Nonnegativity of the `𝒲^{4,∞}`-norm -/

/-- `WlInf α 4 f` is nonnegative as soon as its finitely many suprema are honest
(`WlInfMem α 4 f`): it is a sum of `supAbs`s, each of which is `≥ 0` under the honesty
hypotheses. -/
theorem wlInf_nonneg_of_mem {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f) :
    0 ≤ Work.Spaces.WlInf α 4 f := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 f hmem) (Work.Spaces.wlThSum_nonneg α 4 f hmem)

/-! ## The pointwise bound with the universal constant `200` -/

/-- **Every mixed `D`-derivative of total order `≤ 4` of a `SmoothOpen`, `𝒲^{4,∞}`-function is
bounded by `200 |f|_{𝒲^{4,∞}}` inside the open quadrant.**

For `j = 0` this is the `D_z`-only bound (`DzIter_le_WlInf_open`); for `j ≥ 1` it is
`Mixed_le_WlInf_open` combined with the elementary bound
`(α + sin 2θ)·sin(2θ)^{α/5} ≤ 2` (`0 < α ≤ 1`, `sin 2θ ≤ 1`). -/
theorem mixed_le_WlInf_200 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.WlInfMem α 4 f)
    {b j : ℕ} (hbj : b + j ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b j f z θ| ≤ 200 * Work.Spaces.WlInf α 4 f := by
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := wlInf_nonneg_of_mem hmem
  obtain rfl | hj := Nat.eq_zero_or_pos j
  · rw [Work.Spaces.mixed_zero_right]
    calc |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f :=
          DzIter_le_WlInf_open hf hmem (by omega) hz hθ
      _ ≤ 200 * Work.Spaces.WlInf α 4 f := by linarith
  · have hs0 : 0 ≤ Real.sin (2 * θ) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hα5 : 0 ≤ α / 5 := by linarith
    have hΦ1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 hα5
    have hΦ2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
      nlinarith [hΦ1, Real.rpow_nonneg hs0 (α / 5), hs0, hα]
    calc |Work.Spaces.mixed b j f z θ|
        ≤ 100 * (Work.Spaces.WlInf α 4 f
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Mixed_le_WlInf_open hα hf hmem hj (by omega) hz hθ
      _ ≤ 100 * (Work.Spaces.WlInf α 4 f * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦ2 hW) (by norm_num)
      _ = 200 * Work.Spaces.WlInf α 4 f := by ring

/-! ## The comparison of the two norms -/

/-- **`WDp` is dominated by the `𝒲^{4,∞}`-norm**: there is a universal constant `C` with
`WDp 4 f ≤ C · WlInf α 4 f` for every `0 < α ≤ 1` and every `SmoothOpen` function
`f` of class `WlInfMem α 4 f`.

The constant is `25 · 200 = 5000`: the `WDp`-grid has `25` entries and
`mixed_le_WlInf_200` bounds each of them by `200 |f|_𝒲`. -/
theorem WDp_le_WlInf :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.WDp 4 f ≤ C * Work.Spaces.WlInf α 4 f := by
  refine ⟨5000, by norm_num, fun α f hα hα1 hf hmem => ?_⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := wlInf_nonneg_of_mem hmem
  have hM : (0 : ℝ) ≤ 200 * Work.Spaces.WlInf α 4 f := by positivity
  have hgrid := WDp_le_of_pointwise (α := α) (M := 200 * Work.Spaces.WlInf α 4 f) (f := f) hM
    (fun b j hbj z θ hz hθ hθ' => mixed_le_WlInf_200 hα hα1 hf hmem hbj hz ⟨hθ, hθ'⟩)
  calc Work.FTS.VocabO.WDp 4 f ≤ 25 * (200 * Work.Spaces.WlInf α 4 f) := hgrid
    _ = 5000 * Work.Spaces.WlInf α 4 f := by ring

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.wang_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The iterated angular operator applied to a function which is constant in `z` does not depend
on `z` (the derivatives are taken of literally the same angular function). -/
theorem DthIter_const_z_eq (a : ℝ → ℝ) :
    ∀ (i : ℕ) (z z' θ : ℝ),
      Work.Spaces.DthIter i (fun _ θ' => a θ') z θ
        = Work.Spaces.DthIter i (fun _ θ' => a θ') z' θ := by
  intro i
  induction i with
  | zero => intro z z' θ; rfl
  | succ i ih =>
    intro z z' θ
    change Work.Spaces.Dth (Work.Spaces.DthIter i (fun _ θ' => a θ')) z θ
      = Work.Spaces.Dth (Work.Spaces.DthIter i (fun _ θ' => a θ')) z' θ
    rw [show Work.Spaces.Dth (Work.Spaces.DthIter i (fun _ θ' => a θ')) z θ
        = Real.sin (2 * θ) * deriv (fun θ' =>
            Work.Spaces.DthIter i (fun _ θ'' => a θ'') z θ') θ from rfl,
      show Work.Spaces.Dth (Work.Spaces.DthIter i (fun _ θ' => a θ')) z' θ
        = Real.sin (2 * θ) * deriv (fun θ' =>
            Work.Spaces.DthIter i (fun _ θ'' => a θ'') z' θ') θ from rfl]
    have hfun : (fun θ' => Work.Spaces.DthIter i (fun _ θ'' => a θ'') z θ')
        = fun θ' => Work.Spaces.DthIter i (fun _ θ'' => a θ'') z' θ' := by
      funext θ'
      exact ih z z' θ'
    rw [hfun]

/-- **Multiplication by an angular profile in the `D`-sup norm.** -/
theorem wang_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∀ (a : ℝ → ℝ) (h : Fn) (Ca : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      Work.FTS.EllipticEst.SmoothOpen h →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
      WDMem 4 h →
      WDMem 4 (fun z θ => a θ * h z θ) ∧
      WDp 4 (fun z θ => a θ * h z θ) ≤ C * Ca * WDp 4 h := by
  refine ⟨400, by norm_num, ?_⟩
  intro α hα hα1 a h Ca hasm hhsm hab hdab hm
  have hCa : 0 ≤ Ca := by
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hab 0 h0)
  have hhnn : 0 ≤ WDp 4 h := WDp_nonneg 4 h
  have hMnn : 0 ≤ 16 * (Ca * WDp 4 h) := mul_nonneg (by norm_num) (mul_nonneg hCa hhnn)
  have hbound : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j (fun z θ => a θ * h z θ) z θ| ≤ 16 * (Ca * WDp 4 h) := by
    intro b j hbj z θ hz hθ0 hθ1
    have hLeib : Work.Spaces.mixed b j (fun z θ => a θ * h z θ) z θ
        = ∑ u ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
            ((j.choose u : ℝ) * (b.choose c : ℝ))
              * (Work.Spaces.mixed c u (fun _ θ' => a θ') z θ
                * Work.Spaces.mixed (b - c) (j - u) h z θ) :=
      ProdOpen.leibniz_open_mixed b j (fun _ θ' => a θ') h hasm hhsm z θ hz hθ0 hθ1
    rw [hLeib]
    refine le_trans (Finset.abs_sum_le_sum_abs
      (fun u => ∑ c ∈ Finset.range (b + 1), (j.choose u : ℝ) * (b.choose c : ℝ)
        * (Work.Spaces.mixed c u (fun _ θ' => a θ') z θ
          * Work.Spaces.mixed (b - c) (j - u) h z θ)) (Finset.range (j + 1))) ?_
    have hstep : ∀ u ∈ Finset.range (j + 1),
        |∑ c ∈ Finset.range (b + 1), (j.choose u : ℝ) * (b.choose c : ℝ)
            * (Work.Spaces.mixed c u (fun _ θ' => a θ') z θ
              * Work.Spaces.mixed (b - c) (j - u) h z θ)|
          ≤ ∑ c ∈ Finset.range (b + 1), (j.choose u : ℝ) * (b.choose c : ℝ)
              * (Ca * WDp 4 h) := by
      intro u hu
      refine le_trans (Finset.abs_sum_le_sum_abs
        (fun c => (j.choose u : ℝ) * (b.choose c : ℝ)
          * (Work.Spaces.mixed c u (fun _ θ' => a θ') z θ
            * Work.Spaces.mixed (b - c) (j - u) h z θ)) (Finset.range (b + 1))) ?_
      refine Finset.sum_le_sum fun c hc => ?_
      have huj : u ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
      have hcb : c ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have hcn : (0 : ℝ) ≤ (b.choose c : ℝ) := Nat.cast_nonneg _
      have hun : (0 : ℝ) ≤ (j.choose u : ℝ) := Nat.cast_nonneg _
      have h1 : |Work.Spaces.mixed c u (fun _ θ' => a θ') z θ| ≤ Ca := by
        rcases Nat.eq_zero_or_pos c with hc0 | hcpos
        · subst hc0
          simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero]
          rcases Nat.eq_zero_or_pos u with hu0 | hupos
          · subst hu0
            exact hab θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩
          · have hz0 : Work.Spaces.DthIter u (fun _ θ' => a θ') z θ
                = Work.Spaces.DthIter u (fun _ θ' => a θ') 0 θ :=
              DthIter_const_z_eq a u z 0 θ
            rw [hz0]
            refine le_trans (hdab u hupos (by omega) θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩) ?_
            have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
            nlinarith [hCa, hsin1]
        · have hzero : Work.Spaces.mixed c u (fun _ θ' => a θ') z θ = 0 := by
            have hD := DzIter_eq_zero_of_z_const
              (F := Work.Spaces.DthIter u (fun _ θ' => a θ'))
              (fun z θ => DthIter_const_z_eq a u z 0 θ) c hcpos
            simp only [Work.Spaces.mixed]
            rw [hD]
          rw [hzero, abs_zero]
          exact hCa
      have h2 : |Work.Spaces.mixed (b - c) (j - u) h z θ| ≤ WDp 4 h :=
        mixed_le_WDp hm (by omega) hz hθ0 hθ1
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hun, abs_of_nonneg hcn]
      calc (j.choose u : ℝ) * (b.choose c : ℝ)
            * (|Work.Spaces.mixed c u (fun _ θ' => a θ') z θ|
              * |Work.Spaces.mixed (b - c) (j - u) h z θ|)
          = (j.choose u : ℝ) * ((b.choose c : ℝ)
              * (|Work.Spaces.mixed c u (fun _ θ' => a θ') z θ|
                * |Work.Spaces.mixed (b - c) (j - u) h z θ|)) := by ring
        _ ≤ (j.choose u : ℝ) * ((b.choose c : ℝ) * (Ca * WDp 4 h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul h1 h2 (abs_nonneg _) hCa) hcn) hun
        _ = (j.choose u : ℝ) * (b.choose c : ℝ) * (Ca * WDp 4 h) := by ring
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hswap : ((∑ u ∈ Finset.range (j + 1), (j.choose u : ℝ))
            * (∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ)))
          * (Ca * WDp 4 h)
        = ∑ u ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
            (j.choose u : ℝ) * (b.choose c : ℝ) * (Ca * WDp 4 h) := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
    rw [← hswap]
    have hchoose_j : (∑ u ∈ Finset.range (j + 1), (j.choose u : ℝ)) = 2 ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    have hchoose_b : (∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ)) = 2 ^ b := by
      exact_mod_cast Nat.sum_range_choose b
    rw [hchoose_j, hchoose_b, ← pow_add]
    have hpow : (2 : ℝ) ^ (j + b) ≤ 16 := by
      have hjb : j + b ≤ 4 := by omega
      calc (2 : ℝ) ^ (j + b) ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hjb
        _ = 16 := by norm_num
    nlinarith [hCa, hhnn, hpow, mul_nonneg hCa hhnn]
  constructor
  · intro b j hbj
    exact ⟨16 * (Ca * WDp 4 h),
      fun z θ hz hθ0 hθ1 => hbound b j hbj z θ hz hθ0 hθ1⟩
  · refine le_trans (WDp_le_of_pointwise (α := α) hMnn
      (fun b j hbj z θ hz hθ0 hθ1 => hbound b j hbj z θ hz hθ0 hθ1)) ?_
    nlinarith [hCa, hhnn, mul_nonneg hCa hhnn]

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.hasDerivAt_Jeps_slice_th =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

theorem hasDerivAt_Jeps_slice_th (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => Work.FTS.StrongEps.Jeps ρ ε g z θ')
      (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) * deriv (fun θ' => Work.FTS.StrongEps.thShift θ' p.2) θ)) θ := by
  -- the two smoothness hypotheses of the dominated-convergence lemma
  have hf : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.StrongEps.Quad := hg 1
  have hdf : ContinuousOn (Function.uncurry (Work.Spaces.pth g)) Work.FTS.StrongEps.Quad :=
    ((Work.Spaces.uncurry_partial_c1 Work.FTS.StrongEps.isOpen_Quad (hg 2)).2).continuousOn
  -- near `θ` the slice of `Jeps` is the `p`-integral defining it
  have hev : (fun θ' => Work.FTS.StrongEps.Jeps ρ ε g z θ')
      =ᶠ[𝓝 θ] fun θ' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ' p.2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Work.FTS.StrongEps.Jeps_eq_integral ρ ε g hz hθ'
  -- the kernel is supported in the ball, so `closedBall`-restricted integrals are unrestricted
  have hF : (fun θ' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ' p.2)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)))
      = fun θ' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ' p.2) := by
    funext θ'
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ' p.2))
      (fun p hp => by rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])
  have hG : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
          * deriv (fun θ' => Work.FTS.StrongEps.thShift θ' p.2) θ))
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
          * deriv (fun θ' => Work.FTS.StrongEps.thShift θ' p.2) θ)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
          * deriv (fun θ' => Work.FTS.StrongEps.thShift θ' p.2) θ))
      (fun p hp => by rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])).symm
  have hd := Work.FTS.StrongEps.hasDerivAt_integral_Jeps_th (ρ := ρ) (ε := ε) (f := g)
    hρ hε hf hdf hz hθ
  rw [hF, ← hG] at hd
  exact hd.congr_of_eventuallyEq hev

end Work.FTS.StrongEps.DiffAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.continuous_logW_leaf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open scoped Real

/-!
# `continuous_logW_leaf` — continuity of the log-coordinate leaf densities

For each of the three leaf weights `leafEta`, `leafOne`, `leafGam α` of the `IP4`-unfolding
(`TransportS.Slots`), the log-coordinate density

  `logW w y = logJac y.1 y.2 * w (e^{y.1}) (arctan (e^{y.2}))`

is continuous on the plane.  This is the regularity hypothesis consumed by the transfer
estimates of `JepsTransfer` (e.g. the convolution identities relating `logPair` to the pairings
`slotPairing`).

Everything reduces to the continuity of the thre factors on `ℝ²`:

* the Jacobian `logJac s ζ = e^s · e^ζ / (1 + e^{2ζ})`;
* the radial factor `w (e^s)² = ((1+e^s)²/(e^s)²)²` (continuous because `e^s > 0` for all `s`,
  which is exactly why the pole of `Spaces.w` at `0` is harmless);
* the angular factor `sin(2 arctan (e^ζ))^{-q}`, `q ≥ 0`; here `arctan (e^ζ) ∈ (0, π/2)` for
  *every* `ζ`, so the base is genuinely positive and `Real.rpow` is continuous in the base on
  this range (no junk-value issues).
-/

private lemma arctan_exp_mem_clw (ζ : ℝ) :
    Real.arctan (Real.exp ζ) ∈ Set.Ioo 0 (π / 2) :=
  ⟨Real.arctan_pos.mpr (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩

/-- The Jacobian `logJac` of the log-coordinate substitution is continuous on the plane. -/
private lemma continuous_logJac_clw :
    Continuous (fun y : ℝ × ℝ => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2) := by
  simp only [Work.FTS.StrongEps.HkSqAux.logJac, Work.FTS.StrongEps.HkSqAux.kappa]
  exact ((Real.continuous_exp.comp continuous_fst)).mul
    (((Real.continuous_exp.comp continuous_snd)).div
      (continuous_const.add ((Real.continuous_exp.comp (continuous_const.mul continuous_snd))))
      (fun y => by positivity))

/-- The radial factor `y ↦ w (e^{y.1})²` of the leaf weights is continuous on the plane. -/
private lemma continuous_wtZ_exp_clw :
    Continuous (fun y : ℝ × ℝ => Work.Spaces.w (Real.exp y.1) ^ 2) := by
  have h : Continuous fun y : ℝ × ℝ =>
      ((1 + Real.exp y.1) ^ 2 / (Real.exp y.1) ^ 2) ^ 2 :=
    (((continuous_const.add (Real.continuous_exp.comp continuous_fst)).pow 2).div
      ((Real.continuous_exp.comp continuous_fst).pow 2)
      (fun y => pow_ne_zero 2 (ne_of_gt (Real.exp_pos _)))).pow 2
  simpa only [Work.Spaces.w] using h

/-- The angular factor `y ↦ sin(2 arctan (e^{y.2}))^{-q}` is continuous on the plane for every
exponent `q`. -/
private lemma continuous_sinTwo_arctan_exp_clw (q : ℝ) :
    Continuous (fun y : ℝ × ℝ => Real.sin (2 * Real.arctan (Real.exp y.2)) ^ (-q)) := by
  have hsin : Continuous (fun y : ℝ × ℝ => Real.sin (2 * Real.arctan (Real.exp y.2))) :=
    Real.continuous_sin.comp
      (continuous_const.mul (Real.continuous_arctan.comp (Real.continuous_exp.comp continuous_snd)))
  refine hsin.rpow_const (fun y => Or.inl ?_)
  have hθ := arctan_exp_mem_clw y.2
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))

theorem continuous_logW_leaf {w : ℝ → ℝ → ℝ} {α : ℝ}
    (hw : w = Work.FTS.TransportS.leafEta ∨ w = Work.FTS.TransportS.leafOne
      ∨ w = Work.FTS.TransportS.leafGam α) :
    Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w) := by
  rcases hw with rfl | rfl | rfl
  · show Continuous (fun y : ℝ × ℝ => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2 *
      (Work.Spaces.w (Real.exp y.1) ^ 2 *
        Real.sin (2 * Real.arctan (Real.exp y.2)) ^ (-(Work.Spaces.eta))))
    exact continuous_logJac_clw.mul (continuous_wtZ_exp_clw.mul
      (continuous_sinTwo_arctan_exp_clw Work.Spaces.eta))
  · show Continuous (fun y : ℝ × ℝ => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2 *
      Work.Spaces.w (Real.exp y.1) ^ 2)
    exact continuous_logJac_clw.mul continuous_wtZ_exp_clw
  · show Continuous (fun y : ℝ × ℝ => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2 *
      (Work.Spaces.w (Real.exp y.1) ^ 2 *
        Real.sin (2 * Real.arctan (Real.exp y.2)) ^ (-(Work.Spaces.gam α))))
    exact continuous_logJac_clw.mul (continuous_wtZ_exp_clw.mul
      (continuous_sinTwo_arctan_exp_clw (Work.Spaces.gam α)))

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `leaf_logW_shift` — the log-coordinate shift estimate for the leaf weights

The three leaf weights of the `IP4`-unfolding are

  `leafEta = w² sin(2θ)^{-η}`,  `leafOne = w²`,  `leafGam α = w² sin(2θ)^{-γ α}`,

with `w z = (1+z)²/z²`, `η = 99/100`, `γ α = 1 + α/10`.  In the log coordinates
`(s,ζ) = (log z, log tan θ)` the weight `logW w` is the product of the Jacobian `logJac` of the
substitution and `w ∘ Ψ`, and the shift `y ↦ y + p` on the plane corresponds to
`z ↦ z e^{p.1}`, `tan θ ↦ tan θ · e^{p.2}`.  The present file proves that this shift changes
`logW w` by at most `e^{C(|p.1|+|p.2|)}`, in both directions — the hypothesis needed by
`logPair_conv_transfer`.

Everything is elementary and assembled from the shift bounds of the individual factors:

* `logJac_add_le` — `logJac (s+p₁) (ζ+p₂) ≤ e^{4(|p₁|+|p₂|)} logJac s ζ`, from
  `HkSqAux.kappa_shift_core`;
* `wtZ_exp_add_le` — the radial factor `wtZ = w²`, from `wtZ_zShift_le`;
* `sEtaW_thShift_le` / `sGamW_shift_le_sharp` — the angular factors
  `sin(2θ)^{-q}` for `q = η` resp. `q = γ α`, the second one being the sharp
  `e^{(γ α)|p|}`-version of `wtG_shift_le`'s `sGamW_shift_le` (which assumes `α ≤ 1`); it is
  obtained from the two-sided bound `sinTwo_thShift_bounds` by `rpow_shift_le`.

-/

/-! ## Elementary identifications of the shifted arguments -/

/-- The angle `arctan (e^ζ)` always lies in the open quadrant. -/
theorem arctan_exp_mem (ζ : ℝ) :
    Real.arctan (Real.exp ζ) ∈ Set.Ioo 0 (π / 2) :=
  ⟨Real.arctan_pos.mpr (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩

/-- `ζ ↦ ζ + p` is the `θ`-shift `thShift · (-p)` after the identification `θ = arctan (e^ζ)`. -/
theorem arctan_exp_add (ζ p : ℝ) :
    Real.arctan (Real.exp (ζ + p))
      = Work.FTS.StrongEps.thShift (Real.arctan (Real.exp ζ)) (-p) := by
  rw [Work.FTS.StrongEps.thShift, Real.tan_arctan, neg_neg, ← Real.exp_add]

/-- `ζ ↦ ζ + p` is the `z`-shift `zShift · (-p)` after the identification `z = e^ζ`. -/
theorem exp_add_eq_zShift (ζ p : ℝ) :
    Real.exp (ζ + p) = Work.FTS.StrongEps.zShift (Real.exp ζ) (-p) := by
  rw [Work.FTS.StrongEps.zShift, neg_neg, ← Real.exp_add]

/-! ## The Jacobian factor -/

/-- **The Jacobian factor shifts forwards by `e^{4(|p₁|+|p₂|)}`.**  This is
`HkSqAux.kappa_shift_core` (`kappa (ζ+p₂) ≤ e^{2|p₂|+p₂} kappa ζ`) combined with
`Real.exp (s+p₁) = e^s e^{p₁} ≤ e^s e^{|p₁|}`. -/
theorem logJac_add_le (s ζ p₁ p₂ : ℝ) :
    Work.FTS.StrongEps.HkSqAux.logJac (s + p₁) (ζ + p₂)
      ≤ Real.exp (4 * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac s ζ := by
  have hk : Work.FTS.StrongEps.HkSqAux.kappa (ζ + p₂)
      ≤ Real.exp (2 * |p₂| + p₂) * Work.FTS.StrongEps.HkSqAux.kappa ζ := by
    have h := Work.FTS.StrongEps.HkSqAux.kappa_shift_core (ζ + p₂) p₂
    rwa [show ζ + p₂ - p₂ = ζ from by ring] at h
  have he : Real.exp (s + p₁) ≤ Real.exp |p₁| * Real.exp s := by
    rw [Real.exp_add, mul_comm (Real.exp s)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_abs_self p₁))
      (Real.exp_pos s).le
  have hE : Real.exp |p₁| * Real.exp (2 * |p₂| + p₂)
      ≤ Real.exp (4 * (|p₁| + |p₂|)) := by
    rw [show Real.exp |p₁| * Real.exp (2 * |p₂| + p₂)
        = Real.exp (|p₁| + (2 * |p₂| + p₂)) from
      (Real.exp_add |p₁| (2 * |p₂| + p₂)).symm]
    exact Real.exp_le_exp.mpr
      (by nlinarith [abs_nonneg p₁, abs_nonneg p₂, le_abs_self p₂])
  rw [Work.FTS.StrongEps.HkSqAux.logJac, Work.FTS.StrongEps.HkSqAux.logJac]
  calc Real.exp (s + p₁) * Work.FTS.StrongEps.HkSqAux.kappa (ζ + p₂)
      ≤ (Real.exp |p₁| * Real.exp s)
        * (Real.exp (2 * |p₂| + p₂) * Work.FTS.StrongEps.HkSqAux.kappa ζ) :=
        mul_le_mul he hk (Work.FTS.StrongEps.HkSqAux.kappa_nonneg _)
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos s).le)
    _ = (Real.exp |p₁| * Real.exp (2 * |p₂| + p₂))
        * (Real.exp s * Work.FTS.StrongEps.HkSqAux.kappa ζ) := by ring
    _ ≤ Real.exp (4 * (|p₁| + |p₂|))
        * (Real.exp s * Work.FTS.StrongEps.HkSqAux.kappa ζ) :=
        mul_le_mul_of_nonneg_right hE
          (mul_nonneg (Real.exp_pos s).le (Work.FTS.StrongEps.HkSqAux.kappa_nonneg ζ))

/-! ## The radial factor `wtZ = w²` -/

/-- **The radial weight shifts forwards by `e^{4|p|}`**: `wtZ (e^{s+p}) ≤ e^{4|p|} wtZ (e^s)`.
This is `wtZ_zShift_le` at the point `z = e^s` with parameter `-p`. -/
theorem wtZ_exp_add_le (s p : ℝ) :
    Work.FTS.StrongEps.wtZ (Real.exp (s + p))
      ≤ Real.exp (4 * |p|) * Work.FTS.StrongEps.wtZ (Real.exp s) := by
  have h := Work.FTS.StrongEps.wtZ_zShift_le (Real.exp s) (-p) (Real.exp_pos s)
  rw [← exp_add_eq_zShift s p, abs_neg] at h
  exact h

/-! ## The angular factor `sin(2θ)^{-γ α}` with the sharp exponent -/

/-- **The angular weight `sin(2θ)^{-γ α}` is shifted by at most `e^{(γ α)|p|}`** for every
`α > 0` (no upper bound on `α`).  This is the sharp version of `sGamW_shift_le`: from the lower
bound `e^{-|p|} sin(2θ) ≤ sin(2·thShift θ p)` one raises to the negative power `-γ α` using
`rpow_shift_le`. -/
theorem sGamW_shift_le_sharp {α : ℝ} (hα : 0 < α) {θ p : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.StrongEps.sGamW α (Work.FTS.StrongEps.thShift θ p)
      ≤ Real.exp (Work.Spaces.gam α * |p|) * Work.FTS.StrongEps.sGamW α θ := by
  have hlo : Real.exp (-|p|) * Real.sin (2 * θ)
      ≤ Real.sin (2 * Work.FTS.StrongEps.thShift θ p) :=
    (Work.FTS.StrongEps.sinTwo_thShift_bounds hθ).1
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hγ : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have h := Work.FTS.StrongEps.rpow_shift_le (s := Real.sin (2 * θ))
    (s' := Real.sin (2 * Work.FTS.StrongEps.thShift θ p)) (c := |p|)
    (γ := Work.Spaces.gam α) hs hγ hlo
  simpa only [Work.FTS.StrongEps.sGamW] using h

/-! ## The general one-sided shift bound -/


/-! ## The target -/


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/Defs.lean` — the derivative-priced plane transfer estimate

The `JepsTransfer` chapter isolates, as the predicate `JT.LogPlaneTransfer`, the analytic core of
the *even*-kernel transfer estimate: for an even kernel `k` supported in the `ℓ¹`-ball of radius
`2ε` and a log-Lipschitz weight `Q`,

  `|∫ Q (k * G₁) G₂ − ∫ Q G₁ (k * G₂)| ≤ C ε √(∫ Q G₁²) √(∫ Q G₂²)`.

That estimate is **false** without the evenness of `k` (take `k` a point mass at `p₀` with
`|p₀| = ε`, `G₁ = 1_{[−ε,0]}`, `G₂ = 1_{[0,ε]}`: the defect is `≍ ε` while `ε‖G₁‖‖G₂‖ ≍ ε²`).
What *is* true for an arbitrary kernel is the same estimate **at the price of one derivative on
the second argument**:

  `|∫ Q (k * G₁) G₂ − ∫ Q G₁ (k * G₂)| ≤ C ε √(∫ Q G₁²) (√(∫ Q G₂²) + √(∫ Q ‖fderiv G₂‖²))`.

The mechanism: writing `D` for the defect and substituting `y ↦ y + p` in the first half,

  `D = ∫∫ k p · G₁ y · [Q (y+p) G₂ (y+p) − Q y G₂ (y−p)] dy dp`,

splits into the *weight difference* `∫∫ k p G₁ y (Q (y+p) − Q y) G₂ (y+p)` — which is `O(ε)`
because `Q` is log-Lipschitz (`Pieces2.weight_diff_integral_le`, proved) — and the *shift
difference* `∫∫ k p G₁ y Q y (G₂ (y+p) − G₂ (y−p))`.  For even `k` the shift-difference term
cancels under `p ↦ −p`; for odd `k` it does not, but it is a *difference operator*:
`∫ k p (G₂ (y+p) − G₂ (y−p)) dp` is controlled by `2|p| · sup|∇G₂|` on the segment, so its
`L²_Q`-norm is `O(ε) ‖∇G₂‖_{L²_Q}`.

This is the interface consumed by the level-four (and level-six) transfer lemmas of the
`Apriori4` chapter.  The predicate is stated for an arbitrary measurable kernel `k` with
`∫ |k| ≤ 1`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-- **The derivative-priced plane transfer estimate.**  For every measurable kernel `k` with
`∫ |k| ≤ 1` supported in the `ℓ¹`-ball of radius `2ε`, every nonnegative log-Lipschitz weight `Q`
and all `C¹` profiles `G₁`, `G₂` with finite weighted `L²`-norms, the transfer defect of the
convolution `k * ·` is `O(ε)`, with one derivative charged on the second argument.

The constant is `100 (Cw+1) e^{4Cw}`; the hypotheses `hI1`, `hI2`, `hIg`, `hconv1`, `hconv2` are
the integrability certificates (they are discharged in the applications from the weighted
membership of the slots). -/
def PlaneTransferDeriv : Prop :=
  ∀ {k Q : ℝ × ℝ → ℝ} {ε Cw : ℝ},
    0 < ε → ε ≤ 1 → 0 ≤ Cw →
    Measurable k → Integrable k → (∫ p : ℝ × ℝ, |k p| ≤ 1) →
    (∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε) →
    (∀ y : ℝ × ℝ, 0 ≤ Q y) → Measurable Q →
    (∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y) →
    (∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p)) →
    ∀ {G₁ G₂ : ℝ × ℝ → ℝ}, Measurable G₁ → Measurable G₂ → ContDiff ℝ 1 G₂ →
      (∀ y : ℝ × ℝ, Integrable (fun p : ℝ × ℝ => k p * G₁ (y - p))) →
      (∀ y : ℝ × ℝ, Integrable (fun p : ℝ × ℝ => k p * G₂ (y - p))) →
      Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2) →
      Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2) →
      Integrable (fun y : ℝ × ℝ => Q y * ‖fderiv ℝ G₂ y‖ ^ 2) →
      |(∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
        - (∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)))| ≤
        100 * (Cw + 1) * Real.exp (4 * Cw) * ε * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)
              + Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2))

/-- **The integrability certificates of the derivative-priced slot transfer**, for one specific
slot pair `(u, v)`.  The single-slot transfer estimate is applied to the pairing
`wip w (mixed b a ·) (mixed b a ·)`; the plane estimate consumes the finiteness of the two slots,
of the *mollified* second slot, of the mixed product, and of the two first-order slots of the
second argument (the derivative price).  In the applications these six conditions are discharged
from `HkMem α 4 f` (for `u`) and `HkMem α 5 h` (for `v`). -/
def SlotIntegrableDeriv (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (w : ℝ → ℝ → ℝ) (a b : ℕ)
    (u v : Work.FTS.Galerkin.Fn) : Prop :=
  Integrable (Function.uncurry (fun z θ => w z θ * (Work.Spaces.mixed b a u z θ) ^ 2))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ * (Work.Spaces.mixed b a v z θ) ^ 2))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ
        * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v) z θ) ^ 2))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ * Work.Spaces.mixed b a u z θ
        * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v) z θ))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ
        * (Work.Spaces.mixed (b + 1) a v z θ) ^ 2))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ
        * (Work.Spaces.mixed b (a + 1) v z θ) ^ 2))

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.contDiff_logPull =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts

/-- The log-coordinate map `Ψ(s,ζ) = (e^s, arctan (e^ζ))` is smooth of every finite order as a
map `ℝ × ℝ → ℝ × ℝ`. -/
theorem contDiff_logPsi (n : ℕ) :
    ContDiff ℝ n (fun x : ℝ × ℝ => (Real.exp x.1, Real.arctan (Real.exp x.2))) :=
  (Real.contDiff_exp.comp contDiff_fst).prodMk
    (Real.contDiff_arctan.comp (Real.contDiff_exp.comp contDiff_snd))

/-- The log-coordinate map lands in the open quadrant `Q0` (for every `y`, `e^{y.1} > 0` and
`0 < arctan (e^{y.2}) < π/2`). -/
theorem logPsi_mem_Q0 (x : ℝ × ℝ) :
    (Real.exp x.1, Real.arctan (Real.exp x.2)) ∈ Work.FTS.EllipticEst.Q0 :=
  Work.FTS.EllipticEst.mem_Q0.mpr
    ⟨Real.exp_pos x.1, Real.arctan_pos.mpr (Real.exp_pos x.2), Real.arctan_lt_pi_div_two _⟩

theorem contDiff_logPull {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (n : ℕ) :
    ContDiff ℝ n (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) := by
  -- `logPull g` is the composite `(uncurry g) ∘ Ψ` of the `C^n` map `Ψ` (whose image lies in the
  -- open quadrant `Q0`) with the function `uncurry g`, which is `C^n` *on* `Q0`.
  exact ContDiffOn.comp_contDiff (hg n) (contDiff_logPsi n) logPsi_mem_Q0

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.norm_fderiv_logPull_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `norm_fderiv_logPull_sq_le` — the size of the Fréchet derivative of the log-pull

In the log coordinates `(s, ζ) ↦ Ψ(s,ζ) = (e^s, arctan (e^ζ))` the transport operators
`D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` become the two partial derivatives of the pulled-back
profile: the directional derivative of `logPull g` in the `s`-direction is `D_z g`, and in the
`ζ`-direction it is `D_θ g / 2` (because `dθ/dζ = sin(2θ)/2` for `θ = arctan(e^ζ)`).

Since the norm on `ℝ × ℝ` is the sup norm, whose unit ball is the square, one has
`‖L‖ ≤ |L e₁| + |L e₂|` for every continuous linear functional `L`, hence

  `‖fderiv ℝ (logPull g) y‖² ≤ 2 (D_z g)² + 2 (D_θ g / 2)² ≤ 2 (D_z g)² + (D_θ g)²`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts

/-! ## Elementary one-dimensional facts -/

/-- `sin (2 arctan t) / 2 = t / (1 + t²)`: the elementary trigonometric identity behind the
change of coordinate `θ = arctan (e^ψ)`. -/
private lemma sin_two_arctan_div_two (t : ℝ) : Real.sin (2 * Real.arctan t) / 2 = t / (1 + t ^ 2) := by
  have hD : (0 : ℝ) ≤ 1 + t ^ 2 := by positivity
  have h2 : Real.sin (Real.arctan t) * Real.cos (Real.arctan t) = t / (1 + t ^ 2) := by
    rw [Real.sin_arctan, Real.cos_arctan, div_mul_div_comm, mul_one, Real.mul_self_sqrt hD]
  rw [Real.sin_two_mul]
  rw [show (2 : ℝ) * Real.sin (Real.arctan t) * Real.cos (Real.arctan t) / 2
        = Real.sin (Real.arctan t) * Real.cos (Real.arctan t) by ring]
  exact h2

/-- `d/dψ arctan (e^ψ) = sin (2 arctan (e^ψ)) / 2`. -/
private lemma hasDerivAt_arctan_exp (ψ : ℝ) :
    HasDerivAt (fun ψ' => Real.arctan (Real.exp ψ'))
      (Real.sin (2 * Real.arctan (Real.exp ψ)) / 2) ψ := by
  have h := (Real.hasDerivAt_arctan (Real.exp ψ)).comp ψ (Real.hasDerivAt_exp ψ)
  have hv : (1 / (1 + (Real.exp ψ) ^ 2)) * Real.exp ψ
      = Real.sin (2 * Real.arctan (Real.exp ψ)) / 2 := by
    rw [sin_two_arctan_div_two]
    rw [one_div, inv_mul_eq_div]
  rw [hv] at h
  exact h

/-- The `θ`-derivative of the `θ`-slice of a function smooth on the open quadrant.  (The
`z`-analogue is `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`.) -/
private lemma hasDerivAt_slice_th {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ :=
  ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt

/-! ## The operator norm on `ℝ × ℝ` -/

/-- For a continuous linear functional on `ℝ × ℝ` (with the sup norm) the operator norm is
bounded by the sum of the absolute values of the two values on the standard basis.  Squaring
gives the form used below. -/
private lemma opNorm_sq_le_inl_inr (L : ℝ × ℝ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 ≤ 2 * (L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) ^ 2
      + 2 * (L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) ^ 2 := by
  have hM : ‖L‖ ≤ |L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)| + |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)| := by
    refine ContinuousLinearMap.opNorm_le_bound L (by positivity) fun v => ?_
    have hv : v = v.1 • (ContinuousLinearMap.inl ℝ ℝ ℝ 1)
        + v.2 • (ContinuousLinearMap.inr ℝ ℝ ℝ 1) := by
      ext <;> simp [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
    have hLv : L v = v.1 • L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)
        + v.2 • L (ContinuousLinearMap.inr ℝ ℝ ℝ 1) := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul]
    rw [hLv]
    have h1 : |v.1| ≤ ‖v‖ := by
      have := norm_fst_le v
      rwa [Real.norm_eq_abs] at this
    have h2 : |v.2| ≤ ‖v‖ := by
      have := norm_snd_le v
      rwa [Real.norm_eq_abs] at this
    calc ‖v.1 • L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)
            + v.2 • L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)‖
        ≤ ‖v.1 • L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)‖
            + ‖v.2 • L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)‖ := norm_add_le _ _
      _ = |v.1| * |L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)|
            + |v.2| * |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)| := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ (|L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)|
              + |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)|) * ‖v‖ := by
          have hA : (0 : ℝ) ≤ |L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)| := abs_nonneg _
          have hB : (0 : ℝ) ≤ |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)| := abs_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right h1 hA, mul_le_mul_of_nonneg_right h2 hB]
  have h1 : ‖L‖ ^ 2
      ≤ (|L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)| + |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)|) ^ 2 := by
    nlinarith [norm_nonneg L]
  have h2 : (|L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)| + |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)|) ^ 2
      ≤ 2 * (L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) ^ 2
        + 2 * (L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) ^ 2 := by
    nlinarith [sq_nonneg (|L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)|
          - |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)|),
      sq_abs (L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)),
      sq_abs (L (ContinuousLinearMap.inr ℝ ℝ ℝ 1))]
  linarith

/-! ## The two directional derivatives of `logPull` -/

/-- The directional derivative of `logPull g` along the `s`-direction is `D_z g`. -/
private lemma hasDerivAt_logPull_inl {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y.1 + t, y.2))
      (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) 0 := by
  have hSmooth : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hθ : Real.arctan (Real.exp y.2) ∈ Set.Ioo 0 (π / 2) :=
    ⟨Real.arctan_pos.mpr (Real.exp_pos y.2), Real.arctan_lt_pi_div_two _⟩
  have hslice : HasDerivAt (fun z' : ℝ => g z' (Real.arctan (Real.exp y.2)))
      (Work.Spaces.pz g (Real.exp (y.1 + 0)) (Real.arctan (Real.exp y.2)))
      (Real.exp (y.1 + 0)) :=
    hSmooth.hasDerivAt_slice hθ (Real.exp_pos _)
  have hinner : HasDerivAt (fun t : ℝ => Real.exp (y.1 + t)) (Real.exp (y.1 + 0) * 1) 0 :=
    (Real.hasDerivAt_exp (y.1 + 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add y.1)
  have hc := hslice.comp 0 hinner
  refine hc.congr_deriv ?_
  simp only [Work.Spaces.Dz, Work.Spaces.pz, add_zero, mul_one]
  ring

/-- The directional derivative of `logPull g` along the `ζ`-direction is `D_θ g / 2`. -/
private lemma hasDerivAt_logPull_inr {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y.1, y.2 + t))
      (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2) 0 := by
  have hSmooth : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hθ : Real.arctan (Real.exp (y.2 + 0)) ∈ Set.Ioo 0 (π / 2) :=
    ⟨Real.arctan_pos.mpr (Real.exp_pos _), Real.arctan_lt_pi_div_two _⟩
  have hslice : HasDerivAt (fun θ' : ℝ => g (Real.exp y.1) θ')
      (Work.Spaces.pth g (Real.exp y.1) (Real.arctan (Real.exp (y.2 + 0))))
      (Real.arctan (Real.exp (y.2 + 0))) :=
    hasDerivAt_slice_th hSmooth (Real.exp_pos y.1) hθ
  have hinner : HasDerivAt (fun t : ℝ => Real.arctan (Real.exp (y.2 + t)))
      (Real.sin (2 * Real.arctan (Real.exp (y.2 + 0))) / 2 * 1) 0 :=
    (hasDerivAt_arctan_exp (y.2 + 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add y.2)
  have hc := hslice.comp 0 hinner
  refine hc.congr_deriv ?_
  simp only [Work.Spaces.Dth, Work.Spaces.pth, add_zero, mul_one]
  ring

/-- `logPull g` is differentiable at every point (the quadrant is open, so `g` is smooth there). -/
private lemma differentiableAt_logPull {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    DifferentiableAt ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y := by
  have hΨ : DifferentiableAt ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi) y := by
    have hf : Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi
        = fun y : ℝ × ℝ => (Real.exp y.1, Real.arctan (Real.exp y.2)) := rfl
    rw [hf]
    exact ((differentiableAt_fst (p := y)).exp).prodMk (((differentiableAt_snd (p := y)).exp).arctan)
  have hQ0 : Work.FTS.EllipticEst.Q0
      ∈ 𝓝 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi y) :=
    Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi_mem_quad y)
  have hA : DifferentiableAt ℝ (Function.uncurry g)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi y) :=
    ((hg 1).differentiableOn (by norm_num)).differentiableAt hQ0
  exact hA.comp y hΨ

/-! ## The values of the Fréchet derivative on the standard basis -/

/-- The Fréchet derivative of `logPull g` at `y` sends the first basis vector to `D_z g`. -/
private lemma fderiv_logPull_inl {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
        (ContinuousLinearMap.inl ℝ ℝ ℝ 1)
      = Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2)) := by
  have hpt : (y.1 + 0, y.2) = y := by simp
  have hF : HasFDerivAt (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) (y.1 + 0, y.2))
      (y.1 + 0, y.2) :=
    (differentiableAt_logPull hg (y.1 + 0, y.2)).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => y + t • (ContinuousLinearMap.inl ℝ ℝ ℝ 1))
      (ContinuousLinearMap.inl ℝ ℝ ℝ 1) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (ContinuousLinearMap.inl ℝ ℝ ℝ 1)).const_add y
    simpa using h
  have hfun : (fun t : ℝ => y + t • (ContinuousLinearMap.inl ℝ ℝ ℝ 1))
      = fun t : ℝ => (y.1 + t, y.2) := by
    funext t
    simp only [ContinuousLinearMap.inl_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    exact (Prod.add_def y (t, 0)).trans (by simp)
  rw [hfun] at hcurve
  have hcomp := hF.comp_hasDerivAt 0 hcurve
  rw [hpt] at hcomp
  exact hcomp.unique (hasDerivAt_logPull_inl hg y)

/-- The Fréchet derivative of `logPull g` at `y` sends the second basis vector to `D_θ g / 2`. -/
private lemma fderiv_logPull_inr {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
        (ContinuousLinearMap.inr ℝ ℝ ℝ 1)
      = Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2 := by
  have hpt : (y.1, y.2 + 0) = y := by simp
  have hF : HasFDerivAt (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) (y.1, y.2 + 0))
      (y.1, y.2 + 0) :=
    (differentiableAt_logPull hg (y.1, y.2 + 0)).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => y + t • (ContinuousLinearMap.inr ℝ ℝ ℝ 1))
      (ContinuousLinearMap.inr ℝ ℝ ℝ 1) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (ContinuousLinearMap.inr ℝ ℝ ℝ 1)).const_add y
    simpa using h
  have hfun : (fun t : ℝ => y + t • (ContinuousLinearMap.inr ℝ ℝ ℝ 1))
      = fun t : ℝ => (y.1, y.2 + t) := by
    funext t
    simp only [ContinuousLinearMap.inr_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    exact (Prod.add_def y (0, t)).trans (by simp)
  rw [hfun] at hcurve
  have hcomp := hF.comp_hasDerivAt 0 hcurve
  rw [hpt] at hcomp
  exact hcomp.unique (hasDerivAt_logPull_inr hg y)

/-- **The Fréchet derivative of the log-pull is bounded by `D_z g` and `D_θ g`.** -/
theorem norm_fderiv_logPull_sq_le {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2
      ≤ 2 * (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2
        + (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2 := by
  have h := opNorm_sq_le_inl_inr (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y)
  rw [fderiv_logPull_inl hg y, fderiv_logPull_inr hg y] at h
  have hsq : (2 : ℝ) * (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2) ^ 2
      ≤ (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2 := by
    nlinarith [sq_nonneg (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)))]
  linarith

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.decayAll_of_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## `scoef n n = 1`, the diagonal of the Stirling expansion of `D_z^n` -/

theorem scoef_self (n : ℕ) : Work.Spaces.scoef n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (n + 1) * Work.Spaces.scoef n (n + 1) + Work.Spaces.scoef n n = 1
    rw [Work.Spaces.scoef_eq_zero_of_lt (Nat.lt_succ_self n), ih]
    ring

/-! ## A function vanishing on a half-line has zero derivative at its endpoint -/

/-- If `f` vanishes on `(-∞,c]` then `deriv f c = 0`. -/
theorem deriv_eq_zero_of_forall_le {f : ℝ → ℝ} {c : ℝ} (h : ∀ x, x ≤ c → f x = 0) :
    deriv f c = 0 := by
  show fderiv ℝ f c 1 = 0
  by_cases hd : DifferentiableAt ℝ f c
  · have h1 : HasFDerivWithinAt f (fderiv ℝ f c) (Set.Iic c) c :=
      hd.hasFDerivAt.hasFDerivWithinAt
    have h2 : fderivWithin ℝ f (Set.Iic c) c = fderiv ℝ f c :=
      h1.fderivWithin (uniqueDiffWithinAt_Iic c)
    have h3 : HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) (Set.Iic c) c :=
      (hasFDerivWithinAt_const (𝕜 := ℝ) (0 : ℝ) c (Set.Iic c)).congr
        (fun y hy => h y hy) (h c le_rfl)
    have h4 : fderivWithin ℝ f (Set.Iic c) c = 0 :=
      h3.fderivWithin (uniqueDiffWithinAt_Iic c)
    have h5 : fderiv ℝ f c = 0 := by rw [← h2, h4]
    rw [h5]; simp
  · rw [fderiv_zero_of_not_differentiableAt hd]; simp

/-- If `f` vanishes on `[c,∞)` then `deriv f c = 0`. -/
theorem deriv_eq_zero_of_forall_ge {f : ℝ → ℝ} {c : ℝ} (h : ∀ x, c ≤ x → f x = 0) :
    deriv f c = 0 := by
  show fderiv ℝ f c 1 = 0
  by_cases hd : DifferentiableAt ℝ f c
  · have h1 : HasFDerivWithinAt f (fderiv ℝ f c) (Set.Ici c) c :=
      hd.hasFDerivAt.hasFDerivWithinAt
    have h2 : fderivWithin ℝ f (Set.Ici c) c = fderiv ℝ f c :=
      h1.fderivWithin (uniqueDiffWithinAt_Ici c)
    have h3 : HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) (Set.Ici c) c :=
      (hasFDerivWithinAt_const (𝕜 := ℝ) (0 : ℝ) c (Set.Ici c)).congr
        (fun y hy => h y hy) (h c le_rfl)
    have h4 : fderivWithin ℝ f (Set.Ici c) c = 0 :=
      h3.fderivWithin (uniqueDiffWithinAt_Ici c)
    have h5 : fderiv ℝ f c = 0 := by rw [← h2, h4]
    rw [h5]; simp
  · rw [fderiv_zero_of_not_differentiableAt hd]; simp

/-! ## The angular slices at `θ = 0` and `θ = π/2` of a function vanishing off the quadrant -/

/-- If `f` vanishes on the closed half-plane `θ ≤ 0` then so does every `pthIter i f`. -/
theorem pthIter_eq_zero_of_forall_nonpos {f : ℝ → ℝ → ℝ} (h : ∀ z θ, θ ≤ 0 → f z θ = 0) :
    ∀ i z θ, θ ≤ 0 → Work.Spaces.pthIter i f z θ = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ n ih =>
    intro z θ hθ
    rcases lt_or_eq_of_le hθ with hlt | heq
    · have hev : (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
        refine Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Iio 0, isOpen_Iio.mem_nhds hlt, fun θ' hθ' => ih z θ' (le_of_lt hθ')⟩
      show deriv (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') θ = 0
      rw [hev.deriv_eq, deriv_const]
    · subst heq
      exact deriv_eq_zero_of_forall_le (fun θ' hθ' => ih z θ' hθ')

/-- If `f` vanishes on the closed half-plane `θ ≥ π/2` then so does every `pthIter i f`. -/
theorem pthIter_eq_zero_of_forall_ge_pi_half {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Real.pi / 2 ≤ θ → f z θ = 0) :
    ∀ i z θ, Real.pi / 2 ≤ θ → Work.Spaces.pthIter i f z θ = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ n ih =>
    intro z θ hθ
    rcases lt_or_eq_of_le hθ with hlt | heq
    · have hev : (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
        refine Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioi (Real.pi / 2), isOpen_Ioi.mem_nhds hlt, fun θ' hθ' => ih z θ' (le_of_lt hθ')⟩
      show deriv (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') θ = 0
      rw [hev.deriv_eq, deriv_const]
    · subst heq
      exact deriv_eq_zero_of_forall_ge (fun θ' hθ' => ih z θ' hθ')

/-- The `θ = 0` slices of `∂_z^j∂_θ^i f` vanish identically for a function vanishing at `θ ≤ 0`. -/
theorem pzIter_pthIter_eq_zero_of_forall_nonpos {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, θ ≤ 0 → f z θ = 0) (j i : ℕ) (z : ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pthIter i f) z 0 = 0 := by
  induction j generalizing z with
  | zero => simpa using pthIter_eq_zero_of_forall_nonpos h i z 0 le_rfl
  | succ n ih =>
    have hfun : (fun z' : ℝ => Work.Spaces.pzIter n (Work.Spaces.pthIter i f) z' 0)
        = fun _ : ℝ => (0 : ℝ) := funext fun z' => ih z'
    show deriv (fun z' : ℝ => Work.Spaces.pzIter n (Work.Spaces.pthIter i f) z' 0) z = 0
    rw [hfun, deriv_const]

/-- The `θ = π/2` slices of `∂_z^j∂_θ^i f` vanish identically for a function vanishing at
`θ ≥ π/2`. -/
theorem pzIter_pthIter_eq_zero_of_forall_ge_pi_half {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Real.pi / 2 ≤ θ → f z θ = 0) (j i : ℕ) (z : ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pthIter i f) z (Real.pi / 2) = 0 := by
  induction j generalizing z with
  | zero => simpa using pthIter_eq_zero_of_forall_ge_pi_half h i z (Real.pi / 2) le_rfl
  | succ n ih =>
    have hfun : (fun z' : ℝ => Work.Spaces.pzIter n (Work.Spaces.pthIter i f) z' (Real.pi / 2))
        = fun _ : ℝ => (0 : ℝ) := funext fun z' => ih z'
    show deriv (fun z' : ℝ =>
      Work.Spaces.pzIter n (Work.Spaces.pthIter i f) z' (Real.pi / 2)) z = 0
    rw [hfun, deriv_const]

/-- The `θ = 0` slices of the mixed operators `D_z^b D_θ^a f` vanish identically for a function
vanishing at `θ ≤ 0`. -/
theorem DzIter_DthIter_eq_zero_of_forall_nonpos {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, θ ≤ 0 → f z θ = 0) :
    ∀ a b z, Work.Spaces.DzIter b (Work.Spaces.DthIter a f) z 0 = 0 := by
  have hD : ∀ a z, Work.Spaces.DthIter a f z 0 = 0 := by
    intro a
    induction a with
    | zero => intro z; exact h z 0 le_rfl
    | succ n ih =>
      intro z
      show Real.sin (2 * 0) * Work.Spaces.pth (Work.Spaces.DthIter n f) z 0 = 0
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero, zero_mul]
  intro a b
  induction b with
  | zero => intro z; simpa using hD a z
  | succ n ih =>
    intro z
    have hfun : (fun z' : ℝ => Work.Spaces.DzIter n (Work.Spaces.DthIter a f) z' 0)
        = fun _ : ℝ => (0 : ℝ) := funext fun z' => ih z'
    show z * deriv (fun z' : ℝ => Work.Spaces.DzIter n (Work.Spaces.DthIter a f) z' 0) z = 0
    rw [hfun, deriv_const, mul_zero]

/-- The `θ = π/2` slices of the mixed operators `D_z^b D_θ^a f` vanish identically for a function
vanishing at `θ ≥ π/2`. -/
theorem DzIter_DthIter_eq_zero_of_forall_ge_pi_half {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Real.pi / 2 ≤ θ → f z θ = 0) :
    ∀ a b z, Work.Spaces.DzIter b (Work.Spaces.DthIter a f) z (Real.pi / 2) = 0 := by
  have hD : ∀ a z, Work.Spaces.DthIter a f z (Real.pi / 2) = 0 := by
    intro a
    induction a with
    | zero => intro z; exact h z (Real.pi / 2) le_rfl
    | succ n ih =>
      intro z
      show Real.sin (2 * (Real.pi / 2))
        * Work.Spaces.pth (Work.Spaces.DthIter n f) z (Real.pi / 2) = 0
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
  intro a b
  induction b with
  | zero => intro z; simpa using hD a z
  | succ n ih =>
    intro z
    have hfun : (fun z' : ℝ => Work.Spaces.DzIter n (Work.Spaces.DthIter a f) z' (Real.pi / 2))
        = fun _ : ℝ => (0 : ℝ) := funext fun z' => ih z'
    show z * deriv (fun z' : ℝ =>
      Work.Spaces.DzIter n (Work.Spaces.DthIter a f) z' (Real.pi / 2)) z = 0
    rw [hfun, deriv_const, mul_zero]

/-! ## The two triangular inversions -/

/-- **Radial inversion.**  At an interior angle, if all the mixed radial derivatives `D_z^b F`
(`b ≤ B`) decay at `+∞` then so do all the plain partials `∂_z^j F` (`j ≤ B`), because
`D_z^n = Σ_{k≤n} S(n,k) z^k ∂_z^k` with `S(n,n) = 1` and `z^k ≥ 1` for `z ≥ 1`. -/
theorem tendsto_pzIter_of_tendsto_DzIter {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {B : ℕ}
    (hD : ∀ b ≤ B, Tendsto (fun z => Work.Spaces.DzIter b F z θ) atTop (𝓝 0)) :
    ∀ j ≤ B, Tendsto (fun z => Work.Spaces.pzIter j F z θ) atTop (𝓝 0) := by
  have hexp : ∀ n (z : ℝ), 0 < z → Work.Spaces.DzIter n F z θ
      = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
          * (z ^ k * Work.Spaces.pzIter k F z θ) := by
    intro n z hz
    exact Work.FTS.GalBasis.Xmb.DzIter_eq_sum_scoef_of_contDiffOn F Work.FTS.EllipticEst.Q0
      Work.FTS.EllipticEst.isOpen_Q0 n (Work.FTS.EllipticEst.SmoothOpen.forall hsm (n + 1)) z θ
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  have key : ∀ j, j ≤ B → ∀ k ≤ j,
      Tendsto (fun z => z ^ k * Work.Spaces.pzIter k F z θ) atTop (𝓝 0) := by
    intro j
    induction j with
    | zero =>
      intro _ k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simpa using hD 0 (Nat.zero_le B)
    | succ n ih =>
      intro hn k hk
      rcases eq_or_lt_of_le hk with heq | hlt
      · subst heq
        have hprev := ih (by omega)
        have hDs : Tendsto (fun z => Work.Spaces.DzIter (n + 1) F z θ) atTop (𝓝 0) :=
          hD (n + 1) hn
        have hsum : Tendsto (fun z => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef (n + 1) k : ℝ) * (z ^ k * Work.Spaces.pzIter k F z θ))
            atTop (𝓝 0) := by
          have hmain : Tendsto (fun z => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef (n + 1) k : ℝ) * (z ^ k * Work.Spaces.pzIter k F z θ))
              atTop (𝓝 (∑ k ∈ Finset.range (n + 1), (0 : ℝ))) := by
            refine tendsto_finsetSum _ (fun k hk => ?_)
            simpa using (hprev k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul
              (↑(Work.Spaces.scoef (n + 1) k))
          simpa using hmain
        have hcomb : Tendsto (fun z => Work.Spaces.DzIter (n + 1) F z θ
              - ∑ k ∈ Finset.range (n + 1),
                  (Work.Spaces.scoef (n + 1) k : ℝ) * (z ^ k * Work.Spaces.pzIter k F z θ))
            atTop (𝓝 0) := by
          simpa using hDs.sub hsum
        refine hcomb.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        show Work.Spaces.DzIter (n + 1) F z θ
            - ∑ k ∈ Finset.range (n + 1),
                (Work.Spaces.scoef (n + 1) k : ℝ) * (z ^ k * Work.Spaces.pzIter k F z θ)
          = z ^ (n + 1) * Work.Spaces.pzIter (n + 1) F z θ
        rw [hexp (n + 1) z hz, Finset.sum_range_succ, scoef_self]
        push_cast
        ring
      · exact ih (by omega) k (by omega)
  intro j hj
  have hzj : Tendsto (fun z => z ^ j * Work.Spaces.pzIter j F z θ) atTop (𝓝 0) :=
    key j hj j le_rfl
  have hnorm : Tendsto (fun z => |Work.Spaces.pzIter j F z θ|) atTop (𝓝 0) := by
    have hgn : Tendsto (fun z => |z ^ j * Work.Spaces.pzIter j F z θ|) atTop (𝓝 0) := by
      simpa [Real.norm_eq_abs] using hzj.norm
    refine squeeze_zero' (Eventually.of_forall (fun z => abs_nonneg _)) ?_ hgn
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz1
    have h1 : (1 : ℝ) ≤ z ^ j := one_le_pow₀ hz1
    calc |Work.Spaces.pzIter j F z θ| = |Work.Spaces.pzIter j F z θ| * 1 := by ring
      _ ≤ |Work.Spaces.pzIter j F z θ| * z ^ j :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |z ^ j * Work.Spaces.pzIter j F z θ| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z) j)]
          ring
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hnorm)

/-- **Angular inversion.**  At an interior angle and for a fixed radial order `j`, if all the
derivatives `∂_z^j D_θ^a F` (`a ≤ A`) decay at `+∞` then so do the plain mixed partials
`∂_z^j∂_θ^i F` (`i ≤ A`), because `D_θ^m = Σ_{r≤m} a_{m,r}(θ) ∂_θ^r` with
`a_{m,m} = sin(2θ)^m ≠ 0` at interior angles. -/
theorem tendsto_pzIter_pthIter_of_tendsto_pzIter_DthIter {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j A : ℕ}
    (hD : ∀ a ≤ A, Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.DthIter a F) z θ)
      atTop (𝓝 0)) :
    ∀ i ≤ A, Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.pthIter i F) z θ)
      atTop (𝓝 0) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hexp : ∀ a (z : ℝ), 0 < z → Work.Spaces.pzIter j (Work.Spaces.DthIter a F) z θ
      = ∑ r ∈ Finset.range (a + 1), Work.FTS.EllipticEst.remov.selfdth.dthCoef a r θ
          * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ := by
    intro a z hz
    exact Work.FTS.GalBasis.Xmb.pzIter_DthIter_expansion (U := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 (N := a + j + 2)
      (Work.FTS.EllipticEst.SmoothOpen.forall hsm (a + j + 2))
      (b := a) (k := j) (by omega) (by omega)
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  have key : ∀ i, i ≤ A → ∀ r ≤ i,
      Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ) atTop (𝓝 0) := by
    intro i
    induction i with
    | zero =>
      intro _ r hr
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      subst hr0
      simpa using hD 0 (Nat.zero_le A)
    | succ n ih =>
      intro hn r hr
      rcases eq_or_lt_of_le hr with heq | hlt
      · subst heq
        have hprev := ih (by omega)
        have hDs : Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.DthIter (n + 1) F) z θ)
            atTop (𝓝 0) := hD (n + 1) hn
        have hsum : Tendsto (fun z => ∑ r ∈ Finset.range (n + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ) atTop (𝓝 0) := by
          have hmain : Tendsto (fun z => ∑ r ∈ Finset.range (n + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ)
              atTop (𝓝 (∑ r ∈ Finset.range (n + 1), (0 : ℝ))) := by
            refine tendsto_finsetSum _ (fun r hr => ?_)
            simpa using (hprev r
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))).const_mul
                (Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ)
          simpa using hmain
        have hcomb : Tendsto (fun z =>
              Work.Spaces.pzIter j (Work.Spaces.DthIter (n + 1) F) z θ
              - ∑ r ∈ Finset.range (n + 1),
                  Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                    * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ) atTop (𝓝 0) := by
          simpa using hDs.sub hsum
        have hscaled : Tendsto (fun z => ((Real.sin (2 * θ)) ^ (n + 1))⁻¹
              * (Work.Spaces.pzIter j (Work.Spaces.DthIter (n + 1) F) z θ
                - ∑ r ∈ Finset.range (n + 1),
                    Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                      * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ)) atTop (𝓝 0) := by
          have := hcomb.const_mul (((Real.sin (2 * θ)) ^ (n + 1))⁻¹)
          simpa using this
        refine hscaled.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have hid : Work.Spaces.pzIter j (Work.Spaces.pthIter (n + 1) F) z θ
            = ((Real.sin (2 * θ)) ^ (n + 1))⁻¹
              * (Work.Spaces.pzIter j (Work.Spaces.DthIter (n + 1) F) z θ
                - ∑ r ∈ Finset.range (n + 1),
                    Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                      * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ) := by
          have hx := hexp (n + 1) z hz
          rw [hx, Finset.sum_range_succ, Work.FTS.EllipticEst.remov.selfdth.dthCoef_self]
          have hsp : Real.sin (2 * θ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hsinpos)
          field_simp
          ring
        exact hid.symm
      · exact ih (by omega) r (by omega)
  intro i hi
  exact key i hi i le_rfl

/-! ## The target -/

theorem decayAll_of_classC {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.ClassC.ClassC α g) (hco : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g) :
    Work.Spaces.DecayAll 4 g := by
  -- `normTh g = g` kills the two endpoint angles
  have hzeroL : ∀ z θ, θ ≤ 0 → g z θ = 0 := by
    intro z θ hθ
    have h1 : g z θ = Work.FTS.ClassC.normTh g z θ := (congrFun (congrFun hg.norm z) θ).symm
    rw [h1, Work.FTS.ClassC.normTh_apply_of_not_mem]
    intro hmem
    exact absurd hmem.1 (not_lt.mpr hθ)
  have hzeroR : ∀ z θ, Real.pi / 2 ≤ θ → g z θ = 0 := by
    intro z θ hθ
    have h1 : g z θ = Work.FTS.ClassC.normTh g z θ := (congrFun (congrFun hg.norm z) θ).symm
    rw [h1, Work.FTS.ClassC.normTh_apply_of_not_mem]
    intro hmem
    exact absurd hmem.2 (not_lt.mpr hθ)
  constructor
  · -- `DecayInZ 4`
    intro j i hij θ hθ
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
      · -- interior angle
        have hθI : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ2⟩
        have hmix : ∀ a b : ℕ, a + b ≤ 4 →
            Tendsto (fun z => Work.Spaces.DzIter b (Work.Spaces.DthIter a g) z θ)
              atTop (𝓝 0) :=
          fun a b hab => Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero hg.tr (by omega) hθI
        have hstep : ∀ a k, a + k ≤ 4 →
            Tendsto (fun z => Work.Spaces.pzIter k (Work.Spaces.DthIter a g) z θ)
              atTop (𝓝 0) := by
          intro a k hak
          have ha : a ≤ 4 := by omega
          refine tendsto_pzIter_of_tendsto_DzIter (B := 4 - a) (hg.reg.DthIter a) hθI ?_ k ?_
          · intro b hb
            exact hmix a b (by omega)
          · omega
        refine tendsto_pzIter_pthIter_of_tendsto_pzIter_DthIter hg.reg hθI (j := j)
          (A := i) ?_ i le_rfl
        · intro a ha
          exact hstep a j (by omega)
      · -- `θ = π/2`
        subst hθ2
        have hfun : (fun z : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i g) z (Real.pi / 2))
            = fun _ : ℝ => (0 : ℝ) :=
          funext fun z => pzIter_pthIter_eq_zero_of_forall_ge_pi_half hzeroR j i z
        rw [hfun]
        exact tendsto_const_nhds
    · -- `θ = 0`
      subst hθ0
      have hfun : (fun z : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i g) z 0)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun z => pzIter_pthIter_eq_zero_of_forall_nonpos hzeroL j i z
      rw [hfun]
      exact tendsto_const_nhds
  · -- `DecayMixed 4`
    intro a b hab θ hθ
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
      · exact Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero hg.tr (by omega) ⟨hθ0, hθ2⟩
      · subst hθ2
        have hfun : (fun z : ℝ => Work.Spaces.mixed b a g z (Real.pi / 2)) =
            fun _ : ℝ => (0 : ℝ) :=
          funext fun z => DzIter_DthIter_eq_zero_of_forall_ge_pi_half hzeroR a b z
        rw [hfun]
        exact tendsto_const_nhds
    · subst hθ0
      have hfun : (fun z : ℝ => Work.Spaces.mixed b a g z 0) = fun _ : ℝ => (0 : ℝ) :=
        funext fun z => DzIter_DthIter_eq_zero_of_forall_nonpos hzeroL a b z
      rw [hfun]
      exact tendsto_const_nhds

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE5Facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The clauses read off the extraction -/


/-- **`bd4`**: the uniform `ℋ⁴`-bound of the limit, from the uniform `ℋ⁴`-bound of the
approximants (lower semicontinuity of the `ℋ⁴`-energy along locally uniform slot convergence).
This is the proved `Xn_le_of_convLocUnif` under the name used by the assembly. -/
theorem EpsLimBd4 {α B C₀ : ℝ} {G : ℕ → Fn} {f : Fn}
    (hconv : ConvLocUnifH6 α B G f)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 4 (G n))
    (hbsq : ∀ n : ℕ, Work.FTS.Nonlin.Xn α (G n) ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 :=
  Xn_le_of_convLocUnif hconv hmem hbsq

/-- **`mem4`**: the honest `ℋ⁴`-membership of the limit, from the slot convergence, the
`ℋ⁶`-membership and uniform `ℋ⁶`-bound of the approximants, and the **per-`z` bound**

  `∀ z ∈ Iz, ∃ Bz, ∀ n, ∫_θ HkIntegrand α 4 (G n) z θ ≤ Bz`

of the approximating sequence.  The per-`z` hypothesis is *not* removable: `HkMem` is a per-`z`
condition while Fatou only gives it a.e. in `z`, and a uniform `ℋ⁶`-bound does not control the
per-`z` slice integrals (the family `G n (z,θ) = ψ n z · θ^{a n}`, `a n ↓ (γ-1)/2`, is the sharp
witness — see `NOTES_session9.md` §3.2). -/
theorem EpsLimMem4 {α B : ℝ} {G : ℕ → Fn} {f : Fn}
    (hconv : ConvLocUnifH6 α B G f)
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (G n)) Work.FTS.EllipticEst.Q0)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (G n) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 4 f ∧ Work.Spaces.HkNorm α 4 f ≤ B := by
  refine HkMem_of_tendsto (k := 4) (m := 6) (by norm_num)
    (fun n => hsm n 4) hconv.contDiffOn ?_ hmem hb hz
  intro j i hji z θ hzθ
  have hK : IsCompact ({(z, θ)} : Set (ℝ × ℝ)) := isCompact_singleton
  have hKQ : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact hzθ
  exact (hconv.conv {(z, θ)} hK hKQ j i hji).tendsto_at (Set.mem_singleton _)

/-! ## The clamped limit family — `init` and `vanish` by definition -/













end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.AngRad5

set_option maxHeartbeats 1600000

/-- **Pointwise separation of an angular profile and a radial function in the `ℋⁿ`-integrand,
`n ≤ 5`.**

This is the level-`n` (`n ≤ 5`) version of `Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le`
(and of `Work.FTS.CoercivityFix.Transfer.E2norm.HkIntegrand_ang_rad_le_n`, which covers `n ≤ 4`).
The proof is the same pointwise computation: the two separation identities
`dzIter_ang_rad`/`mixed_ang_rad` split every iterate of `z ↦ a θ * r z` into the angular factor
`D_θ^i a` times the radial factor `D_z^j r`, the two squared-weight identities
`light_sq_nn`/`heavy_sq_nn` (valid on all of `Iθ`, including the endpoints where `sin(2θ) = 0`)
convert the weights, and the angular factor is bounded termwise using `ha0` and `ha1`.

The sums run over `range (n+1)`, and the angular orders genuinely occurring are `1 ≤ i ≤ n ≤ 5`;
the coefficient `5` is the number of them.  The sum over these orders is extended to all five of
`1..5` (`(range (n+1)).filter (1 ≤ ·) ⊆ (range 6).filter (1 ≤ ·)`) using the nonnegativity of
the summands. -/
theorem HkIntegrand_ang_rad_le5 {n : ℕ} (hn : n ≤ 5) {α : ℝ} {a : ℝ → ℝ} {r : ℝ → ℝ}
    {G : ℝ → ℝ} {B0 B1 : ℝ}
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α n (fun z θ => a θ * r z) z θ
      ≤ (∑ i ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 5 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ
  have hsmGnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
    Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ
  -- ## The angular factor, bounded with the (at most) five available orders
  have hsum_ang : (∑ i ∈ Finset.range (n + 1),
        (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
      ≤ 5 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    rw [← Finset.sum_filter]
    have hcnn : 0 ≤ B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsmGnn
    have hstep : ∀ i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i),
        (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ
          ≤ B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hin, h1⟩ := hi
      have hb := ha1 i h1 (by omega) θ hθ
      have h3 : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
          ≤ B1 ^ 2 * (G θ) ^ 2 := by
        have h4 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        rw [sq_abs, mul_pow] at h4
        exact h4
      exact mul_le_mul_of_nonneg_right h3 hsmGnn
    calc ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i),
            (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ ∑ _i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i),
            B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ :=
          Finset.sum_le_sum hstep
      _ ≤ ∑ _i ∈ (Finset.range 6).filter (fun i => 1 ≤ i),
            B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hcnn)
          intro i hi
          rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact ⟨by omega, hi.2⟩
      _ = 5 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
          rw [show (Finset.range 6).filter (fun i => 1 ≤ i) = Finset.Icc 1 5 from by decide,
            Finset.sum_const, Nat.card_Icc]
          norm_num
          ring
  -- ## The pure `D_z`-slots
  have hpure : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          * (∑ j ∈ Finset.range (n + 1),
              (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
      show (a θ * Work.Elliptic.DzdIter i r z
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = ((a θ * Work.Elliptic.DzdIter i r z)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        from by ring,
      Work.FTS.NonlinRows.AuxAngRad.light_sq_nn _ z θ hs]
    ring
  -- ## The mixed slots
  have hmix : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ (∑ i ∈ Finset.range (n + 1),
            (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
          * (∑ j ∈ Finset.range (n + 1),
              (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    have hterm2 : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i hi j hj
      by_cases h1 : 1 ≤ i
      · by_cases h2 : i + j ≤ n
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
          rw [Work.FTS.Nonlinear.Pieces.mixed_ang_rad,
            show (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
                  * Work.Elliptic.DzdIter j r z * Work.Spaces.Wt α z θ) ^ 2
                = ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
                    * Work.Elliptic.DzdIter j r z) * Work.Spaces.Wt α z θ) ^ 2
              from by ring,
            Work.FTS.NonlinRows.AuxAngRad.heavy_sq_nn α _ z θ hs]
          exact le_of_eq (by ring)
        · rw [if_neg (fun h => h2 h.2), if_pos h1]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) hsmGnn)
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
        simp
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), if 1 ≤ i ∧ i + j ≤ n then
            (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
              * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = (∑ i ∈ Finset.range (n + 1),
              (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
            * (∑ j ∈ Finset.range (n + 1),
                (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          (Finset.sum_mul_sum _ _ _ _).symm
  -- ## Assembly
  have hRnn : 0 ≤ ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hM : (a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        + (∑ i ∈ Finset.range (n + 1),
            (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
      ≤ B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        + 5 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    refine add_le_add ?_ hsum_ang
    have h2 : (a θ) ^ 2 ≤ B0 ^ 2 := by
      have h3 := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha0 θ hθ) 2
      rwa [sq_abs] at h3
    exact mul_le_mul_of_nonneg_right h2 hsmEnn
  calc Work.Spaces.HkIntegrand α n (fun z θ => a θ * r z) z θ
      = (∑ i ∈ Finset.range (n + 1), (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            if 1 ≤ i ∧ i + j ≤ n then
              (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
          rw [Work.Spaces.HkIntegrand]
    _ ≤ (a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          * (∑ j ∈ Finset.range (n + 1),
              (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + (∑ i ∈ Finset.range (n + 1),
              (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
            * (∑ j ∈ Finset.range (n + 1),
                (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
        add_le_add (le_of_eq hpure) hmix
    _ = (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * ((a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + (∑ i ∈ Finset.range (n + 1),
                  (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
                    * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))) := by
        rw [mul_add]
        congr 1
        · exact mul_comm _ _
        · exact mul_comm _ _
    _ ≤ (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 5 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) :=
        mul_le_mul_of_nonneg_left hM hRnn

end Work.FTS.StrongEps.H5.AngRad5
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.lintegral_arctan_exp_subst_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

theorem lintegral_arctan_exp_subst_gen (U : ℝ → ENNReal) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2), U θ)
      = ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.kappa ζ)
          * U (Real.arctan (Real.exp ζ)) := by
  have hmono : MonotoneOn (fun ζ : ℝ => Real.arctan (Real.exp ζ)) Set.univ :=
    strictMono_arctan_exp.monotone.monotoneOn Set.univ
  have hderiv : ∀ ζ ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) (kappa ζ) Set.univ ζ :=
    fun ζ _ => (hasDerivAt_arctan_exp ζ).hasDerivWithinAt
  have h := MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (s := Set.univ) (f := fun ζ : ℝ => Real.arctan (Real.exp ζ)) (f' := kappa)
    MeasurableSet.univ hderiv hmono U
  have hrange : Set.range (fun ζ : ℝ => Real.arctan (Real.exp ζ)) = Set.Ioo 0 (Real.pi / 2) := by
    simpa [Set.image_univ] using range_arctan_exp
  simpa [hrange] using h

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.slot_sq_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/StrongEps/HkSqAux/slot_sq_bound.lean`

The single-slot `L²`-bound behind the `E1` weighted estimates.  If the difference quotient `D`
commutes with the mollifier `J_ε` in the form

  `D (Jeps ρ ε f) z θ = ∫ p, Jker ρ ε p * D f (zShift z p.1) (thShift θ p.2)`

and the weight `W` is almost invariant under the two shifts,
`W z θ ≤ e^{cε} · W (zShift z p.1) (thShift θ p.2)` for every `p`, then

  `(W z θ * D (Jeps ρ ε f) z θ)^2 ≤ e^{2cε} ∫ p, Jker ρ ε p * (W (zShift z p.1) (thShift θ p.2)
      * D f (zShift z p.1) (thShift θ p.2))^2`.

Since `Jker ρ ε` is, by `IsMollKernel`, a *probability* density (nonnegative, total mass `1`,
supported in the ball of radius `ε`), this is Jensen's inequality for the average of the shifted
slot, with the weight ratio `e^{cε}` taken out of the integral.

The proof splits into the two halves of the statement.

* **`abs_slot_le` (the absolute-value bound).**  The shift inequality gives, pointwise,
  `W z θ * |D f (shift p)| ≤ e^{cε} * |W (shift p) * D f (shift p)|` (the shifted weight is
  nonnegative, being `≥ e^{-cε} W z θ ≥ 0`).  Integrating against the nonnegative kernel and
  pulling out the constant `e^{cε}` bounds `|W z θ * D (Jeps ρ ε f) z θ|`.
* **Cauchy–Schwarz.**  `sq_integral_Jker_mul_le` applied to the test function
  `|W (shift ·) * D f (shift ·)|`, whose square is the weight times the square of the slot.

Both integrals are genuine because `Jker ρ ε` is supported in the compact ball of radius `ε`, on
which the relevant test functions are continuous (`hg`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

/-- **The absolute-value half of the slot bound.**  Under the shift inequality for the weight `W`,
the weighted average `W z θ * D (Jeps ρ ε f) z θ` is dominated in absolute value by `e^{cε}` times
the average of `|W (shift p) * D f (shift p)|` against the (probability) kernel.

The proof is monotonicity of the integral for the pointwise inequality
`W z θ * |D f (shift p)| ≤ e^{cε} * |W (shift p) * D f (shift p)|`, together with
`|∫ p, k p * A p| ≤ ∫ p, k p * |A p|` for `k = Jker ρ ε ≥ 0`. -/
theorem abs_slot_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε c : ℝ} (hε : 0 < ε)
    (D : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ) (W f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hcomm : D (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (hWnn : 0 ≤ W z θ)
    (hW : ∀ p : ℝ × ℝ, W z θ ≤ Real.exp (c * ε)
        * W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (hg : ContinuousOn (fun p : ℝ × ℝ =>
        W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    |W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ|
      ≤ Real.exp (c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| := by
  -- the shifted weight is nonnegative, since `0 ≤ W z θ ≤ e^{cε} * W (shift p)`
  have hWsh : ∀ p : ℝ × ℝ,
      0 ≤ W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => nonneg_of_mul_nonneg_right (le_trans hWnn (hW p)) (Real.exp_pos _)
  -- pull the constant `W z θ` inside the integral
  have hX : W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W z θ * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
    rw [hcomm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => by ring)
  -- the pointwise comparison of the two slots
  have hpt : ∀ p : ℝ × ℝ,
      W z θ * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        ≤ Real.exp (c * ε) * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| := by
    intro p
    have h3 : Real.exp (c * ε) * |W (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        = Real.exp (c * ε) * (W (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
            * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) := by
      rw [abs_mul, abs_of_nonneg (hWsh p)]
    rw [h3]
    calc W z θ * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        ≤ (Real.exp (c * ε) * W (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2))
            * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| :=
          mul_le_mul_of_nonneg_right (hW p) (abs_nonneg _)
      _ = Real.exp (c * ε) * (W (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
            * |D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) := by
          ring
  rw [hX]
  calc |∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W z θ * D f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2))|
      ≤ ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p
          * (W z θ * D f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2))| := by
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm
            (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
              * (W z θ * D f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)))
    _ = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W z θ * |D f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)|) := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only
        rw [abs_mul, abs_mul, abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p),
          abs_of_nonneg hWnn]
    _ ≤ ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (Real.exp (c * ε) * |W (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) := by
        refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun p => ?_) ?_
          (Eventually.of_forall fun p => ?_)
        · simp only
          exact mul_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p)
            (mul_nonneg hWnn (abs_nonneg _))
        · exact Work.FTS.StrongEps.HkSqAux.integrable_Jker_mul ρ hρ hε (hg.abs.const_mul _)
        · simp only
          exact mul_le_mul_of_nonneg_left (hpt p)
            (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p)
    _ = Real.exp (c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => by ring)

theorem slot_sq_bound (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε c : ℝ} (hε : 0 < ε)
    (D : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ) (W f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hcomm : D (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (hWnn : 0 ≤ W z θ)
    (hW : ∀ p : ℝ × ℝ, W z θ ≤ Real.exp (c * ε)
        * W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (hg : ContinuousOn (fun p : ℝ × ℝ =>
        W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    (W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ) ^ 2
      ≤ Real.exp (2 * c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
  have hbound := abs_slot_le ρ hρ hε D W f hcomm hWnn hW hg
  -- Cauchy–Schwarz for the probability density `Jker ρ ε`
  have hCS := Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le ρ hρ hε
    (fun p : ℝ × ℝ => |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
        * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) hg.abs
  have hCSeq : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) ^ 2
      ≤ ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * (W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
    simpa only [sq_abs] using hCS
  have hexp : Real.exp (c * ε) ^ 2 = Real.exp (2 * c * ε) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  calc (W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ) ^ 2
      = |W z θ * D (Work.FTS.StrongEps.Jeps ρ ε f) z θ| ^ 2 := by rw [sq_abs]
    _ ≤ (Real.exp (c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hbound 2
    _ = Real.exp (c * ε) ^ 2 * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * |W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) ^ 2 := by
        rw [mul_pow]
    _ ≤ Real.exp (c * ε) ^ 2 * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hCSeq (sq_nonneg _)
    _ = Real.exp (2 * c * ε) * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (W (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
              * D f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
        rw [hexp]

end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12Sub4.QuadAbsLintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12Sub4

/-! ## Elementary regularity facts for the weighted integrand `K(θ)|f z θ|/z` -/

/-- `(z,θ) ↦ |f z θ|` is continuous on the open quadrant as soon as `f` is smooth there. -/
private theorem continuousOn_abs_uncurry {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => |f p.1 p.2|) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hso.continuousOn
  exact hcont.abs

/-- The full weighted integrand `(z,θ) ↦ K(θ)|f z θ|/z` is continuous on the open quadrant
(`z` never vanishes there). -/
private theorem continuousOn_quadWeightedAbs {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * |f p.1 p.2| / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.Coercivity.K_facts_continuous.comp_continuousOn continuous_snd.continuousOn
  exact (hK.mul (continuousOn_abs_uncurry hso)).div continuousOn_fst
    (fun p hp => ne_of_gt hp.1)

/-- **Angular slice integrability.**  For `z > 0` the slice `θ ↦ K(θ)|f z θ|/z` is integrable
on `Iθ`: it is dominated by `(3/(2z))((f z θ)² + 1)`, whose θ-integral is finite by the
`ℋ⁴`-membership hypothesis. -/
private theorem integrableOn_sliceWeightedAbs {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * |f z θ| / z)
      Work.Spaces.Iθ := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn α hso hm hz
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact (continuousOn_const (c := (1 : ℝ))).integrableOn_compact isCompact_Icc
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (3 / (2 * z)) * ((f z θ) ^ 2 + 1)) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2 + 1) Work.Spaces.Iθ :=
      hsl.add hconst
    exact h1.const_mul (3 / (2 * z))
  refine hmaj.mono'
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (continuousOn_quadWeightedAbs hso) hz) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  have hKnn : 0 ≤ Work.Spaces.K θ := Work.Coercivity.K_facts_nonneg θ hθ
  have hKle : Work.Spaces.K θ ≤ 3 := Work.Coercivity.K_facts_le_three θ hθ
  have hval : 0 ≤ Work.Spaces.K θ * |f z θ| / z :=
    div_nonneg (mul_nonneg hKnn (abs_nonneg _)) (le_of_lt hz)
  rw [Real.norm_eq_abs, abs_of_nonneg hval]
  have h1 : Work.Spaces.K θ * |f z θ| / z ≤ 3 * |f z θ| / z := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hz)
    exact mul_le_mul_of_nonneg_right hKle (abs_nonneg _)
  have h2 : 3 * |f z θ| / z = (3 / (2 * z)) * (2 * |f z θ|) := by
    field_simp
  have ham : 2 * |f z θ| ≤ (f z θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|f z θ| - 1), sq_abs (f z θ)]
  have hcz : 0 ≤ 3 / (2 * z) := by positivity
  calc Work.Spaces.K θ * |f z θ| / z ≤ 3 * |f z θ| / z := h1
    _ = (3 / (2 * z)) * (2 * |f z θ|) := h2
    _ ≤ (3 / (2 * z)) * ((f z θ) ^ 2 + 1) := mul_le_mul_of_nonneg_left ham hcz

/-! ## Integrability of the radial density -/

/-- **The radial density `z ↦ ∫_θ K(θ)|f z θ|/z` is integrable on `(0,∞)`.**

The pointwise Cauchy–Schwarz of `L12dens_sq_slice` gives
`|∫_θ K|f|/z| ≤ √3·√(∫_θ f²)/z`; writing `1/z = ((1+z)/z)·(1/(1+z))` shows this is
`√3·√((∫_θ f²)w(z))·(1/(1+z))`, and Young's inequality dominates the product of the two
square-integrable factors `√((∫_θ f²)w)` (finite by `phiWeight_slice_le` + `hm.2`) and
`1/(1+z)` (finite by `InvOneAddSq`). -/
private theorem integrableOn_densityAbs {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
      (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hso.continuousOn
  -- (1) the Hardy-weighted angular energy is integrable
  have hPhi : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hm.2.mono_set Set.Ioi_subset_Ici_self
  have henergy_aesm : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.OpenPkg.l12zero_energy_aesm hcont
  have hfin : MeasureTheory.IntegrableOn
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine hPhi.mono' henergy_aesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg fun θ => sq_nonneg _)
      (sq_nonneg _))]
    exact Work.FTS.H2.L12Q.phiWeight_slice_le α f hm r hr
  -- (2) almost-everywhere strong measurability of the density
  have hdensity_aesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hjoint : MeasureTheory.AEStronglyMeasurable
        (Function.uncurry fun z θ => Work.Spaces.K θ * |f z θ| / z)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_quadWeightedAbs hso)).mono_measure
        (Measure.prod_mono (Measure.restrict_mono_set volume Set.Ioi_subset_Ici_self) le_rfl)
    simpa only [Function.uncurry] using hjoint.integral_prod_right'
  -- (3) an integrable majorant
  have hmaj : MeasureTheory.IntegrableOn
      (fun z : ℝ => 3 * ((∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) * ((1 + z) / z) ^ 2)
        + (1 / (1 + z)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (hfin.const_mul 3).add Work.FTS.H2.InvOneAddSq.1
  refine hmaj.mono' hdensity_aesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
  -- the pointwise domination
  have hz0 : (0 : ℝ) < z := hz
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; exact integral_nonneg fun θ => sq_nonneg _
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn α hso hm hz
  have hslabs : MeasureTheory.IntegrableOn (fun θ : ℝ => |f z θ| ^ 2) Work.Spaces.Iθ :=
    hsl.congr_fun (fun θ _ => (sq_abs (f z θ)).symm) measurableSet_Icc
  have hdens : Work.FM.L12dens Work.Spaces.K (fun z θ => |f z θ|) z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z := by
    rw [Work.FM.L12dens, Work.Spaces.Iθ]
  have hcs := Work.Coercivity.L12dens_sq_slice (fun z θ => |f z θ|)
    Work.Coercivity.integral_Itheta_K hz hslabs
  have hPabs : (∫ θ in Work.Spaces.Iθ, |f z θ| ^ 2) = P := by
    rw [hPdef]
    exact integral_congr_ae (Filter.Eventually.of_forall fun θ => sq_abs (f z θ))
  rw [hPabs, hdens] at hcs
  -- `hcs : (∫_θ K θ |f z θ|/z)^2 ≤ 3 * P / z^2`
  have hstep1 : |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z|
      ≤ Real.sqrt 3 * Real.sqrt P / z := by
    rw [← Real.sqrt_sq_eq_abs (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)]
    refine le_trans (Real.sqrt_le_sqrt hcs) ?_
    rw [Real.sqrt_div (by linarith : (0 : ℝ) ≤ 3 * P), Real.sqrt_sq_eq_abs,
      abs_of_pos hz0, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) P]
  have hstep2 : Real.sqrt 3 * Real.sqrt P / z
      = Real.sqrt 3 * Real.sqrt (P * ((1 + z) / z) ^ 2) * (1 / (1 + z)) := by
    have hsz : Real.sqrt (P * ((1 + z) / z) ^ 2) = Real.sqrt P * ((1 + z) / z) := by
      rw [Real.sqrt_mul hPnn, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) / z)]
    have hkey : Real.sqrt P / z = Real.sqrt (P * ((1 + z) / z) ^ 2) * (1 / (1 + z)) := by
      rw [hsz]
      field_simp
    rw [mul_div_assoc, hkey]
    ring
  have hstep3 : Real.sqrt 3 * Real.sqrt (P * ((1 + z) / z) ^ 2) * (1 / (1 + z))
      ≤ 3 * (P * ((1 + z) / z) ^ 2) + (1 / (1 + z)) ^ 2 := by
    have hu : Real.sqrt (P * ((1 + z) / z) ^ 2) ^ 2 = P * ((1 + z) / z) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg (Real.sqrt 3 * Real.sqrt (P * ((1 + z) / z) ^ 2)
      - (1 / (1 + z)))]
  have hgoal : ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z‖
      ≤ 3 * ((∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) * ((1 + z) / z) ^ 2)
        + (1 / (1 + z)) ^ 2 := by
    rw [Real.norm_eq_abs, ← hPdef]
    exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  exact hgoal

/-! ## The main estimate -/

/-- **The weighted `L¹` size of an `ℋ⁴` profile**, in the quadrant (`dθ dr`, weight `K(θ)/r`):
for `α ∈ (0,1]`, `f` smooth on the open quadrant with honest `ℋ⁴`-membership,

  `∫⁻_z∈(0,∞) ∫⁻_θ∈Iθ ofReal (K(θ) |f z θ| / z) ≤ ofReal (4 ‖f‖_{ℋ⁴})`.

The constant is universal (independent of `α` and `f`).

Hints: everything is nonnegative, so it suffices to bound the corresponding Bochner integrals and
convert with `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`.  The chain is the one of
`Work.FTS.Nonlinear.Pieces.L12_zero_le_weak` / `Work.FTS.OpenPkg.l12zero_field`: by definition
`L₁₂(|f|)(0) = ∫_{r>0} ∫_θ K(θ)|f r θ|/r ≥ 0` (`L12_zero_eq_double` of `Defs`), and
`|L₁₂(|f|)(0)| ≤ 3 √(∫_{r>0} (∫_θ f²) ((1+r)/r)²)` by `L12_zero_le_weak` applied to `|f|` (its two
integrability hypotheses are literally those of `f`: `(∫_θ (|f|)²) = ∫_θ f²`; they are available from
`Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn` and `Work.FTS.H2.L12Q.phiWeight_slice_le` +
`hm.2`), while `∫_{r>0} (∫_θ f²) ((1+r)/r)² ≤ ∫_{r>0}∫_θ HkIntegrand α 4 f = HkSq α 4 f`.
For the `ofReal` conversion one needs integrability of the nonnegative product integrand
`(z,θ) ↦ K θ |f z θ|/z` on `Ioi 0 ×ˢ Iθ`; it is finite by the same Cauchy–Schwarz chain performed at
the level of `∫⁻` (equivalently: `Integrable.mono'` against a majorant whose integral is the finite
quantity above), or one argues that the `lintegral` equals `ofReal` of the Bochner integral once the
latter is finite. -/
theorem QuadAbsLintegral {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.K θ * |f z θ| / z))
      ≤ ENNReal.ofReal (4 * Work.Spaces.HkNorm α 4 f) := by
  -- the estimate is uniform in `α`; the range hypothesis on `α` is not needed
  have _hαpos : (0 : ℝ) < α := hα.1
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hso.continuousOn
  -- integrability of the radial density, and its positivity
  have hdensity : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
      (Set.Ioi (0 : ℝ)) := integrableOn_densityAbs hso hm
  have hnonneg : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz =>
      integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => div_nonneg (mul_nonneg (Work.Coercivity.K_facts_nonneg θ hθ)
          (abs_nonneg _)) (le_of_lt hz))))
  -- the two `ofReal`-conversions
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.K θ * |f z θ| / z))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z) :=
    fun z hz => (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrableOn_sliceWeightedAbs hso hm hz)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        div_nonneg (mul_nonneg (Work.Coercivity.K_facts_nonneg θ hθ) (abs_nonneg _))
          (le_of_lt hz)))).symm
  have houter : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z))
      = ENNReal.ofReal (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * |f z θ| / z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hdensity hnonneg).symm
  -- the estimate for the Bochner integral
  have hbound : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
      ≤ 4 * Work.Spaces.HkNorm α 4 f := by
    have hL12 : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
        = Work.Construction.L12 (fun z θ => |f z θ|) 0 := (L12_zero_eq_double _).symm
    rw [hL12]
    have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        MeasureTheory.IntegrableOn (fun θ : ℝ => (|f r θ|) ^ 2) Work.Spaces.Iθ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact (Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn α hso hm hr).congr_fun
        (fun θ _ => (sq_abs (f r θ)).symm) measurableSet_Icc
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (|f r θ|) ^ 2) * ((1 + r) / r) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      refine (Work.FTS.OpenPkg.l12zero_energy_aesm hcont).congr ?_
      filter_upwards with r
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun θ => (sq_abs (f r θ)).symm)
    have hPhi : MeasureTheory.IntegrableOn
        (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
        (Set.Ioi (0 : ℝ)) := hm.2.mono_set Set.Ioi_subset_Ici_self
    have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        (∫ θ in Work.Spaces.Iθ, (|f r θ|) ^ 2) * ((1 + r) / r) ^ 2
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      rw [integral_congr_ae (Filter.Eventually.of_forall fun θ => sq_abs (f r θ))]
      exact Work.FTS.H2.L12Q.phiWeight_slice_le α f hm r hr
    have hmain := Work.FTS.OpenPkg.l12zero_of_weight_bound
      (f := fun z θ => |f z θ|) hsl hmeas hPhi hbd
    have hHkSq : (∫ r in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f r θ) = Work.Spaces.HkSq α 4 f := by
      rw [Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    rw [hHkSq] at hmain
    have hN : 0 ≤ Work.Spaces.HkNorm α 4 f := Real.sqrt_nonneg _
    calc Work.Construction.L12 (fun z θ => |f z θ|) 0
        ≤ |Work.Construction.L12 (fun z θ => |f z θ|) 0| := le_abs_self _
      _ ≤ 3 * Real.sqrt (Work.Spaces.HkSq α 4 f) := hmain
      _ = 3 * Work.Spaces.HkNorm α 4 f := rfl
      _ ≤ 4 * Work.Spaces.HkNorm α 4 f := by linarith
  calc (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.K θ * |f z θ| / z))
      = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z) :=
        MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi hslice
    _ = ENNReal.ofReal (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * |f z θ| / z) := houter
    _ ≤ ENNReal.ofReal (4 * Work.Spaces.HkNorm α 4 f) := ENNReal.ofReal_le_ofReal hbound

end Work.FTS.StrongEps.L12Sub4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12_lipschitz_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- **Lipschitz (difference) form of the `L₁₂`-zero-mode bound.**

The zero-mode estimate `|L₁₂(f)(0)| ≤ C|f|_{ℋ⁴}` (`Work.FTS.OpenPkg.l12zero_field_all`) is applied
to the difference `f - g`: since `L₁₂` is *additive* on the open class with honest `ℋ⁴`-membership
(`Work.FTS.StrongEps.EComparison.L12_sub_HkMem`) we have
`L₁₂ f(0) - L₁₂ g(0) = L₁₂ (f - g)(0)`, and `HQo α 4 (f - g)` is exactly the hypothesis that lets
the zero-mode bound act on that difference.  The constant is the universal `3` of
`l12zero_field_all`, whose sub-additivity along `f - g` is all that is used. -/
theorem L12_lipschitz_field : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f g : Work.FTS.Galerkin.Fn,
    Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
    Work.FTS.VocabO.HQo α 4 (fun z θ => f z θ - g z θ) →
    |Work.Construction.L12 f 0 - Work.Construction.L12 g 0|
      ≤ C * Work.FTS.Nonlin.Xn α (fun z θ => f z θ - g z θ) := by
  obtain ⟨C, hC, h⟩ := Work.FTS.OpenPkg.l12zero_field_all
  refine ⟨C, hC, ?_⟩
  intro α hα f g hf hg hfg
  -- additivity of `L₁₂` on the open class turns the difference into `L₁₂(f - g)(0)`
  have hsub : Work.Construction.L12 (fun z θ => f z θ - g z θ) 0
      = Work.Construction.L12 f 0 - Work.Construction.L12 g 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hf.1 hg.1 hf.2 hg.2 0
      (by simp [Work.Spaces.Iz])
  rw [← hsub]
  exact h α hα (fun z θ => f z θ - g z θ) hfg

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.Prelim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option autoImplicit false

/-! ## The two smoothness classes -/


/-! ## Support in the radial variable, and the decay it forces -/

/-- `f` vanishes for `z > Z`, uniformly in the angle.  This is the form of "compact support in `z`"
that the strong route's data satisfy (the Galerkin profiles are supported in `z ≤ Z(τ)`), and it is
what makes the sup-norm bounds of `Linf_H2`-type available.  The strict inequality is what makes
every derivative vanish on a *two-sided* neighbourhood of each point of `Ioi Z`. -/
def SupportsInZ (f : Fn) (Z : ℝ) : Prop := ∀ z, Z < z → ∀ θ : ℝ, f z θ = 0


/-- A function vanishing for `z > Z` is (at every fixed angle) eventually zero, hence has limit `0`
at `z = ∞`. -/
theorem SupportsInZ.tendsto {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) (θ : ℝ) :
    Tendsto (fun z => f z θ) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨Z + 1, fun z hz =>
    (h z (by linarith : Z < z) θ).symm⟩)

/-- The pure `z`-derivative of a function vanishing for `z > Z` vanishes there as well. -/
theorem SupportsInZ.pz {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) :
    SupportsInZ (Work.Spaces.pz f) Z := by
  intro z hz θ
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' hz' θ
  rw [Work.Spaces.pz, hev.deriv_eq]
  simp

/-- The pure `θ`-derivative of a function vanishing for `z > Z` vanishes there as well. -/
theorem SupportsInZ.pth {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) :
    SupportsInZ (Work.Spaces.pth f) Z := by
  intro z hz θ
  have hev : (fun θ' => f z θ') = fun _ => (0 : ℝ) := funext fun θ' => h z hz θ'
  rw [Work.Spaces.pth, hev]
  simp

/-- Every iterated mixed derivative `D_z^c D_θ^d f` of a function vanishing for `z > Z` vanishes
there as well. -/
theorem SupportsInZ.mixed {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) (c d : ℕ) :
    SupportsInZ (Work.Spaces.mixed c d f) Z := by
  induction c with
  | zero =>
      induction d with
      | zero => simpa using h
      | succ d ih =>
          intro z hz θ
          have hthis : Work.Spaces.pth (Work.Spaces.DthIter d f) z θ = 0 := ih.pth z hz θ
          show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter d f) z θ = 0
          rw [hthis, mul_zero]
  | succ c ih =>
      intro z hz θ
      have hthis : Work.Spaces.pz (Work.Spaces.mixed c d f) z θ = 0 := ih.pz z hz θ
      show z * Work.Spaces.pz (Work.Spaces.mixed c d f) z θ = 0
      rw [hthis, mul_zero]




/-! ## Rectangles inside the open quadrant -/

/-- **A compact subset of the open quadrant is contained in a product of intervals with positive
endpoints.**  This is the localisation used by `sobolev_C4_bound`: on such a rectangle the weights
`z` and `sin(2θ)` are bounded below, so the pointwise inversion of the mixed operators is bounded. -/
theorem exists_rect_of_compact_subset_Q0 {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d : ℝ, 0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧ d < π / 2 ∧
      K ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, 1, 1, one_pos, le_rfl, one_pos, le_rfl,
      by linarith [Real.pi_gt_three], by simp⟩
  · obtain ⟨p₁, hp₁, hmin₁⟩ := hK.exists_isMinOn hne (continuous_fst.continuousOn)
    obtain ⟨p₂, hp₂, hmax₁⟩ := hK.exists_isMaxOn hne (continuous_fst.continuousOn)
    obtain ⟨p₃, hp₃, hmin₂⟩ := hK.exists_isMinOn hne (continuous_snd.continuousOn)
    obtain ⟨p₄, hp₄, hmax₂⟩ := hK.exists_isMaxOn hne (continuous_snd.continuousOn)
    have hQ₁ : (0 : ℝ) < p₁.1 := (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp₁)).1
    have hQ₃ : (0 : ℝ) < p₃.2 := (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp₃)).2.1
    have hQ₄ : p₄.2 < π / 2 := (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp₄)).2.2
    exact ⟨p₁.1, p₂.1, p₃.2, p₄.2, hQ₁, hmin₁ hp₂, hQ₃, hmin₂ hp₄, hQ₄,
      fun p hp => ⟨⟨hmin₁ hp, hmax₁ hp⟩, ⟨hmin₂ hp, hmax₂ hp⟩⟩⟩

end Work.FTS.StrongLWP
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialBounded6_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `radialBounded6_majorant` — a bounded radial factor is a bounded multiplier on `ℋ⁶`

The claim is purely pointwise.  Let `r : ℝ → ℝ` be a radial factor whose one-dimensional
`D_z`-iterates (`DzdIter`, i.e. `z ↦ (z ∂_z)^k r`) are bounded by `Br` up to order `6`, and let
`g` be `C^∞` on the quadrant.  Then, at every interior point `(z,θ)`,

`HkIntegrand α 6 (r·g) ≤ 10^8 · Br² · HkIntegrand α 6 g`.

The two ingredients are

* the Leibniz rules for a radial factor, `Work.FTS.OpenPkg.leibniz_rad_Dz` and
  `Work.FTS.OpenPkg.leibniz_rad_mixed`:
  `D_z^j(r·g) = ∑_{b≤j} C(j,b) (D_z^b r)(D_z^{j-b} g)` and
  `D_z^jD_θ^i(r·g) = ∑_{b≤j} C(j,b) (D_z^b r)(D_z^{j-b}D_θ^i g)` (all the `D_θ`-derivatives
  fall on `g`, since `r` is constant in `θ`);
* the weighted Cauchy–Schwarz bound `sum_choose_mul_sq_le` for such a Leibniz sum, in which the
  binomial coefficients cost the universal factor `10^6` and every slot
  `D_z^{j-b}D_θ^i g` is priced by the whole integrand `HkIntegrand α 6 g`
  (`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`).

There are `7` pure slots and `7·7 = 49` mixed slots, so the total cost is
`56 · 10^6 ≤ 10^8`.  No smoothness of `g` beyond `C^∞` on the open quadrant is used, and no
integrability at all: the statement is a pointwise majorant of the integrand.
-/

/-- **Weighted Cauchy–Schwarz for a Leibniz sum.**  For `n ≤ 6`, a family `A` bounded by `Br` and
a family `X` whose squares are bounded by `M`, the square of the binomial Leibniz sum
`∑_{b≤n} C(n,b)·(A b·X b)` is at most `10^6 · Br² · M`.

The constant is very generous: `∑_b C(n,b)² ≤ 4096` and the Cauchy–Schwarz cardinal factor is at
most `7`, giving `7 · 4096 · Br² M ≤ 28672 · Br² M ≤ 10^6 · Br² M`. -/
private theorem sum_choose_mul_sq_le {n : ℕ} (hn : n ≤ 6) {Br M : ℝ} (hBr : 0 ≤ Br)
    (hM : 0 ≤ M) {A X : ℕ → ℝ} (hA : ∀ b ≤ n, |A b| ≤ Br) (hX : ∀ b ≤ n, X b ^ 2 ≤ M) :
    (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)) ^ 2
      ≤ 10 ^ 6 * Br ^ 2 * M := by
  -- the sum of the squared binomial coefficients
  have hC : (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2) ≤ 4096 := by
    have h1 : ∀ b ∈ Finset.range (n + 1),
        ((n.choose b : ℝ)) ^ 2 ≤ 64 * ((n.choose b : ℝ)) := by
      intro b _
      have hb2 : n.choose b ≤ 64 := by
        have h : n.choose b ≤ 2 ^ n := Nat.choose_le_two_pow n b
        have h2 : 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
        omega
      have hc0 : (0 : ℝ) ≤ (n.choose b : ℝ) := Nat.cast_nonneg _
      have hc64 : ((n.choose b : ℝ)) ≤ 64 := by exact_mod_cast hb2
      nlinarith
    calc (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2)
        ≤ ∑ b ∈ Finset.range (n + 1), 64 * ((n.choose b : ℝ)) := Finset.sum_le_sum h1
      _ = 64 * ∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) := by rw [Finset.mul_sum]
      _ = 64 * (2 : ℝ) ^ n := by
            rw [← Nat.cast_sum, Nat.sum_range_choose]
            push_cast
            ring
      _ ≤ 4096 := by
            have h2n : (2 : ℝ) ^ n ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hn
            norm_num at h2n ⊢
            linarith
  -- Cauchy–Schwarz with the binomial weights
  have hcs : (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2
      ≤ (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2)
        * ∑ b ∈ Finset.range (n + 1), |X b| ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1)) _ _
  rw [show (∑ b ∈ Finset.range (n + 1), |X b| ^ 2)
      = ∑ b ∈ Finset.range (n + 1), X b ^ 2 from
        Finset.sum_congr rfl fun b _ => sq_abs (X b)] at hcs
  have h2 : (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2
      ≤ 4096 * ∑ b ∈ Finset.range (n + 1), X b ^ 2 :=
    le_trans hcs (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun b _ => sq_nonneg _))
  -- each square is bounded by `M`
  have h3 : ∑ b ∈ Finset.range (n + 1), X b ^ 2 ≤ ((n + 1 : ℕ) : ℝ) * M := by
    calc ∑ b ∈ Finset.range (n + 1), X b ^ 2
        ≤ ∑ _b ∈ Finset.range (n + 1), M :=
          Finset.sum_le_sum fun b hb => hX b (by simpa [Finset.mem_range] using hb)
      _ = ((n + 1 : ℕ) : ℝ) * M := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h3' : ∑ b ∈ Finset.range (n + 1), X b ^ 2 ≤ 7 * M := by
    refine le_trans h3 ?_
    have hn7 : ((n + 1 : ℕ) : ℝ) ≤ 7 := by
      have : n + 1 ≤ 7 := by omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hn7 hM
  -- the absolute-value bound on the Leibniz sum
  have h1 : |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)|
      ≤ Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b| := by
    calc |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)|
        ≤ ∑ b ∈ Finset.range (n + 1), |(n.choose b : ℝ) * (A b * X b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |A b * X b| := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose b))]
      _ = ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (|A b| * |X b|) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [abs_mul]
      _ ≤ ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (Br * |X b|) := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hb' : b ≤ n := by simpa [Finset.mem_range] using hb
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hA b hb') (abs_nonneg _))
            (Nat.cast_nonneg (n.choose b))
      _ = Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
  calc (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)) ^ 2
      = |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = Br ^ 2 * (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2 := by ring
    _ ≤ Br ^ 2 * (4096 * ∑ b ∈ Finset.range (n + 1), X b ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg Br)
    _ ≤ Br ^ 2 * (4096 * (7 * M)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Br)
        exact mul_le_mul_of_nonneg_left h3' (by norm_num)
    _ ≤ 10 ^ 6 * Br ^ 2 * M := by
        have hB2 : (0 : ℝ) ≤ Br ^ 2 := sq_nonneg Br
        nlinarith [hB2, hM]

theorem radialBounded6_majorant :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (Br : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z) →
      Work.FTS.EllipticEst.SmoothOpen g → 0 ≤ Br →
      (∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter b r z| ≤ Br) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 6 (fun z θ => r z * g z θ) z θ
          ≤ K * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α r g Br hr hg hBr hbdd z θ hz hθ0 hθ1
  have hzI : z ∈ Set.Ioi (0 : ℝ) := hz
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHg : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hM0 : (0 : ℝ) ≤ 10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Br)) hHg
  -- the pure `D_z` slot, priced by the whole integrand
  have hz1 : ∀ i : ℕ, i ≤ 6 →
      (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ 10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro i hi
    have hleib := Work.FTS.OpenPkg.leibniz_rad_Dz r g hr hg i z hzI θ hθI
    have hfac : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (i - b) g z θ))
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hleib, hfac]
    exact sum_choose_mul_sq_le (n := i) hi hBr hHg
      (fun b hb => hbdd b (by omega) z hz.le)
      (fun b hb => Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ (i - b) (by omega))
  -- the mixed slots, priced by the whole integrand
  have hm1 : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 6 →
      (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ 10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro i j hi hij
    have hleib := Work.FTS.OpenPkg.leibniz_rad_mixed r g hr hg j i hi z hzI θ hθI
    have hfac : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ))
          * Work.Spaces.Wt α z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hleib, hfac]
    exact sum_choose_mul_sq_le (n := j) (by omega) hBr hHg
      (fun b hb => hbdd b (by omega) z hz.le)
      (fun b hb => Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ i (j - b) hi (by omega))
  -- the two sums
  have hS1 : (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
    have h := Finset.sum_le_card_nsmul (Finset.range (6 + 1))
      (fun i => (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
      (fun i hi => hz1 i (by have h := Finset.mem_range.mp hi; omega))
    refine le_trans h (le_of_eq ?_)
    rw [Finset.card_range, nsmul_eq_mul]
    norm_num
  have hS2 : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
        if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 49 * (10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
    have hinner : ∀ i : ℕ, (∑ j ∈ Finset.range (6 + 1),
          if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ 7 * (10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
      intro i
      have h := Finset.sum_le_card_nsmul (Finset.range (6 + 1))
        (fun j => if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        (10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
        (fun j _ => by
          split_ifs with hguard
          · exact hm1 i j hguard.1 hguard.2
          · exact hM0)
      refine le_trans h (le_of_eq ?_)
      rw [Finset.card_range, nsmul_eq_mul]
      norm_num
    calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range (6 + 1),
            (7 * (10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)) :=
          Finset.sum_le_sum fun i _ => hinner i
      _ = 49 * (10 ^ 6 * Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hunf : Work.Spaces.HkIntegrand α 6 (fun z θ => r z * g z θ) z θ
      = (∑ i ∈ Finset.range (6 + 1),
            (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
            if 1 ≤ i ∧ i + j ≤ 6 then
              (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0 := rfl
  rw [hunf]
  refine le_trans (add_le_add hS1 hS2) ?_
  have h1 : (0 : ℝ) ≤ Br ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ :=
    mul_nonneg (sq_nonneg Br) hHg
  nlinarith [h1]

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.contHkAngRad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Continuity of the `ℋ^k`-integrand of an angular `×` radial product

`HkIntegrand α k (fun z θ => a θ * r z)` is continuous on the open quadrant as soon as
the angular iterates `D_θ^i a` (`i ≤ k`) are continuous on `(0,π/2)` and the radial
iterates `D_z^b r` (`b ≤ k`) are continuous on `(0,∞)`.

The two unconditional separation identities `dzIter_ang_rad` / `mixed_ang_rad` rewrite the
iterates of the product `(z,θ) ↦ a θ · r z` as products of the iterates of the two
factors; the weights `w z` and `Wt α z θ` are continuous on the open quadrant (where
`z ≠ 0` and `sin(2θ) > 0`), so every summand is continuous.

This is the general-`k` form of the `k = 4` statement proved (privately) in
`Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le`. -/

private lemma continuousOn_mul_apply {f g : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun p => f p * g p) s :=
  (hf.mul hg).congr (fun p _ => (Pi.mul_apply f g p).symm)

private lemma continuousOn_pow_apply {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (fun p => f p ^ n) s :=
  (hf.pow n).congr (fun p _ => (Pi.pow_apply f n p).symm)

private lemma continuousOn_w_angRad :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  simp only [Work.Spaces.w]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

private lemma continuousOn_sinpow_angRad (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt
      (Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hp.2)))

private lemma continuousOn_wdivsin_angRad :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  continuousOn_w_angRad.div (continuousOn_sinpow_angRad (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos
      (Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hp.2) _))

private lemma continuousOn_Wt_angRad (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine (continuousOn_w_angRad.mul (continuousOn_sinpow_angRad (-(Work.Spaces.gam α / 2)))).congr
    (fun p _ => ?_)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, Pi.mul_apply]

theorem contHkAngRad (k : ℕ) (α : ℝ) (a r : ℝ → ℝ)
    (hcontA : ∀ i : ℕ, i ≤ k → ContinuousOn
      (fun θ : ℝ => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hcontR : ∀ b : ℕ, b ≤ k → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k (fun z θ => a θ * r z)
      p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hA0 : ContinuousOn (fun θ : ℝ => a θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hcontA 0 (Nat.zero_le k)).congr (fun θ _ => by simp)
  have hA : ContinuousOn (fun p : ℝ × ℝ => a p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hA0.comp continuousOn_snd (fun p hp => hp.2)
  have hDzd : ∀ b : ℕ, b ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b r p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun b hb => (hcontR b hb).comp continuousOn_fst (fun p hp => hp.1)
  have hDth : ∀ i : ℕ, i ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun i hi => (hcontA i hi).comp continuousOn_snd (fun p hp => hp.2)
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (a p.2 * Work.Elliptic.DzdIter i r p.1
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0) ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ (fun i hi => ?_)
      have h1 : ContinuousOn (fun p : ℝ × ℝ =>
          a p.2 * Work.Elliptic.DzdIter i r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_mul_apply hA (hDzd i (by have := Finset.mem_range.mp hi; omega))
      have h2 : ContinuousOn (fun p : ℝ × ℝ =>
          (a p.2 * Work.Elliptic.DzdIter i r p.1)
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_mul_apply h1 continuousOn_wdivsin_angRad
      exact continuousOn_pow_apply h2 2
    · refine continuousOn_finsetSum _ (fun i hi => continuousOn_finsetSum _ (fun j hj => ?_))
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · have hfun : (fun p : ℝ × ℝ =>
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0)
            = fun p : ℝ × ℝ =>
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2 := by
          funext p; rw [if_pos h]
        rw [hfun]
        have h1 : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
              * Work.Elliptic.DzdIter j r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_mul_apply (hDth i (by have := Finset.mem_range.mp hi; omega))
            (hDzd j (by have := Finset.mem_range.mp hj; omega))
        have h2 : ContinuousOn (fun p : ℝ × ℝ =>
            (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
              * Work.Elliptic.DzdIter j r p.1) * Work.Spaces.Wt α p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_mul_apply h1 (continuousOn_Wt_angRad α)
        exact continuousOn_pow_apply h2 2
      · have hfun : (fun p : ℝ × ℝ =>
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0) = fun _ : ℝ × ℝ => (0 : ℝ) := by
          funext p; rw [if_neg h]
        rw [hfun]
        exact continuousOn_const
  · intro p _hp
    simp only [Work.Spaces.HkIntegrand, Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
      Work.FTS.Nonlinear.Pieces.mixed_ang_rad]

end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.RMul6.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.RMul6

open Work.FTS.EllipticEst (SmoothOpen Q0)
open Work.FTS.Nonlinear.RadialProd (Qg smE PsiZ psiZ Kth)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The radial density of the level-six norm -/

/-- `Rint6 r z = Σ_{i ≤ 6} (D_z^i r z)² w(z)²`: the radial density of the `ℋ⁶`-norm of the
radial lift of `r`. -/
def Rint6 (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2


theorem Rint6_nonneg (r : ℝ → ℝ) (z : ℝ) : 0 ≤ Rint6 r z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)



/-! ## `Rr6` against the level-six norm of the radial lift -/




/-! ## Integrability -/



/-! ## The radial Hardy bound at level six -/


/-! ## The `Qg`-slots -/



end Work.FTS.StrongPersist.RMul6
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2S_coef2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


/-! ## The repaired bundle and input -/

/-- The repaired `f`-side bundle: `CoefThMem 2 f` in place of `CoefThMem 1 f`. -/
def T2SF2 (α : ℝ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α 4 f
    ∧ Work.FTS.VocabO.CoefThMem 2 f

theorem T2SF2.smoothOpen {α : ℝ} {f : Fn} (h : T2SF2 α f) :
    Work.FTS.EllipticEst.SmoothOpen f := h.1
theorem T2SF2.hk {α : ℝ} {f : Fn} (h : T2SF2 α f) : Work.Spaces.HkMem α 4 f := h.2.1







end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXB.sup_bound_all_alpha`

The pointwise `L^∞`–`ℋ⁴` trade-off of Elgindi's Corollary `SecondDerivativesBounded` in its
**`α`-free** form: for every `α > 0` there is `C = C(α) > 0` with

  `f(z,θ)² ≤ C · |f|²_{ℋ⁴}`

for every `f` which is `C^∞` on the open quadrant (`SmoothOpen`), honestly in `ℋ⁴`
(`HkMem α 4`) and satisfies the boundary-trace vanishing `BdryTraces α 4`, at every point
`z > 0`, `0 < θ < π/2` of the open quadrant.

The available port of the Corollary to the open class
(`Work.FTS.StrongEps.SupPort.mixed_abs_le_of_smoothOpen`) is stated only for `α ≤ 1`, because
the two ingredients `HardyThetaOpen` and `sin_two_rpow` are (`sin_two_rpow` needs
`γ - 2 ≤ 0`).  Here the angular Hardy inequality is used in the form
`Work.FTS_RegExport.RXB.SupGen.thetaHardyGen`, which carries the *abstract* constant `K` in
place of `100/(γ-1)`; the concrete choice

  `K = max (100/(γ-1)) (π/2)`

is supplied by `sin_two_rpow_max` below (`∫_{Iθ} sin(2σ)^p ≤ π/2` for `p ≥ 0`, since `sin ≤ 1`
on `Iθ`; the constant `100/(p+1)` alone is false for large positive `p`).  With that, the
whole chain of `mixed_abs_le_of_smoothOpen` — `slotM_open` for the `(1,1)`-slot, the angular
Hardy inequality, the radial Hardy inequality `mixed_slice_hardyZ_open` and the identification
of the two weighted slots — goes through verbatim for an arbitrary `α > 0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXB

set_option autoImplicit false

/-- **The weighted angular integral bound, for every `p > -1`.**
`∫_{Iθ} sin(2θ)^p dθ ≤ max (100/(p+1)) (π/2)`: for `p ≤ 0` this is
`Work.Spaces.sin_two_rpow`, and for `p ≥ 0` the integrand is bounded by `1` on the interval
`Iθ` of length `π/2`.  (The constant `100/(p+1)` alone is *false* for large positive `p`:
`∫_{Iθ} sin(2θ)^p ∼ c/√p` while `100/(p+1) ∼ 100/p`.) -/
theorem sin_two_rpow_max (p : ℝ) (hp : -1 < p) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p
        ≤ max (100 / (p + 1)) (Real.pi / 2) := by
  have hvol : MeasureTheory.volume Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  rcases lt_or_ge p 0 with hp0 | hp0
  · obtain ⟨hi, hv⟩ := Work.Spaces.sin_two_rpow p hp (le_of_lt hp0)
    exact ⟨hi, le_trans hv (le_max_left _ _)⟩
  · have hbdd : ∀ θ ∈ Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p ≤ 1 := fun θ hθ =>
      Real.rpow_le_one (Work.FTS.H2.sin_two_nonneg hθ) (Real.sin_le_one _) hp0
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Measurable.pow_const
        (Real.measurable_sin.comp (measurable_const.mul measurable_id)) p).aestronglyMeasurable
    have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
        Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.of_bound hvol hmeas 1 ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hθ) p)]
      exact hbdd θ hθ
    refine ⟨hint, ?_⟩
    have hone : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
        Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p
        ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) :=
          MeasureTheory.setIntegral_mono_on hint
            (MeasureTheory.integrableOn_const (ne_of_lt hvol) (by simp)) measurableSet_Icc hbdd
      _ = Real.pi / 2 := hone
      _ ≤ max (100 / (p + 1)) (Real.pi / 2) := le_max_right _ _

/-- **The algebraic identity behind the angular Hardy inequality, in the interior.**
On `0 < θ < π/2` (where `sin(2θ) > 0`) the `∂_θ`-slot with the weight `sin(2θ)^{2-γ}` equals
the `D_θ`-slot with the weight `sin(2θ)^{-γ}`.  Unlike `Work.FTS.H2.pth_sq_mul_sin_eq` the
identity is asserted for *every* `α` (and only off the endpoints `θ = 0, π/2`, where the two
sides can genuinely differ when `γ = 2`). -/
theorem pth_sq_mul_sin_eq_Ioo (α : ℝ) (u : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.pth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth u z θ) ^ 2 := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hθ
  have hD : Work.Spaces.Dth u z θ = Real.sin (2 * θ) * Work.Spaces.pth u z θ := rfl
  rw [hD, mul_pow, show 2 - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
    Real.rpow_add hs, Real.rpow_two]
  ring

theorem sup_bound_all_alpha {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlin.BdryTraces α 4 f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (f z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 4 f := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hK0 : 0 ≤ max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2) :=
    le_trans hπ (le_max_right _ _)
  refine ⟨max (max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro f hF hmem hbd z θ hz hθ0 hθ1
  -- the angular Hardy constant
  have hp1 : -1 < Work.Spaces.gam α - 2 := by rw [Work.Spaces.gam]; linarith
  obtain ⟨hSint, hSval₀⟩ := sin_two_rpow_max (Work.Spaces.gam α - 2) hp1
  have hSval : ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)
      ≤ max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2) := by
    refine le_trans hSval₀ ?_
    rw [show Work.Spaces.gam α - 2 + 1 = Work.Spaces.gam α - 1 by ring]
  -- the `(1,1)`-slot of `HkSq`, in the `θ`-first form
  have hγne : Work.Spaces.gam α ≠ 0 := ne_of_gt (by linarith : 0 < Work.Spaces.gam α)
  obtain ⟨hTle, hTint, hTae⟩ :=
    Work.FTS.StrongEps.SupPort.slotM_open α f hF hmem 1 1 (by norm_num) (by norm_num)
  have hptslot : ∀ σ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      (Work.Spaces.mixed 1 1 f z σ * Work.Spaces.Wt α z σ) ^ 2
        = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * ((Work.Spaces.mixed 1 1 f z σ) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro σ hσ z
    rw [show Work.Spaces.Wt α z σ
        = Work.Spaces.w z * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) from rfl,
      mul_pow, Work.FTS.H2.Wt_sq α hα z σ hσ]
    ring
  set B : ℝ → ℝ := fun σ => ∫ z in Work.Spaces.Iz,
    (Work.Spaces.mixed 1 1 f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 with hBdef
  have hBae : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun σ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed 1 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    filter_upwards [hTae, MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with σ _ hσI
    rw [hBdef]
    have hstep : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (∫ z in Work.Spaces.Iz,
              (Work.Spaces.mixed 1 1 f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
        = ∫ z in Work.Spaces.Iz,
            (Work.Spaces.mixed 1 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ici fun z _ => (hptslot σ hσI z).symm
    exact hstep
  have hTint' : MeasureTheory.Integrable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hTint.congr hBae.symm
  set T : ℝ := ∫ σ in Work.Spaces.Iθ,
    (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ with hTdef
  have hTle' : T ≤ Work.Spaces.HkSq α 4 f := by
    rw [hTdef]
    rw [show (∫ σ in Work.Spaces.Iθ,
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
        = ∫ σ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
            (Work.Spaces.mixed 1 1 f z σ * Work.Spaces.Wt α z σ) ^ 2
        from integral_congr_ae hBae]
    exact hTle
  -- the angular vanishing at `θ = 0⁺`, from the boundary traces
  have hlim0 : Tendsto (fun θ' => f z θ') (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := (hbd 0 0 (by norm_num)).2 z (Set.mem_Ioi.mpr hz)
    exact Work.FTS.H2.tendsto_nhdsGT_zero_of_traces α hα (by simpa using h.1)
  -- the angular integrability of the `∂_θ`-slot
  have hint_ang : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.FTS.TransportS.T2SupB2.integrableOn_pth_sq_rpow hF hmem 0 0 (by norm_num) hz
  -- the angular Hardy inequality
  have hHT : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2), (f z θ') ^ 2
      ≤ max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2)
        * ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
    SupGen.thetaHardyGen hα (max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2)) hK0 f z
      hF hz hlim0 hint_ang hSint hSval
  -- the `D_θ`-slot with the weight `sin^{-γ}` is integrable
  have hDth_int2 : MeasureTheory.IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth f z σ) ^ 2) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.Integrable (fun σ => (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint_ang
    refine h1.congr ?_
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
    exact pth_sq_mul_sin_eq_Ioo α f hσ
  have hI1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.Dth f z σ) ^ 2 :=
    Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo
      (fun σ hσ => pth_sq_mul_sin_eq_Ioo α f hσ)
  -- the radial Hardy inequality at a.e. angle
  have hrad : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.Dth f z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ := by
    filter_upwards [hTae, MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with σ hσint hσI
    rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
    · have hsin0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
    · have hsin0 : Real.sin (2 * σ) = 0 := by
        rw [hσeq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    · have hσ' : σ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hσpos, hσlt⟩
      have hDth_eq : Work.Spaces.Dth f z σ = Work.Spaces.mixed 0 1 f z σ :=
        Work.FTS.StrongEps.SupPort.Dth_mixed_open hF 0 0 hz hσ'
      rw [hDth_eq]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.StrongEps.SupPort.mixed_slice_hardyZ_open α f hF hbd 0 1 (by norm_num)
          hσ' hσint z (Set.mem_Ioi.mpr hz))
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσI) _)
  have hIntLe : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) ≤ T := by
    rw [hI1, hTdef]
    exact integral_mono_ae hDth_int2 hTint' hrad
  have hfin : (f z θ) ^ 2 ≤ max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2) * T :=
    le_trans (hHT θ ⟨hθ0, hθ1⟩) (mul_le_mul_of_nonneg_left hIntLe hK0)
  exact le_trans (le_trans hfin (mul_le_mul_of_nonneg_left hTle' hK0))
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Work.Spaces.HkSq_nonneg α 4 f))

end Work.FTS_RegExport.RXB
end
end
