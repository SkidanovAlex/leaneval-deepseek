import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.TT.Shim.DzPsiAux
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.sin2_parseval_aesm
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.T3Q.Msurv_abs_le_Q
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.L12Add
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.HkIntegrand_integral_le_pth2_half =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
**The per-`z` angular Poincaré comparison `f` vs `∂_θ²f` in the half-strip class.**

This is the port of the *already proved* `Work.FTS.EllipticEst.Blocks.HkIntegrand_integral_le_pth2`
(`Submission/Work/FTS/EllipticEst/Blocks/HkIntegrand_integral_le_pth2.lean`, sorry-free) from the
hypothesis `Work.Spaces.SmoothNbhd f` to the weaker, provable hypothesis
`Work.FTS.EllipticEst.SmoothHalf f` (see `Submission/Work/FTS/EllipticEst/HalfSmooth.lean`).

WHY it is needed: `SmoothNbhd` (`C^∞` on a 2D neighbourhood of the closed quadrant, hence on
`z < 0`) is FALSE for the straightened residual `Ξ = EllResid α F Ψ`, while `SmoothHalf Ξ` holds.

ROUTE: copy the proof of the original file and replace the hypothesis `SmoothNbhd f` by
`SmoothHalf f`, using the half-strip layer `Submission/Work/Blocks/SmoothHalfAux.lean`
(namespace `Work.FTS.EllipticEst.HalfU`, all sorry-free).  In the original proof everything after
the split `rcases eq_or_lt_of_le hz0 with hzeq | hzpos` runs in the branch `0 < z`, exactly the
regime in which the half-strip layer applies; `hsm.halfAn : HalfU.HalfAn f` is the second
conjunct of `SmoothHalf` (`ContDiffOn ℝ ⊤ (Function.uncurry f) (Ioi 0 ×ˢ Ioo (-1) (π/2+1))`).
Dictionary of replacements:

* `SmoothNbhd.DzIter hsm j` + `sliceSmooth_of_SmoothNbhd … hz` ↦ `HalfU.HalfAn.slice_DzIter hsm.halfAn j hzpos`;
* `sliceV_DzIter hsm j hz hθ` ↦ `HalfU.sliceV_DzIter hsm.halfAn j hzpos hθ`;
* `LopIter_sliceV_DzIter_eq_mixed hsm j m hz hθ` ↦ `HalfU.LopIter_sliceV_DzIter_eq_mixed hsm.halfAn j m hzpos hθ`;
* the private `mixed_eq_LopIter` (built from `DthIter_DzIter`) ↦ `HalfU.LopIter_DzIter_eq_mixed hsm.halfAn j i hzpos hθ`;
* `integrableOn_HkIntegrand_terms α k (pthIter 2 f) (hsm.pth.pth) hz …` ↦
  `HalfU.integrableOn_HkIntegrand_terms_half α k (pthIter 2 f) (hsm.halfAn.pthIter 2) hzpos …`;
* `Blocks.slice_data_integrable_of_HkIntegrand α k f hsm hzpos j hj …` ↦
  `HalfU.slice_data_integrable_of_HkIntegrand_half α k f hsm.halfAn hzpos j hj …`.

Everything else (`DzIter_boundary_zero hvan j`, `HkIntegrand_eq_slice_sum`, `sliceGroup`, `sliceA`,
`slicePhi`, `Sq_le_HkIntegrand_z`, `sq_le_HkIntegrand_mixed`, `integral_mono_of_nonneg`, the
`Sfun`/`Bdom` helpers and the arithmetic) is unchanged, and so is the `hC1` hypothesis verbatim:
the angular slices of `DzIter j f` at a level `z > 0` ARE `SliceSmooth` because `SmoothHalf`'s
second conjunct is smoothness on the half-strip `(0,∞) × (-1, π/2+1)`.
-/
/-! ## Auxiliary vocabulary for the proof

`Sfun` is the sum of the three fixed integrable angular weights produced by the boundary
conditions in `slicePhi`; `Bdom` is the dominating function by which a single angular
integrand (at a fixed radial level `z`, with a fixed value `M` of the `H^k`-integral of
`∂_θ² f`) is bounded. -/

/-- `Sfun α θ = sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ}`: the three fixed integrable
terms attached to `sliceA u` in `slicePhi`. -/
private def Sfun (α θ : ℝ) : ℝ :=
  Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
    + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)










end Work.Blocks
end
end
-- ===== merged: Submission.Work.Blocks.StripMajorantAux.mixIntS_dzIter_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the radial slice functionals `mixIntS (D_z^r V)`

The majorant of the mixed-derivative interpolation estimate contains, for each `r ≤ k`, the
radial slice functional

`mixIntS (D_z^r V) z = w(z)² ∫_θ (D_z ∂_θ (D_z^r V) z θ)² σ_η(θ) dθ`

(`Submission/Work/EllipticEst/Core/Defs.lean`).  This module shows that this function of `z` is
integrable on `Iz = [0,∞)` as soon as `V` is `C^∞` on the open quadrant and the single function
`D_z ∂_θ V` lies in the weighted space `ℋ^k` (`Work.Spaces.HkMem`).

The argument is purely a *slicewise comparison with the `ℋ^k`-integrand*:

* for `z > 0` the derivative block `D_z ∂_θ (D_z^r V)` equals `D_z^r (D_z ∂_θ V)` (Clairaut plus
  the commutation of `∂_θ` with the iterates of `D_z` on the open quadrant);
* the square identity `(D · (w / σ^{η/2}))² = D² w² σ^{-η}` turns the slice integrand into the
  `i = r` summand of `HkIntegrand α k (D_z ∂_θ V)`, which is `≤ HkIntegrand` by
  `Work.Spaces.sq_le_HkIntegrand_z`;
* the generic honesty step `Work.EllipticEst.Core.i0Aux.integrableOn_of_slice_le` converts this
  domination (`HkMem` is exactly integrability of the `θ`-integral of `HkIntegrand`) plus
  a.e. strong measurability (from `Work.EllipticEst.Core.v2_aesm_integral`) into integrability.

Nothing here uses `sorry`; the module rests on `[propext, Classical.choice, Quot.sound]`.
-/
namespace Work.Blocks.StripMajorantAux

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Nonnegativity of the slice functional -/

/-- `mixIntS u z ≥ 0`: it is the product of the nonnegative weight `w(z)²` with the `θ`-integral
of the nonnegative integrand `(D_z ∂_θ u)² σ_η`. -/
theorem mixIntS_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.EllipticEst.Core.mixIntS u z := by
  rw [Work.EllipticEst.Core.mixIntS]
  refine mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae ?_)
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ))

/-! ## The `θ`-slice identity -/

/-- For `z > 0`, the derivative block `D_z ∂_θ (D_z^r V)` equals the `r`-th iterate of the fixed
block `D_z ∂_θ V`: `∂_θ` commutes with `D_z^r` on the open quadrant, and `D_z` commutes with its
own iterates. -/
theorem Dz_pth_DzIter_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.pth V)) z θ := by
  -- Clairaut on the open quadrant: `∂_θ (D_z^r V) = D_z^r (∂_θ V)`
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter r V)))
      (Function.uncurry (Work.Spaces.DzIter r (Work.Spaces.pth V)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall V).mp hV) r
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ1, hθ2⟩
  -- `D_z` of the two functions agrees (its `deriv` sees only a neighbourhood)
  have h1 : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ := by
    show z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ
    rw [Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hmem]
  have h2' : Work.Spaces.DzIter (r + 1) (Work.Spaces.pth V)
      = Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.pth V)) := by
    rw [Work.Spaces.DzIter_add_right r 1]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have h2 : Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.pth V)) z θ := by
    rw [← congrFun (congrFun (Work.Spaces.DzIter_succ r (Work.Spaces.pth V)) z) θ,
      congrFun (congrFun h2' z) θ]
  rw [h1, h2]

/-- **The slice identity for the radial family.**  For `z > 0`, `mixIntS (D_z^r V) z` is the
`θ`-integral of the weighted square of the *fixed* block `D_z^r (D_z ∂_θ V)`. -/
theorem mixIntS_dzIter_slice_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z : ℝ} (hz : 0 < z) :
    Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.pth V)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  -- step 1: purely algebraic rewriting of the `θ`-integrand (no positivity of `z` needed)
  have h1 : Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Work.EllipticEst.Core.mixIntS, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    simp only [Work.FTS.EllipticEst.thEta]
    rw [Work.EllipticEst.Core.i0Aux.mul_div_rpow_sq_eq
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']
    ring
  rw [h1]
  -- step 2: identify the derivative block a.e. in `θ` (the endpoints are null)
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Dz_pth_DzIter_eq hV r hz hθ.1 hθ.2]

/-! ## Domination by the `ℋ^k`-integrand -/

/-- **Slicewise domination.**  For `r ≤ k` and `z > 0`, the slice functional
`mixIntS (D_z^r V) z` is bounded by the `θ`-integral of the `ℋ^k`-integrand of the fixed block
`D_z ∂_θ V`: the former is (a.e.) exactly the `i = r` summand of the latter. -/
theorem mixIntS_dzIter_le_HkIntegrand {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)))
    (hr : r ≤ k) {z : ℝ} (hz : 0 < z) :
    Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z
      ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.Dz (Work.Spaces.pth V)) z θ := by
  rw [mixIntS_dzIter_slice_eq hV r hz]
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 z (Set.mem_Ici.mpr hz.le))
    (Filter.Eventually.of_forall fun θ =>
      Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.Dz (Work.Spaces.pth V)) z θ r hr)

/-! ## Measurability in `z` -/

/-- The slice functional `mixIntS (D_z^r V)` is a.e. strongly measurable for `volume.restrict Iz`:
it is the weighted angular integral of the `C^∞`-on-the-open-quadrant function
`D_z ∂_θ (D_z^r V)`. -/
theorem aesm_mixIntS_dzIter {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h := Work.EllipticEst.Core.v2_aesm_integral ((hV.DzIter r).pth.Dz)
    (-(Work.Spaces.eta))
  simpa only [Work.EllipticEst.Core.mixIntS, Work.FTS.EllipticEst.thEta]
    using h.aestronglyMeasurable

/-! ## The value of the `z`-integral -/


/-! ## The target -/

theorem mixIntS_dzIter_integrable {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)))
    (hr : r ≤ k) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      Work.Spaces.Iz := by
  refine Work.EllipticEst.Core.i0Aux.integrableOn_of_slice_le
    (g := Work.Spaces.Dz (Work.Spaces.pth V))
    (G := fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
    hmem (fun z => mixIntS_nonneg (Work.Spaces.DzIter r V) z)
    (aesm_mixIntS_dzIter hV r) ?_
  filter_upwards [Work.EllipticEst.Core.i0Aux.ae_pos_Iz] with z hz
  exact mixIntS_dzIter_le_HkIntegrand hV hmem hr hz

end

end Work.Blocks.StripMajorantAux
end
-- ===== merged: Submission.Work.EllipticEst.Assembly.PairAuxRest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem existsBoxQ0Aux {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b : ℝ × ℝ, a ≤ b ∧ 0 < a.1 ∧ 0 < a.2 ∧ b.2 < π / 2 ∧
      K ⊆ Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2 := by
  rcases K.eq_empty_or_nonempty with hK0 | hne
  · subst hK0
    refine ⟨(1, 1), (2, 3 / 2), ?_, by norm_num, by norm_num, by linarith [Real.pi_gt_three], ?_⟩
    · constructor <;> norm_num
    · intro x hx; exact absurd hx (Set.notMem_empty x)
  · obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨q, hqK, hqmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    obtain ⟨r, hrK, hrmin⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨s, hsK, hsmax⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
    have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp (hsub hpK)).1
    have hq1 : 0 < q.1 := (Work.FTS.EllipticEst.mem_Q0.mp (hsub hqK)).1
    have hr2 : 0 < r.2 := (Work.FTS.EllipticEst.mem_Q0.mp (hsub hrK)).2.1
    have hs2 : s.2 < π / 2 := (Work.FTS.EllipticEst.mem_Q0.mp (hsub hsK)).2.2
    have hpq : p.1 ≤ q.1 := hpmin hqK
    have hrs : r.2 ≤ s.2 := hrmin hsK
    refine ⟨(p.1 / 2, r.2 / 2), (2 * q.1, (π / 2 + s.2) / 2), ?_, ?_, ?_, ?_, ?_⟩
    · constructor <;> linarith
    · linarith
    · linarith
    · linarith
    · intro x hx
      have hx1 : p.1 ≤ x.1 := hpmin hx
      have hx1' : x.1 ≤ q.1 := hqmax hx
      have hx2 : r.2 ≤ x.2 := hrmin hx
      have hx2' : x.2 ≤ s.2 := hsmax hx
      rw [Set.mem_prod]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem supportVanishAux {g : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry g)) :
    g x.1 x.2 = 0 ∧ Work.Spaces.pz g x.1 x.2 = 0 ∧ Work.Spaces.pth g x.1 x.2 = 0 := by
  obtain ⟨U, V, hUo, hVo, hxU, hxV, hzero⟩ := exists_isOpen_local_zero_of_notMem_tsupport hx
  refine ⟨hzero x.1 hxU x.2 hxV, ?_, ?_⟩
  · have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.1] (fun z => g z x.2) := by
      filter_upwards [hUo.mem_nhds hxU] with z hz
      exact (hzero z hz x.2 hxV).symm
    exact ((hs.deriv_eq).symm.trans (deriv_const x.1 0))
  · have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.2] (fun θ => g x.1 θ) := by
      filter_upwards [hVo.mem_nhds hxV] with θ hθ
      exact (hzero x.1 hxU θ hθ).symm
    exact ((hs.deriv_eq).symm.trans (deriv_const x.2 0))

theorem contDiffOnPairAux {α : ℝ} {Φ φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) (hφ : Work.FTS.EllipticEst.SmoothOpen φ) :
    ContDiffOn ℝ 1 (Work.EllipticEst.Assembly.pairRad α Φ φ) Work.FTS.EllipticEst.Q0
      ∧ ContDiffOn ℝ 1 (Work.EllipticEst.Assembly.pairAng α Φ φ) Work.FTS.EllipticEst.Q0 := by
  have hrpow : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => x.1 ^ (pairBeta α + 2))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.contDiffOn_iff.mpr fun x hx =>
      (Real.contDiffAt_rpow_const_of_ne (p := pairBeta α + 2)
        (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hx).1)).comp x contDiffAt_fst
  have hrpow1 : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => x.1 ^ pairBeta α)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.contDiffOn_iff.mpr fun x hx =>
      (Real.contDiffAt_rpow_const_of_ne (p := pairBeta α)
        (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hx).1)).comp x contDiffAt_fst
  have hcos : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Real.cos x.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hφ0 : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => φ x.1 x.2) Work.FTS.EllipticEst.Q0 :=
    hφ.forall 1
  have hΦ0 : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Φ x.1 x.2) Work.FTS.EllipticEst.Q0 :=
    hΦ.forall 1
  have hpzφ : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Work.Spaces.pz φ x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hφ.pz).forall 1
  have hpzΦ : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Work.Spaces.pz Φ x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hΦ.pz).forall 1
  have hpthφ : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Work.Spaces.pth φ x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hφ.pth).forall 1
  have hpthΦ : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Work.Spaces.pth Φ x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hΦ.pth).forall 1
  constructor
  · refine (((contDiffOn_const (c := α ^ 2)).mul hrpow).mul hcos).mul ?_
    exact (hpzφ.mul hΦ0).sub (hpzΦ.mul hφ0)
  · exact (hrpow1.mul hcos).mul ((hpthφ.mul hΦ0).sub (hpthΦ.mul hφ0))

theorem pairRad_eq_zero_off_tsupport {α : ℝ} {Φ φ : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry φ)) : pairRad α Φ φ x = 0 := by
  obtain ⟨h1, h2, -⟩ := supportVanishAux (g := φ) hx
  simp only [pairRad_apply]
  rw [h1, h2]
  ring

theorem pairAng_eq_zero_off_tsupport {α : ℝ} {Φ φ : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry φ)) : pairAng α Φ φ x = 0 := by
  obtain ⟨h1, -, h3⟩ := supportVanishAux (g := φ) hx
  simp only [pairAng_apply]
  rw [h1, h3]
  ring


end Work.EllipticEst.Assembly
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-- The flat angular variable `ρ = f · sin(2θ)^{-(1+η)/2}`. -/
def rho (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  f θ * (Real.sin (2 * θ)) ^ (-((1 + Work.Spaces.eta) / 2))

/-- The primitive of the weighted `θ`-integration by parts:
`Φ = f f' σ + (η/2) f² (s'/s) σ` with `s = sin(2θ)`, `σ = s^{-η}`. -/
def Phi (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  f θ * deriv f θ * Work.FTS.EllipticEst.thEta θ
    + (Work.Spaces.eta / 2) * (f θ) ^ 2 * (2 * Real.cos (2 * θ))
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- `β = f² sin(2θ)^{η}`; its derivative is `2 sin(2θ)^{2η} · Φ`. -/
def beta (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `rho² = f² sin(2θ)^{-(1+η)}`. -/
theorem rho_sq (f : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (rho f θ) ^ 2 = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
  have hs := sin_two_pos hθ
  have h2 : ((Real.sin (2 * θ)) ^ (-((1 + Work.Spaces.eta) / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    push_cast
    ring
  rw [rho, mul_pow, h2]

/-- `beta = rho² · sin(2θ)^{1+2η}`. -/
theorem beta_eq (f : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    beta f θ = (rho f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 + 2 * Work.Spaces.eta) := by
  have hs := sin_two_pos hθ
  rw [beta, rho_sq f hθ, mul_assoc, ← Real.rpow_add hs]
  congr 1
  ring


end Work.EllipticEst.Core.i0Aux
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.Helpers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Auxiliary facts -/

/-- `Icc a b` and `Ioo a b` agree almost everywhere. -/
lemma tvc_ae_eq_Icc_Ioo (a b : ℝ) : Set.Icc a b =ᵐ[volume] Set.Ioo a b := by
  have h0 : volume (Set.Icc a b \ Set.Ioo a b) = 0 := by
    have hsub : Set.Icc a b \ Set.Ioo a b ⊆ ({a, b} : Set ℝ) := by
      rintro x ⟨hx, hx'⟩
      rw [Set.mem_Icc] at hx
      rw [Set.mem_Ioo] at hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hxa : x = a
      · exact Or.inl hxa
      · by_cases hxb : x = b
        · exact Or.inr hxb
        · exfalso
          exact hx' ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    exact measure_mono_null hsub (Set.Finite.measure_zero (by simp) volume)
  have hmem : ∀ᵐ x : ℝ, x ∉ (Set.Icc a b \ Set.Ioo a b) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using h0
  filter_upwards [hmem] with x hx
  rw [Set.mem_sdiff] at hx
  exact propext ⟨fun h1 => by
      by_contra h2
      exact hx ⟨h1, h2⟩,
    fun h1 => ⟨le_of_lt h1.1, le_of_lt h1.2⟩⟩

lemma tvc_ae_eq_Iθ_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
  simpa only [Work.Spaces.Iθ] using tvc_ae_eq_Icc_Ioo 0 (Real.pi / 2)


lemma tvc_setIntegral_Iθ_eq_Ioo (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in Set.Ioo 0 (Real.pi / 2), g θ :=
  MeasureTheory.setIntegral_congr_set tvc_ae_eq_Iθ_Ioo

lemma tvc_integrableOn_Ioo_of_Iθ {g : ℝ → ℝ}
    (h : IntegrableOn g Work.Spaces.Iθ) : IntegrableOn g (Set.Ioo 0 (Real.pi / 2)) := by
  rw [IntegrableOn] at h ⊢
  rwa [← Measure.restrict_congr_set tvc_ae_eq_Iθ_Ioo]

/-- The weight is a.e. strongly measurable on `Iθ` (it is continuous on the open interval). -/
lemma tvc_aesm_thEta :
    AEStronglyMeasurable Work.FTS.EllipticEst.thEta (volume.restrict Work.Spaces.Iθ) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hcont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo 0 (Real.pi / 2)) := by
    refine hsin.rpow_const ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  rw [Measure.restrict_congr_set tvc_ae_eq_Iθ_Ioo]
  exact hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioo


/-! ## The scale -/

/-- The scale of the surrogate: `L⁴ = P / (16 (P + E))`. -/
noncomputable def sScale (P E : ℝ) : ℝ := Real.sqrt (Real.sqrt (P / (16 * (P + E))))


lemma sScale_pos {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) : 0 < sScale P E := by
  have h1 : 0 < P / (16 * (P + E)) := by
    apply div_pos hP
    nlinarith
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h1)

lemma sScale_sq (P E : ℝ) : sScale P E ^ 2 = Real.sqrt (P / (16 * (P + E))) := by
  rw [sScale, Real.sq_sqrt (Real.sqrt_nonneg _)]

lemma sScale_pow4 {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ 4 = P / (16 * (P + E)) := by
  have h1 : 0 ≤ P / (16 * (P + E)) := by
    apply div_nonneg hP.le
    nlinarith
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sScale_sq, Real.sq_sqrt h1]

lemma sScale_rpow_four {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (4 : ℝ) = P / (16 * (P + E)) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sScale_pow4 hP hE

lemma sScale_le_half {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) : sScale P E ≤ 1 / 2 := by
  have h1 : P / (16 * (P + E)) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by nlinarith : (0:ℝ) < 16 * (P + E))]
    nlinarith
  have h2 : (0 : ℝ) ≤ P / (16 * (P + E)) := by
    apply div_nonneg hP.le; nlinarith
  calc sScale P E = Real.sqrt (Real.sqrt (P / (16 * (P + E)))) := rfl
    _ ≤ Real.sqrt (Real.sqrt (1 / 16)) := by
        apply Real.sqrt_le_sqrt
        apply Real.sqrt_le_sqrt
        exact h1
    _ = 1 / 2 := by
        rw [show (1 : ℝ) / 16 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
          show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma sScale_mul_A {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (3 + Work.Spaces.eta) * sScale P E ^ (1 - Work.Spaces.eta)
      = sScale P E ^ (4 : ℝ) := by
  rw [← Real.rpow_add (sScale_pos hP hE)]
  congr 1
  ring

lemma sScale_mul_B {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (Work.Spaces.eta - 1) * sScale P E ^ (1 - Work.Spaces.eta) = 1 := by
  rw [← Real.rpow_add (sScale_pos hP hE),
    show Work.Spaces.eta - 1 + (1 - Work.Spaces.eta) = 0 by ring,
    Real.rpow_zero (sScale P E)]

lemma sScale_mul_C {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (-(3 + Work.Spaces.eta)) * sScale P E ^ (3 + Work.Spaces.eta) = 1 := by
  rw [← Real.rpow_add (sScale_pos hP hE),
    show -(3 + Work.Spaces.eta) + (3 + Work.Spaces.eta) = 0 by ring,
    Real.rpow_zero (sScale P E)]

lemma sScale_inv_four {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (-4 : ℝ) = 16 * (P + E) / P := by
  have h4 : sScale P E ^ (4 : ℝ) = P / (16 * (P + E)) := sScale_rpow_four hP hE
  rw [show (-4 : ℝ) = -(4 : ℝ) by ring, Real.rpow_neg (le_of_lt (sScale_pos hP hE)), h4]
  try field_simp
  try ring

lemma sScale_mul_D {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (-(3 + Work.Spaces.eta)) * sScale P E ^ (Work.Spaces.eta - 1)
      = 16 * (P + E) / P := by
  rw [← Real.rpow_add (sScale_pos hP hE),
    show -(3 + Work.Spaces.eta) + (Work.Spaces.eta - 1) = -4 by ring]
  exact sScale_inv_four hP hE

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
lemma tvc_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
  apply Real.sqrt_le_sqrt
  rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (Real.sqrt a - Real.sqrt b),
    Real.sq_sqrt (mul_nonneg ha hb)]

/-- `√(P (P + E)) ≤ P + √(P E)` for `P, E ≥ 0`. -/
lemma tvc_sqrt_mul_le {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    Real.sqrt (P * (P + E)) ≤ P + Real.sqrt (P * E) := by
  have h1 : P * (P + E) = P ^ 2 + P * E := by ring
  calc Real.sqrt (P * (P + E)) = Real.sqrt (P ^ 2 + P * E) := by rw [h1]
    _ ≤ Real.sqrt (P ^ 2) + Real.sqrt (P * E) :=
        tvc_sqrt_add_le (sq_nonneg P) (mul_nonneg hP hE)
    _ = P + Real.sqrt (P * E) := by rw [Real.sqrt_sq hP]

end

end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.traceVanishingInterp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 20000000

/-!
## Auxiliary calculus for the weighted angular interpolation inequality

This file proves `traceVanishingInterp`: the one-dimensional weighted interpolation
inequality

  `∫_{Iθ} (f')² σ ≤ C (∫_{Iθ} f² σ + √(∫_{Iθ} f² σ · ∫_{Iθ} (f'')² σ))`

for `σ = thEta = sin(2θ)^{-η}`, `η = 99/100`, and `f` of class `C²` on the open interval
`(0, π/2)` whose two endpoint traces vanish and whose three weighted `L²`-norms are finite.

The proof has three layers.

* **The interior integration by parts** (`ibp_main`, `ibp_cot`): for `0 < a < b < π/2`,
  ```
  ∫_a^b (f')² σ = [f f' σ + η f² c σ]_a^b - ∫_a^b f f'' σ + 2η ∫_a^b f² σ
                    + 2η(1+η) ∫_a^b f² c² σ,
  ∫_a^b f f' c σ = ∫_a^b f² σ + (1+η) ∫_a^b f² c² σ + (1/2) [f² c σ]_a^b,
  ```
  where `c = cot(2·)`; everything is written with the auxiliary weight
  `cs1 θ = cos(2θ) sin(2θ)^{-(1+η)}` (equal to `cot(2θ) σ θ` on `(0,π/2)`) and
  `csq θ = cos²(2θ) sin(2θ)^{-(2+η)}` (equal to `cot²(2θ) σ θ`), so that no derivative of
  `cot` and no Pythagorean identity is needed: the rpow bookkeeping is pure
  `Real.rpow_add`.

* **The completed square**: eliminating `∫ f² c² σ` between the two identities via
  `0 ≤ ∫_a^b (f' - (1+η) f c)² σ` gives, on `[a,b]`,
  ```
  (1/199) ∫_a^b (f')² σ = [f f' σ - η f² c σ]_a^b - ∫_a^b f f'' σ
      - 2η ∫_a^b f² σ - (2η/(1+η)) ∫_a^b (f' - (1+η) f c)² σ,
  ```
  with `1 - 2η/(1+η) = (1-η)/(1+η) = 1/199`.

* **The endpoint analysis**: the four boundary terms tend to `0` along the truncating
  sequence (`traceBoundarySeq`), the Cauchy–Schwarz bound `|∫ f f'' σ| ≤ √(P E)` and the
  monotone convergence of `∫_{a_n}^{b_n} (f')² σ` to `∫_{Iθ} (f')² σ` (`expandingIntegral`)
  finish the proof.
-/

/-! ## §1. Elementary facts about the weight -/

/-- `sin (2θ) > 0` on the open angular interval. -/
private theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    0 < Real.sin (2*θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The weight `thEta` is positive on the open angular interval. -/
private theorem thEta_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    0 < Work.FTS.EllipticEst.thEta θ :=
  Real.rpow_pos_of_pos (sin_two_pos_of_mem hθ) _

/-- The auxiliary weight `cos(2θ) sin(2θ)^{-(1+η)}`, which equals `cot(2θ) * thEta θ` on the
open angular interval. -/
private def cs1 (θ : ℝ) : ℝ := Real.cos (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))

/-- The auxiliary weight `cos²(2θ) sin(2θ)^{-(2+η)}`, which equals `cot²(2θ) * thEta θ` on the
open angular interval. -/
private def csq (θ : ℝ) : ℝ := Real.cos (2*θ) ^ 2 * Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta))

/-- `(cos(2θ)/sin(2θ)) * thEta θ = cs1 θ`: the rpow identity behind the cross term. -/
private theorem cossin_mul_thEta {θ : ℝ} (hsin : 0 < Real.sin (2*θ)) :
    (Real.cos (2*θ) / Real.sin (2*θ)) * Work.FTS.EllipticEst.thEta θ = cs1 θ := by
  rw [cs1, Work.FTS.EllipticEst.thEta, div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc,
    ← Real.rpow_neg_one (Real.sin (2*θ)), ← Real.rpow_add hsin,
    show -(Work.Spaces.eta) + (-1:ℝ) = -(1 + Work.Spaces.eta) by ring]

/-- `(cos(2θ)/sin(2θ))^2 * thEta θ = csq θ`: the rpow identity behind the squared term. -/
private theorem cossin_sq_mul_thEta {θ : ℝ} (hsin : 0 < Real.sin (2*θ)) :
    (Real.cos (2*θ) / Real.sin (2*θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ = csq θ := by
  have h1 : ((Real.sin (2*θ)) ^ 2)⁻¹ = Real.sin (2*θ) ^ (-(2:ℝ)) := by
    rw [Real.rpow_neg hsin.le, Real.rpow_two]
  rw [csq, Work.FTS.EllipticEst.thEta, div_pow, div_eq_mul_inv, mul_assoc, h1,
    ← Real.rpow_add hsin,
    show (-(2:ℝ)) + -(Work.Spaces.eta) = -(2 + Work.Spaces.eta) by ring]

/-! ## §2. The Jordan-type bounds at the two endpoints -/

/-- `thEta θ ≤ ((4/π) θ)^{-η}` for `0 < θ ≤ π/4`. -/
private theorem thEta_le_left {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi/4) :
    Work.FTS.EllipticEst.thEta θ ≤ ((4/Real.pi) * θ) ^ (-(Work.Spaces.eta)) := by
  have hs : (4/Real.pi) * θ ≤ Real.sin (2*θ) := by
    have h := Real.mul_le_sin (x := 2*θ) (by linarith) (by linarith [hθ1, Real.pi_pos])
    calc (4/Real.pi) * θ = 2/Real.pi * (2*θ) := by ring
      _ ≤ Real.sin (2*θ) := h
  have hpos : 0 < (4/Real.pi) * θ := by positivity
  have hz : (-(Work.Spaces.eta)) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  rw [Work.FTS.EllipticEst.thEta]
  exact Real.rpow_le_rpow_of_nonpos hpos hs hz

/-- `cs1 θ ≤ ((4/π) θ)^{-(1+η)}` for `0 < θ ≤ π/4`. -/
private theorem cs1_le_left {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi/4) :
    cs1 θ ≤ ((4/Real.pi) * θ) ^ (-(1 + Work.Spaces.eta)) := by
  have hs : (4/Real.pi) * θ ≤ Real.sin (2*θ) := by
    have h := Real.mul_le_sin (x := 2*θ) (by linarith) (by linarith [hθ1, Real.pi_pos])
    calc (4/Real.pi) * θ = 2/Real.pi * (2*θ) := by ring
      _ ≤ Real.sin (2*θ) := h
  have hpos : 0 < (4/Real.pi) * θ := by positivity
  have hz : (-(1 + Work.Spaces.eta)) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  have h1 : Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))
      ≤ ((4/Real.pi) * θ) ^ (-(1 + Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_nonpos hpos hs hz
  have hsin0 : 0 ≤ Real.sin (2*θ) := le_of_lt (by
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos]))
  have h2 : Real.cos (2*θ) ≤ 1 := Real.cos_le_one _
  rw [cs1]
  calc Real.cos (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))
      ≤ 1 * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hsin0 _)
    _ = Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)) := one_mul _
    _ ≤ ((4/Real.pi) * θ) ^ (-(1 + Work.Spaces.eta)) := h1

/-- `thEta θ ≤ ((4/π) (π/2 - θ))^{-η}` for `π/4 ≤ θ < π/2`. -/
private theorem thEta_le_right {θ : ℝ} (hθ0 : Real.pi/4 ≤ θ) (hθ1 : θ < Real.pi/2) :
    Work.FTS.EllipticEst.thEta θ ≤ ((4/Real.pi) * (Real.pi/2 - θ)) ^ (-(Work.Spaces.eta)) := by
  have hδ0 : 0 < Real.pi/2 - θ := by linarith
  have hδ1 : Real.pi/2 - θ ≤ Real.pi/4 := by linarith
  have hsin : Real.sin (2*θ) = Real.sin (2*(Real.pi/2 - θ)) := by
    rw [show 2*θ = Real.pi - 2*(Real.pi/2 - θ) by ring, Real.sin_pi_sub]
  rw [Work.FTS.EllipticEst.thEta, hsin]
  exact thEta_le_left hδ0 hδ1


/-! ## §3. Derivatives of the weights -/

/-- `HasDerivAt` of `sin (2 ·)`. -/
private theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2*θ')) (2 * Real.cos (2*θ)) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  exact ((Real.hasDerivAt_sin (2*θ)).comp θ h1).congr_deriv (by ring)

/-- `HasDerivAt` of `cos (2 ·)`. -/
private theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2*θ')) (-(2 * Real.sin (2*θ))) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  exact ((Real.hasDerivAt_cos (2*θ)).comp θ h1).congr_deriv (by ring)

/-- `HasDerivAt` of `thEta θ' = sin(2θ')^{-η}`, with the value written through `cs1`. -/
private theorem hasDerivAt_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt Work.FTS.EllipticEst.thEta (-(2 * Work.Spaces.eta) * cs1 θ) θ := by
  have hsin := sin_two_pos_of_mem hθ
  have hbase : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ') ^ (-(Work.Spaces.eta)))
      (-(2 * Work.Spaces.eta) * (Real.cos (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)))) θ := by
    have h0 := (Real.hasDerivAt_rpow_const (x := Real.sin (2*θ)) (p := -(Work.Spaces.eta))
      (Or.inl hsin.ne')).comp θ (hasDerivAt_sin_two θ)
    have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ') ^ (-(Work.Spaces.eta)))
        ((-(Work.Spaces.eta)) * Real.sin (2*θ) ^ (-(Work.Spaces.eta) - 1)
          * (2 * Real.cos (2*θ))) θ := by
      simpa [Function.comp_def] using h0
    refine h1.congr_deriv ?_
    rw [show -(Work.Spaces.eta) - 1 = -(1 + Work.Spaces.eta) by ring]
    ring
  rw [show Work.FTS.EllipticEst.thEta
    = (fun θ' : ℝ => Real.sin (2*θ') ^ (-(Work.Spaces.eta))) from rfl]
  simpa only [cs1] using hbase

/-- `HasDerivAt` of `cs1`, with value `-2 thEta θ - 2(1+η) csq θ`. -/
private theorem hasDerivAt_cs1 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt cs1 (-2 * Work.FTS.EllipticEst.thEta θ
      - 2*(1 + Work.Spaces.eta) * csq θ) θ := by
  have hsin := sin_two_pos_of_mem hθ
  have hbase : HasDerivAt (fun θ' : ℝ => Real.cos (2*θ') * Real.sin (2*θ') ^ (-(1 + Work.Spaces.eta)))
      (-2 * (Real.sin (2*θ) ^ (-(Work.Spaces.eta)))
        - 2*(1 + Work.Spaces.eta) * ((Real.cos (2*θ))^2 * Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta)))) θ := by
    have h0 := (Real.hasDerivAt_rpow_const (x := Real.sin (2*θ)) (p := -(1 + Work.Spaces.eta))
      (Or.inl hsin.ne')).comp θ (hasDerivAt_sin_two θ)
    have hp : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ') ^ (-(1 + Work.Spaces.eta)))
        ((-(1 + Work.Spaces.eta)) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta) - 1)
          * (2 * Real.cos (2*θ))) θ := by
      simpa [Function.comp_def] using h0
    have hmul := (hasDerivAt_cos_two θ).mul hp
    refine hmul.congr_deriv ?_
    have hsinpow : Real.sin (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))
        = Real.sin (2*θ) ^ (-(Work.Spaces.eta)) := by
      nth_rewrite 1 [← Real.rpow_one (Real.sin (2*θ))]
      rw [← Real.rpow_add hsin,
        show (1:ℝ) + -(1 + Work.Spaces.eta) = -(Work.Spaces.eta) by ring]
    rw [show -(1 + Work.Spaces.eta) - 1 = -(2 + Work.Spaces.eta) by ring]
    rw [show (-(2 * Real.sin (2*θ))) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))
        = -2 * (Real.sin (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))) by ring]
    rw [hsinpow]
    ring
  rw [show cs1 = (fun θ' : ℝ => Real.cos (2*θ') * Real.sin (2*θ') ^ (-(1 + Work.Spaces.eta)))
    from rfl]
  simpa only [csq, Work.FTS.EllipticEst.thEta] using hbase

/-! ## §4. The primitives of the two integrations by parts -/

/-- The derivative of the primitive `f f' σ + η f² cs1`. -/
private theorem hasDerivAt_prim1 {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt (fun θ' : ℝ => f θ' * deriv f θ' * Work.FTS.EllipticEst.thEta θ'
        + Work.Spaces.eta * (f θ')^2 * cs1 θ')
      (((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta) * ((f θ)^2 * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)) * ((f θ)^2 * csq θ)) θ := by
  have hcd2 : ContDiffAt ℝ 2 f θ := hf.contDiffAt (Ioo_mem_nhds hθ.1 hθ.2)
  have hdf : HasDerivAt f (deriv f θ) θ := (hcd2.differentiableAt two_ne_zero).hasDerivAt
  have hdf' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    ((hcd2.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hσ := hasDerivAt_thEta hθ
  have hcs := hasDerivAt_cs1 hθ
  have h1 : HasDerivAt (fun θ' : ℝ => f θ' * deriv f θ' * Work.FTS.EllipticEst.thEta θ')
      ((deriv f θ * deriv f θ + f θ * deriv (deriv f) θ) * Work.FTS.EllipticEst.thEta θ
        + (f θ * deriv f θ) * (-(2 * Work.Spaces.eta) * cs1 θ)) θ :=
    (hdf.mul hdf').mul hσ
  have hp : HasDerivAt (fun θ' : ℝ => (f θ')^2) (2 * f θ * deriv f θ) θ :=
    (hdf.pow 2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.eta * (f θ')^2 * cs1 θ')
      (Work.Spaces.eta * (2 * f θ * deriv f θ) * cs1 θ
        + Work.Spaces.eta * (f θ)^2 * (-2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * csq θ)) θ :=
    (hp.const_mul Work.Spaces.eta).mul hcs
  refine (h1.add h2).congr_deriv ?_
  simp only [cs1, csq, Work.FTS.EllipticEst.thEta]
  ring

/-- The derivative of the primitive `(1/2) f² cs1`. -/
private theorem hasDerivAt_prim2 {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt (fun θ' : ℝ => (1/2) * (f θ')^2 * cs1 θ')
      (f θ * deriv f θ * cs1 θ - (f θ)^2 * Work.FTS.EllipticEst.thEta θ
        - (1 + Work.Spaces.eta) * ((f θ)^2 * csq θ)) θ := by
  have hcd2 : ContDiffAt ℝ 2 f θ := hf.contDiffAt (Ioo_mem_nhds hθ.1 hθ.2)
  have hdf : HasDerivAt f (deriv f θ) θ := (hcd2.differentiableAt two_ne_zero).hasDerivAt
  have hcs := hasDerivAt_cs1 hθ
  have hp : HasDerivAt (fun θ' : ℝ => (f θ')^2) (2 * f θ * deriv f θ) θ :=
    (hdf.pow 2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun θ' : ℝ => (1/2 : ℝ) * (f θ')^2 * cs1 θ')
      ((1/2 : ℝ) * (2 * f θ * deriv f θ) * cs1 θ
        + (1/2 : ℝ) * (f θ)^2 * (-2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * csq θ)) θ :=
    (hp.const_mul (1/2 : ℝ)).mul hcs
  refine h2.congr_deriv ?_
  simp only [cs1, csq, Work.FTS.EllipticEst.thEta]
  ring

/-! ## §5. The two integrations by parts on an interior sub-interval -/

/-- The first integration by parts: on an interior sub-interval `[a,b]`,

`∫_a^b (f')² σ = [f f' σ + η f² cs1]_a^b - ∫_a^b f f'' σ + 2η ∫_a^b f² σ
  + 2η(1+η) ∫_a^b f² csq`. -/
private theorem ibp_main {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi/2) (hab : a ≤ b) :
    (∫ θ in a..b, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (f b * deriv f b * Work.FTS.EllipticEst.thEta b
            + Work.Spaces.eta * (f b) ^ 2 * cs1 b)
        - (f a * deriv f a * Work.FTS.EllipticEst.thEta a
            + Work.Spaces.eta * (f a) ^ 2 * cs1 a)
        - (∫ θ in a..b, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        + 2 * Work.Spaces.eta * (∫ θ in a..b, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (∫ θ in a..b, (f θ) ^ 2 * csq θ) := by
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
  have hcf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcf' : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen hIoo (by norm_num)).mono hmem
  have hcf'' : ContinuousOn (deriv (deriv f)) (Set.uIcc a b) := by
    have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hf.deriv_of_isOpen hIoo (by norm_num)
    exact (contDiffOn_zero.1 (h1.deriv_of_isOpen hIoo (by norm_num))).mono hmem
  have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinne : ∀ θ ∈ Set.uIcc a b, Real.sin (2*θ) ≠ 0 := fun θ hθ =>
    (sin_two_pos_of_mem (hmem θ hθ)).ne'
  have hσC : ContinuousOn Work.FTS.EllipticEst.thEta (Set.uIcc a b) :=
    hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
  have hcsqC : ContinuousOn csq (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Real.cos (2*θ))^2) (Set.uIcc a b) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  have hIA : IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      volume a b := ((hcf'.pow 2).mul hσC).intervalIntegrable
  have hIB : IntervalIntegrable
      (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) volume a b :=
    ((hcf.mul hcf'').mul hσC).intervalIntegrable
  have hIC : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      volume a b := ((hcf.pow 2).mul hσC).intervalIntegrable
  have hID : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * csq θ) volume a b :=
    ((hcf.pow 2).mul hcsqC).intervalIntegrable
  set G : ℝ → ℝ := fun θ : ℝ => ((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
        + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
      - (2 * Work.Spaces.eta) * ((f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)) * ((f θ)^2 * csq θ) with hGdef
  set F : ℝ → ℝ := fun θ : ℝ => f θ * deriv f θ * Work.FTS.EllipticEst.thEta θ
      + Work.Spaces.eta * (f θ)^2 * cs1 θ with hFdef
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (G x) x := by
    intro x hx
    rw [hFdef, hGdef]
    exact hasDerivAt_prim1 hf (hmem x hx)
  have hAB : IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
      + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) volume a b := hIA.add hIB
  have h2C : IntervalIntegrable
      (fun θ : ℝ => (2 * Work.Spaces.eta) * ((f θ)^2 * Work.FTS.EllipticEst.thEta θ))
      volume a b := hIC.const_mul (2 * Work.Spaces.eta)
  have hAB2C : IntervalIntegrable
      (fun θ : ℝ => ((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta) * ((f θ)^2 * Work.FTS.EllipticEst.thEta θ)) volume a b :=
    hAB.sub h2C
  have h2D : IntervalIntegrable
      (fun θ : ℝ => (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)) * ((f θ)^2 * csq θ))
      volume a b := hID.const_mul _
  have hGint : IntervalIntegrable G volume a b := by
    rw [hGdef]; exact hAB2C.sub h2D
  have hFTC : (∫ θ in a..b, G θ) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hGint
  have hFb : F b = f b * deriv f b * Work.FTS.EllipticEst.thEta b
      + Work.Spaces.eta * (f b) ^ 2 * cs1 b := rfl
  have hFa : F a = f a * deriv f a * Work.FTS.EllipticEst.thEta a
      + Work.Spaces.eta * (f a) ^ 2 * cs1 a := rfl
  rw [hFb, hFa] at hFTC
  have hGval : (∫ θ in a..b, G θ)
      = (∫ θ in a..b, (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)
        + (∫ θ in a..b, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta) * (∫ θ in a..b, (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)) * (∫ θ in a..b, (f θ)^2 * csq θ) := by
    rw [hGdef]
    rw [intervalIntegral.integral_sub hAB2C h2D, intervalIntegral.integral_sub hAB h2C,
      intervalIntegral.integral_add hIA hIB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  linarith [hFTC, hGval]

/-- The second integration by parts (the `cot`-primitive).

`∫_a^b f f' cs1 = ∫_a^b f² σ + (1+η) ∫_a^b f² csq + (1/2)[f² cs1]_a^b`. -/
private theorem ibp_cot {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi/2) (hab : a ≤ b) :
    (∫ θ in a..b, f θ * deriv f θ * cs1 θ)
      = (∫ θ in a..b, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + (1 + Work.Spaces.eta) * (∫ θ in a..b, (f θ) ^ 2 * csq θ)
        + (1/2) * ((f b) ^ 2 * cs1 b - (f a) ^ 2 * cs1 a) := by
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
  have hcf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcf' : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen hIoo (by norm_num)).mono hmem
  have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinne : ∀ θ ∈ Set.uIcc a b, Real.sin (2*θ) ≠ 0 := fun θ hθ =>
    (sin_two_pos_of_mem (hmem θ hθ)).ne'
  have hσC : ContinuousOn Work.FTS.EllipticEst.thEta (Set.uIcc a b) :=
    hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
  have hcs1C : ContinuousOn cs1 (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.cos (2*θ)) (Set.uIcc a b) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  have hcsqC : ContinuousOn csq (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Real.cos (2*θ))^2) (Set.uIcc a b) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  have hIBc : IntervalIntegrable (fun θ : ℝ => f θ * deriv f θ * cs1 θ) volume a b :=
    ((hcf.mul hcf').mul hcs1C).intervalIntegrable
  have hIC : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      volume a b := ((hcf.pow 2).mul hσC).intervalIntegrable
  have hID : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * csq θ) volume a b :=
    ((hcf.pow 2).mul hcsqC).intervalIntegrable
  set Q2 : ℝ → ℝ := fun θ : ℝ => f θ * deriv f θ * cs1 θ
      - (f θ)^2 * Work.FTS.EllipticEst.thEta θ
      - (1 + Work.Spaces.eta) * ((f θ)^2 * csq θ) with hQ2def
  set P2 : ℝ → ℝ := fun θ : ℝ => (1/2) * (f θ)^2 * cs1 θ with hP2def
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt P2 (Q2 x) x := by
    intro x hx
    rw [hP2def, hQ2def]
    exact hasDerivAt_prim2 hf (hmem x hx)
  have hB2 : IntervalIntegrable
      (fun θ : ℝ => f θ * deriv f θ * cs1 θ - (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      volume a b := hIBc.sub hIC
  have h1e : IntervalIntegrable
      (fun θ : ℝ => (1 + Work.Spaces.eta) * ((f θ)^2 * csq θ)) volume a b :=
    hID.const_mul _
  have hQ2int : IntervalIntegrable Q2 volume a b := by
    rw [hQ2def]; exact hB2.sub h1e
  have hFTC : (∫ θ in a..b, Q2 θ) = P2 b - P2 a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hQ2int
  have hPb : P2 b = (1/2) * (f b)^2 * cs1 b := rfl
  have hPa : P2 a = (1/2) * (f a)^2 * cs1 a := rfl
  rw [hPb, hPa] at hFTC
  have hQ2val : (∫ θ in a..b, Q2 θ)
      = (∫ θ in a..b, f θ * deriv f θ * cs1 θ)
        - (∫ θ in a..b, (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
        - (1 + Work.Spaces.eta) * (∫ θ in a..b, (f θ)^2 * csq θ) := by
    rw [hQ2def]
    rw [intervalIntegral.integral_sub hB2 h1e, intervalIntegral.integral_sub hIBc hIC,
      intervalIntegral.integral_const_mul]
  linarith [hFTC, hQ2val]

/-! ## §6. The truncating sequences -/

/-- The left truncation point `a_n = 1/(n+2)`. -/
private def za (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

/-- The right truncation point `b_n = π/2 - 1/(n+2)`. -/
private def zb (n : ℕ) : ℝ := Real.pi / 2 - 1 / ((n : ℝ) + 2)

private theorem za_pos (n : ℕ) : 0 < za n := by
  rw [za]; positivity

private theorem za_le_half (n : ℕ) : za n ≤ 1/2 := by
  rw [za, div_le_iff₀ (by positivity)]
  have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  linarith

private theorem za_lt_pi4 (n : ℕ) : za n < Real.pi / 4 := by
  rw [za, div_lt_iff₀ (by positivity)]
  have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [Real.pi_gt_three]

private theorem zb_lt_pi2 (n : ℕ) : zb n < Real.pi / 2 := by
  have h : 0 < (1:ℝ) / ((n:ℝ) + 2) := za_pos n
  rw [zb]
  linarith

private theorem zb_ge_pi4 (n : ℕ) : Real.pi / 4 ≤ zb n := by
  have h : (1:ℝ) / ((n:ℝ) + 2) < Real.pi/4 := za_lt_pi4 n
  rw [zb]
  linarith

private theorem za_lt_zb (n : ℕ) : za n < zb n := by
  have h1 : za n < Real.pi/4 := za_lt_pi4 n
  have h2 : Real.pi/4 ≤ zb n := zb_ge_pi4 n
  linarith

private theorem za_mem (n : ℕ) : za n ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
  ⟨za_pos n, lt_trans (za_lt_pi4 n) (by linarith [Real.pi_pos])⟩

private theorem zb_mem (n : ℕ) : zb n ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
  ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) (zb_ge_pi4 n), zb_lt_pi2 n⟩

private theorem za_antitone : Antitone za := by
  intro m n hmn
  rw [za, za]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  linarith

private theorem zb_monotone : Monotone zb := by
  intro m n hmn
  rw [zb, zb]
  have h : (1:ℝ) / ((n:ℝ) + 2) ≤ 1 / ((m:ℝ) + 2) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
    linarith
  linarith

private theorem tendsto_za : Tendsto za atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => ((n:ℝ) + 2)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h2 : Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ) + 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h
  exact h2


private theorem tendsto_za_nhdsWithin : Tendsto za atTop (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_za, Eventually.of_forall fun n => za_pos n⟩

/-- The elementary power limits at the two endpoints. -/
private theorem tendsto_rpow_pos_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun θ : ℝ => θ ^ a) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h := (tendsto_rpow_neg_nhdsGT_zero (show -a < 0 by linarith)).inv_tendsto_atTop
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  show (θ ^ (-a))⁻¹ = θ ^ a
  rw [Real.rpow_neg (le_of_lt hθ), inv_inv]

private theorem tendsto_rpow_za {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (za n) ^ a) atTop (nhds 0) :=
  (tendsto_rpow_pos_nhdsGT_zero ha).comp tendsto_za_nhdsWithin

/-- `√(c θ^{1+η}) = √c · θ^{(1+η)/2}`. -/
private theorem sqrt_mul_rpow_half {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 ≤ θ) :
    Real.sqrt (c * θ ^ (1 + Work.Spaces.eta)) = Real.sqrt c * θ ^ ((1 + Work.Spaces.eta)/2) := by
  have h1 : Real.sqrt (θ ^ (1 + Work.Spaces.eta)) = θ ^ ((1 + Work.Spaces.eta)/2) := by
    have hsq : θ ^ ((1 + Work.Spaces.eta)/2) * θ ^ ((1 + Work.Spaces.eta)/2)
        = θ ^ (1 + Work.Spaces.eta) := by
      rw [← Real.rpow_add' hθ (by linarith [Work.Spaces.eta_pos]),
        show (1 + Work.Spaces.eta)/2 + (1 + Work.Spaces.eta)/2 = 1 + Work.Spaces.eta by ring]
    rw [← hsq, Real.sqrt_mul (Real.rpow_nonneg hθ _), ← pow_two,
      Real.sq_sqrt (Real.rpow_nonneg hθ _)]
  rw [Real.sqrt_mul hc, h1]

/-- `cs1` is nonnegative on `(0, π/4]`. -/
private theorem cs1_nonneg_left {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi/4) : 0 ≤ cs1 θ := by
  have h2θ : 2*θ ≤ Real.pi/2 := by linarith [hθ1, Real.pi_pos]
  have hc : 0 ≤ Real.cos (2*θ) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], h2θ⟩
  rw [cs1]
  refine mul_nonneg hc ?_
  exact Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))) _

/-! ## §7. The tails of an integrable function -/

/-- The integral of an integrable function over the shrinking left intervals tends to `0`. -/
private theorem tail_left (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Ioo (0:ℝ) (Real.pi/2))) :
    Tendsto (fun n : ℕ => ∫ t in Set.Ioo (0:ℝ) (za n), g t) atTop (nhds 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (Set.Ioo (0:ℝ) (za n)) := fun n => measurableSet_Ioo
  have hanti : Antitone (fun n : ℕ => Set.Ioo (0:ℝ) (za n)) := by
    intro m n hmn x hx
    exact ⟨hx.1, lt_of_lt_of_le hx.2 (za_antitone hmn)⟩
  have hint : IntegrableOn g (Set.Ioo (0:ℝ) (za 0)) :=
    hg.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (le_of_lt (za_mem 0).2)⟩)
  have h := Antitone.tendsto_setIntegral hmeas hanti hint
  have hInter : (⋂ n : ℕ, Set.Ioo (0:ℝ) (za n)) = ∅ := by
    ext x
    constructor
    · intro hx
      have hx0 : (0:ℝ) < x := (Set.mem_iInter.mp hx 0).1
      obtain ⟨k, hk⟩ := exists_nat_gt (1/x)
      have hkx : (1:ℝ) / ((k:ℝ) + 2) < x := by
        rw [div_lt_iff₀ (by positivity)]
        have h2 : (1:ℝ)/x < (k:ℝ) + 2 := by
          have : (k:ℝ) < (k:ℝ) + 2 := by linarith
          linarith [hk]
        rw [div_lt_iff₀ hx0] at h2
        linarith [h2]
      exact absurd (Set.mem_iInter.mp hx k).2 (not_lt.mpr hkx.le)
    · intro hx; exact absurd hx (Set.notMem_empty x)
  rw [hInter, MeasureTheory.setIntegral_empty] at h
  simpa using h

/-- The integral of an integrable function over the shrinking right intervals tends to `0`. -/
private theorem tail_right (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Ioo (0:ℝ) (Real.pi/2))) :
    Tendsto (fun n : ℕ => ∫ t in Set.Ioo (zb n) (Real.pi/2), g t) atTop (nhds 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (Set.Ioo (zb n) (Real.pi/2)) := fun n => measurableSet_Ioo
  have hanti : Antitone (fun n : ℕ => Set.Ioo (zb n) (Real.pi/2)) := by
    intro m n hmn x hx
    exact ⟨lt_of_le_of_lt (zb_monotone hmn) hx.1, hx.2⟩
  have hint : IntegrableOn g (Set.Ioo (zb 0) (Real.pi/2)) :=
    hg.mono_set (fun x hx => ⟨lt_of_lt_of_le (zb_mem 0).1 (le_of_lt hx.1), hx.2⟩)
  have h := Antitone.tendsto_setIntegral hmeas hanti hint
  have hInter : (⋂ n : ℕ, Set.Ioo (zb n) (Real.pi/2)) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxlt : x < Real.pi/2 := (Set.mem_iInter.mp hx 0).2
      have hposd : 0 < Real.pi/2 - x := by linarith
      obtain ⟨k, hk⟩ := exists_nat_gt (1/(Real.pi/2 - x))
      have h1 : x < zb k := by
        rw [zb]
        have h3 : (1:ℝ) / ((k:ℝ) + 2) < Real.pi/2 - x := by
          rw [div_lt_iff₀ (by positivity)]
          have h4 : (1:ℝ)/(Real.pi/2 - x) < (k:ℝ) + 2 := by
            have : (k:ℝ) < (k:ℝ) + 2 := by linarith
            linarith [hk]
          rw [div_lt_iff₀ hposd] at h4
          linarith [h4]
        linarith
      exact absurd (Set.mem_iInter.mp hx k).1 (not_lt.mpr h1.le)
    · intro hx; exact absurd hx (Set.notMem_empty x)
  rw [hInter, MeasureTheory.setIntegral_empty] at h
  simpa using h

/-! ## §8. Monotone convergence of the truncated integrals -/

/-- The truncated integrals increase to the full integral over `Iθ`. -/
private theorem expandingIntegral (g : ℝ → ℝ) (hg : IntegrableOn g Work.Spaces.Iθ)
    (hgn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ g θ) :
    Tendsto (fun n : ℕ => ∫ x in (za n)..(zb n), g x) atTop (nhds (∫ x in Work.Spaces.Iθ, g x)) := by
  have hIθ : Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) := rfl
  have hsub : ∀ n : ℕ, Set.Icc (za n) (zb n) ⊆ Work.Spaces.Iθ := by
    intro n x hx
    rw [Set.mem_Icc] at hx
    exact ⟨le_of_lt (lt_of_lt_of_le (za_pos n) hx.1),
      le_of_lt (lt_of_le_of_lt hx.2 (zb_lt_pi2 n))⟩
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by rw [hIθ]; exact measurableSet_Icc
  have hmeas : ∀ n : ℕ, MeasurableSet (Work.Spaces.Iθ \ Set.Icc (za n) (zb n)) :=
    fun n => hIθmeas.diff measurableSet_Icc
  have hanti : Antitone (fun n : ℕ => Work.Spaces.Iθ \ Set.Icc (za n) (zb n)) := by
    intro m n hmn x hx
    exact ⟨hx.1, fun hxin => hx.2 (Set.Icc_subset_Icc (za_antitone hmn) (zb_monotone hmn) hxin)⟩
  have hint : IntegrableOn g (Work.Spaces.Iθ \ Set.Icc (za 0) (zb 0)) :=
    hg.mono_set Set.sdiff_subset
  have hlim := Antitone.tendsto_setIntegral hmeas hanti hint
  have hInter : (⋂ n : ℕ, (Work.Spaces.Iθ \ Set.Icc (za n) (zb n))) = {0, Real.pi/2} := by
    ext x
    constructor
    · intro hx
      have hxI : x ∈ Work.Spaces.Iθ := (Set.mem_iInter.mp hx 0).1
      rw [hIθ, Set.mem_Icc] at hxI
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hx0, hxpi⟩ := hcon
      have hxpos : 0 < x := lt_of_le_of_ne hxI.1 (Ne.symm hx0)
      have hxlt : x < Real.pi/2 := lt_of_le_of_ne hxI.2 hxpi
      obtain ⟨k, hk⟩ := exists_nat_gt (1/x)
      have hza : za k < x := by
        rw [za, div_lt_iff₀ (by positivity)]
        have h4 : (1:ℝ)/x < (k:ℝ) + 2 := by
          have h5 : (k:ℝ) < (k:ℝ) + 2 := by linarith
          linarith [hk]
        rw [div_lt_iff₀ hxpos] at h4
        linarith [h4]
      have hposd : 0 < Real.pi/2 - x := by linarith
      obtain ⟨l, hl⟩ := exists_nat_gt (1/(Real.pi/2 - x))
      have hzb : x < zb l := by
        rw [zb]
        have h5 : (1:ℝ)/((l:ℝ) + 2) < Real.pi/2 - x := by
          rw [div_lt_iff₀ (by positivity)]
          have h6 : (1:ℝ)/(Real.pi/2 - x) < (l:ℝ) + 2 := by
            have h7 : (l:ℝ) < (l:ℝ) + 2 := by linarith
            linarith [hl]
          rw [div_lt_iff₀ hposd] at h6
          linarith [h6]
        linarith
      have hmem : x ∈ Set.Icc (za (max k l)) (zb (max k l)) :=
        ⟨le_of_lt (lt_of_le_of_lt (za_antitone (le_max_left k l)) hza),
          le_of_lt (lt_of_lt_of_le hzb (zb_monotone (le_max_right k l)))⟩
      exact (Set.mem_iInter.mp hx (max k l)).2 hmem
    · intro hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [Set.mem_iInter]
      intro n
      constructor
      · rw [hIθ, Set.mem_Icc]
        rcases hx with h | h
        · rw [h]; exact ⟨le_refl 0, by linarith [Real.pi_pos]⟩
        · rw [h]; exact ⟨by linarith [Real.pi_pos], le_refl _⟩
      · intro hmem
        rw [Set.mem_Icc] at hmem
        rcases hx with h | h
        · rw [h] at hmem; exact absurd hmem.1 (not_le.mpr (za_pos n))
        · rw [h] at hmem; exact absurd hmem.2 (not_le.mpr (zb_lt_pi2 n))
  rw [hInter] at hlim
  have hzero : (∫ x in ({0, Real.pi/2} : Set ℝ), g x) = 0 :=
    MeasureTheory.setIntegral_measure_zero _ (Set.Finite.measure_zero (by simp) MeasureTheory.volume)
  rw [hzero] at hlim
  have hdisj : ∀ n : ℕ, Disjoint (Work.Spaces.Iθ \ Set.Icc (za n) (zb n))
      (Set.Icc (za n) (zb n)) := by
    intro n
    rw [Set.disjoint_iff]
    intro x hx1
    exact hx1.1.2 hx1.2
  have hunion : ∀ n : ℕ, (Work.Spaces.Iθ \ Set.Icc (za n) (zb n)) ∪ Set.Icc (za n) (zb n)
      = Work.Spaces.Iθ := by
    intro n
    ext x
    constructor
    · rintro (⟨h1, -⟩ | h2)
      · exact h1
      · exact hsub n h2
    · intro hx
      by_cases h : x ∈ Set.Icc (za n) (zb n)
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
  have hadd : ∀ n : ℕ, (∫ x in Work.Spaces.Iθ \ Set.Icc (za n) (zb n), g x)
      + (∫ x in Set.Icc (za n) (zb n), g x) = (∫ x in Work.Spaces.Iθ, g x) := by
    intro n
    rw [← MeasureTheory.setIntegral_union (hdisj n) measurableSet_Icc
      (hg.mono_set Set.sdiff_subset) (hg.mono_set (hsub n)), hunion n]
  have hpoint : ∀ n : ℕ, (∫ x in Set.Icc (za n) (zb n), g x)
      = (∫ x in Work.Spaces.Iθ, g x)
        - (∫ x in Work.Spaces.Iθ \ Set.Icc (za n) (zb n), g x) := fun n => by linarith [hadd n]
  have hlim2 : Tendsto (fun n : ℕ => ∫ x in Set.Icc (za n) (zb n), g x) atTop
      (nhds (∫ x in Work.Spaces.Iθ, g x)) := by
    have h' : Tendsto (fun n : ℕ => (∫ x in Work.Spaces.Iθ, g x)
        - (∫ x in Work.Spaces.Iθ \ Set.Icc (za n) (zb n), g x)) atTop
        (nhds ((∫ x in Work.Spaces.Iθ, g x) - 0)) := tendsto_const_nhds.sub hlim
    rw [sub_zero] at h'
    refine h'.congr' ?_
    filter_upwards with n
    exact (hpoint n).symm
  refine hlim2.congr' ?_
  filter_upwards with n
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_of_lt (za_lt_zb n))]

/-! ## §9. The endpoint analysis and the Cauchy–Schwarz bound -/

/-- The interval-integrability of the five integrands on an interior sub-interval. -/
private theorem intervalIntegrable_pieces {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi/2) (hab : a ≤ b) :
    IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => (f θ)^2 * Work.FTS.EllipticEst.thEta θ) volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => (f θ)^2 * csq θ) volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => f θ * deriv f θ * cs1 θ) volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => (deriv (deriv f) θ)^2 * Work.FTS.EllipticEst.thEta θ)
        volume a b := by
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
  have hcf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcf' : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen hIoo (by norm_num)).mono hmem
  have hcf'' : ContinuousOn (deriv (deriv f)) (Set.uIcc a b) := by
    have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hf.deriv_of_isOpen hIoo (by norm_num)
    exact (contDiffOn_zero.1 (h1.deriv_of_isOpen hIoo (by norm_num))).mono hmem
  have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinne : ∀ θ ∈ Set.uIcc a b, Real.sin (2*θ) ≠ 0 := fun θ hθ =>
    (sin_two_pos_of_mem (hmem θ hθ)).ne'
  have hσC : ContinuousOn Work.FTS.EllipticEst.thEta (Set.uIcc a b) :=
    hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
  have hcs1C : ContinuousOn cs1 (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.cos (2*θ)) (Set.uIcc a b) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  have hcsqC : ContinuousOn csq (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Real.cos (2*θ))^2) (Set.uIcc a b) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  exact ⟨((hcf'.pow 2).mul hσC).intervalIntegrable, ((hcf.mul hcf'').mul hσC).intervalIntegrable,
    ((hcf.pow 2).mul hσC).intervalIntegrable, ((hcf.pow 2).mul hcsqC).intervalIntegrable,
    ((hcf.mul hcf').mul hcs1C).intervalIntegrable, ((hcf''.pow 2).mul hσC).intervalIntegrable⟩

/-- The pointwise expansion of the completed square. -/
private theorem sq_expand_pointwise {f : ℝ → ℝ} {θ : ℝ} (hsin : 0 < Real.sin (2*θ)) :
    (deriv f θ - (1 + Work.Spaces.eta) * f θ * (Real.cos (2*θ)/Real.sin (2*θ)))^2
        * Work.FTS.EllipticEst.thEta θ
      = (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
        - 2*(1 + Work.Spaces.eta) * (f θ * deriv f θ * cs1 θ)
        + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ) := by
  have k1 : Real.cos (2*θ)/Real.sin (2*θ) * Work.FTS.EllipticEst.thEta θ = cs1 θ :=
    cossin_mul_thEta hsin
  have k2 : (Real.cos (2*θ)/Real.sin (2*θ))^2 * Work.FTS.EllipticEst.thEta θ = csq θ :=
    cossin_sq_mul_thEta hsin
  calc (deriv f θ - (1 + Work.Spaces.eta) * f θ * (Real.cos (2*θ)/Real.sin (2*θ)))^2
        * Work.FTS.EllipticEst.thEta θ
      = ((deriv f θ)^2
          - 2*(1 + Work.Spaces.eta)*(deriv f θ * f θ * (Real.cos (2*θ)/Real.sin (2*θ)))
          + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * (Real.cos (2*θ)/Real.sin (2*θ))^2))
        * Work.FTS.EllipticEst.thEta θ := by ring
    _ = (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * ((deriv f θ * f θ)
              * ((Real.cos (2*θ)/Real.sin (2*θ)) * Work.FTS.EllipticEst.thEta θ))
          + (1 + Work.Spaces.eta)^2 * ((f θ)^2
              * ((Real.cos (2*θ)/Real.sin (2*θ))^2 * Work.FTS.EllipticEst.thEta θ)) := by ring
    _ = (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * ((deriv f θ * f θ) * cs1 θ)
          + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ) := by rw [k1, k2]
    _ = (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * (f θ * deriv f θ * cs1 θ)
          + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ) := by ring

/-- The two endpoint weights `f f' σ` and `f² cs1` vanish along the truncating sequence. -/
private theorem traceBoundarySeq {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    (h0 : Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Tendsto f (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0))
    (hA : IntegrableOn (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi/2)))
    (hE : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ)^2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi/2))) :
    (Tendsto (fun n : ℕ => f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n))
        atTop (nhds 0))
    ∧ (Tendsto (fun n : ℕ => (f (za n))^2 * cs1 (za n)) atTop (nhds 0))
    ∧ (Tendsto (fun n : ℕ => f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n))
        atTop (nhds 0))
    ∧ (Tendsto (fun n : ℕ => (f (zb n))^2 * cs1 (zb n)) atTop (nhds 0)) := by
  obtain ⟨K, hKpos, hmain⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  obtain ⟨c1, hc1tend, hc1bnd⟩ := (hmain f (hf.of_le (by norm_num)) hA).1
  have hc1z : c1 = 0 := tendsto_nhds_unique hc1tend h0
  obtain ⟨c2, hc2tend, hc2bnd⟩ := (hmain (deriv f) hd1 hE).1
  obtain ⟨d1, hd1tend, hd1bnd⟩ := (hmain f (hf.of_le (by norm_num)) hA).2
  have hd1z : d1 = 0 := tendsto_nhds_unique hd1tend h1
  obtain ⟨d2, hd2tend, hd2bnd⟩ := (hmain (deriv f) hd1 hE).2
  set Aoo : ℝ := ∫ t in Set.Ioo (0:ℝ) (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t
    with hAoo
  set Eoo : ℝ := ∫ t in Set.Ioo (0:ℝ) (Real.pi/2),
    (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t with hEoo
  have hAoonn : 0 ≤ Aoo := by
    rw [hAoo]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (le_of_lt (thEta_pos_of_mem ht)))
  have hEoonn : 0 ≤ Eoo := by
    rw [hEoo]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (le_of_lt (thEta_pos_of_mem ht)))
  -- the two Agmon bounds at the left endpoint
  have hbndfL : ∀ n : ℕ, (f (za n))^2 ≤ K * (za n)^(1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo (0:ℝ) (za n), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by
    intro n
    have h := hc1bnd (za n) (za_mem n)
    rw [hc1z, sub_zero] at h
    exact h
  have hbndgL : ∀ n : ℕ, (deriv f (za n) - c2)^2 ≤ K * (za n)^(1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo (0:ℝ) (za n), (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) :=
    fun n => hc2bnd (za n) (za_mem n)
  -- the two Agmon bounds at the right endpoint
  have hbndfR : ∀ n : ℕ, (f (zb n))^2 ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo (zb n) (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by
    intro n
    have h := hd1bnd (zb n) (zb_mem n)
    rw [hd1z, sub_zero] at h
    exact h
  have hbndgR : ∀ n : ℕ, (deriv f (zb n) - d2)^2 ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo (zb n) (Real.pi/2), (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) :=
    fun n => hd2bnd (zb n) (zb_mem n)
  have hδn : ∀ n : ℕ, Real.pi/2 - zb n = za n := by
    intro n
    rw [zb, za]; ring
  have htailAL : ∀ n : ℕ, (∫ t in Set.Ioo (0:ℝ) (za n),
      (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) ≤ Aoo := by
    intro n
    rw [hAoo]
    refine MeasureTheory.setIntegral_mono_set hA ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem ht))
    · filter_upwards with t ht
      exact ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt (za_mem n).2)⟩
  have htailEL : ∀ n : ℕ, (∫ t in Set.Ioo (0:ℝ) (za n),
      (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) ≤ Eoo := by
    intro n
    rw [hEoo]
    refine MeasureTheory.setIntegral_mono_set hE ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem ht))
    · filter_upwards with t ht
      exact ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt (za_mem n).2)⟩
  have htailAR : ∀ n : ℕ, (∫ t in Set.Ioo (zb n) (Real.pi/2),
      (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) ≤ Aoo := by
    intro n
    rw [hAoo]
    refine MeasureTheory.setIntegral_mono_set hA ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem ht))
    · filter_upwards with t ht
      exact ⟨lt_trans (zb_mem n).1 ht.1, ht.2⟩
  have htailER : ∀ n : ℕ, (∫ t in Set.Ioo (zb n) (Real.pi/2),
      (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) ≤ Eoo := by
    intro n
    rw [hEoo]
    refine MeasureTheory.setIntegral_mono_set hE ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem ht))
    · filter_upwards with t ht
      exact ⟨lt_trans (zb_mem n).1 ht.1, ht.2⟩
  -- the bounds on the factors
  have hfbL : ∀ n : ℕ, |f (za n)| ≤ Real.sqrt (K * Aoo) * (za n)^((1 + Work.Spaces.eta)/2) := by
    intro n
    have h1 : (f (za n))^2 ≤ K * Aoo * (za n)^(1 + Work.Spaces.eta) := by
      have h2 := hbndfL n
      have h3 := htailAL n
      calc (f (za n))^2 ≤ K * (za n)^(1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo (0:ℝ) (za n), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := h2
        _ ≤ K * (za n)^(1 + Work.Spaces.eta) * Aoo :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hKpos.le
              (Real.rpow_nonneg (le_of_lt (za_pos n)) _))
        _ = K * Aoo * (za n)^(1 + Work.Spaces.eta) := by ring
    have h2 : Real.sqrt ((f (za n))^2) ≤ Real.sqrt (K * Aoo * (za n)^(1 + Work.Spaces.eta)) :=
      Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs] at h2
    rw [sqrt_mul_rpow_half (mul_nonneg hKpos.le hAoonn) (le_of_lt (za_pos n))] at h2
    exact h2
  have hfdL : ∀ n : ℕ, |deriv f (za n)| ≤ |c2| + Real.sqrt (K * Eoo) := by
    intro n
    have h1 : (deriv f (za n) - c2)^2 ≤ K * Eoo := by
      have h2 := hbndgL n
      have h3 := htailEL n
      calc (deriv f (za n) - c2)^2 ≤ K * (za n)^(1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo (0:ℝ) (za n),
                (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) := h2
        _ ≤ K * (za n)^(1 + Work.Spaces.eta) * Eoo :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hKpos.le
              (Real.rpow_nonneg (le_of_lt (za_pos n)) _))
        _ ≤ K * 1 * Eoo := by
            refine mul_le_mul_of_nonneg_right ?_ hEoonn
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            refine le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_ge (za_pos n)
              (by linarith [za_le_half n]) (by have := Work.Spaces.eta_pos; linarith))
              (Real.rpow_zero _)
        _ = K * Eoo := by ring
    have h2 : |deriv f (za n) - c2| ≤ Real.sqrt (K * Eoo) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    have h3 : |deriv f (za n)| = |(deriv f (za n) - c2) + c2| := by ring_nf
    rw [h3]
    linarith [h2, abs_add_le (deriv f (za n) - c2) c2]
  have hfbR : ∀ n : ℕ, |f (zb n)| ≤ Real.sqrt (K * Aoo) * (Real.pi/2 - zb n)^((1 + Work.Spaces.eta)/2) := by
    intro n
    have h1 : (f (zb n))^2 ≤ K * Aoo * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta) := by
      have h2 := hbndfR n
      have h3 := htailAR n
      calc (f (zb n))^2 ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo (zb n) (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := h2
        _ ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta) * Aoo :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hKpos.le
              (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _))
        _ = K * Aoo * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta) := by ring
    have h2 : Real.sqrt ((f (zb n))^2) ≤
        Real.sqrt (K * Aoo * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs] at h2
    rw [sqrt_mul_rpow_half (mul_nonneg hKpos.le hAoonn) (by linarith [zb_lt_pi2 n])] at h2
    exact h2
  have hfdR : ∀ n : ℕ, |deriv f (zb n)| ≤ |d2| + Real.sqrt (K * Eoo) := by
    intro n
    have h1 : (deriv f (zb n) - d2)^2 ≤ K * Eoo := by
      have h2 := hbndgR n
      have h3 := htailER n
      calc (deriv f (zb n) - d2)^2 ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo (zb n) (Real.pi/2),
                (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) := h2
        _ ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta) * Eoo :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hKpos.le
              (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _))
        _ ≤ K * 1 * Eoo := by
            refine mul_le_mul_of_nonneg_right ?_ hEoonn
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            have h4 : Real.pi/2 - zb n ≤ 1 := by rw [hδn n]; linarith [za_le_half n]
            refine le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_ge
              (by linarith [zb_lt_pi2 n]) h4 (by have := Work.Spaces.eta_pos; linarith))
              (Real.rpow_zero _)
        _ = K * Eoo := by ring
    have h2 : |deriv f (zb n) - d2| ≤ Real.sqrt (K * Eoo) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    have h3 : |deriv f (zb n)| = |(deriv f (zb n) - d2) + d2| := by ring_nf
    rw [h3]
    linarith [h2, abs_add_le (deriv f (zb n) - d2) d2]
  -- the weight bounds
  have hσL : ∀ n : ℕ, Work.FTS.EllipticEst.thEta (za n)
      ≤ (4/Real.pi)^(-(Work.Spaces.eta)) * (za n)^(-(Work.Spaces.eta)) := by
    intro n
    calc Work.FTS.EllipticEst.thEta (za n) ≤ ((4/Real.pi) * (za n))^(-(Work.Spaces.eta)) :=
          thEta_le_left (za_pos n) (le_of_lt (za_lt_pi4 n))
      _ = (4/Real.pi)^(-(Work.Spaces.eta)) * (za n)^(-(Work.Spaces.eta)) :=
          Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (le_of_lt (za_pos n))
  have hσR : ∀ n : ℕ, Work.FTS.EllipticEst.thEta (zb n)
      ≤ (4/Real.pi)^(-(Work.Spaces.eta)) * (Real.pi/2 - zb n)^(-(Work.Spaces.eta)) := by
    intro n
    calc Work.FTS.EllipticEst.thEta (zb n)
          ≤ ((4/Real.pi) * (Real.pi/2 - zb n))^(-(Work.Spaces.eta)) :=
          thEta_le_right (zb_ge_pi4 n) (zb_lt_pi2 n)
      _ = (4/Real.pi)^(-(Work.Spaces.eta)) * (Real.pi/2 - zb n)^(-(Work.Spaces.eta)) :=
          Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (by linarith [zb_lt_pi2 n])
  have hcsL : ∀ n : ℕ, cs1 (za n)
      ≤ (4/Real.pi)^(-(1 + Work.Spaces.eta)) * (za n)^(-(1 + Work.Spaces.eta)) := by
    intro n
    calc cs1 (za n) ≤ ((4/Real.pi) * (za n))^(-(1 + Work.Spaces.eta)) :=
          cs1_le_left (za_pos n) (le_of_lt (za_lt_pi4 n))
      _ = (4/Real.pi)^(-(1 + Work.Spaces.eta)) * (za n)^(-(1 + Work.Spaces.eta)) :=
          Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (le_of_lt (za_pos n))
  have hcsR : ∀ n : ℕ, |cs1 (zb n)|
      ≤ (4/Real.pi)^(-(1 + Work.Spaces.eta)) * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta)) := by
    intro n
    have hδ0 : 0 < Real.pi/2 - zb n := by linarith [zb_lt_pi2 n]
    have hδ1 : Real.pi/2 - zb n ≤ Real.pi/4 := by rw [hδn n]; exact le_of_lt (za_lt_pi4 n)
    have hneg : cs1 (zb n) = - cs1 (Real.pi/2 - zb n) := by
      rw [cs1, cs1]
      have hsin : Real.sin (2*zb n) = Real.sin (2*(Real.pi/2 - zb n)) := by
        rw [show 2*zb n = Real.pi - 2*(Real.pi/2 - zb n) by ring, Real.sin_pi_sub]
      have hcos : Real.cos (2*zb n) = -Real.cos (2*(Real.pi/2 - zb n)) := by
        rw [show 2*zb n = Real.pi - 2*(Real.pi/2 - zb n) by ring, Real.cos_pi_sub]
      rw [hsin, hcos]; ring
    rw [hneg, abs_neg, abs_of_nonneg (cs1_nonneg_left hδ0 hδ1)]
    calc cs1 (Real.pi/2 - zb n) ≤ ((4/Real.pi) * (Real.pi/2 - zb n))^(-(1 + Work.Spaces.eta)) :=
          cs1_le_left hδ0 hδ1
      _ = (4/Real.pi)^(-(1 + Work.Spaces.eta))
            * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta)) :=
          Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (le_of_lt hδ0)
  -- the majorant constants
  set Mx : ℝ := (|c2| + Real.sqrt (K * Eoo)) * Real.sqrt (K * Aoo)
    * (4/Real.pi)^(-(Work.Spaces.eta)) with hMx
  set Md : ℝ := (|d2| + Real.sqrt (K * Eoo)) * Real.sqrt (K * Aoo)
    * (4/Real.pi)^(-(Work.Spaces.eta)) with hMd
  set Mq : ℝ := K * (4/Real.pi)^(-(1 + Work.Spaces.eta)) with hMq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun n : ℕ => ‖f (za n) * deriv f (za n)
        * Work.FTS.EllipticEst.thEta (za n)‖)
      (g := fun n : ℕ => Mx * (za n)^((1 - Work.Spaces.eta)/2))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [Real.norm_eq_abs]
      have hσnn : 0 ≤ Work.FTS.EllipticEst.thEta (za n) :=
        le_of_lt (thEta_pos_of_mem (za_mem n))
      calc |f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n)|
          = |f (za n)| * |deriv f (za n)| * Work.FTS.EllipticEst.thEta (za n) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hσnn]
        _ ≤ (Real.sqrt (K * Aoo) * (za n)^((1 + Work.Spaces.eta)/2))
              * (|c2| + Real.sqrt (K * Eoo))
              * ((4/Real.pi)^(-(Work.Spaces.eta)) * (za n)^(-(Work.Spaces.eta))) := by
            refine mul_le_mul (mul_le_mul (hfbL n) (hfdL n) (abs_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg (K * Aoo))
                (Real.rpow_nonneg (le_of_lt (za_pos n)) _)))
              (hσL n) hσnn ?_
            exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg (K * Aoo))
              (Real.rpow_nonneg (le_of_lt (za_pos n)) _))
              (add_nonneg (abs_nonneg _) (Real.sqrt_nonneg (K * Eoo)))
        _ = Mx * ((za n)^((1 + Work.Spaces.eta)/2) * (za n)^(-(Work.Spaces.eta))) := by
            rw [hMx]; ring
        _ = Mx * (za n)^((1 - Work.Spaces.eta)/2) := by
            rw [← Real.rpow_add (za_pos n)]
            congr 1
            ring
    · have hpow := tendsto_rpow_za (a := (1 - Work.Spaces.eta)/2)
        (by linarith [Work.Spaces.eta_lt_one])
      simpa using hpow.const_mul Mx
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun n : ℕ => ‖(f (za n))^2 * cs1 (za n)‖)
      (g := fun n : ℕ => Mq * (∫ t in Set.Ioo (0:ℝ) (za n),
        (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [Real.norm_eq_abs]
      have hcs1nn : 0 ≤ cs1 (za n) := cs1_nonneg_left (za_pos n) (le_of_lt (za_lt_pi4 n))
      have htailnn : 0 ≤ ∫ t in Set.Ioo (0:ℝ) (za n),
          (deriv f t)^2 * Work.FTS.EllipticEst.thEta t :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (le_of_lt (thEta_pos_of_mem ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt (za_mem n).2)⟩)))
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hcs1nn)]
      have h6 : (za n)^(1 + Work.Spaces.eta) * (za n)^(-(1 + Work.Spaces.eta)) = 1 := by
        rw [← Real.rpow_add (za_pos n),
          show (1 + Work.Spaces.eta) + (-(1 + Work.Spaces.eta)) = 0 by ring, Real.rpow_zero]
      calc (f (za n))^2 * cs1 (za n)
          ≤ (K * (za n)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo (0:ℝ) (za n), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
              * ((4/Real.pi)^(-(1 + Work.Spaces.eta)) * (za n)^(-(1 + Work.Spaces.eta))) := by
            refine mul_le_mul (hbndfL n) (hcsL n) hcs1nn ?_
            exact mul_nonneg (mul_nonneg hKpos.le
              (Real.rpow_nonneg (le_of_lt (za_pos n)) _)) htailnn
        _ = Mq * ((∫ t in Set.Ioo (0:ℝ) (za n),
              (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * ((za n)^(1 + Work.Spaces.eta) * (za n)^(-(1 + Work.Spaces.eta)))) := by
            rw [hMq]; ring
        _ = Mq * (∫ t in Set.Ioo (0:ℝ) (za n),
              (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by
            rw [h6]; ring
    · have htailA := tail_left (fun t : ℝ => (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) hA
      simpa using htailA.const_mul Mq
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun n : ℕ => ‖f (zb n) * deriv f (zb n)
        * Work.FTS.EllipticEst.thEta (zb n)‖)
      (g := fun n : ℕ => Md * (Real.pi/2 - zb n)^((1 - Work.Spaces.eta)/2))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [Real.norm_eq_abs]
      have hσnn : 0 ≤ Work.FTS.EllipticEst.thEta (zb n) :=
        le_of_lt (thEta_pos_of_mem (zb_mem n))
      calc |f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n)|
          = |f (zb n)| * |deriv f (zb n)| * Work.FTS.EllipticEst.thEta (zb n) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hσnn]
        _ ≤ (Real.sqrt (K * Aoo) * (Real.pi/2 - zb n)^((1 + Work.Spaces.eta)/2))
              * (|d2| + Real.sqrt (K * Eoo))
              * ((4/Real.pi)^(-(Work.Spaces.eta)) * (Real.pi/2 - zb n)^(-(Work.Spaces.eta))) := by
            refine mul_le_mul (mul_le_mul (hfbR n) (hfdR n) (abs_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg (K * Aoo))
                (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _)))
              (hσR n) hσnn ?_
            exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg (K * Aoo))
              (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _))
              (add_nonneg (abs_nonneg _) (Real.sqrt_nonneg (K * Eoo)))
        _ = Md * ((Real.pi/2 - zb n)^((1 + Work.Spaces.eta)/2)
              * (Real.pi/2 - zb n)^(-(Work.Spaces.eta))) := by
            rw [hMd]; ring
        _ = Md * (Real.pi/2 - zb n)^((1 - Work.Spaces.eta)/2) := by
            rw [← Real.rpow_add (by linarith [zb_lt_pi2 n])]
            congr 1
            ring
    · have hpow : Tendsto (fun n : ℕ => (Real.pi/2 - zb n)^((1 - Work.Spaces.eta)/2))
          atTop (nhds 0) := by
        refine (tendsto_rpow_za (a := (1 - Work.Spaces.eta)/2)
          (by linarith [Work.Spaces.eta_lt_one])).congr' ?_
        filter_upwards with n
        rw [hδn n]
      simpa using hpow.const_mul Md
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun n : ℕ => ‖(f (zb n))^2 * cs1 (zb n)‖)
      (g := fun n : ℕ => Mq * (∫ t in Set.Ioo (zb n) (Real.pi/2),
        (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [Real.norm_eq_abs]
      have htailnn : 0 ≤ ∫ t in Set.Ioo (zb n) (Real.pi/2),
          (deriv f t)^2 * Work.FTS.EllipticEst.thEta t :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (le_of_lt (thEta_pos_of_mem ⟨lt_trans (zb_mem n).1 ht.1, ht.2⟩)))
      have h6 : (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
          * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta)) = 1 := by
        rw [← Real.rpow_add (by linarith [zb_lt_pi2 n]),
          show (1 + Work.Spaces.eta) + (-(1 + Work.Spaces.eta)) = 0 by ring, Real.rpow_zero]
      calc |(f (zb n))^2 * cs1 (zb n)|
          = (f (zb n))^2 * |cs1 (zb n)| := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        _ ≤ (K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo (zb n) (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
              * ((4/Real.pi)^(-(1 + Work.Spaces.eta))
                * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta))) := by
            refine mul_le_mul (hbndfR n) (hcsR n) (abs_nonneg _) ?_
            exact mul_nonneg (mul_nonneg hKpos.le
              (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _)) htailnn
        _ = Mq * ((∫ t in Set.Ioo (zb n) (Real.pi/2),
              (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * ((Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
                  * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta)))) := by
            rw [hMq]; ring
        _ = Mq * (∫ t in Set.Ioo (zb n) (Real.pi/2),
              (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by
            rw [h6]; ring
    · have htailA := tail_right (fun t : ℝ => (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) hA
      simpa using htailA.const_mul Mq


/-- Two a.e.-equal forms of the angular interval. -/
private theorem Icc_ae_eq_Ioo_aux (a b : ℝ) : Set.Icc a b =ᵐ[MeasureTheory.volume] Set.Ioo a b := by
  have hpair : MeasureTheory.volume ({a, b} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({a, b} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  filter_upwards [hpairab] with x hx
  refine propext ⟨?_, ?_⟩
  · intro h
    rw [Set.mem_Icc] at h
    rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
      lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
  · intro h
    rw [Set.mem_Ioo] at h
    rw [Set.mem_Icc]
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩

/-- Integrability transfers from the closed to the open angular interval. -/
private theorem integrableOn_Ioo_of_Iθ {g : ℝ → ℝ} (hg : IntegrableOn g Work.Spaces.Iθ) :
    IntegrableOn g (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  rw [MeasureTheory.IntegrableOn] at hg ⊢
  exact MeasureTheory.Measure.restrict_congr_set (Icc_ae_eq_Ioo_aux 0 (Real.pi/2)) ▸ hg

theorem traceVanishingInterp : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  refine ⟨199, by norm_num, ?_⟩
  intro f hf h0 h1 hPint hAint hEint
  have hAintoo := integrableOn_Ioo_of_Iθ hAint
  have hEintoo := integrableOn_Ioo_of_Iθ hEint
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ)^2 * Work.FTS.EllipticEst.thEta θ with hPdef
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ with hAdef
  set E : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ)^2 * Work.FTS.EllipticEst.thEta θ with hEdef
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl]
    exact measurableSet_Icc
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))
  obtain ⟨hb1, hb2, hb3, hb4⟩ := traceBoundarySeq hf h0 h1 hAintoo hEintoo
  -- ## Cauchy–Schwarz on the full interval
  have hCS : ∀ n : ℕ, |∫ θ in (za n)..(zb n),
      f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ| ≤ Real.sqrt (P * E) := by
    intro n
    have ha := za_pos n
    have hb := zb_lt_pi2 n
    have hab := le_of_lt (za_lt_zb n)
    obtain ⟨hIA, hIB, hIC, hID, hIJ, hIE⟩ := intervalIntegrable_pieces hf ha hb hab
    have hmem : ∀ x ∈ Set.uIcc (za n) (zb n), x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    have hCcont : ContinuousOn (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        (Set.uIcc (za n) (zb n)) := by
      have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
      have hcf : ContinuousOn f (Set.uIcc (za n) (zb n)) := hf.continuousOn.mono hmem
      have hcf'' : ContinuousOn (deriv (deriv f)) (Set.uIcc (za n) (zb n)) := by
        have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
          hf.deriv_of_isOpen hIoo (by norm_num)
        exact (contDiffOn_zero.1 (h1.deriv_of_isOpen hIoo (by norm_num))).mono hmem
      have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc (za n) (zb n)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      have hσC : ContinuousOn Work.FTS.EllipticEst.thEta (Set.uIcc (za n) (zb n)) :=
        hsinC.rpow_const (fun θ hθ => Or.inl (sin_two_pos_of_mem (hmem θ hθ)).ne')
      exact (hcf.mul hcf'').mul hσC
    have hCs : IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioc (za n) (zb n)) := hCcont.intervalIntegrable.1
    have hcs := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
      (s := Set.Ioc (za n) (zb n))
      (A := fun θ : ℝ => (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      (B := fun θ : ℝ => (deriv (deriv f) θ)^2 * Work.FTS.EllipticEst.thEta θ)
      (C := fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
      hIC.1 hIE.1 hCs
      (fun z hz => mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem
        ⟨lt_trans ha hz.1, lt_of_le_of_lt hz.2 hb⟩)))
      (fun z hz => mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem
        ⟨lt_trans ha hz.1, lt_of_le_of_lt hz.2 hb⟩)))
      (fun z hz => by
        have hz' : z ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
          ⟨lt_trans ha hz.1, lt_of_le_of_lt hz.2 hb⟩
        have hσnn : 0 ≤ Work.FTS.EllipticEst.thEta z := le_of_lt (thEta_pos_of_mem hz')
        have hsq : Real.sqrt (Work.FTS.EllipticEst.thEta z)
            * Real.sqrt (Work.FTS.EllipticEst.thEta z) = Work.FTS.EllipticEst.thEta z := by
          rw [show Real.sqrt (Work.FTS.EllipticEst.thEta z)
                * Real.sqrt (Work.FTS.EllipticEst.thEta z)
              = (Real.sqrt (Work.FTS.EllipticEst.thEta z))^2 by rw [pow_two],
            Real.sq_sqrt hσnn]
        rw [abs_mul, abs_mul, abs_of_nonneg hσnn,
          Real.sqrt_mul (sq_nonneg (f z)), Real.sqrt_mul (sq_nonneg (deriv (deriv f) z)),
          Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
          show (|f z| * Real.sqrt (Work.FTS.EllipticEst.thEta z))
                * (|deriv (deriv f) z| * Real.sqrt (Work.FTS.EllipticEst.thEta z))
              = |f z| * |deriv (deriv f) z|
                * (Real.sqrt (Work.FTS.EllipticEst.thEta z)
                    * Real.sqrt (Work.FTS.EllipticEst.thEta z))
              by ring,
          hsq])
    have hAle : (∫ z in Set.Ioc (za n) (zb n), (f z)^2 * Work.FTS.EllipticEst.thEta z) ≤ P := by
      rw [hPdef]
      refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with z hz
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hz)
      · filter_upwards with z hz
        exact ⟨le_of_lt (lt_trans ha hz.1), le_of_lt (lt_of_le_of_lt hz.2 hb)⟩
    have hEle : (∫ z in Set.Ioc (za n) (zb n),
        (deriv (deriv f) z)^2 * Work.FTS.EllipticEst.thEta z) ≤ E := by
      rw [hEdef]
      refine MeasureTheory.setIntegral_mono_set hEint ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with z hz
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hz)
      · filter_upwards with z hz
        exact ⟨le_of_lt (lt_trans ha hz.1), le_of_lt (lt_of_le_of_lt hz.2 hb)⟩
    have hsqrt : Real.sqrt (∫ z in Set.Ioc (za n) (zb n), (f z)^2 * Work.FTS.EllipticEst.thEta z)
        * Real.sqrt (∫ z in Set.Ioc (za n) (zb n),
            (deriv (deriv f) z)^2 * Work.FTS.EllipticEst.thEta z)
        ≤ Real.sqrt P * Real.sqrt E :=
      mul_le_mul (Real.sqrt_le_sqrt hAle) (Real.sqrt_le_sqrt hEle)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc |∫ θ in (za n)..(zb n), f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ|
        = |∫ z in Set.Ioc (za n) (zb n),
            f z * deriv (deriv f) z * Work.FTS.EllipticEst.thEta z| := by
          rw [intervalIntegral.integral_of_le hab]
      _ ≤ Real.sqrt (∫ z in Set.Ioc (za n) (zb n), (f z)^2 * Work.FTS.EllipticEst.thEta z)
            * Real.sqrt (∫ z in Set.Ioc (za n) (zb n),
                (deriv (deriv f) z)^2 * Work.FTS.EllipticEst.thEta z) := hcs
      _ ≤ Real.sqrt P * Real.sqrt E := hsqrt
      _ = Real.sqrt (P * E) := (Real.sqrt_mul hPnn E).symm
  -- ## the key estimate on each truncated interval
  set Hf : ℕ → ℝ := fun n => (f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n)
        - Work.Spaces.eta * (f (zb n))^2 * cs1 (zb n))
      - (f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n)
        - Work.Spaces.eta * (f (za n))^2 * cs1 (za n)) with hHf
  have hkey : ∀ n : ℕ, (∫ θ in (za n)..(zb n), (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 199 * (Hf n + Real.sqrt (P * E)) := by
    intro n
    have ha := za_pos n
    have hb := zb_lt_pi2 n
    have hab := le_of_lt (za_lt_zb n)
    have hmem : ∀ x ∈ Set.uIcc (za n) (zb n), x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    obtain ⟨hIA, hIB, hIC, hID, hIJ, hIE⟩ := intervalIntegrable_pieces hf ha hb hab
    set An : ℝ := ∫ θ in (za n)..(zb n), (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ with hAn
    set Bn : ℝ := ∫ θ in (za n)..(zb n),
      f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ with hBn
    set Cn : ℝ := ∫ θ in (za n)..(zb n), (f θ)^2 * Work.FTS.EllipticEst.thEta θ with hCn
    set Dn : ℝ := ∫ θ in (za n)..(zb n), (f θ)^2 * csq θ with hDn
    set Jn : ℝ := ∫ θ in (za n)..(zb n), f θ * deriv f θ * cs1 θ with hJn
    have hI2J : IntervalIntegrable (fun θ : ℝ => (2*(1 + Work.Spaces.eta))
        * (f θ * deriv f θ * cs1 θ)) volume (za n) (zb n) := hIJ.const_mul _
    have hI2D : IntervalIntegrable (fun θ : ℝ => (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ))
        volume (za n) (zb n) := hID.const_mul _
    have hsub1 : IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
        - (2*(1 + Work.Spaces.eta)) * (f θ * deriv f θ * cs1 θ)) volume (za n) (zb n) :=
      hIA.sub hI2J
    have hS1 : An = (f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n)
            + Work.Spaces.eta * (f (zb n))^2 * cs1 (zb n))
        - (f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n)
            + Work.Spaces.eta * (f (za n))^2 * cs1 (za n))
        - Bn + 2 * Work.Spaces.eta * Cn
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * Dn := by
      rw [hAn, hBn, hCn, hDn]
      exact ibp_main hf ha hb hab
    have hS2 : Jn = Cn + (1 + Work.Spaces.eta) * Dn
        + (1/2) * ((f (zb n))^2 * cs1 (zb n) - (f (za n))^2 * cs1 (za n)) := by
      rw [hJn, hCn, hDn]
      exact ibp_cot hf ha hb hab
    have hQnn : 0 ≤ An - 2*(1 + Work.Spaces.eta)*Jn + (1 + Work.Spaces.eta)^2*Dn := by
      have hcongr : (∫ θ in (za n)..(zb n), (deriv f θ - (1 + Work.Spaces.eta) * f θ
            * (Real.cos (2*θ)/Real.sin (2*θ)))^2 * Work.FTS.EllipticEst.thEta θ)
          = ∫ θ in (za n)..(zb n), ((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
              - 2*(1 + Work.Spaces.eta) * (f θ * deriv f θ * cs1 θ)
              + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ)) :=
        intervalIntegral.integral_congr
          (fun θ hθ => sq_expand_pointwise (sin_two_pos_of_mem (hmem θ hθ)))
      have hnonneg : 0 ≤ ∫ θ in (za n)..(zb n), (deriv f θ - (1 + Work.Spaces.eta) * f θ
          * (Real.cos (2*θ)/Real.sin (2*θ)))^2 * Work.FTS.EllipticEst.thEta θ := by
        rw [intervalIntegral.integral_of_le hab]
        exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun θ hθ => mul_nonneg (sq_nonneg _)
          (le_of_lt (thEta_pos_of_mem ⟨lt_trans ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)))
      have hlin : (∫ θ in (za n)..(zb n), ((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
              - 2*(1 + Work.Spaces.eta) * (f θ * deriv f θ * cs1 θ)
              + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ)))
          = An - 2*(1 + Work.Spaces.eta)*Jn + (1 + Work.Spaces.eta)^2*Dn := by
        rw [hAn, hJn, hDn]
        rw [intervalIntegral.integral_add hsub1 hI2D, intervalIntegral.integral_sub hIA hI2J,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      linarith [hcongr, hnonneg, hlin]
    have hDle : (1 + Work.Spaces.eta)^2 * Dn ≤ An - 2*(1 + Work.Spaces.eta)*Cn
        - (1 + Work.Spaces.eta) * ((f (zb n))^2 * cs1 (zb n) - (f (za n))^2 * cs1 (za n)) := by
      have h1 : 2*(1 + Work.Spaces.eta)*Jn = 2*(1 + Work.Spaces.eta)*Cn
          + 2*(1 + Work.Spaces.eta)^2*Dn
          + (1 + Work.Spaces.eta)*((f (zb n))^2 * cs1 (zb n) - (f (za n))^2 * cs1 (za n)) := by
        rw [hS2]; ring
      nlinarith [hQnn, h1]
    have hCn0 : 0 ≤ Cn := by
      rw [hCn, intervalIntegral.integral_of_le hab]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun θ hθ => mul_nonneg (sq_nonneg _)
        (le_of_lt (thEta_pos_of_mem ⟨lt_trans ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)))
    have hstep : An * (1 - Work.Spaces.eta) ≤ (1 + Work.Spaces.eta) * (Hf n + |Bn|) := by
      rw [hHf]
      have heta : Work.Spaces.eta = 99/100 := rfl
      rw [heta] at hS1 hDle ⊢
      nlinarith [hS1, hDle, hCn0, neg_le_abs Bn]
    have hstep2 : An ≤ 199 * (Hf n + Real.sqrt (P * E)) := by
      have hbn : |Bn| ≤ Real.sqrt (P * E) := hCS n
      have hXn : Hf n + |Bn| ≤ Hf n + Real.sqrt (P * E) := by linarith [hbn]
      have h2 : (1 + Work.Spaces.eta) * (Hf n + |Bn|)
          ≤ (1 + Work.Spaces.eta) * (Hf n + Real.sqrt (P * E)) :=
        mul_le_mul_of_nonneg_left hXn (by have := Work.Spaces.eta_pos; linarith)
      rw [hHf] at hstep h2 ⊢
      have heta : Work.Spaces.eta = 99/100 := rfl
      rw [heta] at hstep h2 ⊢
      nlinarith [hstep, h2]
    exact hstep2
  -- ## the limit
  have hlimH : Tendsto (fun n : ℕ => 199 * (Hf n + Real.sqrt (P * E))) atTop
      (nhds (199 * Real.sqrt (P * E))) := by
    have hL : Tendsto (fun n : ℕ => f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n)
        - Work.Spaces.eta * (f (za n))^2 * cs1 (za n)) atTop (nhds 0) := by
      have h := hb1.sub (hb2.const_mul Work.Spaces.eta)
      simpa using (h.congr' (Eventually.of_forall fun n => by ring))
    have hR : Tendsto (fun n : ℕ => f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n)
        - Work.Spaces.eta * (f (zb n))^2 * cs1 (zb n)) atTop (nhds 0) := by
      have h := hb3.sub (hb4.const_mul Work.Spaces.eta)
      simpa using (h.congr' (Eventually.of_forall fun n => by ring))
    have h3 : Tendsto (fun n : ℕ => Hf n + Real.sqrt (P * E)) atTop
        (nhds (0 + Real.sqrt (P * E))) := by
      rw [hHf]
      have h4 := (hR.sub hL).add (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Real.sqrt (P * E)) atTop (nhds (Real.sqrt (P * E))))
      simpa using h4
    simpa using h3.const_mul 199
  have hlimA : Tendsto (fun n : ℕ => ∫ θ in (za n)..(zb n),
      (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) atTop (nhds A) := by
    have h0 : Tendsto (fun n : ℕ => ∫ θ in (za n)..(zb n),
        (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) atTop
        (nhds (∫ θ in Work.Spaces.Iθ, (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)) :=
      expandingIntegral (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) hAint
        (fun θ hθ => mul_nonneg (sq_nonneg (deriv f θ)) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    exact h0
  have hlim : A ≤ 199 * Real.sqrt (P * E) :=
    le_of_tendsto_of_tendsto' hlimA hlimH hkey
  have hgoal : A ≤ 199 * (P + Real.sqrt (P * E)) := by
    have h2 : Real.sqrt (P * E) ≤ P + Real.sqrt (P * E) := le_add_of_nonneg_left hPnn
    nlinarith [hlim, h2]
  rw [hAdef, hPdef, hEdef] at hgoal
  exact hgoal

end

end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.RRKop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The real (`deriv`-level) form of the transported operator: this is `bslOp α` in the
`(σ,θ)`-coordinates at `z = exp (α σ)` for a test function of the form `ψ (log z / α) θ`. -/
def kopDr (ψ : ℝ → ℝ → ℝ) (σ θ : ℝ) : ℝ :=
  - deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ
    - deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ
    - 5 * deriv (fun σ' => ψ σ' θ) σ
    + Real.tan θ * deriv (fun θ' => ψ σ θ') θ
    + ((Real.tan θ) ^ 2 - 5) * ψ σ θ

/-- `deriv` commutes with (the composition by) a continuous linear map. -/
lemma deriv_clm_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ℝ → E} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun y => L (f y)) x = L (deriv f x) := by
  have h2 : HasFDerivAt (fun y : ℝ => L (f y)) (L.comp (fderiv ℝ f x)) x :=
    L.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h2.hasDerivAt.deriv, ContinuousLinearMap.comp_apply, (hf.hasFDerivAt.hasDerivAt).deriv]

/-- The real part of the derivative of a complex-valued function is the derivative of its real
part. -/
lemma deriv_re_fst {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    (deriv f x).re = deriv (fun y => (f y).re) x := by
  have h := deriv_clm_comp (L := Complex.reCLM) hf
  simpa [Complex.reCLM_apply] using h.symm

/-- The imaginary part of the derivative of a complex-valued function is the derivative of its
imaginary part. -/
lemma deriv_im_fst {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    (deriv f x).im = deriv (fun y => (f y).im) x := by
  have h := deriv_clm_comp (L := Complex.imCLM) hf
  simpa [Complex.imCLM_apply] using h.symm

/-- Differentiability of the `σ`-slices of a smooth function of two variables. -/
lemma contDiff2_fst_slice {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (θ : ℝ) : ContDiff ℝ 2 (fun σ' : ℝ => ψ σ' θ) := by
  have h : ContDiff ℝ 2 (fun σ' : ℝ => (σ', θ)) := ContDiff.prodMk contDiff_id contDiff_const
  have h2 : ContDiff ℝ 2 (fun σ' : ℝ => Function.uncurry ψ (σ', θ)) := (hψ 2).comp h
  simpa [Function.uncurry] using h2

/-- Differentiability of the `θ`-slices of a smooth function of two variables. -/
lemma contDiff2_snd_slice {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (σ : ℝ) : ContDiff ℝ 2 (fun θ' : ℝ => ψ σ θ') := by
  have h : ContDiff ℝ 2 (fun θ' : ℝ => (σ, θ')) := ContDiff.prodMk contDiff_const contDiff_id
  have h2 : ContDiff ℝ 2 (fun θ' : ℝ => Function.uncurry ψ (σ, θ')) := (hψ 2).comp h
  simpa [Function.uncurry] using h2

/-- **The real part of `kopD`.** -/
lemma kopD_re {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (σ θ : ℝ) :
    (kopD ψ σ θ).re = kopDr (fun σ θ => (ψ σ θ).re) σ θ := by
  have hσ : ContDiff ℝ 2 (fun σ' : ℝ => ψ σ' θ) := contDiff2_fst_slice hψ θ
  have hθ : ContDiff ℝ 2 (fun θ' : ℝ => ψ σ θ') := contDiff2_snd_slice hψ σ
  have hdσ : DifferentiableAt ℝ (fun σ' : ℝ => ψ σ' θ) σ := (hσ.differentiable (by norm_num)) σ
  have hdθ : DifferentiableAt ℝ (fun θ' : ℝ => ψ σ θ') θ := (hθ.differentiable (by norm_num)) θ
  have hdσ2 : DifferentiableAt ℝ (deriv (fun σ' : ℝ => ψ σ' θ)) σ :=
    hσ.differentiable_deriv_two σ
  have hdθ2 : DifferentiableAt ℝ (deriv (fun θ' : ℝ => ψ σ θ')) θ :=
    hθ.differentiable_deriv_two θ
  have hA : (deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ).re
      = deriv (fun σ' => deriv (fun σ'' => (ψ σ'' θ).re) σ') σ := by
    rw [deriv_re_fst (f := fun σ' : ℝ => deriv (fun σ'' : ℝ => ψ σ'' θ) σ') hdσ2]
    congr 1
    funext σ'
    exact deriv_re_fst (f := fun σ'' : ℝ => ψ σ'' θ) ((hσ.differentiable (by norm_num)) σ')
  have hB : (deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ).re
      = deriv (fun θ' => deriv (fun θ'' => (ψ σ θ'').re) θ') θ := by
    rw [deriv_re_fst (f := fun θ' : ℝ => deriv (fun θ'' : ℝ => ψ σ θ'') θ') hdθ2]
    congr 1
    funext θ'
    exact deriv_re_fst (f := fun θ'' : ℝ => ψ σ θ'') ((hθ.differentiable (by norm_num)) θ')
  have hC : (deriv (fun σ' => ψ σ' θ) σ).re = deriv (fun σ' => (ψ σ' θ).re) σ :=
    deriv_re_fst (f := fun σ' : ℝ => ψ σ' θ) hdσ
  have hD : (deriv (fun θ' => ψ σ θ') θ).re = deriv (fun θ' => (ψ σ θ').re) θ :=
    deriv_re_fst (f := fun θ' : ℝ => ψ σ θ') hdθ
  have h5 : (5 : ℂ) = ((5 : ℝ) : ℂ) := by norm_num
  simp only [kopD]
  rw [h5]
  simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, zero_add]
  rw [hA, hB, hC, hD]
  simp only [kopDr]
  ring

/-- **The imaginary part of `kopD`.** -/
lemma kopD_im {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (σ θ : ℝ) :
    (kopD ψ σ θ).im = kopDr (fun σ θ => (ψ σ θ).im) σ θ := by
  have hσ : ContDiff ℝ 2 (fun σ' : ℝ => ψ σ' θ) := contDiff2_fst_slice hψ θ
  have hθ : ContDiff ℝ 2 (fun θ' : ℝ => ψ σ θ') := contDiff2_snd_slice hψ σ
  have hdσ : DifferentiableAt ℝ (fun σ' : ℝ => ψ σ' θ) σ := (hσ.differentiable (by norm_num)) σ
  have hdθ : DifferentiableAt ℝ (fun θ' : ℝ => ψ σ θ') θ := (hθ.differentiable (by norm_num)) θ
  have hdσ2 : DifferentiableAt ℝ (deriv (fun σ' : ℝ => ψ σ' θ)) σ :=
    hσ.differentiable_deriv_two σ
  have hdθ2 : DifferentiableAt ℝ (deriv (fun θ' : ℝ => ψ σ θ')) θ :=
    hθ.differentiable_deriv_two θ
  have hA : (deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ).im
      = deriv (fun σ' => deriv (fun σ'' => (ψ σ'' θ).im) σ') σ := by
    rw [deriv_im_fst (f := fun σ' : ℝ => deriv (fun σ'' : ℝ => ψ σ'' θ) σ') hdσ2]
    congr 1
    funext σ'
    exact deriv_im_fst (f := fun σ'' : ℝ => ψ σ'' θ) ((hσ.differentiable (by norm_num)) σ')
  have hB : (deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ).im
      = deriv (fun θ' => deriv (fun θ'' => (ψ σ θ'').im) θ') θ := by
    rw [deriv_im_fst (f := fun θ' : ℝ => deriv (fun θ'' : ℝ => ψ σ θ'') θ') hdθ2]
    congr 1
    funext θ'
    exact deriv_im_fst (f := fun θ'' : ℝ => ψ σ θ'') ((hθ.differentiable (by norm_num)) θ')
  have hC : (deriv (fun σ' => ψ σ' θ) σ).im = deriv (fun σ' => (ψ σ' θ).im) σ :=
    deriv_im_fst (f := fun σ' : ℝ => ψ σ' θ) hdσ
  have hD : (deriv (fun θ' => ψ σ θ') θ).im = deriv (fun θ' => (ψ σ θ').im) θ :=
    deriv_im_fst (f := fun θ' : ℝ => ψ σ θ') hdθ
  have h5 : (5 : ℂ) = ((5 : ℝ) : ℂ) := by norm_num
  simp only [kopD]
  rw [h5]
  simp only [Complex.neg_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_add, zero_mul]
  rw [hA, hB, hC, hD]
  simp only [kopDr]
  try ring

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.bslOp_congr_of_isOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## Locality of `bslOp α` on an arbitrary open set

`Work.Elliptic.bslOp α Ψ` is built from the operators `∂_z`, `∂_z²`, `∂_θ²` and the
θ-derivative of `tan θ · Ψ`, together with pointwise evaluation of `Ψ`.  Each is local:
if two functions agree on an open set `V`, their `z`- and `θ`-derivatives agree there too
(`Work.Spaces.pz_congr_of_isOpen`, `Work.Spaces.pth_congr_of_isOpen`, iterated below).
Hence `bslOp α φ` and `bslOp α g` agree on `V` whenever `φ` and `g` do.

The iterated version is the only place where openness (rather than mere pointwise
agreement) is used: the derivative at a point only sees a neighbourhood of that point. -/

/-- Functions agreeing on an open set have the same iterated `z`-derivatives there. -/
lemma pzIter_congr_of_isOpen_aux {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pzIter k f))
      (Function.uncurry (Work.Spaces.pzIter k g)) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      exact Work.Spaces.pz_congr_of_isOpen hV ih hy

/-- Functions agreeing on an open set have the same iterated `θ`-derivatives there. -/
lemma pthIter_congr_of_isOpen_aux {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter k f))
      (Function.uncurry (Work.Spaces.pthIter k g)) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      exact Work.Spaces.pth_congr_of_isOpen hV ih hy

/-- Multiplication by `tan θ` preserves agreement on an open set. -/
lemma tan_mul_eqOn_of_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (fun z θ => Real.tan θ * f z θ))
      (Function.uncurry (fun z θ => Real.tan θ * g z θ)) V := by
  intro p hp
  have hp' : f p.1 p.2 = g p.1 p.2 := h hp
  simp only [Function.uncurry]
  rw [hp']

/-- `Work.Elliptic.Lzero` is local on an open set. -/
lemma Lzero_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero f))
      (Function.uncurry (Work.Elliptic.Lzero g)) V := by
  intro y hy
  obtain ⟨z, θ⟩ := y
  have h0 : f z θ = g z θ := h hy
  have h2 : Work.Spaces.pthIter 2 f z θ = Work.Spaces.pthIter 2 g z θ :=
    pthIter_congr_of_isOpen_aux hV h 2 hy
  have h3 : Work.Spaces.pth (fun z θ => Real.tan θ * f z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z θ :=
    Work.Spaces.pth_congr_of_isOpen hV (tan_mul_eqOn_of_isOpen h) hy
  simp only [Function.uncurry, Work.Elliptic.Lzero, h0, h2, h3]

/-- **`bslOp α` is local on an open set**: functions agreeing on an open `V ⊆ ℝ²` have the same
`bslOp α` on `V`. -/
theorem bslOp_congr_of_isOpen {α : ℝ} {φ g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry φ) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (Work.Elliptic.bslOp α φ))
      (Function.uncurry (Work.Elliptic.bslOp α g)) V := by
  intro y hy
  obtain ⟨z, θ⟩ := y
  have h1 : Work.Spaces.pz φ z θ = Work.Spaces.pz g z θ :=
    Work.Spaces.pz_congr_of_isOpen hV h hy
  have h2 : Work.Spaces.pzIter 2 φ z θ = Work.Spaces.pzIter 2 g z θ :=
    pzIter_congr_of_isOpen_aux hV h 2 hy
  have h4 : Work.Elliptic.Lzero φ z θ = Work.Elliptic.Lzero g z θ :=
    Lzero_congr_of_isOpen hV h hy
  simp only [Function.uncurry, Work.Elliptic.bslOp_apply, h1, h2, h4]

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.exists_cutoff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option linter.unusedVariables false

/-- For `0 < A < L ≤ U < B` there is a smooth function `χ` with `χ = 1` on `[L,U]` and
`χ z ≠ 0 → A < z ∧ z < B` (i.e. the support of `χ` is contained in `(A,B)`).

Explicit witness: the product of the two Mathlib smooth transitions
`χ z = smoothTransition ((z - A)/(L - A)) * smoothTransition ((B - z)/(B - U))`. -/
theorem exists_cutoff {A L U B : ℝ} (hA : 0 < A) (hAL : A < L) (hLU : L ≤ U) (hUB : U < B) :
    ∃ χ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n χ) ∧ (∀ z : ℝ, χ z ≠ 0 → A < z ∧ z < B) ∧
      (∀ z : ℝ, L ≤ z → z ≤ U → χ z = 1) := by
  have hLA : 0 < L - A := by linarith
  have hBU : 0 < B - U := by linarith
  refine ⟨fun z => Real.smoothTransition ((z - A) / (L - A))
      * Real.smoothTransition ((B - z) / (B - U)), ?_, ?_, ?_⟩
  · intro n
    exact (Real.smoothTransition.contDiff.comp
        ((contDiff_id.sub contDiff_const).div_const (L - A))).mul
      (Real.smoothTransition.contDiff.comp
        ((contDiff_const.sub contDiff_id).div_const (B - U)))
  · intro z hz
    dsimp only at hz
    have h1 : Real.smoothTransition ((z - A) / (L - A)) ≠ 0 := fun h => hz (by rw [h, zero_mul])
    have h2 : Real.smoothTransition ((B - z) / (B - U)) ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have h1' : 0 < (z - A) / (L - A) := by
      by_contra hc
      exact h1 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
    have h2' : 0 < (B - z) / (B - U) := by
      by_contra hc
      exact h2 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
    exact ⟨sub_pos.mp ((div_pos_iff_of_pos_right hLA).mp h1'),
      sub_pos.mp ((div_pos_iff_of_pos_right hBU).mp h2')⟩
  · intro z hzL hzU
    dsimp only
    have h1 : 1 ≤ (z - A) / (L - A) := by rw [one_le_div hLA]; linarith
    have h2 : 1 ≤ (B - z) / (B - U) := by rw [one_le_div hBU]; linarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2,
      mul_one]

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.integrableOn_Q0_iff_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The determinant of `(c • 1).prodMap 1` acting on `ℝ × ℝ` is `c`. -/
private theorem det_toSpanSingleton_prodMap_one (c : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ c).prodMap (1 : ℝ →L[ℝ] ℝ)).det = c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    LinearMap.det_ring]
  simp

theorem integrableOn_Q0_iff_strip {α : ℝ} (hα : 0 < α) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : ℝ × ℝ → E) :
    MeasureTheory.IntegrableOn X Work.FTS.EllipticEst.Q0 ↔
      MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
          (α * Real.exp (α * q.1)) • X (Real.exp (α * q.1), q.2))
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  -- the substitution `(σ,θ) ↦ (exp (ασ), θ)` and its derivative
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (α * p.1), p.2) with hΦ
  set f' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fun p =>
    (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)).prodMap
      (1 : ℝ →L[ℝ] ℝ) with hf'
  set s : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) with hs'
  -- the half-strip is measurable
  have hs : MeasurableSet s := by rw [hs']; exact MeasurableSet.univ.prod measurableSet_Ioo
  -- the range of `σ ↦ exp (α σ)` is `(0,∞)`
  have hrange : Set.range (fun z : ℝ => Real.exp (α * z)) = Set.Ioi (0 : ℝ) := by
    have h1 : Set.range (fun z : ℝ => α * z) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      exact ⟨y / α, by field_simp⟩
    calc Set.range (fun z : ℝ => Real.exp (α * z))
        = Set.range (Real.exp ∘ fun z : ℝ => α * z) := rfl
      _ = Real.exp '' Set.range (fun z : ℝ => α * z) := Set.range_comp _ _
      _ = Real.exp '' Set.univ := by rw [h1]
      _ = Set.range Real.exp := Set.image_univ
      _ = Set.Ioi 0 := Real.range_exp
  -- the substitution maps the half-strip onto the open quadrant
  have himg : Φ '' s = Work.FTS.EllipticEst.Q0 := by
    rw [hΦ, hs', Work.FTS.EllipticEst.Q0]
    change (Prod.map (fun z : ℝ => Real.exp (α * z)) id) ''
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
        = Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
    rw [Set.prodMap_image_prod, Set.image_univ, hrange, Set.image_id]
  -- and it is injective there
  have hinj : Set.InjOn Φ s := by
    rw [hΦ]
    rintro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : a1 = b1 := by
      have : α * a1 = α * b1 := Real.exp_injective h1
      exact mul_left_cancel₀ hα.ne' this
    rw [h1', h2]
  -- its derivative on the half-strip
  have hderiv : ∀ p ∈ s, HasFDerivWithinAt Φ (f' p) s p := by
    intro p hp
    have h : HasDerivAt (fun z : ℝ => α * z) α p.1 := by
      simpa using (hasDerivAt_id (p.1 : ℝ)).const_mul α
    have hd : HasDerivAt (fun z : ℝ => Real.exp (α * z)) (Real.exp (α * p.1) * α) p.1 :=
      (Real.hasDerivAt_exp (α * p.1)).comp (p.1) h
    have h1 : HasFDerivAt (fun z : ℝ => Real.exp (α * z))
        (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)) p.1 :=
      hd.hasFDerivAt
    have h2 : HasFDerivAt (id : ℝ → ℝ) (1 : ℝ →L[ℝ] ℝ) p.2 := hasFDerivAt_id p.2
    have h3 := HasFDerivAt.prodMap p h1 h2
    rw [hΦ, hf']
    exact h3.hasFDerivWithinAt
  -- the general change of variables formula for integrability
  have key := MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))) (s := s) (f := Φ)
    (f' := f') hs hderiv hinj X
  rw [himg] at key
  rw [key]
  -- identify the Jacobian `|det| = α exp (α σ)`
  have hfun : (fun q : ℝ × ℝ => |(f' q).det| • X (Φ q))
      = fun q : ℝ × ℝ => (α * Real.exp (α * q.1)) • X (Real.exp (α * q.1), q.2) := by
    funext q
    simp only [hΦ, hf']
    rw [det_toSpanSingleton_prodMap_one,
      abs_of_pos (by positivity : (0 : ℝ) < Real.exp (α * q.1) * α),
      mul_comm (Real.exp (α * q.1)) α]
  rw [hfun]

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.integrableOn_pullback_wtRR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- The determinant of `(c • 1).prodMap 1` acting on `ℝ × ℝ` is `c`. -/
private theorem det_toSpanSingleton_prodMap_one_rr (c : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ c).prodMap (1 : ℝ →L[ℝ] ℝ)).det = c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    LinearMap.det_ring]
  simp

/-- **Change of variables `(σ,θ) ↦ (e^{ασ},θ)` with the absolute Jacobian `e^{ασ}|α|`.**
For `α ≠ 0`, `Ψ` locally integrable on the open quadrant `Q0`, and `K` a compact subset of the
half-strip `ℝ × (0,π/2)`, the function
`e^{ασ}|α| · Ψ(e^{ασ},θ)` is integrable on `K`. -/
theorem integrableOn_pullback_absJac {α : ℝ} (hα : α ≠ 0) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKs : K ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ =>
        ((Real.exp (α * p.1) * |α| : ℝ) : ℂ) *
          ((Ψ (Real.exp (α * p.1)) p.2 : ℝ) : ℂ)) K := by
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (α * p.1), p.2) with hΦ
  set Φ' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ × ℝ) := fun p =>
    (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)).prodMap
      (1 : ℝ →L[ℝ] ℝ) with hΦ'
  have hcont : Continuous Φ := by
    rw [hΦ]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).prodMk continuous_snd
  -- the image is a compact subset of the open quadrant
  have hsub : Φ '' K ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro y ⟨p, hp, rfl⟩
    exact ⟨Real.exp_pos _, (hKs hp).2.1, (hKs hp).2.2⟩
  have hcomp : IsCompact (Φ '' K) := hK.image hcont
  have hIntΨ : IntegrableOn (Function.uncurry Ψ) (Φ '' K) :=
    hΨ.integrableOn_compact_subset hsub hcomp
  have hIntC : IntegrableOn (fun y : ℝ × ℝ => ((Function.uncurry Ψ y : ℝ) : ℂ)) (Φ '' K) :=
    Complex.ofRealCLM.integrableOn_comp hIntΨ
  -- the derivative of `Φ` and its injectivity on `K`
  have hderiv : ∀ p ∈ K, HasFDerivWithinAt Φ (Φ' p) K p := by
    intro p _
    have h : HasDerivAt (fun z : ℝ => α * z) α p.1 := by
      simpa using (hasDerivAt_id (p.1 : ℝ)).const_mul α
    have hd : HasDerivAt (fun z : ℝ => Real.exp (α * z)) (Real.exp (α * p.1) * α) p.1 :=
      (Real.hasDerivAt_exp (α * p.1)).comp (p.1) h
    have h1 : HasFDerivAt (fun z : ℝ => Real.exp (α * z))
        (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)) p.1 :=
      hd.hasFDerivAt
    have h2 : HasFDerivAt (id : ℝ → ℝ) (1 : ℝ →L[ℝ] ℝ) p.2 := hasFDerivAt_id p.2
    have h3 := HasFDerivAt.prodMap p h1 h2
    rw [hΦ, hΦ']
    exact h3.hasFDerivWithinAt
  have hinj : InjOn Φ K := by
    rintro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
    rw [hΦ] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : a1 = b1 := by
      have : α * a1 = α * b1 := Real.exp_injective h1
      exact mul_left_cancel₀ hα this
    rw [h1', h2]
  -- the general change of variables formula for integrability
  have key := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) hK.measurableSet hderiv hinj
    (fun y : ℝ × ℝ => ((Function.uncurry Ψ y : ℝ) : ℂ))).mp hIntC
  refine IntegrableOn.congr_fun key (fun p _ => ?_) hK.measurableSet
  have hdet : (Φ' p).det = Real.exp (α * p.1) * α := by
    rw [hΦ']
    exact det_toSpanSingleton_prodMap_one_rr _
  rw [hdet, abs_mul, abs_of_pos (Real.exp_pos (α * p.1)), Complex.real_smul, hΦ]
  simp only [Function.uncurry]

/-- **Change of variables for the substitution `(σ,θ) ↦ (e^{ασ},θ)`, with the weight of `Vf`.**
For `α ≠ 0`, `Ψ` locally integrable on the open quadrant `Q0`, and `K` a compact subset of the
half-strip `stripRR`, the function `α e^{5σ} cos θ · Ψ (e^{ασ}, θ)` is integrable on `K`. -/
theorem integrableOn_pullback_wtRR {α : ℝ} (hα : α ≠ 0) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKs : K ⊆ Work.EllipticEst.InteriorRegularity.Q0.stripRR) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => ((Work.EllipticEst.InteriorRegularity.Q0.wtRR α p.1 p.2 *
        Ψ (Real.exp (α * p.1)) p.2 : ℝ) : ℂ)) K := by
  have hKs' : K ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := hKs
  have hjac := integrableOn_pullback_absJac hα hΨ hK hKs'
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · -- `α < 0`: the factor is `-e^{(5-α)σ} cos θ`
    have habs : |α| = -α := abs_of_neg hneg
    have hc : Continuous fun p : ℝ × ℝ =>
        ((-(Real.exp ((5 - α) * p.1) * Real.cos p.2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
          (Real.continuous_cos.comp continuous_snd)).neg)
    refine IntegrableOn.congr_fun (hjac.mul_continuousOn hc.continuousOn hK)
      (fun p _ => ?_) hK.measurableSet
    have he : Real.exp (α * p.1) * Real.exp ((5 - α) * p.1) = Real.exp (5 * p.1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj, wtRR, habs, ← he]
    ring
  · -- `0 < α`: the factor is `e^{(5-α)σ} cos θ`
    have habs : |α| = α := abs_of_pos hpos
    have hc : Continuous fun p : ℝ × ℝ =>
        ((Real.exp ((5 - α) * p.1) * Real.cos p.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
          (Real.continuous_cos.comp continuous_snd))
    refine IntegrableOn.congr_fun (hjac.mul_continuousOn hc.continuousOn hK)
      (fun p _ => ?_) hK.measurableSet
    have he : Real.exp (α * p.1) * Real.exp ((5 - α) * p.1) = Real.exp (5 * p.1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj, wtRR, habs, ← he]
    ring

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.smoothOn_Gf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

theorem smoothOn_Gf {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ n : ℕ, ContDiffOn ℝ n
      (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Gf α F x : ℂ))
      Work.EllipticEst.InteriorRegularity.stripE := by
  intro n
  -- The un-indicated transported source is `C^n` on the strip, by composition: the map
  -- `x ↦ (exp (α x 0), x 1)` sends the strip into the open quadrant, where `F` is `C^∞`.
  have hcomp : ContDiffOn ℝ n
      (fun x : E2 => Function.uncurry F (Real.exp (α * x 0), x 1)) stripE := by
    refine (hF.forall n).comp ?_ ?_
    · fun_prop
    · intro x hx
      exact ⟨Real.exp_pos _, hx.1, hx.2⟩
  -- multiply by the smooth weight and push through the real-to-complex coercion
  have hmul : ContDiffOn ℝ n
      (fun x : E2 => wt α x * Function.uncurry F (Real.exp (α * x 0), x 1)) stripE :=
    ((wt_contDiff α n).contDiffOn).mul hcomp
  have hc : ContDiffOn ℝ n
      (fun x : E2 =>
        ((wt α x * Function.uncurry F (Real.exp (α * x 0), x 1) : ℝ) : ℂ)) stripE :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hmul
  -- on the strip the indicator is the identity
  refine hc.congr ?_
  intro x hx
  simp only [Gf, Function.uncurry, Set.indicator_of_mem hx]

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.LHSDecomp.i0Family_le_of_interpOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.LHSDecomp


end Work.EllipticEst.LHSDecomp
end
-- ===== merged: Submission.Work.FTS.ClassC.mixedSlot_vanishing_weight_domination =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The sharp (`sin(2θ)^{2r-γ}`) domination of a mixed slot by the plain slots

The sibling `Work.FTS.ClassC.plainSlot_domination` bounds the mixed slot `D_z^j D_θ^i f` by the
plain slots `D_z^j ∂_θ^r f` `(1 ≤ r ≤ i)` with the *fixed* conormal weight
`sin(2θ)^{-η}`.  This cannot be sharpened to the weight `sin(2θ)^{2r-γ}`: the coefficient `a_{i,r}`
of `∂_θ^r f` in `D_θ^i f` carries exactly `sin(2θ)^r`, so the mixed slot really vanishes like
`sin(2θ)^i` at the angular endpoints, and the corresponding square summand
`(D_z^j ∂_θ^r f)² w² sin(2θ)^{2r-γ}` is *much* smaller near `θ = 0, π/2` than the `η`-version.

The proof below keeps the sharp power `sin(2θ)^r` all the way: from the exact expansion
`D_z^j D_θ^i f = Σ_r a_{i,r}(θ) D_z^j ∂_θ^r f` and the divisibility bound
`|a_{i,r}(θ)| ≤ K_r sin(2θ)^r` we get
`|D_z^j D_θ^i f · W| ≤ Σ_r K_r · (|D_z^j ∂_θ^r f| · w · sin(2θ)^{r-γ/2})`,
and one Cauchy–Schwarz (with the *unfixed* factors `K_r`) produces exactly the claimed sum
`Σ_r (D_z^j ∂_θ^r f)² w² sin(2θ)^{2r-γ}`. -/

/-- `sin (2θ)` is non-negative on `Iθ`. -/
private theorem sin_two_nonneg_on_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ Real.pi := by linarith [hθ.2]
  exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2

/-- **The Cauchy–Schwarz step in its sharp form.**  For `t > 0`, a finite index set `s ⊆ ℕ` and
arbitrary factors `Kc r`, `A r`,

`(Σ_{r∈s} Kc r · (A r · t^{r-γ/2}))² ≤ (Σ_{r∈s} Kc r²) · Σ_{r∈s} (A r)² · t^{2r-γ}`,

using `t^{r-γ/2} · t^{r-γ/2} = t^{2r-γ}`.  Keeping the factors `Kc r` inside the Cauchy–Schwarz
sum (rather than majorising them by a single constant) is what allows the sharp conormal power
`t^{2r-γ}` on the right. -/
private theorem sum_sq_le_rpow_of_abs {s : Finset ℕ} {Kc A : ℕ → ℝ} {t γ : ℝ} (ht : 0 < t) :
    (∑ r ∈ s, Kc r * (A r * t ^ ((r : ℝ) - γ / 2))) ^ 2
      ≤ (∑ r ∈ s, (Kc r) ^ 2) * ∑ r ∈ s, (A r) ^ 2 * t ^ (2 * (r : ℝ) - γ) := by
  have hpow : ∀ r : ℕ, (A r * t ^ ((r : ℝ) - γ / 2)) ^ 2
      = (A r) ^ 2 * t ^ (2 * (r : ℝ) - γ) := by
    intro r
    have hexp : ((r : ℝ) - γ / 2) + ((r : ℝ) - γ / 2) = 2 * (r : ℝ) - γ := by ring
    have h2 : (t ^ ((r : ℝ) - γ / 2)) ^ 2 = t ^ (2 * (r : ℝ) - γ) := by
      rw [sq, ← Real.rpow_add ht, hexp]
    rw [mul_pow, h2]
  calc (∑ r ∈ s, Kc r * (A r * t ^ ((r : ℝ) - γ / 2))) ^ 2
      ≤ (∑ r ∈ s, (Kc r) ^ 2) * ∑ r ∈ s, (A r * t ^ ((r : ℝ) - γ / 2)) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s Kc (fun r => A r * t ^ ((r : ℝ) - γ / 2))
    _ = (∑ r ∈ s, (Kc r) ^ 2) * ∑ r ∈ s, (A r) ^ 2 * t ^ (2 * (r : ℝ) - γ) := by
        rw [Finset.sum_congr rfl (fun r _ => hpow r)]

theorem mixedSlot_vanishing_weight_domination {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * ∑ r ∈ Finset.Icc 1 i,
            (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  classical
  -- the divisibility bounds for the angular coefficients
  have hcoef : ∀ r : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ θ : ℝ,
      |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
        ≤ K * |Real.sin (2 * θ)| ^ r :=
    fun r => Work.FTS.EllipticEst.remov.selfdth.DthCoef_sin_pow_bound (m + 1) r
  let Kc : ℕ → ℝ := fun r => Classical.choose (hcoef r)
  have hKcpos : ∀ r : ℕ, 0 < Kc r := fun r => (Classical.choose_spec (hcoef r)).1
  have hKcle : ∀ (r : ℕ) (θ : ℝ),
      |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
        ≤ Kc r * |Real.sin (2 * θ)| ^ r := fun r θ => (Classical.choose_spec (hcoef r)).2 θ
  refine ⟨∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2, ?_, ?_⟩
  · exact Finset.sum_pos' (fun r _ => sq_nonneg _)
      ⟨1, by simp [Finset.mem_Icc], pow_pos (hKcpos 1) 2⟩
  · intro z hz θ hθ
    have hw_nonneg : 0 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    by_cases hW : Work.Spaces.Wt α z θ = 0
    · -- the weight vanishes: both sides vanish
      have hzero : (Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 = 0 := by
        rw [hW, mul_zero]
        simp
      rw [hzero]
      refine mul_nonneg (Finset.sum_nonneg fun r _ => sq_nonneg _) ?_
      refine Finset.sum_nonneg fun r _ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Real.rpow_nonneg (sin_two_nonneg_on_Iθ hθ) _)
    · obtain ⟨hzpos, hθ0, hθ1⟩ := Wt_ne_zero_quadrant hα hz hθ hW
      have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hsinabs : |Real.sin (2 * θ)| = Real.sin (2 * θ) := abs_of_pos hs
      -- the exact expansion of the mixed slot in the plain slots
      have hexp := mixed_eq_sum_dthCoef_succ hsm m j z θ hzpos hθ0 hθ1
      have hD_bound : |Work.Spaces.mixed j (m + 1) f z θ|
          ≤ ∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := by
        rw [hexp]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r _ => ?_)
        calc |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
              * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
            = |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := abs_mul _ _
          _ ≤ (Kc r * |Real.sin (2 * θ)| ^ r)
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| :=
              mul_le_mul_of_nonneg_right (hKcle r θ) (abs_nonneg _)
          _ = Kc r * (Real.sin (2 * θ)) ^ r
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := by rw [hsinabs]
      have hWt_abs : |Work.Spaces.Wt α z θ|
          = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta, abs_mul,
          abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos hs (-(Work.Spaces.gam α / 2)))),
          abs_of_nonneg hw_nonneg]
      -- the sharp power identity `t^r · t^{-γ/2} = t^{r-γ/2}`
      have hrpow_mul : ∀ r : ℕ,
          (Real.sin (2 * θ)) ^ r * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
            = (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2) := by
        intro r
        have hexp : (r : ℝ) + (-(Work.Spaces.gam α / 2)) = (r : ℝ) - Work.Spaces.gam α / 2 := by
          ring
        rw [← Real.rpow_natCast (Real.sin (2 * θ)) r, ← Real.rpow_add hs, hexp]
      -- the sharp domination, with the `sin(2θ)^r` kept inside
      have key : |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ|
          ≤ ∑ r ∈ Finset.Icc 1 (m + 1),
              Kc r * ((|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z)
                * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2)) := by
        calc |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ|
            = |Work.Spaces.mixed j (m + 1) f z θ| * |Work.Spaces.Wt α z θ| := abs_mul _ _
          _ = |Work.Spaces.mixed j (m + 1) f z θ|
                * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := by
              rw [hWt_abs]
          _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|)
              * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
              mul_le_mul_of_nonneg_right hD_bound
                (mul_nonneg hw_nonneg
                  (le_of_lt (Real.rpow_pos_of_pos hs (-(Work.Spaces.gam α / 2)))))
          _ = ∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
              Finset.sum_mul _ _ _
          _ = ∑ r ∈ Finset.Icc 1 (m + 1),
              Kc r * (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z
                * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2)) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              calc Kc r * (Real.sin (2 * θ)) ^ r
                    * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                    * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
                  = Kc r * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                    * Work.Spaces.w z
                    * ((Real.sin (2 * θ)) ^ r
                        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := by ring
                _ = Kc r * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                    * Work.Spaces.w z
                    * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2) := by
                    rw [hrpow_mul r]
                _ = Kc r * (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z
                    * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2)) := by ring
      -- assembly: square, Cauchy–Schwarz, and read off the sharp weights
      calc (Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
          = |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ| ^ 2 := by rw [sq_abs]
        _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1),
              Kc r * ((|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z)
                * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) key 2
        _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2)
              * ∑ r ∈ Finset.Icc 1 (m + 1),
                  (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
            sum_sq_le_rpow_of_abs (s := Finset.Icc 1 (m + 1)) hs
        _ = (∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2)
              * ∑ r ∈ Finset.Icc 1 (m + 1),
                  (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ) ^ 2
                    * (Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) := by
            have hfin : (∑ r ∈ Finset.Icc 1 (m + 1),
                  (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
                = ∑ r ∈ Finset.Icc 1 (m + 1),
                  (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ) ^ 2
                    * (Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
              Finset.sum_congr rfl fun r _ => by rw [mul_pow, sq_abs]
            rw [hfin]

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade.HkMem_zero_of_outer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

set_option autoImplicit false

local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ
local notation "HkInt" => Work.Spaces.HkIntegrand
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "sOpen" => Work.FTS.EllipticEst.SmoothOpen
local notation "QQ" => Work.FTS.EllipticEst.Q0

/-! ## The level-`0` integrand as `w²` times the `σ`-weighted square -/

/-- At level `0` the `ℋ⁰`-integrand is the single square of the weighted profile
(`Work.EllipticEst.Honest.HkIntegrand_zero_eq`, reproved here to keep the import cone small). -/
theorem slm_HkIntegrand_zero_profile (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkInt α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Finset.range_one]
  norm_num

/-- **The level-`0` integrand is `w z²` times the `σ`-weighted square of the value**, on `Iθ`.
This is the bridge between the `HkIntegrand`-form of the workspace's norms and the
`σ = sin(2θ)^{-η}` slice mass of the `SliceMassUpgrade` machinery. -/
theorem slm_HkIntegrand_zero_radial (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Iθ) :
    HkInt α 0 g z θ = (Work.Spaces.w z) ^ 2 * (sEta θ * (g z θ) ^ 2) := by
  rw [slm_HkIntegrand_zero_profile]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rcases eq_or_lt_of_le hs with h0 | hpos
    · rw [← h0, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
        Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta ≠ 0)]
      norm_num
    · rw [pow_two, ← Real.rpow_add hpos]
      congr 1
      ring
  rw [mul_pow, div_pow, hsq, Work.FTS.EllipticEst.sEta, div_eq_mul_inv,
    ← Real.rpow_neg hs (Work.Spaces.eta)]
  ring

/-! ## The angular interval rewritings -/

/-- `∫⁻` over `Iθ = [0,π/2]` equals `∫⁻` over the open interval `(0,π/2)` (the two endpoints
are null). -/
theorem slm_lintegral_Iθ_eq_Ioo (f : ℝ → ℝ≥0∞) :
    (∫⁻ θ in Iθ, f θ) = ∫⁻ θ in Set.Ioo 0 (π / 2), f θ := by
  show (∫⁻ θ : ℝ, f θ ∂(volume.restrict (Set.Icc 0 (π / 2))))
      = ∫⁻ θ : ℝ, f θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm]


/-! ## `w z ≥ 1` on the open half-line -/

/-- `w z = (1+z)²/z² ≥ 1` for `z > 0`. -/
theorem slm_one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [hz]


/-! ## Joint a.e. measurability of the `σ`-weighted square from `SmoothOpen` -/



/-! ## The `σ`-form of an outer `HkIntegrand`-bound -/


/-! ## The main transfer -/


end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_lintegral_up_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-- The general form of the slice-mass up-estimate.  The pointwise estimate `hpt` (an
`ofReal`-level AM–GM Cauchy–Schwarz bound on the slice), the sliver comparison `hcmp`
(which converts the `∂_z`-mass over a sliver into the `D_z`-mass) and the a.e.-measurability
of the `τ`-weighted `∂_z`-density are hypotheses; the weight `τ` itself need *not* be
measurable, which is why the integral of the sum in `hpt` is split on the **second** summand
(whose a.e.-measurability follows from `hmeas` through Tonelli). -/
theorem sliceMass_lintegral_up_gen {F : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hτ : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ τ θ)
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (τ p.2 * (Work.Spaces.pz F p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)))))
    (hpt : ∀ z₁ z₂ θ : ℝ, 0 < z₁ → z₁ ≤ z₂ → θ ∈ Set.Ioo 0 (π / 2) →
      ENNReal.ofReal (τ θ * (F z₂ θ) ^ 2)
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2)
          + ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
    (hcmp : ∀ z₁ s : ℝ, 0 < z₁ → z₁ ≤ s →
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
        ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹
          * ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2))
    {z₁ z₂ : ℝ} (hz₁ : 0 < z₁) (hz₁₂ : z₁ ≤ z₂) :
    (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (F z₂ θ) ^ 2))
      ≤ 2 * (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2))
        + ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)) := by
  have hz1ne : ENNReal.ofReal (z₁ ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith [sq_pos_of_pos hz₁]
  -- (0) a.e.-measurability of the `τ`-weighted `∂_z`-density on the sliver `Ioo z₁ z₂`
  have hAEM : AEMeasurable (Function.uncurry (fun s θ : ℝ =>
      ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)))
      ((volume.restrict (Set.Ioo z₁ z₂)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
    have hle : (volume.restrict (Set.Ioo z₁ z₂)).prod
          (volume.restrict (Set.Ioo 0 (π / 2)))
        ≤ (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2))) := by
      rw [Measure.prod_restrict, Measure.prod_restrict]
      refine Measure.restrict_mono ?_ le_rfl
      exact Set.prod_mono (fun x hx => lt_of_lt_of_le hz₁ (le_of_lt hx.1)) (subset_refl _)
    exact AEMeasurable.mono_measure hmeas hle
  -- (0') the inner `s`-integral is a.e.-measurable as a function of `θ`
  have hJ' : AEMeasurable (fun θ : ℝ => ∫⁻ s in Set.Ioo z₁ z₂,
      ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
      (volume.restrict (Set.Ioo 0 (π / 2))) := hAEM.lintegral_prod_left'
  -- (1) the pointwise identity moving `ofReal ∘ τ` inside the sliver integral
  have hpt_id : ∀ θ ∈ Set.Ioo 0 (π / 2),
      ENNReal.ofReal (τ θ) * (∫⁻ s in Set.Ioo z₁ z₂,
          ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))
        = ∫⁻ s in Set.Ioo z₁ z₂,
            ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2) := by
    intro θ hθ
    rw [(lintegral_const_mul' (ENNReal.ofReal (τ θ))
      (fun s : ℝ => ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))
      ENNReal.ofReal_ne_top).symm]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun s =>
      (ENNReal.ofReal_mul (hτ θ hθ)).symm)
  -- (2) a.e.-measurability of the second summand (`hmeas` + Tonelli; `τ` itself is not
  -- assumed measurable, so this is the only way to split the sum)
  have hb : AEMeasurable (fun θ : ℝ => ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
      * (ENNReal.ofReal (z₂ - z₁)
        * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hbase : AEMeasurable (fun θ : ℝ => ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
        * (∫⁻ s in Set.Ioo z₁ z₂,
            ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))))
        (volume.restrict (Set.Ioo 0 (π / 2))) :=
      AEMeasurable.const_mul
        (AEMeasurable.const_mul hJ' (ENNReal.ofReal (z₂ - z₁))) (ENNReal.ofReal 2)
    refine hbase.congr ?_
    show ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
          * (∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)))
        = ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ) * (ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ => by
      show ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
          * (∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)))
        = ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ) * (ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))
      rw [show ENNReal.ofReal (z₂ - z₁)
            * (∫⁻ s in Set.Ioo z₁ z₂,
                ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
          = ENNReal.ofReal (τ θ) * (ENNReal.ofReal (z₂ - z₁)
              * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)) from by
        rw [← hpt_id θ hθ]; ring]
  -- (3) pointwise bound under the lintegral
  have hstep1 : (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (F z₂ θ) ^ 2))
      ≤ ∫⁻ θ in Set.Ioo 0 (π / 2),
          (ENNReal.ofReal 2 * ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2)
            + ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ => hpt z₁ z₂ θ hz₁ hz₁₂ hθ
  -- (4) split the sum (on the second summand) and pull the constants out
  have hsplit : (∫⁻ θ in Set.Ioo 0 (π / 2),
          (ENNReal.ofReal 2 * ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2)
            + ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))))
      = ENNReal.ofReal 2 * (∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2))
        + (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal 2
            * (ENNReal.ofReal (τ θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))) := by
    rw [lintegral_add_right' _ hb, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- (5) the second summand: normalise, pull the constants, pull `ofReal ∘ τ` inside
  have hsecond : (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal 2
        * (ENNReal.ofReal (τ θ)
          * (ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
      = ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
          * (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))) := by
    rw [show (fun θ : ℝ => ENNReal.ofReal 2
          * (ENNReal.ofReal (τ θ)
            * (ENNReal.ofReal (z₂ - z₁)
              * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
        = fun θ : ℝ => ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
            * (ENNReal.ofReal (τ θ)
              * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
        from by funext θ; ring]
    have hinner : (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ)
          * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))
        = (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
            ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)) := by
      refine lintegral_congr_ae ?_
      show ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
        ENNReal.ofReal (τ θ)
            * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))
          = ∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ hθ => hpt_id θ hθ
    rw [lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' (ENNReal.ofReal (z₂ - z₁)) _ ENNReal.ofReal_ne_top, hinner]
  -- (6) Tonelli
  have hthird : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
      = (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
          ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)) :=
    lintegral_lintegral_swap (μ := volume.restrict (Set.Ioo z₁ z₂))
      (ν := volume.restrict (Set.Ioo 0 (π / 2))) hAEM
  -- (7) bound by the `D_z`-mass
  have hbound : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
      ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹
        * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)) := by
    have h1 : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
        ≤ ∫⁻ s in Set.Ioo z₁ z₂, (ENNReal.ofReal (z₁ ^ 2))⁻¹
            * (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ
                * (s * Work.Spaces.pz F s θ) ^ 2)) := by
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun s hs => hcmp z₁ s hz₁ (le_of_lt hs.1)
    refine le_trans h1 ?_
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hz1ne)]
    exact mul_le_mul_right (lintegral_mono_set
      (fun x hx => lt_of_lt_of_le hz₁ (le_of_lt hx.1))) _
  have hconv : (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
        * ((ENNReal.ofReal (z₁ ^ 2))⁻¹
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2))))
      = ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
        * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < z₁ ^ 2),
      ENNReal.div_eq_inv_mul, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      show ENNReal.ofReal (2:ℝ) = (2 : ℝ≥0∞) from by norm_num]
    ring
  refine le_trans hstep1 ?_
  rw [hsplit, hsecond, ← hthird]
  rw [show ENNReal.ofReal (2:ℝ) = (2 : ℝ≥0∞) from by norm_num]
  refine add_le_add le_rfl ?_
  calc (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
        * (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)))
      ≤ (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
          * ((ENNReal.ofReal (z₁ ^ 2))⁻¹
            * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
                ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)))) :=
        mul_le_mul_right (mul_le_mul_right hbound (ENNReal.ofReal (z₂ - z₁))) (2 : ℝ≥0∞)
    _ = ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)) := hconv

end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.EllExist.ClassCInputs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `(z,θ) ↦ sin 2θ · F_*(g) z` is `C^n` on the open quadrant as soon as `F_*(g)` is `C^n` on
`(0,∞)`. -/
theorem contDiffOn_Fstar_mul_sin_two {g : Fn} (n : ℕ)
    (hF : ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) :
    ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Elliptic.Fstar g p.1 * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Work.Elliptic.Fstar g p.1)
      Work.FTS.EllipticEst.Q0 :=
    hF.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  exact h1.mul h2

/-- **Smoothness of the orthogonalised source.**  If `g` is `C^∞` on the open quadrant and its
angular moment `F_*(g)` is `C^∞` on `(0,∞)`, then so is
`orthSource g = g - (15/4)·sin 2θ·F_*(g)`. -/
theorem smoothOpen_orthSource_of_Fstar_smooth {g : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hF : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry g) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hsm n
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (15 / 4) * (Work.Elliptic.Fstar g p.1 * Real.sin (2 * p.2)))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const (c := (15 / 4 : ℝ))).mul (contDiffOn_Fstar_mul_sin_two n (hF n))
  have hfun : Function.uncurry (Work.Elliptic.orthSource g)
      = fun p : ℝ × ℝ => Function.uncurry g p
          - (15 / 4) * (Work.Elliptic.Fstar g p.1 * Real.sin (2 * p.2)) := by
    funext p
    simp only [Function.uncurry, Work.Elliptic.orthSource]
    ring
  rw [hfun]
  exact h1.sub h2

/-- **Decay of the orthogonalised source.**  If every angular slice of `g` and the angular moment
`F_*(g)` tend to `0` at `z → ∞`, then so does every slice of `orthSource g`. -/
theorem tendsto_orthSource_atTop_of {g : Fn}
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => g z θ) atTop (𝓝 0))
    (hFdec : Tendsto (fun z => Work.Elliptic.Fstar g z) atTop (𝓝 0)) :
    ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Work.Elliptic.orthSource g z θ) atTop (𝓝 0) := by
  intro θ hθ
  have hfun : (fun z => Work.Elliptic.orthSource g z θ)
      = fun z => g z θ - (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar g z) := by
    funext z
    simp only [Work.Elliptic.orthSource]
    ring
  rw [hfun]
  simpa using (hdec θ hθ).sub ((hFdec.const_mul (Real.sin (2 * θ))).const_mul (15 / 4))

end Work.FTS.EllExist
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The unshifted unknown of a shifted solution -/

/-- The inverse of `shiftSing α g`: subtract the same radial multiple of `sin 2θ`. -/
def unshift (α : ℝ) (g Ψ' : Fn) : Fn :=
  fun z θ => Ψ' z θ - Work.Elliptic.Gsing α g z * Real.sin (2 * θ)

@[simp] theorem unshift_apply (α : ℝ) (g Ψ' : Fn) (z θ : ℝ) :
    unshift α g Ψ' z θ = Ψ' z θ - Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- `shiftSing` and `unshift` are mutually inverse. -/
theorem shiftSing_unshift (α : ℝ) (g Ψ' : Fn) : shiftSing α g (unshift α g Ψ') = Ψ' := by
  funext z θ
  simp only [shiftSing_apply, unshift_apply]
  ring

/-! ## Smoothness, Dirichlet data and decay transfer -/

/-- `Gsing α g` times `sin 2θ` is `C^n` on the open quadrant as soon as `Gsing α g` is `C^n` on
`(0,∞)`. -/
theorem contDiffOn_Gsing_sin (α : ℝ) (g : Fn) (n : ℕ)
    (hG : ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) :
    ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Elliptic.Gsing α g p.1 * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Work.Elliptic.Gsing α g p.1)
      Work.FTS.EllipticEst.Q0 :=
    hG.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  exact h1.mul h2

/-- `SmoothOpen` transfers from `Ψ'` to `unshift α g Ψ'` as soon as `Gsing α g` is `C^∞` on
`(0,∞)`. -/
theorem smoothOpen_unshift (α : ℝ) (g Ψ' : Fn)
    (hΨ' : Work.FTS.EllipticEst.SmoothOpen Ψ')
    (hG : ∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (unshift α g Ψ') := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry Ψ') Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ').mp hΨ' n
  have h2 := contDiffOn_Gsing_sin α g n (hG n)
  have hfun : Function.uncurry (unshift α g Ψ')
      = fun p : ℝ × ℝ => Function.uncurry Ψ' p
          - Work.Elliptic.Gsing α g p.1 * Real.sin (2 * p.2) := rfl
  rw [hfun]
  exact h1.sub h2

/-- The Dirichlet values transfer. -/
theorem unshift_zero (α : ℝ) (g Ψ' : Fn) (h : ∀ z, Ψ' z 0 = 0) :
    ∀ z, unshift α g Ψ' z 0 = 0 := by
  intro z; simp [unshift_apply, h z]

/-- The Dirichlet values transfer at `θ = π/2`. -/
theorem unshift_pi_half (α : ℝ) (g Ψ' : Fn) (h : ∀ z, Ψ' z (π / 2) = 0) :
    ∀ z, unshift α g Ψ' z (π / 2) = 0 := by
  intro z
  have hsin : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π from by ring, Real.sin_pi]
  simp [unshift_apply, h z, hsin]

/-- The decay transfers. -/
theorem tendsto_unshift (α : ℝ) (g Ψ' : Fn) (θ : ℝ)
    (hΨ' : Tendsto (fun z => Ψ' z θ) atTop (𝓝 0))
    (hG : Tendsto (fun z => Work.Elliptic.Gsing α g z) atTop (𝓝 0)) :
    Tendsto (fun z => unshift α g Ψ' z θ) atTop (𝓝 0) := by
  have hfun : (fun z => unshift α g Ψ' z θ)
      = fun z => Ψ' z θ - Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl
  rw [hfun]
  simpa using hΨ'.sub (hG.mul_const (Real.sin (2 * θ)))

/-! ## The assembly -/


end Work.FTS.EllExist
end
end
-- ===== merged: Submission.Work.FTS.EllSol.DivSinOpenAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Bridging lemmas: two-variable `D_θ`-iterates versus one-dimensional ones -/

/-- The `θ`-slice at a fixed `z` of the two-variable iterate `D_θ^i` agrees with the
one-dimensional iterate `Dth1Iter i` of the slice. -/
theorem DthIter_slice_eq (X : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i X z θ = Work.Elliptic.Dth1Iter i (fun t => X z t) θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, Work.Elliptic.Dth1Iter_succ]
      have h : (fun θ' => Work.Spaces.DthIter n X z θ')
          = fun θ' => Work.Elliptic.Dth1Iter n (fun t => X z t) θ' := by
        funext θ'
        exact ih z θ'
      simp only [Work.Spaces.Dth, Work.Elliptic.Dth1, Work.Spaces.pth]
      rw [h]

/-- `D_z` commutes with the division by a factor depending on `θ` only. -/
theorem Dz_div_const (Y : ℝ → ℝ → ℝ) (g : ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => Y z θ / g θ)
      = fun z θ => Work.Spaces.Dz Y z θ / g θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [deriv_div_const, mul_div_assoc]

/-- Every iterate `D_z^j` commutes with the division by a factor depending on `θ` only. -/
theorem DzIter_div_const (Y : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => Y z θ / g θ)
      = fun z θ => Work.Spaces.DzIter j Y z θ / g θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      exact Dz_div_const (Work.Spaces.DzIter n Y) g

/-- **Clairaut on the open quadrant**: the `θ`-derivative of the slice of `D_z^j Φ` is the
slice of `D_z^j (∂_θΦ)`. -/
theorem deriv_DzIter_slice {Φ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => Work.Spaces.DzIter j Φ z t) θ
      = Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry Φ)
      Work.FTS.EllipticEst.Q0 := (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hSO
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j Φ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth Φ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hsm j
  have hx : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  simpa only [Function.uncurry, Work.Spaces.pth] using hEq hx

/-- The mixed summand of the quotient `Φ/sin 2θ` is the `D_θ`-iterate of the quotient of the
slice: `D_z^j D_θ^i (Φ/sin 2θ) = D_θ^i ((D_z^j Φ)/sin 2θ)`. -/
theorem mixed_div_eq {Φ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ (fun t => Work.Spaces.DzIter j Φ z t)) θ := by
  have hdiv : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hSO
  have hsm : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry (fun z θ => Φ z θ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hdiv
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i
        (Work.Spaces.DzIter j (fun z θ => Φ z θ / Real.sin (2 * θ)))))
      (Function.uncurry (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hsm j i
  have hx : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h' : Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = Work.Spaces.DthIter i
          (Work.Spaces.DzIter j (fun z θ => Φ z θ / Real.sin (2 * θ))) z θ := (hEq hx).symm
  rw [h', DthIter_slice_eq]
  refine congrArg (fun f => Work.Elliptic.Dth1Iter i f θ) ?_
  funext t
  simp only [Work.Elliptic.SinQ]
  exact congrFun (congrFun (DzIter_div_const Φ (fun θ => Real.sin (2 * θ)) j) z) t

/-- The mixed summand of `∂_θΦ` is the `D_θ`-iterate of the slice of `D_z^j (∂_θΦ)`. -/
theorem mixed_pth_eq {Φ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j m : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
      = Work.Elliptic.Dth1Iter m (fun t => Work.Spaces.DzIter j (Work.Spaces.pth Φ) z t) θ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry (Work.Spaces.pth Φ))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSO.pth
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter m
        (Work.Spaces.DzIter j (Work.Spaces.pth Φ))))
      (Function.uncurry (Work.Spaces.mixed j m (Work.Spaces.pth Φ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hsm j m
  have hx : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h' : Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
      = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) z θ := (hEq hx).symm
  rw [h', DthIter_slice_eq]

/-! ## Elementary angular facts -/

/-- A property holding on `(0,π/2)` holds a.e. on `Iθ`. -/
lemma ae_Iθ_of_forall_Ioo {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  have hμ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm
  rw [hμ]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-- `Dth1Iter` respects equality on the open interval. -/
lemma Dth1Iter_congr_of_Ioo {g g' : ℝ → ℝ}
    (h : Set.EqOn g g' (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    Set.EqOn (Work.Elliptic.Dth1Iter m g) (Work.Elliptic.Dth1Iter m g')
      (Set.Ioo 0 (Real.pi / 2)) := by
  induction m with
  | zero => exact h
  | succ j ih =>
      intro θ hθ
      have hnb : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
      have hev : (Work.Elliptic.Dth1Iter j g) =ᶠ[𝓝 θ] (Work.Elliptic.Dth1Iter j g') := by
        filter_upwards [hnb] with θ' hθ'
        exact ih hθ'
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1,
        Work.Elliptic.Dth1, hev.deriv_eq]

/-- Integrability is transported along an equality that holds on the open interval only. -/
lemma integrableOn_congr_of_EqOn_Ioo {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Ioo 0 (Real.pi / 2)))
    (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) : MeasureTheory.IntegrableOn g Work.Spaces.Iθ := by
  have hμ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm
  refine hf.congr ?_
  rw [hμ]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => h hθ)

/-! ## The weight and slot identities -/

lemma wdivsin_sq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [← Work.FTS.H2.Whz_eq]
  exact (Work.FTS.H2.Whz_Wm_sq 1 zero_lt_one z θ hθ).1

lemma Wt_sq_E (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [← Work.FTS.H2.Wm_eq]
  exact (Work.FTS.H2.Whz_Wm_sq α hα z θ hθ).2

/-- The pure-`D_z` summand of the quotient integrand, in terms of the data integrand. -/
lemma Pslot_eq (b : ℕ) (Φ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.DzIter b (fun z' θ' => Φ z' θ' / Real.sin (2 * θ')) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.DzIter b Φ z θ / Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [Work.Elliptic.DivSinFactor Φ b z θ hθ, mul_pow,
    wdivsin_sq z θ ⟨hθ.1.le, hθ.2.le⟩]
  ring

/-- The mixed summand of the quotient integrand, in terms of the angular data integrand. -/
lemma Mslot_eq (α : ℝ) (hα : 0 < α) (i j : ℕ) (Φ : ℝ → ℝ → ℝ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Φ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.mixed j i (fun z' θ' => Φ z' θ' / Real.sin (2 * θ')) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 *
        ((Work.Elliptic.Dth1Iter i
            (fun θ' => Work.Spaces.DzIter j Φ z θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  rw [mixed_div_eq hSO j i hz hθ,
    show Work.Elliptic.SinQ (fun t => Work.Spaces.DzIter j Φ z t)
      = (fun θ' => Work.Spaces.DzIter j Φ z θ' / Real.sin (2 * θ')) from rfl,
    mul_pow, Wt_sq_E α hα z θ ⟨hθ.1.le, hθ.2.le⟩]
  ring

/-- The `η`-weighted data integrand of the slice `D_z^j Φ` is `w^{-2}` times the `j`-th pure
summand of `HkIntegrand α k (∂_θΦ)`. -/
lemma Zdata_eq (j : ℕ) (Φ : ℝ → ℝ → ℝ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Φ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hwz : Work.Spaces.w z ≠ 0) :
    (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = ((Work.Spaces.w z) ^ 2)⁻¹ *
        (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [deriv_DzIter_slice hSO j hz hθ, mul_pow,
    wdivsin_sq z θ ⟨hθ.1.le, hθ.2.le⟩]
  field_simp

/-- The `γ`-weighted data integrand of the slice `D_z^j Φ` is `w^{-2}` times the corresponding
mixed summand of `HkIntegrand α k (∂_θΦ)`. -/
lemma Mdata_eq (α : ℝ) (hα : 0 < α) (m j : ℕ) (Φ : ℝ → ℝ → ℝ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Φ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hwz : Work.Spaces.w z ≠ 0) :
    (Work.Elliptic.Dth1Iter m
        (fun θ' => deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = ((Work.Spaces.w z) ^ 2)⁻¹ *
        (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hEqOn : Set.EqOn (fun θ' : ℝ => deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ')
      (fun θ' : ℝ => Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := fun θ' hθ' => deriv_DzIter_slice hSO j hz hθ'
  rw [Dth1Iter_congr_of_Ioo hEqOn m hθ, ← mixed_pth_eq hSO j m hz hθ, mul_pow,
    Wt_sq_E α hα z θ ⟨hθ.1.le, hθ.2.le⟩]
  field_simp

/-! ## The per-slice hypotheses -/

/-- **The slice data**: for `z > 0` and `j ≤ k` the slice `θ ↦ D_z^j Φ z θ` is `C^∞` on the open
interval, vanishes at both endpoints and its `η`- and `γ`-weighted data integrals are honest. -/
theorem sliceData {k : ℕ} {α : ℝ} {Φ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hsl : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2)))
    (ht0 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (ht1 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pth Φ)) (hα : 0 < α)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z) :
    ∀ j : ℕ, j ≤ k →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
          (Set.Ioo 0 (Real.pi / 2)) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
        (∀ m : ℕ, 1 ≤ m → m ≤ k - j → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (fun θ' : ℝ =>
              deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) := by
  intro j hj
  have hsmj : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [Work.Stability.smoothOrder] using hsl z hzpos j hj
  have h1 := (hkMem_slots α k hSO hmem hz hzpos hα).1 j hj
  have h1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
    refine h1.congr ?_
    filter_upwards [ae_Iθ_of_forall_Ioo
      (fun θ hθ => deriv_DzIter_slice hSO j hzpos hθ)] with θ hθ
    show (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [← hθ]
  refine ⟨hsmj, ht0 z hzpos j hj, ht1 z hzpos j hj, h1', fun m hm1 hmkj => ?_⟩
  have hmj : m + j ≤ k := by omega
  have h2 := (hkMem_slots α k hSO hmem hz hzpos hα).2 m j hm1 hmj
  have hEqOn : Set.EqOn (fun θ' : ℝ => deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ')
      (fun θ' : ℝ => Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := fun θ' hθ' => deriv_DzIter_slice hSO j hzpos hθ'
  refine integrableOn_congr_of_EqOn_Ioo ?_ h2
  intro θ hθ
  show (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Work.Elliptic.Dth1Iter m (fun θ' : ℝ => deriv (fun θ'' : ℝ =>
          Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
  rw [Dth1Iter_congr_of_Ioo hEqOn m hθ, ← mixed_pth_eq hSO j m hzpos hθ]

end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.continuousOn_slice_joint =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The Fourier kernel `t ↦ exp (-(2π i ξ t))` has complex norm one. -/
private lemma norm_exp_fourierKernel (ξ t : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))‖ = 1 := by
  have h : -(2 * Real.pi * Complex.I * ξ * t)
      = ((↑(-(2 * Real.pi * ξ * t)) : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- For a fixed angle `θ` in the open interval, the `t`-slice of `φ` is continuous on `ℝ`
(this only needs the joint continuity at points whose second coordinate is in the open interval,
whereas the values of `φ t θ` for `θ ∉ (0, π/2)` are irrelevant). -/
private lemma continuous_slice_fst {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Continuous fun t : ℝ => φ t θ := by
  rw [continuous_iff_continuousAt]
  rintro s
  have hmem : (s, θ) ∈ Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨trivial, hθ⟩
  have h1 : ContinuousAt (Function.uncurry φ) (s, θ) :=
    (hφ.continuousWithinAt hmem).continuousAt
      (IsOpen.mem_nhds (isOpen_univ.prod isOpen_Ioo) hmem)
  exact h1.comp (x := s) (f := fun y : ℝ => (y, θ))
    (continuousAt_id.prodMk continuousAt_const)

/-- For a fixed `t`, the map `q ↦ φ t q.2` is continuous on the half-strip. -/
private lemma continuousOn_slice_snd {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (t : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => φ t q.2) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  hφ.comp ((continuous_const.prodMk continuous_snd).continuousOn)
    (fun _ hq => ⟨trivial, hq.2⟩)

/-- Joint continuity at a point `(ξ, θ)` with `θ ∈ (0, π/2)` of the `t`-Fourier slice of a
function `φ` which is continuous on the half-strip and uniformly compactly supported in `t`.

Proof: dominated convergence (`MeasureTheory.continuousAt_of_dominated`) with respect to the
restricted measure on the support interval `[-M, M]`.  The dominating function is the constant
`K := sup_{|t| ≤ M, θ' ∈ [θ/2, (θ+π/2)/2]} |φ t θ'|`, which exists because the corresponding
product of compact intervals lies inside the half-strip on which `φ` is continuous.  The
integrand vanishes off the support interval, whence the restricted integral is the slice. -/
private theorem continuousAt_slice {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsupp : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → φ t θ = 0)
    {ξ θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousAt (fun p : ℝ × ℝ => slice φ p.1 p.2) (ξ, θ) := by
  obtain ⟨M, hM, hsuppM⟩ := hsupp
  have hθlo : 0 < θ / 2 := by linarith [hθ.1]
  have hθhi : (θ + Real.pi / 2) / 2 < Real.pi / 2 := by linarith [hθ.2]
  have hθ1 : θ / 2 < θ := by linarith [hθ.1]
  have hθ2 : θ < (θ + Real.pi / 2) / 2 := by linarith [hθ.2]
  -- a point outside the support interval is beyond the support radius
  have habs : ∀ t : ℝ, t ∉ Set.Icc (-M) M → M < |t| := by
    intro t ht
    by_contra hcon
    exact ht (abs_le.mp (le_of_not_gt hcon))
  -- uniform bound for the angular parameters in a compact sub-interval
  have hsub : Set.Icc (-M) M ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2)
      ⊆ Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact ⟨trivial, ⟨lt_of_lt_of_le hθlo hb.1, lt_of_le_of_lt hb.2 hθhi⟩⟩
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hφ.mono hsub)
  set K : ℝ := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right K₀ 0
  have hK : ∀ t ∈ Set.Icc (-M) M, ∀ θ' ∈ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2),
      ‖φ t θ'‖ ≤ K :=
    fun t ht θ' hθ' => le_trans (hK₀ (t, θ') ⟨ht, hθ'⟩) (le_max_left K₀ 0)
  -- the relevant neighbourhoods of the parameter point
  have hU : Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 (ξ, θ) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem (Ioo_mem_nhds hθ.1 hθ.2)
  have hU' : Set.univ ×ˢ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2) ∈ 𝓝 (ξ, θ) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem (Ioo_mem_nhds hθ1 hθ2)
  -- the integrand
  set F : ℝ × ℝ → ℝ → ℂ := fun q t =>
    (φ t q.2 : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * q.1 * t)) with hFdef
  -- dominated convergence for the restricted integral
  have hmain : ContinuousAt
      (fun q : ℝ × ℝ => ∫ t, F q t ∂(volume.restrict (Set.Icc (-M) M))) (ξ, θ) := by
    refine MeasureTheory.continuousAt_of_dominated (μ := volume.restrict (Set.Icc (-M) M))
      (F := F) (bound := fun _ : ℝ => K) ?_ ?_ ?_ ?_
    · -- a.e. strong measurability: the slices are continuous in `t`
      filter_upwards [hU] with q hq
      have h1 : Continuous fun t : ℝ => φ t q.2 := continuous_slice_fst hφ hq.2
      have h2 : Continuous fun t : ℝ =>
          Complex.exp (-(2 * Real.pi * Complex.I * q.1 * t)) := by fun_prop
      have hc : Continuous fun t : ℝ => F q t := by
        simp only [F]
        exact (Complex.continuous_ofReal.comp h1).mul h2
      exact hc.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
    · -- the pointwise domination by the constant `K`
      filter_upwards [hU'] with q hq
      filter_upwards with t
      by_cases ht : t ∈ Set.Icc (-M) M
      · have hb : ‖φ t q.2‖ ≤ K := hK t ht q.2 ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩
        calc ‖F q t‖
            = ‖(φ t q.2 : ℂ)‖ * ‖Complex.exp (-(2 * Real.pi * Complex.I * q.1 * t))‖ := by
              simp only [F, norm_mul]
          _ = ‖φ t q.2‖ * 1 := by rw [Complex.norm_real, norm_exp_fourierKernel]
          _ ≤ K := by rw [mul_one]; exact hb
      · have hz : φ t q.2 = 0 := hsuppM t q.2 (habs t ht)
        rw [show F q t = 0 by simp only [F, hz, Complex.ofReal_zero, zero_mul]]
        simpa using hK0
    · -- the dominating constant is integrable on a finite interval
      exact MeasureTheory.integrableOn_const (s := Set.Icc (-M) M) (C := K)
        (isCompact_Icc.measure_lt_top (μ := volume)).ne enorm_ne_top
    · -- a.e. continuity in the parameter
      filter_upwards with t
      have h1 : ContinuousAt (fun q : ℝ × ℝ => (φ t q.2 : ℂ)) (ξ, θ) :=
        ContinuousAt.comp (x := (ξ, θ)) (f := fun q : ℝ × ℝ => φ t q.2)
          Complex.continuous_ofReal.continuousAt
          ((continuousOn_slice_snd hφ t).continuousAt hU)
      have h2 : ContinuousAt
          (fun q : ℝ × ℝ => Complex.exp (-(2 * Real.pi * Complex.I * q.1 * t))) (ξ, θ) := by
        fun_prop
      exact h1.mul h2
  -- the restricted integral is the slice, since the integrand vanishes off the support interval
  refine hmain.congr ?_
  filter_upwards [hU] with q _
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-M) M)
    (f := F q) (fun t ht => by
      have hz : φ t q.2 = 0 := hsuppM t q.2 (habs t ht)
      simp only [F, hz, Complex.ofReal_zero, zero_mul])]
  simp only [slice, hFdef]

theorem continuousOn_slice_joint {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsupp : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → φ t θ = 0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.FlatFT.slice φ p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro p hp
  obtain ⟨ξ, θ⟩ := p
  simp only [Set.mem_prod, Set.mem_univ, true_and] at hp
  exact (continuousAt_slice hφ hsupp hp).continuousWithinAt

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped FourierTransform

namespace Work.FTS.EllSol.FlatFT

noncomputable section

set_option maxHeartbeats 800000

/-- `slice1 h ξ` is the pointwise Fourier transform `𝓕 h ξ` (Mathlib's convention). -/
theorem slice1_eq_fourier (h : ℝ → ℂ) (ξ : ℝ) : slice1 h ξ = 𝓕 h ξ := by
  rw [Real.fourier_eq']
  rw [slice1]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Real.inner_apply, smul_eq_mul]
  have hexp : -(2 * (Real.pi : ℂ) * Complex.I * ξ * (t : ℂ))
      = ↑(-2 * Real.pi * (t * ξ)) * Complex.I := by
    push_cast
    ring
  rw [hexp]
  ring

/-- The `L²` norm of an `L²` function of one real variable, as an integral. -/
theorem lp_norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ ξ : ℝ, ‖(f : ℝ → ℂ) ξ‖ ^ 2 := by
  have hmem : MemLp (f : ℝ → ℂ) 2 (volume : Measure ℝ) := Lp.memLp f
  have hnorm : ‖f‖ = Real.sqrt (∫ ξ : ℝ, ‖(f : ℝ → ℂ) ξ‖ ^ 2) := by
    rw [Lp.norm_def, hmem.eLpNorm_eq_integral_rpow_norm (p := 2) (μ := volume)
      (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num
  rw [hnorm, Real.sq_sqrt (integral_nonneg (fun _ => by positivity))]

/-- The pairing identity behind Plancherel for `L¹ ∩ L²` functions: the `L²` Fourier transform
of the class of `h` is self-adjoint against Schwartz test functions. -/
theorem fourier_lp_pairing {h : ℝ → ℂ} (h2 : MemLp h 2 (volume : Measure ℝ))
    (ψ : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (ψ : ℝ → ℂ) x • (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) x
      = ∫ x : ℝ, (𝓕 (ψ : ℝ → ℂ)) x • h x := by
  have hdist := Lp.fourier_toTemperedDistribution_eq (h2.toLp h)
  have happ := congrArg (fun T : TemperedDistribution ℝ ℂ => T ψ) hdist
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at happ
  rw [← happ]
  apply integral_congr_ae
  filter_upwards [h2.coeFn_toLp] with x hx
  rw [hx]
  simp only [SchwartzMap.fourier_coe]

/-- The `L²` Fourier transform of an `L¹ ∩ L²` function is, almost everywhere, its pointwise
Fourier transform. -/
theorem fourier_lp_ae_eq {h : ℝ → ℂ} (h1 : Integrable h) (h2 : MemLp h 2 (volume : Measure ℝ)) :
    ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 h := by
  have hFmem : MemLp (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) 2 volume :=
    Lp.memLp _
  have hFcont : Continuous (𝓕 h) :=
    VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := volume)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner h1
  refine ae_eq_of_integral_contDiff_smul_eq (hFmem.locallyIntegrable (by norm_num))
    (hFcont.locallyIntegrable) ?_
  intro g hg hgsupp
  have hof : ContDiff ℝ (↑(⊤ : ℕ∞)) (⇑Complex.ofRealCLM) := Complex.ofRealCLM.contDiff
  have hgC : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => (g x : ℂ)) := hof.comp hg
  have hsuppC : HasCompactSupport (fun x : ℝ => (g x : ℂ)) := hgsupp.comp_left Complex.ofReal_zero
  let ψ : SchwartzMap ℝ ℂ := hsuppC.toSchwartzMap hgC
  have hψx : ∀ x : ℝ, ψ x = (g x : ℂ) := fun x => rfl
  have hpair := fourier_lp_pairing h2 ψ
  have hself : ∫ x : ℝ, (𝓕 h) x • (ψ : ℝ → ℂ) x
      = ∫ x : ℝ, h x • (𝓕 (ψ : ℝ → ℂ)) x := by
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
      (μ := volume) (ν := volume) (L := innerₗ ℝ) (f := h) (g := (ψ : ℝ → ℂ))
      Real.continuous_fourierChar continuous_inner h1 ψ.integrable
    rw [flip_innerₗ] at h
    exact h
  have hcomm1 : ∫ x : ℝ, (𝓕 (ψ : ℝ → ℂ)) x • h x = ∫ x : ℝ, h x • (𝓕 (ψ : ℝ → ℂ)) x := by
    apply integral_congr_ae
    filter_upwards with x
    exact mul_comm _ _
  have hgψ : ∫ x : ℝ, g x • (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) x
      = ∫ x : ℝ, (ψ : ℝ → ℂ) x •
          (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hψx x, Complex.coe_smul]
  have hψg : ∫ x : ℝ, (𝓕 h) x • (ψ : ℝ → ℂ) x = ∫ x : ℝ, g x • (𝓕 h) x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hψx x]
    exact mul_comm _ _
  exact hgψ.trans (hpair.trans (hcomm1.trans (hself.symm.trans hψg)))

/-- **Plancherel's theorem for the first `t`-Fourier slice.**  For a continuous compactly
supported `h : ℝ → ℂ` the `L²` norm of `slice1 h` (the Fourier transform in `t`) equals the `L²`
norm of `h`. -/
theorem plancherelSlice1 (h : ℝ → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    ∫ ξ : ℝ, ‖Work.FTS.EllSol.FlatFT.slice1 h ξ‖ ^ 2 = ∫ t : ℝ, ‖h t‖ ^ 2 := by
  have hInt : Integrable h := hh.integrable_of_hasCompactSupport hs
  have hMem : MemLp h 2 (volume : Measure ℝ) := hh.memLp_of_hasCompactSupport hs
  have hae := fourier_lp_ae_eq hInt hMem
  have hstep : ∫ ξ : ℝ, ‖slice1 h ξ‖ ^ 2
      = ∫ ξ : ℝ, ‖(((𝓕 (hMem.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hae] with ξ hξ
    rw [slice1_eq_fourier h ξ, ← hξ]
  rw [hstep, ← lp_norm_sq_eq_integral (𝓕 (hMem.toLp h)), Lp.norm_fourier_eq,
    lp_norm_sq_eq_integral (hMem.toLp h)]
  apply integral_congr_ae
  filter_upwards [hMem.coeFn_toLp] with t ht
  rw [ht]

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.sliceContDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The open strip, the angular interval and the oscillatory factor -/

/-- The open half-strip `ℝ × (0, π/2)` on which the datum is smooth. -/
abbrev sliceStrp : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The angular interval `(0, π/2)`. -/
abbrev sliceSθ : Set ℝ := Set.Ioo 0 (Real.pi / 2)

/-- The oscillatory factor `t ↦ e^{-2πiξt}`. -/
abbrev sliceK (ξ : ℝ) : ℝ → ℂ := fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))

theorem isOpen_sliceStrp : IsOpen sliceStrp := isOpen_univ.prod isOpen_Ioo

theorem isOpen_sliceSθ : IsOpen sliceSθ := isOpen_Ioo

theorem continuous_sliceK (ξ : ℝ) : Continuous (sliceK ξ) := by
  fun_prop

theorem norm_sliceK (ξ t : ℝ) : ‖sliceK ξ t‖ = 1 := by
  dsimp only [sliceK]
  rw [show -(2 * Real.pi * Complex.I * ξ * t) = (-(2 * Real.pi * ξ * t) : ℝ) * Complex.I from by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _


/-! ## Continuity of the `t`-slices of a smooth function on the strip -/

/-- For `x ∈ (0,π/2)` the slice `t ↦ G t x` of a function which is `C^k` on the strip is
continuous. -/
theorem continuous_tslice {G : ℝ → ℝ → ℝ} {k : ℕ∞ω}
    (hG : ContDiffOn ℝ k (Function.uncurry G) sliceStrp) {x : ℝ}
    (hx : x ∈ sliceSθ) :
    Continuous fun t : ℝ => G t x := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hmem : (t, x) ∈ sliceStrp := ⟨trivial, hx⟩
  have hca : ContDiffAt ℝ k (Function.uncurry G) (t, x) :=
    hG.contDiffAt (isOpen_sliceStrp.mem_nhds hmem)
  have hc : ContinuousAt (fun t' : ℝ => (t', x)) t := continuousAt_id.prodMk continuousAt_const
  have hcomp := ContinuousAt.comp (f := fun t' : ℝ => (t', x)) (g := Function.uncurry G)
    (x := t) hca.continuousAt hc
  simpa only [Function.comp_def, Function.uncurry] using hcomp

/-! ## A support bookkeeping lemma -/

/-- If `M ≥ 0` and `t ∉ [-M, M]` then `M < |t|`. -/
theorem abs_lt_of_notMem_Icc' {M t : ℝ} (hM : 0 ≤ M) (h : t ∉ Set.Icc (-M) M) :
    M < |t| := by
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · rw [abs_of_neg hlt]
    by_contra hc
    push Not at hc
    exact h (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  · subst heq
    exact absurd (Set.mem_Icc.mpr ⟨by linarith, hM⟩) h
  · rw [abs_of_pos hgt]
    by_contra hc
    push Not at hc
    exact h (Set.mem_Icc.mpr ⟨by linarith, hc⟩)

/-! ## Parametric continuity -/

/-- The slice of a datum which is continuous on the strip and has uniformly compact
`t`-support is continuous on `(0, π/2)`. -/
theorem slice_continuousOn (ψ : ℝ → ℝ → ℝ) (ξ : ℝ)
    (hψ : ContDiffOn ℝ 0 (Function.uncurry ψ) sliceStrp)
    (hsupp : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → ψ t θ = 0) :
    ContinuousOn (fun θ : ℝ => slice ψ ξ θ) sliceSθ := by
  obtain ⟨M, hM, hsuppM⟩ := hsupp
  have hψc : ContinuousOn (Function.uncurry ψ) sliceStrp := contDiffOn_zero.mp hψ
  -- joint continuity of the integrand on the product of the angular interval with the line
  have hjoint : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry ψ (p.2, p.1))
      (sliceSθ ×ˢ Set.univ) :=
    hψc.comp continuous_swap.continuousOn (fun p hp => ⟨trivial, hp.1⟩)
  have hf : ContinuousOn (Function.uncurry (fun θ t : ℝ => (ψ t θ : ℂ) * sliceK ξ t))
      (sliceSθ ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => ((Function.uncurry ψ) (p.2, p.1) : ℂ))
        (sliceSθ ×ˢ Set.univ) := Complex.continuous_ofReal.comp_continuousOn hjoint
    have h2 : ContinuousOn (fun p : ℝ × ℝ => sliceK ξ p.2) (sliceSθ ×ˢ Set.univ) :=
      (continuous_sliceK ξ).comp_continuousOn continuous_snd.continuousOn
    refine (h1.mul h2).congr ?_
    intro p _
    rfl
  have hfs : ∀ θ : ℝ, ∀ x : ℝ, θ ∈ sliceSθ → x ∉ Set.Icc (-M) M →
      (fun θ t : ℝ => (ψ t θ : ℂ) * sliceK ξ t) θ x = 0 := by
    intro θ x _ hx
    show (ψ x θ : ℂ) * sliceK ξ x = 0
    rw [hsuppM x θ (abs_lt_of_notMem_Icc' hM hx), Complex.ofReal_zero, zero_mul]
  have hmain := continuousOn_integral_of_compact_support (μ := volume)
    (f := fun θ t : ℝ => (ψ t θ : ℂ) * sliceK ξ t)
    (s := sliceSθ) (k := Set.Icc (-M) M) isCompact_Icc hf hfs
  show ContinuousOn (fun θ : ℝ => ∫ t, (ψ t θ : ℂ) * sliceK ξ t) sliceSθ
  exact hmain

/-! ## Differentiation under the `t`-integral -/

/-- **Differentiation under the `t`-integral defining a slice.**

Let `φ` be of class `C¹` on the open strip `ℝ × (0,π/2)` with continuous `θ`-partial
there, let `φ` vanish for `M < |t|` with `M ≥ 0`, and let `κ` be continuous with
`‖κ t‖ = 1`.  Then for `x₀ ∈ (0,π/2)` the function `x ↦ ∫_t (φ t x : ℂ) · κ t` is
differentiable at `x₀` with derivative `∫_t (∂_θφ t x₀ : ℂ) · κ t`. -/
theorem slice_hasDerivAt_aux
    (φ : ℝ → ℝ → ℝ) (κ : ℝ → ℂ)
    (hφ : ContDiffOn ℝ 1 (Function.uncurry φ) sliceStrp)
    (hφ' : ContinuousOn (Function.uncurry (Work.Spaces.pth φ)) sliceStrp)
    (hκ : Continuous κ) (hκ1 : ∀ t, ‖κ t‖ = 1)
    {M : ℝ} (hM : 0 ≤ M) (hsupp : ∀ t θ, M < |t| → φ t θ = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ sliceSθ) :
    HasDerivAt (fun x => ∫ t, (φ t x : ℂ) * κ t)
      (∫ t, ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t) x₀ := by
  -- the angle window `(x₀-ε, x₀+ε)` on which everything is differentiated
  set ε : ℝ := min x₀ (Real.pi / 2 - x₀) / 2 with hεdef
  have hmin0 : 0 < min x₀ (Real.pi / 2 - x₀) :=
    lt_min hx₀.1 (by linarith [hx₀.2, Real.pi_pos])
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  have hεx : ε < x₀ := by
    have h := min_le_left x₀ (Real.pi / 2 - x₀)
    rw [hεdef]; linarith
  have hεπ : ε < Real.pi / 2 - x₀ := by
    have h := min_le_right x₀ (Real.pi / 2 - x₀)
    rw [hεdef]; linarith
  have hs : Set.Ioo (x₀ - ε) (x₀ + ε) ∈ 𝓝 x₀ :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hsub : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the `θ`-partial vanishes off the `t`-support of `φ`
  have hpth_zero : ∀ t, M < |t| → ∀ x, Work.Spaces.pth φ t x = 0 := by
    intro t ht x
    simp only [Work.Spaces.pth]
    rw [show (fun y : ℝ => φ t y) = fun _ => (0 : ℝ) from funext fun y => hsupp t y ht]
    simp
  -- the compact box on which `∂_θφ` is bounded
  have hBox : Set.Icc (-M) M ×ˢ Set.Icc (x₀ - ε) (x₀ + ε) ⊆ sliceStrp := by
    intro p hp
    obtain ⟨-, hp2⟩ := Set.mem_prod.mp hp
    exact ⟨trivial, ⟨by linarith [hp2.1], by linarith [hp2.2]⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -M) (b := M)).prod
      (isCompact_Icc (a := x₀ - ε) (b := x₀ + ε)) |>.exists_bound_of_continuousOn
        (hφ'.mono hBox)
  have hCnn : 0 ≤ C := by
    refine le_trans (norm_nonneg _) (hC (0, x₀) ?_)
    exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨by linarith, hM⟩,
      Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩
  -- continuity of the `θ`-partial on the vertical line `t = x₀`
  have hpth_cont : Continuous fun t : ℝ => Work.Spaces.pth φ t x₀ := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hmem : (t, x₀) ∈ sliceStrp := ⟨trivial, hx₀⟩
    have hc : ContinuousAt (fun p : ℝ × ℝ => Work.Spaces.pth φ p.1 p.2) (t, x₀) :=
      hφ'.continuousAt (isOpen_sliceStrp.mem_nhds hmem)
    have hc' : ContinuousAt (fun t' : ℝ => (t', x₀)) t :=
      continuousAt_id.prodMk continuousAt_const
    have hcomp := ContinuousAt.comp (f := fun t' : ℝ => (t', x₀))
      (g := fun p : ℝ × ℝ => Work.Spaces.pth φ p.1 p.2) (x := t) hc hc'
    simpa only [Function.comp_def, Function.uncurry] using hcomp
  -- the four side conditions of the domination theorem
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun t : ℝ => (φ t x : ℂ) * κ t)
      (volume.restrict (Set.Icc (-M) M)) := by
    filter_upwards [hs] with x hx
    have hcont : Continuous fun t : ℝ => φ t x := continuous_tslice hφ (hsub hx)
    exact ((Complex.continuous_ofReal.comp hcont).mul hκ).aestronglyMeasurable
  have hF_int : Integrable (fun t : ℝ => (φ t x₀ : ℂ) * κ t)
      (volume.restrict (Set.Icc (-M) M)) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc (a := -M) (b := M))
      ((Complex.continuous_ofReal.comp (continuous_tslice hφ hx₀)).mul hκ).continuousOn
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t)
      (volume.restrict (Set.Icc (-M) M)) :=
    ((Complex.continuous_ofReal.comp hpth_cont).mul hκ).aestronglyMeasurable
  have hbound : ∀ᵐ a ∂(volume.restrict (Set.Icc (-M) M)),
      ∀ x ∈ Set.Ioo (x₀ - ε) (x₀ + ε),
        ‖((Work.Spaces.pth φ) a x : ℂ) * κ a‖ ≤ (fun _ : ℝ => C) a := by
    refine Filter.Eventually.of_forall fun a x hx => ?_
    by_cases ha : a ∈ Set.Icc (-M) M
    · have h1 : ‖((Work.Spaces.pth φ) a x : ℂ)‖ ≤ C := by
        simpa using hC (a, x) (Set.mem_prod.mpr ⟨ha,
          Set.mem_Icc.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩)
      calc ‖((Work.Spaces.pth φ) a x : ℂ) * κ a‖
          = ‖((Work.Spaces.pth φ) a x : ℂ)‖ * ‖κ a‖ := norm_mul _ _
        _ = ‖((Work.Spaces.pth φ) a x : ℂ)‖ := by rw [hκ1 a, mul_one]
        _ ≤ C := h1
    · rw [hpth_zero a (abs_lt_of_notMem_Icc' hM ha) x, Complex.ofReal_zero, zero_mul, norm_zero]
      exact hCnn
  have hb_int : Integrable (fun _ : ℝ => C) (volume.restrict (Set.Icc (-M) M)) :=
    MeasureTheory.integrableOn_const (μ := volume) (s := Set.Icc (-M) M) (C := C)
      (ne_of_lt (measure_Icc_lt_top (a := -M) (b := M))) (by simp)
  have hdiff : ∀ᵐ a ∂(volume.restrict (Set.Icc (-M) M)),
      ∀ x ∈ Set.Ioo (x₀ - ε) (x₀ + ε),
        HasDerivAt (fun x' : ℝ => (φ a x' : ℂ) * κ a)
          (((Work.Spaces.pth φ) a x : ℂ) * κ a) x := by
    refine Filter.Eventually.of_forall fun a x hx => ?_
    have hmem : (a, x) ∈ sliceStrp := ⟨trivial, hsub hx⟩
    have hd : DifferentiableAt ℝ (fun x' : ℝ => φ a x') x :=
      Work.Spaces.differentiableAt_curry_right
        ((hφ.differentiableOn (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
          (isOpen_sliceStrp.mem_nhds hmem))
    exact (hd.hasDerivAt.ofReal_comp).mul_const (κ a)
  obtain ⟨-, hmain⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc (-M) M)) (𝕜 := ℝ)
    (F := fun x t => (φ t x : ℂ) * κ t)
    (F' := fun x t => ((Work.Spaces.pth φ) t x : ℂ) * κ t)
    (bound := fun _ : ℝ => C) (x₀ := x₀) (s := Set.Ioo (x₀ - ε) (x₀ + ε))
    hs hF_meas hF_int hF'_meas hbound hb_int hdiff
  -- transfer the two restricted integrals back to the full line
  have hsupp_int : ∀ x ∈ Set.Ioo (x₀ - ε) (x₀ + ε),
      (∫ t, (φ t x : ℂ) * κ t) = ∫ t in Set.Icc (-M) M, (φ t x : ℂ) * κ t := by
    intro x hx
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by
        rw [hsupp t x (abs_lt_of_notMem_Icc' hM ht), Complex.ofReal_zero, zero_mul])).symm
  have hdersupp : (∫ t in Set.Icc (-M) M, ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t)
      = ∫ t, ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    rw [hpth_zero t (abs_lt_of_notMem_Icc' hM ht) x₀, Complex.ofReal_zero, zero_mul]
  refine (hmain.congr_of_eventuallyEq ?_).congr_deriv hdersupp
  filter_upwards [hs] with x hx
  exact hsupp_int x hx

/-! ## The `θ`-derivative of the slice is the slice of the `θ`-partial -/

theorem slice_deriv_eq (ψ : ℝ → ℝ → ℝ) (ξ : ℝ)
    (hψ : ContDiffOn ℝ 1 (Function.uncurry ψ) sliceStrp)
    (hψ' : ContinuousOn (Function.uncurry (Work.Spaces.pth ψ)) sliceStrp)
    {M : ℝ} (hM : 0 ≤ M) (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0) {θ : ℝ}
    (hθ : θ ∈ sliceSθ) :
    deriv (fun θ' : ℝ => slice ψ ξ θ') θ = slice (Work.Spaces.pth ψ) ξ θ :=
  (slice_hasDerivAt_aux ψ (sliceK ξ) hψ hψ' (continuous_sliceK ξ) (norm_sliceK ξ) hM hsupp hθ).deriv

/-! ## The induction -/

/-- The slice of a `C^k` datum with uniformly compact `t`-support is `C^k` on `(0,π/2)`. -/
theorem slice_contDiffOn_aux : ∀ (k : ℕ) (ψ : ℝ → ℝ → ℝ) (ξ : ℝ),
    ContDiffOn ℝ k (Function.uncurry ψ) sliceStrp →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → ψ t θ = 0) →
      ContDiffOn ℝ k (fun θ : ℝ => slice ψ ξ θ) sliceSθ := by
  intro k
  induction k with
  | zero =>
      intro ψ ξ hψ hsupp
      exact contDiffOn_zero.mpr (slice_continuousOn ψ ξ hψ hsupp)
  | succ k ih =>
      intro ψ ξ hψ hsupp
      obtain ⟨M, hM, hsuppM⟩ := hsupp
      have hψ1 : ContDiffOn ℝ 1 (Function.uncurry ψ) sliceStrp :=
        hψ.of_le (by simp)
      have hpth : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.pth ψ)) sliceStrp :=
        pth_contDiffOn_succ isOpen_sliceStrp hψ
      have hsupppth : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → Work.Spaces.pth ψ t θ = 0 := by
        refine ⟨M, hM, fun t θ ht => ?_⟩
        simp only [Work.Spaces.pth]
        rw [show (fun y : ℝ => ψ t y) = fun _ => (0 : ℝ) from funext fun y => hsuppM t y ht]
        simp
      have hpthc : ContinuousOn (Function.uncurry (Work.Spaces.pth ψ)) sliceStrp :=
        hpth.continuousOn
      have hderivcd : ContDiffOn ℝ k
          (fun θ : ℝ => slice (Work.Spaces.pth ψ) ξ θ) sliceSθ :=
        ih (Work.Spaces.pth ψ) ξ hpth hsupppth
      have hpoint : ∀ θ ∈ sliceSθ,
          deriv (fun θ' : ℝ => slice ψ ξ θ') θ = slice (Work.Spaces.pth ψ) ξ θ :=
        fun θ hθ => slice_deriv_eq ψ ξ hψ1 hpthc hM hsuppM hθ
      have hderiv : ContDiffOn ℝ k (deriv (fun θ' : ℝ => slice ψ ξ θ')) sliceSθ :=
        hderivcd.congr fun θ hθ => hpoint θ hθ
      have hdiff : DifferentiableOn ℝ (fun θ' : ℝ => slice ψ ξ θ') sliceSθ := fun θ hθ =>
        ((slice_hasDerivAt_aux ψ (sliceK ξ) hψ1 hpthc (continuous_sliceK ξ) (norm_sliceK ξ)
          hM hsuppM hθ).differentiableAt).differentiableWithinAt
      have hsucc : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun θ' : ℝ => slice ψ ξ θ') sliceSθ :=
        (contDiffOn_succ_iff_deriv_of_isOpen isOpen_sliceSθ).mpr
          ⟨hdiff, fun h => absurd h (by simp), hderiv⟩
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 from by simp]
      exact hsucc

end

/-- **Smoothness of the `t`-Fourier slice in the angle.**  A datum which is `C^n` (`n ≤ 2`)
on the open strip `ℝ × (0,π/2)` and has uniformly compact `t`-support has `C^n` slices
`θ ↦ ∫_t φ(t,θ) e^{-2πiξt} dt` on `(0,π/2)`. -/
theorem sliceContDiffOn {φ : ℝ → ℝ → ℝ} {n : ℕ} (hn : n ≤ 2)
    (hφ : ContDiffOn ℝ n (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsupp : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → φ t θ = 0) (ξ : ℝ) :
    ContDiffOn ℝ n (fun θ : ℝ => Work.FTS.EllSol.FlatFT.slice φ ξ θ) (Set.Ioo 0 (Real.pi / 2)) := by
  -- the induction of `slice_contDiffOn_aux` works for every order, so `hn` is not needed
  have _ := hn
  exact slice_contDiffOn_aux n φ ξ hφ hsupp

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.SlotEngineBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # Basic bookkeeping for `TraceEngine.slotBounds`

The domain facts, the commutativity of the iterates of `D_z` and the continuity of the
angular weight `w²·σ_η` on the open quadrant, all used by `slotBounds`. -/

theorem slotAux_measurableSet_dom : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  measurableSet_Ici.prod measurableSet_Icc

theorem slotAux_volume_restrict_dom :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
  (Measure.prod_restrict _ _).symm

/-- Almost every angle of `Iθ` is interior. -/
theorem slotAux_ae_mem_Ioo_Itheta :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  change ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `D_z` commutes with its own iterates. -/
theorem slotAux_Dz_DzIter_comm (r : ℕ) (V : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (Work.Spaces.DzIter r V) = Work.Spaces.DzIter r (Work.Spaces.Dz V) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      show Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V))
        = Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.Dz V))
      rw [ih]


theorem slotAux_Dz_iter_comm_apply (r : ℕ) (V : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ :=
  congrFun (congrFun (slotAux_Dz_DzIter_comm r V) z) θ

theorem slotAux_DzIter_two_comm (r : ℕ) (V : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V)
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) := by
  have h1 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V)
      = Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) := rfl
  have h2 : Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V))
      = Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.Dz V)) :=
    congrArg Work.Spaces.Dz (slotAux_Dz_DzIter_comm r V)
  have h3 : Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.Dz V))
      = Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.Dz V)) :=
    slotAux_Dz_DzIter_comm r (Work.Spaces.Dz V)
  have h4 : Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.Dz V))
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) := rfl
  exact h1.trans (h2.trans (h3.trans h4))

theorem slotAux_DzIter_two_comm_apply (r : ℕ) (V : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ :=
  congrFun (congrFun (slotAux_DzIter_two_comm r V) z) θ

theorem slotAux_pthIter_two_eq (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl

theorem slotAux_DzIter_two_eq (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter 2 f = Work.Spaces.Dz (Work.Spaces.Dz f) := rfl

/-- The weight `w²·σ_η` is continuous on the open quadrant. -/
theorem slotAux_continuousOn_w2_thEta :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    have h1 : (0 : ℝ) < p.2 := hp.2.1
    have h2 : p.2 < Real.pi / 2 := hp.2.2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
      funext p; simp only [Work.Spaces.w]
    rw [hfun]
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · exact (continuousOn_const.add continuousOn_fst).pow 2
    · exact continuousOn_fst.pow 2
    · intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      exact pow_ne_zero 2 (ne_of_gt hp1)
  have hth : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    simp only [Work.FTS.EllipticEst.thEta]
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    · intro p hp; exact Or.inl (ne_of_gt (hsinpos p hp))
  exact hw.mul hth

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.Shift2Flat.integrableOn_shift_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set

noncomputable section

set_option autoImplicit false

/-! ## Elementary facts about the `Ω`-weight `omegaAux`

`Ω` never vanishes (positivity), which is what allows the *integrable* majorant `(v²σ)·Ω` to
be divided by `Ω`, and it is continuous, which makes the resulting coefficient `e^{2bt}/Ω`
measurable.  Together these produce the a.e. strong measurability of the shifted integrand
`e^{2bt}(v²σ)`, even though nothing is assumed about the measurability of `u`, `v` or `σ`. -/

theorem shiftSq_omegaAux_pos (t : ℝ) : 0 < Work.FTS.EllSol.omegaAux t := by
  simp only [Work.FTS.EllSol.omegaAux]
  positivity

theorem shiftSq_continuous_omegaAux : Continuous (Work.FTS.EllSol.omegaAux) := by
  unfold Work.FTS.EllSol.omegaAux
  exact ((continuous_const.add Real.continuous_exp).pow 4).mul
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))

/-- On the closed strip `Iθ` the only points which are not interior are the two endpoints
`0` and `π/2`; this is what makes the passage from the open strip (where the identity
`u = e^{bt} v` is available) to `univ ×ˢ Iθ` harmless. -/
theorem shiftSq_Iθ_diff_Ioo_eq_endpoints {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hθ' : θ ∉ Set.Ioo 0 (Real.pi / 2)) : θ = 0 ∨ θ = Real.pi / 2 := by
  have hIcc : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
  rcases eq_or_lt_of_le hIcc.1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm hIcc.2 (le_of_not_gt fun hlt => hθ' ⟨h, hlt⟩))

/-- The set of non-interior points of the strip is null. -/
theorem shiftSq_volume_prod_endpoints :
    (volume : Measure (ℝ × ℝ)) (Set.univ ×ˢ ({0, Real.pi / 2} : Set ℝ)) = 0 := by
  have h : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 := by
    rw [Set.insert_eq]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton _)
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, h, mul_zero]

/-- Transfer of `σ`-weighted square integrability under the exponential shift `u = e^{bt} v`:
if the `Ω`-weighted square of `v` is integrable on the strip `univ ×ˢ Iθ` (with `Ω` dominating
`e^{2bt}`), and `u = e^{bt}·v` on the open strip `0 < θ < π/2`, then the `σ`-weighted square of
`u` is integrable on the strip.  No measurability of `u`, `v`, `σ` is assumed: it is produced
from the integrability of the majorant. -/
theorem integrableOn_shift_sq {b : ℝ} {u v : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hexp : ∀ t : ℝ, Real.exp (2 * b * t) ≤ Work.FTS.EllSol.omegaAux t)
    (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hv : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hid : ∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      u t θ = Real.exp (b * t) * v t θ) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2 * σ p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
  set S : Set (ℝ × ℝ) := Set.univ ×ˢ Work.Spaces.Iθ with hS
  set G : ℝ × ℝ → ℝ := fun p => (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2
    with hGdef
  set G0 : ℝ × ℝ → ℝ := fun p => (v p.1 p.2) ^ 2 * σ p.2 with hG0def
  set f0 : ℝ × ℝ → ℝ := fun p => Real.exp (2 * b * p.1) * G0 p with hf0def
  have hSmeas : MeasurableSet S := by
    rw [hS]; exact MeasurableSet.univ.prod measurableSet_Icc
  -- the majorant `G` is integrable on the (restricted) strip
  have hGint : Integrable G (volume.restrict S) := by
    rw [hS, hGdef]
    exact hv
  -- `f0` is a.e. strongly measurable: it is `(e^{2bt}/Ω)·G` and `Ω` never vanishes
  have hf0_eq : f0 = fun p : ℝ × ℝ =>
      (Real.exp (2 * b * p.1) / Work.FTS.EllSol.omegaAux p.1) * G p := by
    funext p
    have hω : Work.FTS.EllSol.omegaAux p.1 ≠ 0 :=
      ne_of_gt (shiftSq_omegaAux_pos p.1)
    simp only [hf0def, hGdef, hG0def]
    field_simp
  have hf0_aesm : AEStronglyMeasurable f0 (volume.restrict S) := by
    rw [hf0_eq]
    have hc : Measurable (fun p : ℝ × ℝ =>
        Real.exp (2 * b * p.1) / Work.FTS.EllSol.omegaAux p.1) :=
      (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).div
        (shiftSq_continuous_omegaAux.measurable.comp measurable_fst)
    exact hc.aestronglyMeasurable.mul hGint.aestronglyMeasurable
  -- a.e. domination: on the strip `σ ≥ 0` and `e^{2bt} ≤ Ω`
  have hmono : ∀ᵐ p ∂(volume.restrict S), ‖f0 p‖ ≤ G p := by
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with p hp
    have hpIθ : p.2 ∈ Work.Spaces.Iθ := by
      simpa only [hS, Set.mem_prod, Set.mem_univ, true_and] using hp
    have hσp : 0 ≤ σ p.2 := hσ p.2 hpIθ
    have hf0unf : f0 p = Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2) := rfl
    have hGunf : G p = (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2 := rfl
    have hωnn : 0 ≤ Work.FTS.EllSol.omegaAux p.1 :=
      le_of_lt (shiftSq_omegaAux_pos p.1)
    have hG0nn : 0 ≤ (v p.1 p.2) ^ 2 * σ p.2 := mul_nonneg (sq_nonneg _) hσp
    have hf0nn : 0 ≤ Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2) :=
      mul_nonneg (Real.exp_nonneg _) hG0nn
    have hGnn : 0 ≤ (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hωnn) hσp
    have hmain : Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2)
        ≤ (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2 := by
      calc Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2)
          ≤ Work.FTS.EllSol.omegaAux p.1 * ((v p.1 p.2) ^ 2 * σ p.2) :=
            mul_le_mul_of_nonneg_right (hexp p.1) hG0nn
        _ = (v p.1 p.2) ^ 2 * Work.FTS.EllSol.omegaAux p.1 * σ p.2 := by ring
    have hf0abs : ‖f0 p‖ = Real.exp (2 * b * p.1) * ((v p.1 p.2) ^ 2 * σ p.2) := by
      rw [hf0unf, Real.norm_eq_abs, abs_of_nonneg hf0nn]
    rw [hf0abs, hGunf]
    exact hmain
  -- the only points of `S` where the identity `u = e^{bt}v` may fail are the endpoints
  have haeIoo : ∀ᵐ p ∂(volume.restrict S), p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' hSmeas, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ shiftSq_volume_prod_endpoints
    intro p hp
    simp only [Set.mem_ofPred_eq, not_imp] at hp
    have hpIθ : p.2 ∈ Work.Spaces.Iθ := by
      simpa only [hS, Set.mem_prod, Set.mem_univ, true_and] using hp.1
    have hmem : p.2 = 0 ∨ p.2 = Real.pi / 2 := shiftSq_Iθ_diff_Ioo_eq_endpoints hpIθ hp.2
    refine ⟨Set.mem_univ _, ?_⟩
    rcases hmem with h0 | hpi
    · rw [Set.mem_insert_iff]; exact Or.inl h0
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr hpi
  have hFint : Integrable (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2 * σ p.2)
      (volume.restrict S) := by
    refine (hGint.mono' hf0_aesm hmono).congr ?_
    filter_upwards [haeIoo] with p hp
    have hG0unf : G0 p = (v p.1 p.2) ^ 2 * σ p.2 := rfl
    have hf0unf : f0 p = Real.exp (2 * b * p.1) * G0 p := rfl
    rw [hf0unf, hG0unf, hid p.1 p.2 hp]
    have hexp2 : Real.exp (2 * b * p.1) = Real.exp (b * p.1) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [hexp2, mul_pow]
    ring
  exact hFint

end

end Work.FTS.EllSol.Shift2Flat
end
-- ===== merged: Submission.Work.FTS.EllSol.SpecAux.timFlipData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

-- The time reversal `(t,θ) ↦ u (-t) θ` is the composition of `u` with the (linear, hence
-- smooth) map `(t,θ) ↦ (-t,θ)`, which maps the strip `ℝ × (0,π/2)` to itself; hence it
-- preserves `C²`-regularity on the strip.
theorem timFlip_strip_contDiffOn (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (Function.uncurry (timFlip u))
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hflip : ContDiff ℝ 2 (fun p : ℝ × ℝ => (-p.1, p.2)) := by fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (-p.1, p.2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun p hp => ⟨trivial, hp.2⟩
  rw [uncurry_timFlip_eq_comp u]
  exact hu.comp hflip.contDiffOn hmaps


end Work.FTS.EllSol.SpecAux
end
-- ===== merged: Submission.Work.FTS.EllSol.Trunc.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The basic smooth cutoff: `= 1` for `|t| ≤ 1`, `= 0` for `2 ≤ |t|`. -/
def tk (t : ℝ) : ℝ := Real.smoothTransition (2 - t ^ 2)

theorem tk_contDiff (n : ℕ) : ContDiff ℝ n tk := by
  have h1 : ContDiff ℝ n (fun t : ℝ => 2 - t ^ 2) :=
    contDiff_const.sub (contDiff_id.pow 2)
  have h2 : ContDiff ℝ n (Real.smoothTransition : ℝ → ℝ) :=
    Real.smoothTransition.contDiff (n := (n : ℕ∞))
  exact h2.comp h1

theorem tk_nonneg (t : ℝ) : 0 ≤ tk t := Real.smoothTransition.nonneg _

theorem tk_le_one (t : ℝ) : tk t ≤ 1 := Real.smoothTransition.le_one _

/-- `tk t = 1` whenever `|t| ≤ 1`. -/
theorem tk_eq_one {t : ℝ} (h : |t| ≤ 1) : tk t = 1 := by
  unfold tk
  apply Real.smoothTransition.one_of_one_le
  have h2 : t ^ 2 ≤ 1 := by
    have := abs_le.mp h
    nlinarith [this.1, this.2]
  linarith

/-- `tk t = 0` whenever `2 ≤ |t|`. -/
theorem tk_eq_zero {t : ℝ} (h : 2 ≤ |t|) : tk t = 0 := by
  unfold tk
  apply Real.smoothTransition.zero_of_nonpos
  have h2 : (4:ℝ) ≤ t ^ 2 := by
    have h3 := sq_abs t
    nlinarith [abs_nonneg t, h, h3]
  linarith

/-- The cutoff at scale `N`: `chi N t = tk (t/N)`. -/
def chi (N : ℝ) (t : ℝ) : ℝ := tk (t / N)

theorem chi_contDiff (n : ℕ) (N : ℝ) : ContDiff ℝ n (chi N) := by
  have h1 : ContDiff ℝ n (fun t : ℝ => t / N) := contDiff_id.div_const N
  have h2 : ContDiff ℝ n (tk : ℝ → ℝ) := tk_contDiff n
  exact h2.comp h1

theorem chi_nonneg (N t : ℝ) : 0 ≤ chi N t := tk_nonneg _

theorem chi_le_one (N t : ℝ) : chi N t ≤ 1 := tk_le_one _

/-- For `N > 0` the cutoff is `1` on `[-N,N]`. -/
theorem chi_eq_one {N t : ℝ} (hN : 0 < N) (h : |t| ≤ N) : chi N t = 1 := by
  unfold chi
  apply tk_eq_one
  rw [abs_div, abs_of_pos hN]
  exact (div_le_one hN).mpr h

/-- For `N > 0` the cutoff vanishes off `[-2N,2N]`. -/
theorem chi_eq_zero {N t : ℝ} (hN : 0 < N) (h : 2 * N ≤ |t|) : chi N t = 0 := by
  unfold chi
  apply tk_eq_zero
  rw [abs_div, abs_of_pos hN]
  rw [le_div_iff₀ hN]
  linarith

/-- The derivative of the cutoff at scale `N`. -/
theorem deriv_chi_eq (N t : ℝ) : deriv (chi N) t = deriv tk (t / N) / N := by
  rw [show chi N = fun s : ℝ => tk (s / N) from rfl]
  change deriv (tk ∘ fun s : ℝ => s / N) t = deriv tk (t / N) / N
  rw [deriv_comp]
  · rw [deriv_div_const, deriv_id'', div_eq_mul_inv]
    ring
  · exact (tk_contDiff 1).differentiable (by norm_num) (t / N)
  · exact differentiableAt_id.div_const N

/-- `deriv tk` is bounded. -/
theorem exists_bound_deriv_tk : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv tk t| ≤ K := by
  have hcont : Continuous (deriv tk) := (tk_contDiff 1).continuous_deriv (by norm_num)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-2:ℝ) 2
  · exact le_trans (hK t ht) (le_max_left _ _)
  · have h0 : deriv tk t = 0 := by
      have hev : tk =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        have hopen : IsOpen {s : ℝ | 2 < |s|} := isOpen_lt continuous_const continuous_abs
        have hmem : t ∈ {s : ℝ | 2 < |s|} := by
          rw [Set.mem_setOf_eq]
          exact lt_of_not_ge fun hle => ht (Set.mem_Icc.mpr (abs_le.mp hle))
        filter_upwards [hopen.mem_nhds hmem] with s hs
        exact tk_eq_zero (le_of_lt hs)
      rw [hev.deriv_eq, deriv_const]
    rw [h0, abs_zero]
    exact le_max_right _ _

/-- The bound on the derivative of the cutoff at scale `N`. -/
theorem abs_deriv_chi_le {K N : ℝ} (hK : ∀ t : ℝ, |deriv tk t| ≤ K) (hN : 0 < N) (t : ℝ) :
    |deriv (chi N) t| ≤ K / N := by
  rw [deriv_chi_eq, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right (hK (t / N)) (le_of_lt hN)

/-! ## Elementary pointwise algebra -/



/-- `(a+b+c)² ≤ 3(a²+b²+c²)` (Cauchy–Schwarz in `ℝ³`). -/
theorem three_sq_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-! ## The "nice" (compactly supported) case, as a predicate

`NiceBound C` is exactly the conclusion of `Work.FTS.EllSol.FlatFT.flat2DAgmonNiceB` (in
product-integral form): the `flat2DAgmon` inequality with constant `C` for data of class
`NiceFlat`.  `flat2DAgmon` is then obtained by `flat2DAgmon_of_nice`, which passes from
`NiceBound C₀` to the general data of the target. -/


end

end Work.FTS.EllSol.Trunc
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.sliceGroup_pth_eq_sliceW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Clairaut for `∂_θ` and `D_z^j` on the open quadrant.**  For `f` which is `C^∞` on the open
quadrant, `D_z^j (∂_θ f)` is the `θ`-derivative of the `D_z^j`-slice.  This is the pointwise form
of the general open-set statement
`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen`. -/
theorem DzIter_pth_eq_deriv_quad {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
      = deriv (fun θ' => Work.Spaces.DzIter j f z θ') θ :=
  (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
    (isOpen_Ioi.prod isOpen_Ioo) hf j
    (show (z, θ) ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) from ⟨hz, hθ⟩)).symm

/-- **The angular iterates of the `θ`-derivative of a slice.**  For `f` which is `C^∞` on the
open quadrant, the `i`-th iterate of `L = D_θ = sin(2θ)∂_θ` applied to the derived slice
`θ' ↦ ∂_θ(D_z^j f z ·)` is the mixed derivative `D_z^j D_θ^i (∂_θ f)`.  This is the open-quadrant
counterpart of `Work.FTS.EllipticEst.ThetaU.LopIter_deriv_DzIter_eq_mixed_open`, which is stated
in the half-strip class `SmoothOpenθ`. -/
theorem LopIter_deriv_DzIter_eq_mixed_quad {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.LopIter i
        (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ
      = Work.Spaces.mixed j i (Work.Spaces.pth f) z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  -- `pth f` is `C^∞` on the open quadrant as well
  have hf_pth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.LocData.contDiffOn_pth hV (contDiffOn_infty.mpr hf)).of_le (by simp)
  -- the two slices agree on the open interval `(0,π/2)`, which contains `θ`
  have hEq : Set.EqOn (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ')
      (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ' hθ'
    show deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ'
      = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ'
    exact (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen hV hf j
      (show (z, θ') ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) from ⟨hz, hθ'⟩))
  rw [Work.FTS.EllipticEst.ThetaU.LopIter_congr_of_isOpen isOpen_Ioo hEq i hθ]
  rw [congrFun (Work.FTS.EllipticEst.LopIter_slice i
    (Work.Spaces.DzIter j (Work.Spaces.pth f)) z) θ]
  exact Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hf_pth j i hz hθ

/-
# The `j`-th slice group of the `ℋ^k`-integrand of `∂_θ f`, rewritten through a single slice

Same setting as `Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW`, with `f` replaced by its angular
derivative `Work.Spaces.pth f`:
claim: for `z > 0`, `θ ∈ (0,π/2)` and `f` of class `C^∞` on the open quadrant,

  `sliceGroup α k j (pth f) z θ
     = (w z)² · sliceW (k-j) α (fun θ' => deriv (fun θ'' => D_z^j f z θ'') θ') θ`,

where `sliceW K α u θ = (u θ)²·thEta θ + ∑_{1≤i≤K}(L^i u θ)²·thGam α θ` is the single-slice
functional of `Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean`.

ROUTE: as in `sliceGroup_eq_sliceW`, unfold `sliceGroup`, use
`Work.FTS.EllipticEst.w_div_sin_sq`/`Wt_sq` for the weights, and identify the mixed terms: for
`θ ∈ (0,π/2)` and `z > 0`,
`mixed j i (pth f) z θ = D_θ^i (D_z^j (pth f)) z θ` (open-quadrant commutation
`Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open` in `SliceDecompDefs`), while
`D_z^j (pth f) = pth (D_z^j f)` pointwise on the open quadrant — that is
`pth_DzIter_eqOn_of_isOpen` from
`Submission/Work/FTS/EllipticEst/ThetaU/OpenSliceAux/pth_DzIter_eqOn_of_isOpen.lean` (Clairaut for
`∂_θ` and `D_z^j`, stated for an arbitrary open set with the raw `∀ n, ContDiffOn ℝ n`
hypothesis), so the mixed term is
`D_θ^i (pth (D_z^j f)) z θ = L^i (fun θ' => deriv (fun θ'' => D_z^j f z θ'') θ') θ`
by `Work.FTS.EllipticEst.LopIter_slice`. Note that `fun θ' => pth (D_z^j f) z θ'` is
*definitionally* `fun θ' => deriv (fun θ'' => D_z^j f z θ'') θ'`. The `j`-th radial summand
similarly uses `DzIter j (pth f) z θ = deriv (fun θ'' => DzIter j f z θ'') θ`
(`Work.FTS.EllipticEst.DzIter_pth_eq_deriv`-style, again from the open-quadrant Clairaut fact).
-/
theorem sliceGroup_pth_eq_sliceW (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ
        = (Work.Spaces.w z) ^ 2
            * Work.FTS.EllSol.VopAux.sliceW (k - j) α
                (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ := by
  intro θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the `j`-th radial summand: `D_z^j (∂_θ f)` is `∂_θ` of the `D_z^j`-slice
  have hB : Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
      = deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ :=
    DzIter_pth_eq_deriv_quad hf j hz hθ
  -- the mixed summands: `D_z^j D_θ^i (∂_θ f)` is the `L^i`-iterate of the derived slice
  have hA : ∀ i : ℕ, Work.FTS.EllipticEst.LopIter i
        (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ
      = Work.Spaces.mixed j i (Work.Spaces.pth f) z θ :=
    fun i => LopIter_deriv_DzIter_eq_mixed_quad hf j i hz hθ
  -- the radial summand is `w(z)²` times the `η`-weighted square of the derived slice
  have hrad : (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2
          * ((deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
    rw [hB, mul_pow, Work.FTS.EllipticEst.w_div_sin_sq hθIθ z]
    ring
  -- and each mixed summand is `w(z)²` times the `γ`-weighted square of its `L`-iterate
  have hmix : ∀ i ∈ Finset.Icc 1 (k - j),
      (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 *
            ((Work.FTS.EllipticEst.LopIter i
                (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ) ^ 2
              * Work.FTS.EllipticEst.thGam α θ) := by
    intro i _
    rw [← hA i, mul_pow, Work.FTS.EllipticEst.Wt_sq hθIθ α z]
    ring
  rw [Work.FTS.EllipticEst.sliceGroup, Work.FTS.EllSol.VopAux.sliceW]
  rw [hrad]
  rw [Finset.sum_congr rfl hmix]
  rw [mul_add, Finset.mul_sum]

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Fstar_div_integrable_of_sol_Hk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.FstarSmooth

/-! ## Placeholders for the two delegated lemmas (exactly as requested) -/



/-! ## The source is `C^∞` on the open quadrant -/


/-! ## The `ℋ⁰`-integrand and its domination by the `ℋ^k`-integrand -/

theorem HkIntegrand_zero_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem HkIntegrand_zero_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [HkIntegrand_zero_apply, Work.Spaces.HkIntegrand]
  have hmixed : 0 ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs with hc
      · exact sq_nonneg _
      · exact le_refl 0
  have hsingle : (Work.Spaces.DzIter 0 f z θ * (Work.Spaces.w z
        / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    Finset.single_le_sum
      (s := Finset.range (k + 1))
      (f := fun i => (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.succ_pos k))
  exact le_trans (by simpa only [Work.Spaces.DzIter_zero] using hsingle)
    (le_add_of_nonneg_right hmixed)


/-! ## `F_*` as an angular integral of `bslOp α Ψ` -/


/-! ## The pointwise bound -/



/-! ## A.e. strong measurability of `F_*(F)/·` -/


/-! ## The main theorem -/


end Work.FTS.EllipticEst.Cert.FstarSmooth
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.sliceRateSigA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

theorem sliceRateSigA :
    ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∃ K : ℝ, 0 < K ∧ ∀ (Φ : ℝ → ℝ),
        ContDiffOn ℝ 1 Φ (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (deriv Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
        (∃ c : ℝ, Filter.Tendsto Φ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
            ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
              (Φ θ - c) ^ 2 ≤ K * θ ^ (Work.Spaces.gam α - 1) *
                ∫ θ' in Set.Ioo 0 θ,
                  (deriv Φ θ') ^ 2 * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α))
        ∧ (∃ c : ℝ,
            Filter.Tendsto Φ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
            ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
              (Φ θ - c) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) *
                ∫ θ' in Set.Ioo θ (Real.pi / 2),
                  (deriv Φ θ') ^ 2 * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) := by
  intro α hα hα1
  obtain ⟨KW, hKW, hKWb⟩ := integral_sigA_inv_le α hα hα1
  obtain ⟨KWr, hKWr, hKWrb⟩ := integral_sigA_inv_le_right α hα hα1
  have he : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hKpos : (0 : ℝ) < max KW KWr := lt_of_lt_of_le hKW (le_max_left _ _)
  have hKnn : (0 : ℝ) ≤ max KW KWr := hKpos.le
  refine ⟨max KW KWr, hKpos, fun Φ hΦ hInt => ⟨?_, ?_⟩⟩
  · -- ===================== left endpoint =====================
    have hA : IntegrableOn (fun t : ℝ => (deriv Φ t) ^ 2 * sigA α t)
        (Set.Ioo 0 (Real.pi / 2)) := hInt
    have hB : IntegrableOn (fun t : ℝ => (sigA α t)⁻¹) (Set.Ioo 0 (Real.pi / 2)) :=
      (integrableOn_sigA_inv hα hα1).mono_set Set.Ioo_subset_Icc_self
    have hderiv : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 2)) :=
      integrableOn_deriv measurableSet_Ioo (fun t ht => ht) hA hB
    set c : ℝ := Φ (Real.pi / 4) - ∫ t in Set.Ioo 0 (Real.pi / 4), deriv Φ t with hc
    have hid : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Φ θ - c = ∫ t in Set.Ioo 0 θ, deriv Φ t := by
      intro θ hθ
      rw [hc]
      exact ftc_at_quarter hΦ hderiv θ hθ
    have hMnn : (0 : ℝ) ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
      setIntegral_nonneg measurableSet_Ioo (fun t ht => sq_mul_sigA_nonneg ht (deriv Φ t))
    have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Φ θ - c) ^ 2 ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
          * ∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t := by
      intro θ hθ
      have hs : Set.Ioo (0 : ℝ) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
        fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
      have hAθ : IntegrableOn (fun t => (deriv Φ t) ^ 2 * sigA α t) (Set.Ioo 0 θ) :=
        hA.mono_set hs
      have hBθ : IntegrableOn (fun t => (sigA α t)⁻¹) (Set.Ioo 0 θ) := hB.mono_set hs
      have hcs := cs_step hα1 measurableSet_Ioo hs hAθ hBθ
      rw [hid θ hθ]
      have h2 : ∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹ ≤ KW * θ ^ (Work.Spaces.gam α - 1) :=
        hKWb θ hθ
      have h5 : KW ≤ max KW KWr := le_max_left _ _
      have h6 : (0 : ℝ) ≤ θ ^ (Work.Spaces.gam α - 1) := Real.rpow_nonneg hθ.1.le _
      have h7 : (0 : ℝ) ≤ ∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t :=
        setIntegral_nonneg measurableSet_Ioo (fun x hx => sq_mul_sigA_nonneg (hs hx) (deriv Φ x))
      calc (∫ t in Set.Ioo 0 θ, deriv Φ t) ^ 2
          ≤ (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
              * (∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
              * (KW * θ ^ (Work.Spaces.gam α - 1)) := mul_le_mul_of_nonneg_left h2 h7
        _ ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
              * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t) := by
            rw [show (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
                  * (KW * θ ^ (Work.Spaces.gam α - 1))
                = KW * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
                  * θ ^ (Work.Spaces.gam α - 1) from by ring,
              show (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
                  * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
                = (max KW KWr) * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t)
                  * θ ^ (Work.Spaces.gam α - 1) from by ring]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 h7) h6
    have hfull : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Φ θ - c) ^ 2 ≤ (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
          * θ ^ (Work.Spaces.gam α - 1) := by
      intro θ hθ
      have h1 : ∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t
          ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
        setIntegral_mono_Ioo hθ.2.le hA (fun x hx => sq_mul_sigA_nonneg hx (deriv Φ x))
      have h2 : (0 : ℝ) ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1) :=
        mul_nonneg hKnn (Real.rpow_nonneg hθ.1.le _)
      calc (Φ θ - c) ^ 2
          ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
            * (∫ t in Set.Ioo 0 θ, (deriv Φ t) ^ 2 * sigA α t) := hbound θ hθ
        _ ≤ (max KW KWr) * θ ^ (Work.Spaces.gam α - 1)
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = (max KW KWr * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
            * θ ^ (Work.Spaces.gam α - 1) := by ring
    have habs : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |Φ θ - c| ≤ Real.sqrt (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
          * θ ^ ((Work.Spaces.gam α - 1) / 2) := by
      intro θ hθ
      exact abs_le_sqrt_mul_rpow hKnn hMnn hθ.1.le (hfull θ hθ)
    have hlim : Tendsto Φ (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
      have h0 : Tendsto (fun θ => Φ θ - c) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_zero_of_abs_le (A := Real.sqrt (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)))
          (by linarith : 0 < (Work.Spaces.gam α - 1) / 2) habs
      have h1 := Tendsto.add_const c h0
      simpa using h1
    exact ⟨c, hlim, hbound⟩
  · -- ===================== right endpoint =====================
    have hA : IntegrableOn (fun t : ℝ => (deriv Φ t) ^ 2 * sigA α t)
        (Set.Ioo 0 (Real.pi / 2)) := hInt
    have hB : IntegrableOn (fun t : ℝ => (sigA α t)⁻¹) (Set.Ioo 0 (Real.pi / 2)) :=
      (integrableOn_sigA_inv hα hα1).mono_set Set.Ioo_subset_Icc_self
    have hderiv : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 2)) :=
      integrableOn_deriv measurableSet_Ioo (fun t ht => ht) hA hB
    set c : ℝ := Φ (Real.pi / 4) + ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), deriv Φ t with hc
    have hid : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Φ θ - c = -(∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t) := by
      intro θ hθ
      rw [hc]
      exact ftc_at_quarter_right hΦ hderiv θ hθ
    have hMnn : (0 : ℝ) ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
      setIntegral_nonneg measurableSet_Ioo (fun t ht => sq_mul_sigA_nonneg ht (deriv Φ t))
    have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Φ θ - c) ^ 2 ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
          * ∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t := by
      intro θ hθ
      have hs : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
        fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
      have hAθ : IntegrableOn (fun t => (deriv Φ t) ^ 2 * sigA α t)
          (Set.Ioo θ (Real.pi / 2)) := hA.mono_set hs
      have hBθ : IntegrableOn (fun t => (sigA α t)⁻¹) (Set.Ioo θ (Real.pi / 2)) :=
        hB.mono_set hs
      have hcs := cs_step hα1 measurableSet_Ioo hs hAθ hBθ
      rw [hid θ hθ]
      rw [show (-(∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t)) ^ 2
          = (∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t) ^ 2 from by ring]
      have h2 : ∫ t in Set.Ioo θ (Real.pi / 2), (sigA α t)⁻¹
          ≤ KWr * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) := hKWrb θ hθ
      have h5 : KWr ≤ max KW KWr := le_max_right _ _
      have h6 : (0 : ℝ) ≤ (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) :=
        Real.rpow_nonneg (by linarith [hθ.2]) _
      have h7 : (0 : ℝ) ≤ ∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
        setIntegral_nonneg measurableSet_Ioo (fun x hx => sq_mul_sigA_nonneg (hs hx) (deriv Φ x))
      calc (∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t) ^ 2
          ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
              * (∫ t in Set.Ioo θ (Real.pi / 2), (sigA α t)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
              * (KWr * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)) :=
            mul_le_mul_of_nonneg_left h2 h7
        _ ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
              * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t) := by
            rw [show (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
                  * (KWr * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1))
                = KWr * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
                  * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) from by ring,
              show (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
                  * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
                = (max KW KWr) * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)
                  * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) from by ring]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 h7) h6
    have hfull : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Φ θ - c) ^ 2 ≤ (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
          * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) := by
      intro θ hθ
      have h1 : ∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t
          ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t :=
        setIntegral_mono_Ioo_left hθ.1.le hA (fun x hx => sq_mul_sigA_nonneg hx (deriv Φ x))
      have h2 : (0 : ℝ) ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) :=
        mul_nonneg hKnn (Real.rpow_nonneg (by linarith [hθ.2]) _)
      calc (Φ θ - c) ^ 2
          ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
            * (∫ t in Set.Ioo θ (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t) := hbound θ hθ
        _ ≤ (max KW KWr) * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1)
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = (max KW KWr * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
            * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) := by ring
    have habs : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Φ (Real.pi / 2 - y) - c| ≤ Real.sqrt (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
          * y ^ ((Work.Spaces.gam α - 1) / 2) := by
      intro y hy
      have hθ : Real.pi / 2 - y ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have hfy : (Φ (Real.pi / 2 - y) - c) ^ 2
          ≤ (max KW KWr * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t))
            * y ^ (Work.Spaces.gam α - 1) := by
        have hf := hfull (Real.pi / 2 - y) hθ
        simpa [show Real.pi / 2 - (Real.pi / 2 - y) = y from by ring] using hf
      exact abs_le_sqrt_mul_rpow hKnn hMnn hy.1.le hfy
    have hlim : Tendsto Φ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) := by
      have h0 : Tendsto (fun θ => Φ θ - c) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds 0) :=
        tendsto_zero_of_abs_le_reflect (A := Real.sqrt (max KW KWr
            * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv Φ t) ^ 2 * sigA α t)))
          (by linarith : 0 < (Work.Spaces.gam α - 1) / 2) habs
      have h1 := Tendsto.add_const c h0
      simpa using h1
    exact ⟨c, hlim, hbound⟩

end Work.FTS.EllipticEst.Cores
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.outerIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg.mixedTrunc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary continuity facts -/

/-- `σ θ = sin(2θ)^{-η}` is continuous on the open angular interval `(0, π/2)`. -/
theorem oi_continuousOn_sigθ :
    ContinuousOn Work.FTS.EllipticEst.AeColl.sigθ (Set.Ioo 0 (Real.pi / 2)) := by
  have h : Work.FTS.EllipticEst.AeColl.sigθ
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
  rw [h]
  refine ContinuousOn.rpow_const ?_ ?_
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.mono
      (Set.subset_univ _)
  · intro θ hθ
    left
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))

/-- `w z ²` is continuous on the open half-line (the pole at `z = 0` is not met). -/
theorem oi_continuousOn_wt :
    ContinuousOn Work.FTS.EllipticEst.AeColl.wt (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ContinuousOn.pow ((continuous_const.add continuous_id).continuousOn) 2
    · exact ContinuousOn.pow (continuous_id.continuousOn) 2
    · intro z hz
      exact pow_ne_zero 2 (ne_of_gt hz)
  have h : Work.FTS.EllipticEst.AeColl.wt = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
  rw [h]
  exact ContinuousOn.pow hw 2

/-- `ψ_δ''` vanishes off the closed interval `[δ/4, π/2 - δ/4]`: `ψ_δ` is identically zero on a
whole *neighbourhood* of every point of the complement (no hypothesis on `δ` is needed). -/
theorem oi_psiD2_eq_zero_of_notMem (δ : ℝ) :
    ∀ θ : ℝ, θ ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) →
      deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ = 0 := by
  intro θ hθ
  have hpsi : ∀ θ' : ℝ, θ' ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) →
      Work.FTS.EllipticEst.AeColl.psiD δ θ' = 0 :=
    fun θ' h' => Work.FTS.EllipticEst.AeColl.psiD_eq_zero_of_notMem δ θ' h'
  -- `ψ_δ` vanishes on a whole neighbourhood of `θ` ...
  have hmem : Set.Iio (δ / 4) ∈ 𝓝 θ ∨ Set.Ioi (Real.pi / 2 - δ / 4) ∈ 𝓝 θ := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    rcases hθ with h | h
    · exact Or.inl (isOpen_Iio.mem_nhds h)
    · exact Or.inr (isOpen_Ioi.mem_nhds h)
  -- ... hence so does its first derivative, and then its second derivative vanishes
  have h1 : deriv (Work.FTS.EllipticEst.AeColl.psiD δ) =ᶠ[𝓝 θ] (fun _ : ℝ => (0 : ℝ)) := by
    rcases hmem with hmem | hmem
    · filter_upwards [hmem] with θ' hθ'
      have heq : Work.FTS.EllipticEst.AeColl.psiD δ =ᶠ[𝓝 θ'] (fun _ : ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem (isOpen_Iio.mem_nhds hθ') (fun θ'' hθ'' => hpsi θ'' (by
          rw [Set.mem_Icc, not_and_or, not_le, not_le]
          exact Or.inl hθ''))
      simpa using heq.deriv_eq
    · filter_upwards [hmem] with θ' hθ'
      have heq : Work.FTS.EllipticEst.AeColl.psiD δ =ᶠ[𝓝 θ'] (fun _ : ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hθ') (fun θ'' hθ'' => hpsi θ'' (by
          rw [Set.mem_Icc, not_and_or, not_le, not_le]
          exact Or.inr hθ''))
      simpa using heq.deriv_eq
  calc deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
      = deriv (fun _ : ℝ => (0 : ℝ)) θ := h1.deriv_eq
    _ = 0 := by simp

/-! ## The general shape -/

/-- **The outer integrability of one truncated angular energy.**  For an angular factor `κ`
supported in `[δ/4, π/2 - δ/4]` and an angular `X` whose joint composite with `σ` and `κ` is
continuous on the open quadrant, the radial integral of `χ_n·w²·∫_θ σ κ X²` is finite. -/
theorem oi_shape (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2)
    (κ : ℝ → ℝ) (X : ℝ → ℝ → ℝ)
    (hκ : ∀ θ : ℝ, θ ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) → κ θ = 0)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2 * κ p.2
      * (X p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2)) (Set.Ioi 0) := by
  set a : ℝ := 1 / ((n : ℝ) + 1) with ha
  set b : ℝ := 3 * ((n : ℝ) + 1) with hb
  set c : ℝ := δ / 4 with hc
  set c' : ℝ := Real.pi / 2 - δ / 4 with hc'
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hab : a < b := by
    rw [ha, hb, div_lt_iff₀ hn1]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    nlinarith [h1]
  have hc_pos : 0 < c := by rw [hc]; linarith
  have hc'_lt : c' < Real.pi / 2 := by rw [hc']; linarith
  have hcc' : c < c' := by rw [hc, hc']; linarith [hδ2, Real.pi_pos]
  have hIcc_sub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha_pos hz.1
  have hsub : Set.Icc c c' ⊆ Set.Ioo 0 (Real.pi / 2) := fun θ hθ =>
    ⟨lt_of_lt_of_le hc_pos hθ.1, lt_of_le_of_lt hθ.2 hc'_lt⟩
  have hRsub : (Set.Icc a b ×ˢ Set.Icc c c') ⊆
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun p hp => ⟨hIcc_sub hp.1, hsub hp.2⟩
  -- a uniform bound for the angular integrand on the compact rectangle
  obtain ⟨M₂, hM₂⟩ := ((isCompact_Icc (a := a) (b := b)).prod
    (isCompact_Icc (a := c) (b := c'))).exists_bound_of_continuousOn (hcont.mono hRsub)
  have hM₂nn : 0 ≤ M₂ := by
    have hmem : (a, c) ∈ Set.Icc a b ×ˢ Set.Icc c c' :=
      ⟨⟨le_rfl, le_of_lt hab⟩, ⟨le_rfl, le_of_lt hcc'⟩⟩
    exact le_trans (norm_nonneg _) (hM₂ (a, c) hmem)
  -- a uniform bound for `χ_n · w²`
  have hcutwt_cont : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z) (Set.Icc a b) :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn).mul
      (oi_continuousOn_wt.mono hIcc_sub)
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hcutwt_cont
  -- a.e. strong measurability
  have haesm0 : MeasureTheory.AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ * (X z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aesm_thetaIntegral_Ioi hcont measurableSet_Ioo (fun θ hθ =>
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2)) (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    (hcutwt_cont.aestronglyMeasurable measurableSet_Icc).mul
      (haesm0.mono_measure (MeasureTheory.Measure.restrict_mono hIcc_sub le_rfl))
  -- the inner `θ`-integral is uniformly bounded on the radial support
  have hinner_bound : ∀ z ∈ Set.Icc a b,
      ‖∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2‖
        ≤ M₂ * (MeasureTheory.volume.real (Set.Ioo 0 (Real.pi / 2))) := by
    intro z hz
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const ?_ (fun θ hθ => ?_)
    · exact lt_of_le_of_lt (MeasureTheory.measure_mono Set.Ioo_subset_Icc_self)
        isCompact_Icc.measure_lt_top
    · by_cases h : θ ∈ Set.Icc c c'
      · exact hM₂ (z, θ) ⟨hz, h⟩
      · have h' : θ ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) := by rwa [hc, hc'] at h
        rw [show Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ * (X z θ) ^ 2 = 0 by
          rw [hκ θ h', mul_zero, zero_mul]]
        simpa using hM₂nn
  -- the resulting bound for the full outer integrand
  have hf_bound : ∀ z ∈ Set.Icc a b,
      ‖Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
            * (X z θ) ^ 2)‖
        ≤ M₁ * (M₂ * (MeasureTheory.volume.real (Set.Ioo 0 (Real.pi / 2)))) := by
    intro z hz
    refine le_trans (le_of_eq (norm_mul (Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z)
      (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
        * (X z θ) ^ 2))) ?_
    exact mul_le_mul (hM₁ z hz) (hinner_bound z hz) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hM₁ z hz))
  -- integrability on the compact radial support
  have h1 : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2)) (Set.Icc a b) := by
    refine MeasureTheory.IntegrableOn.of_bound
      (isCompact_Icc (a := a) (b := b)).measure_lt_top haesm
      (M₁ * (M₂ * (MeasureTheory.volume.real (Set.Ioo 0 (Real.pi / 2))))) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
    exact hf_bound z hz
  -- the integrand vanishes off the radial support
  have h2 : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2)) (Set.Ioi 0 \ Set.Icc a b) := by
    refine MeasureTheory.IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ))
      MeasureTheory.integrableOn_zero (fun z hz => ?_)
      (measurableSet_Ioi.diff measurableSet_Icc)
    have hz1 : z ∉ Set.Icc a b := hz.2
    have hzero : Work.FTS.EllipticEst.cut n z = 0 := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hz1
      rcases hz1 with h | h
      · have h1 : z < 1 / ((n : ℝ) + 1) := by rwa [ha] at h
        exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt h1)
      · have h1 : 3 * ((n : ℝ) + 1) < z := by rwa [hb] at h
        exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt h1)
    rw [hzero, zero_mul, zero_mul]
  refine (h1.union h2).mono_set (fun z hz => ?_)
  by_cases h : z ∈ Set.Icc a b
  · exact Or.inl h
  · exact Or.inr ⟨hz, h⟩

/-! ## The target -/

theorem outerIntegrable (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ)
    (hu : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.psiD δ θ
            * (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2)) (Set.Ioi 0)
    ∧ MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.psiD δ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)) (Set.Ioi 0)
    ∧ MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.psiD δ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ
                - (1 + Work.Spaces.eta) * (Work.FTS.EllipticEst.AeColl.Uz u z θ)
                  * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2)) (Set.Ioi 0)
    ∧ MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
            * (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2)) (Set.Ioi 0) := by
  have hsig : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ContinuousOn.comp oi_continuousOn_sigθ
      (ContinuousOn.mono (continuous_snd.continuousOn) (Set.subset_univ _))
      (fun p hp => hp.2)
  have hUz : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_Uz_quad hu
  have hVz : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_Vz_quad hu
  have hpsi : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.psiD δ p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (((Work.FTS.EllipticEst.AeColl.psiD_contDiff δ).continuous.comp
      continuous_snd).continuousOn).mono (Set.subset_univ _)
  have hd2 : Continuous (deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ))) := by
    have h1' : ContDiff ℝ 1 (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) := by
      simpa only [Nat.reduceAdd] using (Work.FTS.EllipticEst.AeColl.psiD_contDiff δ).deriv'
    exact h1'.continuous_deriv_one
  have hd2c : ContinuousOn (fun p : ℝ × ℝ =>
      deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hd2.comp continuous_snd).continuousOn).mono (Set.subset_univ _)
  have hmixed : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2
      - (1 + Work.Spaces.eta) * (Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2) * Real.cos (2 * p.2)
      * (Real.sin (2 * p.2)) ^ (-(1 : ℝ))) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hcos : ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn).mono
        (Set.subset_univ _)
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mono
        (Set.subset_univ _)
    have hsinpow : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(1 : ℝ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hsin.rpow_const (fun p hp => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hp.2.1]) (by linarith [hp.2.2]))))
    exact hVz.sub (((hUz.const_mul (1 + Work.Spaces.eta)).mul hcos).mul hsinpow)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact oi_shape n δ hδ hδ2 (Work.FTS.EllipticEst.AeColl.psiD δ)
      (fun z θ => Work.FTS.EllipticEst.AeColl.Uz u z θ)
      (fun θ hθ => Work.FTS.EllipticEst.AeColl.psiD_eq_zero_of_notMem δ θ hθ)
      ((hsig.mul hpsi).mul (hUz.pow 2))
  · exact oi_shape n δ hδ hδ2 (Work.FTS.EllipticEst.AeColl.psiD δ)
      (fun z θ => Work.FTS.EllipticEst.AeColl.Vz u z θ)
      (fun θ hθ => Work.FTS.EllipticEst.AeColl.psiD_eq_zero_of_notMem δ θ hθ)
      ((hsig.mul hpsi).mul (hVz.pow 2))
  · exact oi_shape n δ hδ hδ2 (Work.FTS.EllipticEst.AeColl.psiD δ)
      (fun z θ => Work.FTS.EllipticEst.AeColl.Vz u z θ
        - (1 + Work.Spaces.eta) * (Work.FTS.EllipticEst.AeColl.Uz u z θ) * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 : ℝ)))
      (fun θ hθ => Work.FTS.EllipticEst.AeColl.psiD_eq_zero_of_notMem δ θ hθ)
      ((hsig.mul hpsi).mul (hmixed.pow 2))
  · exact oi_shape n δ hδ hδ2 (deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)))
      (fun z θ => Work.FTS.EllipticEst.AeColl.Uz u z θ)
      (fun θ hθ => oi_psiD2_eq_zero_of_notMem δ θ hθ)
      ((hsig.mul hd2c).mul (hUz.pow 2))

end Work.FTS.EllipticEst.Deleg.mixedTrunc
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.sliceCollarLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg.mixedTrunc

set_option linter.unusedVariables false

/-- **The collar bound on a single `θ`-slice.**

`CollarBound Cw` is a *schema*: it bounds the `ψ_δ''`-moment of any `f : ℝ → ℝ` of class `C¹` on
`(0,π/2)` whose endpoint rates are controlled by the partial `σ`-energies of `deriv f`.  This
lemma is the instance of that schema at the slice `f = Uz u z = z ∂_z u(z,·)`, whose derivative is
the mixed slot `Vz u z = z ∂_z∂_θ u(z,·)` (`hder`): the `deriv f`-integrability and the two rate
hypotheses are transported across the pointwise identity `deriv (Uz u z) = Vz u z` on
`(0,π/2)`, which holds on every set on which the quantities occur (the collar intervals
`(0,δ)` and `(π/2-δ,π/2)` both lie inside `(0,π/2)` because `4δ ≤ π/2`).

This is the per-slice input of `Work.FTS.EllipticEst.Deleg.mixedTruncPairLe`. -/
theorem sliceCollarLe (Cw : ℝ) (hC : Work.FTS.EllipticEst.Deleg.CollarBound Cw)
    (u : ℝ → ℝ → ℝ) (K z δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2)
    (hz : 0 < z)
    (hsmooth : ContDiffOn ℝ 1 (fun θ => Work.FTS.EllipticEst.AeColl.Uz u z θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioo 0 (Real.pi / 2)))
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ
        = Work.FTS.EllipticEst.AeColl.Vz u z θ)
    (hr1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.AeColl.Vz u z t) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ t))
    (hr2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.AeColl.Vz u z t) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ t)) :
    |∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
        * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
        * (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2|
      ≤ Cw * K * ((∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
          + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
              Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)) := by
  -- the two angular weights are the same function
  have hsig : ∀ θ : ℝ, Work.FTS.EllipticEst.AngSecond.sig θ
      = Work.FTS.EllipticEst.AeColl.sigθ θ := fun θ => rfl
  -- `deriv (Uz u z) = Vz u z` on the whole open angular interval (`hder`): transport the three
  -- `deriv f`-hypotheses of `CollarBound`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hint.congr_fun (fun θ hθ => by rw [hder θ hθ, hsig θ]) measurableSet_Ioo
  have hr1' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ((fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2
        ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 θ, (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t) := by
    intro θ hθ
    have hcongr : (∫ t in Set.Ioo 0 θ,
          (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t)
        = ∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.AeColl.Vz u z t) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ t :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => by
        rw [hder t ⟨ht.1, lt_trans ht.2 hθ.2⟩, hsig t])
    rw [hcongr]
    exact hr1 θ hθ
  have hr2' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ((fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t) := by
    intro θ hθ
    have hcongr : (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t)
        = ∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.AeColl.Vz u z t) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ t :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => by
        rw [hder t ⟨lt_trans hθ.1 ht.1, ht.2⟩, hsig t])
    rw [hcongr]
    exact hr2 θ hθ
  -- apply the schema to the slice
  have h := hC K hK δ hδ hδ2 (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ')
    hsmooth hint' hr1' hr2'
  -- the two collar terms: the collar intervals sit inside `(0,π/2)`, so `deriv (Uz u z) = Vz u z`
  have hδlt : δ < Real.pi / 2 := by linarith [hδ2, hδ]
  have hcol1 : (∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AngSecond.sig θ
        * (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2)
      = ∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by
      rw [hder θ ⟨hθ.1, lt_trans hθ.2 hδlt⟩, hsig θ])
  have hcol2 : (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig θ
        * (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2)
      = ∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
          Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by
      rw [hder θ ⟨by linarith [hθ.1, hδlt], hθ.2⟩, hsig θ])
  rw [hcol1, hcol2] at h
  exact h

end Work.FTS.EllipticEst.Deleg.mixedTrunc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.EllTwoAsm.LightSliceRate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.EllTwoAsm

open Filter




end Work.FTS.EllipticEst.EllTwoAsm
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.Step3PsiBar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.Honest

set_option autoImplicit false


open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Local abbreviation for the angular weight `σ θ = sin(2θ)^{-η}`
(`Work.FTS.EllipticEst.AngSecond.sig`). -/
local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- **The `z`-assembly.**  If the slicewise estimate
`∫ sin²θ (∂_θ(Ψ/cos θ))² σ ≤ ∫ (∂_θθΨ)² σ + 2 ∫ Ψ² σ` holds at every `z > 0`, then the
honest `HkSq`-bound holds with constant `2`. -/
theorem step3PsiBar_of_slice_le (Ψ : ℝ → ℝ → ℝ)
    (hmemΨ : Work.Spaces.HkMem 0 0 Ψ)
    (hmemB : Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ))
    (hmemG : Work.Spaces.HkMem 0 0 (fun z θ => Real.sin θ
      * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
    (hsl : ∀ z : ℝ, 0 < z →
      (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
          * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ)
        ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) :
    Real.sqrt (Work.Spaces.HkSq 0 0 (fun z θ => Real.sin θ
        * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ 2 * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) := by
  set G : ℝ → ℝ → ℝ := fun z θ => Real.sin θ
    * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ with hG
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hB
  have hmemG' : Work.Spaces.HkMem 0 0 G := hmemG
  have hmemB' : Work.Spaces.HkMem 0 0 B := hmemB
  -- the pointwise (in `z`) inequality, weighted by `w²`
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
        ≤ (Work.Spaces.w z) ^ 2 * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) := by
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h | h
    · subst h
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      simp [hw0]
    · have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
          ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := by
        have hG2 : ∀ θ : ℝ, (G z θ) ^ 2 * sg θ = (Real.sin θ) ^ 2
            * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ := by
          intro θ; rw [hG]; ring
        have hB2 : ∀ θ : ℝ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ
            = (B z θ) ^ 2 * sg θ := by
          intro θ; rw [hB]
        calc (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)
            = (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
                * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ) :=
              MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hG2 θ)
          _ ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
                + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := hsl z h
          _ = (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
                + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ) := by
              rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
                    (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sg θ)
                  = ∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ from
                MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hB2 θ)]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- integrability of the three `z`-integrands
  have hintG : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemG'.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemG' hz
  have hintB : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemB'.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemB' hz
  have hintP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    refine hmemΨ.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact hkIntegrand_zero_integral_eq hmemΨ hz
  have hintR : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) Work.Spaces.Iz := by
    refine (hintB.add (hintP.const_mul 2)).congr_fun (fun z _ => ?_) measurableSet_Ici
    simp only [Pi.add_apply]
    ring
  have hmono : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ))
      ≤ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) :=
    MeasureTheory.setIntegral_mono_on hintG hintR measurableSet_Ici hpt
  have eL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), (G z θ) ^ 2 * sg θ))
      = Work.Spaces.HkSq 0 0 G := (hkSq_zero_eq_sliceW hmemG').symm
  have eR : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
      = Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ := by
    have hsplit : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
        = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ))
          + 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)) := by
      rw [show (fun z => (Work.Spaces.w z) ^ 2
            * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
              + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ)))
          = (fun z => (Work.Spaces.w z) ^ 2
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (B z θ) ^ 2 * sg θ)
            + 2 * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ) ^ 2 * sg θ))) from by
        funext z; ring]
      rw [MeasureTheory.integral_add hintB (hintP.const_mul 2),
        MeasureTheory.integral_const_mul]
    rw [hsplit, hkSq_zero_eq_sliceW hmemB', hkSq_zero_eq_sliceW hmemΨ]
  have hmain : Work.Spaces.HkSq 0 0 G ≤ Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ := by
    rw [← eL, ← eR]
    exact hmono
  have hBnn : 0 ≤ Work.Spaces.HkSq 0 0 B := HkSq_zero_nonneg 0 B
  have hPnn : 0 ≤ Work.Spaces.HkSq 0 0 Ψ := HkSq_zero_nonneg 0 Ψ
  have h2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sqrt_two_lt_three_halves
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (Work.Spaces.HkSq 0 0 Ψ))
  calc Real.sqrt (Work.Spaces.HkSq 0 0 G)
      ≤ Real.sqrt (Work.Spaces.HkSq 0 0 B + 2 * Work.Spaces.HkSq 0 0 Ψ) :=
        Real.sqrt_le_sqrt hmain
    _ ≤ Real.sqrt (Work.Spaces.HkSq 0 0 B) + Real.sqrt (2 * Work.Spaces.HkSq 0 0 Ψ) :=
        sqrt_add_le_sqrt_add_sqrt hBnn (by positivity)
    _ = Real.sqrt (Work.Spaces.HkSq 0 0 B)
          + Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq 0 0 Ψ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ) + Real.sqrt (Work.Spaces.HkSq 0 0 B)) := by
        linarith [Real.sqrt_nonneg (Work.Spaces.HkSq 0 0 B)]

/-- **The `I₄`/Ψ̄-bound of Step 2 of `prop:H2`.**  Under the honest slice hypotheses, the
`σ`-weighted `L²`-norm of `sin θ · ∂_θ(Ψ/cos θ)` is controlled by the norms of `Ψ` and of
`∂_θθΨ` (the positivity `I_{4,2}` of Elgindi, Annals 194 (2021), tex 890--905).

Route hint: with `ψ = Ψ/cos θ`, `s = sin(2θ)`, `σ = s^{-η}`, the two integrations by parts of
`Work.FTS.EllipticEst.TanTheta.slice_ident` (`TanTheta/slice_ident.lean`, proved; it needs `u`
of class `C²` on a neighbourhood of `[0,π/2]` with `u(π/2) = 0`) give the slicewise identity
`∫ ((1-η)/2·cos 2θ + 2 sin²θ)(ψ')² σ = -∫ sinθ ψ' Ψ'' σ + ((1-η)/2)∫ cos 2θ ψ² σ`.
Its coefficient is `(1-η)/2 + (1+η)sin²θ ≥ (1+η)sin²θ`, so Cauchy--Schwarz in `θ` and Young in
the two slice quantities `y = (∫ sin²θ ψ'² σ)^{1/2}` and `x = (∫(Ψ'')² σ)^{1/2}` give
`y² ≤ C (y·x + ∫ |cos 2θ| ψ² σ)`; multiplying by `w z ^ 2` and integrating in `z` gives the
statement once `∫|cos 2θ|ψ²σ` is controlled (in the strong class this is `I4_psi_bounds`/
`hardy`-type; here it must come from `HkMem (∂_θθΨ)` and `HkMem Ψ`, e.g. via a weighted Agmon
inequality on the slices — note `∫cos2θ ψ² σ` is very negative near `π/2`, not bounded by
`4∫Ψ²σ`).

The honest class (no `SmoothNbhd`) is what makes this non-trivial: the boundary terms of the
two integrations by parts and the integrability of `sinθ cosθ ψ ψ' σ`, `sinθ cosθ ψ' ψ'' σ`
must be recovered from the three `HkMem` hypotheses (a `θ`-truncation `Ψ·χ_ε` argument in
which `slice_ident` applies verbatim, or weighted one-dimensional Hardy/Agmon inequalities on
the slices).  The hypothesis `HkMem (sinθ · ψ')` is not needed for the *truth* of the estimate
but it removes the degenerate case in which a slice of `sinθ ψ'` fails to be integrable, and
is available to the caller. -/
theorem step3PsiBar : ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    Work.Spaces.HkMem 0 0 Ψ →
    Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 Ψ) →
    Work.Spaces.HkMem 0 0
      (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) →
    Real.sqrt (Work.Spaces.HkSq 0 0
        (fun z θ => Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ))
      ≤ C * (Real.sqrt (Work.Spaces.HkSq 0 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 Ψ))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro Ψ hsm h0 h1 hmemΨ hmemB hmemG
  refine step3PsiBar_of_slice_le Ψ hmemΨ hmemB hmemG ?_
  intro z hz
  -- the slice hypotheses
  have hu : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice_of_hsm hsm hz 2
  have hB : IntegrableOn (fun θ => (Ψ z θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (integrableOn_sq_mul_sig_of_hkMem hmemΨ hz).mono_set Set.Ioo_subset_Icc_self
  have hX : IntegrableOn (fun θ => (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((integrableOn_sq_mul_sig_of_hkMem hmemB hz).mono_set
      Set.Ioo_subset_Icc_self).congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show Work.Spaces.pthIter 2 Ψ z θ ^ 2 * sg θ
      = deriv (deriv (fun θ' => Ψ z θ')) θ ^ 2 * sg θ
    rw [pthIter_two_apply]
  have hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine ((integrableOn_sq_mul_sig_of_hkMem hmemG hz).mono_set
      Set.Ioo_subset_Icc_self).congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sg θ
      = (Real.sin θ) ^ 2 * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * sg θ
    rw [pth_div_apply]
    ring
  obtain ⟨hA, hA'⟩ := slice_psi_mem (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY
  obtain ⟨hv1, hv2, hv3, hv4⟩ :=
    psi_boundary_vanish (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY hA hA'
  have hident := slice_ident_honest (fun θ => Ψ z θ) hu (h0 z) (h1 z) hB hX hY hA hA'
    hv1 hv2 hv3 hv4
  have hpth : ∀ θ : ℝ, Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
      = deriv (fun θ' => Ψ z θ' / Real.cos θ') θ := fun θ => pth_div_apply Ψ z θ
  have hpth2 : ∀ θ : ℝ, Work.Spaces.pthIter 2 Ψ z θ
      = deriv (deriv (fun θ' => Ψ z θ')) θ := fun θ => pthIter_two_apply Ψ z θ
  simpa only [hpth, hpth2] using
    slice_sq_le_of_ident (fun θ => Ψ z θ) hu hA hA' hB hX hY hident


end Work.FTS.EllipticEst.H2W.AngBW.S3
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakAux.I1ZibpOpenAbs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.WeakAux

open MeasureTheory Set Filter
open scoped Real Topology ContDiff

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

abbrev Qd0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

abbrev muP : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## The `k = 0` integrand is a single weighted square -/

theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem HkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ := by
  rw [HkIntegrand_zero_eq]
  exact Work.FTS.EllipticEst.AngSecond.sq_mul_W g hθ

theorem w2_zero : Work.FTS.EllipticEst.AngSecond.w2 0 = 0 := by
  simp [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]

theorem sig_rpow_eq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := by
  have h := Work.FTS.EllipticEst.AngSecond.sq_mul_W (fun _ _ : ℝ => (1 : ℝ))
    (z := z) (θ := θ) hθ
  simpa using h

/-! ## The pointwise AM–GM bound -/

theorem abs_mul_le_Hk_sum (α : ℝ) (f h : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ|
      ≤ (Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2) := by
  have hWs : (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ :=
    sig_rpow_eq z θ hθ
  have hL : |f z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ|
      = |f z θ| * |h z θ| * (Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z),
      abs_of_nonneg (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)]
    ring
  have hR : (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        + (h z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (f z θ ^ 2 + h z θ ^ 2)
        * (Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [mul_pow, mul_pow, hWs]; ring
  rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, hL, hR]
  have hAM : 2 * (|f z θ| * |h z θ|) ≤ f z θ ^ 2 + h z θ ^ 2 := by
    nlinarith [sq_nonneg (|f z θ| - |h z θ|), sq_abs (f z θ), sq_abs (h z θ)]
  have hW : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z
      * Work.FTS.EllipticEst.AngSecond.sig θ :=
    mul_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
      (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
  have := mul_le_mul_of_nonneg_right hAM hW
  linarith

/-! ## Joint integrability of a mixed product on the quadrant -/

theorem prod_integrable_mul {α : ℝ} {f h : ℝ → ℝ → ℝ}
    (hfc : ContinuousOn (Function.uncurry f) Qd0)
    (hhc : ContinuousOn (Function.uncurry h) Qd0)
    (hf : Work.Spaces.HkMem α 0 f) (hh : Work.Spaces.HkMem α 0 h) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => f p.1 p.2 * h p.1 p.2
        * Work.FTS.EllipticEst.AngSecond.w2 p.1 * Work.FTS.EllipticEst.AngSecond.sig p.2)
      muP := by
  let F : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * h p.1 p.2
    * Work.FTS.EllipticEst.AngSecond.w2 p.1 * Work.FTS.EllipticEst.AngSecond.sig p.2
  show MeasureTheory.Integrable F muP
  have hcont : ContinuousOn F Qd0 := by
    show ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * h p.1 p.2
      * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2) Qd0
    exact ((hfc.mul hhc).mul Work.FTS.EllipticEst.AngSecond.continuousOn_w2_Qd).mul
      Work.FTS.EllipticEst.AngSecond.continuousOn_sig_Qd
  have haesm : AEStronglyMeasurable F muP := Work.Spaces.aesm_of_continuousOn_Qd F hcont
  rw [MeasureTheory.integrable_prod_iff haesm]
  constructor
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ _ => ?_) measurableSet_Icc
      show (0 : ℝ) = F (0, θ)
      simp [F, w2_zero]
    · have hκm : Measurable (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) :=
        Work.FTS.EllipticEst.AngSecond.measurable_sig.const_mul _
      have hκnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
        fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
          (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
      have hf2 : MeasureTheory.IntegrableOn (fun θ => f z θ * f z θ
          * (Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
        (hf.1 z hz).congr (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          show Work.Spaces.HkIntegrand α 0 f z θ = f z θ * f z θ
            * (Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          rw [HkIntegrand_zero_eq' α f hθ]; ring))
      have hh2 : MeasureTheory.IntegrableOn (fun θ => h z θ * h z θ
          * (Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
        (hh.1 z hz).congr (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          show Work.Spaces.HkIntegrand α 0 h z θ = h z θ * h z θ
            * (Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          rw [HkIntegrand_zero_eq' α h hθ]; ring))
      refine (Work.AngSecond.integrableOn_mul_of_sq_aux (s := Work.Spaces.Iθ)
        (F := fun θ => f z θ) (G := fun θ => h z θ)
        (κ := fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        measurableSet_Icc ?_ ?_ hκm hκnn hf2 hh2).congr (Eventually.of_forall (fun θ => ?_))
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hfc hzpos
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry h) hhc hzpos
      · show f z θ * h z θ * (Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) = F (z, θ)
        simp only [F]; ring
  · have haesm2 : AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, ‖F (z, θ)‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      haesm.norm.integral_prod_right'
    refine MeasureTheory.Integrable.mono' (((hf.2.add hh.2).const_mul (1 / 2))) haesm2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hFnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, ‖F (z, θ)‖ :=
      integral_nonneg (fun θ => norm_nonneg (F (z, θ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    simp only [Real.norm_eq_abs]
    change (∫ θ in Work.Spaces.Iθ, |F (z, θ)|) ≤ (1 / 2) *
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ))
    have h2 : (∫ θ in Work.Spaces.Iθ, |F (z, θ)|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 0 f z θ
            + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2) := by
      refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun θ => abs_nonneg _))
        (((hf.1 z hz).add (hh.1 z hz)).mul_const (1 / 2)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      show |F (z, θ)| ≤ (Work.Spaces.HkIntegrand α 0 f z θ
        + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2)
      simp only [F]
      exact abs_mul_le_Hk_sum α f h hθ
    have h3 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 0 f z θ
            + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2))
        = ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ)) * (1 / 2) := by
      rw [MeasureTheory.integral_mul_const,
        MeasureTheory.integral_add (hf.1 z hz) (hh.1 z hz)]
    calc (∫ θ in Work.Spaces.Iθ, |F (z, θ)|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 0 f z θ
            + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2) := h2
      _ = ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ)) * (1 / 2) := h3
      _ = _ := by ring

/-! ## Mixed honesty from the diagonal honesties, in the open class -/

theorem IPMem_of_diag_open {g h : ℝ → ℝ → ℝ}
    (hgc : ContinuousOn (Function.uncurry g) Qd0)
    (hhc : ContinuousOn (Function.uncurry h) Qd0)
    (hg : Work.FTS.EllipticEst.AngSecond.IPMem g g)
    (hh : Work.FTS.EllipticEst.AngSecond.IPMem h h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h := by
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ _ => ?_) measurableSet_Icc
      show (0 : ℝ) = g 0 θ * h 0 θ * Work.FTS.EllipticEst.AngSecond.w2 0
        * Work.FTS.EllipticEst.AngSecond.sig θ
      simp [w2_zero]
    · have hκm : Measurable (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) :=
        Work.FTS.EllipticEst.AngSecond.measurable_sig.const_mul _
      have hκnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
        fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
          (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
      have hg2 : MeasureTheory.IntegrableOn (fun θ => g z θ * g z θ
          * (Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
        (hg.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
      have hh2 : MeasureTheory.IntegrableOn (fun θ => h z θ * h z θ
          * (Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
        (hh.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
      refine (Work.AngSecond.integrableOn_mul_of_sq_aux (s := Work.Spaces.Iθ)
        (F := fun θ => g z θ) (G := fun θ => h z θ)
        (κ := fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        measurableSet_Icc ?_ ?_ hκm hκnn hg2 hh2).congr (Eventually.of_forall (fun θ => ?_))
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hgc hzpos
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry h) hhc hzpos
      · show g z θ * h z θ * (Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
          = (fun θ' => g z θ' * h z θ' * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ') θ
        ring
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2
        * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2) Qd0 :=
      (((hgc.mul hhc)).mul Work.FTS.EllipticEst.AngSecond.continuousOn_w2_Qd).mul
        Work.FTS.EllipticEst.AngSecond.continuousOn_sig_Qd
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
          * Work.FTS.EllipticEst.AngSecond.sig p.2) muP :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    refine MeasureTheory.Integrable.mono' (((hg.2.add hh.2).const_mul (1 / 2)))
      hjoint.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    change ‖∫ θ in Work.Spaces.Iθ, g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ‖ ≤ (1 / 2) *
      ((∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        + (∫ θ in Work.Spaces.Iθ, h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ))
    have h2 : |∫ θ in Work.Spaces.Iθ, g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ|
        ≤ ∫ θ in Work.Spaces.Iθ, (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ
            + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2) := by
      refine le_trans abs_integral_le_integral_abs ?_
      refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun θ => abs_nonneg _))
        (((hg.1 z hz).add (hh.1 z hz)).mul_const (1 / 2)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      show |g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ|
          ≤ (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ
              + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2)
      have hw2 : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z :=
        Work.FTS.EllipticEst.AngSecond.w2_nonneg z
      have hs : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
        Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
      have hAM : 2 * (|g z θ| * |h z θ|) ≤ g z θ * g z θ + h z θ * h z θ := by
        nlinarith [sq_nonneg (|g z θ| - |h z θ|), sq_abs (g z θ), sq_abs (h z θ)]
      have hstep : |g z θ| * |h z θ| ≤ (g z θ * g z θ + h z θ * h z θ) / 2 := by linarith
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw2, abs_of_nonneg hs]
      have hkey := mul_le_mul_of_nonneg_right hstep (mul_nonneg hw2 hs)
      calc |g z θ| * |h z θ| * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ
          = |g z θ| * |h z θ| * (Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
        _ ≤ ((g z θ * g z θ + h z θ * h z θ) / 2)
              * (Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) := hkey
        _ = (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ
              + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2) := by ring
    have h3 : (∫ θ in Work.Spaces.Iθ, (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ
            + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2))
        = ((∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)
            + (∫ θ in Work.Spaces.Iθ, h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)) * (1 / 2) := by
      rw [MeasureTheory.integral_mul_const,
        MeasureTheory.integral_add (hg.1 z hz) (hh.1 z hz)]
    rw [Real.norm_eq_abs]
    calc |∫ θ in Work.Spaces.Iθ, g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ|
        ≤ ∫ θ in Work.Spaces.Iθ, (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ
            + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2) := h2
      _ = ((∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)
            + (∫ θ in Work.Spaces.Iθ, h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)) * (1 / 2) := h3
      _ = _ := by ring

/-! ## Smoothness helpers -/

theorem smoothOpen_fst : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
  contDiff_fst.contDiffOn

theorem continuousOn_uncurry_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen F) : ContinuousOn (Function.uncurry F) Qd0 :=
  h.continuousOn

theorem smoothOpen_sq_mul_pzIter {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  (smoothOpen_fst.pow 2).mul (h.pzIter 2)

theorem smoothOpen_fst_mul_pz {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
  smoothOpen_fst.mul h.pz

theorem smoothOpen_pthIter_two {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := by
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h.pth.pth

theorem smoothOpen_fst_mul_pz_pthIter_two {Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
  smoothOpen_fst.mul (smoothOpen_pthIter_two h).pz

/-! ## The angular weight at the two angular endpoints -/

theorem sig_zero : Work.FTS.EllipticEst.AngSecond.sig 0 = 0 := by
  rw [Work.FTS.EllipticEst.AngSecond.sig]
  simp only [mul_zero, Real.sin_zero]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

theorem sig_pi_half : Work.FTS.EllipticEst.AngSecond.sig (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.AngSecond.sig]
  have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [h2, Real.sin_pi]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
/-! ## A triangle-inequality helper -/

theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa using abs_add_le a (-b)

theorem continuousOn_fst_Qd0 : ContinuousOn (fun p : ℝ × ℝ => p.1) Qd0 :=
  continuous_fst.continuousOn

theorem continuousOn_sig_Qd0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2) Qd0 :=
  Work.FTS.EllipticEst.AngSecond.continuousOn_sig_Qd

theorem continuousOn_w2_Qd0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1) Qd0 :=
  Work.FTS.EllipticEst.AngSecond.continuousOn_w2_Qd

/-! ## The pointwise bound on `σ · nice` -/

theorem abs_sig_nice_le (α K : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hKnn : 0 ≤ K)
    (hK : ∀ z : ℝ, |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.EllipticEst.AngSecond.sig θ * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ|
      ≤ 12 * (1 + K) * (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ) := by
  have hGs : Work.Spaces.Dz Ψ = Work.FTS.EllipticEst.AngSecond.G Ψ := rfl
  have hPs : Work.Spaces.pthIter 2 Ψ = Work.FTS.EllipticEst.AngSecond.Phi Ψ := rfl
  have hHs : (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
      = Work.FTS.EllipticEst.AngSecond.H Ψ := rfl
  rw [hHs, hPs, hGs]
  have hsb : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
    Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  have hwb : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z :=
    Work.FTS.EllipticEst.AngSecond.w2_nonneg z
  have hc0 : 0 ≤ Work.FTS.EllipticEst.cut n z := Work.FTS.EllipticEst.cut_nonneg n z
  have hc1 : |Work.FTS.EllipticEst.cut n z| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, Work.FTS.EllipticEst.cut_le_one n z⟩
  have h1z : 0 < 1 + z := by linarith
  have hABnn : 0 ≤ |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
      * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
      + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
        * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ| :=
    add_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hBr : |2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
        + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
        - 4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
          * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z)|
      ≤ 6 * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|) := by
    have h1 : |2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
          + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ|
        ≤ 2 * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)
          + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have h3 : |4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z)|
        ≤ 4 * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|) := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos h1z,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      rw [div_le_iff₀ h1z]
      have h0 : (0 : ℝ) ≤ 4 * |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
          * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ| * z :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _)) hz
      nlinarith [h0]
    refine ((abs_sub_le_add
      (2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
        + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ)
      (4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z))).trans
        (add_le_add h1 h3)).trans ?_
    nlinarith [mul_nonneg (abs_nonneg (Work.FTS.EllipticEst.AngSecond.G Ψ z θ))
      (abs_nonneg (Work.FTS.EllipticEst.AngSecond.H Ψ z θ))]
  have hnice : |Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ|
      ≤ 12 * (1 + K) * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) := by
    have hU : |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z
          * (2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
            + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
            - 4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z))|
        ≤ 6 * (Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
              + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hc0]
      have hb := mul_le_mul hc1 hBr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hb2 := mul_le_mul_of_nonneg_right hb hwb
      calc Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z
            * |2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
              + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
              - 4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z)|
          = (|Work.FTS.EllipticEst.cut n z|
              * |2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                  * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
                + Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                  * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
                - 4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                  * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z)|)
              * Work.FTS.EllipticEst.AngSecond.w2 z := by
            rw [abs_of_nonneg hc0]; ring
        _ ≤ (1 * (6 * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)))
              * Work.FTS.EllipticEst.AngSecond.w2 z := hb2
        _ = 6 * (Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
              + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) := by ring
    have hV : |Work.FTS.EllipticEst.AngSecond.w2 z
          * (Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ)
          * (z * deriv (Work.FTS.EllipticEst.cut n) z)|
        ≤ K * (Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hwb]
      have hb := mul_le_mul_of_nonneg_left (hK z)
        (mul_nonneg hwb (mul_nonneg (abs_nonneg (Work.FTS.EllipticEst.AngSecond.G Ψ z θ))
          (abs_nonneg (Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ))))
      calc Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)
            * |z * deriv (Work.FTS.EllipticEst.cut n) z|
          ≤ (Work.FTS.EllipticEst.AngSecond.w2 z
              * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)) * K := hb
        _ = K * (Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)) := by ring
    rw [Work.FTS.EllipticEst.AngSecond.nice]
    refine ((abs_add_le _ _).trans (add_le_add hU hV)).trans ?_
    have hYX : Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)
        ≤ Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|) :=
      mul_le_mul_of_nonneg_left (by
        have h1 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.G Ψ z θ)
        have h2 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ)
        have h3 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.H Ψ z θ)
        nlinarith) hwb
    have hYnn : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|) :=
      mul_nonneg hwb (by
        have h1 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.G Ψ z θ)
        have h2 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ)
        have h3 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.H Ψ z θ)
        nlinarith)
    have hKY : K * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|))
        ≤ K * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) :=
      mul_le_mul_of_nonneg_left hYX hKnn
    have hlast : (6 + K) * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|))
        ≤ 12 * (1 + K) * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) :=
      mul_le_mul_of_nonneg_right (by linarith) hYnn
    linarith [hKY, hlast]
  have hsum : |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
          + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
      ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.G Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.Phi Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.H Ψ) z θ := by
    have h1 := abs_mul_le_Hk_sum α (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.Phi Ψ) (z := z) hθ
    have h2 := abs_mul_le_Hk_sum α (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.H Ψ) (z := z) hθ
    have h3 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.FTS.EllipticEst.AngSecond.G Ψ) z θ
    have h4 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.FTS.EllipticEst.AngSecond.Phi Ψ) z θ
    have h5 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.FTS.EllipticEst.AngSecond.H Ψ) z θ
    linarith
  have he1 : |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
      = |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
        * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hsb]
  have he2 : |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
      = |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
        * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hsb]
  have hcoef : (0 : ℝ) ≤ 12 * (1 + K) := by linarith
  calc |Work.FTS.EllipticEst.AngSecond.sig θ * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ|
      = Work.FTS.EllipticEst.AngSecond.sig θ
          * |Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ| := by
        rw [abs_mul, abs_of_nonneg hsb]
    _ ≤ Work.FTS.EllipticEst.AngSecond.sig θ
          * (12 * (1 + K) * (Work.FTS.EllipticEst.AngSecond.w2 z
              * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                  * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
                + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                  * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|))) :=
        mul_le_mul_of_nonneg_left hnice hsb
    _ = 12 * (1 + K) * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
          + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|) := by
        rw [he1, he2]; ring
    _ ≤ 12 * (1 + K) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.G Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.Phi Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.H Ψ) z θ) :=
        mul_le_mul_of_nonneg_left hsum hcoef

/-! ## Joint integrability of `cut n · Akern` and of `σ · nice` -/

theorem prod_integrable_cut_akern (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1
        * Work.FTS.EllipticEst.AngSecond.Akern Ψ p.1 p.2) muP := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hbase := prod_integrable_mul (α := α)
    (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    (h := Work.Spaces.pthIter 2 Ψ)
    (continuousOn_uncurry_of_smoothOpen (smoothOpen_sq_mul_pzIter hΨ))
    (continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ)) hQ hΦ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1
      * Work.FTS.EllipticEst.AngSecond.Akern Ψ p.1 p.2) Qd0 := by
    have hQc : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2) Qd0 :=
      (continuousOn_fst_Qd0.pow 2).mul (continuousOn_uncurry_of_smoothOpen (hΨ.pzIter 2))
    have hΦc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2) Qd0 :=
      continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ)
    have hcut : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1) Qd0 :=
      ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn
    have hmid : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2
        * Work.Spaces.pthIter 2 Ψ p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2) Qd0 :=
      ((hQc.mul hΦc).mul continuousOn_w2_Qd0).mul continuousOn_sig_Qd0
    exact hcut.mul hmid
  refine (hbase.norm).mono' (Work.Spaces.aesm_of_continuousOn_Qd _ hcont) ?_
  filter_upwards with p
  have hc1 : |Work.FTS.EllipticEst.cut n p.1| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Work.FTS.EllipticEst.cut_nonneg n p.1],
      Work.FTS.EllipticEst.cut_le_one n p.1⟩
  have hEq : Work.FTS.EllipticEst.cut n p.1 * Work.FTS.EllipticEst.AngSecond.Akern Ψ p.1 p.2
      = Work.FTS.EllipticEst.cut n p.1
          * ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2
            * (Work.Spaces.pthIter 2 Ψ) p.1 p.2
            * Work.FTS.EllipticEst.AngSecond.w2 p.1
            * Work.FTS.EllipticEst.AngSecond.sig p.2) := by
    simp only [Work.FTS.EllipticEst.AngSecond.Akern]
  rw [hEq, norm_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) hc1

theorem prod_integrable_sig_nice (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2
        * Work.FTS.EllipticEst.AngSecond.nice n Ψ p.1 p.2) muP := by
  obtain ⟨K, hKpos, hKb, -, -⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  have hKnn : (0 : ℝ) ≤ K := le_of_lt hKpos
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  let F : ℝ × ℝ → ℝ := fun p => Work.FTS.EllipticEst.AngSecond.sig p.2
    * Work.FTS.EllipticEst.AngSecond.nice n Ψ p.1 p.2
  show MeasureTheory.Integrable F muP
  have hcont : ContinuousOn F Qd0 := by
    have hGc : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz Ψ p.1 p.2) Qd0 :=
      continuousOn_fst_Qd0.mul (continuousOn_uncurry_of_smoothOpen hΨ.pz)
    have hPc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2) Qd0 :=
      continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ)
    have hHc : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
        Qd0 :=
      continuousOn_fst_Qd0.mul (continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ).pz)
    have hcut : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1) Qd0 :=
      ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn
    have hdcut : ContinuousOn (fun p : ℝ × ℝ => deriv (Work.FTS.EllipticEst.cut n) p.1) Qd0 :=
      ((Work.FTS.EllipticEst.AngSecond.continuous_deriv_cut n).comp continuous_fst).continuousOn
    have hone : ContinuousOn (fun p : ℝ × ℝ => (1 : ℝ) + p.1) Qd0 :=
      (continuous_const.add continuous_fst).continuousOn
    have hne : ∀ p ∈ Qd0, (1 : ℝ) + p.1 ≠ 0 := by
      rintro ⟨z, θ⟩ hzp
      have h1 : (0 : ℝ) < z := hzp.1
      linarith
    have hfrac : ContinuousOn (fun p : ℝ × ℝ => 4 * (p.1 * Work.Spaces.pz Ψ p.1 p.2)
        * (Work.Spaces.pthIter 2 Ψ p.1 p.2) / (1 + p.1)) Qd0 :=
      (((continuousOn_const (c := (4 : ℝ))).mul hGc).mul hPc).div hone hne
    have hsum : ContinuousOn (fun p : ℝ × ℝ => 2 * (p.1 * Work.Spaces.pz Ψ p.1 p.2)
          * (Work.Spaces.pthIter 2 Ψ p.1 p.2)
        + (p.1 * Work.Spaces.pz Ψ p.1 p.2)
          * (p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
        - 4 * (p.1 * Work.Spaces.pz Ψ p.1 p.2)
          * (Work.Spaces.pthIter 2 Ψ p.1 p.2) / (1 + p.1)) Qd0 :=
      (((continuousOn_const (c := (2 : ℝ))).mul hGc).mul hPc).add (hGc.mul hHc) |>.sub hfrac
    have hinner : ContinuousOn (fun p : ℝ × ℝ =>
        Work.FTS.EllipticEst.cut n p.1 * Work.FTS.EllipticEst.AngSecond.w2 p.1
          * (2 * (p.1 * Work.Spaces.pz Ψ p.1 p.2) * (Work.Spaces.pthIter 2 Ψ p.1 p.2)
            + (p.1 * Work.Spaces.pz Ψ p.1 p.2)
              * (p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
            - 4 * (p.1 * Work.Spaces.pz Ψ p.1 p.2)
              * (Work.Spaces.pthIter 2 Ψ p.1 p.2) / (1 + p.1))
        + Work.FTS.EllipticEst.AngSecond.w2 p.1
          * ((p.1 * Work.Spaces.pz Ψ p.1 p.2) * (Work.Spaces.pthIter 2 Ψ p.1 p.2))
          * (p.1 * deriv (Work.FTS.EllipticEst.cut n) p.1)) Qd0 :=
      ((hcut.mul continuousOn_w2_Qd0).mul hsum).add
        ((continuousOn_w2_Qd0.mul (hGc.mul hPc)).mul (continuousOn_fst_Qd0.mul hdcut))
    exact continuousOn_sig_Qd0.mul hinner
  have haesm : AEStronglyMeasurable F muP := Work.Spaces.aesm_of_continuousOn_Qd F hcont
  rw [MeasureTheory.integrable_prod_iff haesm]
  constructor
  · filter_upwards [Work.FTS.EllipticEst.AngSecond.ae_pos_of_Iz,
      MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hzpos hz
    have hz0 : 0 ≤ z := le_of_lt hzpos
    have hdom : MeasureTheory.IntegrableOn (fun θ => 12 * (1 + K)
        * (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ))
        Work.Spaces.Iθ :=
      ((((hG.1 z hz).add (hΦ.1 z hz)).add (hH.1 z hz))).const_mul _
    refine hdom.mono' (Work.Spaces.aesm_slice_of_continuousOn_Qd F hcont hzpos) ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have hFval : F (z, θ) = Work.FTS.EllipticEst.AngSecond.sig θ
        * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ := rfl
    rw [hFval, Real.norm_eq_abs]
    exact abs_sig_nice_le α K n Ψ hKnn (hKb n) hz0 hθ
  · have haesm2 : AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, ‖F (z, θ)‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      haesm.norm.integral_prod_right'
    have hdom2 : MeasureTheory.Integrable (fun z : ℝ => 12 * (1 + K)
        * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.const_mul (((hG.2.add hΦ.2)).add hH.2) _
    refine hdom2.mono' haesm2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : 0 ≤ z := Set.mem_Ici.mp hz
    have hFnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, ‖F (z, θ)‖ :=
      integral_nonneg (fun θ => norm_nonneg (F (z, θ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, ‖F (z, θ)‖ ≤ 12 * (1 + K)
        * (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ) := by
      intro θ hθ
      have hFval : F (z, θ) = Work.FTS.EllipticEst.AngSecond.sig θ
          * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ := rfl
      rw [hFval, Real.norm_eq_abs]
      exact abs_sig_nice_le α K n Ψ hKnn (hKb n) hz0 hθ
    have hmono : (∫ θ in Work.Spaces.Iθ, ‖F (z, θ)‖)
        ≤ ∫ θ in Work.Spaces.Iθ, 12 * (1 + K)
          * (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
            + Work.Spaces.HkIntegrand α 0
                (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun θ => norm_nonneg _))
        ((((hG.1 z hz).add (hΦ.1 z hz)).add (hH.1 z hz)).const_mul _)
        (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul]
    have h1 := MeasureTheory.integral_add ((hG.1 z hz).add (hΦ.1 z hz)) (hH.1 z hz)
    have h2 := MeasureTheory.integral_add (hG.1 z hz) (hΦ.1 z hz)
    simp only [Pi.add_apply] at h1 h2
    rw [h1, h2]
end

/-! ## The two Fubini swaps -/

theorem swap_cut_akern (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ :=
  MeasureTheory.integral_integral_swap (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ)
    (prod_integrable_cut_akern α n Ψ hsm hQ hΦ)

theorem swap_sig_nice (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ
        * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.sig θ
          * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ :=
  MeasureTheory.integral_integral_swap (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => Work.FTS.EllipticEst.AngSecond.sig θ
      * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
    (prod_integrable_sig_nice α n Ψ hsm hG hΦ hH)

/-! ## The cut-off identity in the open class -/

theorem I1_cutoff_identity_open (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
        (Work.Spaces.pthIter 2 Ψ)
      = - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.AngSecond.sig θ
            * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ := by
  calc Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
        (Work.Spaces.pthIter 2 Ψ)
      = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.Afun Ψ z :=
        Work.FTS.EllipticEst.AngSecond.IP_cut_eq n Ψ
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        rw [Work.FTS.EllipticEst.AngSecond.Afun, MeasureTheory.integral_const_mul]
    _ = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ := swap_cut_akern α n Ψ hsm hQ hΦ
    _ = ∫ θ in Work.Spaces.Iθ,
          -(∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.sig θ
              * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
        rcases eq_or_ne θ 0 with rfl | hθ0
        · have hz1 : (fun z : ℝ => Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.Akern Ψ z 0) = fun _ : ℝ => (0 : ℝ) := by
            funext z
            simp only [Work.FTS.EllipticEst.AngSecond.Akern, sig_zero, mul_zero]
          have hz2 : (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.sig 0
              * Work.FTS.EllipticEst.AngSecond.nice n Ψ z 0) = fun _ : ℝ => (0 : ℝ) := by
            funext z
            simp only [sig_zero, zero_mul]
          rw [hz1, hz2]
          simp
        · rcases eq_or_ne θ (Real.pi / 2) with rfl | hθπ
          · have hz1 : (fun z : ℝ => Work.FTS.EllipticEst.cut n z
                * Work.FTS.EllipticEst.AngSecond.Akern Ψ z (Real.pi / 2))
                = fun _ : ℝ => (0 : ℝ) := by
              funext z
              simp only [Work.FTS.EllipticEst.AngSecond.Akern, sig_pi_half, mul_zero]
            have hz2 : (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.sig (Real.pi / 2)
                * Work.FTS.EllipticEst.AngSecond.nice n Ψ z (Real.pi / 2))
                = fun _ : ℝ => (0 : ℝ) := by
              funext z
              simp only [sig_pi_half, zero_mul]
            rw [hz1, hz2]
            simp
          · have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
              ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0),
                lt_of_le_of_ne hθ.2 hθπ⟩
            rw [show (fun z : ℝ => Work.FTS.EllipticEst.cut n z
                  * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ)
                = fun z : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ
                    * (Work.Spaces.pzIter 2 Ψ z θ
                      * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ
                        * Work.FTS.EllipticEst.cut n z
                        * Work.FTS.EllipticEst.AngSecond.w2 z)) from by
              funext z
              simp only [Work.FTS.EllipticEst.AngSecond.Akern]
              ring]
            rw [MeasureTheory.integral_const_mul]
            rw [show (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.sig θ
                  * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
                = Work.FTS.EllipticEst.AngSecond.sig θ
                  * ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ from
                MeasureTheory.integral_const_mul _ _]
            rw [Work.FTS.EllipticEst.H2W.AeWAux.niceSliceIBPOpen n Ψ hsm hθIoo]
            ring
    _ = - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.AngSecond.sig θ
            * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ := by
        rw [MeasureTheory.integral_neg, (swap_sig_nice α n Ψ hsm hG hΦ hH).symm]

/-! ## The radial integration by parts of `I₁`, in the open class -/

theorem I1_ibp_identity_open (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (Work.Spaces.pthIter 2 Ψ)
      = - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (Work.FTS.EllipticEst.AngSecond.H Ψ)
        - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hGc : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.AngSecond.G Ψ)) Qd0 :=
    continuousOn_uncurry_of_smoothOpen (smoothOpen_fst_mul_pz hΨ)
  have hΦc : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.AngSecond.Phi Ψ)) Qd0 :=
    continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ)
  have hHc : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.AngSecond.H Ψ)) Qd0 :=
    continuousOn_uncurry_of_smoothOpen (smoothOpen_fst_mul_pz_pthIter_two hΨ)
  have hGm : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.G Ψ) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hG
  have hΦm : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.Phi Ψ)
      (Work.FTS.EllipticEst.AngSecond.Phi Ψ) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hΦ
  have hHm : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.H Ψ)
      (Work.FTS.EllipticEst.AngSecond.H Ψ) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hH
  have hQΦ : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ) :=
    IPMem_of_diag_open
      (continuousOn_uncurry_of_smoothOpen (smoothOpen_sq_mul_pzIter hΨ)) hΦc
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hQ) hΦm
  have hGΦ : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.Phi Ψ) :=
    IPMem_of_diag_open hGc hΦc hGm hΦm
  have hGH : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.H Ψ) :=
    IPMem_of_diag_open hGc hHc hGm hHm
  have hAfun : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngSecond.Afun Ψ)
      Work.Spaces.Iz := Work.FTS.EllipticEst.AngSecond.integrableOn_Afun Ψ hQΦ
  have hPhi1 : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngSecond.Phi1 Ψ)
      Work.Spaces.Iz := Work.FTS.EllipticEst.AngSecond.integrableOn_Phi1 Ψ hGΦ
  have hBfun : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngSecond.Bfun Ψ)
      Work.Spaces.Iz := Work.FTS.EllipticEst.AngSecond.integrableOn_Bfun Ψ hGΦ hGH
  have hkey : ∀ n : ℕ, (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = (- (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Bfun Ψ z))
        - (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
            * (z * deriv (Work.FTS.EllipticEst.cut n) z)) := by
    intro n
    have h1 := I1_cutoff_identity_open α n Ψ hsm hQ hG hΦ hH
    rw [Work.FTS.EllipticEst.AngSecond.IP_cut_eq n Ψ] at h1
    have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.AngSecond.sig θ
            * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
        = (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Bfun Ψ z)
          + (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
              * (z * deriv (Work.FTS.EllipticEst.cut n) z)) := by
      rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.AngSecond.sig θ
              * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
          = ∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.Bfun Ψ z
              + Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
                * (z * deriv (Work.FTS.EllipticEst.cut n) z)) from
          MeasureTheory.setIntegral_congr_fun measurableSet_Ici
            (fun z hz => Work.FTS.EllipticEst.AngSecond.nfun_eq n Ψ hGΦ hGH hz)]
      exact MeasureTheory.integral_add
        (Work.FTS.EllipticEst.AngSecond.integrableOn_cut_mul hBfun n)
        (Work.FTS.EllipticEst.AngSecond.integrableOn_cutDeriv_mul hPhi1 n)
    rw [h1, h2]
    ring
  have htA := Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hAfun
  have htB := Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hBfun
  have htC := Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cutDeriv_mul hPhi1
  have hseq : (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = fun n : ℕ => (- (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Bfun Ψ z))
          - (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
              * (z * deriv (Work.FTS.EllipticEst.cut n) z)) :=
    funext hkey
  rw [hseq] at htA
  have hlim : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = (- (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Bfun Ψ z)) - 0 :=
    tendsto_nhds_unique htA (htB.neg.sub htC)
  have hA : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          (Work.Spaces.pthIter 2 Ψ) := by
    rw [Work.FTS.EllipticEst.AngSecond.IP]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => by simp only [Work.FTS.EllipticEst.AngSecond.Akern])
  have hPhi1c : (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z)
      = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
    rw [show (∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z)
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Cwfun Ψ z from
        MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => by
          rw [Work.FTS.EllipticEst.AngSecond.Cwfun, Work.FTS.EllipticEst.AngSecond.Phi1,
            ← MeasureTheory.integral_const_mul]
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
            (fun θ _ => by ring))]
    rw [Work.FTS.EllipticEst.AngSecond.IP]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  have hBHc : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.BHfun Ψ z)
      = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
          (Work.FTS.EllipticEst.AngSecond.H Ψ) := by
    rw [Work.FTS.EllipticEst.AngSecond.IP]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  have hBZ : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Bfun Ψ z)
      = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (Work.FTS.EllipticEst.AngSecond.H Ψ)
        + Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
    have hsplit : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Bfun Ψ z)
        = ∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
            + Work.FTS.EllipticEst.AngSecond.BHfun Ψ z) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici
        (fun z hz => Work.FTS.EllipticEst.AngSecond.Bfun_eq Ψ hGΦ hGH hz)
    rw [hsplit, MeasureTheory.integral_add
      (Work.FTS.EllipticEst.AngSecond.integrableOn_cwPhi1 Ψ hPhi1)
      (Work.FTS.EllipticEst.AngSecond.integrableOn_BHfun Ψ hGH), hPhi1c, hBHc]
    ring
  have hgoal : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (Work.FTS.EllipticEst.AngSecond.H Ψ)
        - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
    rw [hlim, hBZ]
    ring
  rw [← hA]
  exact hgoal

theorem I1ZibpOpenAbs (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ z : ℝ, Ψ z 0 = 0) (hπ : ∀ z : ℝ, Ψ z (Real.pi / 2) = 0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (Work.Spaces.pthIter 2 Ψ)
      = - Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.Dz Ψ)
            (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        - Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.Dz Ψ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.Spaces.pthIter 2 Ψ z θ) :=
  I1_ibp_identity_open α Ψ hsm hQ hG hΦ hH

end Work.FTS.EllipticEst.H2W.WeakAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.eigenFTCPoleDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/eigenFTCPoleDefs` — the left-half companions of `Gd`, `Ki`

The file `WeakPureAux/eigenFTCAux` carries the *right-half* running quantities of the
`(Dfun, Rfun)` system of `Lzero1 u = mu * u`:

* `Gd u θ = ∫_{π/4}^{θ} |Rfun u s| · ew s ds` (the running `σ|u|`-mass) and
* `Ki θ = ∫_{π/4}^{θ} ek s ds` (the running kernel of the `Rfun` equation),

together with the running bounds `Dfun_run_bound`, `Rfun_run_bound` for `θ ∈ [π/4, π/2)`.

This file adds the two mirror definitions for the *left* half `θ ∈ (0, π/4]`,
`GdL u θ = ∫_{θ}^{π/4} |Rfun u s| · ew s ds` and `Kl θ = ∫_{θ}^{π/4} ek s ds`, and the
elementary bounds (`ew ≤ 1`, `ew = O(t³)` near `π/2`, `ew = O(θ²)` near `0`, and hence
`ew · Ki`, `ew · Kl` bounded) that turn the running bounds of the two halves into
constant-coefficient Grönwall inequalities.
-/

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section


/-- The *left-half* running kernel: `Kl θ = ∫_θ^{π/4} ek s ds`. -/
def Kl (θ : ℝ) : ℝ := ∫ s in θ..(Real.pi / 4), ek s










end

end Work.FTS.EllipticEst.H2W.WeakPureAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.sourceBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-!
# `sourceBounds`: the weighted `L¹` mass of a source with an inverse-power bound

For `u` of class `C²` on the open interval `(0, π/2)` with `Lzero1 u = g` there and

  `|g θ| ≤ C (θ^{-(R+2)} + (π/2 - θ)^{-(R+2)})`,   `R > 1`,

the weighted mass `∫ sin s cos²s |Lzero1 u s| ds` of the source over the two halves adjacent
to `π/4` obeys the *inverse-power* bounds

* `∫_θ^{π/4} sin s cos²s |Lzero1 u s| ds ≤ C (1/R + (4/π)^{R+2}(π/4)) θ^{-R}` for
  `θ ∈ (0, π/4]` (the weight `sin s cos²s ≤ s` cancels one power at `s = 0`, and the
  remaining source term `(π/2 - s)^{-(R+2)}` is bounded by `(4/π)^{R+2}` on the half);
* `∫_{π/4}^{θ} sin s cos²s |Lzero1 u s| ds ≤ C ((π²/16)(4/π)^{R+2}(π/2) + 1/(R-1))
  (π/2 - θ)^{1-R}` for `θ ∈ [π/4, π/2)` (at `s = π/2` the weight `sin s cos²s ≤ (π/2-s)²`
  cancels two powers of the second-order pole exactly, leaving the integrable
  `(π/2-s)^{-R}`; the printed constant is deliberately generous).

The four elementary interval integrals are isolated as `sinCos2_int_pow_left`,
`sinCos2_int_tsq_pow_left`, `sinCos2_int_pow_right` and `sinCos2_int_tsq_pow_right`.
-/

/-! ## The four elementary interval integrals -/





/-! ## The main bound -/


end Work.FTS.EllipticEst.H2W.WeakPureAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HonGaps.psiCutZLayerLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.HonGaps

set_option linter.unusedSimpArgs false

/-! ## Elementary facts about the weight `σ = sigS` and the interval `Iθ` -/


/-- The radial weight `w(z) = (1+z)²/z²` is measurable. -/
theorem measurable_w : Measurable Work.Spaces.w := by
  have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact ((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)

/-- `Iθ = [0, π/2]` is measurable. -/
theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-! ## The two angular layers and their measures -/









/-! ## The general layer limit

The statement below is the general form of the target: `g` is an angular integrand on `Iθ`,
nonnegative on `Iθ`, with jointly measurable uncurried form, a.e. integrable `θ`-slices and
square-weighted `z`-integral (the `χ²w²`-weighted mass of `g` on `Iθ`) integrable on `(0,∞)`. -/

/-! ## The requested lemma -/


end Work.FTS.EllipticEst.HonGaps
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I1LowerHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1LowerHonest` — the `I₁` lower bound of Step 2 of `prop:H2`, honest class

Target: `∃ C > 0, ∀ α F Ψ, Hon α F Ψ → HkMem α 0 (z ∂_z Ψ) → -C α² (A + √A √B) ≤ α² D`
where `A = IP (z∂_zΨ) (z∂_zΨ)`, `B = IP (∂_θθΨ) (∂_θθΨ)`, `D = IP (z²∂_zzΨ) (∂_θθΨ)` and
`IP g h = ∫_z ∫_θ g h w²σ` (`σ = sin(2θ)^{-η}`, `η = 99/100`).

The statement is **true**; it is (after dividing by `α² > 0`) the pure quadratic-form inequality
`D ≥ -C (A + √A √B)`, which does not involve `F` at all.  The route and the verified identities
are recorded in `NOTES_I1LowerHonest.md`; in outline, with `T = z∂_z`, `G = TΨ`, `Bf = Ψ_θθ`,
`P := ‖G_θ‖²_ρ`, `N := ∫∫ G² cos²(2θ) sin(2θ)^{-(2+η)} w²`:

* **z-IBP** (`Honest/SliceIbpZ`) : `⟨T²Ψ, Bf⟩_ρ = -⟨G, T Bf⟩_ρ + ⟨G, c·Bf⟩_ρ`, `c(z) = (3-z)/(1+z)`;
* **θ-IBP** (`Honest/SliceIbpTheta`) : `⟨G, T Bf⟩_ρ = -P + 2η(1+η)N + 2ηA`;
  hence `D = P - 2η(1+η)N - 2ηA + ⟨G,(c-1)Bf⟩_ρ` with `|c-1| ≤ 2`;
* **sharp θ-Hardy** (`SharpHardyCosWeight`) : `2η(1+η) N ≤ (2η/(1+η)) P + C' A`, where
  `2η/(1+η) = 0.99497 < 1`;
* dropping the positive `((1-η)/(1+η)) P` term gives `D ≥ -(C'+2η)(A + √A√B)`.

`I1_lower_of_pieces` below is the (fully proved) algebraic core of that reduction: it is the
last step of any proof of the target, whatever route produced the three inputs.  The remaining
gap is the honest-class justification of the two IBPs — in particular the finiteness of
`P = ‖z∂_z∂_θΨ‖²_ρ`, which is *not* among the hypotheses (`Hon` only gives `HkMem` of
`F`, `z²∂_zzΨ`, `∂_θθΨ`, and the target's own hypothesis adds `HkMem (z∂_zΨ)`).
-/

namespace Work.FTS.EllipticEst.Honest


/-- **The pointwise slice rate** (`H2W.Ae.AeDzSliceRate`, the workspace's recorded "single
remaining analytic gap"): almost every `z`-slice of `z∂_zΨ` is bounded by a multiple of
`sin(2θ)`.  It is a *sup-type* statement, hence not an `L²`-consequence of `Hon`; it is consumed
here only as an explicit hypothesis. -/
def SliceRate (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |z * Work.Spaces.pz Ψ z θ| ≤ K * Real.sin (2 * θ)




end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.slicePsiMemAlt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## Elementary measure-theoretic helpers -/

/-- `σ` is measurable. -/
theorem measurable_sig : Measurable sg := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

/-- `σ ∈ L¹((0,π/2))`. -/
theorem integrableOn_sig_Ioo : IntegrableOn sg (Set.Ioo 0 (Real.pi / 2)) := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_nonneg])).1
  have h2 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) := h.mono_set Set.Ioo_subset_Icc_self
  exact h2.congr_fun (fun θ _ => rfl) measurableSet_Ioo

/-- `σ ≥ 1` on the open quadrant. -/
theorem one_le_sg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sg θ :=
  Work.FTS.EllipticEst.AngSecond.one_le_sig hθ

/-- The `σ`-weighted square of a continuous function is a.e. strongly measurable. -/
theorem aestronglyMeasurable_sq_mul_sig {f : ℝ → ℝ} {s : Set ℝ} (hm : MeasurableSet s)
    (hf : ContinuousOn f s) :
    AEStronglyMeasurable (fun θ => f θ ^ 2 * sg θ) ((volume : Measure ℝ).restrict s) :=
  ((hf.aestronglyMeasurable hm).pow 2).mul measurable_sig.aestronglyMeasurable

/-- From `∫ f² σ < ∞` on a subinterval of the quadrant, get `∫ f² < ∞` (as `σ ≥ 1` there). -/
theorem integrableOn_sq_of_sq_mul_sig {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Ioo 0 (Real.pi / 2))
    (hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).restrict s))
    (hf : IntegrableOn (fun θ => f θ ^ 2 * sg θ) s) :
    IntegrableOn (fun θ => f θ ^ 2) s := by
  refine MeasureTheory.Integrable.mono' hf (hmeas.pow 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hs] with θ hθ
  have h1 : 1 ≤ sg θ := one_le_sg (hsub hθ)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (f θ), h1]

/-- On a finite-measure set, `f² ∈ L¹` implies `f ∈ L¹`. -/
theorem integrableOn_of_sq_integrable {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : (volume : Measure ℝ) s ≠ ⊤)
    (hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).restrict s))
    (h2 : IntegrableOn (fun x => f x ^ 2) s) :
    IntegrableOn f s := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) hfin
  refine MeasureTheory.Integrable.mono' (h2.add hconst) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x), abs_nonneg (f x)]

/-- **Gluing**: integrability on two adjacent open pieces gives it on the union. -/
theorem integrableOn_Ioo_glue {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : IntegrableOn f (Set.Ioo a b)) (h2 : IntegrableOn f (Set.Ioo b c)) :
    IntegrableOn f (Set.Ioo a c) := by
  have h1' : IntegrableOn f (Set.Ioc a b) :=
    h1.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b)).symm
  have h2' : IntegrableOn f (Set.Ioc b c) :=
    h2.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := b) (b := c)).symm
  have hu : IntegrableOn f (Set.Ioc a b ∪ Set.Ioc b c) := h1'.union h2'
  rw [Set.Ioc_union_Ioc_eq_Ioc hab hbc] at hu
  exact hu.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := c))

/-! ## The bound on `u'` near `0` -/

/-- `∫ (u'')² σ < ∞` bounds `u'` on `(0,π/8)`: `u'' ∈ L¹` there (`σ ≥ 1`, `u''` continuous),
so `u'` has a finite limit at `0`; the rest is compactness. -/
theorem deriv_u_bdd_near_zero {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2))) :
    ∃ M : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8), |deriv u θ| ≤ M := by
  have hπ := Real.pi_pos
  have hsub8 : Set.Ioo (0 : ℝ) (Real.pi / 8) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 (by linarith)⟩
  have hu'c : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hu''c : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv_deriv hu
  have hXsq : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_sq_of_sq_mul_sig measurableSet_Ioo (fun θ hθ => hθ)
      (hu''c.aestronglyMeasurable measurableSet_Ioo) hX
  have hXsq8 : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 8)) :=
    hXsq.mono_set hsub8
  have hu''L1 : IntegrableOn (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 8)) := by
    have hmeas : AEStronglyMeasurable (deriv (deriv u))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 8))) :=
      (hu''c.mono hsub8).aestronglyMeasurable measurableSet_Ioo
    refine MeasureTheory.Integrable.mono'
      (hXsq8.add (MeasureTheory.integrableOn_const (C := (1 : ℝ))
        (show (volume : Measure ℝ) (Set.Ioo (0 : ℝ) (Real.pi / 8)) ≠ ⊤ from by
          rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)))
      hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (deriv (deriv u) x), abs_nonneg (deriv (deriv u) x),
      sq_abs (deriv (deriv u) x)]
  have hderivDeriv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      HasDerivAt (deriv u) (deriv (deriv u) x) x := by
    intro x hx
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    exact ((h1.contDiffAt (isOpen_Ioo.mem_nhds (hsub8 hx))).differentiableAt
      (by norm_num)).hasDerivAt
  obtain ⟨L0, hL0⟩ := Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    (δ := Real.pi / 8) (by linarith) hderivDeriv hu''L1
  have hev : {θ : ℝ | deriv u θ ∈ Set.Ioo (L0 - 1) (L0 + 1)} ∈ 𝓝[>] (0 : ℝ) :=
    hL0.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨u0, hu0gt, hu0sub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hev
  have hu0gt' : (0 : ℝ) < u0 := hu0gt
  have hbdd_on : ∀ θ ∈ Set.Ioo (0 : ℝ) u0, |deriv u θ| ≤ |L0| + 1 := by
    intro θ hθ
    have hb := hu0sub hθ
    rw [abs_le]
    exact ⟨by linarith [hb.1, neg_abs_le L0], by linarith [hb.2, le_abs_self L0]⟩
  by_cases hcase : Real.pi / 8 ≤ u0
  · exact ⟨|L0| + 1, fun θ hθ => hbdd_on θ ⟨hθ.1, lt_of_lt_of_le hθ.2 hcase⟩⟩
  · push_neg at hcase
    have hsubK : Set.Icc (u0 / 2) (Real.pi / 8) ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      exact ⟨by linarith [hx.1, hu0gt'], lt_of_le_of_lt hx.2 (by linarith)⟩
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := u0 / 2) (b := Real.pi / 8)).exists_bound_of_continuousOn
      (hu'c.mono hsubK)
    refine ⟨max (|L0| + 1) C, fun θ hθ => ?_⟩
    rcases lt_or_ge θ u0 with hlt | hge
    · exact le_trans (hbdd_on θ ⟨hθ.1, hlt⟩) (le_max_left _ _)
    · have hmem : θ ∈ Set.Icc (u0 / 2) (Real.pi / 8) :=
        ⟨by linarith [hge, hu0gt'], hθ.2.le⟩
      exact le_trans (by simpa [Real.norm_eq_abs] using hC θ hmem) (le_max_right _ _)

/-! ## The two halves of the slice integrability -/

/-- **The near-`0` half.**  With `ψ = u/cos`, both `ψ²σ` and `(ψ')²σ` are integrable on
`(0,π/8)`: `ψ² ≤ 4u²`, `(ψ')² ≤ 32u² + 32 M²` where `M` bounds `u'` on `(0,π/8)`. -/
theorem psi_sq_mem_left {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sg θ) (Set.Ioo (0 : ℝ) (Real.pi / 8)) ∧
    IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 8)) := by
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  have hsub8 : Set.Ioo (0 : ℝ) (Real.pi / 8) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hcos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hψcont : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hψ]
    exact (hu.div Real.contDiff_cos.contDiffOn fun θ hθ => ne_of_gt (hcos θ hθ)).continuousOn
  have hψ'c : ContinuousOn (deriv ψ) (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hψ]; exact continuousOn_deriv_div_cos hu
  have hsig8 : IntegrableOn sg (Set.Ioo (0 : ℝ) (Real.pi / 8)) :=
    integrableOn_sig_Ioo.mono_set hsub8
  have hB8 : IntegrableOn (fun θ => (u θ) ^ 2 * sg θ) (Set.Ioo (0 : ℝ) (Real.pi / 8)) :=
    hB.mono_set hsub8
  obtain ⟨M0, hM0⟩ := deriv_u_bdd_near_zero hu hX
  have hM0nn : 0 ≤ M0 := by
    have h : |deriv u (Real.pi / 16)| ≤ M0 :=
      hM0 _ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    linarith [abs_nonneg (deriv u (Real.pi / 16))]
  -- the derivative formula for `ψ`
  have hψ'formula : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      deriv ψ θ = (deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2 := by
    intro θ hθ
    have hcid : ContDiffAt ℝ 2 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds (hsub8 hθ))
    have hUd : DifferentiableAt ℝ u θ := hcid.differentiableAt (by norm_num)
    simp only [hψ]
    change deriv (u / Real.cos) θ = _
    rw [deriv_div hUd Real.differentiableAt_cos (ne_of_gt (hcos θ (hsub8 hθ))),
      Real.deriv_cos]
    ring
  have hcos8 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8), (1 : ℝ) / 2 ≤ Real.cos θ := by
    intro θ hθ
    have h1 : Real.cos (Real.pi / 3) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ.1.le (by linarith [Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
    rwa [Real.cos_pi_div_three] at h1
  -- `ψ² σ`
  have hpsi_sq : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ) (Set.Ioo (0 : ℝ) (Real.pi / 8)) := by
    refine MeasureTheory.Integrable.mono' (hB8.const_mul 4)
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψcont.mono hsub8)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hc : (1 : ℝ) / 2 ≤ Real.cos θ := hcos8 θ hθ
    have hcpos : 0 < Real.cos θ := hcos θ (hsub8 hθ)
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub8 hθ))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    have h1 : (ψ θ) ^ 2 = (u θ) ^ 2 / Real.cos θ ^ 2 := by
      rw [hψ]; simp only; rw [div_pow]
    have h2 : (u θ) ^ 2 / Real.cos θ ^ 2 ≤ 4 * (u θ) ^ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.cos θ ^ 2)]
      have h4 : (1 : ℝ) ≤ 4 * Real.cos θ ^ 2 := by nlinarith [hc, hcpos]
      have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (u θ))
      linarith [h5]
    have h3 : (ψ θ) ^ 2 ≤ 4 * (u θ) ^ 2 := by rw [h1]; exact h2
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h3 hsig
  -- `(ψ')² σ`
  have hpsi'_sq : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sg θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 8)) := by
    refine MeasureTheory.Integrable.mono'
      ((hB8.const_mul 32).add (hsig8.const_mul (32 * M0 ^ 2)))
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψ'c.mono hsub8)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8) := hθ
    have hc : (1 : ℝ) / 2 ≤ Real.cos θ := hcos8 θ hθ'
    have hcpos : 0 < Real.cos θ := hcos θ (hsub8 hθ')
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub8 hθ'))
    have hM := hM0 θ hθ'
    have hnum : |deriv u θ * Real.cos θ + u θ * Real.sin θ| ≤ M0 + |u θ| := by
      have h1 : |deriv u θ * Real.cos θ + u θ * Real.sin θ| ≤ |deriv u θ| + |u θ| := by
        calc |deriv u θ * Real.cos θ + u θ * Real.sin θ|
            ≤ |deriv u θ * Real.cos θ| + |u θ * Real.sin θ| := abs_add_le _ _
          _ ≤ |deriv u θ| + |u θ| := by
              rw [abs_mul, abs_mul]
              have hc1 : |Real.cos θ| ≤ 1 :=
                abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
              have hs1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
              nlinarith [abs_nonneg (deriv u θ), abs_nonneg (u θ), hc1, hs1]
      linarith [h1, hM]
    have hψ' : |deriv ψ θ| ≤ 4 * (M0 + |u θ|) := by
      rw [hψ'formula θ hθ', abs_div, abs_of_pos (pow_pos hcpos 2)]
      rw [div_le_iff₀ (show (0 : ℝ) < Real.cos θ ^ 2 from pow_pos hcpos 2)]
      have hcs : (1 : ℝ) / 4 ≤ Real.cos θ ^ 2 := by nlinarith [hc, hcpos]
      have hcs' : (1 : ℝ) ≤ 4 * Real.cos θ ^ 2 := by linarith
      have h4 := mul_le_mul_of_nonneg_left hcs' (by positivity : (0 : ℝ) ≤ M0 + |u θ|)
      linarith [hnum, h4]
    have hsq : (4 * (M0 + |u θ|)) ^ 2 ≤ 32 * M0 ^ 2 + 32 * (u θ) ^ 2 := by
      have h1 : |u θ| ^ 2 = (u θ) ^ 2 := sq_abs (u θ)
      nlinarith [sq_nonneg (M0 - |u θ|), h1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    have h5 : (deriv ψ θ) ^ 2 ≤ 32 * M0 ^ 2 + 32 * (u θ) ^ 2 := by
      have h6 : (deriv ψ θ) ^ 2 = |deriv ψ θ| ^ 2 := (sq_abs (deriv ψ θ)).symm
      rw [h6]
      exact le_trans (pow_le_pow_left₀ (abs_nonneg _) hψ' 2) hsq
    have h7 : (deriv ψ θ) ^ 2 * sg θ
        ≤ 32 * (u θ) ^ 2 * sg θ + (32 * M0 ^ 2) * sg θ := by
      have h8 := mul_le_mul_of_nonneg_right h5 hsig
      linarith [h8]
    simp only [Pi.add_apply]
    linarith [h7]
  rw [hψ] at hpsi_sq hpsi'_sq
  exact ⟨hpsi_sq, hpsi'_sq⟩

/-- **The near-`π/2` half.**  With `ψ = u/cos`: `(ψ')²σ` is integrable on `(π/4,π/2)` by
hypothesis (`sin²θ ≥ 1/2` there), hence `ψ' ∈ L¹` near `π/2`, so `ψ` has a finite limit at
`π/2` and is therefore bounded there; the middle piece `(π/8,π/4)` is compact. -/
theorem psi_sq_mem_right {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 8) (Real.pi / 2)) ∧
    IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) := by
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  have h8 : (0 : ℝ) < Real.pi / 8 := by linarith [Real.pi_pos]
  have h4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hsub44 : Set.Ioo (Real.pi / 8) (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans h8 hx.1, lt_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hsub42 : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans h4 hx.1, hx.2⟩
  have hsubIcc44 : Set.Icc (Real.pi / 8) (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le h8 hx.1, lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])⟩
  have hcos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hψcd : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hψ]
    exact hu.div Real.contDiff_cos.contDiffOn fun θ hθ => ne_of_gt (hcos θ hθ)
  have hψc : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)) := hψcd.continuousOn
  have hψ'c : ContinuousOn (deriv ψ) (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hψ]; exact continuousOn_deriv_div_cos hu
  have hsig44 : IntegrableOn sg (Set.Ioo (Real.pi / 8) (Real.pi / 4)) :=
    integrableOn_sig_Ioo.mono_set hsub44
  -- the middle piece: boundedness on the compact `[π/8, π/4]`
  have hmid : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 8) (Real.pi / 4)) ∧
      IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 8) (Real.pi / 4)) := by
    obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := Real.pi / 8) (b := Real.pi / 4)).exists_bound_of_continuousOn
      (hψc.mono hsubIcc44)
    obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := Real.pi / 8) (b := Real.pi / 4)).exists_bound_of_continuousOn
      (hψ'c.mono hsubIcc44)
    constructor
    · refine MeasureTheory.Integrable.mono' (hsig44.const_mul (C1 ^ 2))
        (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψc.mono hsub44)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hmem : θ ∈ Set.Icc (Real.pi / 8) (Real.pi / 4) := ⟨hθ.1.le, hθ.2.le⟩
      have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub44 hθ))
      have h1 : |ψ θ| ≤ C1 := by simpa [Real.norm_eq_abs] using hC1 θ hmem
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
      exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (ψ θ), h1, sq_abs (ψ θ)]) hsig
    · refine MeasureTheory.Integrable.mono' (hsig44.const_mul (C2 ^ 2))
        (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψ'c.mono hsub44)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hmem : θ ∈ Set.Icc (Real.pi / 8) (Real.pi / 4) := ⟨hθ.1.le, hθ.2.le⟩
      have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub44 hθ))
      have h1 : |deriv ψ θ| ≤ C2 := by simpa [Real.norm_eq_abs] using hC2 θ hmem
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
      exact mul_le_mul_of_nonneg_right
        (by nlinarith [abs_nonneg (deriv ψ θ), h1, sq_abs (deriv ψ θ)]) hsig
  -- the piece `(π/4, π/2)`: `(ψ')²σ` from the hypothesis
  have hsq42' : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have hY' : IntegrableOn (fun θ => (Real.sin θ) ^ 2 * (deriv ψ θ) ^ 2 * sg θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      rw [hψ] at hY
      exact hY.mono_set hsub42
    refine MeasureTheory.Integrable.mono' (hY'.const_mul 2)
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψ'c.mono hsub42)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hθ' : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := hθ
    have hsin : (1 : ℝ) / 2 ≤ Real.sin θ ^ 2 := by
      have h1 : Real.sin (Real.pi / 4) ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := θ)
          (by linarith [Real.pi_pos]) (by linarith [hθ'.2, Real.pi_pos]) hθ'.1.le
      rw [Real.sin_pi_div_four] at h1
      have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      have h4 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.sin θ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      linarith [h2, h4]
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub42 hθ'))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    have h4 : (deriv ψ θ) ^ 2 ≤ 2 * (Real.sin θ ^ 2 * (deriv ψ θ) ^ 2) := by
      nlinarith [sq_nonneg (deriv ψ θ), hsin]
    calc (deriv ψ θ) ^ 2 * sg θ ≤ 2 * (Real.sin θ ^ 2 * (deriv ψ θ) ^ 2) * sg θ :=
          mul_le_mul_of_nonneg_right h4 hsig
      _ = 2 * (Real.sin θ ^ 2 * (deriv ψ θ) ^ 2 * sg θ) := by ring
  -- `ψ' ∈ L¹` there, so `ψ` has a limit at `π/2`
  have hsq42 : IntegrableOn (fun θ => (deriv ψ θ) ^ 2) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_sq_of_sq_mul_sig measurableSet_Ioo hsub42
      ((hψ'c.mono hsub42).aestronglyMeasurable measurableSet_Ioo) hsq42'
  have hL1 : IntegrableOn (deriv ψ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_of_sq_integrable measurableSet_Ioo
      (show (volume : Measure ℝ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) ≠ ⊤ from by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      ((hψ'c.mono hsub42).aestronglyMeasurable measurableSet_Ioo) hsq42
  obtain ⟨Lπ, hLπ⟩ := exists_tendsto_nhdsLT_of_integrableOn_deriv (a := Real.pi / 4)
    (b := Real.pi / 2) (by linarith [Real.pi_pos])
    (fun x hx => ((hψcd.contDiffAt (isOpen_Ioo.mem_nhds (hsub42 hx))).differentiableAt
      (by norm_num)).hasDerivAt) hL1
  -- `ψ` is bounded near `π/2`
  obtain ⟨δp, hδp_pos, hδp_lt, hδp_bdd⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 4 ∧
      ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |ψ θ| ≤ |Lπ| + 1 := by
    have hev : {θ : ℝ | ψ θ ∈ Set.Ioo (Lπ - 1) (Lπ + 1)} ∈ 𝓝[<] (Real.pi / 2) :=
      hLπ.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    obtain ⟨t, ht_lt, htsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hev
    have ht_lt' : t < Real.pi / 2 := ht_lt
    refine ⟨min (Real.pi / 2 - t) (Real.pi / 8), lt_min (by linarith) (by linarith),
      lt_of_le_of_lt (min_le_right _ _) (by linarith), fun θ hθ => ?_⟩
    have hδle : min (Real.pi / 2 - t) (Real.pi / 8) ≤ Real.pi / 2 - t := min_le_left _ _
    have hmem : θ ∈ Set.Ioo t (Real.pi / 2) := ⟨by linarith [hθ.1, hδle], hθ.2⟩
    have hb := htsub hmem
    rw [abs_le]
    exact ⟨by linarith [hb.1, neg_abs_le Lπ], by linarith [hb.2, le_abs_self Lπ]⟩
  have hsub_tail : Set.Ioo (Real.pi / 2 - δp) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hδp_pos, hδp_lt, hx.1], hx.2⟩
  have hsq_tail : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 2 - δp) (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono'
      ((integrableOn_sig_Ioo.mono_set hsub_tail).const_mul ((|Lπ| + 1) ^ 2))
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψc.mono hsub_tail)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub_tail hθ))
    have h1 : |ψ θ| ≤ |Lπ| + 1 := hδp_bdd θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (ψ θ), h1, sq_abs (ψ θ)]) hsig
  have hsub_mid : Set.Ioo (Real.pi / 4) (Real.pi / 2 - δp) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans h4 hx.1, lt_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hsubIcc_mid : Set.Icc (Real.pi / 4) (Real.pi / 2 - δp) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le h4 hx.1, lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])⟩
  have hsq_mid : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2 - δp)) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := Real.pi / 4)
      (b := Real.pi / 2 - δp)).exists_bound_of_continuousOn (hψc.mono hsubIcc_mid)
    refine MeasureTheory.Integrable.mono'
      ((integrableOn_sig_Ioo.mono_set hsub_mid).const_mul (C ^ 2))
      (aestronglyMeasurable_sq_mul_sig measurableSet_Ioo (hψc.mono hsub_mid)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hmem : θ ∈ Set.Icc (Real.pi / 4) (Real.pi / 2 - δp) := ⟨hθ.1.le, hθ.2.le⟩
    have hsig : 0 ≤ sg θ := le_trans zero_le_one (one_le_sg (hsub_mid hθ))
    have h1 : |ψ θ| ≤ C := by simpa [Real.norm_eq_abs] using hC θ hmem
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hsig]
    exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (ψ θ), h1, sq_abs (ψ θ)]) hsig
  have hsq42 : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      hsq_mid hsq_tail
  have hsq82 : IntegrableOn (fun θ => (ψ θ) ^ 2 * sg θ) (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
    integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hmid.1 hsq42
  have hsq82' : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sg θ)
      (Set.Ioo (Real.pi / 8) (Real.pi / 2)) :=
    integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hmid.2 hsq42'
  rw [hψ] at hsq82 hsq82'
  exact ⟨hsq82, hsq82'⟩

/-- **`∫ ψ² σ < ∞` and `∫ (ψ')² σ < ∞` on a slice**, from the honest slice hypotheses
(`σ θ = sin(2θ)^{-η}`, `ψ = u/cos θ`). -/
theorem slice_psi_mem_alt (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)) ∧
    IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  obtain ⟨h1, h1'⟩ := psi_sq_mem_left hu hB hX
  obtain ⟨h2, h2'⟩ := psi_sq_mem_right hu hY
  exact ⟨integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) h1 h2,
    integrableOn_Ioo_glue (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) h1' h2'⟩

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.BSlotTop.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.BSlotTop

set_option autoImplicit false

/-- The source slot, with the source written as `TT.ESW.Gsl`. -/
abbrev GsumC (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)

/-- The lower angular chain sum of `B = ∂_θθΨ`. -/
abbrev EsumrC (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)

/-- The top plain angular slot of `Ψ`. -/
abbrev UslC (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)

/-- The high angular slots of `Ψ`. -/
abbrev EjsumC (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α)

/-- The `η`-weighted slot of `∂_θθΨ`. -/
abbrev EtaslC (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The low order terms `∫∫(Ψ')² w²` and `∫∫Ψ² w²`, as two separate integrals. -/
abbrev LoslC (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
    + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))

end Work.FTS.EllipticEst.Prop.BSlotTop
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.Rtilde.SliceGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Prop.Rtilde.SliceGen`: the one-dimensional angular estimate `slice_ang_gen`, from the
weighted `v = u / cos θ` bounds.

This is the final assembly of the paper's §"General `ℋ^k` case" in its `v`-form: the
`(k+2)`-th angular derivative of `u` is controlled through the differentiated slice ODE
`u^{(k+2)} = ∂_θ^{k+1}(tan θ · u) - 6u^{(k)} - g^{(k)}` (`remov.ang_ode_iterate`) and the
Leibniz/Cauchy–Schwarz estimates `remov.slice_ang_A_leibniz`, `remov.slice_ang_A_cs` applied to
`∂_θ^{k+1}(sin θ · v)` with `v = u / cos θ`.  The only geometric input is the weighted `v`-bound
(`VBound`), produced by `remov.slice_ang_v_outer` (proved) and the far-window bound.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Prop.Rtilde

set_option autoImplicit false
set_option maxHeartbeats 2000000


/-- Split a three-term integral. -/
theorem integral_three {s : Set ℝ} {A B C : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A s) (hB : MeasureTheory.IntegrableOn B s)
    (hC : MeasureTheory.IntegrableOn C s) :
    (∫ θ in s, (A θ + B θ + C θ)) = (∫ θ in s, A θ) + (∫ θ in s, B θ) + (∫ θ in s, C θ) := by
  rw [MeasureTheory.integral_add (f := fun θ => A θ + B θ) (g := C) (hA.add hB) hC,
    MeasureTheory.integral_add (f := A) (g := B) hA hB]




end Work.FTS.EllipticEst.Prop.Rtilde
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ### The `η`-slot -/

/-- Almost every `θ ∈ Iθ` is in the open interval (where `sin(2θ) > 0`). -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The pointwise weight identity `(w/σ^{η/2})² = w²·σ^{-η}` at points with `σ > 0`. -/
theorem Zu_sq_eq {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [sq, ← Real.rpow_add hs]
    congr 1
    ring
  rw [Work.FTS.EllipticEst.sEta, div_pow, h1, div_eq_mul_inv, Real.rpow_neg hs.le]

/-- **The `η`-slot bound**: the pure (`i = 0`) slot of `HkIntegrand`. -/
theorem eta_slot_le {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α l f) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ Work.Spaces.HkSq α l f := by
  have hslot := Work.Spaces.L2Sq_DzIter_le_HkSq α l f hmem 0 (Nat.zero_le l)
  have hL2 : Work.Spaces.L2Sq (fun z θ => f z θ *
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [Work.Spaces.L2Sq]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ,
        (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (ae_mem_Ioo_Iθ.mono (fun θ hθ => ?_))
    show (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
    rw [mul_pow, Zu_sq_eq hθ]
    ring
  rw [← hL2]
  simpa only [Work.Spaces.DzIter_zero, sq] using hslot

/-! ### The lower angular chain of `B` -/

/-- The lower `D_θ`-slots of `B = ∂_θθΨ` are controlled by `HkSq α (k-1) B`, with a
constant that is uniform in `α` and in `Ψ`. -/
theorem E_le_HkSq (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (Ψ : ℝ → ℝ → ℝ), 0 < α →
      Work.FTS.EllipticEst.SmoothOpen Ψ →
      Work.Spaces.HkMem α (k - 1) (Bsl Ψ) →
      (∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α (k - 1) (Bsl Ψ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.remov.high_chain_sum_self (k - 1)
  exact ⟨C, hCpos, fun α Ψ hα hsm hmem => hC α (Bsl Ψ) hα (SmoothOpen.forall (hsm.pth.pth)) hmem⟩

end Work.FTS.EllipticEst.TT.ESW
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Shim.DthAux =====
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
set_option maxHeartbeats 2000000

/-! ## 1. The weight comparison -/

theorem sin_sq_mul_Wt_sq_le (α : ℝ) (hα1 : α ≤ 1) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hs : 0 < Real.sin (2 * θ)) :
    (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
  set s := Real.sin (2 * θ) with hsdef
  have hs0 : 0 ≤ s := le_of_lt hs
  have hs1 : s ≤ 1 := Real.sin_le_one _
  have hgam : Work.Spaces.gam α = 1 + α / 10 := rfl
  have hexp : 0 ≤ 2 - Work.Spaces.gam α + Work.Spaces.eta := by
    rw [hgam, Work.Spaces.eta]; linarith
  have h1 : s ^ (2 - Work.Spaces.gam α + Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hs0 hs1 hexp
  have h2 : s ^ (2 - Work.Spaces.gam α) = s ^ (2 - Work.Spaces.gam α + Work.Spaces.eta)
      * s ^ (-(Work.Spaces.eta)) := by
    rw [← Real.rpow_add hs]; ring_nf
  have h3 : s ^ (2 - Work.Spaces.gam α) ≤ s ^ (-(Work.Spaces.eta)) := by
    rw [h2]
    calc s ^ (2 - Work.Spaces.gam α + Work.Spaces.eta) * s ^ (-(Work.Spaces.eta))
        ≤ 1 * s ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs0 _)
      _ = s ^ (-(Work.Spaces.eta)) := one_mul _
  have h4 : s ^ (2:ℝ) * s ^ (-(Work.Spaces.gam α)) = s ^ (2 - Work.Spaces.gam α) := by
    rw [← Real.rpow_add hs]; ring_nf
  have hA : (s ^ (-(Work.Spaces.gam α / 2))) ^ 2 = s ^ (-(Work.Spaces.gam α)) := by
    conv_lhs => rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hs0]
    congr 1
    ring
  have hB : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ (Work.Spaces.eta) := by
    conv_lhs => rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hs0]
    congr 1
    ring
  have hWt : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (s ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta, ← hsdef]
    rw [mul_pow]
  have hC : s ^ 2 = s ^ (2:ℝ) := (Real.rpow_natCast s 2).symm
  have hR : (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.eta)) := by
    rw [div_pow, hB, div_eq_mul_inv, ← Real.rpow_neg hs0]
  calc s ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (s ^ (2:ℝ) * (s ^ (-(Work.Spaces.gam α / 2))) ^ 2) := by
        rw [hC, hWt]; ring
    _ = (Work.Spaces.w z) ^ 2 * s ^ (2 - Work.Spaces.gam α) := by rw [hA, h4]
    _ ≤ (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2)) ^ 2 := hR.symm

theorem smV_of_smoothNbhd {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    ThetaU.SmV f := by
  have hsub : ThetaU.V ⊆ Work.Spaces.nbhU := by
    intro p hp
    exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp.1]), hp.2⟩
  exact ((h.mono hsub).of_le le_top)

theorem hsin_iter (a : ℕ) (z' θ' : ℝ) :
    Work.Spaces.DthIter a (fun _ θ' : ℝ => Real.sin (2 * θ')) z' θ'
      = Real.sin (2 * θ') * Work.FTS.EllipticEst.hfun a θ' := by
  have h1 := congrFun (Work.Spaces.DthIter_eq_iterate_Lop a (fun _ θ' : ℝ => Real.sin (2*θ')) z') θ'
  rw [h1]
  show Work.FTS.EllipticEst.LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ'
      = Real.sin (2 * θ') * Work.FTS.EllipticEst.hfun a θ'
  rw [Work.FTS.EllipticEst.sd_LopIter_sin_factor]

theorem mixed_Dth_expand (n j : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.mixed j n (Work.Spaces.Dth f) z θ
      = ∑ m ∈ Finset.range (n + 1),
          (n.choose (n - m) : ℝ) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ)
            * Work.Spaces.mixed j m (Work.Spaces.pth f) z θ := by
  have hV : (z, θ) ∈ ThetaU.V := ThetaU.mem_V hz hθ
  have hf : ThetaU.SmV f := smV_of_smoothNbhd hsm
  have hsin_slice : ContDiffOn ℝ ⊤ (fun θ' : ℝ => Real.sin (2 * θ'))
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by fun_prop
  -- the θ-only Leibniz expansion of `D_θ^n(D_θ f)`
  have hDth : Set.EqOn (Function.uncurry (Work.Spaces.DthIter n (Work.Spaces.Dth f)))
      (Function.uncurry (fun z θ => ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * ((Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ)
          * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z θ))) ThetaU.V := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    have hpth_slice : ContDiffOn ℝ ⊤ (fun θ'' => Work.Spaces.pth f z' θ'')
        (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      Work.FTS.EllipticEst.Cert.DzAux.contDiffOn_slice_nbh_snd hsm.pth
        (Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp.1]))
    show Work.Spaces.DthIter n (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth f z θ) z' θ' = _
    rw [Work.Spaces.DthIter_mul n (fun _ θ' : ℝ => Real.sin (2 * θ')) (Work.Spaces.pth f) z'
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) isOpen_Ioo hsin_slice hpth_slice θ' hp.2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsin_iter a z' θ']
  -- reassociation of the coefficients
  have hZ : Set.EqOn
      (Function.uncurry (fun z θ => ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * ((Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ)
          * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z θ)))
      (Function.uncurry (fun z θ => ∑ a ∈ Finset.range (n + 1),
        ((n.choose a : ℝ) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ))
          * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z θ)) ThetaU.V := by
    intro p hp
    simp only [Function.uncurry]
    exact Finset.sum_congr rfl fun a _ => by ring
  have h1 : Work.Spaces.DzIter j (Work.Spaces.DthIter n (Work.Spaces.Dth f)) z θ
      = Work.Spaces.DzIter j (fun z θ => ∑ a ∈ Finset.range (n + 1),
          ((n.choose a : ℝ) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ))
            * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z θ) z θ :=
    (ThetaU.DzIter_congr_V hDth j hV).trans (ThetaU.DzIter_congr_V hZ j hV)
  have h2 : Work.Spaces.DzIter j (fun z θ => ∑ a ∈ Finset.range (n + 1),
        ((n.choose a : ℝ) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ))
          * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z θ) z θ
      = ∑ a ∈ Finset.range (n + 1),
          ((n.choose a : ℝ) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ))
            * Work.Spaces.DzIter j (Work.Spaces.DthIter (n - a) (Work.Spaces.pth f)) z θ :=
    ThetaU.DzIter_sum_eqOn_V j (n + 1)
      (fun a θ => (n.choose a : ℝ) * ((Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ)))
      (fun a => Work.Spaces.DthIter (n - a) (Work.Spaces.pth f))
      (fun a => (hf.pth).DthIter (n - a)) hV
  rw [show Work.Spaces.mixed j n (Work.Spaces.Dth f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter n (Work.Spaces.Dth f)) z θ from rfl, h1, h2]
  simp only [Work.Spaces.mixed]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [show n + 1 - 1 - m = n - m from by omega, show n - (n - m) = m from by omega]

/-- `D_z` sees only the `z`-variable, so it commutes with multiplication by a factor `u(θ)`
depending on `θ` only.  (No differentiability hypothesis: `deriv_const_mul_field` is
unconditional.) -/
theorem Dz_mul_of_angular (u : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => u θ * g z θ) = fun z θ => u θ * Work.Spaces.Dz g z θ := by
  funext z θ
  show z * Work.Spaces.pz (fun z θ => u θ * g z θ) z θ = u θ * (z * Work.Spaces.pz g z θ)
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_field (u θ)]
  ring

/-- Iterated form of `Dz_mul_of_angular`. -/
theorem DzIter_mul_of_angular (i : ℕ) (u : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => u θ * g z θ)
      = fun z θ => u θ * Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      exact Dz_mul_of_angular u (Work.Spaces.DzIter n g)

/-- `D_z^i (D_θ f) = sin(2θ)·D_z^i (∂_θ f)` pointwise. -/
theorem DzIter_Dth_eq (i : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter i (Work.Spaces.pth f) z θ := by
  have h := congrFun (congrFun
    (DzIter_mul_of_angular i (fun θ : ℝ => Real.sin (2 * θ)) (Work.Spaces.pth f)) z) θ
  show Work.Spaces.DzIter i (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth f z θ) z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
  exact h

/-- At an angle where `sin(2θ) = 0` the `ℋ^k`-integrand vanishes identically: every summand
carries one of the two weights `w z / sin(2θ)^{η/2}` and `w z·sin(2θ)^{-γ/2}`, both of which
are `0` there (Lean's totalised division resp. `Real.zero_rpow`). -/
theorem HkIntegrand_eq_zero_of_sin_eq_zero (α : ℝ) (hα : 0 < α) (k : ℕ) (g : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α k g z θ = 0 := by
  have h2 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (x := Work.Spaces.eta / 2)
      (div_ne_zero (ne_of_gt Work.Spaces.eta_pos) (by norm_num))]
  have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) = 0 := by
    rw [hs, Real.zero_rpow (x := -(Work.Spaces.gam α / 2))
      (neg_ne_zero.mpr (div_ne_zero (ne_of_gt (Work.Spaces.gam_pos hα)) (by norm_num)))]
  have hA : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [h2, div_zero, mul_zero]; ring)
  have hB : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) = 0 :=
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]
        simp only [Work.Spaces.Wt, Work.Spaces.wTheta, h1, mul_zero]
        ring
      · rw [if_neg hc]))
  rw [Work.Spaces.HkIntegrand, hA, hB, add_zero]

/-- Each radial summand of the `ℋ^k`-integrand of `D_θ f` is a radial summand of the
integrand of `∂_θ f`: the extra factor `sin(2θ)` is bounded by `1` in modulus. -/
theorem radial_summand_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (i : ℕ) (hi : i ≤ k) :
    (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ := by
  rw [DzIter_Dth_eq i f z θ]
  have h1 : (Real.sin (2 * θ) * Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  rw [h1]
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pth f) z θ i hi)
  calc (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 1 * (Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.sin_sq_le_one (2 * θ)) (sq_nonneg _)
    _ = (Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := one_mul _

/-- **The mixed summands.**  For `1 ≤ n`, `n + j ≤ k` and `sin(2θ) ≠ 0`, the mixed summand
of the `ℋ^k`-integrand of `D_θ f` at indices `(n,j)` is bounded by `(k+1)²·((2^k·B)²)` times
the `ℋ^k`-integrand of `∂_θ f`, where `B` bounds the finitely many coefficient functions
`hfun i`, `i ≤ k`, on `Iθ`. -/
theorem mixed_summand_le (α : ℝ) (hα1 : α ≤ 1) (k n j : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) {B : ℝ}
    (hB : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.EllipticEst.hfun i θ| ≤ B)
    (hBnn : 0 ≤ B) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    (hs : Real.sin (2 * θ) ≠ 0) (hn1 : 1 ≤ n) (hnk : n + j ≤ k) :
    (Work.Spaces.mixed j n (Work.Spaces.Dth f) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2)
          * Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ := by
  have hslt : 0 < Real.sin (2 * θ) :=
    lt_of_le_of_ne (Work.FTS.EllipticEst.sin_two_nonneg hθ) hs.symm
  have hnk' : n ≤ k := le_trans (Nat.le_add_right n j) hnk
  have hjk : j ≤ k := le_trans (Nat.le_add_left j n) hnk
  have hθ' : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
  · -- the degenerate slice `z = 0`: both weights vanish
    subst hz0
    have hWt0 : Work.Spaces.Wt α 0 θ = 0 := by
      simp [Work.Spaces.Wt, Work.Spaces.w]
    have hHk0 : Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) 0 θ = 0 :=
      Work.FTS.LocData.HkIntegrand_zero_fst α k (Work.Spaces.pth f) θ
    rw [hWt0, hHk0, mul_zero, mul_zero]
    norm_num
  rw [mixed_Dth_expand n j hsm hz0 hθ']
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  set I : ℝ := Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ with hI
  have hInn : 0 ≤ I := by
    rw [hI]
    exact Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ
  have hKc : 0 ≤ ((2 : ℝ) ^ k * B) ^ 2 := sq_nonneg _
  -- ### The summand bounds
  have hterm : ∀ m ∈ Finset.range (n + 1),
      ((↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
        * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)) ^ 2
      ≤ ((2 : ℝ) ^ k * B) ^ 2 * I := by
    intro m hm
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- the summand with no angular derivative of `∂_θ f`: the weight comparison applies
      subst hm0
      rw [Work.Spaces.mixed_zero_right]
      have hc0 : ↑(n.choose (n - 0)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - 0) θ)
          = Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun n θ := by simp
      rw [hc0]
      have hhB : |Work.FTS.EllipticEst.hfun n θ| ≤ B := hB n hnk' θ hθ
      have hh2 : (Work.FTS.EllipticEst.hfun n θ) ^ 2 ≤ B ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hBnn]
        exact hhB
      have hwt : (Real.sin (2 * θ)) ^ 2 * W ^ 2
          ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
        rw [hW]
        exact sin_sq_mul_Wt_sq_le α hα1 hθ hslt
      have hzJ : (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ I := by
        rw [hI]
        exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pth f) z θ j hjk
      have hmain : (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun n θ
            * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ * W)) ^ 2 ≤ B ^ 2 * I := by
        have h1 : (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun n θ
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ * W)) ^ 2
            = (Work.FTS.EllipticEst.hfun n θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 * W ^ 2)
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2 := by ring
        rw [h1]
        have hprod : (Work.FTS.EllipticEst.hfun n θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 * W ^ 2)
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2
            ≤ B ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hh2 hwt (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg B))
            (sq_nonneg _)
        calc (Work.FTS.EllipticEst.hfun n θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 * W ^ 2)
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2
            ≤ B ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2 := hprod
          _ = B ^ 2 * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
                ring
          _ ≤ B ^ 2 * I := mul_le_mul_of_nonneg_left hzJ (sq_nonneg B)
      have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hBB : B ≤ (2 : ℝ) ^ k * B := by
        simpa using mul_le_mul_of_nonneg_right h2k hBnn
      have hB2 : B ^ 2 ≤ ((2 : ℝ) ^ k * B) ^ 2 := pow_le_pow_left₀ hBnn hBB 2
      exact le_trans hmain (mul_le_mul_of_nonneg_right hB2 hInn)
    · -- a summand carrying a genuine angular derivative of `∂_θ f`
      have hm1 : 1 ≤ m := hmpos
      have hmj : m + j ≤ k := le_trans (Nat.add_le_add_right hmle j) hnk
      have hch : (↑(n.choose (n - m)) : ℝ) ≤ (2 : ℝ) ^ k := by
        have h1 : n.choose (n - m) ≤ 2 ^ n := Nat.choose_le_two_pow n (n - m)
        have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hnk'
        calc (↑(n.choose (n - m)) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast h1
          _ ≤ (2 : ℝ) ^ k := h2
      have hc2 : (↑(n.choose (n - m)) * (Real.sin (2 * θ)
            * Work.FTS.EllipticEst.hfun (n - m) θ)) ^ 2 ≤ ((2 : ℝ) ^ k * B) ^ 2 := by
        rw [mul_pow]
        have hsh : (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ) ^ 2 ≤ B ^ 2 := by
          rw [mul_pow]
          have hhB : |Work.FTS.EllipticEst.hfun (n - m) θ| ≤ B :=
            hB (n - m) (le_trans (Nat.sub_le n m) hnk') θ hθ
          have hh2 : (Work.FTS.EllipticEst.hfun (n - m) θ) ^ 2 ≤ B ^ 2 := by
            rw [sq_le_sq, abs_of_nonneg hBnn]
            exact hhB
          calc (Real.sin (2 * θ)) ^ 2 * (Work.FTS.EllipticEst.hfun (n - m) θ) ^ 2
              ≤ 1 * B ^ 2 :=
                mul_le_mul (Real.sin_sq_le_one (2 * θ)) hh2 (sq_nonneg _) zero_le_one
            _ = B ^ 2 := one_mul _
        calc (↑(n.choose (n - m)) : ℝ) ^ 2
              * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ) ^ 2
            ≤ ((2 : ℝ) ^ k) ^ 2 * B ^ 2 :=
              mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hch 2) hsh (sq_nonneg _)
                (by positivity)
          _ = ((2 : ℝ) ^ k * B) ^ 2 := by ring
      have hxw : (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W) ^ 2 ≤ I := by
        rw [hW, hI]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α k (Work.Spaces.pth f) z θ m j hm1 hmj
      calc ((↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
            * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)) ^ 2
          = (↑(n.choose (n - m)) * (Real.sin (2 * θ)
              * Work.FTS.EllipticEst.hfun (n - m) θ)) ^ 2
            * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W) ^ 2 := by ring
        _ ≤ ((2 : ℝ) ^ k * B) ^ 2 * I := mul_le_mul hc2 hxw (sq_nonneg _) hKc
  -- ### Cauchy–Schwarz and summation
  have hgather : (∑ m ∈ Finset.range (n + 1),
        ↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ)
          * Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)
      = ∑ m ∈ Finset.range (n + 1),
        (↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
          * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W) :=
    Finset.sum_congr rfl (fun m _ => by ring)
  rw [Finset.sum_mul, hgather]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (n + 1))
    (f := fun m => (↑(n.choose (n - m)) * (Real.sin (2 * θ)
          * Work.FTS.EllipticEst.hfun (n - m) θ))
        * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W))
  have hcard : ((Finset.range (n + 1)).card : ℝ) = (n + 1 : ℝ) := by simp
  rw [hcard] at hcs
  have h1 : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have h : n + 1 ≤ k + 1 := Nat.succ_le_succ hnk'
    exact_mod_cast h
  calc (∑ m ∈ Finset.range (n + 1),
        (↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
          * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)) ^ 2
      ≤ (n + 1 : ℝ) * ∑ m ∈ Finset.range (n + 1),
          ((↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
            * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)) ^ 2 := hcs
    _ ≤ (n + 1 : ℝ) * ∑ m ∈ Finset.range (n + 1), ((2 : ℝ) ^ k * B) ^ 2 * I :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = (n + 1 : ℝ) * ((n + 1 : ℝ) * (((2 : ℝ) ^ k * B) ^ 2 * I)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = (((n : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I := by ring
    _ ≤ (((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 2) hKc) hInn
    _ = ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I := by push_cast; ring

/-- Pointwise domination of the `ℋ^k`-integrand of `D_θ f` by that of `∂_θ f` on the whole
closed quadrant. -/
theorem HkIntegrand_Dth_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
        ≤ C * Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ := by
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.EllipticEst.sd_exists_bound_hfun k
  refine ⟨(k + 1 : ℝ) + (k + 1 : ℝ) ^ 2 * ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2),
    by positivity, ?_⟩
  intro z hz θ hθ
  set I : ℝ := Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ with hI
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin_eq_zero α hα k (Work.Spaces.Dth f) hs]
    exact mul_nonneg (by positivity) (Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ)
  · have hsum1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (k + 1 : ℝ) * I := by
      calc (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ i ∈ Finset.range (k + 1), I :=
            Finset.sum_le_sum (fun i hi => by
              rw [hI]
              exact radial_summand_le α k f i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        _ = (k + 1 : ℝ) * I := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hsum2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ (k + 1 : ℝ) ^ 2 * (((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0))
          ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I :=
            Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ k
              · rw [if_pos hc]
                have h := mixed_summand_le α hα1 k i j hsm hB (le_of_lt hBpos) hz hθ hs hc.1 hc.2
                rw [← hI] at h
                exact h
              · rw [if_neg hc]
                have h0 : 0 ≤ I := by
                  rw [hI]
                  exact Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ
                exact mul_nonneg (by positivity) h0))
        _ = (k + 1 : ℝ) ^ 2 * (((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I) := by
            rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
            push_cast
            ring
    calc Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
        = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * Work.Spaces.Wt α z θ) ^ 2
              else 0) := by rw [Work.Spaces.HkIntegrand]
      _ ≤ (k + 1 : ℝ) * I + (k + 1 : ℝ) ^ 2 * (((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I) :=
          add_le_add hsum1 hsum2
      _ = ((k + 1 : ℝ) + (k + 1 : ℝ) ^ 2 * ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2)) * I := by
          ring


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.interpGamma_core_compact =====
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

/-! ## 1. Vanishing off the support rectangle

If the (uncurried) `h` vanishes off `[A,B] × [c,d]`, then so does every derivative built from
`∂_z`, `∂_θ`, `D_z = z∂_z`, `D_θ = sin(2θ)∂_θ`: off the closed rectangle the function is
*identically* zero on a neighbourhood of the point, so all iterated derivatives vanish. -/









/-! ## 2. Smoothness on the closed angular interval from smoothness on the open one

For a function which vanishes outside a compact subinterval `[c,d] ⊂ (0,π/2)`, smoothness on the
open interval upgrades to smoothness on the closed interval `Iθ`: at the two endpoints the
function is identically zero on a neighbourhood. -/


/-! ## 3. Derivative identities for the slices of `G`

For `z > 0` and `θ ∈ (0,π/2)` the angular derivatives of the `θ`-slice of `D_zG` are the
corresponding slices of `D_z∂_θG`, resp. `D_z∂_θ²G` (Clairaut on the open quadrant). -/

lemma deriv_slice_Dz {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.Dz G z θ') θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  exact (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall G).mp hG) 1) hmem


/-! ## 4. The slicewise interpolation inequality

For `z ≥ 0`, with `σ_a = sigA α` the light weight:

  `∫_θ (D_z∂_θG)² σ_a ≤ -∫_θ (D_zG)(D_z∂_θ²G) σ_a`

(`0 ≤ z` is enough: at `z = 0` both sides are `0`). -/


/-! ## 5. Continuity on the support rectangle -/





/-! ## 6. The main theorem -/


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.OpenIntegrability =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

variable {f : ℝ → ℝ → ℝ}

/-! ## The fixed angular weight `Sfun` -/

/-- `Sfun α θ = sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ}`: the three fixed integrable
terms attached to `sliceA u` in `slicePhi`. -/
def Sfun (α θ : ℝ) : ℝ :=
  Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
    + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)






/-! ## Interior equalities are a.e. equalities on `Iθ` -/

/-- `Iθ` and its interior differ by the two null endpoints. -/
theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc).symm

/-- An equality of functions holding at every interior angle holds a.e. on `Iθ`. -/
theorem ae_eq_of_forall_Ioo {u v : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ = v θ) :
    u =ᵐ[volume.restrict Work.Spaces.Iθ] v := by
  rw [Filter.EventuallyEq, MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-! ## Integrability of the individual summands -/


private lemma measurable_Wt_right (α z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
    hsin.pow_const _
  have : Measurable (fun θ : ℝ => Work.Spaces.w z *
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := measurable_const.mul hpow
  simpa [Work.Spaces.Wt, Work.Spaces.wTheta] using this


/-! ## Stripping the radial weight -/

private lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  rw [Work.Spaces.w]
  exact div_ne_zero h1 h2




end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.AeChainDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- **Step 1 of the level-`0` estimate in the weak class `AeData`** (the paper's Step 1, i.e. the
energy identity obtained by pairing `(PolarBSL)` with `u` and integrating, followed by the
`σ`-upgrade and the Hardy-based `Ψ̄ = u/cos θ` companion).

For every datum `AeData α u G` there is a universal `C` with

* `u`, `z ∂_z u` and `u / cos θ` honest in `ℋ⁰` (`HkMem α 0`),
* `‖u‖_ρ ≤ C‖G‖_ρ` and `α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`,
* `‖u/cos θ‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ)`.

(Paper's ingredients: multiply `(PolarBSL)` by `u` and integrate against the weight; the angular
part gives `|∂_θu|² - 6|u|² ≤ |G||u|`, and the moment condition `F_*(u) = 0` a.e. (used through
the Fourier/Parseval decomposition `u = Σ u_n(z)sin(2nθ)`) excludes the `n = 1` mode, which is
what makes `-6|u|²` absorbable; then `‖u/cos θ‖` and the `σ`-upgrade follow from the Hardy
inequalities `∫ f²/sin²(2θ) ≤ 10∫(f')²` and the constrained slice Poincaré
(`Honest.SigmaPoincare`, `Honest.Gap9Open`, both proved) — cf. `Honest/NOTES_step1.md`.) -/
def AeStep1Full : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u ∧
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) ∧
      Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G ∧
      α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u))





end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzPrim.PairAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.PerzPrim

set_option autoImplicit false

/-- For `f` smooth on the open quadrant and `z ∈ Iz`, the angular slice of the level-`k`
`ℋ`-integrand is a.e. strongly measurable on `Iθ`. -/
lemma aesm_slice_HkIntegrand_of_smoothOpen {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ => (0 : ℝ) from
      funext fun θ => Work.Spaces.HkIntegrand_zero_z α k f θ]
    exact aestronglyMeasurable_const
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (hf.continuousOn_HkIntegrand α k) hzpos

/-- **The reverse triangle inequality for the `ℋ^k`-integrand.**  With `f`, `g` smooth on the
open quadrant, on `Iz × Iθ`,
`HkIntegrand α k f ≤ 2 · HkIntegrand α k (f+g) + 2 · HkIntegrand α k g`.
Obtained from `HkIntegrand_add_le_open` applied to the pair `(f+g, -g)`. -/
lemma HkIntegrand_le_add_of_smoothOpen {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k f z θ ≤
      2 * Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hfg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hf hg
  have hng : Work.FTS.EllipticEst.SmoothOpen (-g) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun x : ℝ × ℝ => -g x.1 x.2)
      Work.FTS.EllipticEst.Q0
    exact hg.neg
  have h := Work.FTS.EllipticEst.HkIntegrand_add_le_open α k
    (f := fun z θ => f z θ + g z θ) (g := -g) hfg hng hz hθ
  rw [Work.FTS.EllipticEst.HkIntegrand_neg α k g,
    show (fun z θ => (f z θ + g z θ) + (-g) z θ) = f from by ext z θ; simp] at h
  exact h

/-- **The junk-robust per-`z` angular-energy bound for a sum.**  If the angular energy of `g` is
integrable at `z` with integral `≤ b`, and the Bochner integral of the angular energy of `f` is
`≤ B` (no integrability of `f` assumed), then the angular energy of `f + g` has Bochner integral
`≤ 2 B + 2 b`. -/
theorem integral_HkIntegrand_add_le {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {B b : ℝ}
    (hB : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) ≤ B) (hB0 : 0 ≤ B)
    (hbint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k g z θ) Work.Spaces.Iθ)
    (hb : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) ≤ b) (hb0 : 0 ≤ b) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      ≤ 2 * B + 2 * b := by
  set a : ℝ → ℝ := fun θ => Work.Spaces.HkIntegrand α k f z θ with ha
  set bb : ℝ → ℝ := fun θ => Work.Spaces.HkIntegrand α k g z θ with hbb
  set ff : ℝ → ℝ := fun θ => Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ with hff
  have hfg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hf hg
  have hAESMa : MeasureTheory.AEStronglyMeasurable a
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_slice_HkIntegrand_of_smoothOpen hf hz
  have hAESMf : MeasureTheory.AEStronglyMeasurable ff
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_slice_HkIntegrand_of_smoothOpen hfg hz
  have hfw : ∀ θ ∈ Work.Spaces.Iθ, ff θ ≤ 2 * a θ + 2 * bb θ := fun θ hθ =>
    Work.FTS.EllipticEst.HkIntegrand_add_le_open α k hf hg hz hθ
  have hrev : ∀ θ ∈ Work.Spaces.Iθ, a θ ≤ 2 * ff θ + 2 * bb θ := fun θ hθ =>
    HkIntegrand_le_add_of_smoothOpen hf hg hz hθ
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ff θ ≤ 2 * a θ + 2 * bb θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hfw θ hθ
  have hae_rev : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖a θ‖ ≤ 2 * ff θ + 2 * bb θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hrev θ hθ
  have hae_fwd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖ff θ‖ ≤ 2 * a θ + 2 * bb θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k _ z θ)]
    exact hfw θ hθ
  by_cases hA : MeasureTheory.Integrable a (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · have h2ab : MeasureTheory.Integrable (fun θ => 2 * a θ + 2 * bb θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hA.const_mul 2).add (hbint.const_mul 2)
    have hffint : MeasureTheory.Integrable ff (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      h2ab.mono' hAESMf hae_fwd
    have hmain := MeasureTheory.integral_mono_ae hffint h2ab hae
    rw [MeasureTheory.integral_add (hA.const_mul 2) (hbint.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmain
    linarith
  · have hnotff : ¬ MeasureTheory.Integrable ff
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      intro hffint
      have h2fb : MeasureTheory.Integrable (fun θ => 2 * ff θ + 2 * bb θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hffint.const_mul 2).add (hbint.const_mul 2)
      exact hA (h2fb.mono' hAESMa hae_rev)
    rw [MeasureTheory.integral_undef hnotff]
    linarith

end Work.FTS.EpsEngine.PerzPrim
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzTools.aesm_uncurry_restricted_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.PerzTools

open MeasureTheory Set

/-- **Carathéodory measurability of a `(s,θ)`-function continuous in `θ` on `(0,π/2)` and
vanishing off it**, relative to the horizon `A`.  The `s`-slices need only be a.e. strongly
measurable for `volume.restrict A`, and only for `θ` in the open interval.  The proof truncates
to `A` (making the `s`-slices a.e. strongly measurable w.r.t. the unrestricted `volume`),
applies the unrestricted one-dimensional Carathéodory lemma, and transfers back along the
dominated measure `(volume.restrict A).prod volume ≤ volume.prod volume` together with the a.e.
fact that `p.1 ∈ A`. -/
theorem aesm_uncurry_restricted_theta {A : Set ℝ} (hA : MeasurableSet A) {g : ℝ → ℝ → ℝ}
    (hcont : ∀ s ∈ A, ContinuousOn (fun θ : ℝ => g s θ) (Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ s ∈ A, ∀ θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → g s θ = 0)
    (hmeas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => g s θ) (MeasureTheory.volume.restrict A)) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
      ((MeasureTheory.volume.restrict A).prod MeasureTheory.volume) := by
  classical
  -- Truncate `g` to the horizon `A`.
  set g₁ : ℝ → ℝ → ℝ := fun s θ => if s ∈ A then g s θ else 0 with hg₁
  -- Measurability of the `s`-slices, extended to *all* `θ` (for `θ ∉ Ioo` the slice vanishes
  -- on `A`, hence is a.e. equal to `0` for `volume.restrict A`).
  have hmeas_all : ∀ θ : ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g s θ)
      (MeasureTheory.volume.restrict A) := by
    intro θ
    by_cases hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · exact hmeas θ hθ
    · refine (MeasureTheory.aestronglyMeasurable_const (b := (0 : ℝ))).congr ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict hA] with x hx
      exact (hzero x hx θ hθ).symm
  -- Continuity of the truncated `θ`-slices.
  have hcont₁ : ∀ s : ℝ, ContinuousOn (fun θ : ℝ => g₁ s θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro s
    by_cases hs : s ∈ A
    · refine (hcont s hs).congr ?_
      intro θ _
      simp only [hg₁]
      rw [if_pos hs]
    · have hfun : (fun θ : ℝ => g₁ s θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp only [hg₁]
        rw [if_neg hs]
      rw [hfun]
      exact continuousOn_const
  -- Vanishing of the truncated function off the interval.
  have hzero₁ : ∀ s : ℝ, ∀ θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → g₁ s θ = 0 := by
    intro s θ hθ
    by_cases hs : s ∈ A
    · simp only [hg₁]
      rw [if_pos hs]
      exact hzero s hs θ hθ
    · simp only [hg₁]
      rw [if_neg hs]
  -- Strong measurability of the truncated `s`-slices for the unrestricted measure: the
  -- truncated slice is the indicator of `A` applied to the original slice.
  have hmeas₁ : ∀ θ : ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g₁ s θ)
      (MeasureTheory.volume : Measure ℝ) := by
    intro θ
    have hfun : (fun s : ℝ => g₁ s θ) = A.indicator (fun s : ℝ => g s θ) := by
      funext s
      simp only [hg₁, Set.indicator_apply]
    rw [hfun]
    exact (aestronglyMeasurable_indicator_iff hA).2 (hmeas_all θ)
  have hbig : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => g₁ p.1 p.2)
      ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ)) :=
    aesm_uncurry_of_continuousOn_of_zero_1d (g := g₁) hcont₁ hzero₁ hmeas₁
  -- The restricted product measure is dominated by the unrestricted one.
  have hle : (MeasureTheory.volume.restrict A).prod (MeasureTheory.volume : Measure ℝ)
      ≤ (MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ) :=
    MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self le_rfl
  -- ... and is carried by `A ×ˢ univ`.
  have haeA : ∀ᵐ p ∂((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume : Measure ℝ)),
      p.1 ∈ A := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : ℝ × ℝ | ¬ p.1 ∈ A} = Aᶜ ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.restrict_apply' hA,
      Set.compl_inter_self, measure_empty, zero_mul]
  refine (hbig.mono_measure hle).congr ?_
  filter_upwards [haeA] with p hp
  simp only [hg₁]
  rw [if_pos hp]

end Work.FTS.EpsEngine.PerzTools
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.SharpMulSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000





end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.upper_inv_layer_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut


end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.intervalIntegrable_mixed_div_sin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

/-!
# Integrability of the angular quotient `D_z^b D_θ f / sin(2θ)` near `θ = 0`

The layer lemmas of `Work.FTS.GalBasis.cc` (`sharp_layer_le`, `wrongWeight_layer_tendsto_zero`)
need the *interval* integrability of `θ ↦ D_z^b D_θ f (z,θ) / sin(2θ)` on `[0,2t]` for a fixed
`z > 0`, with `2t ≤ π/4` (so `sin(2θ)` is small only at the left endpoint).

For a merely `C^∞`-on-the-open-quadrant `f` this is *not* continuity at `θ = 0` — the quotient may
well be unbounded there — but it is a genuine `L¹` statement, and the `ℋ^4`-membership forbids the
blow-up: writing

  `D_z^b D_θ f / sin(2θ) = (D_z^b D_θ f · W) · (w⁻¹ · sin(2θ)^{γ/2 - 1})`,

the first factor is (up to a summand) square-integrable because `HkIntegrand α 4 f` dominates
`(mixed b 1 f · W)²` for `b ≤ 3`, and the second is square-integrable because `γ > 1` makes
`sin(2θ)^{γ-2}` integrable on `(0,2t]` (the sharp Hardy-side exponent).  Cauchy–Schwarz /
`2|xy| ≤ x² + y²` then gives the `L¹`-bound.

The two auxiliary facts used below are `Work.Spaces.sq_le_HkIntegrand_mixed` (a mixed summand of
`HkIntegrand` is dominated by the whole integrand) and
`Work.FTS.GalBasis.cc.integrableOn_sin_pow_sub_two` (`sin(2θ)^{γ-2} ∈ L¹(0,b)` for `γ > 1`,
`b ≤ π/4`).
-/

/-! ## Continuity of the `W`-weight on the open quadrant -/

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2) (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The angular slice of the weighted mixed derivative `D_z^j D_θ^i f · W` is a.e. strongly
measurable, for `z > 0`. -/
lemma aesm_slice_mixed_Wt {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _
    (((hsm.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) hz

/-- The square of the angular slice above is a.e. strongly measurable. -/
lemma aesm_slice_mixed_Wt_sq {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  convert (aesm_slice_mixed_Wt hsm α j i hz).pow 2 using 1

/-! ## The main lemma -/


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.psiCut_spec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.Transport_L12_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.GalFields.RHS

set_option linter.unusedVariables false

/-! ## Continuity of the density integrand on the open quadrant -/

/-- The joint integrand `(z,θ) ↦ K θ·Transport f z θ/z` of the `L₁₂`-density of `Transport f`
is continuous on the open quadrant, for `f` of class `SmoothOpen`. -/
private theorem transport_dens_continuousOn {f : ℝ → ℝ → ℝ}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.K p.2 * Work.Coercivity.Transport f p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hSf.pth).continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hc : Continuous fun θ : ℝ => Work.Spaces.K θ := by
      change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
      fun_prop
    exact (hc.comp continuous_snd).continuousOn
  have hTr : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Transport f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    show ContinuousOn (fun p : ℝ × ℝ =>
      3 * (Real.sin (2 * p.2) * Work.Spaces.pth f p.1 p.2) / (1 + p.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
    refine ContinuousOn.div ?_ (continuousOn_const.add continuousOn_fst) (fun p hp => ?_)
    · exact continuousOn_const.mul
        (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mul hpth)
    · have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
      linarith
  exact (hK.mul hTr).div continuousOn_fst
    (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)

/-- **A.e. strong measurability of the `L₁₂`-density of the transport term** on `(0,∞)`: the
density is the partial `θ`-integral of the jointly continuous integrand of
`transport_dens_continuousOn`, hence a.e. strongly measurable by Fubini measurability. -/
private theorem aesm_L12dens_transport {f : ℝ → ℝ → ℝ}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Work.Construction.L12dens (Work.Coercivity.Transport f))
      (volume.restrict (Set.Ioi 0)) := by
  have hcont := transport_dens_continuousOn hSf
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Coercivity.Transport f p.1 p.2 / p.1) hcont
  have h := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
  have h3 : AEStronglyMeasurable (Work.Construction.L12dens (Work.Coercivity.Transport f))
      (volume.restrict Work.Spaces.Iz) := by
    convert h using 1
    funext z
    rfl
  have hset : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz := MeasureTheory.Ioi_ae_eq_Ici
  rw [MeasureTheory.Measure.restrict_congr_set hset]
  exact h3

/-! ## The two pointwise bounds -/

/-- **Pointwise bound on an angular slice.**  For `s > 0` and `θ ∈ Iθ`, the slice integrand of
the `L₁₂`-density of `Transport f` is dominated by `Wlam3 s·9(1 + HkIntegrand α 4 f s θ)/2`,
an integrable function of `θ` as soon as `f ∈ ℋ⁴_α`.  The `ℋ⁴`-slot used is the `(i,j) = (1,0)`
one, `(D_θ f·W)² ≤ HkIntegrand α 4 f`. -/
private theorem transport_slice_pointwise_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s|
      ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s
        * (9 * (1 + Work.Spaces.HkIntegrand α 4 f s θ) / 2) := by
  rw [Work.FTS.StrongPersist.L3Aux.tl12_Transport_integrand_eq α f hs hθ]
  rw [abs_mul, abs_of_nonneg (Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hs))]
  refine mul_le_mul_of_nonneg_left ?_
    (Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hs))
  have hKGnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.KG α θ :=
    Work.FTS.StrongPersist.L3Aux.tl12_KG_nonneg α hθ
  have hKGle : Work.FTS.StrongPersist.L3Aux.KG α θ ≤ 9 :=
    Work.FTS.StrongPersist.L3Aux.tl12_KG_le_nine α hθ
      (Work.FTS.StrongPersist.L3Aux.tl12_gam_half_nonneg hα)
  have hsq : (Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s θ 1 0 (le_refl 1) (by norm_num)
  have hb : |Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f s θ) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hAM := Work.FTS.GalBasis.cc.sqrt_le_half_one_add
    (Work.Spaces.HkIntegrand_nonneg α 4 f s θ)
  calc |Work.FTS.StrongPersist.L3Aux.KG α θ
        * (Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ)|
      = Work.FTS.StrongPersist.L3Aux.KG α θ
          * |Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ| := by
        rw [abs_mul, abs_of_nonneg hKGnn]
    _ ≤ 9 * Real.sqrt (Work.Spaces.HkIntegrand α 4 f s θ) :=
        mul_le_mul hKGle hb (abs_nonneg _) (by norm_num)
    _ ≤ 9 * (1 + Work.Spaces.HkIntegrand α 4 f s θ) / 2 := by
        have h := mul_le_mul_of_nonneg_left hAM (by norm_num : (0 : ℝ) ≤ 9)
        linarith

/-- **Pointwise bound on the density.**  For `s > 0` and `f ∈ ℋ⁴_α`, the `L₁₂`-density of
`Transport f` is dominated by `13·(Wlam3 s² + (√(∫_θ HkIntegrand α 4 f s θ))²)`: the angular
Cauchy–Schwarz step `tl12_abs_integral_KG_le` (with `√(∫_θ KG²) ≤ 13`) followed by AM–GM. -/
private theorem transport_L12dens_pointwise_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α 4 f) {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens (Work.Coercivity.Transport f) s|
      ≤ 13 * (Work.FTS.StrongPersist.L3Aux.Wlam3 s ^ 2
          + (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) ^ 2) := by
  have hsz : s ∈ Work.Spaces.Iz := le_of_lt hs
  have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iθ :=
    hmf.1 s hsz
  have hW3nn : 0 ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s :=
    Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hs)
  rw [Work.FTS.StrongPersist.L3Aux.tl12_L12dens_Transport_eq α f hs, abs_mul,
    abs_of_nonneg hW3nn]
  have h1 : |∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.KG α θ
        * (Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ)|
      ≤ 13 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ) := by
    refine le_trans (Work.FTS.StrongPersist.L3Aux.tl12_abs_integral_KG_le α hα f hInt) ?_
    have h13 := Work.FTS.StrongPersist.L3Aux.tl12_sqrt_KG_sq_le α hα
    exact mul_le_mul_of_nonneg_right h13 (Real.sqrt_nonneg _)
  calc Work.FTS.StrongPersist.L3Aux.Wlam3 s
        * |∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.KG α θ
            * (Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ)|
      ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s
          * (13 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) :=
        mul_le_mul_of_nonneg_left h1 hW3nn
    _ = 13 * (Work.FTS.StrongPersist.L3Aux.Wlam3 s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) := by ring
    _ ≤ 13 * (Work.FTS.StrongPersist.L3Aux.Wlam3 s ^ 2
          + (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        nlinarith [sq_nonneg (Work.FTS.StrongPersist.L3Aux.Wlam3 s
          - Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ))]

/-! ## The theorem -/

theorem Transport_L12_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) (hmf : Work.Spaces.HkMem α 4 f) :
    (∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun s => Work.Construction.L12dens (Work.Coercivity.Transport f) s) (Set.Ioi 0) := by
  have hcont := transport_dens_continuousOn hSf
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  constructor
  · intro s hs
    have hsz : s ∈ Work.Spaces.Iz := le_of_lt hs
    have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iθ :=
      hmf.1 s hsz
    have haesm : AEStronglyMeasurable
        (fun θ => Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hs
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      continuous_const.integrableOn_Icc
    have hmaj : IntegrableOn (fun θ => Work.FTS.StrongPersist.L3Aux.Wlam3 s
        * (9 * (1 + Work.Spaces.HkIntegrand α 4 f s θ) / 2)) Work.Spaces.Iθ := by
      have h1 : IntegrableOn (fun θ => (Work.FTS.StrongPersist.L3Aux.Wlam3 s * (9 / 2))
          * (1 + Work.Spaces.HkIntegrand α 4 f s θ)) Work.Spaces.Iθ :=
        (hconst.add hHk).const_mul _
      refine h1.congr_fun (fun θ _ => ?_) hIθ
      ring
    refine hmaj.mono' haesm ?_
    rw [ae_restrict_iff' hIθ]
    exact Eventually.of_forall fun θ hθ => by
      rw [Real.norm_eq_abs]
      exact transport_slice_pointwise_le hα hs hθ
  · set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ with hH
    set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
    have hHnn : ∀ s, 0 ≤ H s :=
      fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f s θ
    have hH_int : IntegrableOn H (Set.Ioi 0) := hmf.2.mono_set Set.Ioi_subset_Ici_self
    have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) :=
      hH_int.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
    have hcont3 : ContinuousOn Work.FTS.StrongPersist.L3Aux.Wlam3 (Set.Ioi 0) := by
      change ContinuousOn (fun s : ℝ => s / (1 + s) ^ 3) (Set.Ioi 0)
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 3)
        (fun s hs => ?_)
      have h1 : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs]
      positivity
    have hW3sq_int : IntegrableOn (fun s => Work.FTS.StrongPersist.L3Aux.Wlam3 s ^ 2)
        (Set.Ioi 0) := by
      refine Work.Elliptic.psi_sq_integrable_aux.mono'
        ((hcont3.pow 2).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hsm : 0 < s := Set.mem_Ioi.mp hs
      have h0 : 0 ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s :=
        Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hsm)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h0
        (Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_le_Wlam (le_of_lt hsm)) 2
    have hmaj : IntegrableOn
        (fun s => 13 * (Work.FTS.StrongPersist.L3Aux.Wlam3 s ^ 2 + A s ^ 2))
        (Set.Ioi 0) := (hW3sq_int.add hA2_int).const_mul 13
    refine hmaj.mono' (aesm_L12dens_transport hSf) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun s hs => by
      have hb := transport_L12dens_pointwise_le hα hmf hs
      simpa only [hA, hH, Real.norm_eq_abs] using hb

end Work.FTS.GalFields.RHS
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Tail.L12_Fstar_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.Tail

set_option autoImplicit false


end Work.FTS.GalFields.Tail
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.ZetaBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

open Work.FTS.GalBasis.cc

set_option linter.unusedVariables false

/-! ## 1. The iterated derivatives of `sin` -/

/-- `∂^m sin x = sin (x + m π/2)`. -/
theorem cab_iteratedDeriv_sin_eq (m : ℕ) :
    iteratedDeriv m Real.sin = fun x : ℝ => Real.sin (x + (m : ℝ) * (Real.pi / 2)) := by
  induction m with
  | zero => funext x; simp
  | succ m ih =>
    funext x
    rw [iteratedDeriv_succ, ih]
    have h1 : HasDerivAt (fun x : ℝ => Real.sin (x + (m : ℝ) * (Real.pi / 2)))
        (Real.cos (x + (m : ℝ) * (Real.pi / 2)) * 1) x :=
      ((hasDerivAt_id x).add_const _).sin
    rw [h1.deriv, mul_one, ← Real.sin_add_pi_div_two]
    congr 1
    push_cast
    ring

/-! ## 2. The all-order bounds on the rescaled angular coefficient `rhoM lam`

`rhoM lam u = lam · sin (2 (u + 1)/lam)` is the coefficient of the operator `D_θ` in the
rescaled variable `u = lam θ - 1`.  On the transition layer `u ∈ [0,1]` all its derivatives are
bounded by `4 · 2^m`, *uniformly in `lam ≥ 1`*. -/

theorem cab_iteratedDeriv_rhoM_bound_all {lam : ℝ} (hlam : 1 ≤ lam) (m : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : |iteratedDeriv m (rhoM lam) u| ≤ 4 * 2 ^ m := by
  have hpos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    rw [iteratedDeriv_zero, pow_zero, mul_one]
    have hpt : rhoM lam u = lam * Real.sin (2 * (u + 1) / lam) := by simp only [rhoM]
    rw [hpt, abs_mul, abs_of_pos hpos]
    have htpos : 0 ≤ 2 * (u + 1) / lam := div_nonneg (by linarith [hu.1]) (le_of_lt hpos)
    have hb : |Real.sin (2 * (u + 1) / lam)| ≤ 2 * (u + 1) / lam :=
      le_trans (Real.abs_sin_le_abs (x := 2 * (u + 1) / lam)) (le_of_eq (abs_of_nonneg htpos))
    calc lam * |Real.sin (2 * (u + 1) / lam)| ≤ lam * (2 * (u + 1) / lam) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hpos)
      _ = 2 * (u + 1) := by field_simp
      _ ≤ 4 := by linarith [hu.2]
  · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hmpos)
    subst hm'
    have hfun : rhoM lam = fun u : ℝ => lam * Real.sin ((2 / lam) * u + (2 / lam)) := by
      funext u
      simp only [rhoM]
      rw [show 2 * (u + 1) / lam = (2 / lam) * u + (2 / lam) from by field_simp]
    rw [hfun]
    have hconst : iteratedDeriv (m' + 1) (fun u : ℝ => lam * Real.sin ((2 / lam) * u + (2 / lam)))
          u = lam * iteratedDeriv (m' + 1)
            (fun u : ℝ => Real.sin ((2 / lam) * u + (2 / lam))) u :=
      iteratedDeriv_const_mul lam (by fun_prop)
    rw [hconst]
    have hcomp : iteratedDeriv (m' + 1) (fun u : ℝ => Real.sin ((2 / lam) * u + (2 / lam))) u
        = (2 / lam) ^ (m' + 1) * iteratedDeriv (m' + 1) Real.sin ((2 / lam) * u + (2 / lam)) := by
      have hcd : ContDiff ℝ ((m' + 1 : ℕ) : WithTop ℕ∞)
          (fun y : ℝ => Real.sin (y + (2 / lam))) :=
        Real.contDiff_sin.comp (contDiff_id.add contDiff_const)
      have h1 := congrFun (iteratedDeriv_comp_const_mul (n := m' + 1) (c := 2 / lam)
        (f := fun y : ℝ => Real.sin (y + (2 / lam))) hcd) u
      have h2 := congrFun (iteratedDeriv_comp_add_const (m' + 1) Real.sin (2 / lam)) ((2 / lam) * u)
      simp only [h2] at h1
      simpa using h1
    rw [hcomp]
    have hS : |iteratedDeriv (m' + 1) Real.sin ((2 / lam) * u + (2 / lam))| ≤ 1 := by
      rw [cab_iteratedDeriv_sin_eq]
      exact Real.abs_sin_le_one _
    rw [abs_mul, abs_mul, abs_of_pos hpos,
      abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 / lam) (m' + 1))]
    have h2div : 2 / lam ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
    have hpow2 : (2 / lam) ^ m' ≤ 2 ^ m' := pow_le_pow_left₀ (by positivity) h2div m'
    have hkey : lam * (2 / lam) ^ (m' + 1) = 2 * (2 / lam) ^ m' := by
      rw [pow_succ]
      field_simp
    calc lam * ((2 / lam) ^ (m' + 1)
          * |iteratedDeriv (m' + 1) Real.sin ((2 / lam) * u + (2 / lam))|)
        ≤ lam * ((2 / lam) ^ (m' + 1) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (pow_nonneg (by positivity) _))
            (le_of_lt hpos)
      _ = 2 * (2 / lam) ^ m' := by rw [mul_one, hkey]
      _ ≤ 2 * 2 ^ m' := mul_le_mul_of_nonneg_left hpow2 (by norm_num)
      _ = 2 ^ (m' + 1) := by rw [pow_succ]; ring
      _ ≤ 4 * 2 ^ (m' + 1) := by
          have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (m' + 1); linarith

/-! ## 3. The abstract iterate bound with an explicit constant

This is `exists_Eiter_smoothTransition_bound` with the witness `K` made explicit: it is
`k ↦ max (Cbnd M B k 0) 1`, which depends only on `M` and `B`, *not* on the coefficient `ρ`. -/

theorem cab_eiter_explicit_bound {ρ : ℝ → ℝ} {M B : ℕ → ℝ}
    (hMnn : ∀ m, 0 ≤ M m) (hBnn : ∀ m, 0 ≤ B m)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hM : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m ρ u| ≤ M m)
    (hB : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m Real.smoothTransition u| ≤ B m) :
    ∀ (k : ℕ) (v : ℝ), |Eiter k ρ Real.smoothTransition v| ≤ max (Cbnd M B k 0) 1 := by
  intro k v
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Eiter_zero]
    have hσ : |Real.smoothTransition v| ≤ 1 := by
      rcases le_or_gt v 0 with hv | hv
      · rw [Real.smoothTransition.zero_of_nonpos hv, abs_zero]
        norm_num
      rcases le_or_gt 1 v with hv1 | hv1
      · rw [Real.smoothTransition.one_of_one_le hv1, abs_one]
      · rw [abs_of_nonneg (Real.smoothTransition.nonneg v)]
        exact Real.smoothTransition.le_one v
    exact le_trans hσ (le_max_right _ _)
  · by_cases hv : v ∈ Set.Icc (0 : ℝ) 1
    · have h := Eiter_deriv_bound_all hMnn hBnn hρ contDiff_smoothTransition hM hB k 0 v hv
      simp only [iteratedDeriv_zero] at h
      exact le_trans h (le_max_left _ _)
    · rw [Set.mem_Icc, not_and_or] at hv
      have hzero : Eiter k ρ Real.smoothTransition v = 0 := by
        rcases hv with hv | hv
        · have hv' : v < 0 := lt_of_not_ge hv
          exact Eiter_eq_zero_of_open_const isOpen_Iio (Set.mem_Iio.mpr hv') (fun w hw => by
            rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hw),
              Real.smoothTransition.zero_of_nonpos (le_of_lt hv')]) k hkpos v
            (Set.mem_Iio.mpr hv')
        · have hv' : 1 < v := lt_of_not_ge hv
          exact Eiter_eq_zero_of_open_const isOpen_Ioi (Set.mem_Ioi.mpr hv') (fun w hw => by
            rw [Real.smoothTransition.one_of_one_le (le_of_lt hw),
              Real.smoothTransition.one_of_one_le (le_of_lt hv')]) k hkpos v
            (Set.mem_Ioi.mpr hv')
      rw [hzero, abs_zero]
      exact le_trans zero_le_one (le_max_right _ _)

/-! ## 4. The degenerate scale `n = 0` -/

/-- All the `D_θ`-iterates of the zero function vanish. -/
theorem cab_DthIter_zero_fun (a : ℕ) : Work.Spaces.DthIter a (0 : ℝ → ℝ → ℝ) = 0 := by
  induction a with
  | zero => rfl
  | succ a ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth, Pi.zero_apply]
      rw [deriv_const, mul_zero]

/-- At scale `0` the angular cut-off vanishes identically. -/
theorem cab_zetaR_zero (z θ : ℝ) : zetaR 0 θ = 0 := by
  have h1 : (↑(0 : ℕ) : ℝ) * θ - 1 ≤ 0 := by norm_num
  have h2 : (↑(0 : ℕ) : ℝ) * (Real.pi / 2 - θ) - 1 ≤ 0 := by norm_num
  simp only [zetaR, cut01]
  rw [Real.smoothTransition.zero_of_nonpos h1, Real.smoothTransition.zero_of_nonpos h2, zero_mul]

/-! ## 5. The main statement -/

theorem estZetaBound : ∃ L : ℕ → ℝ, (∀ a : ℕ, 0 ≤ L a) ∧
    ∀ (n a : ℕ) (z θ : ℝ),
      |Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ) z θ| ≤ L a := by
  obtain ⟨B, hBnn, hB⟩ := exists_iteratedDeriv_smoothTransition_bound
  set M : ℕ → ℝ := fun m => 4 * 2 ^ m with hMdef
  have hMnn : ∀ m : ℕ, 0 ≤ M m := fun m => by rw [hMdef]; positivity
  have hMbd : ∀ (lam : ℝ), 1 ≤ lam → ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m (rhoM lam) u| ≤ M m := fun lam hlam m u hu => by
    rw [hMdef]; exact cab_iteratedDeriv_rhoM_bound_all hlam m hu
  have heng : ∀ (lam : ℝ) (hlam : 1 ≤ lam) (k : ℕ) (v : ℝ),
      |Eiter k (rhoM lam) Real.smoothTransition v| ≤ max (Cbnd M B k 0) 1 := fun lam hlam k v =>
    cab_eiter_explicit_bound hMnn hBnn (contDiff_rhoM lam) (hMbd lam hlam) hB k v
  have heng' : ∀ (lam : ℝ) (hlam : 1 ≤ lam) (k : ℕ) (v : ℝ),
      |Eiter k (fun u => -(rhoM lam u)) Real.smoothTransition v| ≤ max (Cbnd M B k 0) 1 :=
    fun lam hlam k v => cab_eiter_explicit_bound hMnn hBnn
      (fun n => (contDiff_rhoM lam n).neg) (fun m u hu => by
        change |iteratedDeriv m (-(rhoM lam)) u| ≤ M m
        rw [iteratedDeriv_neg, abs_neg]; exact hMbd lam hlam m u hu) hB k v
  set K : ℕ → ℝ := fun c => max (Cbnd M B c 0) 1 with hKdef
  have hKnn : ∀ c : ℕ, 0 ≤ K c := fun c => le_trans zero_le_one (le_max_right _ _)
  have hLnn : ∀ a : ℕ, 0 ≤ 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 := fun a => by
    have h : (0 : ℝ) ≤ 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  refine ⟨fun a => 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2, hLnn, ?_⟩
  intro n a z θ
  have hL : (1 : ℝ) ≤ 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 := by
    have h : (0 : ℝ) ≤ 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hz0 : (fun _ θ : ℝ => zetaR 0 θ) = (0 : ℝ → ℝ → ℝ) := by
      funext z θ; exact cab_zetaR_zero z θ
    rw [hz0, cab_DthIter_zero_fun a]
    simp only [Pi.zero_apply, abs_zero]
    linarith
  · set lam : ℝ := (n : ℝ) with hlamdef
    have hlam1 : 1 ≤ lam := by rw [hlamdef]; exact_mod_cast hnpos
    have hlamne : lam ≠ 0 := by linarith
    set u : ℝ → ℝ := fun θ' : ℝ => Real.smoothTransition (lam * θ' + (-1)) with hudef
    set v : ℝ → ℝ := fun θ' : ℝ =>
      Real.smoothTransition ((-lam) * θ' + (lam * (Real.pi / 2) - 1)) with hvdef
    have hfun : (fun θ' : ℝ => zetaR n θ') = u * v := by
      funext θ'
      have h1 : (n : ℝ) * θ' - 1 = lam * θ' + (-1) := by rw [← hlamdef]; ring
      have h2 : (n : ℝ) * (Real.pi / 2 - θ') - 1 = (-lam) * θ' + (lam * (Real.pi / 2) - 1) := by
        rw [← hlamdef]; ring
      rw [hudef, hvdef]
      simp only [zetaR, cut01, Pi.mul_apply, h1, h2]
    have hu : ∀ m : ℕ, ContDiff ℝ m u := by
      intro m; rw [hudef]; exact (contDiff_smoothTransition m).comp (contDiff_affine lam (-1) m)
    have hv : ∀ m : ℕ, ContDiff ℝ m v := by
      intro m; rw [hvdef]
      exact (contDiff_smoothTransition m).comp (contDiff_affine (-lam) _ m)
    have hub : ∀ b : ℕ, |Work.Spaces.Lop^[b] u θ| ≤ K b := by
      intro b
      rw [hudef, Lop_iter_affine_st lam (-1) hlamne b θ, coef_affine_eq_rhoM lam]
      exact heng lam hlam1 b (lam * θ + (-1))
    have hvb : ∀ c : ℕ, |Work.Spaces.Lop^[c] v θ| ≤ K c := by
      intro c
      rw [hvdef, Lop_iter_affine_st (-lam) (lam * (Real.pi / 2) - 1) (by simpa using hlamne) c θ,
        coef_affine_eq_neg_rhoM lam hlamne]
      exact heng' lam hlam1 c ((-lam) * θ + (lam * (Real.pi / 2) - 1))
    rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop a (fun _ θ' : ℝ => zetaR n θ') z) θ, hfun,
      Lop_iter_mul hu hv a θ]
    rw [show (fun a : ℕ => 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2) a
        = 1 + 2 ^ a * (∑ c ∈ Finset.range (a + 1), K c) ^ 2 from rfl]
    set S : ℝ := ∑ c ∈ Finset.range (a + 1), K c with hSdef
    have hSnn : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg (fun c _ => hKnn c)
    calc |∑ b ∈ Finset.range (a + 1), (a.choose b : ℝ) *
            (Work.Spaces.Lop^[b] u θ * Work.Spaces.Lop^[a - b] v θ)|
        ≤ ∑ b ∈ Finset.range (a + 1), |(a.choose b : ℝ) *
            (Work.Spaces.Lop^[b] u θ * Work.Spaces.Lop^[a - b] v θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ Finset.range (a + 1), (a.choose b : ℝ) * (S * S) := by
          apply Finset.sum_le_sum
          intro b hb
          have hb' : b ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          have hKb : K b ≤ S :=
            Finset.single_le_sum (fun c _ => hKnn c) (Finset.mem_range.mpr (by omega))
          have hKab : K (a - b) ≤ S :=
            Finset.single_le_sum (fun c _ => hKnn c) (Finset.mem_range.mpr (by omega))
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (a.choose b)), abs_mul]
          refine le_trans (mul_le_mul_of_nonneg_left
            (mul_le_mul (hub b) (hvb (a - b)) (abs_nonneg _) (hKnn b)) (Nat.cast_nonneg _)) ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul hKb hKab (hKnn _) hSnn) (Nat.cast_nonneg _)
      _ = (∑ b ∈ Finset.range (a + 1), (a.choose b : ℝ)) * (S * S) :=
          (Finset.sum_mul (Finset.range (a + 1)) (fun b => (a.choose b : ℝ)) (S * S)).symm
      _ = (2 : ℝ) ^ a * (S * S) := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ = (2 : ℝ) ^ a * S ^ 2 := by ring
      _ ≤ 1 + 2 ^ a * S ^ 2 := by linarith

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Fstar_approx =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false

/-! ## The smoothness, sign and size of the moment profile -/

/-- `rhoAux θ = cut01 (2θ - 2) * cut01 (3 - 2θ)` is nonnegative everywhere. -/
private theorem rhoAux_nonneg (θ : ℝ) : 0 ≤ rhoAux θ := by
  rw [rhoAux, cut01]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- `rhoAux` is strictly positive on its support `(1, 3/2)`. -/
private theorem rhoAux_pos_of_mem {θ : ℝ} (h0 : 1 < θ) (h1 : θ < 3 / 2) : 0 < rhoAux θ := by
  rw [rhoAux, cut01]
  exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
    (Real.smoothTransition.pos_of_pos (by linarith))

/-- `sinθcos²θ` is nonnegative on the closed quadrant `[0, π/2]`. -/
private theorem sinCos2_nonneg_of_mem {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [Real.pi_pos]⟩) (sq_nonneg _)

/-- `sinθcos²θ` is strictly positive on the open quadrant `(0, π/2)`. -/
private theorem sinCos2_pos_of_mem {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    0 < Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_pos (Real.sin_pos_of_mem_Ioo ⟨h0, by linarith [Real.pi_pos]⟩)
    (pow_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩) 2)

/-- The integrand `rhoAux · sinθcos²θ` of the normalisation constant is continuous. -/
private theorem continuous_rhoAux_mul_sinCos2 :
    Continuous fun θ : ℝ => rhoAux θ * Work.Elliptic.sinCos2 θ := by
  simp only [rhoAux, cut01, Work.Elliptic.sinCos2]
  fun_prop

/-! ## The normalisation `∫_θ rho θ · sinθcos²θ = 1` -/

/-- The normalisation constant `crho = ∫_θ rhoAux θ · sinθcos²θ` is positive: the integrand
vanishes off `[1, 3/2]`, is nonnegative, and is strictly positive at `θ = 5/4`. -/
theorem crho_pos : 0 < crho := by
  have hone : 0 < ∫ θ in (0 : ℝ)..(π / 2), rhoAux θ * Work.Elliptic.sinCos2 θ := by
    refine intervalIntegral.integral_pos (by linarith [Real.pi_pos])
      continuous_rhoAux_mul_sinCos2.continuousOn
      (fun x hx => mul_nonneg (rhoAux_nonneg x)
        (sinCos2_nonneg_of_mem (le_of_lt hx.1) hx.2)) ?_
    refine ⟨5 / 4, ⟨by norm_num, by linarith [Real.pi_gt_three]⟩, ?_⟩
    exact mul_pos (rhoAux_pos_of_mem (by norm_num) (by norm_num))
      (sinCos2_pos_of_mem (by norm_num) (by linarith [Real.pi_gt_three]))
  rw [show crho = ∫ θ in (0 : ℝ)..(π / 2), rhoAux θ * Work.Elliptic.sinCos2 θ from ?_]
  exact hone
  rw [crho, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- `crho ≠ 0`, so that the normalised profile `rho = crho⁻¹ * rhoAux` is nontrivial. -/
theorem crho_ne_zero : crho ≠ 0 := ne_of_gt crho_pos

/-- **The normalisation of the moment profile**: `∫_θ rho θ · sinθcos²θ = 1`. -/
theorem rho_moment : ∫ θ in Work.Spaces.Iθ, rho θ * Work.Elliptic.sinCos2 θ = 1 := by
  have h : ∫ θ in Work.Spaces.Iθ, rho θ * Work.Elliptic.sinCos2 θ
      = crho⁻¹ * ∫ θ in Work.Spaces.Iθ, rhoAux θ * Work.Elliptic.sinCos2 θ := by
    rw [show (fun θ : ℝ => rho θ * Work.Elliptic.sinCos2 θ)
        = fun θ : ℝ => crho⁻¹ * (rhoAux θ * Work.Elliptic.sinCos2 θ) from by
      funext θ
      simp only [rho]
      ring]
    rw [MeasureTheory.integral_const_mul]
  rw [h]
  show crho⁻¹ * crho = 1
  exact inv_mul_cancel₀ crho_ne_zero

/-! ## The angular moment of the approximation -/

theorem Fstar_approx {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} (hF : Work.Spaces.HkMem α k F)
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.FTS.PhiStar.Honesty.CptApp.approx n F) z = 0 := by
  -- neither `HkMem α k F` nor `2 ≤ n` is needed for this identity
  have _ := hF
  have _ := hn
  intro z hz
  -- the `rho`-piece of the integrand is always integrable (continuous with compact support)
  have hYint : MeasureTheory.Integrable
      (fun θ : ℝ => lam n F z * (rho θ * Work.Elliptic.sinCos2 θ))
      (volume.restrict Work.Spaces.Iθ) := by
    have h0 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => rhoAux θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        continuous_rhoAux_mul_sinCos2.continuousOn
    have h1 : MeasureTheory.Integrable
        (fun θ : ℝ => crho⁻¹ * (rhoAux θ * Work.Elliptic.sinCos2 θ))
        (volume.restrict Work.Spaces.Iθ) := h0.const_mul crho⁻¹
    have h2 : MeasureTheory.Integrable
        (fun θ : ℝ => rho θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h1.congr (Filter.Eventually.of_forall (fun θ => by simp only [rho]; ring))
    exact h2.const_mul (lam n F z)
  -- the two integrals making up the moment
  have hXval : ∫ θ in Work.Spaces.Iθ, zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ
      = lam n F z := rfl
  have hYval : ∫ θ in Work.Spaces.Iθ, lam n F z * (rho θ * Work.Elliptic.sinCos2 θ)
      = lam n F z := by
    rw [MeasureTheory.integral_const_mul, rho_moment, mul_one]
  -- the truncated moment integral vanishes
  have hmain : ∫ θ in Work.Spaces.Iθ,
      (zetaR n θ * F z θ - lam n F z * rho θ) * Work.Elliptic.sinCos2 θ = 0 := by
    rw [show (fun θ : ℝ => (zetaR n θ * F z θ - lam n F z * rho θ)
          * Work.Elliptic.sinCos2 θ)
        = (fun θ : ℝ => (zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ)
            - (lam n F z * (rho θ * Work.Elliptic.sinCos2 θ))) from by
      funext θ
      ring]
    by_cases hX : MeasureTheory.Integrable
        (fun θ : ℝ => zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ)
    · rw [MeasureTheory.integral_sub hX hYint, hXval, hYval]
      ring
    · -- `X` is not integrable: then `∫ X = 0` and `∫ (X - Y) = 0`, so the identity is trivial
      have hXY : ¬ MeasureTheory.Integrable
          (fun θ : ℝ => (zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ)
            - (lam n F z * (rho θ * Work.Elliptic.sinCos2 θ)))
          (volume.restrict Work.Spaces.Iθ) := by
        intro h
        refine hX ((h.add hYint).congr (Filter.Eventually.of_forall (fun θ => ?_)))
        show (zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ
            - lam n F z * (rho θ * Work.Elliptic.sinCos2 θ))
          + lam n F z * (rho θ * Work.Elliptic.sinCos2 θ)
          = zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ
        ring
      rw [MeasureTheory.integral_undef hXY]
  rw [Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => approx n F z θ * Work.Elliptic.sinCos2 θ)
      = (fun θ : ℝ => chiR n z * ((zetaR n θ * F z θ - lam n F z * rho θ)
          * Work.Elliptic.sinCos2 θ)) from by
    funext θ
    simp only [approx]
    ring]
  rw [MeasureTheory.integral_const_mul, hmain, mul_zero]

end Work.FTS.PhiStar.Honesty.CptApp
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.LamAux

local notation "𝕋" => Real.smoothTransition

/-! ## 1. The two steps whose product is `chiR n`, in affine form -/

/-- The lower step of `chiR n`: `𝕋 (n z − 1)`, in the affine form `𝕋 (λ z + a)` with
`λ = n`, `a = −1`. -/
def psiLo (n : ℕ) (z : ℝ) : ℝ := 𝕋 ((n : ℝ) * z + (-1))

/-- The upper step of `chiR n`: `𝕋 (2 − z/n)`, in the affine form `𝕋 (λ z + a)` with
`λ = −1/n`, `a = 2` (valid also for `n = 0`, where both expressions are the constant `2`). -/
def psiHi (n : ℕ) (z : ℝ) : ℝ := 𝕋 ((-(n : ℝ)⁻¹) * z + 2)

/-- **The factorisation of `chiR n`.** -/
theorem chiR_eq_psiLo_mul_psiHi (n : ℕ) :
    Work.FTS.PhiStar.Honesty.CptApp.chiR n = fun z => psiLo n z * psiHi n z := by
  funext z
  simp only [Work.FTS.PhiStar.Honesty.CptApp.chiR, Work.FTS.PhiStar.Honesty.CptApp.cut01,
    psiLo, psiHi]
  have h1 : (n : ℝ) * z - 1 = (n : ℝ) * z + (-1) := by ring
  have h2 : (2 : ℝ) - z / (n : ℝ) = -(n : ℝ)⁻¹ * z + 2 := by
    rw [div_eq_mul_inv]; ring
  rw [h1, h2]

theorem contDiff_psiLo (n : ℕ) : ContDiff ℝ Work.Stability.smoothOrder (psiLo n) := by
  have hlin : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => (n : ℝ) * z + (-1)) :=
    ((contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (n : ℝ))).mul
        contDiff_id).add
      (contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (-1 : ℝ)))
  exact Real.smoothTransition.contDiff.comp hlin

theorem contDiff_psiHi (n : ℕ) : ContDiff ℝ Work.Stability.smoothOrder (psiHi n) := by
  have hlin : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => (-(n : ℝ)⁻¹) * z + 2) :=
    ((contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (-(n : ℝ)⁻¹))).mul
        contDiff_id).add
      (contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (2 : ℝ)))
  exact Real.smoothTransition.contDiff.comp hlin

/-! ## 2. The weighted derivatives of a rescaled step -/

theorem weighted_deriv_exp (F : ℝ → ℝ) (hF : ∀ m : ℕ, ContDiff ℝ m F) (lam a₀ : ℝ) :
    ∀ (k : ℕ) (z : ℝ), z ^ k * iteratedDeriv k (fun z => F (lam * z + a₀)) z
      = (lam * z + a₀ - a₀) ^ k * iteratedDeriv k F (lam * z + a₀) := by
  intro k z
  have hchain : iteratedDeriv k (fun z => F (lam * z + a₀)) z
      = lam ^ k * iteratedDeriv k F (lam * z + a₀) :=
    Work.FTS.GalBasis.cc.iteratedDeriv_comp_mul_add F hF lam a₀ k z
  rw [hchain, ← mul_assoc, ← mul_pow,
    show z * lam = lam * z + a₀ - a₀ by ring]

/-- The weighted derivatives of the lower step, uniformly in `n`. -/
theorem weighted_deriv_psiLo {A : ℕ → ℝ}
    (hA : ∀ (a : ℕ) (u : ℝ), |(u - (-1)) ^ a * iteratedDeriv a 𝕋 u| ≤ A a) :
    ∀ (n k : ℕ) (z : ℝ), |z ^ k * iteratedDeriv k (psiLo n) z| ≤ A k := by
  intro n k z
  show |z ^ k * iteratedDeriv k (fun z => 𝕋 ((n : ℝ) * z + (-1))) z| ≤ A k
  rw [weighted_deriv_exp 𝕋 Work.FTS.GalBasis.cc.contDiff_smoothTransition (n : ℝ) (-1) k z]
  exact hA k ((n : ℝ) * z + (-1))

/-- The weighted derivatives of the upper step, uniformly in `n`. -/
theorem weighted_deriv_psiHi {B : ℕ → ℝ}
    (hB : ∀ (b : ℕ) (v : ℝ), |(v - 2) ^ b * iteratedDeriv b 𝕋 v| ≤ B b) :
    ∀ (n k : ℕ) (z : ℝ), |z ^ k * iteratedDeriv k (psiHi n) z| ≤ B k := by
  intro n k z
  show |z ^ k * iteratedDeriv k (fun z => 𝕋 ((-(n : ℝ)⁻¹) * z + 2)) z| ≤ B k
  rw [weighted_deriv_exp 𝕋 Work.FTS.GalBasis.cc.contDiff_smoothTransition (-(n : ℝ)⁻¹) 2 k z]
  exact hB k ((-(n : ℝ)⁻¹) * z + 2)

/-! ## 3. The product rule for the weighted derivatives -/

/-- **Binomial product bound.** -/
theorem weighted_deriv_prod {A B : ℕ → ℝ}
    (hAnn : ∀ a : ℕ, 0 ≤ A a)
    (hA : ∀ (a : ℕ) (u : ℝ), |(u - (-1)) ^ a * iteratedDeriv a 𝕋 u| ≤ A a)
    (hB : ∀ (b : ℕ) (v : ℝ), |(v - 2) ^ b * iteratedDeriv b 𝕋 v| ≤ B b) :
    ∀ (n k : ℕ) (z : ℝ),
      |z ^ k * iteratedDeriv k (fun z => psiLo n z * psiHi n z) z| ≤
        ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * A a * B (k - a) := by
  intro n k z
  have hsm1 : ContDiff ℝ (k : WithTop ℕ∞) (psiLo n) :=
    (contDiff_psiLo n).of_le (by simp)
  have hsm2 : ContDiff ℝ (k : WithTop ℕ∞) (psiHi n) :=
    (contDiff_psiHi n).of_le (by simp)
  have hkey : iteratedDeriv k (fun z => psiLo n z * psiHi n z) z
      = ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ)
          * iteratedDeriv a (psiLo n) z * iteratedDeriv (k - a) (psiHi n) z :=
    iteratedDeriv_mul hsm1.contDiffAt hsm2.contDiffAt
  have hsplit : z ^ k * iteratedDeriv k (fun z => psiLo n z * psiHi n z) z
      = ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ)
          * ((z ^ a * iteratedDeriv a (psiLo n) z)
             * (z ^ (k - a) * iteratedDeriv (k - a) (psiHi n) z)) := by
    rw [hkey, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hzk : z ^ a * z ^ (k - a) = z ^ k := by rw [← pow_add, Nat.add_sub_cancel' ha']
    rw [← hzk]
    ring
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun a _ => ?_)
  have hX : |z ^ a * iteratedDeriv a (psiLo n) z| ≤ A a := weighted_deriv_psiLo hA n a z
  have hY : |z ^ (k - a) * iteratedDeriv (k - a) (psiHi n) z| ≤ B (k - a) :=
    weighted_deriv_psiHi hB n (k - a) z
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.choose a))]
  calc (k.choose a : ℝ) * (|z ^ a * iteratedDeriv a (psiLo n) z|
        * |z ^ (k - a) * iteratedDeriv (k - a) (psiHi n) z|)
      ≤ (k.choose a : ℝ) * (A a * B (k - a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hX hY (abs_nonneg _) (hAnn a))
          (Nat.cast_nonneg _)
    _ = (k.choose a : ℝ) * A a * B (k - a) := by ring

/-! ## 4. The Stirling assembly and the main statement -/

/-- **The reduction to weighted plain derivatives.** -/
theorem exists_cutRadialBound_aux {A B : ℕ → ℝ} (hA1 : ∀ a : ℕ, 1 ≤ A a)
    (hB1 : ∀ b : ℕ, 1 ≤ B b)
    (hA : ∀ (a : ℕ) (u : ℝ), |(u - (-1)) ^ a * iteratedDeriv a 𝕋 u| ≤ A a)
    (hB : ∀ (b : ℕ) (v : ℝ), |(v - 2) ^ b * iteratedDeriv b 𝕋 v| ≤ B b) :
    ∃ K : ℕ → ℝ, (∀ b : ℕ, 0 ≤ K b) ∧
      ∀ (n b : ℕ) (z θ : ℝ),
        |Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z)
          z θ| ≤ K b := by
  have hAnn : ∀ a : ℕ, 0 ≤ A a := fun a => le_trans zero_le_one (hA1 a)
  have hBnn : ∀ b : ℕ, 0 ≤ B b := fun b => le_trans zero_le_one (hB1 b)
  refine ⟨fun b => ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
      * (∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * A a * B (k - a)), ?_, ?_⟩
  · intro b
    refine Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) ?_
    refine Finset.sum_nonneg fun a _ => ?_
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hAnn a)) (hBnn (k - a))
  · intro n b z θ
    have hm : (fun z (_ : ℝ) => Work.FTS.PhiStar.Honesty.CptApp.chiR n z)
        = Work.Coercivity.CommutZ.mulZ (fun z => psiLo n z * psiHi n z) := by
      funext z' _
      simp only [Work.Coercivity.CommutZ.mulZ_apply]
      exact congrFun (chiR_eq_psiLo_mul_psiHi n) z'
    rw [hm, Work.Coercivity.CommutZ.DzIter_mulZ b (fun z => psiLo n z * psiHi n z)]
    simp only [Work.Coercivity.CommutZ.mulZ_apply]
    have hsm : ContDiff ℝ Work.Stability.smoothOrder (fun z => psiLo n z * psiHi n z) :=
      (contDiff_psiLo n).mul (contDiff_psiHi n)
    have hexp := congrFun
      (Work.FTS.LocData.DzIterZ_eq_sum_scoef (fun z => psiLo n z * psiHi n z) hsm b) z
    rw [hexp]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Work.Spaces.scoef b k))]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact weighted_deriv_prod hAnn hA hB n k z

/-- **The `D_z`-jets of `chiR n` are uniformly bounded in `n`** (copy of
`CptApp.cutRadialBound` with the `cutBasic` import removed). -/
theorem chiR_dzIter_boundAux : ∃ K : ℕ → ℝ, (∀ b : ℕ, 0 ≤ K b) ∧
    ∀ (n b : ℕ) (z θ : ℝ),
      |Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z)
        z θ| ≤ K b := by
  obtain ⟨A, hA1, hA⟩ := Work.FTS.GalBasis.cc.exists_weighted_smoothTransition_bound (-1)
  obtain ⟨B, hB1, hB⟩ := Work.FTS.GalBasis.cc.exists_weighted_smoothTransition_bound 2
  exact exists_cutRadialBound_aux hA1 hB1 hA hB

end Work.FTS.PhiStar.Honesty.CptApp.LamAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrableOn_slice_L2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- The single `D_z`-summand of the `ℋ^k`-integrand is integrable in `z` once the angular
slice integral is taken:  for `F` smooth on the open quadrant and `F ∈ ℋ^k`,
`z ↦ ∫_θ (D_z^i F · w / sin(2θ)^{η/2})²` is integrable on `Iz`, for every `i ≤ k`.

The proof is a pure domination argument, exactly as in
`Work.FTS.EllipticEst.integrableOn_zSummand` and `Work.Blocks.slice_integrable_of_bound`:

* pointwise, `(D_z^iF · w/sin^{η/2})² ≤ HkIntegrand α k F` (`Work.Spaces.sq_le_HkIntegrand_z`),
  so for each `z ∈ Iz` the slice integral is bounded by `∫_θ HkIntegrand α k F z θ`;
* the majorant `z ↦ ∫_θ HkIntegrand α k F z θ` is integrable on `Iz` by `HkMem α k F`;
* the marginal `z ↦ ∫_θ (D_z^iF · w/sin^{η/2})²` is a.e. strongly measurable because the
  uncurried integrand is continuous on the open quadrant, hence a.e. strongly measurable for
  the product of the restricted measures (`Work.Spaces.aesm_of_continuousOn_Qd`), and
  `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` integrates out `θ`. -/
theorem integrableOn_slice_L2 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    {i : ℕ} (hi : i ≤ k) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))^2)
      Work.Spaces.Iz := by
  -- a.e. strong measurability of the marginal, from continuity of the integrand on `Q0`
  have hX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ ((hsm.continuousOn_summand i).pow 2)
  have hInner : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa using h
  refine MeasureTheory.Integrable.mono' hF.2 hInner ?_
  -- the pointwise domination, for a.e. `z` (namely for `z ∈ Iz`)
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) (fun z hz => ?_)
  have hle : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hF.1 z hz)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.sq_le_HkIntegrand_z α k F z θ i hi)
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
  exact hle

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Omega_iInter_subset_boundary =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

/-- For every real `c > 0` and every `a : ℝ` there is a natural number `m ≥ 1` with
`a < m` (so that `m < a` fails) and `2 / m ≤ c` (so that `p < 2/m` fails for every
`p ≥ c`). -/
lemma exists_nat_two_div_le {a c : ℝ} (hc : 0 < c) :
    ∃ m : ℕ, 1 ≤ m ∧ a < (m : ℝ) ∧ 2 / (m : ℝ) ≤ c := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (a + 1) (2 / c))
  refine ⟨max N 1, le_max_right _ _, ?_, ?_⟩
  · have h1 : a + 1 ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
    have h2 : (N : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left N 1
    linarith
  · have h2 : 2 / c ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
    have h3 : (2 / c : ℝ) ≤ ((max N 1 : ℕ) : ℝ) :=
      le_trans h2 (by exact_mod_cast le_max_left N 1)
    have hmpos : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) := by
      have h4 : (1 : ℕ) ≤ max N 1 := le_max_right _ _
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one h4
    have h5 : 2 ≤ ((max N 1 : ℕ) : ℝ) * c := (div_le_iff₀ hc).mp h3
    exact (div_le_iff₀ hmpos).mpr (by linarith)

theorem Omega_iInter_subset_boundary :
    (⋂ n : ℕ, (Work.FTS.PhiStar.Honesty.CptApp.Omega (n + 1) ∩ Work.Spaces.Dom))
      ⊆ ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
          ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) := by
  intro p hp
  rw [Set.mem_iInter] at hp
  have hDom : p ∈ Work.Spaces.Dom := (hp 0).2
  simp only [Work.Spaces.Dom, Work.Spaces.Iz, Work.Spaces.Iθ, Set.mem_prod, Set.mem_Ici,
    Set.mem_Icc] at hDom
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hnot
  obtain ⟨⟨ha, hb⟩, hc⟩ := hnot
  have h1 : 0 < p.1 := lt_of_le_of_ne hDom.1 (Ne.symm ha)
  have h2 : 0 < p.2 := lt_of_le_of_ne hDom.2.1 (Ne.symm hb)
  have h3 : p.2 < Real.pi / 2 := lt_of_le_of_ne hDom.2.2 hc
  have hcpos : 0 < min (min p.1 p.2) (Real.pi / 2 - p.2) :=
    lt_min (lt_min h1 h2) (by linarith)
  obtain ⟨m, hm1, hma, hmc⟩ := exists_nat_two_div_le (a := p.1)
    (c := min (min p.1 p.2) (Real.pi / 2 - p.2)) hcpos
  have hc_le_1 : min (min p.1 p.2) (Real.pi / 2 - p.2) ≤ p.1 :=
    le_trans (min_le_left (min p.1 p.2) (Real.pi / 2 - p.2)) (min_le_left p.1 p.2)
  have hc_le_2 : min (min p.1 p.2) (Real.pi / 2 - p.2) ≤ p.2 :=
    le_trans (min_le_left (min p.1 p.2) (Real.pi / 2 - p.2)) (min_le_right p.1 p.2)
  have hc_le_3 : min (min p.1 p.2) (Real.pi / 2 - p.2) ≤ Real.pi / 2 - p.2 :=
    min_le_right _ _
  have hle1 : 2 / (m : ℝ) ≤ p.1 := le_trans hmc hc_le_1
  have hle2 : 2 / (m : ℝ) ≤ p.2 := le_trans hmc hc_le_2
  have hle3 : 2 / (m : ℝ) ≤ Real.pi / 2 - p.2 := le_trans hmc hc_le_3
  have hmem : p ∈ Work.FTS.PhiStar.Honesty.CptApp.Omega m := by
    have h := (hp (m - 1)).1
    rwa [Nat.sub_add_cancel hm1] at h
  simp only [Work.FTS.PhiStar.Honesty.CptApp.Omega, Set.mem_ofPred_eq] at hmem
  rcases hmem with h | h | h | h
  · linarith
  · linarith
  · linarith
  · linarith

end Work.FTS.PhiStar.Honesty.CptApp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Omega_succ_subset =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

/-- The first level function `m ↦ 2 / m` of the shrinking region is antitone. -/
private theorem two_div_succ_le (m : ℕ) (hm : 1 ≤ m) :
    2 / ((m + 1 : ℕ) : ℝ) ≤ 2 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact div_le_div_of_nonneg_left (by norm_num) hmR hle

theorem Omega_succ_subset {m : ℕ} (hm : 1 ≤ m) :
    Work.FTS.PhiStar.Honesty.CptApp.Omega (m + 1) ⊆
      Work.FTS.PhiStar.Honesty.CptApp.Omega m := by
  intro p hp
  simp only [Omega, Set.mem_ofPred_eq] at hp ⊢
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hle : 2 / ((m + 1 : ℕ) : ℝ) ≤ 2 / (m : ℝ) := two_div_succ_le m hm
  rcases hp with h | h | h | h
  · exact Or.inl (lt_of_lt_of_le h hle)
  · exact Or.inr (Or.inl (by rw [hcast] at h; linarith))
  · exact Or.inr (Or.inr (Or.inl (lt_of_lt_of_le h hle)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

end Work.FTS.PhiStar.Honesty.CptApp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.hardyLoc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Jordan's inequality and the two weight comparisons on `(0,π/4)` -/

/-- **Jordan's inequality on the quarter interval**: `θ ≤ (π/4) sin(2θ)` for `0 < θ < π/4`. -/
private lemma quarter_le_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  have h2θ0 : (0 : ℝ) ≤ 2 * θ := by linarith [hθ.1]
  have h2θπ : 2 * θ ≤ Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have h := Real.mul_le_sin h2θ0 h2θπ
  have heq : (Real.pi / 4) * (2 / Real.pi * (2 * θ)) = θ := by
    field_simp
    ring
  calc θ = (Real.pi / 4) * (2 / Real.pi * (2 * θ)) := heq.symm
    _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h (by positivity)

/-- `sin(2θ)^{-c} ≤ (π/4)^c θ^{-c}` on `(0,π/4)` for `c > 0`. -/
private lemma sin_pow_neg_le {c : ℝ} (hc : 0 < c) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c * θ ^ (-c) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hj := quarter_le_sin hθ
  have hdiv : θ / Real.sin (2 * θ) ≤ Real.pi / 4 := by
    rw [div_le_iff₀ hsinpos]; linarith [hj]
  have h1 : (θ / Real.sin (2 * θ)) ^ c ≤ (Real.pi / 4) ^ c :=
    Real.rpow_le_rpow (div_nonneg hθ.1.le hsinpos.le) hdiv hc.le
  have h2 : (θ / Real.sin (2 * θ)) ^ c = θ ^ c * (Real.sin (2 * θ)) ^ (-c) := by
    rw [Real.div_rpow hθ.1.le hsinpos.le, div_eq_mul_inv, ← Real.rpow_neg hsinpos.le]
  have h3 : θ ^ c * (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c := h2 ▸ h1
  have hθc : (0 : ℝ) < θ ^ c := Real.rpow_pos_of_pos hθ.1 c
  have h4 : (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c / θ ^ c := by
    rw [le_div_iff₀ hθc]; linarith [h3]
  have h5 : (Real.pi / 4) ^ c / θ ^ c = (Real.pi / 4) ^ c * θ ^ (-c) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hθ.1.le]
  linarith [h4, h5]

/-- `θ^{2-c} ≤ (π/4)^{2-c} sin(2θ)^{2-c}` on `(0,π/4)` for `c ≤ 2`. -/
private lemma pow_le_sin_pow {c : ℝ} (hc2 : c ≤ 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    θ ^ (2 - c) ≤ (Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hj := quarter_le_sin hθ
  have h2c : (0 : ℝ) ≤ 2 - c := by linarith
  calc θ ^ (2 - c) ≤ ((Real.pi / 4) * Real.sin (2 * θ)) ^ (2 - c) :=
        Real.rpow_le_rpow hθ.1.le hj h2c
    _ = (Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c) :=
        Real.mul_rpow (by positivity) hsinpos.le

/-! ## The Hardy inequality on `(0,T)` -/

/-- **The angular weighted Hardy inequality on `(0,T)`**, for `0 < T ≤ π/4`, `1 < c ≤ 2` and `u`
of class `C¹` on `(0,T)` with `u → 0` at `0⁺`, as an inequality of Lebesgue integrals. -/
private theorem hardy_Ioo_fts {T c : ℝ} (hT : 0 < T) (hT4 : T ≤ Real.pi / 4)
    (hc1 : 1 < c) (hc2 : c ≤ 2) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) T))
    (h0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) T,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) T,
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
  have h4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hc0 : (0 : ℝ) < c := by linarith
  have hKpos : (0 : ℝ) < 4 / (c - 1) ^ 2 := by positivity
  have hpi_nn : (0 : ℝ) ≤ (Real.pi / 4) ^ c := (Real.rpow_pos_of_pos h4pos c).le
  have hpi_nn2 : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 - c) := (Real.rpow_pos_of_pos h4pos (2 - c)).le
  -- ## Step A: compare `sin(2θ)^{-c}` with the power `θ^{-c}`
  have hA : (∫⁻ θ in Set.Ioo (0 : ℝ) T,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) T, ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) := ⟨hθ.1, lt_of_lt_of_le hθ.2 hT4⟩
    have hcmp := sin_pow_neg_le hc0 hmem
    rw [← ENNReal.ofReal_mul hpi_nn]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2
        ≤ ((Real.pi / 4) ^ c * θ ^ (-c)) * (u θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
      _ = (Real.pi / 4) ^ c * (θ ^ (-c) * (u θ) ^ 2) := by ring
  -- ## Step B: the power-weighted Hardy inequality on the *same* interval `(0,T)`
  have hB := Work.FTS.EllipticEst.TT.SinHardy.NarrowAlt.powerHardy_open
      (a := T) (η := c - 2) hT (by linarith) (by linarith)
      (hu.continuousOn.aemeasurable measurableSet_Ioo) hu h0
  have hB' : (∫⁻ θ in Set.Ioo (0 : ℝ) T, ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) T,
          ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2)) := by
    have e1 : (∫⁻ θ in Set.Ioo (0 : ℝ) T,
          ENNReal.ofReal (u θ ^ 2 * θ ^ (-(2 + (c - 2)))))
        = (∫⁻ θ in Set.Ioo (0 : ℝ) T, ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := by
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      congr 1
      rw [show -(2 + (c - 2)) = -c by ring]
      ring
    have e2 : (∫⁻ θ in Set.Ioo (0 : ℝ) T,
          ENNReal.ofReal (deriv u θ ^ 2 * θ ^ (-(c - 2))))
        = (∫⁻ θ in Set.Ioo (0 : ℝ) T,
          ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2)) := by
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      congr 1
      rw [show -(c - 2) = 2 - c by ring]
      ring
    rw [e1, e2] at hB
    rw [show (4 : ℝ) / (1 + (c - 2)) ^ 2 = 4 / (c - 1) ^ 2 by ring] at hB
    exact hB
  -- ## Step C: compare the power `θ^{2-c}` with `sin(2θ)^{2-c}`
  have hC : (∫⁻ θ in Set.Ioo (0 : ℝ) T,
        ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) T,
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) := ⟨hθ.1, lt_of_lt_of_le hθ.2 hT4⟩
    have hcmp := pow_le_sin_pow hc2 hmem
    rw [← ENNReal.ofReal_mul hpi_nn2]
    refine ENNReal.ofReal_le_ofReal ?_
    calc θ ^ (2 - c) * (deriv u θ) ^ 2
        ≤ ((Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c)) * (deriv u θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
      _ = (Real.pi / 4) ^ (2 - c) *
            ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) := by ring
  -- ## the constant bookkeeping
  have hAD : (Real.pi / 4) ^ c * (Real.pi / 4) ^ (2 - c) = (Real.pi / 4) ^ 2 := by
    rw [← Real.rpow_add h4pos c (2 - c)]
    norm_num
  have hmerge : ∀ X : ℝ≥0∞, ENNReal.ofReal ((Real.pi / 4) ^ c) *
        (ENNReal.ofReal (4 / (c - 1) ^ 2) * (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) * X))
      = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) * X := by
    intro X
    have hkey : (Real.pi / 4) ^ c * (4 / (c - 1) ^ 2) * (Real.pi / 4) ^ (2 - c)
        = (Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2) := by
      rw [← hAD]; ring
    calc ENNReal.ofReal ((Real.pi / 4) ^ c) *
          (ENNReal.ofReal (4 / (c - 1) ^ 2) * (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) * X))
        = ENNReal.ofReal ((Real.pi / 4) ^ c * (4 / (c - 1) ^ 2) * (Real.pi / 4) ^ (2 - c)) * X := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hpi_nn,
            ← ENNReal.ofReal_mul (mul_nonneg hpi_nn hKpos.le)]
      _ = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) * X := by rw [hkey]
  -- ## assembly
  calc (∫⁻ θ in Set.Ioo (0 : ℝ) T,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) T, ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := hA
    _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) * (ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) T,
            ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2))) :=
        mul_le_mul_right hB' (ENNReal.ofReal ((Real.pi / 4) ^ c))
    _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) * (ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) *
            (∫⁻ θ in Set.Ioo (0 : ℝ) T,
              ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)))) :=
        mul_le_mul_right (mul_le_mul_right hC (ENNReal.ofReal (4 / (c - 1) ^ 2)))
          (ENNReal.ofReal ((Real.pi / 4) ^ c))
    _ = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) T,
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := hmerge _
    _ ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) T,
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
        refine mul_le_mul_left ?_ _
        refine ENNReal.ofReal_le_ofReal ?_
        have hle1 : (Real.pi / 4) ≤ 1 := by linarith [Real.pi_lt_four]
        have hsq1 : ((Real.pi / 4)) ^ 2 ≤ 1 := by nlinarith [h4pos.le, hle1]
        nlinarith [hsq1, hKpos.le]

/-! ## The requested lemma -/

theorem hardyLoc (c θ₀ : ℝ) (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) (hθ : 0 < θ₀)
    (hθ2 : θ₀ ≤ Real.pi / 4) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 θ₀))
    (h0 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo 0 θ₀))
        (fun θ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo 0 θ₀))
          (fun θ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) :=
  hardy_Ioo_fts hθ hθ2 hc1 (by linarith) hu h0

end

end Work.FTS.PhiStar.Honesty.CptApp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.volume_boundary_union_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

theorem volume_boundary_union_zero :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
        ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) = 0 := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  have h1 : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext p; simp
  have h2 : {p : ℝ × ℝ | p.2 = 0} = (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
    ext p; simp
  have h3 : {p : ℝ × ℝ | p.2 = Real.pi / 2} =
      (Set.univ : Set ℝ) ×ˢ ({Real.pi / 2} : Set ℝ) := by
    ext p; simp
  rw [h1, h2, h3]
  refine MeasureTheory.measure_union_null (MeasureTheory.measure_union_null ?_ ?_) ?_
  · rw [MeasureTheory.Measure.prod_prod]; simp
  · rw [MeasureTheory.Measure.prod_prod]; simp
  · rw [MeasureTheory.Measure.prod_prod]; simp

end Work.FTS.PhiStar.Honesty.CptApp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.EllWeakAux.HkMem_sub_of_eqOn_Q0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.EllWeakAux

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## `ℋ^k`-membership is a property of the values on the open quadrant

The lemma requested here is a bookkeeping statement about `Work.Spaces.HkMem`: the `ℋ^k`-integrand
is built from the *local* operators `D_z^i` and `D_z^j D_θ^i` together with weights depending only
on `(z,θ)`, so two functions which agree on the open quadrant `Q0 = (0,∞) × (0,π/2)` have the same
integrand at every interior point, and the boundary lines `z = 0`, `sin(2θ) = 0` are null.

The proof therefore has two halves:

* **the difference is in `ℋ^k`**: with `SmoothOpen` data the `ℋ^k`-integrand is subadditive for
  differences, `HkIntegrand α k (u - v) ≤ 2·HkIntegrand α k u + 2·HkIntegrand α k v` on the closed
  quadrant (`HkIntegrand_sub_le_open` below, obtained from the public addition form
  `Work.FTS.EllipticEst.HkIntegrand_add_le_open` together with the sign invariance
  `Work.FTS.EllipticEst.HkIntegrand_neg` and the equivalence of the difference with `u + (-v)`);
  the closure of `ℋ^k` under an a.e. angular domination
  (`Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open`) then gives `u - v ∈ ℋ^k`;
* **the transfer to `w`**: `w` agrees with `u - v` on `Q0`, so
  `Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0` carries the membership across.

Note that `w` is completely arbitrary off `Q0`; only its values there are used.
-/

/-- **Pointwise subadditivity of the `ℋ^k`-integrand for a difference**, on the closed quadrant
`Iz ×ˢ Iθ`, for data which are `C^∞` on the open quadrant:

`HkIntegrand α k (f - g) ≤ 2·HkIntegrand α k f + 2·HkIntegrand α k g`.

(The boundary lines are trivial: at `z = 0` and at `sin(2θ) = 0` the integrand vanishes
identically, and it is nonnegative everywhere.  On the interior, `f - g = f + (-g)` and the
addition form of the subadditivity applies, the sign invariance killing the `-g`.) -/
theorem HkIntegrand_sub_le_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ - g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
          + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  -- the signed `-g` summand has the same integrand as `g`
  have hneg : Work.Spaces.HkIntegrand α k (fun z θ => -g z θ)
      = Work.Spaces.HkIntegrand α k g := by
    funext z θ
    exact Work.FTS.LocData.HkIntegrand_neg α k g z θ
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · -- radial boundary: the weight `w 0 = 0` kills the integrand
    rw [hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · -- angular boundary: every summand carries a factor `sin(2θ)`
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
      (fun z θ => f z θ - g z θ) z θ hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g z θ
    linarith
  · -- interior point of the quadrant
    have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := by
      simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h | h
      · exact absurd (by rw [← h]; simp) hs
      · exact h
    have hθ2 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h | h
      · exact h
      · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
            Real.sin_pi]) hs
    -- the difference is the sum with the negated second summand
    have he : (fun z θ => f z θ - g z θ)
        = fun z θ => f z θ + (fun z θ => -g z θ) z θ := by
      funext z θ; exact sub_eq_add_neg _ _
    rw [he]
    have h := Work.FTS.EllipticEst.HkIntegrand_add_le_open α k hf
      (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl hg) hz hθ
    rw [hneg] at h
    exact h

theorem HkMem_sub_of_eqOn_Q0 (α : ℝ) (k : ℕ) {u v w : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hmu : Work.Spaces.HkMem α k u) (hmv : Work.Spaces.HkMem α k v)
    (hw : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → w z θ = u z θ - v z θ) :
    Work.Spaces.HkMem α k w := by
  have hpt := HkIntegrand_sub_le_open (α := α) (k := k) hu hv
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => u z θ - v z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hu hv
  -- the a.e. angular domination by the (integrable) majorant `2·HkIntegrand u + 2·HkIntegrand v`
  have hle : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α k (fun z θ => u z θ - v z θ) z θ
          ≤ 2 * Work.Spaces.HkIntegrand α k u z θ
            + 2 * Work.Spaces.HkIntegrand α k v z θ :=
    fun z hz => MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hpt z hz θ hθ)
  have hdd : Work.Spaces.HkMem α k (fun z θ => u z θ - v z θ) :=
    Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open α k hsm hmu hmv hle
  -- transfer along the agreement on the open quadrant
  exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hdd
    (fun z hz θ hθ => (hw z hz θ hθ.1 hθ.2).symm)

end Work.FTS.PhiStar.Honesty.EllWeakAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.EllWeakAux.integrableOn_slice_mul_sinCos2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.EllWeakAux

open MeasureTheory

/-- **Integrability of the angular slice of `Ψ` against `sinθcos²θ`.**

The hypothesis `HkMem α k (∂_θ²Ψ)` (for any `k ≥ 0`) contains, as the `D_z^0`-summand of its
integrand, the integrability of `θ ↦ (∂_θ²Ψ z θ · w z / sin(2θ)^{η/2})²`, i.e. of
`θ ↦ (∂_θ²Ψ z θ)² · sin(2θ)^{-η}` up to the constant `w z ²`.  Since `η > -1`, the weight
`sin(2θ)^{-η}` forces the slice `θ ↦ Ψ z θ` of the `C^∞`-function `Ψ` to be *bounded* on
`(0, π/2)` (Cauchy–Schwarz against `sin(2θ)^{η}` plus the fundamental theorem of calculus from
the interior point `π/4` — nothing is known at the endpoints), and `sinθcos²θ` is bounded by
`1`; this is exactly `HonestBddOfSecondSq`, whose last conjunct is the claim. -/
theorem integrableOn_slice_mul_sinCos2 {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  -- `∂_θ²Ψ` is again `C^∞` on the open quadrant
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hsm.pth.pth
  -- the `D_z^0`-summand of the `ℋ^k`-integrand of `∂_θ²Ψ` is integrable on the slice
  have hslice : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter 0 (Work.Spaces.pthIter 2 Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      ((Work.FTS.EllipticEst.SmoothOpen.aesm_slice_summand hsm2 0 hz).pow 2) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 Ψ) z θ 0 (Nat.zero_le k)
  -- divide by the constant `w z ² ≠ 0`: `(∂_θ²Ψ)² · sin(2θ)^{-η}` is integrable as well
  have hconv : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have hwz : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    refine MeasureTheory.IntegrableOn.congr_fun (hslice.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · intro θ hθ
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
      have hs0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      show ((Work.Spaces.w z) ^ 2)⁻¹
          * (Work.Spaces.DzIter 0 (Work.Spaces.pthIter 2 Ψ) z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = Work.Spaces.pthIter 2 Ψ z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [Work.Spaces.DzIter_zero, Work.FTS.EllipticEst.sEta]
      rw [show (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
          = Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) by
        rw [div_eq_mul_inv, ← Real.rpow_neg hs0]]
      have hsq : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
          = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hs0]
        congr 1
        ring
      rw [mul_pow, mul_pow, hsq]
      rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
            ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 *
              ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))))
          = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2) *
            ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) by ring,
        inv_mul_cancel₀ (pow_ne_zero 2 hwz), one_mul]
    · rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- `θ ↦ ∂_θ²Ψ z θ` is literally the second derivative of the slice `θ ↦ Ψ z θ`
  have hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => deriv (fun t : ℝ => deriv (fun θ' : ℝ => Ψ z θ') t) θ ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hconv
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.curry_θ hz).of_le (by norm_num)
  exact (Work.FTS.EllipticEst.Honest.HonestBddOfSecondSq hf2 hint).2.2.2.2.2

end Work.FTS.PhiStar.Honesty.EllWeakAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Master =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## 1. The master integral lemma -/

/-- The `z`-slice of a compactly supported function on `ℝ²` is compactly supported. -/
theorem hasCompactSupport_slice_fst {F : ℝ × ℝ → ℝ} (h : HasCompactSupport F) (y : ℝ) :
    HasCompactSupport (fun x : ℝ => F (x, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Prod.fst '' tsupport F) ?_ ?_
  · exact IsCompact.image h continuous_fst
  · intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    exact hx ((notMem_tsupport_iff_eventuallyEq.mp
      (fun hmem => hcon ⟨(x, y), hmem, rfl⟩)).eq_of_nhds)

/-- The `θ`-slice of a compactly supported function on `ℝ²` is compactly supported. -/
theorem hasCompactSupport_slice_snd {F : ℝ × ℝ → ℝ} (h : HasCompactSupport F) (x : ℝ) :
    HasCompactSupport (fun y : ℝ => F (x, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Prod.snd '' tsupport F) ?_ ?_
  · exact IsCompact.image h continuous_snd
  · intro y hy
    rw [Function.mem_support] at hy
    by_contra hcon
    exact hy ((notMem_tsupport_iff_eventuallyEq.mp
      (fun hmem => hcon ⟨(x, y), hmem, rfl⟩)).eq_of_nhds)

/-- **The integral of the `z`-derivative of a compactly supported `C¹` function vanishes.**
By Fubini it is the integral over the angles of `∫_z ∂_z F (z,θ) dz`, and each inner integral
vanishes by the one-dimensional fundamental theorem of calculus: the slice is compactly
supported, so its limits at `±∞` are `0`. -/
theorem master_pz_eq_zero {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F))
    (hc : HasCompactSupport (Function.uncurry F)) :
    ∫ p : ℝ × ℝ, Work.Spaces.pz F p.1 p.2 = 0 := by
  have heq : (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry F) p) (1, 0) := by
    funext p
    exact Work.Spaces.pz_eq_fderiv (hF.differentiable_one.differentiableAt)
  have hcont : Continuous (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) := by
    rw [heq]
    exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcpt : HasCompactSupport (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) := by
    rw [heq]; exact hc.fderiv_apply ℝ (1, 0)
  have hint : Integrable (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) :=
    hcont.integrable_of_hasCompactSupport hcpt
  rw [show (volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.Measure.prod (volume : MeasureTheory.Measure ℝ)
          (volume : MeasureTheory.Measure ℝ) from rfl]
  rw [MeasureTheory.integral_prod_symm _ hint]
  have hinner : ∀ θ : ℝ, ∫ z, Work.Spaces.pz F z θ = 0 := by
    intro θ
    have h1 : ContDiff ℝ 1 (fun z : ℝ => F z θ) :=
      hF.comp (contDiff_id.prodMk contDiff_const)
    refine MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun z => F z θ) (f' := fun z => Work.Spaces.pz F z θ) ?_ ?_ ?_
    · intro z
      exact (h1.differentiable_one.differentiableAt (x := z)).hasDerivAt
    · exact (h1.continuous_deriv (le_refl 1)).integrable_of_hasCompactSupport
        (hasCompactSupport_slice_fst hc θ).deriv
    · exact h1.continuous.integrable_of_hasCompactSupport (hasCompactSupport_slice_fst hc θ)
  simp [hinner]

/-- **The integral of the `θ`-derivative of a compactly supported `C¹` function vanishes.** -/
theorem master_pth_eq_zero {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F))
    (hc : HasCompactSupport (Function.uncurry F)) :
    ∫ p : ℝ × ℝ, Work.Spaces.pth F p.1 p.2 = 0 := by
  have heq : (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry F) p) (0, 1) := by
    funext p
    exact Work.Spaces.pth_eq_fderiv (hF.differentiable_one.differentiableAt)
  have hcont : Continuous (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2) := by
    rw [heq]
    exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcpt : HasCompactSupport (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2) := by
    rw [heq]; exact hc.fderiv_apply ℝ (0, 1)
  have hint : Integrable (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2) :=
    hcont.integrable_of_hasCompactSupport hcpt
  rw [show (volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.Measure.prod (volume : MeasureTheory.Measure ℝ)
          (volume : MeasureTheory.Measure ℝ) from rfl]
  rw [MeasureTheory.integral_prod _ hint]
  have hinner : ∀ z : ℝ, ∫ θ, Work.Spaces.pth F z θ = 0 := by
    intro z
    have h1 : ContDiff ℝ 1 (fun θ : ℝ => F z θ) :=
      hF.comp (contDiff_const.prodMk contDiff_id)
    refine MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun θ => F z θ) (f' := fun θ => Work.Spaces.pth F z θ) ?_ ?_ ?_
    · intro θ
      exact (h1.differentiable_one.differentiableAt (x := θ)).hasDerivAt
    · exact (h1.continuous_deriv (le_refl 1)).integrable_of_hasCompactSupport
        (hasCompactSupport_slice_snd hc z).deriv
    · exact h1.continuous.integrable_of_hasCompactSupport (hasCompactSupport_slice_snd hc z)
  simp [hinner]

/-! ## 2. Product rules, continuity and integrability -/

/-- A partial derivative vanishes at a point where the function vanishes on a neighbourhood. -/
theorem pz_eq_zero_of_eventuallyEq_zero {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Function.uncurry F =ᶠ[𝓝 (z, θ)] 0) : Work.Spaces.pz F z θ = 0 := by
  have h' : HasFDerivAt (Function.uncurry F) (0 : ℝ × ℝ →L[ℝ] ℝ) (z, θ) :=
    (hasFDerivAt_const (0 : ℝ) (z, θ)).congr_of_eventuallyEq h
  rw [Work.Spaces.pz_eq_fderiv h'.differentiableAt, h'.fderiv]
  rfl

/-- A partial derivative vanishes at a point where the function vanishes on a neighbourhood. -/
theorem pth_eq_zero_of_eventuallyEq_zero {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Function.uncurry F =ᶠ[𝓝 (z, θ)] 0) : Work.Spaces.pth F z θ = 0 := by
  have h' : HasFDerivAt (Function.uncurry F) (0 : ℝ × ℝ →L[ℝ] ℝ) (z, θ) :=
    (hasFDerivAt_const (0 : ℝ) (z, θ)).congr_of_eventuallyEq h
  rw [Work.Spaces.pth_eq_fderiv h'.differentiableAt, h'.fderiv]
  rfl

/-- If `ψ` vanishes at `p` then so does `g · ψ`. -/
theorem mul_eq_zero_of_uncurry_eq_zero {g ψ : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (h : Function.uncurry ψ p = 0) : g p.1 p.2 * ψ p.1 p.2 = 0 := by
  simp only [Function.uncurry] at h
  rw [h, mul_zero]

/-- If `ψ` vanishes at `p` then so does `uncurry (g · ψ)`. -/
theorem uncurry_mul_eq_zero {g ψ : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (h : Function.uncurry ψ p = 0) :
    Function.uncurry (fun z θ => g z θ * ψ z θ) p = 0 := by
  simp only [Function.uncurry] at h ⊢
  rw [h, mul_zero]

/-- The Leibniz rule for `∂_z`, where the first factor is only smooth on the open quadrant and
the second is a test function (so that everything is smooth in a neighbourhood of the support). -/
theorem pz_mul_rule {g ψ : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hψ : TestQ0 ψ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => g z θ * ψ z θ) z θ
      = Work.Spaces.pz g z θ * ψ z θ + g z θ * Work.Spaces.pz ψ z θ := by
  by_cases hp : (z, θ) ∈ Q0
  · have h1 : HasDerivAt (fun z' : ℝ => g z' θ) (Work.Spaces.pz g z θ) z :=
      hg.hasDerivAt_slice hp.2 hp.1
    have h2 : HasDerivAt (fun z' : ℝ => ψ z' θ) (Work.Spaces.pz ψ z θ) z :=
      ((hψ.smooth.comp (contDiff_id.prodMk (contDiff_const (c := θ)))).differentiable
        (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
    exact (h1.mul h2).deriv
  · have hzψ : (z, θ) ∉ tsupport (Function.uncurry ψ) := fun hmem => hp (hψ.tsupp hmem)
    have h0 : Function.uncurry ψ =ᶠ[𝓝 (z, θ)] 0 := notMem_tsupport_iff_eventuallyEq.mp hzψ
    have hψ0 : ψ z θ = 0 := h0.eq_of_nhds
    have hpzψ0 : Work.Spaces.pz ψ z θ = 0 := pz_eq_zero_of_eventuallyEq_zero h0
    have hF0 : Function.uncurry (fun z θ => g z θ * ψ z θ) =ᶠ[𝓝 (z, θ)] 0 := by
      filter_upwards [h0] with p hp'
      exact uncurry_mul_eq_zero hp'
    have hpzF0 : Work.Spaces.pz (fun z θ => g z θ * ψ z θ) z θ = 0 :=
      pz_eq_zero_of_eventuallyEq_zero hF0
    rw [hpzF0, hψ0, hpzψ0]; ring

/-- The Leibniz rule for `∂_θ`, where the first factor is only smooth on the open quadrant and
the second is a test function. -/
theorem pth_mul_rule {g ψ : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hψ : TestQ0 ψ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => g z θ * ψ z θ) z θ
      = Work.Spaces.pth g z θ * ψ z θ + g z θ * Work.Spaces.pth ψ z θ := by
  by_cases hp : (z, θ) ∈ Q0
  · have h1 : HasDerivAt (fun θ' : ℝ => g z θ') (Work.Spaces.pth g z θ) θ :=
      (hg.curry_θ hp.1).differentiableOn (by simp) |>.differentiableAt
        (isOpen_Ioo.mem_nhds hp.2) |>.hasDerivAt
    have h2 : HasDerivAt (fun θ' : ℝ => ψ z θ') (Work.Spaces.pth ψ z θ) θ :=
      ((hψ.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable
        (by norm_num)).differentiableAt (x := θ) |>.hasDerivAt
    exact (h1.mul h2).deriv
  · have hzψ : (z, θ) ∉ tsupport (Function.uncurry ψ) := fun hmem => hp (hψ.tsupp hmem)
    have h0 : Function.uncurry ψ =ᶠ[𝓝 (z, θ)] 0 := notMem_tsupport_iff_eventuallyEq.mp hzψ
    have hψ0 : ψ z θ = 0 := h0.eq_of_nhds
    have hpthψ0 : Work.Spaces.pth ψ z θ = 0 := pth_eq_zero_of_eventuallyEq_zero h0
    have hF0 : Function.uncurry (fun z θ => g z θ * ψ z θ) =ᶠ[𝓝 (z, θ)] 0 := by
      filter_upwards [h0] with p hp'
      exact uncurry_mul_eq_zero hp'
    have hpthF0 : Work.Spaces.pth (fun z θ => g z θ * ψ z θ) z θ = 0 :=
      pth_eq_zero_of_eventuallyEq_zero hF0
    rw [hpthF0, hψ0, hpthψ0]; ring

/-- The partial `z`-derivative of a globally `C^∞` function is continuous. -/
theorem continuous_pz_of_contDiff {Ψ : ℝ → ℝ → ℝ}
    (h : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)) :
    Continuous (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2) := by
  have hdiff : Differentiable ℝ (Function.uncurry Ψ) :=
    h.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have heq : (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry Ψ) p) (1, 0) := by
    funext p; exact Work.Spaces.pz_eq_fderiv (hdiff p)
  rw [heq]
  exact (h.continuous_fderiv (by rw [Work.Stability.smoothOrder]; simp)).clm_apply
    continuous_const

/-- The partial `θ`-derivative of a globally `C^∞` function is continuous. -/
theorem continuous_pth_of_contDiff {Ψ : ℝ → ℝ → ℝ}
    (h : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)) :
    Continuous (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2) := by
  have hdiff : Differentiable ℝ (Function.uncurry Ψ) :=
    h.differentiable (by rw [Work.Stability.smoothOrder]; simp)
  have heq : (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry Ψ) p) (0, 1) := by
    funext p; exact Work.Spaces.pth_eq_fderiv (hdiff p)
  rw [heq]
  exact (h.continuous_fderiv (by rw [Work.Stability.smoothOrder]; simp)).clm_apply
    continuous_const

/-- A function which is continuous on the (compact) closed support of a test function and
vanishes outside it is integrable. -/
theorem integrable_of_continuousOn_tsupport_test {H : ℝ × ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hψ : TestQ0 ψ) (hcont : ContinuousOn H (tsupport (Function.uncurry ψ)))
    (hsub : Function.support H ⊆ tsupport (Function.uncurry ψ)) :
    Integrable H (volume : MeasureTheory.Measure (ℝ × ℝ)) :=
  (hcont.integrableOn_compact hψ.cpt).integrable_of_forall_notMem_eq_zero (fun p hp => by
    by_contra hne
    exact hp (hsub (Function.mem_support.mpr hne)))

/-- The product of a function smooth on the open quadrant with a test function is globally `C¹`:
inside the quadrant it is a product of smooth functions, and outside the support of the test
function it vanishes identically. -/
theorem contDiff_one_mul_test {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ContDiff ℝ 1 (Function.uncurry (fun z θ => g z θ * ψ z θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport (Function.uncurry ψ)
  · have h1 : ContDiffAt ℝ 1 (Function.uncurry g) p :=
      (((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg 1).contDiffAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hψ.tsupp hp)))
    exact (h1.mul (hψ.smooth.contDiffAt.of_le (by simp))).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (uncurry_mul_eq g ψ))
  · have h0 : Function.uncurry ψ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    have h00 : Function.uncurry (fun z θ => g z θ * ψ z θ) =ᶠ[𝓝 p] 0 := by
      filter_upwards [h0] with q hq
      exact uncurry_mul_eq_zero hq
    exact (contDiffAt_const (c := (0 : ℝ)) (x := p)).congr_of_eventuallyEq h00

/-- **Integration by parts for the plain `z`-derivative.** -/
theorem integral_pz_mul_eq_neg {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.pz g p.1 p.2 * ψ p.1 p.2
      = -∫ p : ℝ × ℝ, g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2 := by
  have hF : ContDiff ℝ 1 (Function.uncurry (fun z θ => g z θ * ψ z θ)) :=
    contDiff_one_mul_test hg hψ
  have hFc : HasCompactSupport (Function.uncurry (fun z θ => g z θ * ψ z θ)) := by
    refine hψ.cpt.mono' ?_
    intro p hp
    rw [Function.mem_support] at hp
    refine subset_closure (Function.mem_support.mpr ?_)
    intro h0
    exact hp (uncurry_mul_eq_zero h0)
  have hmaster := master_pz_eq_zero hF hFc
  have hpt : ∀ p : ℝ × ℝ, Work.Spaces.pz (fun z θ => g z θ * ψ z θ) p.1 p.2
      = Work.Spaces.pz g p.1 p.2 * ψ p.1 p.2
        + g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2 :=
    fun p => pz_mul_rule hg hψ p.1 p.2
  have h1 : Integrable (fun p : ℝ × ℝ => Work.Spaces.pz g p.1 p.2 * ψ p.1 p.2) := by
    refine integrable_of_continuousOn_tsupport_test hψ ?_ ?_
    · exact (((Work.FTS.LocData.contDiffOn_pz Work.FTS.EllipticEst.isOpen_Q0 hg).continuousOn).mono
        hψ.tsupp).mul hψ.continuous.continuousOn
    · intro p hp
      rw [Function.mem_support] at hp
      refine subset_closure (Function.mem_support.mpr ?_)
      intro h0
      exact hp (mul_eq_zero_of_uncurry_eq_zero h0)
  have h2 : Integrable (fun p : ℝ × ℝ => g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2) := by
    refine integrable_of_continuousOn_tsupport_test hψ ?_ ?_
    · exact (hg.continuousOn.mono hψ.tsupp).mul
        (continuous_pz_of_contDiff hψ.smooth).continuousOn
    · intro p hp
      rw [Function.mem_support] at hp
      refine tsupport_pz_subset hψ (subset_closure (Function.mem_support.mpr ?_))
      intro h0
      exact hp (mul_eq_zero_of_uncurry_eq_zero h0)
  have hsum : ∫ p : ℝ × ℝ, (Work.Spaces.pz g p.1 p.2 * ψ p.1 p.2
      + g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2) = 0 := by
    rw [← hmaster]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun p => (hpt p).symm))
  rw [MeasureTheory.integral_add h1 h2] at hsum
  linarith

/-- **Integration by parts for the plain `θ`-derivative.** -/
theorem integral_pth_mul_eq_neg {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.pth g p.1 p.2 * ψ p.1 p.2
      = -∫ p : ℝ × ℝ, g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2 := by
  have hF : ContDiff ℝ 1 (Function.uncurry (fun z θ => g z θ * ψ z θ)) :=
    contDiff_one_mul_test hg hψ
  have hFc : HasCompactSupport (Function.uncurry (fun z θ => g z θ * ψ z θ)) := by
    refine hψ.cpt.mono' ?_
    intro p hp
    rw [Function.mem_support] at hp
    refine subset_closure (Function.mem_support.mpr ?_)
    intro h0
    exact hp (uncurry_mul_eq_zero h0)
  have hmaster := master_pth_eq_zero hF hFc
  have hpt : ∀ p : ℝ × ℝ, Work.Spaces.pth (fun z θ => g z θ * ψ z θ) p.1 p.2
      = Work.Spaces.pth g p.1 p.2 * ψ p.1 p.2
        + g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2 :=
    fun p => pth_mul_rule hg hψ p.1 p.2
  have h1 : Integrable (fun p : ℝ × ℝ => Work.Spaces.pth g p.1 p.2 * ψ p.1 p.2) := by
    refine integrable_of_continuousOn_tsupport_test hψ ?_ ?_
    · exact (((Work.FTS.LocData.contDiffOn_pth Work.FTS.EllipticEst.isOpen_Q0 hg).continuousOn).mono
        hψ.tsupp).mul hψ.continuous.continuousOn
    · intro p hp
      rw [Function.mem_support] at hp
      refine subset_closure (Function.mem_support.mpr ?_)
      intro h0
      exact hp (mul_eq_zero_of_uncurry_eq_zero h0)
  have h2 : Integrable (fun p : ℝ × ℝ => g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2) := by
    refine integrable_of_continuousOn_tsupport_test hψ ?_ ?_
    · exact (hg.continuousOn.mono hψ.tsupp).mul
        (continuous_pth_of_contDiff hψ.smooth).continuousOn
    · intro p hp
      rw [Function.mem_support] at hp
      refine tsupport_pth_subset hψ (subset_closure (Function.mem_support.mpr ?_))
      intro h0
      exact hp (mul_eq_zero_of_uncurry_eq_zero h0)
  have hsum : ∫ p : ℝ × ℝ, (Work.Spaces.pth g p.1 p.2 * ψ p.1 p.2
      + g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2) = 0 := by
    rw [← hmaster]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun p => (hpt p).symm))
  rw [MeasureTheory.integral_add h1 h2] at hsum
  linarith


end Work.FTS.PhiStar.Honesty.SlotsLimit
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Joint.tendsto_term_integral_of_tendsto_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.Joint

/-- **Continuity of the slot integral along the Cauchy family.**

If the approximating data `A n` are `C^∞` on the open quadrant `Q0`, the differences
`A n - A m` lie in `ℋ^k` and their `ℋ^k`-norm squares tend to `0` along
`Filter.atTop ×ˢ Filter.atTop`, then for every sub-slot `(j,i)` of level `k`
(the pure slots `i = 0`, `j ≤ k` and the mixed slots `1 ≤ i`, `i + j ≤ k`) the weighted
`L²`-norms of the differences of the sub-slots tend to `0` as well:

`∫_{Q0} (D_z^jD_θ^i(A n) - D_z^jD_θ^i(A m))² · (termWeight α i)² → 0`.

The proof is the plain squeeze: on the open quadrant the sub-slot of a difference is the
difference of the sub-slots (`mixed_sub_eqOn`, which uses only that `D_z`, `D_θ` are honest
differential operators there), so the integral in question is one of the summands of the
level-`k` integrand and is therefore dominated by the whole `HkSq α k (A n - A m)`
(`term_integral_le_HkSq`), while being nonnegative. -/
theorem tendsto_term_integral_of_tendsto_HkSq {α : ℝ} {k : ℕ} {A : ℕ → ℝ → ℝ → ℝ} (j i : ℕ)
    (hij : (i = 0 ∧ j ≤ k) ∨ (1 ≤ i ∧ i + j ≤ k))
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (A n))
    (hmemsub : ∀ n m : ℕ, Work.Spaces.HkMem α k (fun z θ => A n z θ - A m z θ))
    (h : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α k
        (fun z θ => A nm.1 z θ - A nm.2 z θ)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)) :
    Filter.Tendsto (fun nm : ℕ × ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        (Work.Spaces.mixed j i (A nm.1) p.1 p.2
            - Work.Spaces.mixed j i (A nm.2) p.1 p.2) ^ 2
          * (Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  have hQ0 : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  refine squeeze_zero (fun nm => ?_) (fun nm => ?_) h
  · -- the integral is nonnegative
    exact MeasureTheory.setIntegral_nonneg hQ0
      (fun p _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · -- and it is dominated by the whole `ℋ^k`-norm of the difference
    have hsm_sub : Work.FTS.EllipticEst.SmoothOpen (fun z θ => A nm.1 z θ - A nm.2 z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl (hsm nm.1) (hsm nm.2)
    have hb := term_integral_le_HkSq α k hsm_sub (hmemsub nm.1 nm.2) j i hij
    -- On `Q0` the `(j,i)`-sub-slot of the difference is the difference of the sub-slots, so
    -- the integrand here is `(mixed j i (A n - A m) · termWeight)²`.
    have heqon : Set.EqOn
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i (fun z θ => A nm.1 z θ - A nm.2 z θ)
            p.1 p.2 * Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2)
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i (A nm.1) p.1 p.2
            - Work.Spaces.mixed j i (A nm.2) p.1 p.2) ^ 2
            * (Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      have h1 : Work.Spaces.mixed j i (fun z θ => A nm.1 z θ - A nm.2 z θ) p.1 p.2
          = Work.Spaces.mixed j i (A nm.1) p.1 p.2
            - Work.Spaces.mixed j i (A nm.2) p.1 p.2 :=
        mixed_sub_eqOn (hsm nm.1) (hsm nm.2) j i hp
      show (Work.Spaces.mixed j i (fun z θ => A nm.1 z θ - A nm.2 z θ) p.1 p.2
          * Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2
        = (Work.Spaces.mixed j i (A nm.1) p.1 p.2
            - Work.Spaces.mixed j i (A nm.2) p.1 p.2) ^ 2
          * (Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i p.1 p.2) ^ 2
      rw [h1, mul_pow]
    rw [← MeasureTheory.setIntegral_congr_fun hQ0 heqon]
    exact hb

end Work.FTS.PhiStar.Honesty.SlotsLimit.Joint
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integral_swap_pz_abs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology

/-- The `t`-marginal of `|∂_zF|` is integrable on any interval of radii `[y,x]` with `y > 0`,
and the two iterated integrals agree: Tonelli/Fubini for the nonnegative measurable function
`(t,θ) ↦ |∂_zF t θ|`, whose angular slices are `L¹` by `slice_abs_integrable` and whose
`t`-marginals are dominated by `(∫_θ HkIntegrand α 1 F t θ)/y² + π/4` by
`slice_abs_integral_le`. -/
theorem integral_swap_pz_abs {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => ∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|))
        = ∫ t in Set.uIoc y x, (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|) := by
  rw [Set.uIoc_of_le hyx]
  -- the reference measure on the radial interval, and the fact that it lies in `Iz`
  have hsub : Set.Ioc y x ⊆ Work.Spaces.Iz := fun t ht =>
    le_of_lt (lt_trans hy ht.1)
  -- the marginal `t ↦ ∫_θ HkIntegrand α 1 F t θ` is `L¹` on the radial interval
  have hHIint : MeasureTheory.Integrable
      (fun t : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ)
      (MeasureTheory.volume.restrict (Set.Ioc y x)) :=
    hF.2.mono_set hsub
  -- the dominating function `W` is `L¹` on the radial interval
  have hWint : MeasureTheory.Integrable
      (fun t : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) / y ^ 2
        + Real.pi / 4)
      (MeasureTheory.volume.restrict (Set.Ioc y x)) := by
    have h1 : MeasureTheory.Integrable
        (fun t : ℝ => (1 / y ^ 2) * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 1 F t θ))
        (MeasureTheory.volume.restrict (Set.Ioc y x)) := hHIint.const_mul _
    have h2 : MeasureTheory.Integrable (fun _ : ℝ => Real.pi / 4)
        (MeasureTheory.volume.restrict (Set.Ioc y x)) := MeasureTheory.integrable_const _
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
    show (1 / y ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ)
        + Real.pi / 4
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) / y ^ 2 + Real.pi / 4
    ring
  -- joint a.e. strong measurability of `(t,θ) ↦ |∂_zF t θ|` on the product
  have hjointIcc : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|))
      ((MeasureTheory.volume.restrict (Set.Icc y x)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aesm_uncurry_abs_pzF hsm hy
  have hmono : (MeasureTheory.volume.restrict (Set.Ioc y x)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict (Set.Icc y x)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl) le_rfl
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|))
      ((MeasureTheory.volume.restrict (Set.Ioc y x)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hjointIcc.mono_measure hmono
  -- a.e. (in `t`) integrability of the angular slices
  have hslice : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc y x)),
      MeasureTheory.Integrable (fun θ : ℝ => |Work.Spaces.pz F t θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact (slice_abs_integrable hsm hF (lt_trans hy ht.1)).2
  -- integrability of the `t`-marginal
  have houter : MeasureTheory.Integrable
      (fun t : ℝ => ∫ θ, |Work.Spaces.pz F t θ|
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioc y x)) := by
    have haesm := hjoint.integral_prod_right'
    refine MeasureTheory.Integrable.mono' hWint haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => abs_nonneg _)]
    exact (slice_abs_integral_le hsm hF hy ht.1.le).2
  -- Tonelli/Fubini
  obtain ⟨hprod, hprod_eq⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict (Set.Ioc y x))
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun t θ : ℝ => |Work.Spaces.pz F t θ|) (fun t θ => abs_nonneg _) hjoint hslice houter
  refine ⟨?_, ?_⟩
  · exact hprod.integral_prod_right
  · have hsymm := MeasureTheory.integral_prod_symm
      (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|)) hprod
    exact hsymm.symm.trans hprod_eq

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.slot_joint_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

theorem slot_joint_cont {F : ℝ → Work.FTS.Galerkin.Fn} {T : ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 T,
      ContDiffOn ℝ 4 (Function.uncurry (F τ)) Work.FTS.EllipticEst.Q0)
    (hlipF : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
          |Work.Spaces.mixed j i (F τ) p.1 p.2
            - Work.Spaces.mixed j i (F τ') p.1 p.2| ≤ C * |τ - τ'|) :
    ∀ (j i : ℕ), j + i ≤ 1 →
      ContinuousOn (fun q : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T) := by
  intro j i hji
  -- Componentwise control of `dist q q0` for `q q0 : ℝ × ℝ × ℝ = ℝ × (ℝ × ℝ)`
  -- (that space carries the sup metric, `Prod.dist_eq`).
  have dist_pair_le_dist_triple : ∀ {q q0 : ℝ × ℝ × ℝ},
      dist (q.1, q.2.1) (q0.1, q0.2.1) ≤ dist q q0 := by
    intro q q0
    simp only [Prod.dist_eq]
    exact max_le (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have abs_sub_snd_snd_le_dist_triple : ∀ {q q0 : ℝ × ℝ × ℝ},
      |q.2.2 - q0.2.2| ≤ dist q q0 := by
    intro q q0
    simp only [Prod.dist_eq, Real.dist_eq]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- Spatial continuity of every slot `mixed j i (F τ)` on the open quadrant, at each fixed
  -- time `τ ∈ [0,T]`: `D_z^j D_θ^i` costs `j + i ≤ 1 ≤ 4` of the four available orders.
  have hA : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F τ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    exact (contDiffOn_zero_mixed_le (n := 4) (hsm τ hτ) (by omega)).continuousOn
  intro q0 hq0
  obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq0
  obtain ⟨hq21, hq22⟩ := Set.mem_prod.mp hq2
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hp0 : (q0.1, q0.2.1) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hq1, hq21.1, hq21.2⟩
  -- A compact neighbourhood of `(q0.1, q0.2.1)` inside the open quadrant.
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp Work.FTS.EllipticEst.isOpen_Q0 _ hp0
  have hr0pos : 0 < r / 2 := by linarith
  have hKsub : Metric.closedBall (q0.1, q0.2.1) (r / 2) ⊆ Work.FTS.EllipticEst.Q0 :=
    (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hrsub
  have hK : IsCompact (Metric.closedBall (q0.1, q0.2.1) (r / 2)) := isCompact_closedBall _ _
  obtain ⟨C, hC0, hC⟩ := hlipF _ hK hKsub
  -- Continuity at the base point (spatial variables), and the Lipschitz bound in time on
  -- the compact neighbourhood.
  have hcont0 : ContinuousAt
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F q0.2.2) p.1 p.2) (q0.1, q0.2.1) :=
    (hA q0.2.2 hq22).continuousAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp0)
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ2, hδ2pos, hδ2⟩ := (Metric.continuousAt_iff.mp hcont0) (ε / 2) hε2
  set δ := min (r / 2) (min (ε / (2 * (C + 1))) δ2) with hδdef
  have hC1 : 0 < C + 1 := by linarith
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hr0pos (lt_min (div_pos hε (by linarith)) hδ2pos)
  refine ⟨δ, hδpos, ?_⟩
  intro q hq hdq
  obtain ⟨hq1', hq2'⟩ := Set.mem_prod.mp hq
  obtain ⟨hq21', hq22'⟩ := Set.mem_prod.mp hq2'
  have hδ_le_r : δ ≤ r / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδ_le_eps : δ ≤ ε / (2 * (C + 1)) := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_δ2 : δ ≤ δ2 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hdp : dist (q.1, q.2.1) (q0.1, q0.2.1) < δ :=
    lt_of_le_of_lt dist_pair_le_dist_triple hdq
  have hpK : (q.1, q.2.1) ∈ Metric.closedBall (q0.1, q0.2.1) (r / 2) :=
    Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hdp hδ_le_r))
  -- The two terms of the telescoping decomposition.
  have h1 : |Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1
      - Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1| ≤ C * |q.2.2 - q0.2.2| :=
    hC j i hji (q.1, q.2.1) hpK q.2.2 hq22' q0.2.2 hq22
  have h2 : dist (Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1)
      (Work.Spaces.mixed j i (F q0.2.2) q0.1 q0.2.1) < ε / 2 :=
    hδ2 (lt_of_lt_of_le hdp hδ_le_δ2)
  rw [Real.dist_eq] at h2
  have hdτ : |q.2.2 - q0.2.2| ≤ δ :=
    le_of_lt (lt_of_le_of_lt abs_sub_snd_snd_le_dist_triple hdq)
  have h4 : C * |q.2.2 - q0.2.2| < ε / 2 := by
    have hprod : C * |q.2.2 - q0.2.2| ≤ C * (ε / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left (hdτ.trans hδ_le_eps) hC0
    have hlt : C * (ε / (2 * (C + 1))) < ε / 2 := by
      have hCe : C / (C + 1) < 1 := by rw [div_lt_one hC1]; linarith
      have heq : C * (ε / (2 * (C + 1))) = (ε / 2) * (C / (C + 1)) := by field_simp
      rw [heq]
      calc (ε / 2) * (C / (C + 1)) < (ε / 2) * 1 := mul_lt_mul_of_pos_left hCe (by linarith)
        _ = ε / 2 := by ring
    linarith
  rw [Real.dist_eq]
  have hsplit : Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1
      - Work.Spaces.mixed j i (F q0.2.2) q0.1 q0.2.1
      = (Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1
          - Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1)
      + (Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1
          - Work.Spaces.mixed j i (F q0.2.2) q0.1 q0.2.1) := by ring
  rw [hsplit]
  have := abs_add_le
    (Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1 - Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1)
    (Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1 - Work.Spaces.mixed j i (F q0.2.2) q0.1 q0.2.1)
  linarith

end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.PT.L12dens_hasDerivAt_of_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2.PT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary facts about the weight `K` and about `∂_z` -/

/-- `|K(θ)| = |3 sinθ cos²θ| ≤ 3` on all of `ℝ`. -/
private theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    have h := Real.abs_cos_le_one θ
    nlinarith [abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have hcs : |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 :=
    calc |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul hs hc (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hK : |Work.Spaces.K θ| = 3 * (|Real.sin θ| * Real.cos θ ^ 2) := by
    rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_of_nonneg (sq_nonneg (Real.cos θ))]
    ring
  rw [hK]
  linarith [hcs]

/-- `K` is continuous. -/
private theorem continuous_K : Continuous Work.Spaces.K := by
  unfold Work.Spaces.K
  exact ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2))

/-- `∂_z` costs one order of differentiability: the uncurried `∂_z f` of a datum that is
jointly `C²` on the open quadrant is jointly continuous there. -/
private theorem continuousOn_uncurry_pz_of_two {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 := by
  have hchain : ∀ p ∈ Work.FTS.EllipticEst.Q0, Function.uncurry (Work.Spaces.pz f) p
      = (fderiv ℝ (Function.uncurry f) p) (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
  have hfd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry f) p)
      Work.FTS.EllipticEst.Q0 := by
    have h' := h.fderivWithin (m := 1) Work.FTS.EllipticEst.isOpen_Q0.uniqueDiffOn
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hp]
  have hcomp : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) p) (1, 0))
      Work.FTS.EllipticEst.Q0 :=
    hfd.clm_apply contDiffOn_const
  exact (hcomp.congr hchain).continuousOn

/-! ## The main statement -/

theorem L12dens_hasDerivAt_of_strip {f : ℝ → ℝ → ℝ} {x C : ℝ} (hx : 0 < x) (hC : 0 ≤ C)
    (h2 : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hb₀ : ∀ y ∈ Set.Ioo (x / 2) (2 * x), ∀ θ ∈ Set.Ioo 0 (π / 2), |f y θ| ≤ C)
    (hb₁ : ∀ y ∈ Set.Ioo (x / 2) (2 * x), ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pz f y θ| ≤ C) :
    HasDerivAt (fun x => Work.Construction.L12dens f x)
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.Spaces.pz f x θ / x
        - Work.Spaces.K θ * f x θ / x ^ 2)) x := by
  have hxV : x ∈ Set.Ioo (x / 2) (2 * x) := ⟨by linarith, by linarith⟩
  have hV : IsOpen (Set.Ioo (x / 2) (2 * x)) := isOpen_Ioo
  have hVpos : ∀ y ∈ Set.Ioo (x / 2) (2 * x), 0 < y := fun y hy => by linarith [hy.1, hx]
  -- joint continuity on the open quadrant
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 :=
    continuous_K.comp_continuousOn continuousOn_snd
  have hfc : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := h2.continuousOn
  have hpc : ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_uncurry_pz_of_two h2
  have hg : ContinuousOn (Function.uncurry (fun y θ => Work.Spaces.K θ * f y θ / y))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun y θ => Work.Spaces.K θ * f y θ / y)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry f p / p.1 := by
      funext p; rcases p with ⟨y, θ⟩; rfl
    rw [hfun]
    exact (hKc.mul hfc).div continuousOn_fst (fun p hp => ne_of_gt hp.1)
  have hg' : ContinuousOn
      (Function.uncurry (fun y θ => Work.Spaces.K θ * Work.Spaces.pz f y θ / y
        - Work.Spaces.K θ * f y θ / y ^ 2)) Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun y θ => Work.Spaces.K θ * Work.Spaces.pz f y θ / y
        - Work.Spaces.K θ * f y θ / y ^ 2)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry (Work.Spaces.pz f) p / p.1
            - Work.Spaces.K p.2 * Function.uncurry f p / p.1 ^ 2 := by
      funext p; rcases p with ⟨y, θ⟩; rfl
    rw [hfun]
    exact ((hKc.mul hpc).div continuousOn_fst (fun p hp => ne_of_gt hp.1)).sub
      ((hKc.mul hfc).div (continuousOn_fst.pow 2)
        (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)))
  -- integrability of the base slice
  have hint : Integrable (fun θ => Work.Spaces.K θ * f x θ / x)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.of_bound (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hg hx)
      (3 * C / x) ?_
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hx]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (abs_K_le_three θ) (hb₀ x hxV θ hθ) (abs_nonneg _) (by norm_num)) hx.le
  -- the uniform a.e. bound on the candidate derivative over the strip
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      ‖Work.Spaces.K θ * Work.Spaces.pz f y θ / y - Work.Spaces.K θ * f y θ / y ^ 2‖
        ≤ 3 * C / (x / 2) + 3 * C / (x / 2) ^ 2 := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ y hy => ?_)
    have hy0 : 0 < y := hVpos y hy
    have h1 : |Work.Spaces.K θ * Work.Spaces.pz f y θ / y| ≤ 3 * C / y := by
      rw [abs_div, abs_mul, abs_of_pos hy0]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (abs_K_le_three θ) (hb₁ y hy θ hθ) (abs_nonneg _) (by norm_num)) hy0.le
    have h2' : |Work.Spaces.K θ * f y θ / y ^ 2| ≤ 3 * C / y ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg y)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (abs_K_le_three θ) (hb₀ y hy θ hθ) (abs_nonneg _) (by norm_num))
        (sq_nonneg y)
    have h3C : (0 : ℝ) ≤ 3 * C := by linarith
    have hhalf : 0 < x / 2 := by linarith
    have hsq : (x / 2) ^ 2 ≤ y ^ 2 := by nlinarith [hhalf, hy.1]
    have hb₁' : 3 * C / y ≤ 3 * C / (x / 2) :=
      div_le_div_of_nonneg_left h3C hhalf hy.1.le
    have hb₂' : 3 * C / y ^ 2 ≤ 3 * C / (x / 2) ^ 2 :=
      div_le_div_of_nonneg_left h3C (pow_pos hhalf 2) hsq
    rw [Real.norm_eq_abs]
    calc |Work.Spaces.K θ * Work.Spaces.pz f y θ / y - Work.Spaces.K θ * f y θ / y ^ 2|
        ≤ |Work.Spaces.K θ * Work.Spaces.pz f y θ / y| + |Work.Spaces.K θ * f y θ / y ^ 2| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (Work.Spaces.K θ * Work.Spaces.pz f y θ / y)
              (-(Work.Spaces.K θ * f y θ / y ^ 2))
      _ ≤ 3 * C / (x / 2) + 3 * C / (x / 2) ^ 2 := by linarith
  -- the pointwise derivative at every interior angle
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun z => Work.Spaces.K θ * f z θ / z)
        (Work.Spaces.K θ * Work.Spaces.pz f y θ / y - Work.Spaces.K θ * f y θ / y ^ 2) y := by
    intro θ hθ y hy
    have hy0 : 0 < y := hVpos y hy
    have hd : DifferentiableAt ℝ (Function.uncurry f) (y, θ) :=
      (h2.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hy0, hθ.1, hθ.2⟩))
    have h1 : HasDerivAt (fun z : ℝ => f z θ) (Work.Spaces.pz f y θ) y := by
      simpa only [Work.Spaces.pz] using
        (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt
    have h2' := (h1.const_mul (Work.Spaces.K θ)).div (hasDerivAt_id y) (ne_of_gt hy0)
    convert h2' using 1
    · funext z
      simp only [Pi.div_apply, id_eq]
    · simp only [id_eq]
      field_simp
  -- differentiation under the angular integral
  have key := Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0
    (g := fun y θ => Work.Spaces.K θ * f y θ / y)
    (g' := fun y θ => Work.Spaces.K θ * Work.Spaces.pz f y θ / y
      - Work.Spaces.K θ * f y θ / y ^ 2)
    (V := Set.Ioo (x / 2) (2 * x)) hV hxV hVpos hg hg' hint hbound hdiff
  have hfun : (fun y => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f y θ / y)
      = fun y => Work.Construction.L12dens f y := by
    funext y
    simp only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
  rw [hfun] at key
  exact key

end Work.FTS.StrongEps.E5Aux2.PT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.integrableOn_L12dens_of_aem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux3

/-- **The `L₁₂`-density of an `ℋ⁴_α`-datum is integrable on `(0,∞)`**, as soon as it is a.e.
strongly measurable there.

Route.  `HkMem α 4 F` gives `IntegrableOn (fun s => ∫_θ HkIntegrand α 4 F s θ) (Ioi 0)`
(the two sets `Ioi 0` and `Iz = Ici 0` differ by the null set `{0}`), hence, writing
`A s = √(∫_θ HkIntegrand α 4 F s θ)`, also `IntegrableOn (fun s => A s ^ 2) (Ioi 0)`.
Together with `Wlam ∈ L²` (`Work.Elliptic.psi_sq_integrable_aux`), AM–GM
`Wlam s · A s ≤ Wlam s ^ 2 + A s ^ 2` makes `s ↦ BK · (Wlam s · A s)` integrable, and the
pointwise domination `cc.abs_L12dens_le` with the assumed `hmeas` gives the conclusion by
`Integrable.mono'`. -/
theorem integrableOn_L12dens_of_aem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 F)
    (hmeas : MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens F)
      (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := by
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  -- the angular marginal `H` is nonnegative and integrable on `(0,∞)`
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hH_int : IntegrableOn H (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  -- its square root `A` is a.e. strongly measurable, with `A² = H`
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hH_int.aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) :=
    hH_int.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  -- the radial weight `Wlam` is square-integrable on `(0,∞)`
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.div continuousOn_id ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro s hs
        have h1 : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs]
        exact pow_ne_zero 2 (ne_of_gt h1)
    exact (show ContinuousOn Work.FTS.GalBasis.cc.Wlam (Set.Ioi 0) from hc).aestronglyMeasurable
      measurableSet_Ioi
  have hWlam2_int : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux
  -- AM–GM: `Wlam · A` is integrable
  have hWlamA_int : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s * A s) (Set.Ioi 0) := by
    refine (hWlam2_int.add hA2_int).mono' (hWlam_aesm.mul hA_aesm) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have h1 : 0 ≤ Work.FTS.GalBasis.cc.Wlam s := Work.FTS.GalBasis.cc.Wlam_nonneg hs.le
    have h2 : 0 ≤ A s := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2), Pi.add_apply]
    nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - A s)]
  -- the pointwise domination of the density
  refine (hWlamA_int.const_mul Work.FTS.GalBasis.cc.BK).mono' hmeas ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hb := Work.FTS.GalBasis.cc.abs_L12dens_le α F hmem hs
  calc |Work.Construction.L12dens F s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := by
        simpa only [hA, hH] using hb
    _ = Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by ring

end Work.FTS.StrongEps.E5Aux3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.integrable_angleDens_of_hkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the angular density `K θ · F r θ / r` of an `ℋ⁴_α`-datum

For `F ∈ ℋ⁴_α` (i.e. `Work.Spaces.HkMem α 4 F`), the function
`p ↦ K p.2 · F p.1 p.2 / p.1` is integrable for the product measure on `(0,∞) × Iθ`, with

`∫ ‖K θ · F r θ / r‖ ≤ 3·√(π/2)·√W2 · HkNorm α 4 F`.

**Route.**  On `Iθ` the identity `K θ · F r θ / r = Wlam r · (K θ·Sw θ·Gaz F r θ)` of
`GalBasis.cc` together with `|K·Sw| ≤ 3` and `|Gaz| ≤ √(HkIntegrand)` gives the *pointwise*
bound

`|K θ · F r θ / r| ≤ 3·Wlam r·√(HkIntegrand α 4 F r θ)`   (`r > 0`, `θ ∈ Iθ`),

which, after Cauchy–Schwarz in `θ` (constant `1`, measure `π/2`), upgrades to the *slice*
bound

`∫_θ |K θ · F r θ / r| ≤ 3·√(π/2)·Wlam r·√(H r)`,   `H r := ∫_θ HkIntegrand α 4 F r θ`.

The pointwise form also gives, for a.e. `r`, the integrability of the `θ`-slice of the density
(the majorant `3·Wlam r·√(HkIntegrand)` is integrable since `√x ≤ x + 1` on the finite measure
`Iθ`), and the slice bound gives the integrability of the marginal against the majorant
`3·√(π/2)·(Wlam r·√(H r))` (AM–GM for `Wlam·√H ≤ (Wlam² + H)/2`).  Hence
`MeasureTheory.integrable_prod_iff` applies and the density is integrable on the product.
Tonelli then converts the integral of its norm into the iterated integral, the slice bound
applies a.e., and Cauchy–Schwarz in the radial variable
(`Work.Elliptic.psi_sq_integrable_aux` for `∫Wlam² = W2`, and `∫_{(0,∞)} H = HkSq α 4 F`)
gives the stated constant.

`hslice` (a.e. strong measurability of the slices) is used exactly for the slice integrability,
`hAE` (joint a.e. strong measurability) for `integrable_prod_iff` and for the marginal.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.GalBasis.cc (Wlam W2 Sw Gaz K_mul_h_div_s_eq Wlam_nonneg
  abs_K_mul_Sw_le_three abs_Gaz_le_sqrt_HkIntegrand BK)

namespace Work.FTS.StrongEps.E5Aux3

set_option maxHeartbeats 1000000

/-! ## Elementary angular facts -/

/-- `∫_{Iθ} 1 = π/2`. -/
private lemma integral_one_Iθ : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = π / 2 := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Work.Spaces.Iθ]
  simp only [Measure.real, Real.volume_Icc, sub_zero]
  exact ENNReal.toReal_ofReal (by positivity)

/-- On the angular interval the square root of the `ℋ⁴`-integrand is integrable: on the
finite-measure set `Iθ` the elementary bound `√x ≤ x + 1` reduces this to the integrability
of `HkIntegrand`. -/
private lemma integrableOn_sqrt_HkIntegrand {α s : ℝ} {F : ℝ → ℝ → ℝ}
    (hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)) Work.Spaces.Iθ := by
  have hcone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsum := hint.add hcone
  refine Integrable.mono' hsum ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable hint.aestronglyMeasurable
  · filter_upwards with θ
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Pi.add_apply]
    have hnn : 0 ≤ Work.Spaces.HkIntegrand α 4 F s θ :=
      Work.Spaces.HkIntegrand_nonneg α 4 F s θ
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩

/-! ## The pointwise bound and the slice bound -/

/-- **Pointwise domination of the angular density.**  For `r > 0` and `θ ∈ Iθ`,
`|K θ · F r θ / r| ≤ 3·Wlam r·√(HkIntegrand α 4 F r θ)`. -/
private lemma abs_K_mul_F_div_le_sqrt {α : ℝ} {F : ℝ → ℝ → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * F s θ / s|
      ≤ 3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by
  rw [K_mul_h_div_s_eq F hs θ hθ, abs_mul, abs_of_nonneg (Wlam_nonneg hs.le)]
  have h1 : |Work.Spaces.K θ * Sw θ * Gaz F s θ|
      ≤ 3 * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by
    rw [abs_mul]
    exact mul_le_mul (abs_K_mul_Sw_le_three hθ) (abs_Gaz_le_sqrt_HkIntegrand α F s θ)
      (abs_nonneg _) (by norm_num)
  calc Wlam s * |Work.Spaces.K θ * Sw θ * Gaz F s θ|
      ≤ Wlam s * (3 * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)) :=
        mul_le_mul_of_nonneg_left h1 (Wlam_nonneg hs.le)
    _ = 3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by ring

/-- **The slice bound.**  For `r > 0`, the integral over `θ ∈ Iθ` of the absolute value of the
angular density is dominated by `3·√(π/2)·Wlam r·√(H r)`, with `H r := ∫_θ HkIntegrand`. -/
private lemma slice_abs_le {α : ℝ} {F : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 F) {s : ℝ}
    (hs : 0 < s) :
    (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * F s θ / s|)
      ≤ 3 * Real.sqrt (π / 2) * (Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ)) := by
  have hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ :=
    hmem.1 s (Set.mem_Ici.mpr hs.le)
  have hsqrt_int : IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ))
      Work.Spaces.Iθ := integrableOn_sqrt_HkIntegrand hint
  -- the pointwise domination
  have hmaj_int : IntegrableOn
      (fun θ => 3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)) Work.Spaces.Iθ :=
    hsqrt_int.const_mul _
  have hstep1 : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * F s θ / s|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
      hmaj_int ?_
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall fun θ hθ => abs_K_mul_F_div_le_sqrt (α := α) hs hθ)
  have hstep2 : (∫ θ in Work.Spaces.Iθ,
        3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ))
      = 3 * Wlam s
        * ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) :=
    MeasureTheory.integral_const_mul _ _
  -- Cauchy–Schwarz in `θ` with the constant function `1`
  have hHnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hcs : (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ))
      ≤ Real.sqrt (π / 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ) := by
    have hu : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq
        (f := fun _ : ℝ => (1 : ℝ)) aestronglyMeasurable_const).mpr ?_
      simpa using (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Work.Spaces.Iθ)
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have hv : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)) 2
        (volume.restrict Work.Spaces.Iθ) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq
        hsqrt_int.aestronglyMeasurable).mpr ?_
      exact hint.congr (Eventually.of_forall fun θ =>
        (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 F s θ)).symm)
    have h := Work.Spaces.cs_integral hu hv
    simp only [one_mul] at h
    have h1 : (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = π / 2 := by
      simpa using integral_one_Iθ
    have h2 : (∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ :=
      integral_congr_ae (Eventually.of_forall fun θ =>
        Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 F s θ))
    rw [h1, h2] at h
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) :=
      integral_nonneg fun θ => Real.sqrt_nonneg _
    have hstep := Real.sqrt_le_sqrt h
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ π / 2)] at hstep
    exact hstep
  calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * F s θ / s|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := hstep1
    _ = 3 * Wlam s
          * ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := hstep2
    _ ≤ 3 * Wlam s * (Real.sqrt (π / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ)) :=
        mul_le_mul_of_nonneg_left hcs (mul_nonneg (by norm_num) (Wlam_nonneg hs.le))
    _ = 3 * Real.sqrt (π / 2) * (Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ)) := by ring

/-- **AM–GM in the radial variable.**  `Wlam·√H` is integrable on `(0,∞)` when `H` is,
because `Wlam·√H ≤ Wlam² + H` and `Wlam²` is integrable (`Work.Elliptic.psi_sq_integrable_aux`). -/
private lemma integrableOn_wlam_sqrt {H : ℝ → ℝ} (hHnn : ∀ s, 0 ≤ H s)
    (hH : IntegrableOn H (Set.Ioi 0)) :
    IntegrableOn (fun s => Wlam s * Real.sqrt (H s)) (Set.Ioi 0) := by
  have hA_aesm : AEStronglyMeasurable (fun s => Real.sqrt (H s))
      (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hH.aestronglyMeasurable
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.div continuousOn_id ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro s hs
        have h1 : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs]
        exact pow_ne_zero 2 (ne_of_gt h1)
    exact (show ContinuousOn Wlam (Set.Ioi 0) from hc).aestronglyMeasurable measurableSet_Ioi
  have hWlam2_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hA2_int : IntegrableOn (fun s => Real.sqrt (H s) ^ 2) (Set.Ioi 0) :=
    hH.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  refine (hWlam2_int.add hA2_int).mono' (hWlam_aesm.mul hA_aesm) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
  have h1 : 0 ≤ Wlam s := Wlam_nonneg hs.le
  have h2 : 0 ≤ Real.sqrt (H s) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2), Pi.add_apply]
  nlinarith [sq_nonneg (Wlam s - Real.sqrt (H s))]

/-! ## The theorem -/

theorem integrable_angleDens_of_hkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 F)
    (hAE : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * F r θ / r)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p : ℝ × ℝ, ‖Work.Spaces.K p.2 * F p.1 p.2 / p.1‖
        ∂((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ 3 * Real.sqrt (π / 2) * Real.sqrt Work.FTS.GalBasis.cc.W2
          * Work.Spaces.HkNorm α 4 F := by
  set f : ℝ × ℝ → ℝ := fun p => Work.Spaces.K p.2 * F p.1 p.2 / p.1 with hf
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ with hH
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hH_int : IntegrableOn H (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  -- the majorant `3√(π/2)·(Wlam·√H)` is integrable
  have hg_int : Integrable (fun s => 3 * Real.sqrt (π / 2) * (Wlam s * Real.sqrt (H s)))
      (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_wlam_sqrt hHnn hH_int).const_mul (3 * Real.sqrt (π / 2))
  -- the a.e. slice bound
  have hslice_bd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      (∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
        ≤ 3 * Real.sqrt (π / 2) * (Wlam s * Real.sqrt (H s)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have h1 : (∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
        = ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * F s θ / s| := by
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hf, Real.norm_eq_abs]
    rw [h1]
    exact slice_abs_le hmem hs
  have hslice_bd_norm : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      ‖∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ)‖
        ≤ 3 * Real.sqrt (π / 2) * (Wlam s * Real.sqrt (H s)) :=
    hslice_bd.mono fun s h => by
      rwa [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
  -- a.e. integrability of the slices
  have hslice_int : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      Integrable (fun θ => f (s, θ)) (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hslice, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs hsI
    have hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ :=
      hmem.1 s (Set.mem_Ici.mpr hsI.le)
    refine Integrable.mono'
      ((integrableOn_sqrt_HkIntegrand hint).const_mul (3 * Wlam s)) hs ?_
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall fun θ hθ => by
        simpa only [hf, Real.norm_eq_abs] using abs_K_mul_F_div_le_sqrt (α := α) hsI hθ)
  -- integrability of the marginal
  have hmarg_aesm : AEStronglyMeasurable
      (fun s => ∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Ioi 0)) := (hAE.norm).integral_prod_right'
  have hmarg_int : Integrable (fun s => ∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Ioi 0)) :=
    Integrable.mono' hg_int hmarg_aesm hslice_bd_norm
  -- integrability of the density on the product
  have hInt : Integrable f
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff hAE).mpr ⟨hslice_int, hmarg_int⟩
  refine ⟨hInt, ?_⟩
  -- `∫_{(0,∞)} H = HkSq α 4 F`
  have hHsq : (∫ s in Set.Ioi 0, H s) = Work.Spaces.HkSq α 4 F := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton (0 : ℝ)))]
    rfl
  have hsqrtH : Real.sqrt (∫ s in Set.Ioi 0, H s) = Work.Spaces.HkNorm α 4 F := by
    rw [hHsq, Work.Spaces.HkNorm]
  have hconst : (0 : ℝ) ≤ 3 * Real.sqrt (π / 2) := by
    have hp := Real.pi_pos
    positivity
  rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => ‖f p‖) hInt.norm]
  calc ∫ s, ∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ)
        ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫ s, 3 * Real.sqrt (π / 2) * (Wlam s * Real.sqrt (H s))
          ∂(volume.restrict (Set.Ioi 0)) :=
        integral_mono_ae hmarg_int hg_int hslice_bd
    _ = 3 * Real.sqrt (π / 2)
          * ∫ s, Wlam s * Real.sqrt (H s) ∂(volume.restrict (Set.Ioi 0)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 3 * Real.sqrt (π / 2) * (Real.sqrt W2 * Real.sqrt (∫ s in Set.Ioi 0, H s)) :=
        mul_le_mul_of_nonneg_left (WlamSqrtMarginal hHnn hH_int) hconst
    _ = 3 * Real.sqrt (π / 2) * (Real.sqrt W2 * Work.Spaces.HkNorm α 4 F) := by rw [hsqrtH]
    _ = 3 * Real.sqrt (π / 2) * Real.sqrt W2 * Work.Spaces.HkNorm α 4 F := by ring

end Work.FTS.StrongEps.E5Aux3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.ZmulBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2hatOAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The explicit `n`-only constant of the `z`-multiplier estimate. -/
def zmulC (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1

lemma zmulC_pos (n : ℕ) : 0 < zmulC n := by
  unfold zmulC; positivity

/-- **The `ℋⁿ`-integrand of a product with a `z`-only multiplier**, with a constant
independent of `α`: for `ψ` of class `C^∞` on `(0,∞)` whose `Zop`-iterates up to order `n`
are bounded by `K ≥ 0`, and `f` of class `SmoothOpen`,

`HkIntegrand α n (ψ·f) z θ ≤ zmulC n ·(1+K)²·HkIntegrand α n f z θ`

at every point of the open quadrant. -/
theorem HkIntegrand_zmul_SO (α : ℝ) (n : ℕ) :
    ∀ (ψ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] ψ z| ≤ K) →
      (∀ m : ℕ, ContDiffOn ℝ m ψ (Set.Ioi 0)) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (fun z θ => ψ z * f z θ) z θ
          ≤ zmulC n * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by
  intro ψ K hK hKψ hψ f hf z hz θ hθ
  -- basic facts at the point `(z,θ)`
  have hzpos : 0 < z := hz
  have hQnn : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  -- the binomial coefficients are bounded by `2^n`
  have hchoose : ∀ (m b : ℕ), m ≤ n → |((m.choose b : ℕ) : ℝ)| ≤ (2 : ℝ) ^ n := by
    intro m b hmn
    calc |((m.choose b : ℕ) : ℝ)| = ((m.choose b : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow m b
      _ = (2 : ℝ) ^ m := by push_cast; ring
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hmn
  -- a partial sum of the first (radial) block is bounded by the whole integrand
  have hzsum : ∀ i : ℕ, i ≤ n →
      (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Work.Spaces.HkIntegrand α n f z θ := by
    intro i hin
    rw [Work.Spaces.HkIntegrand]
    have hsub : (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (∑ m ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro m hm
          have hm' : m < i + 1 := Finset.mem_range.mp hm
          exact Finset.mem_range.mpr (by omega))
        (fun m _ _ => sq_nonneg _)
    exact le_trans hsub (le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α n f z θ))
  -- a partial sum of the second (mixed) block is bounded by `(j+1)` integrands
  have hmsum : ∀ i j : ℕ, 1 ≤ i → i + j ≤ n →
      (∑ m ∈ Finset.range (j + 1),
        (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ := by
    intro i j hi1 hij
    calc (∑ m ∈ Finset.range (j + 1),
          (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∑ _m ∈ Finset.range (j + 1), Work.Spaces.HkIntegrand α n f z θ :=
          Finset.sum_le_sum fun m hm => by
            have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            exact Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i m hi1 (by omega)
      _ = ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- the two blocks of the left-hand side are handled separately
  have hZi : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
          * Work.Spaces.HkIntegrand α n f z θ := by
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ := by
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      -- Leibniz for `D_z^i (ψ · f)`
      have hleib : Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] ψ z * Work.Spaces.DzIter (i - b) f z θ) :=
        DzIter_zmul_SO i ψ f hψ hf hzpos hθ
      -- multiply by the weight and distribute
      have hmul : Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] ψ z * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
        rw [hleib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [hmul]
      -- Cauchy–Schwarz on the binomial convolution
      have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le
        (i := i) (D := (2 : ℝ) ^ n) (K := K) hK
        (x := fun b => Work.Spaces.Zop^[b] ψ z)
        (y := fun m => Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (fun b hb => hKψ b (le_trans hb hin) z hz)
        (fun b hb => hchoose i b hin)
      have hbin' : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.Zop^[b] ψ z * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          ≤ (((i : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
              * (∑ m ∈ Finset.range (i + 1),
                  (Work.Spaces.DzIter m f z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ))
                        ^ (Work.Spaces.eta / 2))) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hbin
      refine le_trans hbin' ?_
      have hconst : (((i : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
          ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by
        have hbase : ((i : ℝ) + 1) * (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right
            (by
              have : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hin
              linarith)
            (by positivity)
        have hle : ((i : ℝ) + 1) * (2 : ℝ) ^ n * K ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n * K :=
          mul_le_mul_of_nonneg_right hbase hK
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK) hle 2
      exact mul_le_mul hconst (hzsum i hin) (Finset.sum_nonneg fun m _ => sq_nonneg _)
        (by positivity)
    calc (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1), ((((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ) := Finset.sum_le_sum hterm
      _ = (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hMi : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
          * Work.Spaces.HkIntegrand α n f z θ := by
    have hsummand : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · rw [if_pos hc]
        obtain ⟨hi1, hij⟩ := hc
        have hin : i ≤ n := by omega
        have hjn : j ≤ n := by omega
        -- Leibniz for `D_z^j D_θ^i (ψ · f)`
        have hexp : Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] ψ z * Work.Spaces.mixed (j - b) i f z θ) :=
          mixed_zmul_SO j i ψ f hψ hf hzpos hθ
        have hmul : Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
              * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] ψ z
                    * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ)) := by
          rw [hexp, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hmul]
        have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le
          (i := j) (D := (2 : ℝ) ^ n) (K := K) hK
          (x := fun b => Work.Spaces.Zop^[b] ψ z)
          (y := fun m => Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ)
          (fun b hb => hKψ b (le_trans hb hjn) z hz)
          (fun b hb => hchoose j b hjn)
        have hbin' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] ψ z * (Work.Spaces.mixed (j - b) i f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2
            ≤ (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (∑ m ∈ Finset.range (j + 1),
                    (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hbin
        refine le_trans hbin' ?_
        have hconst : (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by
          have hbase : ((j : ℝ) + 1) * (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right
              (by
                have : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
                linarith)
              (by positivity)
          have hle : ((j : ℝ) + 1) * (2 : ℝ) ^ n * K ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n * K :=
            mul_le_mul_of_nonneg_right hbase hK
          exact pow_le_pow_left₀
            (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK) hle 2
        have hA : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
          linarith
        have hAZ : 0 ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by positivity
        calc (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
              * (∑ m ∈ Finset.range (j + 1),
                  (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ) :=
              mul_le_mul hconst (hmsum i j hi1 hij)
                (Finset.sum_nonneg fun m _ => sq_nonneg _) hAZ
          _ ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (((n : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hQnn) hAZ
          _ = (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
                * Work.Spaces.HkIntegrand α n f z θ := by ring
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hQnn
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (n + 1),
            ((((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
              * Work.Spaces.HkIntegrand α n f z θ) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hsummand i hi j hj
      _ = (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- add the two blocks
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) ?_
  have hKsq : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith [hK]
  have hkey : (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
        * Work.Spaces.HkIntegrand α n f z θ
      + (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
        * Work.Spaces.HkIntegrand α n f z θ
      = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α n f z θ := by ring
  rw [hkey]
  have h0 : 0 ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) := by
    positivity
  have hstep1 : ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α n f z θ
      ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α n f z θ := by
    calc ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
          * Work.Spaces.HkIntegrand α n f z θ
        = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
            * (K ^ 2 * Work.Spaces.HkIntegrand α n f z θ) := by ring
      _ ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
            * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKsq hQnn) h0
      _ = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ := by ring
  refine le_trans hstep1 ?_
  have h1 : 0 ≤ (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ :=
    mul_nonneg (by positivity) hQnn
  rw [zmulC]
  calc ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α n f z θ
      = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) := by ring
    _ ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) :=
        mul_le_mul_of_nonneg_right (by linarith) h1
    _ = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1) * (1 + K) ^ 2
          * Work.Spaces.HkIntegrand α n f z θ := by ring

end Work.FTS.StrongEps.EpsE4Thr.E2hatOAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.L12Add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Additivity of `L₁₂` over `F = F_* + W` -/

/-- **`L₁₂(F_* + W) = L₁₂(F_*) + L₁₂(W)` as functions of `z`, for `z ≥ 0`.**  This is
`Work.Stability.L12Add` with its three integrability inputs discharged from
`SmoothOpen W` and `HkMem α 4 W`. -/
theorem L12Ftot_add {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W : ℝ → ℝ → ℝ}
    (hWs : Work.FTS.EllipticEst.SmoothOpen W) (hWm : Work.Spaces.HkMem α 4 W) :
    ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z := by
  intro z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  have h1 : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) (Set.Ioi z) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz0
  have h2 : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K W) (Set.Ioi z) := by
    have hw : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K W) (Set.Ioi (0:ℝ)) :=
      Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hWs hWm
    exact hw.mono_set (fun x hx => lt_of_le_of_lt hz0 hx)
  have h3 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (Work.Construction.Fstar α s θ + W s θ) / s)
      Work.Spaces.Iθ := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hz0 hs
    have hFs : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α s θ / s) Work.Spaces.Iθ :=
      Work.Stability.integrableOn_slice_Fstar α hα s
    have hW : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * W s θ / s) Work.Spaces.Iθ :=
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hWs hWm hs0
    refine (hFs.add hW).congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [Pi.add_apply]
    ring
  exact Work.Stability.L12Add α hα h1 h2 h3



end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Bridge.L12densLGamma =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero.Bridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The a.e. angular-slice integrability of `∂_z f` -/

/-- For almost every `r > 0` the angular slice `θ ↦ K(θ)·∂_z f(r,θ)` is integrable on
`Iθ`.  This is the a.e.-slice form of the joint integrability hypothesis `hint`
(Fubini on the product `(0,∞) × Iθ`). -/
theorem ae_integrableOn_K_pz_of_hint {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f r θ)
        Work.Spaces.Iθ := by
  have h := hint
  rw [MeasureTheory.IntegrableOn, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← Measure.prod_restrict] at h
  filter_upwards [h.prod_right_ae] with r hr
  simpa [Work.Spaces.Iθ, MeasureTheory.IntegrableOn, Function.uncurry] using hr

/-! ## Two elementary integral identities -/

/-- The angular normalisation: `∫_{Iθ} K(θ)Γ(θ) dθ = c(α)`. -/
theorem integral_K_Gam_eq_c_bridge (α : ℝ) :
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ = Work.Spaces.c α := by
  simp only [Work.Spaces.c]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- Additivity of a set integral over a sum of four functions. -/
theorem setIntegral_add_four_bridge {s : Set ℝ} {a b c d : ℝ → ℝ}
    (ha : MeasureTheory.IntegrableOn a s) (hb : MeasureTheory.IntegrableOn b s)
    (hc : MeasureTheory.IntegrableOn c s) (hd : MeasureTheory.IntegrableOn d s) :
    (∫ x in s, (a x + b x + c x + d x))
      = (∫ x in s, a x) + (∫ x in s, b x) + (∫ x in s, c x) + (∫ x in s, d x) := by
  have h1 : (∫ x in s, a x) + (∫ x in s, b x) = (∫ x in s, a x + b x) :=
    (MeasureTheory.integral_add ha hb).symm
  have h2 : (∫ x in s, a x + b x) + (∫ x in s, c x) = (∫ x in s, a x + b x + c x) :=
    (MeasureTheory.integral_add (ha.add hb) hc).symm
  have h3 : (∫ x in s, a x + b x + c x) + (∫ x in s, d x)
      = (∫ x in s, a x + b x + c x + d x) :=
    (MeasureTheory.integral_add ((ha.add hb).add hc) hd).symm
  rw [← h3, ← h2, ← h1]

/-! ## The density identity, a.e. in `r` -/

/-- **The density of `𝓛_Γ f` along the radial variable**, for almost every `r > 0`, in
terms of the density of `f`, the angular moment of `∂_z f` and the tail integral
`L₁₂(f)(r) = ∫_r^∞ L₁₂dens f`.  This is the identity on which the `L¹`-statement rests. -/
theorem L12dens_LGamma_ae_bridge {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ / r)
        Work.Spaces.Iθ) :
    (fun r : ℝ => Work.Construction.L12dens (Work.Coercivity.LGamma α f) r)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
    (fun r : ℝ => Work.Construction.L12dens f r
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
      - 2 * Work.Construction.L12dens f r / (1 + r)
      - 2 * Work.Coercivity.L12f f r / (1 + r) ^ 2) := by
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  have hGK : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    simpa only [mul_comm] using Work.Spaces.CAux.integrableOn_GamK α hα
  filter_upwards [ae_integrableOn_K_pz_of_hint hint,
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hpz hr
  have hrpos : 0 < r := hr
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have h1r : (1 : ℝ) + r ≠ 0 := by positivity
  -- the four elementary pieces of the density of `𝓛_Γ f`
  set g1 : ℝ → ℝ := fun θ => Work.Spaces.K θ * f r θ / r with hg1
  set g2 : ℝ → ℝ := fun θ => Work.Spaces.K θ * Work.Spaces.pz f r θ with hg2
  set g3 : ℝ → ℝ := fun θ => (-2 / (1 + r)) * g1 θ with hg3
  set g4 : ℝ → ℝ :=
    fun θ => (-(2 * Work.Coercivity.L12f f r / (Work.Spaces.c α * (1 + r) ^ 2)))
      * (Work.Spaces.K θ * Work.Spaces.Gam α θ) with hg4
  have h1 : MeasureTheory.IntegrableOn g1 Work.Spaces.Iθ := hslice r hrpos
  have h2 : MeasureTheory.IntegrableOn g2 Work.Spaces.Iθ := hpz
  have h3 : MeasureTheory.IntegrableOn g3 Work.Spaces.Iθ := by
    rw [hg3]; exact h1.const_mul _
  have h4 : MeasureTheory.IntegrableOn g4 Work.Spaces.Iθ := by
    rw [hg4]; exact hGK.const_mul _
  -- pointwise expansion of the density integrand
  have hpt : ∀ θ : ℝ,
      Work.Spaces.K θ * Work.Coercivity.LGamma α f r θ / r = (g1 + g2 + g3 + g4) θ := by
    intro θ
    simp only [hg1, hg2, hg3, hg4, Pi.add_apply, Work.Coercivity.LGamma, Work.Coercivity.L,
      Work.Spaces.Dz]
    field_simp
    ring
  -- the density is the integral of the four pieces
  have hG : Work.Construction.L12dens (Work.Coercivity.LGamma α f) r
      = ∫ θ in Work.Spaces.Iθ, (g1 + g2 + g3 + g4) θ := by
    rw [show Work.Construction.L12dens (Work.Coercivity.LGamma α f) r
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Coercivity.LGamma α f r θ / r
        from rfl]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)
  -- split the integral into the four pieces
  have hsplit : (∫ θ in Work.Spaces.Iθ, (g1 + g2 + g3 + g4) θ)
      = (∫ θ in Work.Spaces.Iθ, g1 θ) + (∫ θ in Work.Spaces.Iθ, g2 θ)
        + (∫ θ in Work.Spaces.Iθ, g3 θ) + (∫ θ in Work.Spaces.Iθ, g4 θ) :=
    setIntegral_add_four_bridge h1 h2 h3 h4
  -- value of each piece
  have hu1 : (∫ θ in Work.Spaces.Iθ, g1 θ) = Work.Construction.L12dens f r := by
    rw [hg1]; rfl
  have hu2 : (∫ θ in Work.Spaces.Iθ, g2 θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ := by
    rw [hg2]
  have hu3 : (∫ θ in Work.Spaces.Iθ, g3 θ)
      = (-2 / (1 + r)) * Work.Construction.L12dens f r := by
    have h3' : (∫ θ in Work.Spaces.Iθ, g3 θ)
        = (-2 / (1 + r)) * (∫ θ in Work.Spaces.Iθ, g1 θ) := by
      rw [hg3]; exact MeasureTheory.integral_const_mul _ _
    rw [h3', hu1]
  have hu4 : (∫ θ in Work.Spaces.Iθ, g4 θ)
      = (-(2 * Work.Coercivity.L12f f r / (Work.Spaces.c α * (1 + r) ^ 2)))
        * Work.Spaces.c α := by
    have h4' : (∫ θ in Work.Spaces.Iθ, g4 θ)
        = (-(2 * Work.Coercivity.L12f f r / (Work.Spaces.c α * (1 + r) ^ 2)))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ) := by
      rw [hg4]; exact MeasureTheory.integral_const_mul _ _
    rw [h4', integral_K_Gam_eq_c_bridge]
  -- assemble
  have hmain : Work.Construction.L12dens (Work.Coercivity.LGamma α f) r
      = Work.Construction.L12dens f r
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
        - 2 * Work.Construction.L12dens f r / (1 + r)
        - 2 * Work.Coercivity.L12f f r / (1 + r) ^ 2 := by
    rw [hG, hsplit, hu1, hu2, hu3, hu4]
    field_simp
    ring
  exact hmain

/-! ## Termwise `L¹`-bookkeeping -/

/-- The transformed term `r ↦ A r/(1+r)` is integrable as soon as `A ∈ L¹((0,∞))`. -/
theorem integrableOn_div_oneAdd_of_integrableOn {A : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun r : ℝ => A r / (1 + r)) (Set.Ioi 0) := by
  have hinv : AEStronglyMeasurable (fun r : ℝ => (1 + r)⁻¹)
      (volume.restrict (Set.Ioi 0)) :=
    (ContinuousOn.inv₀ (by fun_prop : ContinuousOn (fun r : ℝ => 1 + r) (Set.Ioi 0))
      (fun r hr => by have h := Set.mem_Ioi.mp hr; positivity)).aestronglyMeasurable
        measurableSet_Ioi
  refine hA.norm.mono' ?_ ?_
  · have hmem : AEStronglyMeasurable (A * fun r : ℝ => (1 + r)⁻¹)
        (volume.restrict (Set.Ioi 0)) := hA.aestronglyMeasurable.mul hinv
    refine hmem.congr ?_
    filter_upwards with r
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun r hr => ?_
    have hrpos : 0 < r := hr
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + r)]
    exact div_le_self (abs_nonneg _) (by linarith : (1 : ℝ) ≤ 1 + r)

/-- `(1+r)^{-2}` is integrable on `(0,∞)`: the two summands of the splitting
`(0,∞) = (0,1] ∪ (1,∞)` are handled by boundedness on a finite interval resp. by the
tail `r ↦ r^{-2}`. -/
theorem integrableOn_oneAdd_rpow_neg_two_Ioi_zero :
    MeasureTheory.IntegrableOn (fun r : ℝ => (1 + r) ^ (-2 : ℝ)) (Set.Ioi 0) := by
  have hbase : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Ici 0) := by
    have hunion : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ici 0 := by
      ext z
      simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
      constructor
      · rintro (⟨h1, h2⟩ | h) <;> linarith
      · intro h'
        rcases lt_or_ge z 1 with hz | hz
        · exact Or.inl ⟨h', le_of_lt hz⟩
        · exact Or.inr hz
    have hIcc : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Icc 0 1) := by
      refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ 1 ?_
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      · refine ((continuousOn_const.add continuousOn_id).rpow_const ?_).aestronglyMeasurable
          measurableSet_Icc
        intro z hz
        exact Or.inl (by simp only [Pi.add_apply, id_eq]; linarith [hz.1])
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hz.1]) _)]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hz.1]) (by norm_num)
    have hInt :=
      (Work.FTS.LocData.HkSqAux.integrableOn_and_integral_Ici_oneAdd_rpow_neg_two 1 one_pos).1
    rw [← hunion]; exact hIcc.union hInt
  exact hbase.mono_set (fun x hx => Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hx)))

/-- The tail-integral term `r ↦ (∫_r^∞ A)/(1+r)²` is integrable as soon as
`A ∈ L¹((0,∞))`: the tail is bounded by `∫_0^∞ |A|` and `(1+r)^{-2}` is integrable. -/
theorem integrableOn_Ioi_integral_div_quad_of_integrableOn {A : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun r : ℝ => (∫ s in Set.Ioi r, A s) / (1 + r) ^ 2)
      (Set.Ioi 0) := by
  set M : ℝ := ∫ s in Set.Ioi 0, ‖A s‖ with hM
  have hAbs : MeasureTheory.IntegrableOn (fun s : ℝ => ‖A s‖) (Set.Ioi 0) := hA.norm
  -- the tail is bounded by `M`
  have hbd : ∀ r ∈ Set.Ioi (0 : ℝ), ‖∫ s in Set.Ioi r, A s‖ ≤ M := by
    intro r hr
    have hrpos : 0 < r := hr
    have hmono : (∫ s in Set.Ioi r, ‖A s‖) ≤ M := by
      rw [hM]
      exact MeasureTheory.setIntegral_mono_set hAbs
        (ae_of_all _ fun s => norm_nonneg _)
        (ae_of_all _ fun s hs => lt_of_lt_of_le hrpos (le_of_lt (Set.mem_Ioi.mp hs)))
    calc ‖∫ s in Set.Ioi r, A s‖ = ‖∫ s, A s ∂(volume.restrict (Set.Ioi r))‖ := rfl
      _ ≤ ∫ s, ‖A s‖ ∂(volume.restrict (Set.Ioi r)) :=
          MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi r)) A
      _ = ∫ s in Set.Ioi r, ‖A s‖ := rfl
      _ ≤ M := hmono
  -- the majorant `M(1+r)^{-2}`
  have hIntDomR : MeasureTheory.IntegrableOn (fun r : ℝ => (1 + r) ^ (-2 : ℝ)) (Set.Ioi 0) :=
    integrableOn_oneAdd_rpow_neg_two_Ioi_zero
  have hIntDomAux : MeasureTheory.IntegrableOn
      (fun r : ℝ => M * (1 + r) ^ (-2 : ℝ)) (Set.Ioi 0) :=
    MeasureTheory.Integrable.const_mul hIntDomR M
  have hIntDom : MeasureTheory.IntegrableOn (fun r : ℝ => M / (1 + r) ^ 2) (Set.Ioi 0) := by
    refine hIntDomAux.congr_fun_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hpos : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
    rw [div_eq_mul_inv, Real.rpow_neg hpos.le, Real.rpow_ofNat]
  refine hIntDom.mono' ?_ ?_
  · have hcont : ContinuousOn (fun r => ∫ s in Set.Ioi r, A s) (Set.Ioi 0) :=
      hA.continuousOn_Ici_primitive_Ioi.mono Set.Ioi_subset_Ici_self
    have h1 : AEStronglyMeasurable (fun r => ∫ s in Set.Ioi r, A s)
        (volume.restrict (Set.Ioi 0)) := hcont.aestronglyMeasurable measurableSet_Ioi
    have hinv : AEStronglyMeasurable (fun r : ℝ => ((1 + r) ^ 2)⁻¹)
        (volume.restrict (Set.Ioi 0)) :=
      (ContinuousOn.inv₀ (by fun_prop : ContinuousOn (fun r : ℝ => (1 + r) ^ 2) (Set.Ioi 0))
        (fun r hr => by have h := Set.mem_Ioi.mp hr; positivity)).aestronglyMeasurable
          measurableSet_Ioi
    have hmem : AEStronglyMeasurable
        ((fun r => ∫ s in Set.Ioi r, A s) * fun r : ℝ => ((1 + r) ^ 2)⁻¹)
        (volume.restrict (Set.Ioi 0)) := h1.mul hinv
    refine hmem.congr ?_
    filter_upwards with r
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun r hr => ?_
    have hpos : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
    have hsq : (0 : ℝ) < (1 + r) ^ 2 := by positivity
    have h1 : ‖(∫ s in Set.Ioi r, A s) / (1 + r) ^ 2‖
        = ‖∫ s in Set.Ioi r, A s‖ / (1 + r) ^ 2 := by
      rw [norm_div, Real.norm_of_nonneg hsq.le]
    rw [h1]
    exact div_le_div_of_nonneg_right (hbd r hr) hsq.le

/-! ## The requested bridge lemma -/

theorem L12densLGamma {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hintL2 : MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi 0))
    (hmd : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
      (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Coercivity.LGamma α f)) (Set.Ioi 0) := by
  -- the angular slices of the density integrand of `f` are integrable, for every `r > 0`
  have hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ / r)
        Work.Spaces.Iθ :=
    fun r hr => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hsm hmem hr
  have hae := L12dens_LGamma_ae_bridge hα hα1 hint hslice
  have h3' : MeasureTheory.IntegrableOn
      (fun r : ℝ => 2 * (Work.Construction.L12dens f r / (1 + r))) (Set.Ioi 0) :=
    (integrableOn_div_oneAdd_of_integrableOn hintL2).const_mul 2
  have h3 : MeasureTheory.IntegrableOn
      (fun r : ℝ => 2 * Work.Construction.L12dens f r / (1 + r)) (Set.Ioi 0) := by
    refine h3'.congr_fun_ae ?_
    filter_upwards with r
    ring
  have h4' : MeasureTheory.IntegrableOn
      (fun r : ℝ => 2 * ((∫ s in Set.Ioi r, Work.Construction.L12dens f s) / (1 + r) ^ 2))
      (Set.Ioi 0) :=
    (integrableOn_Ioi_integral_div_quad_of_integrableOn
      (A := Work.Construction.L12dens f) hintL2).const_mul 2
  have h4 : MeasureTheory.IntegrableOn
      (fun r : ℝ => 2 * Work.Coercivity.L12f f r / (1 + r) ^ 2) (Set.Ioi 0) := by
    refine h4'.congr_fun_ae ?_
    filter_upwards with r
    simp only [div_eq_mul_inv, Work.Coercivity.L12f, Work.FM.L12,
      Work.Construction.L12dens]
    ring
  have hSum : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Construction.L12dens f r
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
        - 2 * Work.Construction.L12dens f r / (1 + r)
        - 2 * Work.Coercivity.L12f f r / (1 + r) ^ 2) (Set.Ioi 0) :=
    ((hintL2.add hmd).sub h3).sub h4
  exact hSum.congr_fun_ae hae.symm

end Work.FTS.StrongEps.EpsZero.Bridge
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.pz_prod_integrable_of_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Almost everywhere strong measurability on `Ioi 0 ×ˢ Iθ` -/

/-- Continuity on the open quadrant gives a.e. strong measurability for the product of the
restrictions of Lebesgue measure to `Ioi 0 = (0,∞)` and to `Iθ = [0,π/2]`.  Indeed that product
measure is the restriction of the planar Lebesgue measure to `Ioi 0 ×ˢ Iθ`, which equals the
open quadrant up to a null set (the difference being contained in the two boundary lines
`θ = 0` and `θ = π/2`).  (The `z ∈ [0,∞)`-analogue is `Work.Spaces.aesm_of_continuousOn_Qd`.) -/
theorem aesm_prod_Ioi_of_continuousOn_Q0 {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable g ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Set.Ioi 0 ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθ
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    hg.aestronglyMeasurable hUm
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

/-! ## The elementary radial integral -/

/-- `z ↦ 1/(1+z)²` is integrable on `(0,∞)` (with value `1`); the antiderivative
`z ↦ -1/(1+z)` is nondecreasing and tends to `0` at `+∞`. -/
theorem integrableOn_one_div_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi 0) := by
  have hcont : ContinuousWithinAt (fun z : ℝ => -1 / (1 + z)) (Set.Ici 0) 0 := by
    refine (ContinuousAt.div continuousAt_const
      (continuousAt_const.add continuousAt_id) ?_).continuousWithinAt
    norm_num
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z : ℝ => -1 / (1 + z)) ((-1) * (-1 / (1 + x) ^ 2)) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h0 : (0 : ℝ) < 1 + x := by linarith
    have h1 : HasDerivAt (fun z : ℝ => (1 + z)⁻¹) (-1 / (1 + x) ^ 2) x :=
      ((hasDerivAt_id x).const_add (1 : ℝ)).inv (ne_of_gt h0)
    exact h1.const_mul (-1)
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ ((-1) * (-1 / (1 + x) ^ 2)) := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h0 : (0 : ℝ) < 1 + x := by linarith
    have heq : (-1) * (-1 / (1 + x) ^ 2) = 1 / (1 + x) ^ 2 := by ring
    rw [heq]; positivity
  have hlim : Tendsto (fun z : ℝ => -1 / (1 + z)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have hint : IntegrableOn (fun z : ℝ => (-1) * (-1 / (1 + z) ^ 2)) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim
  refine hint.congr (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- `(z/(1+z)²)² ≤ 1/(1+z)²` for `z > 0` (equivalently `z² ≤ (1+z)²`). -/
private theorem sq_div_one_add_sq_sq_le {z : ℝ} (hz : 0 < z) :
    (z / (1 + z) ^ 2) ^ 2 ≤ 1 / (1 + z) ^ 2 := by
  have h0 : 0 < 1 + z := by linarith
  rw [div_pow]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((1 + z) ^ 2) ^ 2)
    (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 + z), h0]

/-! ## The main lemma -/

theorem pz_prod_integrable_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 1 f) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  show Integrable (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
    (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict]
  -- the integrand is continuous on the open quadrant, hence a.e. strongly measurable
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact Work.Coercivity.K_facts_continuous.comp_continuousOn continuous_snd.continuousOn
    · exact (hsm.pz).continuousOn
  have hAESM := aesm_prod_Ioi_of_continuousOn_Q0 hcont
  have hK3 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.K θ| ≤ 3 := by
    intro θ hθ
    rw [abs_of_nonneg (Work.Coercivity.K_facts_nonneg θ hθ)]
    exact Work.Coercivity.K_facts_le_three θ hθ
  -- angular slices are integrable
  have hslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Integrable (fun θ => Work.Spaces.K θ * Work.Spaces.pz f z θ)
        (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hzpos : 0 < z := hz
    have habs := (Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hmem hzpos).2
    have hmeas : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have h1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pz f z θ)
          (volume.restrict Work.Spaces.Iθ) := by
        simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using
          hsm.aesm_slice_pzIter 1 hzpos
      exact (Work.Coercivity.K_facts_continuous.measurable.aestronglyMeasurable).mul h1
    refine Integrable.mono' (habs.const_mul 3) hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ hθ => hK3 θ hθ)] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
  -- the outer integral is integrable, by Cauchy–Schwarz against `ℋ¹`
  have houter : Integrable (fun z => ∫ θ, ‖Work.Spaces.K θ * Work.Spaces.pz f z θ‖
      ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict (Set.Ioi 0)) := by
    have hHk_int : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 1 f z θ) (volume.restrict (Set.Ioi 0)) :=
      hmem.2.mono_set Set.Ioi_subset_Ici_self
    have hAcont : ContinuousOn (fun z : ℝ => 3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2))
        (Set.Ioi 0) := by
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.div continuousOn_id ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro z hz
        have hz' : (0 : ℝ) < z := hz
        positivity
    have hA2 : Integrable (fun z : ℝ => (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)) ^ 2)
        (volume.restrict (Set.Ioi 0)) := by
      refine Integrable.mono' ((integrableOn_one_div_one_add_sq).const_mul (9 * (π / 2))) ?_ ?_
      · exact (hAcont.pow 2).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        have hzpos : 0 < z := hz
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hle := sq_div_one_add_sq_sq_le hzpos
        have h9 : (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)) ^ 2
            = 9 * (π / 2) * (z / (1 + z) ^ 2) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π / 2)]
          ring
        rw [h9]
        have hpi : (0 : ℝ) < π / 2 := by positivity
        nlinarith [hle, hpi]
    have hB2 : Integrable (fun z : ℝ => (Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 1 f z θ)) ^ 2) (volume.restrict (Set.Ioi 0)) := by
      refine hHk_int.congr (Filter.Eventually.of_forall fun z => ?_)
      exact (Real.sq_sqrt (MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 1 f z θ)).symm
    have hBaesm : AEStronglyMeasurable
        (fun z : ℝ => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
        (volume.restrict (Set.Ioi 0)) :=
      (Real.continuous_sqrt.measurable.comp_aemeasurable hHk_int.aemeasurable).aestronglyMeasurable
    have hAB : Integrable (fun z : ℝ => (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2))
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
        (volume.restrict (Set.Ioi 0)) := by
      have hmaj : Integrable (fun z : ℝ =>
          (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)) ^ 2 / 2
            + (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)) ^ 2 / 2)
          (volume.restrict (Set.Ioi 0)) :=
        (hA2.div_const 2).add (hB2.div_const 2)
      refine Integrable.mono' hmaj ?_ ?_
      · exact (hAcont.aestronglyMeasurable measurableSet_Ioi).mul hBaesm
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)|
            - |Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)|),
          sq_abs (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)),
          sq_abs (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))]
    have hAESM_int : AEStronglyMeasurable
        (fun z => ∫ θ, ‖Work.Spaces.K θ * Work.Spaces.pz f z θ‖ ∂(volume.restrict Work.Spaces.Iθ))
        (volume.restrict (Set.Ioi 0)) := by
      simpa only [Function.uncurry] using
        (hAESM.norm).integral_prod_right' (μ := volume.restrict (Set.Ioi 0))
          (ν := volume.restrict Work.Spaces.Iθ)
    refine Integrable.mono' hAB hAESM_int ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hzpos : 0 < z := hz
    have habs := (Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hmem hzpos).2
    rw [Real.norm_eq_abs,
      abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
    calc ∫ θ, ‖Work.Spaces.K θ * Work.Spaces.pz f z θ‖ ∂(volume.restrict Work.Spaces.Iθ)
        ≤ ∫ θ, 3 * |Work.Spaces.pz f z θ| ∂(volume.restrict Work.Spaces.Iθ) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => norm_nonneg _) (habs.const_mul 3) ?_
          filter_upwards [MeasureTheory.ae_restrict_of_forall_mem
            (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
            (fun θ hθ => hK3 θ hθ)] with θ hθ
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
      _ = 3 * ∫ θ, |Work.Spaces.pz f z θ| ∂(volume.restrict Work.Spaces.Iθ) :=
          MeasureTheory.integral_const_mul 3 _
      _ ≤ 3 * (Real.sqrt (π / 2) * (z / (1 + z) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)) :=
          mul_le_mul_of_nonneg_left
            (Work.FTS.PhiStar.Honesty.pz_abs_slice_le_sqrt_Hk hsm hmem hzpos) (by norm_num)
      _ = (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2))
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ) := by ring
  exact (MeasureTheory.integrable_prod_iff hAESM).mpr ⟨hslice, houter⟩

end Work.FTS.StrongEps.EpsZero
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.hkSqSwapOpenK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

theorem hkSqSwapOpenK (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α k f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ
        = Work.Spaces.HkSq α k f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α k f s σ)
          Work.Spaces.Iz) := by
  -- The integrand is a sum of squares, hence nonnegative.
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
  -- A.e. strong measurability of the uncurried integrand, from `C^∞` on the open quadrant.
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (hF.continuousOn_HkIntegrand α k)
  -- The angular slices are integrable, for every `z ∈ Iz` (hence almost every `z`).
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  -- ... and their `z`-integral is integrable.
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  refine ⟨?_, h2, h3⟩
  rw [Work.Spaces.HkSq]
  exact h1

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.lowGamSlotIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Continuity of the weight `Wt` on the open quadrant -/

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant
(the two endpoints `θ = 0`, `θ = π/2` are excluded there, so `sin(2θ) > 0`). -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The squared weighted mixed slice `(D_z^j D_θ^i f z · · W(α,z,·))²` is a.e. strongly
measurable on `Iθ`, for `z > 0`, as soon as `f` is `C^∞` on the *open* quadrant. -/
private lemma aesm_slice_mixed_Wt_sq {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  (Work.Spaces.aesm_slice_of_continuousOn_Qd _
    (((hsm.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) hz).pow 2

/-- On the open interval the squared weighted mixed slot is
`w² · (D_z^j D_θ^i f)² · sin(2θ)^{-γ}`. -/
private lemma wt_sq_mixed {α : ℝ} {f : ℝ → ℝ → ℝ} {j i : ℕ} {z θ : ℝ}
    (hs : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow,
    Work.FTS.GalBasis.cc.sq_rpow_neg_half (γ := Work.Spaces.gam α) hs]
  ring

/-- Almost every point of `Iθ` is an interior point of the interval. -/
private theorem ae_Ioo_of_restrict_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h := MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
    (b := Real.pi / 2)
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set h]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo

/-- Integrability of the `γ`-weighted mixed slot on the angular interval: for `0 < α ≤ 1`, a datum
`f` of the open class lying in `ℋ⁴`, a slot `(j,i)` with `1 ≤ i` and `i + j ≤ 4`, and `z > 0`, the
function `θ ↦ (D_z^j D_θ^i f z θ)² · sin(2θ)^{-γ(α)}` is integrable on `Iθ`.  The already proved
`Work.FTS.GalBasis.cc.Subcut.LNA.IntegrableOn_mixed_sq_sGamma` is the case `i = 1`, and its proof
generalises verbatim: dominate by `HkIntegrand α 4 f z ·` (integrable by `HkMem α 4 f` via the
summand bound `Work.Spaces.sq_le_HkIntegrand_mixed`) using the identity
`(D_z^j D_θ^i f·Wt α)² = (w z)²·(D_z^j D_θ^i f)²·sin(2θ)^{-γ}` and `(w z)² ≥ 1`; the a.e. strong
measurability comes from the joint continuity of the uncurried slot on the open quadrant
(`Work.Spaces.aesm_slice_of_continuousOn_Qd`). -/
theorem lowGamSlotIntegrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.mixed j i f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hw
  -- The weighted mixed slot is a summand of `HkIntegrand α 4 f z ·`, hence integrable.
  have hmix : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ :=
    (hmem.1 z hzI).mono' (aesm_slice_mixed_Wt_sq hF α j i hz)
      (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)
  -- Divide the weighted slot by `(w z)² ≠ 0`.
  refine (hmix.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  filter_upwards [ae_Ioo_of_restrict_Iθ] with θ hθ
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.GalBasis.cc.sin_two_pos hθ.1 hθ.2
  rw [wt_sq_mixed (α := α) hs, inv_mul_cancel_left₀ hw2]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDthAux.ZslotPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary identifications of iterated `D_θ` -/

/-- `D_θ^n (D_θ f) = D_θ^{n+1} f`. -/
theorem DthIter_Dth (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter n (Work.Spaces.Dth f) = Work.Spaces.DthIter (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ n (Work.Spaces.Dth f), ih]
      rfl

/-- `D_z^j (D_θ f) = D_z^jD_θ f` (definitional). -/
theorem DzIter_Dth_eq (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dth f) = Work.Spaces.mixed j 1 f := rfl

/-- `D_z^jD_θ^i (D_θ f) = D_z^jD_θ^{i+1} f`. -/
theorem mixed_Dth_shift (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f :=
  congrArg (fun g => Work.Spaces.DzIter j g) (DthIter_Dth i f)

/-! ## The `D_z`-slot bound -/

/-- **The pure `D_z`-slots.**  For `i ≤ 3` the `i`-th radial slot of the `ℋ³`-integrand of
`h·D_θ f` (weighted as in `HkIntegrand`) is dominated by `|h|²_𝒲 · HkIntegrand α 4 f`. -/
theorem zslot_le_pt : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i : ℕ, i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α h f hα hα1 hh hhm hf _hfm i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hhm
  have hHInn : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i h (Work.Spaces.Dth f) hh hf.Dth
    z θ hz hθ0 hθ1
  have hsplit : (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [DzIter_Dth_eq]
    ring
  rw [hsplit]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
      * (Work.Spaces.mixed (i - b) 1 f z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
          * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2
        ≤ 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
          * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDh : |Work.Spaces.DzIter b h z θ| ≤ 100 * Work.Spaces.WlInf α 4 h :=
      Work.FTS.OpenPkg.DzIter_le_WlInf_open hh hhm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b h z θ) ^ 2
        ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 := by
      have hB : (0 : ℝ) ≤ 100 * Work.Spaces.WlInf α 4 h := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDh).1
      have h2 := (abs_le.mp hDh).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 i b hbi (by omega)
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
          * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (100 * Work.Spaces.WlInf α 4 h) ^ 2
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2 := by
          refine mul_le_mul (mul_le_mul hch hx (sq_nonneg _) (by norm_num)) le_rfl
            (sq_nonneg _) (by positivity)
      _ = 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2 := by ring
  have hHvWt : Hv ^ 2 ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [hHv]; exact Work.Spaces.H_le_Wt α hα z θ hzI hθI
  have hsumsq : ∑ b ∈ Finset.range (i + 1), (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2
      ≤ ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 4 f z θ := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
          have hmix : (Work.Spaces.mixed (i - b) 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 (i - b) (by norm_num) (by omega)
          calc (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2
              = (Work.Spaces.mixed (i - b) 1 f z θ) ^ 2 * Hv ^ 2 := by ring
            _ ≤ (Work.Spaces.mixed (i - b) 1 f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
                mul_le_mul_of_nonneg_left hHvWt (sq_nonneg _)
            _ = (Work.Spaces.mixed (i - b) 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
            _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hmix
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) * ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
          * (((i : ℝ) + 1) * (((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsumsq (by positivity)
    _ ≤ 10 ^ 8 * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
        have hi16 : ((i : ℝ) + 1) ^ 2 ≤ 16 := by
          have hi3 : (i : ℝ) ≤ 3 := by exact_mod_cast hi
          nlinarith
        have h2nn : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 := sq_nonneg _
        have hkey : 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (((i : ℝ) + 1) * (((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ))
            = (2560000 * ((i : ℝ) + 1) ^ 2)
              * ((Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        have hkey2 : (10 : ℝ) ^ 8 * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ
            = 10 ^ 8 * ((Work.Spaces.WlInf α 4 h) ^ 2
                * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        rw [hkey, hkey2]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg h2nn hHInn)
        nlinarith [hi16]

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.L3MulDzBackup

open Work.Spaces (Dz DzIter)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The radial slots of the product `h·D_z f`, proved without any delegation. -/
theorem zslot_dz_le_b : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i : ℕ, i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (DzIter i (fun z θ => h z θ * Dz f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α h f _hα _hα1 hsmh hWm hsmf hfm i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hWm
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Dz f) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hsmf
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i h (Dz f) hsmh hDzsm z θ hz hθ0 hθ1
  have hsplit : (DzIter i (fun z θ => h z θ * Dz f z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * DzIter b h z θ)
            * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * DzIter b h z θ)
      * (DzIter (i - b) (Dz f) z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * DzIter b h z θ)
          * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2
        ≤ 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
          * (DzIter (i - b + 1) f z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDh : |DzIter b h z θ| ≤ 100 * Work.Spaces.WlInf α 4 h :=
      Work.FTS.OpenPkg.DzIter_le_WlInf_open hsmh hWm (by omega) hz hθ
    have hx : (DzIter b h z θ) ^ 2 ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 := by
      have hB : (0 : ℝ) ≤ 100 * Work.Spaces.WlInf α 4 h := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDh).1
      have h2 := (abs_le.mp hDh).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 i b hbi (by omega)
    have hshift : DzIter (i - b) (Dz f) = DzIter (i - b + 1) f := dzIter_Dz_eq (i - b) f
    calc (((i.choose b : ℝ) * DzIter b h z θ)
          * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (DzIter b h z θ) ^ 2
            * (DzIter (i - b) (Dz f) z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (100 * Work.Spaces.WlInf α 4 h) ^ 2
            * (DzIter (i - b) (Dz f) z θ * Hv) ^ 2 := by gcongr
      _ = 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (DzIter (i - b + 1) f z θ * Hv) ^ 2 := by rw [hshift]; ring
  have hsumsq : ∑ b ∈ Finset.range (i + 1), (DzIter (i - b + 1) f z θ * Hv) ^ 2
      ≤ 5 * Work.Spaces.HkIntegrand α 4 f z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (DzIter (i - b + 1) f z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 4 f z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ (i - b + 1) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 5 * Work.Spaces.HkIntegrand α 4 f z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 4 f z θ
          have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * DzIter b h z θ)
            * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * DzIter b h z θ)
              * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (DzIter (i - b + 1) f z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (DzIter (i - b + 1) f z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
          * (5 * (5 * Work.Spaces.HkIntegrand α 4 f z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 8 * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 4 f z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 := sq_nonneg _
        have hh : 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
              * (5 * (5 * Work.Spaces.HkIntegrand α 4 f z θ))
            = 64000000 * ((Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 8 * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ
            = 10 ^ 8 * ((Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.StrongPersist.L3Rhs.L3MulDzBackup
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

theorem HkIntegrandSepLeGen {α : ℝ} {k : ℕ} {C : ℝ → ℝ} {B : ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z' θ' => C θ' * B z') z θ
      ≤ ((C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + ∑ i ∈ Finset.range (k + 1),
              (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        * (∑ q ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter q (fun z' _ => B z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  -- ### Separation of variables for the pure `D_z`- and the mixed derivatives
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z' θ' => C θ' * B z') z θ
      = C θ * (Work.Spaces.OpZ^[i] B) z := by
    intro i
    have h := Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp i 0 C B z θ
    rw [Work.Spaces.mixed_zero_right] at h
    simpa using h
  have hMx : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z' θ' => C θ' * B z') z θ
      = (Work.Spaces.dthU^[i] C) θ * (Work.Spaces.OpZ^[j] B) z := by
    intro j i
    simpa using Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp j i C B z θ
  -- the radial factor of the right-hand side is `OpZ^[q] B z`, independently of `θ`
  have hDzB : ∀ q : ℕ, Work.Spaces.DzIter q (fun z' _ => B z') z 0
      = (Work.Spaces.OpZ^[q] B) z := by
    intro q
    rw [← congrFun (Work.Spaces.sliceZ_DzIter q (fun z' _ => B z') 0) z]
  -- ### Unfold the integrand
  rw [Work.Spaces.HkIntegrand]
  simp only [hDz, hMx, hDzB]
  -- ### The angular variable and the two weight identities
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Work.FTS.LocData.sin_two_nonneg hθ
  have hWt : Work.Spaces.Wt α z θ = Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hsdef]
  have hgamma : ∀ i : ℕ, 0 ≤ (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
      * s ^ (-(Work.Spaces.gam α)) else 0) := by
    intro i
    split_ifs with h
    · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    · exact le_refl 0
  have hbq : ∀ q : ℕ, 0 ≤ ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- ### The pure `D_z`-summands reproduce the first term of the right-hand side exactly
  have hP : (∑ i ∈ Finset.range (k + 1),
        (C θ * (Work.Spaces.OpZ^[i] B) z * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))) ^ 2)
      = C θ ^ 2 * s ^ (-(Work.Spaces.eta))
        * (∑ q ∈ Finset.range (k + 1),
            ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show C θ * (Work.Spaces.OpZ^[i] B) z * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))
        = (Work.Spaces.OpZ^[i] B) z * C θ * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))
        by ring,
      Work.FTS.LocData.sep_sq1 ((Work.Spaces.OpZ^[i] B) z) (C θ) (Work.Spaces.w z) s
        (Work.Spaces.eta) hs0]
    ring
  rw [hP]
  -- ### The mixed summands are dominated by the product of the two sums
  have hQ : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
            * Work.Spaces.Wt α z θ) ^ 2
          else 0))
      ≤ (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
        * (∑ q ∈ Finset.range (k + 1),
            ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    have hQ1 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * Work.Spaces.Wt α z θ) ^ 2
            else 0))
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                  * s ^ (-(Work.Spaces.gam α)) else 0)
                * (((Work.Spaces.OpZ^[j] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              else 0) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h.1, hWt]
        rw [show Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * (Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2)))
            = (Work.Spaces.OpZ^[j] B) z * (Work.Spaces.dthU^[i] C θ)
              * (Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2))) by ring,
          Work.FTS.LocData.sep_sq2 ((Work.Spaces.OpZ^[j] B) z) (Work.Spaces.dthU^[i] C θ)
            (Work.Spaces.w z) s (Work.Spaces.gam α) hs0]
        ring
      · rw [ite_eq_right h, ite_eq_right h]
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * Work.Spaces.Wt α z θ) ^ 2
            else 0))
        = _ := hQ1
      _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                * s ^ (-(Work.Spaces.gam α)) else 0)
              * (((Work.Spaces.OpZ^[j] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          by_cases h : 1 ≤ i ∧ i + j ≤ k
          · rw [ite_eq_left h]
          · rw [ite_eq_right h]
            exact mul_nonneg (hgamma i) (hbq j)
      _ = (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
              * s ^ (-(Work.Spaces.gam α)) else 0))
            * (∑ q ∈ Finset.range (k + 1),
                ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
  -- ### Assemble
  have hR : (C θ ^ 2 * s ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
      * (∑ q ∈ Finset.range (k + 1), ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = C θ ^ 2 * s ^ (-(Work.Spaces.eta))
          * (∑ q ∈ Finset.range (k + 1),
              ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
          * (∑ q ∈ Finset.range (k + 1),
              ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [add_mul]
  rw [hR]
  exact add_le_add (le_refl _) hQ

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimTower_identify3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

open scoped Real Topology

/-! ## `C³` from a continuous third-order partial tower on an open subset of `ℝ²`

`contDiffOn_two_of_partial_tower` (in `LimTower_c2`) upgrades a continuous partial-derivative
tower of order `2` to `C²`.  Here we need the order-`3` version: continuity of the tower entries
`D a b` for `a + b ≤ 3` together with the slice-derivative relations for `a + b ≤ 2` give
`C³` for the bottom entry `D 0 0`.

The proof is the two-step closure, exactly as for `contDiffOn_two_of_partial_tower`:
the shifted towers `D (1 + ·) ·` and `D · (1 + ·)` have continuous entries up to order `2` and
slice relations up to order `1`, so `contDiffOn_two_of_partial_tower` gives `C²` of `D 1 0` and
`D 0 1`; the Fréchet derivative of `D 0 0` is `p ↦ cop (D 1 0 p) (D 0 1 p)`
(`diffOn_uncurry_of_slices`), which is then `C²` by `contDiffOn_cop`, and
`contDiffOn_succ_of_fderiv_apply` closes. -/
theorem contDiffOn_three_of_partial_tower {φ : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hφ : ∀ z θ, φ z θ = D 0 0 z θ)
    (hcont : ∀ a b : ℕ, a + b ≤ 3 → ContinuousOn (fun p : ℝ × ℝ => D a b p.1 p.2) U)
    (hsz : ∀ a b : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun z' => D a b z' θ) (D (a + 1) b z θ) z)
    (hth : ∀ a b : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun θ' => D a b z θ') (D a (b + 1) z θ) θ) :
    ContDiffOn ℝ 3 (Function.uncurry φ) U := by
  -- the two shifted towers are `C²`
  have h2_10 : ContDiffOn ℝ 2 (Function.uncurry (D 1 0)) U :=
    contDiffOn_two_of_partial_tower hU (fun z θ => rfl)
      (fun a b hab => hcont (1 + a) b (by omega))
      (fun a b hab => hsz (1 + a) b (by omega))
      (fun a b hab => hth (1 + a) b (by omega))
  have h2_01 : ContDiffOn ℝ 2 (Function.uncurry (D 0 1)) U :=
    contDiffOn_two_of_partial_tower hU (fun z θ => rfl)
      (fun a b hab => hcont a (1 + b) (by omega))
      (fun a b hab => hsz a (1 + b) (by omega))
      (fun a b hab => hth a (1 + b) (by omega))
  have hcop : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => cop (D 1 0 p.1 p.2) (D 0 1 p.1 p.2)) U :=
    contDiffOn_cop h2_10 h2_01
  have hdiff := diffOn_uncurry_of_slices hU (hsz 0 0 (by norm_num)) (hth 0 0 (by norm_num))
    (hcont 1 0 (by norm_num)) (hcont 0 1 (by norm_num))
  have hstep : ContDiffOn ℝ (2 + 1) (Function.uncurry (D 0 0)) U := by
    refine contDiffOn_succ_of_fderiv_apply (n := 2) hdiff.1 (fun hω => absurd hω (by simp))
      (fun y => ?_)
    refine (hcop.clm_apply (contDiffOn_const (c := y))).congr fun x hx => ?_
    rw [hdiff.2 hx]
  have hφD : Function.uncurry φ = Function.uncurry (D 0 0) := by
    funext p; exact hφ p.1 p.2
  rw [hφD]
  exact hstep

theorem LimTower_identify3 {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hcont : ∀ (c d : ℕ), c + d ≤ 3 → ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hdz : ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) :
    ContDiffOn ℝ 3 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0 ∧
      ∀ (c d : ℕ), c + d ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        F c d z θ = Work.Spaces.mixed c d (F 0 0) z θ := by
  constructor
  · -- ## `C³` of `F 0 0`, in the coordinates `u = log z`, `v = log tan θ`
    -- the map `(u,v) ↦ (exp u, arctan (exp v))` lands in the open quadrant
    have hmemQ : ∀ p : ℝ × ℝ,
        (Real.exp p.1, Real.arctan (Real.exp p.2)) ∈ Work.FTS.EllipticEst.Q0 := by
      intro p
      refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos p.1, ?_, ?_⟩
      · rw [Real.arctan_pos]; exact Real.exp_pos p.2
      · exact Real.arctan_lt_pi_div_two _
    have hΦcont : Continuous fun p : ℝ × ℝ => (Real.exp p.1, Real.arctan (Real.exp p.2)) := by
      fun_prop
    -- continuity of every tower entry in the `(u,v)`-coordinates
    have hcontT : ∀ a b : ℕ, a + b ≤ 3 →
        ContinuousOn (fun p : ℝ × ℝ => T F a b p.1 p.2) Set.univ := by
      intro a b hab
      have h1 : ContinuousOn (fun p : ℝ × ℝ =>
          F a b (Real.exp p.1) (Real.arctan (Real.exp p.2))) Set.univ :=
        (hcont a b hab).comp hΦcont.continuousOn (fun p _ => hmemQ p)
      simpa only [T] using h1.div_const (2 ^ b)
    -- the `u`-derivative relation
    have hszT : ∀ a b : ℕ, a + b ≤ 2 → ∀ u v : ℝ,
        HasDerivAt (fun u' : ℝ => T F a b u' v) (T F (a + 1) b u v) u := by
      intro a b hab u v
      have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
      have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
      have hd := hdz a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
      have hcomp := hd.comp u (Real.hasDerivAt_exp u)
      have hval : F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) / Real.exp u
          * Real.exp u = F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) := by
        field_simp
      rw [hval] at hcomp
      have h2 := hcomp.div_const (2 ^ b)
      simpa only [T, Function.comp_apply] using h2
    -- the `v`-derivative relation
    have hthT : ∀ a b : ℕ, a + b ≤ 2 → ∀ u v : ℝ,
        HasDerivAt (fun v' : ℝ => T F a b u v') (T F a (b + 1) u v) v := by
      intro a b hab u v
      have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
      have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
      have hd := hdth a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
      have hcomp := hd.comp v (Work.FTS.StrongEps.LocUnif.hasDerivAt_arctan_exp v)
      have hsin : Real.sin (2 * Real.arctan (Real.exp v)) ≠ 0 := by
        rw [show Real.sin (2 * Real.arctan (Real.exp v))
              = 2 * Real.exp v / (1 + (Real.exp v) ^ 2) from by
            have hS : (0 : ℝ) < 1 + (Real.exp v) ^ 2 := by positivity
            rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
            rw [show (2 : ℝ) * (Real.exp v / √(1 + (Real.exp v) ^ 2))
                  * (1 / √(1 + (Real.exp v) ^ 2))
                = 2 * Real.exp v / (√(1 + (Real.exp v) ^ 2)) ^ 2 from by ring]
            rw [Real.sq_sqrt hS.le]]
        positivity
      have hval : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v))
            / Real.sin (2 * Real.arctan (Real.exp v))
            * (Real.sin (2 * Real.arctan (Real.exp v)) / 2)
          = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 := by
        field_simp
      rw [hval] at hcomp
      have h2 := hcomp.div_const (2 ^ b)
      have hval2 : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 / 2 ^ b
          = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ (b + 1) := by
        rw [pow_succ]; ring
      rw [hval2] at h2
      simpa only [T, Function.comp_apply] using h2
    -- the partial tower on `ℝ²` and the transfer back through the smooth coordinate change
    have h3 := contDiffOn_three_of_partial_tower (φ := fun u v => T F 0 0 u v) (D := T F)
      isOpen_univ (fun u v => rfl) hcontT
      (fun a b hab z θ _ => hszT a b hab z θ) (fun a b hab z θ _ => hthT a b hab z θ)
    have hcomp := h3.comp (Work.FTS.StrongEps.LocUnif.contDiffOn_logLog_Q0 3)
      (fun p _ => Set.mem_univ _)
    exact hcomp.congr fun p hp => comp_logLog_T00 F hp
  · -- ## Identification of the tower entries with the `mixed` derivatives of `F 0 0`
    -- first: `F 0 d = D_θ^d (F 0 0)`, by the `θ`-tower relations
    have step1 : ∀ d : ℕ, d ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        F 0 d z θ = Work.Spaces.DthIter d (F 0 0) z θ := by
      intro d
      induction d with
      | zero => intro _ z θ _; rfl
      | succ d ih =>
          intro hd z θ hzθ
          have hprev : d ≤ 3 := by omega
          have heq : ∀ θ' : ℝ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 →
              F 0 d z θ' = Work.Spaces.DthIter d (F 0 0) z θ' :=
            fun θ' hθ' => ih hprev z θ' hθ'
          have hderiv : deriv (fun θ' : ℝ => F 0 d z θ') θ
              = deriv (fun θ' : ℝ => Work.Spaces.DthIter d (F 0 0) z θ') θ := by
            refine Filter.EventuallyEq.deriv_eq ?_
            have hsl : {θ' : ℝ | (z, θ') ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 θ :=
              (Work.FTS.EllipticEst.isOpen_Q0.preimage
                (by fun_prop : Continuous fun θ' : ℝ => (z, θ'))).mem_nhds hzθ
            filter_upwards [hsl] with θ' hθ'
            exact heq θ' hθ'
          obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
          have hsin : Real.sin (2 * θ) ≠ 0 :=
            ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
          have hval := (hdth 0 d (by omega) z θ hzθ).deriv
          calc F 0 (d + 1) z θ
              = Real.sin (2 * θ) * (F 0 (d + 1) z θ / Real.sin (2 * θ)) := by field_simp
            _ = Real.sin (2 * θ) * deriv (fun θ' : ℝ => F 0 d z θ') θ := by rw [hval]
            _ = Real.sin (2 * θ) *
                  deriv (fun θ' : ℝ => Work.Spaces.DthIter d (F 0 0) z θ') θ := by rw [hderiv]
            _ = Work.Spaces.DthIter (d + 1) (F 0 0) z θ := rfl
    -- then: `F c d = D_z^c (D_θ^d (F 0 0))`, by the `z`-tower relations
    have step2 : ∀ d : ℕ, d ≤ 3 → ∀ c : ℕ, c + d ≤ 3 → ∀ z θ : ℝ,
        (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        F c d z θ = Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z θ := by
      intro d hd c
      induction c with
      | zero =>
          intro hcd z θ hzθ
          exact step1 d hd z θ hzθ
      | succ c ih =>
          intro hcd z θ hzθ
          have hprev : c + d ≤ 3 := by omega
          have heq : ∀ z' : ℝ, (z', θ) ∈ Work.FTS.EllipticEst.Q0 →
              F c d z' θ = Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ :=
            fun z' hz' => ih hprev z' θ hz'
          have hderiv : deriv (fun z' : ℝ => F c d z' θ) z
              = deriv (fun z' : ℝ =>
                  Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ) z := by
            refine Filter.EventuallyEq.deriv_eq ?_
            have hsl : {z' : ℝ | (z', θ) ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 z :=
              (Work.FTS.EllipticEst.isOpen_Q0.preimage
                (by fun_prop : Continuous fun z' : ℝ => (z', θ))).mem_nhds hzθ
            filter_upwards [hsl] with z' hz'
            exact heq z' hz'
          obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
          have hval := (hdz c d (by omega) z θ hzθ).deriv
          calc F (c + 1) d z θ
              = z * (F (c + 1) d z θ / z) := by field_simp
            _ = z * deriv (fun z' : ℝ => F c d z' θ) z := by rw [hval]
            _ = z * deriv (fun z' : ℝ =>
                  Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ) z := by rw [hderiv]
            _ = Work.Spaces.DzIter (c + 1) (Work.Spaces.DthIter d (F 0 0)) z θ := rfl
    intro c d hcd z θ hzθ
    have hd3 : d ≤ 3 := by omega
    exact step2 d hd3 c hcd z θ hzθ

end Work.FTS_EllLimOK
end
