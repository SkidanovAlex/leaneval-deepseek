import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.BslZsq
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotData
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.hkMemOfJConv
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.CexRop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.CexAlgebra

set_option autoImplicit false




end Work.FTS.EllSol.PkgK5.CexAlgebra
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.WallDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The trace-strengthened family interpolation** (the statement proved in the sibling module
`Submission/Work/FTS/EllSol/PkgK5/i0Family_le_openTrace.lean`): the `i = 0` family of the paper's
§7 mixed-derivative interpolation for data of the open quadrant whose radial slices vanish at the
two angular endpoints in the sense of *limits*. -/
abbrev InterpFam (k : ℕ) : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      α ^ 2 * (∑ r ∈ Finset.range (k + 1),
          ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        ≤ C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))

end Work.FTS.EllSol.PkgK5

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The wall** (`D_z∂_θ` with the four HkMem hypotheses and the endpoint traces): the
open-class form of the paper's §7 mixed interpolation at the level of `D_z∂_θ`, proved in
`Submission/Work/FTS/EllSol/PkgK5/wall_of_interp.lean` from `InterpFam`. -/
abbrev WallK5 (k : ℕ) : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pthIter 2 V)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) ∧
      α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (Work.Spaces.pth V))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
            + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V))

end Work.FTS.EllSol.PkgK5

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.residTracesK5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false

/-! ## The two smoothness facts for the layer `Ḡ(α,g)·sin 2θ` -/

/-- **`Ḡ(α,g)` is `C^∞` on `(0,∞)`** for a datum of the class `C` (`SmoothOpen g`, all-order
smoothness of the angular moment `F_*(g)` and `HkMem α 7 g`). -/
theorem gbar_contDiffOn_classC {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hfsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0))
    (hmem : Work.Spaces.HkMem α 7 g) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
  Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hfsm
    (Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hreg hmem)

/-- **The layer `-Ḡ(α,g)·sin 2θ` is `C^∞` on the open quadrant** for a datum of the class `C`. -/
theorem smoothOpen_negGbarSin_classC {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hfsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0))
    (hmem : Work.Spaces.HkMem α 7 g) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) :=
  Work.FTS.EllExist.sep_mul_open (g := fun z => -(Work.Elliptic.Gbar α g z))
    (χ := fun θ => Real.sin (2 * θ))
    (fun m => (gbar_contDiffOn_classC hα hreg hfsm hmem m).neg) (by fun_prop)

/-! ## A constant times `sin 2θ` at the two endpoints -/

/-- A `θ`-constant times `sin 2θ` tends to `0` at the two endpoints of `(0,π/2)`. -/
theorem tendsto_const_mul_sin_two_ends (c : ℝ) :
    Filter.Tendsto (fun θ : ℝ => c * Real.sin (2 * θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ : ℝ => c * Real.sin (2 * θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  have hleft : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := hcont.continuousAt (x := 0)
    have h' : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (0 : ℝ))
        (nhds (Real.sin (2 * 0))) := h
    rw [show Real.sin (2 * 0) = 0 by norm_num] at h'
    exact h'.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hright : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have h := hcont.continuousAt (x := Real.pi / 2)
    have h' : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (Real.pi / 2))
        (nhds (Real.sin (2 * (Real.pi / 2)))) := h
    rw [hsin] at h'
    exact h'.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
  exact ⟨by simpa using hleft.const_mul c, by simpa using hright.const_mul c⟩

/-! ## The target -/

theorem residTracesK5 (k : ℕ) :
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      ∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro α g Φg hα hα4 hC hsmo htraces j hj z hz
  -- the layer `-(Ḡ(α,g))·sin 2θ` is `C^∞` on the open quadrant
  have hCsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) :=
    smoothOpen_negGbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm hC.mem
  -- the functional identity `Ξ = Ψ̂ + (-Ḡ(α,g))·sin 2θ`
  have hfun : Work.Elliptic.EllResid α g Φg
      = fun z θ => Work.FTS.EllSol.ellShift α g Φg z θ
          + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ) := by
    funext z θ
    rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
    simp only [Work.FTS.EllSol.ellShift_apply]
    ring
  -- the pointwise decomposition of the radial iterates on the open quadrant
  have hdecomp : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ) := by
    intro z θ hz h1 h2
    rw [hfun]
    rw [Work.FTS.EllipticEst.SmoothOpen.DzIter_add hsmo hCsm j z θ hz h1 h2]
    rw [Work.FTS.EllipticEst.DzIter_mul_of_radial j (fun z => -(Work.Elliptic.Gbar α g z))
      (fun θ => Real.sin (2 * θ)) z θ]
  -- the two one-sided limits of the two summands
  obtain ⟨htl, htr⟩ := htraces j hj z hz
  obtain ⟨hcl, hcr⟩ := tendsto_const_mul_sin_two_ends
    (Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z)
  -- the two eventual equalities, on the two one-sided filters
  have hev0 : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
        + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
            * Real.sin (2 * θ)) := by
    change ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ hθmem
    exact hdecomp z θ hz hθmem hθ
  have hev1 : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
      =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
        + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
            * Real.sin (2 * θ)) := by
    change ∀ᶠ θ : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ hθmem
    exact hdecomp z θ hz hθ hθmem
  exact ⟨Filter.Tendsto.congr' hev0.symm (by simpa using htl.add hcl),
    Filter.Tendsto.congr' hev1.symm (by simpa using htr.add hcr)⟩

end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAuxC.identC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- On the open quadrant,
`∂_θ(Vop Ξ) = -(orthSource g + 6Ψ̂ + 6(-Ḡ·sin 2θ) + α²z²∂_z²Ψ̂ + α(5+α)(z∂_zΨ̂))`, where
`Ξ = PhiTil α g Φg` and `Ψ̂ = ellShift α g Φg`.  **No `α^{-1}` survives.** -/
theorem pth_Vop_PhiTil_eq (α : ℝ) (g Φg : ℝ → ℝ → ℝ)
    (hweak : Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
      (ellShift α g Φg))
    (hGBsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) z θ
      = -(Work.Elliptic.orthSource g z θ + 6 * ellShift α g Φg z θ
          + 6 * (-(Work.Elliptic.Gbar α g z) * Real.sin (2 * θ))
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (ellShift α g Φg) z θ)
          + (α * (5 + α)) * Work.Spaces.Dz (ellShift α g Φg) z θ) := by
  have hSmW : Work.FTS.EllipticEst.SmoothOpen (ellShift α g Φg) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hweak.smooth
  have hSmGBm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Elliptic.Gbar α g z) * Real.sin (2 * θ)) := by
    have h1 := Work.FTS.EllipticEst.SmoothOpen.const_mul' (-1) hGBsm
    refine Work.FTS.EllipticEst.SmoothOpen.congr h1 (fun z θ _ _ _ => ?_)
    ring
  have hdec : (fun z θ => ellShift α g Φg z θ
      + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ))
      = Work.Construction.PhiTil α g Φg := by
    rw [Work.FTS.EllipticEst.PhiTil_eq_EllResid]
    exact (vthC_EllResid_eq_ellShift α g Φg).symm
  have hSmΞ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Φg) :=
    Work.FTS.EllipticEst.SmoothOpen.congr (vthC_smoothOpen_add hSmW hSmGBm)
      (fun z θ _ _ _ => by rw [← hdec])
  have hcos : Real.cos θ ≠ 0 := by
    have h1 : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h1)
  have h1 : Work.Spaces.pth (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) z θ
      = -(Work.Elliptic.Lzero (Work.Construction.PhiTil α g Φg) z θ
          + 6 * Work.Construction.PhiTil α g Φg z θ) := by
    rw [Work.FTS.EllipticEst.Vop_eq α (Work.Construction.PhiTil α g Φg)]
    exact vthC_pth_Vop_eq hSmΞ hz hθ
  have h2 : Work.Elliptic.Lzero (Work.Construction.PhiTil α g Φg) z θ
      = Work.Elliptic.Lzero (ellShift α g Φg) z θ := by
    rw [← hdec, vthC_Lzero_add hSmW hSmGBm hz hθ,
      Work.Elliptic.Lzero_sin_two_mul (fun z => -(Work.Elliptic.Gbar α g z)) z θ hcos,
      add_zero]
  have h3 : Work.Elliptic.Lzero (ellShift α g Φg) z θ
      = Work.Elliptic.orthSource g z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (ellShift α g Φg) z θ)
        + (α * (5 + α)) * Work.Spaces.Dz (ellShift α g Φg) z θ := by
    have hb := Work.FTS.EllipticEst.TT.EllWeakPos.eq hweak z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at hb
    simp only [Work.Spaces.Dz]
    linarith [hb]
  rw [h1, h2, h3, ← hdec]
  ring

end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.Step =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

open Work.FTS.EllipticEst.TT

/-- **The induction step of `prop:Hk`.**  `TT.ESW.StepPieces.EllEstUnif_step_of_pieces` with all
of its inputs supplied by proved declarations. -/
theorem step : ∀ k : ℕ, 3 ≤ k →
    (∃ C : ℝ, 0 < C ∧ EllWeak0 C) →
    (∃ C : ℝ, 0 < C ∧ EllEstUnif (k - 1) C) →
    ∃ C : ℝ, 0 < C ∧ EllEstUnif k C :=
  Work.FTS.EllipticEst.TT.ESW.Pieces.EllEstUnif_step_of_pieces
    (hstep := fun {k} hk α f hcd hmem =>
      Work.FTS.EllipticEst.remov.HkSq_step_le hk α f hcd hmem)
    (hshift := fun {k} hk α f hcd hmem =>
      Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le hk α f hcd hmem)
    (hpos := fun {α} {k} hk {F} {Ψ} h =>
      Work.FTS.EllipticEst.TT.ESW.Shift.EllWeakPos_DzIter_one_shift_of_two_le
        (α := α) (k := k) hk h)
    (hcore := fun D hD k hk =>
      Work.FTS.EllipticEst.remov.EllEstUnif_top_core_of_halves D hD
        (fun k hk => Work.FTS.EllipticEst.remov.A_top_slot_bound D hD k hk)
        (fun k hk => bSlotTop D hD k hk) k hk)
    (hsmF := fun {α} {k} {F} {Ψ} h n =>
      (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1 n)
    (hsmA := fun {α} {k} {F} {Ψ} h n =>
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).2.2.1 n)
    (hsmB := fun {α} {k} {F} {Ψ} h n =>
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).2.2.2 n)
    (hAz := fun {α} {k} {F} {Ψ} h =>
      (Work.FTS.EllipticEst.remov.Dz_slice_identities Ψ h.smoothOpen).1)
    (hBz := fun {α} {k} {F} {Ψ} h =>
      (Work.FTS.EllipticEst.remov.Dz_slice_identities Ψ h.smoothOpen).2)

end Work.FTS.EllipticEst.Prop
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.MeasAlt.EpsLDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The `ofReal` / `lintegral` bridge -/

/-- **The real integral is at most the `lintegral` of its `ofReal`** (nonnegative integrand).  No
measurability is needed: either the function is integrable — and then the `ofReal`/`lintegral`
bridge is an equality — or the Bochner integral is `0` by junk value. -/
theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hf)]
  · rw [integral_undef h, ENNReal.ofReal_zero]
    exact bot_le



/-! ## The `ℝ≥0∞`-valued size `EpsL` -/





end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.EpsMem_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThetaFromEpsLeafA/EpsMem_strip` — the strip truncations of an `EpsMem` profile are `EpsMem`

`EpsMem α f` is the *honesty* predicate of the weighted space `X` of the `ε`-scheme: the weighted
square `(f · epsW α)²` is integrable on the quarter plane `Iz ×ˢ Iθ` (so that `EpsSq α f` is an
honest integral rather than Lean's junk value `0`).

The two angular truncations

    stripLo φ g = (z,θ) ↦ if θ ≤ φ then g z θ else 0 ,
    stripHi φ g = (z,θ) ↦ if π/2 - φ ≤ θ then g z θ else 0

of a profile are *dominated* by the profile itself, so they inherit `EpsMem`.  The point is that
their weighted squares are the indicators of the (measurable) sets `{θ ≤ φ}` resp.
`{π/2 - φ ≤ θ}` times `(g · epsW α)²`:

    (stripLo φ g · epsW α)² = 1_{θ ≤ φ} · (g · epsW α)² ,
    (stripHi φ g · epsW α)² = 1_{π/2 - φ ≤ θ} · (g · epsW α)² .

Integrability of a measurable indicator times an integrable function is
`MeasureTheory.integrable_indicator_iff`.  All of `φ` is allowed (for `φ ≤ 0` the lower strip is
a.e. empty on `Iθ`), and no continuity of `g` is needed.
-/

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

open MeasureTheory Set

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Multiplying an `if`-whose-`else`-branch-is-`0` by anything and squaring truncates the square. -/
private theorem ite_zero_mul_sq (c : Prop) [Decidable c] (a b : ℝ) :
    ((if c then a else (0 : ℝ)) * b) ^ 2 = if c then (a * b) ^ 2 else 0 := by
  by_cases h : c <;> simp [h]

/-- **Domination by an indicator.**  If the weighted square of `h` is the indicator (of a
measurable set `S`) of the weighted square of `g`, and `g ∈ X`, then `h ∈ X`.

This is the abstract form of both halves of `EpsMem_strip`: the truncated weighted square is the
indicator of the corresponding angular half-plane times the untruncated one, and the indicator may
be moved inside the integral. -/
private theorem epsMem_of_indicator {α : ℝ} {g h : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.StrongEps.EpsMem α g) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hfun : (fun p : ℝ × ℝ => (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      = S.indicator (fun p : ℝ × ℝ =>
          (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)) :
    Work.FTS.StrongEps.EpsMem α h := by
  have hs : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hInt : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hg
  rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hfun]
  refine (MeasureTheory.integrable_indicator_iff hs).mp ?_
  have hEq : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (S.indicator (fun p : ℝ × ℝ =>
          (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
      = (S ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)).indicator
        (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) := by
    funext p
    by_cases hp : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
    · rw [Set.indicator_of_mem hp]
      by_cases hq : p ∈ S
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (Set.mem_inter hq hp)]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq h.1)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h => hp h.2)]
  rw [hEq]
  exact (MeasureTheory.integrable_indicator_iff (hS.inter hs)).mpr
    (hInt.mono_set Set.inter_subset_right)

theorem EpsMem_strip {α : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.StrongEps.EpsMem α g) (φ : ℝ) :
    Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g) ∧
    Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g) := by
  constructor
  · refine epsMem_of_indicator hg (S := {p : ℝ × ℝ | p.2 ≤ φ})
      (measurableSet_le measurable_snd measurable_const) ?_
    funext p
    have hstrip : Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g p.1 p.2
        = if p.2 ≤ φ then g p.1 p.2 else 0 := rfl
    rw [hstrip, ite_zero_mul_sq]
    by_cases hp : p.2 ≤ φ
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 ≤ φ} from hp), if_pos hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 ≤ φ} from hp), if_neg hp]
  · refine epsMem_of_indicator hg (S := {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2})
      (measurableSet_le measurable_const measurable_snd) ?_
    funext p
    have hstrip : Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g p.1 p.2
        = if Real.pi / 2 - φ ≤ p.2 then g p.1 p.2 else 0 := rfl
    rw [hstrip, ite_zero_mul_sq]
    by_cases hp : Real.pi / 2 - φ ≤ p.2
    · rw [Set.indicator_of_mem
        (show p ∈ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} from hp), if_pos hp]
    · rw [Set.indicator_of_notMem
        (show p ∉ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} from hp), if_neg hp]

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.ContDiffOn_E2_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **`E₂ α f` is `C³` on the open quadrant in the *open* class.**

`E₂ α f = Ê₂ f + Γ(θ)·radS α f z` splits into a clean defect `Ê₂ f`, whose `C³`-regularity on
the open quadrant only needs `SmoothOpen f` (`E2hat_mem_contDiff_O`), and a product of the
angular factor `Γ α` (`C^∞` on `(0,π/2)`) with the radial profile `radS α f`, which is `C³` on
`(0,∞)` as soon as `L₁₂ f ∈ C⁴` there (`radS_contDiffOn_three` + `contDiffOn_four_L12f`, the
open-class replacement of `L12_contDiffOn_four_of_five`). -/
theorem ContDiffOn_E2_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.Transfer.E2 α f))
      Work.Construction.Qd := by
  -- the class data
  have hO : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  -- `L₁₂ f` is `C⁴` on `(0,∞)`, hence `radS α f` is `C³` there
  have hA : ContDiffOn ℝ 4 (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0) :=
    E2O.contDiffOn_four_L12f α hα hα1 hO hmem5
  have hradS : ContDiffOn ℝ 3 (fun z => Work.FTS.CoercivityFix.Transfer.radS α f z)
      (Set.Ioi 0) :=
    Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three α hα hα1 hA
  -- the clean defect `Ê₂ f` is `C³` on the open quadrant
  have hmem3 : Work.Spaces.HkMem α 3 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 3 (by norm_num) hmem5
  have hmemd3 : Work.Spaces.HkMem α 3 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 3) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem5)
  have hE2hat : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.E2hat f))
      Work.Construction.Qd :=
    (E2O.E2hat_mem_contDiff_O α hα (by norm_num : 3 ≤ 4) hO hmem3 hmemd3).2
  -- the separated summand `Γ(θ)·radS α f z`
  have hGam : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.Construction.Qd :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_Gam_Qd α 3
  have hR : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Transfer.radS α f p.1) Work.Construction.Qd :=
    hradS.comp contDiffOn_fst (fun p hp => hp.1)
  have hsum : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2
      + Work.Spaces.Gam α p.2 * Work.FTS.CoercivityFix.Transfer.radS α f p.1)
      Work.Construction.Qd := hE2hat.add (hGam.mul hR)
  refine hsum.congr ?_
  intro p hp
  simp only [Function.uncurry, Work.FTS.CoercivityFix.Transfer.E2]

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false

/-! ## The domain measure -/

/-- The product measure `dz dθ` on the domain `Iz × Iθ = [0,∞) × [0,π/2]` of the self-similar
variables. -/
def DomM : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The planar Lebesgue measure restricted to `s ×ˢ t` is the product of the two restrictions. -/
theorem prodRestrict_eq2 (s t : Set ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (s ×ˢ t)
      = (MeasureTheory.volume.restrict s).prod (MeasureTheory.volume.restrict t) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]

/-- `DomM` is the planar Lebesgue measure restricted to the closed quadrant. -/
theorem DomM_eq : DomM
    = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  (prodRestrict_eq2 Work.Spaces.Iz Work.Spaces.Iθ).symm

/-- `DomM` is dominated by the planar Lebesgue measure. -/
theorem DomM_le_volume : DomM ≤ (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) := by
  rw [DomM_eq]; exact MeasureTheory.Measure.restrict_le_self

instance : MeasureTheory.SFinite DomM := by
  rw [DomM_eq]; infer_instance

/-! ## The `ℝ≥0∞`-valued weighted size `epsL2` -/

/-- The weighted `L²`-size of a profile, as an `ℝ≥0∞`-valued integral over the domain: the honest
(no junk) form of `EpsSq`. -/
def epsL2 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ,
    ENNReal.ofReal ((f p.1 p.2 * epsW α p.1 p.2) ^ 2) ∂DomM

/-- Almost-everywhere strong measurability of the weighted profile on the domain. -/
def AK2 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : Prop :=
  MeasureTheory.AEStronglyMeasurable
    (fun p : ℝ × ℝ => f p.1 p.2 * epsW α p.1 p.2) DomM

/-! ## `EpsMem` and `epsL2` on the product measure -/

/-- `EpsMem` is integrability of the squared weighted profile for the product measure `DomM`. -/
theorem EpsMem_iff_integrable2 {α : ℝ} {f : Work.FTS.Galerkin.Fn} :
    EpsMem α f ↔ MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM := by
  rw [EpsMem, MeasureTheory.IntegrableOn, DomM_eq]

/-! ## Measurability of the weight and the elementary `AK2` calculus -/

/-- The weight `epsW α` is a measurable function of the two variables. -/
theorem measurable_epsW (α : ℝ) :
    Measurable (fun p : ℝ × ℝ => epsW α p.1 p.2) := by
  simp only [epsW, Work.Spaces.w]
  fun_prop


/-- `AK2` is preserved by addition. -/
theorem AK2_add {α : ℝ} {f g : Work.FTS.Galerkin.Fn} (hf : AK2 α f) (hg : AK2 α g) :
    AK2 α (fun z θ => f z θ + g z θ) := by
  unfold AK2 at hf hg ⊢
  refine MeasureTheory.AEStronglyMeasurable.congr (hf.add hg) ?_
  filter_upwards with p
  simp only [Pi.add_apply]
  ring

/-- `AK2` is preserved by negation. -/
theorem AK2_neg {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : AK2 α f) :
    AK2 α (fun z θ => -f z θ) := by
  unfold AK2 at hf ⊢
  refine hf.neg.congr ?_
  filter_upwards with p
  simp only [Pi.neg_apply]
  ring

/-- `AK2` only depends on the a.e.-class of the profile. -/
theorem AK2_congr_ae {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (h : ∀ᵐ p ∂DomM, f p.1 p.2 = g p.1 p.2) (hg : AK2 α g) : AK2 α f := by
  unfold AK2 at hg ⊢
  refine MeasureTheory.AEStronglyMeasurable.congr hg ?_
  filter_upwards [h] with p hp
  rw [hp]

/-- `AK2` is preserved by subtraction. -/
theorem AK2_sub {α : ℝ} {f g : Work.FTS.Galerkin.Fn} (hf : AK2 α f) (hg : AK2 α g) :
    AK2 α (fun z θ => f z θ - g z θ) :=
  AK2_congr_ae (by filter_upwards with p; ring) (AK2_add hf (AK2_neg hg))



/-! ## A.e.-congruence of the sizes -/

/-- `EpsMem` only depends on the a.e.-class of the profile. -/
theorem EpsMem_congr_ae {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (h : ∀ᵐ p ∂DomM, f p.1 p.2 = g p.1 p.2) (hf : EpsMem α f) : EpsMem α g := by
  rw [EpsMem_iff_integrable2] at hf ⊢
  refine hf.congr ?_
  filter_upwards [h] with p hp
  rw [hp]

/-- `EpsSq` only depends on the a.e.-class of the profile. -/
theorem EpsSq_congr_ae {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (h : ∀ᵐ p ∂DomM, f p.1 p.2 = g p.1 p.2) : EpsSq α f = EpsSq α g := by
  have h' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), f z θ = g z θ :=
    Measure.ae_ae_of_ae_prod h
  rw [EpsSq, EpsSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h'] with z hz
  exact MeasureTheory.integral_congr_ae (hz.mono fun θ hθ => by simp only [hθ])

/-! ## The a.e. open quadrant -/

/-- Almost every point of the domain lies in the open quadrant. -/
theorem ae_open_DomM :
    ∀ᵐ p ∂DomM, 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 := by
  have hz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have h : Work.Spaces.Iz = Set.Ici (0 : ℝ) := rfl
    rw [h, ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0))]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hz)
  have hθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 < θ ∧ θ < Real.pi / 2 := by
    have h : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
    rw [h, ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0)
        (b := Real.pi / 2))]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ⟨hz.1, hz.2⟩)
  rw [DomM]
  rw [Measure.ae_prod_iff_ae_ae
    (p := fun p : ℝ × ℝ => 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2)
    ((measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)))]
  filter_upwards [hz] with z hz'
  filter_upwards [hθ] with θ hθ'
  exact ⟨hz', hθ'.1, hθ'.2⟩

/-- A property which holds everywhere on the open quadrant holds almost everywhere on the
domain. -/
theorem ae_of_forall_open {Q : ℝ → ℝ → Prop}
    (h : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → Q z θ) :
    ∀ᵐ p ∂DomM, Q p.1 p.2 := by
  filter_upwards [ae_open_DomM] with p hp
  exact h p.1 hp.1 p.2 hp.2.1 hp.2.2

/-! ## The conversion kit between `epsL2` and `EpsSq`/`EpsMem` -/

/-- The squared weighted profile of a profile is integrable for `DomM` as soon as its `epsL2`
is finite and the weighted profile is a.e. strongly measurable. -/
theorem EpsMem_of_epsL2_lt_top {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hAK : AK2 α f)
    (h : epsL2 α f < ⊤) : EpsMem α f := by
  rw [EpsMem_iff_integrable2]
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM := hAK.pow 2
  refine ⟨haesm, ?_⟩
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun p => sq_nonneg _)).mpr h

/-- `epsL2` is finite for a member of the weighted space. -/
theorem epsL2_lt_top_of_EpsMem {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f) :
    epsL2 α f < ⊤ := by
  have hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM :=
    EpsMem_iff_integrable2.mp hf
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun p => sq_nonneg _)).mp hg.hasFiniteIntegral

/-- For a member of the weighted space, `epsL2` is the (real) `EpsSq`. -/
theorem epsL2_eq_ofReal_EpsSq {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f) :
    epsL2 α f = ENNReal.ofReal (EpsSq α f) := by
  have hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM :=
    EpsMem_iff_integrable2.mp hf
  have hprod : (∫ p : ℝ × ℝ, (f p.1 p.2 * epsW α p.1 p.2) ^ 2 ∂DomM) = EpsSq α f := by
    rw [EpsSq, DomM]
    exact MeasureTheory.integral_prod _ hg
  have h1 : (∫ p : ℝ × ℝ, (f p.1 p.2 * epsW α p.1 p.2) ^ 2 ∂DomM)
      = (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal ((f p.1 p.2 * epsW α p.1 p.2) ^ 2) ∂DomM).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => sq_nonneg _) hg.aestronglyMeasurable
  have hfin : (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal ((f p.1 p.2 * epsW α p.1 p.2) ^ 2) ∂DomM) ≠ ⊤ :=
    (epsL2_lt_top_of_EpsMem hf).ne
  unfold epsL2
  rw [← hprod, h1, ENNReal.ofReal_toReal hfin]

/-- The `epsL2`-bound of a member of the weighted space. -/
theorem epsL2_le_ofReal_of_mem {α B : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f)
    (h : EpsSq α f ≤ B) : epsL2 α f ≤ ENNReal.ofReal B := by
  rw [epsL2_eq_ofReal_EpsSq hf]
  exact ENNReal.ofReal_le_ofReal h

/-- The passage back: a finite `epsL2`-bound (on an a.e. measurable profile) gives membership and
the `EpsSq`-bound. -/
theorem EpsMem_and_EpsSq_le_of_epsL2_le {α B : ℝ} (hB : 0 ≤ B)
    {f : Work.FTS.Galerkin.Fn} (hAK : AK2 α f) (h : epsL2 α f ≤ ENNReal.ofReal B) :
    EpsMem α f ∧ EpsSq α f ≤ B := by
  have hfin : epsL2 α f < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hmem := EpsMem_of_epsL2_lt_top hAK hfin
  refine ⟨hmem, ?_⟩
  rw [epsL2_eq_ofReal_EpsSq hmem] at h
  rwa [ENNReal.ofReal_le_ofReal_iff hB] at h


/-- A finite `epsL2`-bound of a *member* of the weighted space gives the `EpsSq`-bound. -/
theorem EpsSq_le_of_epsL2_le_of_mem {α B : ℝ} (hB : 0 ≤ B) {f : Work.FTS.Galerkin.Fn}
    (hf : EpsMem α f) (h : epsL2 α f ≤ ENNReal.ofReal B) : EpsSq α f ≤ B := by
  rw [epsL2_eq_ofReal_EpsSq hf] at h
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h

/-! ## Elementary calculus of the two sizes -/

/-- The zero profile is a member of the weighted space. -/
theorem EpsMem_zero2 (α : ℝ) : EpsMem α (fun _ _ => (0 : ℝ)) := by
  rw [EpsMem_iff_integrable2]
  simp

/-- Negation preserves membership. -/
theorem EpsMem_neg2 {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hf : EpsMem α f) :
    EpsMem α (fun z θ => -f z θ) := by
  rw [EpsMem_iff_integrable2] at hf ⊢
  refine hf.congr ?_
  filter_upwards with p
  ring

/-- `EpsSq` is invariant under negation. -/
theorem EpsSq_neg2 {α : ℝ} {f : Work.FTS.Galerkin.Fn} :
    EpsSq α (fun z θ => -f z θ) = EpsSq α f := by
  rw [EpsSq, EpsSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with θ
  ring

/-- `EpsSq` is invariant under swapping a difference. -/
theorem EpsSq_sub_comm {α : ℝ} {f g : Work.FTS.Galerkin.Fn} :
    EpsSq α (fun z θ => f z θ - g z θ) = EpsSq α (fun z θ => g z θ - f z θ) := by
  rw [EpsSq, EpsSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with θ
  ring

/-- Membership of a difference from membership (and a.e. strong measurability) of the two parts. -/
theorem EpsMem_sub2 {α : ℝ} {f g : Work.FTS.Galerkin.Fn} (hakf : AK2 α f) (hakg : AK2 α g)
    (hf : EpsMem α f) (hg : EpsMem α g) : EpsMem α (fun z θ => f z θ - g z θ) := by
  have hf' := EpsMem_iff_integrable2.mp hf
  have hg' := EpsMem_iff_integrable2.mp hg
  rw [EpsMem_iff_integrable2]
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ((f p.1 p.2 - g p.1 p.2) * epsW α p.1 p.2) ^ 2) DomM :=
    (AK2_sub hakf hakg).pow 2
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => 2 * (f p.1 p.2 * epsW α p.1 p.2) ^ 2
        + 2 * (g p.1 p.2 * epsW α p.1 p.2) ^ 2) DomM :=
    (hf'.const_mul 2).add (hg'.const_mul 2)
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 : ((f p.1 p.2 - g p.1 p.2) * epsW α p.1 p.2) ^ 2
      = (f p.1 p.2 * epsW α p.1 p.2 - g p.1 p.2 * epsW α p.1 p.2) ^ 2 := by ring
  rw [h1]
  nlinarith [sq_nonneg (f p.1 p.2 * epsW α p.1 p.2),
    sq_nonneg (g p.1 p.2 * epsW α p.1 p.2),
    sq_nonneg (f p.1 p.2 * epsW α p.1 p.2 - g p.1 p.2 * epsW α p.1 p.2),
    sq_nonneg (f p.1 p.2 * epsW α p.1 p.2 + g p.1 p.2 * epsW α p.1 p.2)]

/-! ## Joint measurability of a family and its sections -/



/-- Joint measurability of the weighted fake-time integral of a family. -/
theorem AK2_intervalIntegral {α : ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    {G : ℝ → Work.FTS.Galerkin.Fn}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM)) :
    AK2 α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ) := by
  rw [Set.uIoc_of_le hτ] at hmeas
  unfold AK2
  simp only [intervalIntegral.integral_of_le hτ]
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ × ℝ => ∫ y : ℝ, G y x.1 x.2 * epsW α x.1 x.2
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 τ))) DomM :=
    hmeas.prod_swap.integral_prod_right'
  refine h2.congr ?_
  filter_upwards with p
  rw [MeasureTheory.integral_mul_const]

end Work.FTS.StrongEps.EpsLocalPStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two spellings of the weight

`epsW α z θ = w z / sin(2θ)^{γ/2}` (`EpsSpace.lean`) and `Wt α z θ = w z · sin(2θ)^{-γ/2}`
(`Spaces.Defs`, `Weights.lean`) are the same function on the angular interval `[0,π/2]`, where
`sin(2θ) ≥ 0`. -/

theorem epsW_eq_Wt_of_mem_Iθ {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    epsW α z θ = Work.Spaces.Wt α z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [epsW, Work.Spaces.Wt, Work.Spaces.wTheta, div_eq_mul_inv,
    Real.rpow_neg hs (Work.Spaces.gam α / 2)]

/-- The integrand of `EpsSq` vanishes when the angular weight vanishes: `z = 0` or `θ = 0` or
`θ = π/2`. -/
theorem epsW_eq_zero_of_not_mem_quad {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) (h : ¬(0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) :
    epsW α z θ = 0 := by
  rw [Work.Spaces.Iz] at hz
  rw [Work.Spaces.Iθ] at hθ
  have hgam : (Work.Spaces.gam α / 2 : ℝ) ≠ 0 := by
    have : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    linarith
  rcases not_and_or.mp h with hz0 | hθbad
  · have hz' : z = 0 := le_antisymm (not_lt.mp hz0) hz
    subst hz'
    simp [epsW, Work.Spaces.w]
  · have hθbad' : θ ≤ 0 ∨ π / 2 ≤ θ := by
      rcases not_and_or.mp hθbad with hh | hh
      · exact Or.inl (not_lt.mp hh)
      · exact Or.inr (not_lt.mp hh)
    have hsin : Real.sin (2 * θ) = 0 := by
      rcases hθbad' with hh | hh
      · have h' : θ = 0 := le_antisymm hh hθ.1
        subst h'
        simp
      · have h' : θ = π / 2 := le_antisymm hθ.2 hh
        subst h'
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    rw [epsW, hsin]
    simp [Real.zero_rpow hgam]


theorem Wt_nonneg_Icc {α z θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    0 ≤ Work.Spaces.Wt α z θ := by
  rw [Work.Spaces.Wt]
  refine mul_nonneg ?_ ?_
  · rw [Work.Spaces.w]; positivity
  · rw [Work.Spaces.wTheta]
    exact Real.rpow_nonneg (sin_two_nonneg hθ) _

/-! ## The `z`- and `θ`-shifts in the log coordinates -/

theorem zShift_exp' (s p : ℝ) : zShift (Real.exp s) p = Real.exp (s - p) := by
  rw [zShift, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]

theorem thShift_arctan_exp' (ζ p : ℝ) :
    thShift (Real.arctan (Real.exp ζ)) p = Real.arctan (Real.exp (ζ - p)) := by
  rw [thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]

end Work.FTS.StrongEps.EpsSqTools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSrc

/-- **`EpsSq` is the iterated `lintegral` of its (nonnegative) integrand.**

`EpsSq α f = ∫_z ∫_θ (f z θ · epsW α z θ)²` is an iterated *Bochner* set integral; the
hypothesis `EpsMem α f` is the joint integrability of the same integrand on the product set
`Iz ×ˢ Iθ`.  The bridge is the two Fubini/Tonelli theorems for set integrals:
`setIntegral_prod` identifies the iterated Bochner integral with the Bochner integral over
`Iz ×ˢ Iθ`, `ofReal_integral_eq_lintegral_ofReal` turns that into the `lintegral` of the
nonnegative integrand, and `setLIntegral_prod` (Tonelli) re-iterates it. -/
theorem ofReal_EpsSq_eq_lintegral {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : EpsMem α f) :
    ENNReal.ofReal (EpsSq α f)
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((f z θ * epsW α z θ) ^ 2) := by
  -- The integrand, as a function on the product.
  have hInt : IntegrableOn (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hf
  -- Step 1: Fubini for set integrals; the product measure on `ℝ × ℝ` is `volume.prod volume`
  -- definitionally.
  have hEpsSq : EpsSq α f
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          (f p.1 p.2 * epsW α p.1 p.2) ^ 2 := by
    rw [EpsSq]
    exact (MeasureTheory.setIntegral_prod _ hInt).symm
  rw [hEpsSq]
  -- Step 2: the Bochner integral of a nonnegative function is the `lintegral` of its `ofReal`.
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun p => sq_nonneg _)]
  -- Step 3: Tonelli for set integrals, iterating the `lintegral`.
  exact MeasureTheory.setLIntegral_prod _
    (ENNReal.measurable_ofReal.comp_aemeasurable hInt.aestronglyMeasurable.aemeasurable)

end Work.FTS.StrongEps.EpsSrc
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.SlotLow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotLow`: the two zeroth-order slot estimates for the base case `base_R`

The two `L²`-pairings of the clean operator `𝓛̂ = 𝓛 − Transport` against `h` itself,

  `wip ρ_η (𝓛̂h) h`  and  `wip w² (𝓛̂h) h`   (`ρ_β = w²·sin(2θ)^{-β}`, `w² = ρ_0`),

are bounded below by `-5·|h|²_{ℋ¹}`, for `h` smooth on the open quadrant with an honest
`ℋ¹`-integral.

The proof has three ingredients, none of which needs the smoothness of `h` beyond what is
already in `HkMem`:

* **pointwise AM–GM.**  `Lhat h z θ = h + D_z h − 2h/(1+z) − 3 D_θh/(1+z)`, and on `z ≥ 0`
  (`1/(1+z) ≤ 1`) the elementary `2|ab| ≤ a² + b²` gives

    `Lhat h · h · ρ ≥ -((1/2)(D_zh)² + (3/2)(D_θh)² + 3h²)·ρ`  for every `ρ ≥ 0`;

* **slot domination.**  The bracket is at most `5·HkIntegrand α 1 h` a.e. in `θ`: each of
  `h²`, `(D_zh)²` with the weight `ρ_η`, resp. `(D_θh)²` with the weight `ρ_γ = w²·Wt²`
  (dominated by `ρ_η` since `η ≤ γ = 1 + α/10` for `α ≥ 0`) is a *single summand* of
  `HkIntegrand α 1 h`, while `w² ≤ ρ_η` because `sin(2θ)^{-η} ≥ 1` on `(0,π/2)`;

* **the exact integral comparison.**  If `f + g ≥ 0` a.e. and `g ≥ 0` is integrable then
  `∫f ≥ -∫g` *without* any integrability or measurability assumption on `f` (a
  non-integrable `f` has Bochner integral `0`).  Applied to the angular slice (with
  `g = 5·HkIntegrand`) and then to the radial variable (with `g = 5·∫_θ HkIntegrand` — the
  integrability there is exactly the second clause of `HkMem α 1 h`), this converts the
  pointwise bound into the two stated inequalities.  In particular no joint integrability
  of `𝓛̂h·h·ρ` is needed.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The general integral comparison -/

/-- **Integral lower bound from a two-sided-signed pointwise bound.**  If `f + g ≥ 0` a.e. and
`g ≥ 0` is integrable, then `∫ f ≥ -∫ g`.  Nothing is assumed about `f`: if `f` is not
integrable its Bochner integral is `0 ≥ -∫g`, and otherwise `∫(f+g) = ∫f + ∫g ≥ 0`. -/
private theorem neg_integral_le_integral {β : Type*} [MeasurableSpace β]
    {μ : MeasureTheory.Measure β} {f g : β → ℝ} (hg : MeasureTheory.Integrable g μ)
    (hgnn : ∀ᵐ a ∂μ, 0 ≤ g a) (hfg : ∀ᵐ a ∂μ, 0 ≤ f a + g a) :
    -(∫ a, g a ∂μ) ≤ ∫ a, f a ∂μ := by
  by_cases hf : MeasureTheory.Integrable f μ
  · have h0 : 0 ≤ ∫ a, f a + g a ∂μ := MeasureTheory.integral_nonneg_of_ae hfg
    rw [MeasureTheory.integral_add hf hg] at h0
    linarith
  · rw [MeasureTheory.integral_undef hf]
    have h0 : 0 ≤ ∫ a, g a ∂μ := MeasureTheory.integral_nonneg_of_ae hgnn
    linarith

/-! ## The pointwise AM–GM bound -/

/-- **The pointwise AM–GM lower bound for `𝓛̂`.**  For `z ≥ 0` and `ρ ≥ 0`,

`𝓛̂h · h · ρ ≥ -((1/2)(D_zh)² + (3/2)(D_θh)² + 3h²)·ρ`.

The decomposition of the sum `𝓛̂h·h + (1/2)(D_zh)² + (3/2)(D_θh)² + 3h²` into the three
nonnegative pieces `(1/2)(h + D_zh)²`, `(3/2)(D_θh − h/(1+z))²` and
`(1/2)(1 − 1/(1+z))(3/(1+z) + 7)h²` is what makes this exact. -/
private theorem lhat_amgm {h : Fn} {z θ ρ : ℝ} (hz : 0 ≤ z) (hρ : 0 ≤ ρ) :
    -((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
        + 3 * (h z θ) ^ 2) * ρ
      ≤ Work.FTS.CoercivityFix.Lhat h z θ * h z θ * ρ := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hL : Work.FTS.CoercivityFix.Lhat h z θ
      = h z θ + Work.Spaces.Dz h z θ - 2 * ((1 + z)⁻¹ * h z θ)
        - 3 * ((1 + z)⁻¹ * Work.Spaces.Dth h z θ) := by
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    field_simp
  have hZ0 : 0 ≤ (1 + z)⁻¹ := by positivity
  have hZ1 : (1 + z)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ h1z]; linarith
  have hkey : Work.FTS.CoercivityFix.Lhat h z θ * h z θ
        + ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
            + 3 * (h z θ) ^ 2)
      = (1 / 2) * (h z θ + Work.Spaces.Dz h z θ) ^ 2
        + (3 / 2) * (Work.Spaces.Dth h z θ - (1 + z)⁻¹ * h z θ) ^ 2
        + (1 / 2) * (1 - (1 + z)⁻¹) * (3 * (1 + z)⁻¹ + 7) * (h z θ) ^ 2 := by
    rw [hL]; ring
  have hT : 0 ≤ Work.FTS.CoercivityFix.Lhat h z θ * h z θ
        + ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
            + 3 * (h z θ) ^ 2) := by
    rw [hkey]
    have h1 : 0 ≤ (1 / 2) * (h z θ + Work.Spaces.Dz h z θ) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h2 : 0 ≤ (3 / 2) * (Work.Spaces.Dth h z θ - (1 + z)⁻¹ * h z θ) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h3 : 0 ≤ (1 / 2) * (1 - (1 + z)⁻¹) * (3 * (1 + z)⁻¹ + 7) * (h z θ) ^ 2 := by
      have hA : 0 ≤ 1 - (1 + z)⁻¹ := by linarith
      have hB : 0 ≤ 3 * (1 + z)⁻¹ + 7 := by linarith
      have hC : 0 ≤ (1 / 2 : ℝ) * (1 - (1 + z)⁻¹) * (3 * (1 + z)⁻¹ + 7) :=
        mul_nonneg (mul_nonneg (by norm_num) hA) hB
      exact mul_nonneg hC (sq_nonneg _)
    linarith
  have hTρ : 0 ≤ (Work.FTS.CoercivityFix.Lhat h z θ * h z θ
        + ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
            + 3 * (h z θ) ^ 2)) * ρ := mul_nonneg hT hρ
  nlinarith [hTρ]

/-! ## The angular weights -/

/-- `η ≤ γ = gam α` for `α ≥ 0`. -/
private theorem eta_le_gam (α : ℝ) (hα : 0 ≤ α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have := Work.Spaces.eta_lt_one
  linarith

/-- `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` on `Iθ`, for `α ≥ 0`. -/
private theorem sig_eta_le_sig_gam (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
      ≤ Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; linarith
  rcases eq_or_lt_of_le (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [Work.FTS.CoercivityFix.Coer1.sig, Work.FTS.CoercivityFix.Coer1.sig, ← h,
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≠ 0),
      Real.zero_rpow (neg_ne_zero.mpr hgam)]
  · have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    rw [Work.FTS.CoercivityFix.Coer1.sig, Work.FTS.CoercivityFix.Coer1.sig]
    exact Real.rpow_le_rpow_of_exponent_ge h hs1 (by linarith [eta_le_gam α hα])

/-- `(W α)² = w²·sin(2θ)^{-γ}` on `Iθ`, for `α ≥ 0`. -/
private theorem Wt_sq_self_Iθ (α : ℝ) (hα : 0 ≤ α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ := by
  have hγ : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; linarith
  have hγ2 : -(Work.Spaces.gam α / 2) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hγ' : -(Work.Spaces.gam α) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hfun : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hfun]
  rcases eq_or_lt_of_le (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [Work.FTS.CoercivityFix.Coer1.sig, ← h, Real.zero_rpow hγ2, Real.zero_rpow hγ']
    ring
  · rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig]
    rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by
      rw [sq, ← Real.rpow_add h]
      congr 1
      ring]

/-! ## The three `ℋ¹`-slots with the `η`-weight -/

/-- The `h²`-slot. -/
private theorem slot_eta_h (α : ℝ) {h : Fn} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (h z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α 1 h z θ := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have he : (h z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      = (h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig_div_sq_Iθ Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) z θ hIθ, Work.FTS.CoercivityFix.Coer1.Rho]
  rw [he]
  exact Work.Spaces.sq_le_HkIntegrand_z α 1 h z θ 0 (by norm_num)

/-- The `D_zh`-slot. -/
private theorem slot_eta_dz (α : ℝ) {h : Fn} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Dz h z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α 1 h z θ := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have he : (Work.Spaces.Dz h z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      = (Work.Spaces.Dz h z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig_div_sq_Iθ Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) z θ hIθ, Work.FTS.CoercivityFix.Coer1.Rho]
  rw [he]
  exact Work.Spaces.sq_le_HkIntegrand_z α 1 h z θ 1 (by norm_num)

/-- The `D_θh`-slot: the `γ`-weight of `ℋ¹` dominates the `η`-weight. -/
private theorem slot_eta_dth (α : ℝ) (hα : 0 ≤ α) {h : Fn} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Dth h z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α 1 h z θ := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsig := sig_eta_le_sig_gam α hα hIθ
  have hstep : (Work.Spaces.Dth h z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ (Work.Spaces.Dth h z θ) ^ 2
        * (Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ) := by
    rw [Work.FTS.CoercivityFix.Coer1.Rho]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsig (sq_nonneg _)) (sq_nonneg _)
  have he : (Work.Spaces.Dth h z θ) ^ 2
        * (Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ)
      = (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [mul_pow, Wt_sq_self_Iθ α hα z θ hIθ]
    rfl
  rw [he] at hstep
  exact le_trans hstep
    (Work.Spaces.sq_le_HkIntegrand_mixed α 1 h z θ 1 0 (by norm_num) (by norm_num))

/-- **Slot domination, `η`-weight.** -/
private theorem slot_dom_eta (α : ℝ) (hα : 0 ≤ α) {h : Fn} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
        + 3 * (h z θ) ^ 2) * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ 5 * Work.Spaces.HkIntegrand α 1 h z θ := by
  nlinarith [slot_eta_h (α := α) (h := h) (z := z) (θ := θ) hθ,
    slot_eta_dz (α := α) (h := h) (z := z) (θ := θ) hθ,
    slot_eta_dth α hα (h := h) (z := z) (θ := θ) hθ,
    Work.Spaces.HkIntegrand_nonneg α 1 h z θ]

/-- **Slot domination, plain radial weight `w²`** (which is `Rhoq 0`). -/
private theorem slot_dom_w (α : ℝ) (hα : 0 ≤ α) {h : Fn} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
        + 3 * (h z θ) ^ 2) * (Work.Spaces.w z) ^ 2
      ≤ 5 * Work.Spaces.HkIntegrand α 1 h z θ := by
  have hone := Work.FTS.CoercivityFix.Coer1.one_le_sig_eta hθ
  have hρ : (Work.Spaces.w z) ^ 2 ≤ Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ := by
    rw [Work.FTS.CoercivityFix.Coer1.Rho]
    simpa using mul_le_mul_of_nonneg_left hone (sq_nonneg (Work.Spaces.w z))
  have h1 : (h z θ) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 h z θ :=
    le_trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))
      (slot_eta_h (α := α) (h := h) (z := z) (θ := θ) hθ)
  have h2 : (Work.Spaces.Dz h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 h z θ :=
    le_trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))
      (slot_eta_dz (α := α) (h := h) (z := z) (θ := θ) hθ)
  have h3 : (Work.Spaces.Dth h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 h z θ :=
    le_trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))
      (slot_eta_dth α hα (h := h) (z := z) (θ := θ) hθ)
  nlinarith [h1, h2, h3, Work.Spaces.HkIntegrand_nonneg α 1 h z θ]

/-! ## The general weighted form, and the target -/

/-- **The weighted form of `SlotLow`.**  For an `ℋ¹`-function `h` and any weight `ρ ≥ 0`
on `Iθ` such that the pointwise bracket is dominated by `5·HkIntegrand α 1 h` a.e.,
`wip ρ (𝓛̂h) h ≥ -5·|h|²_{ℋ¹}`. -/
private theorem slot_low_wip (α : ℝ) {h : Fn} (hm : Work.Spaces.HkMem α 1 h)
    {ρ : Fn} (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hG : ∀ z, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
        + 3 * (h z θ) ^ 2) * ρ z θ ≤ 5 * Work.Spaces.HkIntegrand α 1 h z θ) :
    -(5 : ℝ) * Work.Spaces.HkSq α 1 h
      ≤ Work.Coercivity.wip ρ (Work.FTS.CoercivityFix.Lhat h) h := by
  -- the angular estimate, for every fixed `z ∈ I_z`
  have hθlv : ∀ z ∈ Work.Spaces.Iz,
      -(5 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 h z θ))
        ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.CoercivityFix.Lhat h z θ * h z θ * ρ z θ := by
    intro z hz
    have hgnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ 5 * Work.Spaces.HkIntegrand α 1 h z θ :=
      Filter.Eventually.of_forall fun θ => by
        have := Work.Spaces.HkIntegrand_nonneg α 1 h z θ
        linarith
    have hsum : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ Work.FTS.CoercivityFix.Lhat h z θ * h z θ * ρ z θ
          + 5 * Work.Spaces.HkIntegrand α 1 h z θ := by
      filter_upwards [hG z, MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => hρnn z θ hθ)] with θ hGθ hρθ
      have ham := lhat_amgm (h := h) (z := z) (θ := θ) (ρ := ρ z θ) hz hρθ
      linarith
    have h := neg_integral_le_integral ((hm.1 z hz).const_mul 5) hgnn hsum
    rw [MeasureTheory.integral_const_mul] at h
    linarith
  -- the radial estimate
  have hz_lv : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      0 ≤ (∫ θ in Work.Spaces.Iθ, Work.FTS.CoercivityFix.Lhat h z θ * h z θ * ρ z θ)
        + 5 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 h z θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => by
      have := hθlv z hz
      linarith
  have hgnn₂ : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      0 ≤ 5 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 h z θ) :=
    Filter.Eventually.of_forall fun z => by
      have : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 h z θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 1 h z θ)
      linarith
  have h := neg_integral_le_integral (hm.2.const_mul 5) hgnn₂ hz_lv
  rw [MeasureTheory.integral_const_mul] at h
  simp only [Work.Spaces.HkSq, Work.Coercivity.wip]
  linarith [h]

/-- `Rhoq 0` is the plain radial weight `w²`. -/
private theorem rhoq_zero : Rhoq 0 = fun z θ => (Work.Spaces.w z) ^ 2 := by
  funext z θ
  simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho,
    Work.FTS.CoercivityFix.Coer1.sig, neg_zero, Real.rpow_zero, mul_one]

/-- **`SlotLow`.**  The two zeroth-order pairings of the clean operator `𝓛̂` against `h` are
bounded below by `-5` times the square of the `ℋ¹`-norm of `h`. -/
theorem SlotLow (α : ℝ) (hα : 0 ≤ α) {h : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α 1 h) :
    -(5 : ℝ) * Work.Spaces.HkSq α 1 h
        ≤ Work.Coercivity.wip (Work.FTS.StrongPersist.H6Aux.R.Rhoq Work.Spaces.eta)
            (Work.FTS.CoercivityFix.Lhat h) h
      ∧ -(5 : ℝ) * Work.Spaces.HkSq α 1 h
        ≤ Work.Coercivity.wip (Work.FTS.StrongPersist.H6Aux.R.Rhoq 0)
            (Work.FTS.CoercivityFix.Lhat h) h := by
  refine ⟨?_, ?_⟩
  · exact slot_low_wip α hm (ρ := Work.FTS.StrongPersist.H6Aux.R.Rhoq Work.Spaces.eta)
      (fun z θ hθ => Work.FTS.CoercivityFix.Coer1.Rho_nonneg _ z θ hθ)
      (fun z => Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo.mono
        (fun θ hθ => slot_dom_eta α hα (h := h) (z := z) (θ := θ) hθ))
  · rw [rhoq_zero]
    exact slot_low_wip α hm (ρ := fun z θ => (Work.Spaces.w z) ^ 2)
      (fun z θ _ => sq_nonneg _)
      (fun z => Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo.mono
        (fun θ hθ => slot_dom_w α hα (h := h) (z := z) (θ := θ) hθ))

end Work.FTS.StrongPersist.H6Aux.R
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksDat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

theorem ksDat : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInfMem α 6 (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInf α 6 (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ≤ C * α ∧
    Work.Spaces.WlInfMem α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInf α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) ≤ C * α ∧
    (∀ (A : Work.FTS.Galerkin.Fn),
        (A = (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ∨
         A = (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z)) →
        ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ C * α * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := ksWlInf
  obtain ⟨C2, hC2pos, hC2⟩ := ksTorWlInf
  obtain ⟨C3, hC3pos, hC3⟩ := ksMixed
  refine ⟨max (max C1 C2) C3, ?_, ?_⟩
  · exact lt_of_lt_of_le hC1pos (le_trans (le_max_left C1 C2) (le_max_left (max C1 C2) C3))
  · intro α hαI
    obtain ⟨hα, hα1⟩ := hαI
    -- identify `FK (Fstar α)` with its explicit value `α·2z/(1+z)²`
    have hKF : (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z)
        = (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) := by
      funext z θ
      exact Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1
    have hKFt : (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z)
        = (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2))) := by
      funext z θ
      rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    rw [hKF, hKFt]
    obtain ⟨hA1mem, hA1le⟩ := hC1 α ⟨hα, hα1⟩
    obtain ⟨hA2mem, hA2le⟩ := hC2 α ⟨hα, hα1⟩
    have hA3 := hC3 α ⟨hα, hα1⟩
    have hαnn : 0 ≤ α := le_of_lt hα
    have hC1max : C1 ≤ max (max C1 C2) C3 :=
      le_trans (le_max_left C1 C2) (le_max_left (max C1 C2) C3)
    have hC2max : C2 ≤ max (max C1 C2) C3 :=
      le_trans (le_max_right C1 C2) (le_max_left (max C1 C2) C3)
    have hC3max : C3 ≤ max (max C1 C2) C3 := le_max_right (max C1 C2) C3
    refine ⟨?_, ?_, hA1mem, ?_, hA2mem, ?_, ?_⟩
    · exact SmoothOpen_KsFun α
    · exact SmoothOpen_KsTor α
    · calc Work.Spaces.WlInf α 6 (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2))
          ≤ C1 * α := hA1le
        _ ≤ max (max C1 C2) C3 * α := mul_le_mul_of_nonneg_right hC1max hαnn
    · calc Work.Spaces.WlInf α 6
            (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2)))
          ≤ C2 * α := hA2le
        _ ≤ max (max C1 C2) C3 * α := mul_le_mul_of_nonneg_right hC2max hαnn
    · intro A hA j i hji z θ hz hθ1 hθ2
      have hbound := hA3 A hA j i hji z θ hz hθ1 hθ2
      have hΦnn : 0 ≤ (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
          else 1) := by
        by_cases hi : 1 ≤ i
        · rw [if_pos hi]
          have hs : 0 ≤ Real.sin (2 * θ) :=
            Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ1]) (by linarith [hθ2, Real.pi_pos])
          exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)
        · rw [if_neg hi]
          norm_num
      have hznn : 0 ≤ z / (1 + z) := div_nonneg (le_of_lt hz) (by linarith)
      have hfacnn : 0 ≤ α * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) :=
        mul_nonneg (mul_nonneg hαnn hznn) hΦnn
      calc |Work.Spaces.mixed j i A z θ|
          ≤ C3 * α * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) :=
            hbound
        _ = C3 * (α * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) := by
            ring
        _ ≤ max (max C1 C2) C3 * (α * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) :=
            mul_le_mul_of_nonneg_right hC3max hfacnn
        _ = max (max C1 C2) C3 * α * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
            ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.AngSlot6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The angular slot bound at order `l`, on the closed domain, from the flat data.**

For a datum `f` which is `C^∞` on the open quadrant and vanishes off it, the flat bounds
`FlatW l f K` extend to the weighted angular slots of `Work.Spaces.WlInf α l`:

`|(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α + sin 2θ)| ≤ C·K`   (`1 ≤ j`, `k + j ≤ l`),

on the whole closed rectangle `[0,∞) × [0,π/2]`, with `C` a universal constant (depending on
`l` only).

The three regions:

* **the open quadrant**: the Leibniz expansion of `D_θ = sin(2·)∂_θ`,
  `D_θ^j f = Σ_{a<j} C(j-1,a) (D_θ^a sin 2·) (D_θ^{j-1-a} ∂_θ f)`, whose `z`-derivative form is
  `Work.FTS.PhiStar.pzIter_DthIter_leibniz`.  The coefficient iterates of `sin 2·` carry a
  factor `sin(2θ)` (`sfun_Lop_iter_le`), while `(z+1)^k ∂_z^k D_θ^{j-1-a}(∂_θf)` is one of the
  quantities bounded by `K` in `FlatW`'s second clause.  The surviving `sin(2θ)` is exactly what
  `sin_rpow_slack` consumes: `sin(2θ)·sin(2θ)^{-α/5}/(α + sin 2θ) ≤ 2`.
* **the angular endpoints** `θ = 0, π/2`: the weight vanishes (`0^{-α/5} = 0`).
* **the origin** `z = 0`: the whole `z`-slice vanishes (here `zeroOff` is used), so every
  iterated `z`-derivative of it at `0` is `0`. -/
theorem angSlot_le_flatW_general (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ), 0 < α → α ≤ 1 → 0 ≤ K →
        (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
        Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW l f K →
        ∀ (j k : ℕ), 1 ≤ j → k + j ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * K := by
  obtain ⟨A, hApos, hAb⟩ := Work.FTS.PhiStar.CoreAux.AngSlot.sfun_Lop_iter_le l
  have hCpos : (0 : ℝ) < (2 : ℝ) ^ (l + 1) * A := mul_pos (by positivity) hApos
  refine ⟨(2 : ℝ) ^ (l + 1) * A, hCpos, ?_⟩
  intro α f K hα0 hα1 hK hzero hf hF j k hj hjk z hz θ hθ
  have hsin_nn : 0 ≤ Real.sin (2 * θ) := Work.FTS.PhiStar.sin_two_nonneg_Iθ hθ
  have hCnn : (0 : ℝ) ≤ (2 : ℝ) ^ (l + 1) * A := hCpos.le
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | hz0eq
  · by_cases hθI : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · -- the open quadrant: the Leibniz expansion plus the flat bound
      have hsin_pos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθI.1]) (by linarith [hθI.2, Real.pi_pos])
      have hden_nn : 0 ≤ α + Real.sin (2 * θ) := by linarith
      have hleib := Work.FTS.PhiStar.pzIter_DthIter_leibniz (f := f) (k := k) hf hj hzpos hθI
      have hmain : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
          ≤ (A * (2 : ℝ) ^ l) * K * Real.sin (2 * θ) := by
        have hsum : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            ≤ (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A) * K * Real.sin (2 * θ) := by
          rw [hleib, Finset.mul_sum]
          calc |∑ a ∈ Finset.range j, (z + 1) ^ k * (((j - 1).choose a : ℝ) *
                  (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                      (Work.Spaces.pth f)) z θ))|
              = |∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  ((z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                      (Work.Spaces.pth f)) z θ))| := by
                congr 1
                exact Finset.sum_congr rfl fun a _ => by ring
            _ ≤ ∑ a ∈ Finset.range j, |((j - 1).choose a : ℝ) *
                  ((z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                      (Work.Spaces.pth f)) z θ))| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  |(z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                      (Work.Spaces.pth f)) z θ)| := by
                exact Finset.sum_congr rfl fun a _ => by
                  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            _ ≤ ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * (A * Real.sin (2 * θ) * K) := by
                refine Finset.sum_le_sum fun a ha => ?_
                refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
                have haj : a ≤ j - 1 := by rw [Finset.mem_range] at ha; omega
                have hAterm : |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ|
                    ≤ A * Real.sin (2 * θ) := by
                  have h2 : Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ
                      = (Work.Spaces.Lop^[a]) (fun θ' => Real.sin (2 * θ')) θ := by
                    have hfun : (fun θ' => Work.FTS.H2.Sfun z θ')
                        = (fun θ' => Real.sin (2 * θ')) := by funext θ'; rfl
                    rw [Work.Spaces.DthIter_eq_iterate_Lop a Work.FTS.H2.Sfun z, hfun]
                  rw [h2]
                  exact hAb a (by omega) θ hθ
                have hKterm : |(z + 1) ^ k * Work.Spaces.pzIter k
                      (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ| ≤ K :=
                  (hF z θ hzpos hθI.1 hθI.2).2 k (j - 1 - a) (by omega)
                calc |(z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                      Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                        (Work.Spaces.pth f)) z θ)|
                    = |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| *
                        |(z + 1) ^ k * Work.Spaces.pzIter k
                          (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ| := by
                      rw [show (z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                            Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                              (Work.Spaces.pth f)) z θ)
                          = Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                            ((z + 1) ^ k * Work.Spaces.pzIter k
                              (Work.Spaces.DthIter (j - 1 - a)
                                (Work.Spaces.pth f)) z θ) from by ring, abs_mul]
                  _ ≤ (A * Real.sin (2 * θ)) * K :=
                      mul_le_mul hAterm hKterm (abs_nonneg _)
                        (mul_nonneg hApos.le hsin_nn)
                  _ = A * Real.sin (2 * θ) * K := by ring
            _ = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A) * (K * Real.sin (2 * θ)) := by
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun a _ => by ring
            _ = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A) * K
                  * Real.sin (2 * θ) := by ring
        have hjsum : (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A)
            ≤ A * (2 : ℝ) ^ l := by
          have hchoose : (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ))
              = (2 : ℝ) ^ (j - 1) := by
            have hrange : Finset.range j = Finset.range ((j - 1) + 1) := by congr 1; omega
            rw [hrange]
            exact_mod_cast Nat.sum_range_choose (n := j - 1)
          calc (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A)
              = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ)) * A := (Finset.sum_mul ..).symm
            _ = (2 : ℝ) ^ (j - 1) * A := by rw [hchoose]
            _ ≤ (2 : ℝ) ^ l * A := by
                refine mul_le_mul_of_nonneg_right ?_ hApos.le
                exact pow_le_pow_right₀ (by norm_num) (by omega)
            _ = A * (2 : ℝ) ^ l := by ring
        calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
              ≤ (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * A) * K
                * Real.sin (2 * θ) := hsum
          _ ≤ (A * (2 : ℝ) ^ l) * K * Real.sin (2 * θ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjsum hK) hsin_nn
      -- multiply by the angular weight
      have hrpow : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(α / 5))
          = (Real.sin (2 * θ)) ^ (1 - α / 5) := by
        have h : (1 : ℝ) - α / 5 = 1 + -(α / 5) := by ring
        rw [h, Real.rpow_add hsin_pos, Real.rpow_one]
      have hw_nn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
        div_nonneg (Real.rpow_nonneg hsin_nn _) hden_nn
      calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
            rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsin_nn _),
              abs_of_nonneg hden_nn]
            ring
        _ ≤ ((A * (2 : ℝ) ^ l) * K * Real.sin (2 * θ))
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right hmain hw_nn
        _ = (A * (2 : ℝ) ^ l) * K * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(α / 5))
              / (α + Real.sin (2 * θ))) := by ring
        _ = (A * (2 : ℝ) ^ l) * K * ((Real.sin (2 * θ)) ^ (1 - α / 5)
              / (α + Real.sin (2 * θ))) := by rw [hrpow]
        _ ≤ (A * (2 : ℝ) ^ l) * K * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Work.FTS.PhiStar.sin_rpow_slack hα0 hα1 hsin_nn (Real.sin_le_one _)
        _ ≤ ((2 : ℝ) ^ (l + 1) * A) * K := by
            have h : (A * (2 : ℝ) ^ l) * K * 2 = ((2 : ℝ) ^ (l + 1) * A) * K := by
              rw [pow_succ]; ring
            exact le_of_eq h
    · -- `θ = 0` or `θ = π / 2`: the angular weight vanishes
      rw [Work.Spaces.Iθ] at hθ
      have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases eq_or_lt_of_le hθ.1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (le_antisymm hθ.2 (not_lt.mp fun hlt => hθI ⟨h, hlt⟩))
      have hsin0 : Real.sin (2 * θ) = 0 := by
        rcases hcases with h | h
        · rw [h]; norm_num
        · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hrpow : (Real.sin (2 * θ)) ^ (-(α / 5)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (by linarith : -(α / 5) ≠ 0)
      rw [hrpow, mul_zero, zero_div, abs_zero]
      exact mul_nonneg hCnn hK
  · -- `z = 0`: the whole `z`-slice `z' ↦ D_θ^j f z' θ` vanishes on `(-∞,0]`
    have hz0 : z = 0 := hz0eq.symm
    subst hz0
    have hsd : Work.Spaces.pzIter k (Work.Spaces.DthIter j f) 0 θ = 0 := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv]
      refine Work.FTS.PhiStar.iteratedDeriv_eq_zero_of_eqOn_Iic
        (g := fun z' => Work.Spaces.DthIter j f z' θ) ?_ k 0 le_rfl
      intro z' hz'
      exact Work.FTS.PhiStar.DthIter_eq_zero_of_slice_zero (u := f) (z := z')
        (fun θ' => hzero z' θ' (by
          intro hmem
          have h1 : (0 : ℝ) < z' := (Work.FTS.EllipticEst.mem_Q0.mp hmem).1
          linarith)) j θ
    rw [hsd]
    simp only [mul_zero, zero_mul, zero_div, abs_zero]
    exact mul_nonneg hCnn hK

theorem AngSlot6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
    0 < α → α ≤ 1 → 0 ≤ K →
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
    ∀ (j k : ℕ), 1 ≤ j → k + j ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * K := by
  obtain ⟨C, hC, h⟩ := angSlot_le_flatW_general 6
  exact ⟨C, hC, fun α f K hα0 hα1 hK hzero hf hF j k hj hjk z hz θ hθ =>
    h α f K hα0 hα1 hK hzero hf hF j k hj hjk z hz θ hθ⟩

end Work.FTS.StrongPersist.SP6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.F0SixYblk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The order-`7` Leibniz expansion of `D_θ^i` -/

/-- **The `a`-th summand of the Leibniz expansion of `∂_z^k D_θ^i f`, one angular order
above the range of `FlatW`.**

The angular order here is allowed to reach `i = 6` with `k + i ≤ 7`: the iterate
`D_θ^a (sin 2·)` only runs up to `a ≤ i - 1 ≤ 5` (which is why the hypothesis `i ≤ 6` is
required), and each remaining slot is one of the quantities bounded by `K` in the second
clause of `FlatW 7 f K`, i.e. by `F0 6 K (∂_θ f)`. -/
theorem leibniz_term_le7 {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (hpth : Work.FTS.PhiStar.F0 6 K (Work.Spaces.pth f))
    {i k a : ℕ} (ha : a ∈ Finset.range i) (hi6 : i ≤ 6) (hki : k + i ≤ 7)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ k * (((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ))|
      ≤ ((i - 1).choose a : ℝ) * (A * K) := by
  have halt : a < i := Finset.mem_range.mp ha
  have hai : a ≤ i - 1 := by omega
  have ha5 : a ≤ 5 := by omega
  have hX : |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A := hAb a ha5 z θ hθ hθ'
  have hY : |(z + 1) ^ k * Work.Spaces.pzIter k
      (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ| ≤ K :=
    hpth k (i - 1 - a) (by omega) z θ hz hθ hθ'
  have hcoef : (0 : ℝ) ≤ ((i - 1).choose a : ℝ) := by positivity
  have hzp : (0 : ℝ) < (z + 1) ^ k := pow_pos (by linarith) k
  have h1 : |(z + 1) ^ k * (((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ))|
      = ((i - 1).choose a : ℝ) *
        (|Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| *
          |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ|) := by
    simp only [abs_mul, abs_of_nonneg hcoef, abs_of_pos hzp]
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hX hY (abs_nonneg _) hA) hcoef

/-- **The mixed angular slot of order `k + i ≤ 7`, `i ≤ 6`, at the `∂_θ`-half constant.**

For `1 ≤ i ≤ 6`, `k + i ≤ 7` and a datum whose `∂_θ`-half lies in `F0 6 K`, the Leibniz
expansion of `D_θ^i` (`pzIter_DthIter_leibniz`) gives

`|(z+1)^k ∂_z^k D_θ^i f| ≤ 32·A·K`.

The factor `32 = 2^5` is the binomial sum `∑_{a<i} C(i-1,a) = 2^{i-1} ≤ 2^5`. -/
theorem mixed_flat_le {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hpth : Work.FTS.PhiStar.F0 6 K (Work.Spaces.pth f))
    {i k : ℕ} (hi : 1 ≤ i) (hi6 : i ≤ 6) (hki : k + i ≤ 7)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ| ≤ 32 * A * K := by
  rw [Work.FTS.PhiStar.pzIter_DthIter_leibniz (f := f) hsm hi hz ⟨hθ, hθ'⟩]
  have hchoose : (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ)) = (2 : ℝ) ^ (i - 1) := by
    have h1 : Finset.range i = Finset.range ((i - 1) + 1) := by
      congr 1
      omega
    rw [h1]
    exact_mod_cast Nat.sum_range_choose (n := i - 1)
  have hpow : (2 : ℝ) ^ (i - 1) ≤ 32 := by
    calc (2 : ℝ) ^ (i - 1) ≤ 2 ^ 5 :=
          pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 32 := by norm_num
  rw [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun a ha =>
    leibniz_term_le7 hA hK hAb hpth ha hi6 hki hz hθ hθ')) ?_
  calc (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) * (A * K))
      = (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ)) * (A * K) := (Finset.sum_mul ..).symm
    _ = (2 : ℝ) ^ (i - 1) * (A * K) := by rw [hchoose]
    _ ≤ 32 * (A * K) := mul_le_mul_of_nonneg_right hpow (mul_nonneg hA hK)
    _ = 32 * A * K := by ring

/-! ## The unified slot bound for `Y` -/

/-- **Every mixed slot `∂_z^m D_θ^i Y` with `m + i ≤ 7` and `i ≤ 6` is bounded by
`(32A+1)·K`.**

* `i = 0`: the radial slots of `FlatW 7 Y K` (`m ≤ 7`), compared with `K ≤ (32A+1)K`;
* `i ≥ 1`: the mixed bound `mixed_flat_le`, using `32·A·K ≤ (32A+1)·K`.

This is the order-`7` companion of `Work.FTS.PhiStar.CoreAux.F0_six_of_FlatW` (which stops at
order `6`, exactly because the angular Leibniz rule costs one order). -/
theorem flat_mixed_le {A K : ℝ} {Y : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hflat : Work.FTS.VocabO2.FlatW 7 Y K)
    {m i : ℕ} (hi6 : i ≤ 6) (hmi : m + i ≤ 7) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter i Y) z θ| ≤ (32 * A + 1) * K := by
  have hC1 : (1 : ℝ) ≤ 32 * A + 1 := by linarith
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp only [Work.Spaces.DthIter_zero]
    have hR : |(z + 1) ^ m * Work.Spaces.pzIter m Y z θ| ≤ K :=
      (hflat z θ hz hθ hθ').1 m (by omega)
    calc |(z + 1) ^ m * Work.Spaces.pzIter m Y z θ| ≤ K := hR
      _ = 1 * K := by ring
      _ ≤ (32 * A + 1) * K := mul_le_mul_of_nonneg_right hC1 hK
  · have h1 : 1 ≤ i := Nat.succ_le_of_lt hpos
    have hmix : |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter i Y) z θ|
        ≤ 32 * A * K :=
      mixed_flat_le hA hK hAb hsm
        (Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hflat) h1 hi6 hmi hz hθ hθ'
    have h2 : 32 * A * K ≤ (32 * A + 1) * K := by
      nlinarith [mul_nonneg hA hK]
    linarith

/-! ## The target -/

/-- **`FlatW 7 Y K` implies `F0 6 (C·K) (Yblk Y)`** with the universal constant
`C = 7·(32A+1)`, where `A` bounds the `D_θ`-iterates of `sin 2·` up to order `5`.

`D_θ^i` commutes with `D_z = z∂_z` on the open quadrant, and the `k`-fold product rule
`pzIter_zpz_expand` writes

`∂_z^k D_θ^i (Yblk Y) = z·∂_z^{k+1} D_θ^i Y + k·∂_z^k D_θ^i Y`;

both slots are bounded by `(32A+1)K` (`flat_mixed_le`, the orders being `k+1+i ≤ 7` resp.
`k+i ≤ 6`), and `z/(z+1) ≤ 1`, `k ≤ 6` finish the estimate. -/
theorem F0SixYblk : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ K → Work.FTS.EllipticEst.SmoothOpen Y → Work.FTS.VocabO2.FlatW 7 Y K →
    Work.FTS.PhiStar.F0 6 (C * K) (Work.FTS.PhiStar.Yblk Y) := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.PhiStar.CoreAux.DthIter_five_Sfun_bound
  obtain ⟨A, hApos, hAb⟩ := Work.FTS.PhiStar.CoreAux.exists_bound_of_five hMpos hM
  refine ⟨7 * (32 * A + 1), by positivity, ?_⟩
  intro K Y hK hsm hflat
  have hA0 : 0 ≤ A := hApos.le
  have hC1 : (1 : ℝ) ≤ 32 * A + 1 := by linarith
  -- the two families of slots of `Y` which the estimate consumes
  have hYp : Work.FTS.PhiStar.F0 6 K (Work.Spaces.pth Y) :=
    Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hflat
  have hD : ∀ (m i : ℕ), i ≤ 6 → m + i ≤ 7 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter i Y) z θ|
        ≤ (32 * A + 1) * K :=
    fun m i hi6 hmi z θ hz hθ hθ' => flat_mixed_le hA0 hK hAb hsm hflat hi6 hmi hz hθ hθ'
  intro k i hki z θ hz hθ hθ'
  have hk6 : k ≤ 6 := by omega
  have hi6 : i ≤ 6 := by omega
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  -- commutation and the product rule
  have hcomm := Work.FTS.PhiStar.CoreAux.DthIter_Dz_comm_smoothOpen hsm i
  have hexp := Work.FTS.PhiStar.CoreAux.pzIter_zpz_expand
    (A := Work.Spaces.DthIter i (Work.FTS.PhiStar.Yblk Y))
    (B := Work.Spaces.DthIter i Y) hcomm (hsm.DthIter i) k z θ hz hθ hθ'
  rw [hexp]
  -- the two bounded pieces
  have hb1 : |(z + 1) ^ (k + 1) * Work.Spaces.pzIter (k + 1)
      (Work.Spaces.DthIter i Y) z θ| ≤ (32 * A + 1) * K :=
    hD (k + 1) i hi6 (by omega) z θ hz hθ hθ'
  have hb2 : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ|
      ≤ (32 * A + 1) * K := hD k i hi6 (by omega) z θ hz hθ hθ'
  have hzx : |(z + 1) ^ k * z * Work.Spaces.pzIter (k + 1)
      (Work.Spaces.DthIter i Y) z θ| ≤ (32 * A + 1) * K := by
    have hzk : (0 : ℝ) ≤ z := hz.le
    have hpowk : (0 : ℝ) < (z + 1) ^ k := pow_pos hz1 k
    calc |(z + 1) ^ k * z * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ|
        = (z + 1) ^ k * z
            * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz1.le k), abs_of_nonneg hzk]
      _ ≤ (z + 1) ^ (k + 1)
            * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [pow_succ]
          nlinarith [hpowk]
      _ = |(z + 1) ^ (k + 1) * Work.Spaces.pzIter (k + 1)
            (Work.Spaces.DthIter i Y) z θ| := by
          rw [abs_mul, abs_of_pos (pow_pos hz1 (k + 1))]
      _ ≤ (32 * A + 1) * K := hb1
  have hky : |(z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k
      (Work.Spaces.DthIter i Y) z θ)| ≤ (k : ℝ) * ((32 * A + 1) * K) := by
    calc |(z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ)|
        = (k : ℝ) * |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ| := by
          rw [show (z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ)
                = (k : ℝ) * ((z + 1) ^ k
                    * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ) from by ring,
              abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      _ ≤ (k : ℝ) * ((32 * A + 1) * K) :=
          mul_le_mul_of_nonneg_left hb2 (Nat.cast_nonneg k)
  have hre : (z + 1) ^ k * (z * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ
        + (k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ)
      = ((z + 1) ^ k * z) * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ
        + (z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ) := by
    ring
  rw [hre]
  refine le_trans (abs_add_le _ _) ?_
  have hkR : (k : ℝ) ≤ 6 := by exact_mod_cast hk6
  have hA0K : (0 : ℝ) ≤ (32 * A + 1) * K := mul_nonneg (by linarith) hK
  have hfin : (32 * A + 1) * K + (k : ℝ) * ((32 * A + 1) * K) ≤ 7 * ((32 * A + 1) * K) := by
    have := mul_le_mul_of_nonneg_right hkR hA0K
    linarith
  calc |(z + 1) ^ k * z * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ|
        + |(z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ)|
      ≤ (32 * A + 1) * K + (k : ℝ) * ((32 * A + 1) * K) := add_le_add hzx hky
    _ ≤ 7 * ((32 * A + 1) * K) := hfin
    _ = (7 * (32 * A + 1)) * K := by ring

end Work.FTS.StrongPersist.SP6
end
end
