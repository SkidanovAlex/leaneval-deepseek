import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.BadsummandQ
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.WDp_le_of_pointwise
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.sum_L12_iter_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

open MeasureTheory

/-- The half-line integrals `∫_{(0,∞)}` and `∫_{Iz}` agree, since `Iz = [0,∞)` and `{0}` is
null. -/
private theorem integral_Ioi_eq_integral_Iz (F : ℝ → ℝ) :
    (∫ z in Set.Ioi (0 : ℝ), F z) = ∫ z in Work.Spaces.Iz, F z := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))


end Work.FTS.CoercivityFix.Transfer.E2norm
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.sum_Qang_iter_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.CoercivityFix.Transfer.E2norm



end Work.FTS.CoercivityFix.Transfer.E2norm
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Integrability of the majorant -/


/-! ## The main statement -/


end Work.FTS.CoercivityFix.Transfer.E2pkg
end
end
-- ===== merged: Submission.Work.FTS.EllSol.HeavyFlat.flatHeavy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.HeavyFlat

/-- **The flat shifted heavy-weight mixed-slot finiteness** (`b`-general form).  For every shift
`b : ℝ` and every `u` of class `C²` on the open strip `ℝ × (0,π/2)` whose end-point *values*
vanish, if the three `σ_η`-weighted diagonal slots — `((∂_t-b)u)²σ_η`, `((∂_t-b)²u)²σ_η`,
`(∂_θ²u)²σ_η`, `σ_η = sin(2θ)^{-η}` — are integrable on the strip, then the `σ_η`-weighted
`(1,1)`-slot `(∂_θ(∂_t-b)u)²σ_η` has finite `∫⁻` on the strip.  This is the workspace's recorded
node `Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness` (its file `Shift2Flat/mixedSlotFiniteness.lean`
still carries a `sorry`; `Shift2Flat/mixedSlotLtTop.lean` too, so there is nothing to cite).  Its
route is documented, hand-verified and ingredient-complete in
`Submission/Work/FTS/EllSol/Shift2Flat/NOTES_mixedSlot_route.md`: truncate `u` in `t` by
`Work.FTS.EllSol.Trunc.chi`; apply the *proved* complex angular Agmon
`Work.FTS.EllSol.Trunc.curlAgmon` to the `θ`-slices of the `t`-Fourier transform at each
frequency; identify the four integrated slots with `Work.FTS.EllSol.ShiftFT.plancherelShift`
(and its second-order companion) so that the frequency multiplier `μ(ξ) = (2πξ)²+b²` reproduces
the shifted slots; Cauchy–Schwarz in `ξ`; then Fatou in the truncation scale, the truncation
errors being paid by `(M1)–(M3)` of that note (`u` and `∂_θu` are bounded by
`∫_0^{π/2}|∂_θ²u|`, the latter being the `hQ`-slot). -/
theorem flatHeavy : Work.FTS.EllSol.HeavyFlat.FlatHeavy := by
  -- `FlatHeavy` is the `Shift2Flat.mixedSlotFiniteness` statement with `sEta` written as `sigE`
  -- (`sigE` and `sEta` are the same function by definition).
  intro b u hu h0 hπ hV hZ hQ
  exact Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness (b := b) u hu h0 hπ hV hZ hQ

end Work.FTS.EllSol.HeavyFlat
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.Cores.topSlotB_two_step5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two-dimensional transfer of the slice Step-5 estimate

This file proves the requested lemma `Work.FTS.EllipticEst.Cores.topSlotB_two_step5`, the
two-dimensional Step-5 estimate of Elgindi's `prop:H2` for the second angular derivative
`∂_θθΨ` in the weak hypothesis class `TT.EllWeakPos α 2 F Ψ`:

  `s20M4 α Ψ ≤ C (s20J2 α F Ψ + s20M3 α Ψ + s20A2 Ψ + s20A1 Ψ + s20A0 Ψ)`.

The mathematical content is the *slicewise transfer*:

* for every `z > 0`, the slice `u_z := Ψ z ·` satisfies all the hypotheses of the
  one-dimensional Step-5 estimate (`Cores.topB_sliceStep5_uniform`): the equation
  `Lzero1 u_z = Gsrc α F Ψ z ·` on `(0,π/2)`, the two Dirichlet values, continuity on the closed
  interval (`remov.weakSliceRegular`) and the six `IntegrableOn` slots
  (`H2W.Step5.s20SliceIntegrable` together with `remov.weakSliceRegular`);
* hence the slice estimate holds for every `z > 0`; multiplying it by the nonnegative radial
  weight `2 w(z)²` and rewriting the five right-hand slots as `SG, SM3, SA2, SA1, SA0` gives the
  a.e.-in-`z` comparison
  `z ↦ ∫_θ s20F4 α Ψ z θ ≤ z ↦ 2 C (SG + SM3 + SA2 + SA1 + SA0)`;
* the five slot functions are honest by `Cores.topB_step5_integrable`, so
  `integral_mono_of_nonneg` integrates the comparison:
  `s20M4 α Ψ ≤ 2 C (∫ SG + ∫ SM3 + ∫ SA2 + ∫ SA1 + ∫ SA0)`;
* the slot integrals are `s20J2 α F Ψ`, `s20M3 α Ψ / 8`, `s20A2 Ψ`, `s20A1 Ψ`, `s20A0 Ψ`, and
  `s20M3 α Ψ ≥ 0`, giving the statement with the constant `2 C`. -/

/-! ## Bridging `pthIter` and iterated `deriv` -/

private lemma pthIter_one (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 1 Ψ z θ = deriv (fun t => Ψ z t) θ := rfl

private lemma pthIter_two (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 Ψ z θ = deriv (fun t => deriv (fun s => Ψ z s) t) θ := rfl

private lemma pthIter_three (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 3 Ψ z θ = deriv (deriv (deriv (fun t => Ψ z t))) θ := rfl

private lemma pthIter_four (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 4 Ψ z θ
      = deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ := rfl

private lemma pthIter_two_G (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ
      = deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ := rfl

/-! ## The slot functions -/

/-- The `z`-integrand of `s20J2`: the source slot `∫_θ (∂_θ²Gsrc)² σ₄`. -/
private def SG (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)

/-- The `z`-integrand of `s20M3`: the Step-4 slot `∫_θ (∂_θ³Ψ)² σ₂`. -/
private def SM3 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)

/-- The `z`-integrand of `s20A2`: the `η`-slot `∫_θ (∂_θ²Ψ)² sEta`. -/
private def SA2 (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The `z`-integrand of `s20A1`: the slot `∫_θ (∂_θΨ)²`. -/
private def SA1 (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2

/-- The `z`-integrand of `s20A0`: the slot `∫_θ Ψ²`. -/
private def SA0 (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2

private lemma sin_two_nonneg_Iθ'_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-! ## Rewriting the six integrands -/

private lemma s20F4_eq_slots (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
      = 2 * (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) := by
  have hp : ∀ θ : ℝ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
      = (2 * (Work.Spaces.w z) ^ 2) *
        ((deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) := by
    intro θ
    rw [show Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        = (2 * (Work.Spaces.w z) ^ 2) * ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) from rfl]
    rw [pthIter_four Ψ z θ]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hp),
    MeasureTheory.integral_const_mul]

private lemma SG_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SG α F Ψ z = (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) := by
  rw [SG, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    rw [pthIter_two_G α F Ψ z θ])]

private lemma SM3_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SM3 α Ψ z = (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) := by
  rw [SM3, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    rw [pthIter_three Ψ z θ])]

private lemma SA2_eq (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SA2 Ψ z = (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) := by
  rw [SA2, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    rw [pthIter_two Ψ z θ])]

private lemma SA1_eq (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SA1 Ψ z = (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2) := by
  rw [SA1, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    rw [pthIter_one Ψ z θ])]

/-! ## The assembly -/

theorem topSlotB_two_step5 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20M4 α Ψ
        ≤ C * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ
            + Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
            + Work.FTS.EllipticEst.H2W.s20A0 Ψ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := topB_sliceStep5_uniform
  refine ⟨2 * C₁, by linarith, ?_⟩
  intro α F Ψ hα hα4 h
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hγ1 : 1 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγ2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- the slice estimate, for each `z > 0`
  have hslice : ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
        ≤ 2 * C₁ * (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z) := by
    intro z hz
    have hu4 : ContDiffOn ℝ 4 (fun t => Ψ z t) (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 4 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      have h2 := (h.smooth 4).comp h1 (fun θ hθ => ⟨hz, hθ⟩)
      simpa [Function.comp_def, Function.uncurry] using h2
    have hwr :=
      Work.FTS.EllipticEst.remov.weakSliceRegular 2 (by norm_num) α F Ψ hα hα4 h z hz
    have huc : ContinuousOn (fun t => Ψ z t) (Set.Icc 0 (Real.pi / 2)) := hwr.1
    have hz0 : (fun t => Ψ z t) 0 = 0 := hwr.2.1
    have hzpi : (fun t => Ψ z t) (Real.pi / 2) = 0 := hwr.2.2.1
    have hI0 : MeasureTheory.IntegrableOn (fun θ => ((fun t => Ψ z t) θ) ^ 2)
        Work.Spaces.Iθ := hwr.2.2.2.2.1
    have hI1 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => Ψ z t) θ) ^ 2)
        Work.Spaces.Iθ := hwr.2.2.2.2.2.1
    have hI2 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hwr.2.2.2.2.2.2
    obtain ⟨_, _, _, hIslice3, hIslice4, hIsliceG⟩ :=
      Work.FTS.EllipticEst.H2W.Step5.s20SliceIntegrable α F Ψ hα hα4 h z hz
    have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
          = (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t) θ :=
      fun θ hθ => Work.FTS.EllipticEst.Mine.Lzero1_slice_eq_Gsrc h.eq hz hθ.1 hθ.2
    have h1d := hC₁ (Work.Spaces.gam α) hγ1 hγ2 (fun t => Ψ z t)
      (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t) hu4 huc hz0 hzpi hode
      hIslice4 hIslice3 hI2 hI1 hI0 hIsliceG
    rw [s20F4_eq_slots α Ψ z, SG_eq α F Ψ z, SM3_eq α Ψ z, SA2_eq Ψ z, SA1_eq Ψ z]
    calc 2 * (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
        ≤ 2 * (Work.Spaces.w z) ^ 2 *
            (C₁ * ((∫ θ in Work.Spaces.Iθ,
                  (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
                    Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
                    Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
              + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 *
                    Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, ((fun t => Ψ z t) θ) ^ 2))) := by
          exact mul_le_mul_of_nonneg_left h1d (by positivity)
      _ = 2 * C₁ * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
                (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
                  Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
          + (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
                  Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
          + (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 *
                  Work.FTS.EllipticEst.sEta θ)
          + (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2)
          + (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, ((fun t => Ψ z t) θ) ^ 2)) := by
          ring
  -- the five slot functions are honest
  obtain ⟨hSGint, hSM3int, hSA2int, hSA1int, hSA0int⟩ :=
    topB_step5_integrable α F Ψ hα hα4 h
  -- the a.e. comparison in `z`
  have hae : (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => 2 * C₁ * (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem hIz fun z hz => ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      have h0 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ 0 θ) = 0 := by
        simp only [Work.FTS.EllipticEst.H2W.s20F4, hw0]
        simp
      have h1 : (2 * C₁ * (SG α F Ψ 0 + SM3 α Ψ 0 + SA2 Ψ 0 + SA1 Ψ 0 + SA0 Ψ 0)) = 0 := by
        simp only [SG, SM3, SA2, SA1, SA0, hw0]
        ring
      simp only []
      rw [h0, h1]
    · exact hslice z hzpos
  -- the monotone comparison of the outer integrals
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ) := by
    refine Filter.Eventually.of_forall fun z => ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [show Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        = 2 * (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) from rfl]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ'_prv hθ) _))
  have hintR : MeasureTheory.Integrable
      (fun z => 2 * C₁ * (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((((hSGint.add hSM3int).add hSA2int).add hSA1int).add hSA0int).const_mul _
  have hmain := MeasureTheory.integral_mono_of_nonneg hnn hintR hae
  -- identify the two sides
  have hLs : (∫ z in Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
      = Work.FTS.EllipticEst.H2W.s20M4 α Ψ := rfl
  have hRs : (∫ z in Work.Spaces.Iz,
      (fun z => 2 * C₁ * (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z)) z)
      = 2 * C₁ * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
          + (1 / 8) * Work.FTS.EllipticEst.H2W.s20M3 α Ψ
          + Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
          + Work.FTS.EllipticEst.H2W.s20A0 Ψ) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hA : (∫ z in Work.Spaces.Iz,
        (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z))
        = (∫ z in Work.Spaces.Iz, SG α F Ψ z) + (∫ z in Work.Spaces.Iz, SM3 α Ψ z)
          + (∫ z in Work.Spaces.Iz, SA2 Ψ z) + (∫ z in Work.Spaces.Iz, SA1 Ψ z)
          + (∫ z in Work.Spaces.Iz, SA0 Ψ z) := by
      rw [MeasureTheory.integral_add
            (f := (fun z => SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z))
            (g := (fun z => SA0 Ψ z)) (((hSGint.add hSM3int).add hSA2int).add hSA1int) hSA0int,
          MeasureTheory.integral_add
            (f := (fun z => SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z))
            (g := (fun z => SA1 Ψ z)) ((hSGint.add hSM3int).add hSA2int) hSA1int,
          MeasureTheory.integral_add
            (f := (fun z => SG α F Ψ z + SM3 α Ψ z))
            (g := (fun z => SA2 Ψ z)) (hSGint.add hSM3int) hSA2int,
          MeasureTheory.integral_add (f := (SG α F Ψ)) (g := (SM3 α Ψ)) hSGint hSM3int]
    rw [hA]
    have e1 : (∫ z in Work.Spaces.Iz, SG α F Ψ z) = Work.FTS.EllipticEst.H2W.s20J2 α F Ψ := by
      rw [Work.FTS.EllipticEst.H2W.s20J2]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      rfl
    have e2 : (∫ z in Work.Spaces.Iz, SM3 α Ψ z)
        = (1 / 8) * Work.FTS.EllipticEst.H2W.s20M3 α Ψ := by
      have hF3 : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
          = 8 * SM3 α Ψ z := by
        intro z
        rw [show (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
            = ∫ θ in Work.Spaces.Iθ, (8 * (Work.Spaces.w z) ^ 2) *
                ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
                  Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) from rfl]
        rw [MeasureTheory.integral_const_mul, SM3]
        ring
      rw [Work.FTS.EllipticEst.H2W.s20M3,
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hF3),
        MeasureTheory.integral_const_mul]
      ring
    have e3 : (∫ z in Work.Spaces.Iz, SA2 Ψ z) = Work.FTS.EllipticEst.H2W.s20A2 Ψ := rfl
    have e4 : (∫ z in Work.Spaces.Iz, SA1 Ψ z) = Work.FTS.EllipticEst.H2W.s20A1 Ψ := rfl
    have e5 : (∫ z in Work.Spaces.Iz, SA0 Ψ z) = Work.FTS.EllipticEst.H2W.s20A0 Ψ := rfl
    rw [e1, e2, e3, e4, e5]
  rw [hLs, hRs] at hmain
  have hM3 : 0 ≤ Work.FTS.EllipticEst.H2W.s20M3 α Ψ :=
    Work.FTS.EllipticEst.H2W.s20M3_nonneg α Ψ
  have hfin : 2 * C₁ * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
        + (1 / 8) * Work.FTS.EllipticEst.H2W.s20M3 α Ψ
        + Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
        + Work.FTS.EllipticEst.H2W.s20A0 Ψ)
      ≤ 2 * C₁ * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
        + Work.FTS.EllipticEst.H2W.s20M3 α Ψ + Work.FTS.EllipticEst.H2W.s20A2 Ψ
        + Work.FTS.EllipticEst.H2W.s20A1 Ψ + Work.FTS.EllipticEst.H2W.s20A0 Ψ) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    linarith
  linarith [hmain, hfin]

end

end Work.FTS.EllipticEst.Cores
end
-- ===== merged: Submission.Work.FTS.IPGen.IP4Add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Locality and linearity of the two derivatives on the open quadrant -/

/-- Two functions that agree on the open quadrant have the same `D_θ` there (the derivative is
local and `Qd` is open in the `θ`-variable). -/
theorem Dth_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' ⟨hzθ.1, hθ'⟩
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [heq.deriv_eq]

/-- Two functions that agree on the open quadrant have the same `D_z` there. -/
theorem Dz_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have heq : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ ⟨hz', hzθ.2⟩
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [heq.deriv_eq]

/-- The `(a,b) = (1,0)` block of `BlocksAdd`: `D_θ` is additive on the open quadrant. -/
theorem Dth_add_of_blocksAdd {k : ℕ} {f₁ f₂ : Fn}
    (h : Work.FTS.CoercivityFix.Assembly.BlocksAdd k f₁ f₂) (hk : 1 ≤ k) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (f₁ + f₂) z θ
        = (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) z θ := by
  intro z θ hzθ
  have h0 := h 1 0 hk z θ hzθ
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
    Pi.add_apply] using h0

/-- The `(a,b) = (0,1)` block of `BlocksAdd`: `D_z` is additive on the open quadrant. -/
theorem Dz_add_of_blocksAdd {k : ℕ} {f₁ f₂ : Fn}
    (h : Work.FTS.CoercivityFix.Assembly.BlocksAdd k f₁ f₂) (hk : 1 ≤ k) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (f₁ + f₂) z θ
        = (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) z θ := by
  intro z θ hzθ
  have h0 := h 0 1 hk z θ hzθ
  simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Pi.add_apply] using h0

/-! ## The open-class additivity package -/

/-- **The open-class additivity package at level `n`.**  `IP` is the `n`-fold `HkIPStep`
iterate above `H1IP`; the `add` clause takes the interior class `SmoothOpen` and the honesty
`HkMem α (n+1)` — the level at which the pairing `IP (f₁+f₂) g` is consumed. -/
structure Comm2o (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument on the open class -/
  add : ∀ f₁ f₂ g : Fn, Work.FTS.EllipticEst.SmoothOpen f₁ →
    Work.FTS.EllipticEst.SmoothOpen f₂ → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α (n + 1) f₁ → Work.Spaces.HkMem α (n + 1) f₂ →
    Work.Spaces.HkMem α (n + 1) g → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g

/-- **The base case**: additivity of `H1IP` on the open class, which is
`Transfer.H1IP_add_weak` with the block hypotheses discharged by
`BlocksCont_of_smoothOpen`/`BlocksAdd_of_smoothOpen`. -/
theorem Comm2o_zero (α : ℝ) :
    Comm2o α 0 (Work.Coercivity.H1IP α) := by
  refine ⟨fun f f' g h => Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd α h, ?_⟩
  intro f₁ f₂ g hf₁ hf₂ hg hm₁ hm₂ hmg
  have hbadd : Work.FTS.CoercivityFix.Assembly.BlocksAdd 1 f₁ f₂ :=
    (BlocksAdd_of_smoothOpen hf₁ hf₂ : Work.FTS.CoercivityFix.Assembly.BlocksAdd 1 f₁ f₂)
  exact Work.FTS.CoercivityFix.Transfer.H1IP_add_weak α hm₁ hm₂ hmg
    (hf₁.continuousOn) (hf₂.continuousOn) (hg.continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dz hf₁).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dz hf₂).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dz hg).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hf₁).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hf₂).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hg).continuousOn)
    (Dz_add_of_blocksAdd hbadd (le_refl 1)) (Dth_add_of_blocksAdd hbadd (le_refl 1))

/-- **The induction step**: `Comm2o` climbs one level under `HkIPStep c₁ c₂`, the descent of
the honesty and of the block packages being supplied by the interior smoothness of the
arguments (`IPGen/OpenBasic.lean`). -/
theorem Comm2o_succ (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) (n : ℕ)
    {IP : Fn → Fn → ℝ} {c₁ c₂ : ℝ} (hc : Comm2o α n IP) :
    Comm2o α (n + 1) (Work.Coercivity.HkIPStep c₁ c₂ IP) := by
  have h1n : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  refine ⟨?_, ?_⟩
  · intro f f' g hfg
    have e0 := hc.congr f f' g hfg
    have e1 := hc.congr (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
      (Dth_congr_Qd hfg)
    have e2 := hc.congr (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
      (Dz_congr_Qd hfg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
  · intro f₁ f₂ g hf₁ hf₂ hg hm₁ hm₂ hmg
    -- descent of the honesty from level `n+2` to level `n+1`
    obtain ⟨hm₁', hmth₁, hmz₁⟩ := HkMem_descent hα hf₁ hm₁
    obtain ⟨hm₂', hmth₂, hmz₂⟩ := HkMem_descent hα hf₂ hm₂
    obtain ⟨hmg', hmthg, hmzg⟩ := HkMem_descent hα hg hmg
    have hsf₁ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f₁) :=
      Work.FTS.EllipticEst.SmoothOpen.Dth hf₁
    have hsf₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f₂) :=
      Work.FTS.EllipticEst.SmoothOpen.Dth hf₂
    have hsg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) :=
      Work.FTS.EllipticEst.SmoothOpen.Dth hg
    have hzf₁ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f₁) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz hf₁
    have hzf₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f₂) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz hf₂
    have hzg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz hg
    have hbadd : Work.FTS.CoercivityFix.Assembly.BlocksAdd (n + 1) f₁ f₂ :=
      (BlocksAdd_of_smoothOpen hf₁ hf₂ : Work.FTS.CoercivityFix.Assembly.BlocksAdd (n + 1) f₁ f₂)
    have e0 := hc.add f₁ f₂ g hf₁ hf₂ hg hm₁' hm₂' hmg'
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [hc.congr (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (Dth_add_of_blocksAdd hbadd h1n)]
      exact hc.add (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        hsf₁ hsf₂ hsg hmth₁ hmth₂ hmthg
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [hc.congr (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (Dz_add_of_blocksAdd hbadd h1n)]
      exact hc.add (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        hzf₁ hzf₂ hzg hmz₁ hmz₂ hmzg
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
    ring

/-! ## The three levels up to `IP4` -/

theorem Comm2o_one (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) {c₁ c₂ : ℝ} :
    Comm2o α 1 (Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α) :=
  Comm2o_succ α hα 0 (Comm2o_zero α)

theorem Comm2o_two (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) {c₁ c₂ c₁' c₂' : ℝ} :
    Comm2o α 2 (Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α) :=
  Comm2o_succ α hα 1 (Comm2o_one α hα)

theorem Comm2o_three (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    Comm2o α 3 (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) :=
  Comm2o_succ α hα 2 (Comm2o_two α hα)

/-- **Additivity of the coercive `IP4` on the open class `HQo α 4`** — the `add` clause of the
corrected contract `N4ExtraQ`. -/
theorem ip4_add_HQo {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn,
      Work.FTS.VocabO.HQo α 4 f₁ → Work.FTS.VocabO.HQo α 4 f₂ → Work.FTS.VocabO.HQo α 4 g →
      Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ + f₂) g
        = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g
          + Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα f₁ f₂ g h₁ h₂ h₃
  exact (Comm2o_three α (by linarith [hα.1])).add f₁ f₂ g h₁.1 h₂.1 h₃.1 h₁.2 h₂.2 h₃.2

/-- **Congruence of `IP4` in its first argument on the open quadrant**, with no membership at
all: the `congr` clause of the `Comm2`-package for `IP4` (`Assembly.Comm2_levels`). -/
theorem ip4_congr_Qd {c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ} (hα : 0 < α) {f f' g : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g
      = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f' g :=
  (Work.FTS.CoercivityFix.Assembly.Comm2_levels α hα).2.2.congr f f' g h

end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow11 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-! ## Row 11 with the `𝒲`-decay of the star coefficient restored

The statement `NRow11` of this file is **not derivable from its hypotheses as frozen**: its
`HkMem α 4 (N1ss α Φs)` conjunct is a weighted-decay statement, and the primed package
`Work.FTS.VocabO.StarPkgo` supplies only *flat* open-quadrant suprema
(`WDMem 4 (((z+1)/z)·ℛ(Φ̃_*))`, `WDp 4 (…) ≤ Cs·α`), which by the proved
`Work.FTS.OpenPkg.WDMem_of_WDp_le` give only `|∂_z^b D_θ^j Rv| ≤ Cs·α` — no control of
`z^b ∂_z^b D_θ^j Rv`, which is exactly what the `ℋ⁴`-integrand of `N1ss` needs.  The frozen
*unprimed* `StarPkg.R` carries that information as a `WlInfMem`/`WlInf` field, and the unprimed
row 11 (`Work.FTS.Nonlinear.Pieces.RNPV2.row11`, verified `sorry`-free) is proved from it.

See `NOTES_NRow11.md` for the full diagnosis.  The lemma below is the same row *with that field
restored as an explicit hypothesis*; it is the statement the lead obtains by adding the
`WlInf`-form of `StarPkg.R` (resp. of `dU`, `V` for rows 14/15/18/19) to `StarPkgo`, and it is
proved by running the unprimed proof in the primed (open-quadrant) class, using the
open-quadrant ports `WtoH_Radial_O`, `WtoH_Mixed_O`, `sqm_pz_DthIter_mul_le_4_open`,
`smoothOpen_radA` and `wtoHQ_of_pointwise_open`. -/

/- **RETIRED.**  The row-11 statement under the *frozen* `Work.FTS.NonlinRows.Ctx`
(`VocabO.StarPkgo`) is not derivable: its `HkMem α 4 (N1ss α Φs)` conjunct needs
`(1+z)^b ∂_z^b D_θ^j ((z+1)/z·ℛ(Φ̃_*)) = O(1)` for `b + j ≤ 4`, which the flat `WDMem`/`WDp`
pricing of the star coefficient cannot supply (see `NOTES_NRow11.md`; the machine-checked argument
is in the docstring of `NRow11_of_wlInf` above).  The **true** form is
`Work.FTS.NonlinRows.NRow11T2` in `Submission/Work/FTS/NonlinRows/NRow11T2.lean`, proved against
the upgraded `Work.FTS.VocabO2.Ctx2` whose `StarPkgo2.RW` is exactly the missing `𝒲^{4,∞}` field. -/

end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow1_7Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## `SmoothOpen` closure (local copies, Mathlib-level)

The tree's `SmoothOpen`-API modules (`alphaDzW_Hk_le`, `EllHyp_certificates`, `AeI1Fts`) are
currently unbuildable (`lake` reports upstream errors), so the few closure facts needed here are
re-proved directly from Mathlib's `ContDiffOn` API. -/

theorem smoothOpen_add {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.add hg

theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.mul hg

theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ) = c • Function.uncurry f := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.const_smul c

theorem smoothOpen_sub {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.sub hg

/-- A radial function which is `C^n` on `(0,∞)` for every `n` is `C^∞` on the open quadrant. -/
theorem smoothOpen_radial {r : ℝ → ℝ} (hr : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
  refine contDiffOn_infty.mpr fun n => ?_
  change ContDiffOn ℝ n (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0
  exact (hr n).comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-- `tan` is smooth on the open quadrant. -/
theorem smoothOpen_tan : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.tan θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
    Work.FTS.EllipticEst.Q0
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hθ0], by linarith [Real.pi_pos, hθ1]⟩)
  refine ContDiffOn.congr (hsin.div hcos hne) ?_
  intro p _
  simp only [Real.tan_eq_sin_div_cos, Pi.div_apply]

/-- `Vop Φ` is smooth on the open quadrant as soon as `Φ` is. -/
theorem smoothOpen_Vop {Φ : Fn} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Φ) := by
  have hprod : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Φ z θ) :=
    smoothOpen_mul smoothOpen_tan hΦ
  have hkey : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Φ z θ - Real.tan θ * Φ z θ) :=
    smoothOpen_sub (Work.FTS.EllipticEst.SmoothOpen.pth hΦ) hprod
  refine ContDiffOn.congr (f₁ := fun p : ℝ × ℝ => Work.Construction.Vop Φ p.1 p.2) hkey ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- The `θ`-slice of a `SmoothOpen` function is differentiable. -/
theorem differentiableAt_slice_snd_of_smoothOpen {F : Fn}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => F z θ') θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hc : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry F) (z, θ) :=
    hF.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hc1 : ContDiffAt ℝ 1 (Function.uncurry F) (z, θ) := hc.of_le (by simp)
  have hd : DifferentiableAt ℝ (Function.uncurry F) (z, θ) := hc1.differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ (fun t : ℝ => (z, t)) θ :=
    (differentiableAt_const (c := z)).prodMk differentiableAt_id
  exact (hd.comp θ h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)

/-- **The pointwise relation carried by `EllPkgGo.V`.**  Since
`PhiTil α g Φg = Φg - (1/(4α)) sin(2θ) L₁₂(g)`, one has

  `Vop (PhiTil α g Φg) = Vop Φg - (1/(2α)) · c2m(θ) · L₁₂(g)(z)`. -/
theorem vop_PhiTg_eq (α : ℝ) {g Φg : Fn} {z θ : ℝ}
    (hΦ : DifferentiableAt ℝ (fun θ' => Φg z θ') θ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
      = Work.Construction.Vop Φg z θ
        - (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z) := by
  have hθIoo : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hTheta : HasDerivAt
      (fun θ' : ℝ => (1 / (4 * α)) * (Real.sin (2 * θ') * Work.Construction.L12 g z))
      ((1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z)) θ :=
    (hsin.mul_const (Work.Construction.L12 g z)).const_mul (1 / (4 * α))
  have hPhiTg : HasDerivAt
      (fun θ' : ℝ => Work.FTS.Nonlin.PhiTg α g Φg z θ')
      (deriv (fun θ' => Φg z θ') θ
        - (1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Φg z θ') (deriv (fun θ' => Φg z θ') θ) θ :=
      hΦ.hasDerivAt
    refine (h1.sub hTheta).congr_of_eventuallyEq ?_
    filter_upwards with θ'
    simp only [Work.FTS.Nonlin.PhiTg, Work.Construction.PhiTil, Work.Construction.Theta,
      Work.Construction.s2, Pi.sub_apply]
    ring_nf
  have hmain : deriv (fun θ' => Work.FTS.Nonlin.PhiTg α g Φg z θ') θ
      = deriv (fun θ' => Φg z θ') θ
        - (1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z) :=
    hPhiTg.deriv
  have hcf : Work.Construction.c2m θ = 1 - 3 * Real.sin θ ^ 2 := by
    rw [Work.Construction.c2m, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hfac : 2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ) = 2 * Work.Construction.c2m θ := by
    rw [Work.FTS.EllipticEst.vop_factor_eq θ hθIoo, hcf]
  have htanmul : Real.tan θ * (Real.sin (2 * θ) * Work.Construction.L12 g z)
      = (2 * Real.sin θ ^ 2) * Work.Construction.L12 g z := by
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩)
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
  show deriv (fun θ' => Work.FTS.Nonlin.PhiTg α g Φg z θ') θ
      - Real.tan θ * Work.FTS.Nonlin.PhiTg α g Φg z θ
    = (deriv (fun θ' => Φg z θ') θ - Real.tan θ * Φg z θ)
      - (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z)
  have hmain2 : (1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z)
      - Real.tan θ * ((1 / (4 * α)) * (Real.sin (2 * θ) * Work.Construction.L12 g z))
      = (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z) := by
    have h1 : (1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z)
        - Real.tan θ * ((1 / (4 * α)) * (Real.sin (2 * θ) * Work.Construction.L12 g z))
        = (1 / (4 * α))
          * ((2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ))
            * Work.Construction.L12 g z) := by ring
    rw [h1, hfac]
    ring
  rw [hmain]
  simp only [Work.FTS.Nonlin.PhiTg, Work.Construction.PhiTil, Work.Construction.Theta,
    Work.Construction.s2]
  linarith [hmain2]

/-- **The smoothness of `c2m(θ)·L₁₂(g)(z)`**, read off from `EllPkgGo.V`. -/
theorem smoothOpen_c2m_L12 {α : ℝ} {g Φg : Fn} (hα : 0 < α)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) := by
  have hVΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Φg) := smoothOpen_Vop hΦg
  have hdiff : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Vop Φg z θ
        - Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) :=
    smoothOpen_sub hVΦ hV
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z)) := by
    refine ContDiffOn.congr (f₁ := fun p : ℝ × ℝ => (1 / (2 * α))
      * (Work.Construction.c2m p.2 * Work.Construction.L12 g p.1)) hdiff ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have h := vop_PhiTg_eq (g := g) α
      (differentiableAt_slice_snd_of_smoothOpen hΦg hz ⟨hθ0, hθ1⟩) ⟨hθ0, hθ1⟩
    show (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z)
      = Work.Construction.Vop Φg z θ
        - Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
    rw [h]; ring
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * α) * ((1 / (2 * α))
        * (Work.Construction.c2m θ * Work.Construction.L12 g z))) :=
    smoothOpen_const_mul (2 * α) h1
  refine ContDiffOn.congr (f₁ := fun p : ℝ × ℝ =>
    Work.Construction.c2m p.2 * Work.Construction.L12 g p.1) h2 ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  show Work.Construction.c2m θ * Work.Construction.L12 g z
    = (2 * α) * ((1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z))
  field_simp


/-- **The radial smoothness of `L₁₂(g)`.**  Dividing `c2m(θ)·L₁₂(g)(z)` by the non-zero
constant `c2m(π/4) = -1/2` on the slice `θ = π/4` gives `C^∞`-smoothness of `z ↦ L₁₂(g)(z)`
on `(0,∞)`. -/
theorem smoothOpen_L12_radial {α : ℝ} {g Φg : Fn} (hα : 0 < α)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) := by
  have hc2m := smoothOpen_c2m_L12 hα hΦg hV
  have hθ₀ : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Construction.c2m (Real.pi / 4) * Work.Construction.L12 g z)
      (Set.Ioi 0) :=
    hc2m.curry_z hθ₀
  have hne : Work.Construction.c2m (Real.pi / 4) ≠ 0 := by
    rw [Work.Construction.c2m]
    have h1 : Real.cos (2 * (Real.pi / 4)) = 0 := by
      rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
    rw [h1]
    have h2 : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
      rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [h2]; norm_num
  have hmain : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Construction.L12 g z) (Set.Ioi 0) := by
    refine ContDiffOn.congr
      (hslice.const_smul ((Work.Construction.c2m (Real.pi / 4))⁻¹)) ?_
    intro z _
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  refine smoothOpen_radial (r := fun z => Work.Construction.L12 g z) fun n => ?_
  exact (contDiffOn_infty.mp hmain) n

/-! ## The `D_z`-iterate bounds for `L₁₂(g)` -/

/-- **The uniform bounds on the `D_z`-iterates of `L₁₂(g)`.**  For `GalClass`-type data,
`|D_z^b L₁₂(g)(z)| ≤ KL·Xn α g` for `b ≤ 4` and every `z > 0`: the `b = 0` case is the growth
estimate `(L₁₂ g z)² ≤ Kc X² min(z³, 1/z)`, and `b ≥ 1` is the angular-moment recursion
`D_z^{k+1}L₁₂(g) = -Qang g k` together with `(Qang g k z)² ≤ (∫Kθ²)·HkSq α 4 g`. -/
theorem L12_dzdIter_abs_le :
    ∃ KL : ℝ, 0 < KL ∧ ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g →
      (∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
        Filter.Tendsto (fun z => Work.Spaces.DzIter i g z θ) Filter.atTop (nhds 0)) →
      Work.Construction.L12 g 0 = 0 →
      ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
          ≤ KL * Work.FTS.Nonlin.Xn α g := by
  set Kc : ℝ := max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / (3 : ℝ))
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 with hKc
  have hKth0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hmax0 : 0 ≤ max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / (3 : ℝ))
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) :=
    le_trans (by positivity) (le_max_right _ _)
  have hKc1 : 1 ≤ Kc := by rw [hKc]; linarith
  have hKc0 : 0 < Kc := lt_of_lt_of_le zero_lt_one hKc1
  refine ⟨Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1,
    by positivity, ?_⟩
  intro α g hα hα1 hsm hmem hdec h0 b hb z hz
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hXs : (Work.Spaces.HkSq α 4 g) = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    obtain ⟨hgrowth1, hgrowth2⟩ :=
      Work.FTS.Nonlinear.Pieces.L12_sq_le_growth α hα hα1 hsm hmem h0
    have hKcX0 : 0 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by positivity
    have hbound : (Work.Construction.L12 g z) ^ 2 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
      rcases le_or_gt z 1 with hz1 | hz1
      · refine (hgrowth1 z hz).trans ?_
        have : z ^ 3 ≤ 1 := pow_le_one₀ hz.le hz1
        calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3
            ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left this hKcX0
          _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
      · refine (hgrowth2 z hz).trans ?_
        have : 1 / z ≤ 1 := by rw [div_le_one hz]; linarith
        calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z
            = (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (1 / z) := by ring
          _ ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left this hKcX0
          _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    have h1 : |Work.Construction.L12 g z| ≤ Real.sqrt Kc * Work.FTS.Nonlin.Xn α g := by
      have h := Real.sqrt_le_sqrt hbound
      rw [Real.sqrt_mul (le_of_lt hKc0), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq hX0] at h
      exact h
    have h2 : Real.sqrt Kc * Work.FTS.Nonlin.Xn α g
        ≤ (Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * Work.FTS.Nonlin.Xn α g := by
      have h1' : Real.sqrt Kc ≤ Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ ^ 2) + 1 := by
        have := Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        linarith
      exact mul_le_mul_of_nonneg_right h1' hX0
    calc |Work.Elliptic.DzdIter 0 (fun z => Work.Construction.L12 g z) z|
        = |Work.Construction.L12 g z| := rfl
      _ ≤ Real.sqrt Kc * Work.FTS.Nonlin.Xn α g := h1
      _ ≤ _ := h2
  · have hrec := (Work.FTS.Nonlinear.Pieces.L12_dzdIter_moment α hα hα1 hsm hmem h0).1
      (b - 1) (by omega) z hz
    have hbsucc : b = (b - 1) + 1 := by omega
    rw [hbsucc, hrec, abs_neg]
    have hq := Work.FTS.Nonlinear.Pieces.Qang_sq_le_const α hsm hmem hdec (i := b - 1)
      (by omega) hz
    have hq' : (Work.Elliptic.Qang g (b - 1) z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
      rw [hXs] at hq; exact hq
    have h1 : |Work.Elliptic.Qang g (b - 1) z|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.FTS.Nonlin.Xn α g := by
      have h := Real.sqrt_le_sqrt hq'
      rw [Real.sqrt_mul hKth0, Real.sqrt_sq_eq_abs, Real.sqrt_sq hX0] at h
      exact h
    have h2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.FTS.Nonlin.Xn α g
        ≤ (Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * Work.FTS.Nonlin.Xn α g := by
      have h1' : Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          ≤ Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 := by
        have := Real.sqrt_nonneg Kc
        linarith
      exact mul_le_mul_of_nonneg_right h1' hX0
    calc |Work.Elliptic.Qang g (b - 1) z| ≤ _ := h1
      _ ≤ _ := h2

/-- `D_θ^j` of a function of `z` alone vanishes for `j ≥ 1`. -/
theorem dthIter_rad_eq_zero (r : ℝ → ℝ) : ∀ j : ℕ, 1 ≤ j →
    Work.Spaces.DthIter j (fun z _ => r z) = 0 := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ j ih =>
      intro _hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        funext z θ
        simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
          Work.Spaces.pth, Pi.zero_apply, deriv_const]
        ring
      · rw [Work.Spaces.DthIter_succ, ih hjpos]
        funext z θ
        simp only [Pi.zero_apply, Work.Spaces.Dth, Work.Spaces.pth]
        rw [deriv_const]
        ring

/-- `D_z^b` of the zero function vanishes. -/
theorem dzIter_zero : ∀ b : ℕ, Work.Spaces.DzIter b (0 : ℝ → ℝ → ℝ) = 0 := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp only [Pi.zero_apply, Work.Spaces.Dz, Work.Spaces.pz, deriv_const]
      ring

/-- The radial `D_z`-iterates commute with multiplication by a constant. -/
theorem dzdIter_const_mul (b : ℕ) (c : ℝ) (r : ℝ → ℝ) :
    Work.Elliptic.DzdIter b (fun z => c * r z)
      = fun z => c * Work.Elliptic.DzdIter b r z := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Work.Elliptic.DzdIter_succ, ih, Work.Elliptic.DzdIter_succ]
      funext z
      show z * deriv (fun z' => c * Work.Elliptic.DzdIter b r z') z
        = c * (z * deriv (fun z' => Work.Elliptic.DzdIter b r z') z)
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
      ring

/-- Row 4 of the §8 table, in the primed vocabulary: the `ℋ⁴`-honesty and the pairing bound of
`N₀₄ᵇ = (3/(2α)) sin(2θ) L₁₂(g) ∂_θ g = ((3/(2α)) L₁₂(g)) · D_θ g`; the pairing uses the
`D_θ`-transport clause `N4Extra'.t4` with the `D`-sup coefficient `(3/(2α)) L₁₂(g)`. -/
theorem row4 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) ∧
        |IP α (Work.FTS.Nonlin.N04bF α g) g|
          ≤ K * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCi, hα₂pos⟩ := hN.pos
  obtain ⟨hCt, _⟩ := hE.pos
  obtain ⟨KL, hKLpos, hKLb⟩ := L12_dzdIter_abs_le
  refine ⟨Ct * 25 * (3 / 2) * KL + 1, by positivity, ?_⟩
  intro α g Φs Φg hctx
  have hα := hctx.hα
  have hα1 := hctx.hα1
  have hαα₂ := hctx.hαα₂
  have hgal := hctx.hg
  have hell := hctx.hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hreg6 : Work.FTS.Nonlin.RegQ α 6 g := hgal.reg
  have hreg5 : Work.FTS.Nonlin.RegQ α 5 g :=
    Work.FTS.LocDataExt.RegQ_mono (by norm_num) hreg6
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- the smoothness of the radial coefficient
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) :=
    smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  -- the coefficient `f = (3/(2α))·L₁₂(g)` as an `ℋ⁴`-function
  have hL12 := hN.l12H α hIoc g (Work.FTS.OpenPkg.HQo_of_RegQ hreg4) hgal.l12
  have hfMem : Work.Spaces.HkMem α 4 (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12.1
  have hfx0 : (0 : ℝ) ≤ 3 / (2 * α) := by positivity
  have hfXn : Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ (3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg hfx0]
    exact mul_le_mul_of_nonneg_left hL12.2 hfx0
  -- the pointwise (`D`-sup) bound on the coefficient: `WDMem 4` and `WDp`
  have hpt : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b j (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ|
        ≤ (3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g) := by
    intro b j hbj z θ hz hθ0 hθ1
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hmixed : Work.Spaces.mixed b 0
            (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ
          = (3 / (2 * α)) * Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z := by
        rw [Work.Spaces.mixed_zero_right, Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul]
        simp only [Work.Elliptic.DzIter_rad]
      rw [hmixed, abs_mul, abs_of_nonneg hfx0]
      exact mul_le_mul_of_nonneg_left
        (hKLb hα hα1 hreg6.1 hreg4.2.1
          (fun i hi θ' hθ' => by
            have h := hgal.decay.2 0 i (by omega) θ' hθ'
            simpa only [Work.Spaces.mixed_zero_right] using h)
          hgal.l12 b hbj z hz) hfx0
    · have hzero : Work.Spaces.mixed b j
          (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ = 0 := by
        have hd : Work.Spaces.DthIter j (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
            = 0 := by
          rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul,
            dthIter_rad_eq_zero (fun z => Work.Construction.L12 g z) j hj]
          funext z θ
          simp only [Pi.zero_apply]
          ring
        simp only [Work.Spaces.mixed, hd]
        rw [dzIter_zero b]
        simp only [Pi.zero_apply]
      rw [hzero, abs_zero]
      positivity
  have hWDmem : Work.FTS.VocabO.WDMem 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    fun b j hbj => ⟨(3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g),
      fun z θ hz hθ0 hθ1 => hpt b j hbj z θ hz hθ0 hθ1⟩
  have hWDp : Work.FTS.VocabO.WDp 4
        (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ 25 * ((3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g)) :=
    Work.FTS.OpenPkg.WDp_le_of_pointwise (α := α) (by positivity) hpt
  -- the `ℋ⁴`-honesty of the piece, by the product rule with `D_θ g`
  have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
    Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α 4 (by linarith) hreg5
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) :=
    (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hreg6.1).Dth
  have hprod := hN.prod α hIoc (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
    (Work.Spaces.Dth g) ⟨smoothOpen_const_mul (3 / (2 * α)) hL12sm, hfMem⟩ ⟨hDthSm, hDthMem⟩
  have hid : Work.FTS.Nonlin.N04bF α g
      = fun z θ => (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ
          * Work.Spaces.Dth g z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.Ftot,
      Work.Construction.Fstar, Work.Spaces.Dth, Work.Spaces.pth, Work.Construction.s2,
      Work.FTS.Nonlin.PhiTg]
    ring
  rw [hid]
  refine ⟨hprod.1, ?_⟩
  -- the pairing bound
  have ht4 := hE.t4 α hIoc (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) g
    hWDmem hreg4
  refine ht4.trans ?_
  have hrp : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hb1 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  have hXg3 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g ^ 2 := by positivity
  calc Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4
          (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
        * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (25 * ((3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g)))
        * Work.FTS.Nonlin.Xn α g ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDp ?_) hXg3
        exact mul_nonneg hCt.le hrp
    _ = Ct * 25 * (3 / 2) * KL * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
        have hpow : α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 : ℝ)) = α ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hα]
          norm_num
        have hinv : (3 : ℝ) / (2 * α) = (3 / 2) * α ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one]
          field_simp
        rw [hinv]
        linear_combination (Ct * 25 * (3 / 2) * KL * Work.FTS.Nonlin.Xn α g ^ 3) * hpow
    _ ≤ (Ct * 25 * (3 / 2) * KL + 1)
          * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
        refine mul_le_mul_of_nonneg_right ?_ hb1
        linarith [hCt, hKLpos]

end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular factor: `∂_θ c2m(θ) = -3 sin 2θ` and its `D_θ`-iterates -/

/-- `∂_θ c2m = -3 sin(2θ)`, where `c2m θ = cos 2θ - sin²θ`. -/
private theorem hasDerivAt_c2m (θ : ℝ) :
    HasDerivAt (fun θ' => Work.Construction.c2m θ') (-3 * Real.sin (2 * θ)) θ := by
  have hfun : (fun θ' : ℝ => Work.Construction.c2m θ')
      = fun θ' => Real.cos (2 * θ') - Real.sin θ' * Real.sin θ' := by
    funext θ'; rw [Work.Construction.c2m_eq]; ring
  have h : HasDerivAt (fun θ' : ℝ => Work.Construction.c2m θ')
      (-(Real.sin (2 * θ) * 2) - (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(Real.sin (2 * θ) * 2)) θ := by
      have h := (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.sin θ')
        (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ) θ :=
      (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_sin θ)
    have h3 := h1.sub h2
    rw [hfun]
    exact h3
  have hval : -(Real.sin (2 * θ) * 2) - (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ)
      = -3 * Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; ring
  rw [← hval]
  exact h

/-- `∂_θ c2m = -3 sin(2θ)`. -/
private theorem deriv_c2m (θ : ℝ) :
    deriv (fun θ' => Work.Construction.c2m θ') θ = -3 * Real.sin (2 * θ) :=
  (hasDerivAt_c2m θ).deriv

/-- `∂_θ (c2m(θ)·r(z)) = (∂_θ c2m)(θ)·r(z)`. -/
private theorem pth_c2m_mul_rad (r : ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => Work.Construction.c2m θ * r z)
      = fun z θ => deriv (fun θ' => Work.Construction.c2m θ') θ * r z := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_mul_const (hasDerivAt_c2m θ).differentiableAt (r z)]

/-- The mixed derivatives of `∂_θ(c2m(θ)·r(z))` separate into an angular and a radial factor. -/
private theorem mixed_pth_c2m_mul_rad (r : ℝ → ℝ) (b i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed b i (Work.Spaces.pth (fun z θ => Work.Construction.c2m θ * r z)) z θ
      = Work.Spaces.DthIter i (fun _ θ' =>
            deriv (fun θ'' => Work.Construction.c2m θ'') θ') 0 θ * Work.Elliptic.DzdIter b r z := by
  rw [pth_c2m_mul_rad r]
  exact Work.FTS.Nonlinear.Pieces.mixed_ang_rad
    (fun θ => deriv (fun θ'' => Work.Construction.c2m θ'') θ) r b i z θ

/-- `|D_θ^i (∂_θ c2m)| ≤ 144` on `Iθ`, for `i ≤ 3`. -/
private theorem dthIter_deriv_c2m_le (i : ℕ) (hi : i ≤ 3) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' =>
        deriv (fun θ'' => Work.Construction.c2m θ'') θ') 0 θ| ≤ 144 := by
  have hfun : (fun _ θ' : ℝ => deriv (fun θ'' => Work.Construction.c2m θ'') θ')
      = (fun z θ => (-3) * (fun _ θ' : ℝ => Real.sin (2 * θ')) z θ) := by
    funext z θ'
    rw [deriv_c2m]
  rw [hfun, Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul]
  rw [abs_mul, show |(-3 : ℝ)| = 3 from by norm_num]
  have hS : (fun _ θ' : ℝ => Real.sin (2 * θ')) = Work.FTS.H2.Sfun := rfl
  rw [hS]
  have hb := Work.FTS.H2.abs_DthIter_Sfun_le i (by omega) (0 : ℝ) hθ
  have hAs0 : 0 ≤ Work.FTS.H2.Asin i := (Work.FTS.H2.Asin_pos i).le
  have hAs : Work.FTS.H2.Asin i ≤ 48 := Work.FTS.H2.Asin_le i hi
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : Work.FTS.H2.Asin i * Real.sin (2 * θ) ≤ 48 :=
    calc Work.FTS.H2.Asin i * Real.sin (2 * θ) ≤ 48 * 1 :=
          mul_le_mul hAs hsin1 hsin0 (by norm_num)
      _ = 48 := by norm_num
  have h2 : |Work.Spaces.DthIter i Work.FTS.H2.Sfun 0 θ| ≤ 48 := le_trans hb h1
  linarith

/-! ## The radial factor: `D_z`-iterates of `L₁₂(F_*) = 2α/(1+z)` -/

/-- The plain `z`-iterates of a radial function. -/
private theorem pzIter_radial (r : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => r z) z θ = deriv^[k] r z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      have hfun : (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) = deriv^[k] r :=
        funext fun z' => ih z'
      show deriv (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) z = deriv^[k + 1] r z
      rw [hfun, Function.iterate_succ_apply']

/-- `D_z` commutes with equality on the open half-line `(-1,∞)`. -/
private theorem DzdIter_congr_Ioi {u v : ℝ → ℝ} (h : ∀ z ∈ Set.Ioi (-1), u z = v z) :
    ∀ (b : ℕ) (z : ℝ), z ∈ Set.Ioi (-1) →
      Work.Elliptic.DzdIter b u z = Work.Elliptic.DzdIter b v z := by
  intro b
  induction b with
  | zero => intro z hz; exact h z hz
  | succ b ih =>
      intro z hz
      have hev : Work.Elliptic.DzdIter b u =ᶠ[𝓝 z] Work.Elliptic.DzdIter b v :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun y hy => ih y hy)
      show z * deriv (Work.Elliptic.DzdIter b u) z
        = z * deriv (Work.Elliptic.DzdIter b v) z
      rw [hev.deriv_eq]

/-- `2α/(1+z)` is `C^∞` (indeed analytic) on `(-1,∞)`. -/
private theorem contDiffOn_invH (α : ℝ) :
    ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi (-1)) := by
  have h : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi (-1)) := by
    refine ContDiffOn.inv ?_ ?_
    · have h : ContDiffOn ℝ ⊤ (fun z : ℝ => 1 + z) (Set.Ioi (-1)) := by fun_prop
      exact h
    · intro z hz; simp only [Set.mem_Ioi] at hz; linarith
  have h2 : ContDiffOn ℝ ⊤ (fun z : ℝ => (2 * α) * ((1 + z)⁻¹)) (Set.Ioi (-1)) :=
    ContDiffOn.mul contDiffOn_const h
  refine h2.congr ?_
  intro z _
  simp only [div_eq_mul_inv]

/-- `|z^j ∂_z^j (2α/(1+z))| ≤ 48α` for `j ≤ 4` on `[0,∞)`. -/
private theorem pzIter_invH_bound (α : ℝ) (hα : 0 < α) (j : ℕ) (hj : j ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j (fun z _ => 2 * α / (1 + z)) z θ| ≤ 48 * α := by
  intro z hzIz θ _
  have hz0 : (0 : ℝ) ≤ z := hzIz
  rw [pzIter_radial (fun z => 2 * α / (1 + z)) j z θ]
  rw [show (fun z : ℝ => 2 * α / (1 + z)) = fun z => (2 * α) * (1 + z)⁻¹ from by
    funext z; rw [div_eq_mul_inv]]
  have hderiv : deriv^[j] (fun z : ℝ => (2 * α) * (1 + z)⁻¹) z
      = (2 * α) * deriv^[j] (fun z : ℝ => (1 + z)⁻¹) z := by
    rw [Work.FTS.Nonlinear.FstarPkg.deriv_iter_const_mul]
  rw [hderiv, Work.FTS.Nonlinear.FstarPkg.iter_deriv_nInvClosed j z (by linarith)]
  have hkey : z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| ≤ (j.factorial : ℝ) := by
    have h1 := Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted j z hz0
    have h2 : z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|
        ≤ (z + 1) ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 (by linarith) j) (abs_nonneg _)
    have h3 : (z + 1) ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|
        = |(z + 1) ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) j)]
    rw [h3] at h2
    linarith
  have hfact : (j.factorial : ℝ) ≤ 24 := by
    interval_cases j <;> norm_num
  have hα2 : (0 : ℝ) < 2 * α := by linarith
  have hgoal : |z ^ j * ((2 * α) * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z)|
      = (2 * α) * (z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|) := by
    have h1 : |(2 : ℝ) * α| = 2 * α := abs_of_nonneg hα2.le
    have h2 : |z ^ j| = z ^ j := abs_of_nonneg (pow_nonneg hz0 j)
    rw [show z ^ j * ((2 * α) * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z)
        = (2 * α) * (z ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z) from by ring]
    simp only [abs_mul, h1, h2]
  rw [hgoal]
  calc (2 * α) * (z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|)
      ≤ (2 * α) * (j.factorial : ℝ) := mul_le_mul_of_nonneg_left hkey hα2.le
    _ ≤ (2 * α) * 24 := mul_le_mul_of_nonneg_left hfact hα2.le
    _ = 48 * α := by ring

/-- `|D_z^b (L₁₂(F_*)) z| ≤ 4800α` for `b ≤ 4`, `z > 0`. -/
private theorem DzdIter_L12Fstar_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (b : ℕ) (hb : b ≤ 4)
    {z : ℝ} (hz : 0 < z) :
    |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z|
      ≤ 4800 * α := by
  have hz1 : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  rw [DzdIter_congr_Ioi (u := fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
    (v := fun z => 2 * α / (1 + z))
    (fun y hy => Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hy) b z hz1]
  have hθ0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hmain := Work.Spaces.DzIter_le_of_pzIter (h := fun z _ => 2 * α / (1 + z))
    (M := 48 * α) (by positivity)
    (fun θ _ => contDiffOn_invH α)
    (fun j hj z hzIz θ hθ => pzIter_invH_bound α hα j hj z hzIz θ hθ)
    b hb z (le_of_lt hz) 0 hθ0
  have hrew : |Work.Spaces.DzIter b (fun z _ => 2 * α / (1 + z)) z 0|
      = |Work.Elliptic.DzdIter b (fun z => 2 * α / (1 + z)) z| := by
    rw [Work.Elliptic.DzIter_rad (fun z => 2 * α / (1 + z)) b z 0]
  rw [hrew] at hmain
  rw [show (100 : ℝ) * (48 * α) = 4800 * α from by ring] at hmain
  exact hmain

/-! ## The flat angular norm of the row-7 coefficient -/

/-- The per-slot bound behind `CoefThMem 3` for `f = c2m(θ)·L₁₂(F_*)(z)`. -/
private theorem coefTh_slot_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (b i : ℕ) (hbi : b + i ≤ 3) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b i (Work.Spaces.pth (fun z θ => Work.Construction.c2m θ *
        Work.Construction.L12 (Work.Construction.Fstar α) z)) z θ| ≤ 144 * (4800 * α) := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hi3 : i ≤ 3 := by omega
  have hb4 : b ≤ 4 := by omega
  rw [mixed_pth_c2m_mul_rad (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
    b i z θ]
  rw [abs_mul]
  exact mul_le_mul (dthIter_deriv_c2m_le i hi3 θ hθ)
    (DzdIter_L12Fstar_le α hα hα1 b hb4 hz) (abs_nonneg _) (by positivity)

/-- `CoefThMem 3` for `f = c2m(θ)·L₁₂(F_*)(z)`. -/
private theorem coefThMem_c2mL12 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.VocabO.CoefThMem 3 (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z) :=
  fun b i hbi => ⟨144 * (4800 * α), coefTh_slot_le α hα hα1 b i hbi⟩

/-- `CoefTh 3 f ≤ 16·144·4800·α = 11059200·α` for `f = c2m(θ)·L₁₂(F_*)(z)`. -/
private theorem coefTh_c2mL12_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.VocabO.CoefTh 3 (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ 11059200 * α := by
  have hconst : ∀ c : ℝ, (∑ _b ∈ Finset.range 4, ∑ _i ∈ Finset.range 4, c) = 16 * c := by
    intro c
    simp [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    ring
  rw [Work.FTS.VocabO.CoefTh]
  calc (∑ b ∈ Finset.range (3 + 1), ∑ i ∈ Finset.range (3 + 1),
        if b + i ≤ 3 then Work.FTS.H2.supAbsO
          (Work.Spaces.mixed b i (Work.Spaces.pth (fun z θ => Work.Construction.c2m θ *
            Work.Construction.L12 (Work.Construction.Fstar α) z))) else 0)
      ≤ ∑ _b ∈ Finset.range 4, ∑ _i ∈ Finset.range 4, (144 * (4800 * α)) := by
        refine Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun i hi => ?_
        by_cases hc : b + i ≤ 3
        · rw [if_pos hc]
          exact Work.FTS.H2.supAbsO_le (coefTh_slot_le α hα hα1 b i hc)
        · rw [if_neg hc]
          positivity
    _ = 11059200 * α := by
        rw [hconst]
        ring

/-! ## Smoothness of the coefficient -/

/-- `SmoothOpen` of the row-7 coefficient `c2m(θ)·L₁₂(F_*)(z)` (written as the explicit
separated product `c2m(θ)·2α/(1+z)` on the open quadrant). -/
private theorem smoothOpen_c2mL12 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  have hexp : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      ((fun p : ℝ × ℝ => Work.Construction.c2m p.2) *
        (fun p : ℝ × ℝ => 2 * α / (1 + p.1))) Work.FTS.EllipticEst.Q0
    refine ContDiffOn.mul ?_ ?_
    · have hc : ContDiff ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Work.Construction.c2m θ) := by
        rw [show (fun θ : ℝ => Work.Construction.c2m θ)
            = fun θ => Real.cos (2 * θ) - Real.sin θ ^ 2 from by
              funext θ; rw [Work.Construction.c2m_eq]]
        fun_prop
      exact hc.comp_contDiffOn contDiffOn_snd
    · have hden : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => 1 + p.1) Work.FTS.EllipticEst.Q0 := by fun_prop
      have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, 1 + p.1 ≠ 0 := by
        intro p hp
        have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
        linarith
      have hinv := hden.inv hne
      have hmul : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => (2 * α) * (1 + p.1)⁻¹) Work.FTS.EllipticEst.Q0 :=
        ContDiffOn.mul contDiffOn_const hinv
      refine hmul.congr ?_
      intro p _
      simp only [div_eq_mul_inv]
  refine ContDiffOn.congr hexp ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 (by linarith)]


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row23 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

set_option linter.unusedVariables false

/-! ## Smoothness of a radial factor and of the angular profile `dthU Γ`

The two facts used to feed the `ℋ⁴`-honesty of `N₄^{**} = a(θ)·r(z)` into the angular `×` radial
product lemma. -/

/-- A radial function smooth on `(0,∞)` gives a `SmoothOpen` function of `z` alone. -/
theorem row23_smoothOpen_radial {r : ℝ → ℝ}
    (hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => r z) (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  exact (hr n).comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C^∞` on the open quadrant. -/
theorem row23_smoothOpen_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.Gam α θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hbase : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2) Work.FTS.EllipticEst.Q0 :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hp'.2.1, Real.pi_pos]) (by linarith [hp'.2.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp'.2.1, Real.pi_pos], hp'.2.2⟩
    positivity
  exact hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

/-- The angular profile `dthU Γ = sin(2θ)·Γ'` is `C^∞` on the open quadrant. -/
theorem row23_smoothOpen_dthU_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ) := by
  have h : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (fun _ (θ : ℝ) => Work.Spaces.Gam α θ)) :=
    (row23_smoothOpen_Gam α).Dth
  refine h.congr (fun p _ => ?_)
  simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.dthU_apply, Function.uncurry]

/-- `hKer z = z/(1+z)²` is `C^∞` on `(0,∞)`. -/
theorem row23_contDiffOn_hKer :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
  intro n
  have h : ContDiffOn ℝ n (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) :=
    contDiffOn_id.div ((contDiffOn_const.add contDiffOn_id).pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt (by linarith [Set.mem_Ioi.mp hz])))
  simpa only [Work.Spaces.hKer_apply] using h


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

/-- `V₀(θ) = V(Φ̃_*)(0,θ)`: the value of the coefficient at `z = 0`. -/
abbrev Vs0 (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ := fun θ => Vs α Φs 0 θ

/-- `V₀` viewed as a function of `(z,θ)`: constant in `z`. -/
abbrev Vs0f (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ := fun _ θ => Vs0 α Φs θ

/-- `W = V(Φ̃_*) - V₀`: the part of the coefficient that vanishes at `z = 0`. -/
abbrev VsW (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Vs α Φs z θ - Vs0 α Φs θ

@[simp] theorem Vs0f_apply (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    Vs0f α Φs z θ = Vs α Φs 0 θ := rfl

@[simp] theorem VsW_apply (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    VsW α Φs z θ = Vs α Φs z θ - Vs0 α Φs θ := rfl


/-- `W` vanishes at `z = 0`. -/
@[simp] theorem VsW_zero (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (θ : ℝ) :
    VsW α Φs 0 θ = 0 := by
  simp only [VsW_apply, sub_self]

/-! ## Smoothness -/

/-- `V₀` is `C^∞` on the half strip (it is the `z = 0` slice of `V`). -/
theorem contDiffOn_Vs0f {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Vs0f α Φs))
      (Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hV := Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Vs α Φs 0 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hV.curry_θ (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num)
  have hfun : Function.uncurry (Vs0f α Φs) = fun p : ℝ × ℝ => Vs α Φs 0 p.2 := rfl
  rw [hfun]
  exact hslice.comp contDiff_snd.contDiffOn (fun p hp => hp.2)

/-- `W = V - V₀` is `C^∞` on the half strip (`SmoothQuad`). -/
theorem smoothQuad_VsW {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.LocData.SmoothQuad (VsW α Φs) := by
  have hV := Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have h0 : Work.FTS.LocData.SmoothQuad (Vs0f α Φs) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry (contDiffOn_Vs0f hα hs)
  have hsub := Work.FTS.LocData.smoothQuad_sub hV h0
  refine hsub.congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- The `z`-slices of the `D_θ`-iterates of a `SmoothQuad` function are differentiable. -/
theorem differentiableAt_slice_DthIter_z {G : ℝ → ℝ → ℝ} (hG : Work.FTS.LocData.SmoothQuad G)
    (i : ℕ) {z : ℝ} (hz : -1 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.DthIter i G z' θ) z := by
  have h := hG.differentiableAt_slice_mixed 0 i hz hθ
  simpa only [Work.Spaces.mixed_zero_left] using h

/-! ## Identities: the iterated derivatives of `W` against those of `V` -/

/-- Iterated `∂_z` of a function minus a constant is the iterated `∂_z` of the function. -/
theorem iter_deriv_sub_const (a : ℕ) (ha : 1 ≤ a) (f : ℝ → ℝ) (c : ℝ) :
    deriv^[a] (fun x => f x - c) = deriv^[a] f := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      funext x
      simpa using deriv_sub_const (f := f) (x := x) c
    · have hprev : deriv^[n] (fun x => f x - c) = deriv^[n] f := ih (by omega)
      funext x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hprev]

/-- `pzIter a f z θ` is the `a`-th plain `z`-derivative of the `z`-slice. -/
theorem pzIter_eq_iter_deriv (a : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter a f z θ = deriv^[a] (fun t => f t θ) z := by
  induction a generalizing z with
  | zero => simp
  | succ n ih =>
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    rw [show (fun z' => Work.Spaces.pzIter n f z' θ) = deriv^[n] (fun t => f t θ) from
      funext (fun z' => ih z')]
    exact congrFun (Function.iterate_succ_apply' deriv n (fun t => f t θ)).symm z

/-- For `a ≥ 1` the `z`-derivatives of `W` and of `V` agree (a constant is subtracted). -/
theorem pzIter_VsW_eq (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (a : ℕ) (ha : 1 ≤ a) (z θ : ℝ) :
    Work.Spaces.pzIter a (VsW α Φs) z θ = Work.Spaces.pzIter a (Vs α Φs) z θ := by
  rw [pzIter_eq_iter_deriv, pzIter_eq_iter_deriv]
  have hfun : (fun t : ℝ => VsW α Φs t θ) = fun t => Vs α Φs t θ - Vs0 α Φs θ := by
    funext t
    simp only [VsW_apply]
  rw [hfun, iter_deriv_sub_const a ha]


/-- `D_θ^i W(z,θ) = D_θ^i V(z,θ) - D_θ^i V(0,θ)` on the open quadrant. -/
theorem DthIter_VsW_eq {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (VsW α Φs) z θ
        = Work.Spaces.DthIter i (Vs α Φs) z θ - Work.Spaces.DthIter i (Vs α Φs) 0 θ := by
  have hsq : Work.FTS.LocData.SmoothQuad (Vs α Φs) :=
    Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  induction i with
  | zero => intro z θ _ _ _; simp only [Work.Spaces.DthIter_zero]
  | succ n ih =>
    intro z θ hz h1 h2
    have heq : (fun θ' => Work.Spaces.DthIter n (VsW α Φs) z θ')
        =ᶠ[𝓝 θ] fun θ' => Work.Spaces.DthIter n (Vs α Φs) z θ'
            - Work.Spaces.DthIter n (Vs α Φs) 0 θ' := by
      filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨h1, h2⟩)]
        with θ' hθ'
      exact ih z θ' hz hθ'.1 hθ'.2
    have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n (Vs α Φs) z θ') θ :=
      hsq.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
    have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n (Vs α Φs) 0 θ') θ :=
      hsq.differentiableAt_slice_DthIter n (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num) ⟨h1, h2⟩
    have hd : deriv (fun θ' => Work.Spaces.DthIter n (Vs α Φs) z θ'
          - Work.Spaces.DthIter n (Vs α Φs) 0 θ') θ
        = deriv (fun θ' => Work.Spaces.DthIter n (Vs α Φs) z θ') θ
          - deriv (fun θ' => Work.Spaces.DthIter n (Vs α Φs) 0 θ') θ :=
      deriv_sub hd1 hd2
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [heq.deriv_eq, hd]
    ring

/-- The angular derivatives of `W` vanish at `z = 0`. -/
theorem DthIter_VsW_zero (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (i : ℕ) (θ : ℝ) :
    Work.Spaces.DthIter i (VsW α Φs) 0 θ = 0 := by
  induction i generalizing θ with
  | zero => simp
  | succ i ih =>
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    have h0 : (fun θ' : ℝ => Work.Spaces.DthIter i (VsW α Φs) 0 θ')
        = fun _ : ℝ => (0 : ℝ) := funext (fun θ' => ih θ')
    rw [h0]
    simp

/-- Iterated `deriv` respects eventual equality. -/
theorem eventuallyEq_iter_deriv {f g : ℝ → ℝ} {z : ℝ} (h : f =ᶠ[𝓝 z] g) :
    ∀ a : ℕ, deriv^[a] f =ᶠ[𝓝 z] deriv^[a] g
  | 0 => by simpa using h
  | a + 1 => by
    have h' : deriv^[a] f =ᶠ[𝓝 z] deriv^[a] g := eventuallyEq_iter_deriv h a
    have h'' : deriv (deriv^[a] f) =ᶠ[𝓝 z] deriv (deriv^[a] g) := h'.deriv
    have e1 : deriv^[a + 1] f = deriv (deriv^[a] f) :=
      Function.iterate_succ_apply' deriv a f
    have e2 : deriv^[a + 1] g = deriv (deriv^[a] g) :=
      Function.iterate_succ_apply' deriv a g
    rw [e1, e2]
    exact h''

/-- `deriv^[a]` is a local operation: functions agreeing near the point have equal iterated
derivatives there. -/
theorem iter_deriv_congr_of_eventuallyEq {f g : ℝ → ℝ} {z : ℝ} (h : f =ᶠ[𝓝 z] g) (a : ℕ) :
    deriv^[a] f z = deriv^[a] g z :=
  (eventuallyEq_iter_deriv h a).eq_of_nhds

/-- For `a ≥ 1` and `z > -1` the `z`-derivatives of `D_θ^i W` and of `D_θ^i V` agree. -/
theorem pzIter_DthIter_VsW_eq {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) (i a : ℕ) (ha : 1 ≤ a) {z θ : ℝ}
    (hz : -1 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter a (fun z θ => Work.Spaces.DthIter i (VsW α Φs) z θ) z θ
      = Work.Spaces.pzIter a (fun z θ => Work.Spaces.DthIter i (Vs α Φs) z θ) z θ := by
  rw [pzIter_eq_iter_deriv, pzIter_eq_iter_deriv]
  have h1 : deriv^[a] (fun t : ℝ => Work.Spaces.DthIter i (VsW α Φs) t θ) z
      = deriv^[a] (fun t : ℝ => Work.Spaces.DthIter i (Vs α Φs) t θ
          - Work.Spaces.DthIter i (Vs α Φs) 0 θ) z := by
    refine iter_deriv_congr_of_eventuallyEq ?_ a
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    exact DthIter_VsW_eq hα hs i t θ ht hθ.1 hθ.2
  rw [h1]
  exact congrFun (iter_deriv_sub_const a ha (fun t : ℝ => Work.Spaces.DthIter i (Vs α Φs) t θ)
    (Work.Spaces.DthIter i (Vs α Φs) 0 θ)) z

/-- The Lipschitz bound of `Vs_lipschitz`, in the form used by the row. -/
theorem abs_VsW_le_lip {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |VsW α Φs z θ| ≤ max Cs 0 * α * z := by
  intro z hz θ hθ
  have h := Vs_lipschitz (α := α) (Cs := Cs) (Φs := Φs) hα hs z hz θ hθ
  simpa only [VsW_apply, Vs0] using h

/-- The global bound `|W| ≤ 2 max Cs 0 · α`. -/
theorem abs_VsW_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |VsW α Φs z θ| ≤ 2 * (max Cs 0 * α) := by
  intro z hz θ hθ
  have h1 := Work.FTS.Nonlinear.Pieces.RNP.abs_Vs_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have h2 := h1 z hz θ hθ
  have h3 := h1 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ))) θ hθ
  have h4 : |VsW α Φs z θ|
      ≤ |Vs α Φs z θ| + |Vs0 α Φs θ| := by
    simp only [VsW_apply, Vs0]
    exact abs_sub _ _
  linarith

/-- `|W(z,θ)| ≤ 2 max Cs 0 · α · min z 1` on the open angular interval: the Lipschitz
bound together with global boundedness. -/
theorem abs_VsW_le_min {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |VsW α Φs z θ| ≤ 2 * (max Cs 0 * α) * min z 1 := by
  intro z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hz0 : 0 ≤ z := hz
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have h1 : |VsW α Φs z θ| ≤ max Cs 0 * α * z := by
    rcases eq_or_lt_of_le hz0 with h | h
    · rw [← h, VsW_zero]; simp
    · exact abs_VsW_le_lip hα hs z hz θ hθ
  have h2 : |VsW α Φs z θ| ≤ 2 * (max Cs 0 * α) := abs_VsW_le hα hs z hz θ hθI
  rcases le_total z 1 with hz1 | hz1
  · rw [min_eq_left hz1]
    nlinarith
  · rw [min_eq_right hz1]
    nlinarith
/-- The angular weight of every angular bound of this file is nonnegative on the open
angular interval. -/
theorem angular_weight_nonneg {α θ : ℝ} (hα : 0 < α)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have h2θ : (2 * θ) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact mul_nonneg (by linarith [Real.sin_nonneg_of_mem_Icc h2θ, hα])
    (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc h2θ) _)

/-- **The weighted `z`-derivative bounds of `W`**: `|z^a ∂_z^a W| ≤ 2 max Cs 0 α · min z 1`
for `a ≤ 4` on the open angular interval. -/
theorem abs_zpow_pzIter_VsW_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ a : ℕ, a ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |z ^ a * Work.Spaces.pzIter a (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α) * min z 1 := by
  intro a ha z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  rcases Nat.eq_zero_or_pos a with h0 | hapos
  · subst h0
    simpa using abs_VsW_le_min (α := α) (Cs := Cs) (Φs := Φs) hα hs z hz θ hθ
  · have hder : Work.Spaces.pzIter a (VsW α Φs) z θ
        = Work.Spaces.pzIter a (Vs α Φs) z θ := pzIter_VsW_eq α Φs a hapos z θ
    rw [hder, abs_mul, abs_of_nonneg (pow_nonneg hz a)]
    have hz0 : 0 ≤ z := hz
    have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
    have hle : Work.Spaces.WlInf α 4 (Vs α Φs) ≤ max Cs 0 * α :=
      le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
    have hzp : (0 : ℝ) < z + 1 := by linarith
    have hw := Work.Spaces.WlInf_z_bound α 4 (Vs α Φs) hs.V.1 a ha z θ hz hθI
    have hw' : (z + 1) ^ a * |Work.Spaces.pzIter a (Vs α Φs) z θ| ≤ max Cs 0 * α := by
      rw [abs_mul, abs_of_nonneg (le_of_lt (pow_pos hzp a))] at hw
      exact le_trans hw hle
    have hratio : z / (z + 1) ≤ min z 1 := by
      rcases le_total z 1 with h | h
      · rw [min_eq_left h, div_le_iff₀ hzp]; nlinarith
      · rw [min_eq_right h, div_le_one hzp]; linarith
    have hratio0 : 0 ≤ z / (z + 1) := div_nonneg hz0 (le_of_lt hzp)
    have hratio1 : z / (z + 1) ≤ 1 := by rw [div_le_one hzp]; linarith
    have hmin0 : 0 ≤ min z 1 := le_min hz0 zero_le_one
    have hpowle : (z / (z + 1)) ^ a ≤ min z 1 :=
      calc (z / (z + 1)) ^ a ≤ (z / (z + 1)) ^ 1 :=
            pow_le_pow_of_le_one hratio0 hratio1 hapos
        _ = z / (z + 1) := pow_one _
        _ ≤ min z 1 := hratio
    have hsplit : z ^ a * |Work.Spaces.pzIter a (Vs α Φs) z θ|
        = (z / (z + 1)) ^ a * ((z + 1) ^ a * |Work.Spaces.pzIter a (Vs α Φs) z θ|) := by
      rw [div_pow]
      field_simp
    rw [hsplit]
    calc (z / (z + 1)) ^ a * ((z + 1) ^ a * |Work.Spaces.pzIter a (Vs α Φs) z θ|)
        ≤ min z 1 * (max Cs 0 * α) :=
          mul_le_mul hpowle hw' (mul_nonneg (by positivity) (abs_nonneg _)) hmin0
      _ ≤ 2 * (max Cs 0 * α) * min z 1 := by nlinarith

/-- **The angular-derivative bounds of `W`**, first form: `|D_θ^i W| ≤ 2 max Cs 0 α ·
(α + sin 2θ) sin(2θ)^{α/5}` for `1 ≤ i ≤ 4`, on the closed domain. -/
theorem abs_DthIter_VsW_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  intro i hi1 hi4 z hz θ hθ
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hle : Work.Spaces.WlInf α 4 (Vs α Φs) ≤ max Cs 0 * α :=
    le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  have hθ0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have harg : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hθ0 _)
  have key : ∀ z' ∈ Work.Spaces.Iz,
      |Work.Spaces.DthIter (j + 1) (Vs α Φs) z' θ|
        ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    intro z' hz'
    have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Vs α Φs) hs.V.1 (j + 1) 0 (by omega)
      (by omega) z' θ hz' hθ
    simp only [Work.Spaces.pzIter_zero, pow_zero, div_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hle harg)
  rcases eq_or_lt_of_le hθ.1 with hθzero | hθpos
  · rw [← hθzero, Work.Spaces.DthIter_apply_zero (VsW α Φs) j z, abs_zero]
    have hsin : Real.sin (2 * (0 : ℝ)) = 0 := by simp
    rw [hsin, Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < α / 5)), mul_zero, mul_zero]
  rcases eq_or_lt_of_le hθ.2 with hθpi | hθlt
  · rw [hθpi, Work.Spaces.DthIter_apply_pi_half (VsW α Φs) j z, abs_zero]
    have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
    rw [hsin, Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < α / 5)), mul_zero, mul_zero]
  have hz0' : (0 : ℝ) ≤ z := hz
  have hid := DthIter_VsW_eq hα hs (j + 1) z θ (by linarith) hθpos hθlt
  rw [hid]
  refine le_trans (abs_sub_le (Work.Spaces.DthIter (j + 1) (Vs α Φs) z θ) 0
    (Work.Spaces.DthIter (j + 1) (Vs α Φs) 0 θ)) ?_
  rw [sub_zero, zero_sub, abs_neg]
  have h1 := key z hz
  have h2 := key 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
  linarith

/-- **The angular-derivative bounds of `W`**, with the `z`-vanishing, for `i ≤ 3`. -/
theorem abs_DthIter_VsW_le_min {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DthIter i (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
  intro i hi1 hi3 z hz θ hθ
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hsq : Work.FTS.LocData.SmoothQuad (Vs α Φs) :=
    Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have harg : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    angular_weight_nonneg hα hθ
  have hle : Work.Spaces.WlInf α 4 (Vs α Φs) ≤ max Cs 0 * α :=
    le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  have hz0 : 0 ≤ z := hz
  have hglobal := abs_DthIter_VsW_le (α := α) (Cs := Cs) (Φs := Φs) hα hs (j + 1) (by omega)
    (by omega) z hz θ hθI
  -- the mean value theorem in `z` on `[0,z]`
  have hmvt : |Work.Spaces.DthIter (j + 1) (VsW α Φs) z θ|
      ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * z := by
    rcases eq_or_lt_of_le hz0 with h0 | hpos
    · rw [← h0, DthIter_VsW_zero α Φs (j + 1) θ, abs_zero]
      nlinarith [mul_nonneg hM0 harg]
    · have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) z,
          DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.DthIter (j + 1) (Vs α Φs) t θ) x := by
        intro x hx
        exact differentiableAt_slice_DthIter_z hsq (j + 1) (by linarith [hx.1]) hθ
      have hbdd : ∀ x ∈ Set.Icc (0 : ℝ) z,
          ‖deriv (fun t : ℝ => Work.Spaces.DthIter (j + 1) (Vs α Φs) t θ) x‖
            ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
        intro x hx
        have hxI : x ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hx.1
        have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Vs α Φs) hs.V.1 (j + 1) 1 (by omega)
          (by omega) x θ hxI hθI
        rw [show Work.Spaces.pzIter 1 (Work.Spaces.DthIter (j + 1) (Vs α Φs)) x θ
            = deriv (fun t : ℝ => Work.Spaces.DthIter (j + 1) (Vs α Φs) t θ) x from rfl] at h
        rw [Real.norm_eq_abs]
        refine le_trans h ?_
        have hx1 : (0 : ℝ) < x + 1 := by linarith [hx.1]
        have hdiv : ((x + 1 : ℝ))⁻¹ ≤ 1 := by
          rw [inv_le_one₀ hx1]; linarith [hx.1]
        calc Work.Spaces.WlInf α 4 (Vs α Φs) / (x + 1) ^ 1
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            = (Work.Spaces.WlInf α 4 (Vs α Φs) * (x + 1)⁻¹)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
              rw [pow_one, div_eq_mul_inv]
          _ ≤ (max Cs 0 * α) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
              refine mul_le_mul_of_nonneg_right ?_ harg
              calc Work.Spaces.WlInf α 4 (Vs α Φs) * (x + 1)⁻¹
                  ≤ (max Cs 0 * α) * (x + 1)⁻¹ := mul_le_mul_of_nonneg_right hle (by positivity)
                _ ≤ (max Cs 0 * α) * 1 := mul_le_mul_of_nonneg_left hdiv hM0
                _ = max Cs 0 * α := mul_one _
      have hmain := (convex_Icc (0 : ℝ) z).norm_image_sub_le_of_norm_deriv_le hdiff hbdd
        (left_mem_Icc.mpr hz0) (right_mem_Icc.mpr hz0)
      rw [Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg hpos.le] at hmain
      have hid := DthIter_VsW_eq hα hs (j + 1) z θ (by linarith) hθ.1 hθ.2
      rw [hid]
      exact hmain
  rcases le_total z 1 with hz1 | hz1
  · rw [min_eq_left hz1]
    nlinarith [hmvt, hglobal, mul_nonneg (mul_nonneg hM0 harg) hz0]
  · rw [min_eq_right hz1]
    nlinarith [hmvt, hglobal, mul_nonneg hM0 harg]

/-- **The mixed bounds of `W`**: `|z^a ∂_z^a D_θ^i W| ≤ 2 max Cs 0 α (α+sin 2θ) sin(2θ)^{α/5}
· min z 1` for `1 ≤ i`, `1 ≤ a`, `a + i ≤ 4`. -/
theorem abs_zpow_pzIter_DthIter_VsW_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ i a : ℕ, 1 ≤ i → 1 ≤ a → a + i ≤ 4 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |z ^ a * Work.Spaces.pzIter a (fun z θ => Work.Spaces.DthIter i (VsW α Φs) z θ) z θ|
          ≤ 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
  intro i a hi1 ha1 hai z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have harg : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    angular_weight_nonneg hα hθ
  have hle : Work.Spaces.WlInf α 4 (Vs α Φs) ≤ max Cs 0 * α :=
    le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  have hz0 : 0 ≤ z := hz
  rw [pzIter_DthIter_VsW_eq hα hs i a ha1 (by linarith) hθ,
    abs_mul, abs_of_nonneg (pow_nonneg hz0 a)]
  have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Vs α Φs) hs.V.1 i a hi1 (by omega)
    z θ hz hθI
  have hzp : (0 : ℝ) < z + 1 := by linarith
  have hsplit : z ^ a * (Work.Spaces.WlInf α 4 (Vs α Φs) / (z + 1) ^ a
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      = (z / (z + 1)) ^ a * (Work.Spaces.WlInf α 4 (Vs α Φs)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
    rw [div_pow]
    field_simp
  have hratio : z / (z + 1) ≤ min z 1 := by
    rcases le_total z 1 with h1 | h1
    · rw [min_eq_left h1, div_le_iff₀ hzp]; nlinarith
    · rw [min_eq_right h1, div_le_one hzp]; linarith
  have hratio0 : 0 ≤ z / (z + 1) := div_nonneg hz0 (le_of_lt hzp)
  have hratio1 : z / (z + 1) ≤ 1 := by rw [div_le_one hzp]; linarith
  have hpowle : (z / (z + 1)) ^ a ≤ min z 1 :=
    calc (z / (z + 1)) ^ a ≤ (z / (z + 1)) ^ 1 :=
          pow_le_pow_of_le_one hratio0 hratio1 ha1
      _ = z / (z + 1) := pow_one _
      _ ≤ min z 1 := hratio
  have hmin0 : 0 ≤ min z 1 := le_min hz0 zero_le_one
  calc z ^ a * |Work.Spaces.pzIter a (fun z θ => Work.Spaces.DthIter i (Vs α Φs) z θ) z θ|
      ≤ z ^ a * (Work.Spaces.WlInf α 4 (Vs α Φs) / (z + 1) ^ a
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 a)
    _ = (z / (z + 1)) ^ a * (Work.Spaces.WlInf α 4 (Vs α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := hsplit
    _ ≤ min z 1 * ((max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
        refine le_trans (mul_le_mul_of_nonneg_right hpowle
          (mul_nonneg (Work.Spaces.WlInf_nonneg α 4 (Vs α Φs) hs.V.1) harg)) ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle harg) hmin0
    _ ≤ 2 * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
        rw [show 2 * (max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1
            = 2 * (min z 1 * ((max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) from by ring]
        have hxy : (0 : ℝ) ≤ min z 1 * ((max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_nonneg hmin0 (mul_nonneg hM0 harg)
        linarith

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.n3Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 3200000

/-!
# `n3Bound` — the `N₃`-row of the `L₁₂(N)(0)` estimate

The goal is
`∫_{s>0} ‖L₁₂dens(N₃ α (F_*+g) (Φ_s+Φ_g)) s‖ ≤ K(α² + √α·X + α^{-3/2}X²)`, `X = |g|_{ℋ⁴}`.

`N₃ = -2α·𝒱(Φ̃)·D_zF` with `Φ̃ = Φ̃_* + Φ̃_g` and `F = F_* + g`, so on the open quadrant
(`n3split`)

  `N₃ = -2α·(𝒱(Φ̃_g) + 𝒱(Φ̃_*))·(D_zg + D_zF_*)`,

and the two coefficients are bounded *pointwise* — `|𝒱(Φ̃_g)| ≤ 10√(10/α)·max Ce 0·X`
(`gPt`) and `|𝒱(Φ̃_*)| ≤ max Cs 0·α` (`starPt`).  Hence

  `‖L₁₂dens(N₃) s‖ ≤ (c₀/s)·∫_θ K(θ)(|D_zg| + |D_zF_*|)`,  `c₀ = 2α(cg + cs)`,

and Cauchy–Schwarz against the weight `K` (`Coercivity.slice_cs_K`) followed by `√(w s) =
(1+s)/s` turns the right-hand side into

  `A s · B s`,  `A s = 3·c₀·√(w s·Φ(s))`,  `B s = 1/(1+s)`,
  `Φ(s) = ∫_θ ((D_zg)² + (D_zF_*)²)`.

`w·Φ` is integrable with `∫ w·Φ ≤ HkSq α 4 g + 1600πα²` (the `i = 1` slot for the `g`-part,
`FstarPt` for the `F_*`-part), and `densNormCS` (Cauchy–Schwarz in `s`) gives
`≤ √(∫A²)·√(∫B²) ≤ 3√2·c₀·(X + 40√π·α)`, whence the stated bound.
-/

/-! ## Elementary `θ`-calculus -/



/-- The Lebesgue measure of `Iθ` is `π/2`. -/
theorem real_volume_Iθ :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [Work.Spaces.Iθ, MeasureTheory.Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring


/-- The open angular interval and `Iθ` carry the same measure. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- The radial weight is nonnegative everywhere (the value at `0` is junk). -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The radial weight is `≥ 1` on `z > 0`. -/
theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg z]

/-- The radial weight is positive on `z > 0`. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z :=
  lt_of_lt_of_le zero_lt_one (one_le_w_of_pos hz)




/-- Four-term triangle inequality. -/
theorem abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith



/-! ## The `θ`-slice of `D_z g` and its slot -/

/-- `SmoothQuad` is preserved by `D_z`. -/
theorem smoothQuad_Dz {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) :=
  Work.FTS.LocData.contDiffOn_Dz (isOpen_Ioi.prod isOpen_Ioo) hsm



/-! ## The function `Φ` and its weighted energy -/









/-! ## The estimate -/








end

end Work.FTS.Nonlinear.Pieces.Rl1
end
-- ===== merged: Submission.Work.FTS.OpenPkg.wmul_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.OpenPkg.wmul_field` — the `D`-sup product rule of the open-quadrant vocabulary

This file proves the `wmul` clause of `Work.FTS.OpenPkg.N4Norm'`: on the open quadrant
`(0,∞) × (0,π/2)`, for two `C^∞` functions whose mixed derivatives `D_z^b D_θ^j`
(`D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`) are bounded up to order `4` (`VocabO.WDMem`), the product
again has bounded mixed derivatives and

`WDp 4 (f·g) ≤ C · WDp 4 f · WDp 4 g`

with a **universal** constant `C` (here `160000`), independent of `α`, `f` and `g`.

The `open scoped Real` below is what makes the `π` of the statement denote `Real.pi`: without it,
under this project's `autoImplicit = false`, the bare `π` is an unknown identifier.

Note that `VocabO.WDp`/`WDMem` are built from `Work.FTS.H2.supAbsO`, whose supremum is taken
over the **open** quadrant only (no boundary line, no `(z+1)^k` weight, no angular weight).
Consequently the boundary-vanishing hypothesis on the `z`-derivatives of `g`'s slices — which is
essential for the frozen `WlInf`-form of the same statement
(`Submission/Work/FTS/Nonlinear/N4Fields/wmul_field.lean`) — is *not* needed here: it is kept in
the statement only for interface compatibility, and the proof never uses it.

The mathematical content is the two-operator Leibniz rule
`D_z^b D_θ^j (f·g) = ∑_{a≤j} ∑_{c≤b} C(j,a) C(b,c) (D_z^c D_θ^a f)(D_z^{b-c} D_θ^{j-a} g)`
on the open quadrant, which is already available as
`Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed`.  Every term of the right-hand side pairs a mixed
derivative of `f` of order `c + a ≤ b + j ≤ 4` with one of `g` of order
`(b - c) + (j - a) ≤ 4`; the hypotheses bound each of them, and the `WDp`-norm of a factor
dominates the supremum of each of its mixed derivatives (`supAbsO_mixed_le_WDp`).
-/

noncomputable section
open scoped Real Topology

namespace Work.FTS.OpenPkg

open Work.FTS.VocabO

/-! ## Two elementary consequences of the hypotheses -/

/-- **Each mixed-derivative supremum of a `WDMem`-function is dominated by its `WDp`-norm.**
`WDp 4 f` is the sum of the `supAbsO (mixed b j f)` over the pairs `b + j ≤ 4`, so one such
supremum is `≤` the whole sum (all summands are nonnegative, `supAbsO_nonneg`). -/
theorem supAbsO_mixed_le_WDp {f : ℝ → ℝ → ℝ} (hfm : WDMem 4 f) {b j : ℕ} (hbj : b + j ≤ 4) :
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) ≤ WDp 4 f :=
  Work.FTS.H2.supAbsO_le (fun z θ hz hθ hθ' =>
    WDMem_of_WDp_le hfm le_rfl b j hbj z θ hz hθ hθ')

/-- **The pointwise Leibniz bound for the product.**  For `SmoothOpen` functions `f, g` whose
mixed derivatives are bounded up to order `4` (`WDMem 4`), and for `b + j ≤ 4`, every mixed
derivative `D_z^b D_θ^j (f·g)` is bounded on the open quadrant by `6400 · WDp 4 f · WDp 4 g`.

The constant is deliberately loose: the Leibniz expansion has `(b+1)(j+1) ≤ 25` summands, each of
which is a product of a binomial coefficient `≤ 16` (`Nat.choose_le_two_pow`), one mixed
derivative of `f` (bounded by `WDp 4 f` via `le_supAbsO` and `supAbsO_mixed_le_WDp`) and one of
`g` (bounded by `WDp 4 g`); hence `25 · 16 · 16 = 6400`. -/
theorem mixed_mul_abs_le {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hfm : WDMem 4 f) (hgm : WDMem 4 g)
    {b j : ℕ} (hbj : b + j ≤ 4) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j (fun z θ => f z θ * g z θ) z θ|
        ≤ 6400 * (WDp 4 f * WDp 4 g) := by
  intro z θ hz hθ0 hθ1
  have hWf : 0 ≤ WDp 4 f := WDp_nonneg 4 f
  have hWg : 0 ≤ WDp 4 g := WDp_nonneg 4 g
  have hWfg : 0 ≤ WDp 4 f * WDp 4 g := mul_nonneg hWf hWg
  -- each individual mixed derivative of `f`, resp. `g`, is bounded by the corresponding `WDp`
  have hX : ∀ c a : ℕ, c + a ≤ 4 → |Work.Spaces.mixed c a f z θ| ≤ WDp 4 f := by
    intro c a hca
    exact le_trans
      (Work.FTS.H2.le_supAbsO hz hθ0 hθ1 (fun z' θ' hz' hθ' hθ'' =>
        WDMem_of_WDp_le hfm le_rfl c a hca z' θ' hz' hθ' hθ''))
      (supAbsO_mixed_le_WDp hfm hca)
  have hY : ∀ c a : ℕ, c + a ≤ 4 → |Work.Spaces.mixed c a g z θ| ≤ WDp 4 g := by
    intro c a hca
    exact le_trans
      (Work.FTS.H2.le_supAbsO hz hθ0 hθ1 (fun z' θ' hz' hθ' hθ'' =>
        WDMem_of_WDp_le hgm le_rfl c a hca z' θ' hz' hθ' hθ''))
      (supAbsO_mixed_le_WDp hgm hca)
  -- the binomial coefficients occurring in the expansion
  have hcoef : ∀ n k : ℕ, n ≤ 4 → (n.choose k : ℝ) ≤ 16 := by
    intro n k hn
    have h1 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
    have h2 : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn
    have h3 : n.choose k ≤ 16 := by simpa using le_trans h1 h2
    exact_mod_cast h3
  rw [ProdOpen.leibniz_open_mixed b j f g hf hg z θ hz hθ0 hθ1]
  calc |∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
          ((j.choose a : ℝ) * (b.choose c : ℝ))
            * (Work.Spaces.mixed c a f z θ * Work.Spaces.mixed (b - c) (j - a) g z θ)|
      ≤ ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
          |((j.choose a : ℝ) * (b.choose c : ℝ))
            * (Work.Spaces.mixed c a f z θ * Work.Spaces.mixed (b - c) (j - a) g z θ)| := by
        refine le_trans (Finset.abs_sum_le_sum_abs
          (fun a => ∑ c ∈ Finset.range (b + 1),
            ((j.choose a : ℝ) * (b.choose c : ℝ))
              * (Work.Spaces.mixed c a f z θ * Work.Spaces.mixed (b - c) (j - a) g z θ))
          (Finset.range (j + 1))) ?_
        exact Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
          (256 * (WDp 4 f * WDp 4 g)) := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun c hc => ?_
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hcb : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
        have hb4 : b ≤ 4 := by omega
        have hj4 : j ≤ 4 := by omega
        have hca : c + a ≤ 4 := by omega
        have hca' : (b - c) + (j - a) ≤ 4 := by omega
        rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
          abs_mul]
        have h1 : (j.choose a : ℝ) * (b.choose c : ℝ) ≤ 16 * 16 :=
          mul_le_mul (hcoef j a hj4) (hcoef b c hb4) (Nat.cast_nonneg _) (by norm_num)
        have h2 : |Work.Spaces.mixed c a f z θ| * |Work.Spaces.mixed (b - c) (j - a) g z θ|
            ≤ WDp 4 f * WDp 4 g :=
          mul_le_mul (hX c a hca) (hY (b - c) (j - a) hca') (abs_nonneg _) hWf
        calc (j.choose a : ℝ) * (b.choose c : ℝ)
              * (|Work.Spaces.mixed c a f z θ| * |Work.Spaces.mixed (b - c) (j - a) g z θ|)
            ≤ (16 * 16) * (WDp 4 f * WDp 4 g) :=
              mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
          _ = 256 * (WDp 4 f * WDp 4 g) := by norm_num
    _ = ((j + 1) * (b + 1) : ℝ) * (256 * (WDp 4 f * WDp 4 g)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
          Nat.cast_one]
        ring
    _ ≤ 25 * (256 * (WDp 4 f * WDp 4 g)) := by
        have h1 : ((j + 1) * (b + 1) : ℕ) ≤ 25 := by
          have hb : b + 1 ≤ 5 := by omega
          have hj : j + 1 ≤ 5 := by omega
          calc (j + 1) * (b + 1) ≤ 5 * 5 := Nat.mul_le_mul hj hb
            _ = 25 := by norm_num
        have h1' : ((j + 1) * (b + 1) : ℝ) ≤ 25 := by exact_mod_cast h1
        exact mul_le_mul_of_nonneg_right h1' (mul_nonneg (by norm_num) hWfg)
    _ = 6400 * (WDp 4 f * WDp 4 g) := by ring

/-! ## The product rule -/

theorem wmul_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.FTS.VocabO.WDMem 4 f → Work.FTS.VocabO.WDMem 4 g →
      (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
        Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
      Work.FTS.VocabO.WDMem 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.VocabO.WDp 4 (fun z θ => f z θ * g z θ)
        ≤ C * Work.FTS.VocabO.WDp 4 f * Work.FTS.VocabO.WDp 4 g := by
  refine ⟨160000, by norm_num, ?_⟩
  intro α _hα _hα1 f g hf hg hfm hgm _hbdy
  have hpoint : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j (fun z θ => f z θ * g z θ) z θ|
        ≤ 6400 * (WDp 4 f * WDp 4 g) :=
    fun b j hbj => mixed_mul_abs_le hf hg hfm hgm hbj
  have hMnn : 0 ≤ 6400 * (WDp 4 f * WDp 4 g) :=
    mul_nonneg (by norm_num) (mul_nonneg (WDp_nonneg 4 f) (WDp_nonneg 4 g))
  refine ⟨fun b j hbj => ⟨6400 * (WDp 4 f * WDp 4 g), hpoint b j hbj⟩, ?_⟩
  calc WDp 4 (fun z θ => f z θ * g z θ)
      ≤ 25 * (6400 * (WDp 4 f * WDp 4 g)) :=
        WDp_le_of_pointwise (α := 0) hMnn hpoint
    _ = 160000 * WDp 4 f * WDp 4 g := by ring

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Decomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The angular model extracted from `Psi0_exists` -/

/-- `Psi0_exists` yields an `AngModel` together with a bound on the angular interval. -/
theorem Psi0AngModel {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∃ (C : ℝ) (ψ : ℝ → ℝ), 0 < C ∧ AngModel α ψ ∧ ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := Psi0_exists
  obtain ⟨ψ, hsm, hcont, h0, h1, heq, hmom, -, -, hDth⟩ := hC α hα hα4
  refine ⟨C, ψ, hCpos, ⟨hsm, hcont, h0, h1, heq, hmom⟩, ?_⟩
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0' | h0'
  · rw [← h0', h0, abs_zero]; exact hCpos.le
  rcases eq_or_lt_of_le hθ.2 with h1' | h1'
  · rw [h1', h1, abs_zero]; exact hCpos.le
  have hbound := hDth 0 (by norm_num) θ ⟨h0', h1'⟩
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  calc |ψ θ| = |Work.Spaces.DthIter 0 (fun _ θ' => ψ θ') 0 θ| := rfl
    _ ≤ C * Real.sin (2 * θ) := hbound
    _ ≤ C * 1 := by
        exact mul_le_mul_of_nonneg_left hsin1 hCpos.le
    _ = C := mul_one C

/-! ## Smoothness of the model part -/

/-- The model part `Model α (GzProfile α) ψ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_model {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hψ : AngModel α ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Model α (GzProfile α) ψ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  exact contDiffOn_model n (GzProfile_smooth hα hα4 n)
    (contDiffOn_iff_forall_nat_le.mp hψ.smooth n le_top)

/-! ## The decomposition of a solution -/


/-! ## End-to-end: the profile's stream function splits through the `O(α²)` equation -/


end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3

theorem L12_dzdIter_moment_honest (α : ℝ) {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    (∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g k z)
    ∧ (∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z)) z) := by
  -- The index-raising recursion `D_z^{k+1} L₁₂(g) = - Qang g k` (`k ≤ 3`) and the weighted
  -- integrability of `L₁₂(g)² w²` are the output of the open-quadrant `L₁₂`-bundle.  Note
  -- `Work.Construction.L12 = Work.Elliptic.L12` definitionally (`rfl`).
  have hbundle := Work.FTS.OpenPkg.l12_open_bundle α g hα hα1 hsm hmem h0
  have hrec : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g k z :=
    fun k hk z hz => hbundle.1 k hk z hz
  -- `Qang g j` is differentiable on `(0,∞)` for `j ≤ 2`, with `∂_z Qang g j = Qang g (j+1)/z`.
  have hQdiff : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (Work.Elliptic.Qang g j) (Work.Elliptic.Qang g (j + 1) z / z) z :=
    (Work.FTS.OpenPkg.QangOpen.QangDiff_open α g hα hα1 hsm hmem).1
  refine ⟨hrec, ?_⟩
  intro b hb3 z hz
  rcases b with _ | c
  · -- `b = 0`: `L₁₂(g)` has derivative `-3·F_*(g)(z)/z` at `z > 0`.
    have hd : HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
      (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 g hsm hmem
        (by norm_num)).2 z hz
    exact hd.differentiableAt
  · -- `b = c + 1`, `c ≤ 2`: on the open half-line `D_z^{c+1} L₁₂(g) = - Qang g c`, and the
    -- angular moment `Qang g c` is differentiable there.
    have hc : c ≤ 2 := by omega
    have hev : Work.Elliptic.DzdIter (c + 1) (fun z => Work.Construction.L12 g z)
        =ᶠ[nhds z] fun u => - Work.Elliptic.Qang g c u := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
      exact hrec c (by omega) u hu
    exact ((hQdiff c hc z hz).differentiableAt.neg).congr_of_eventuallyEq hev

end Work.FTS.StrongEps.E4R3
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.EDthW_EL12z_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary continuity on the open quadrant -/

/-- The radial weight `w z = (1+z)²/z²` is continuous on the open quadrant. -/
theorem continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- The square of the radial weight is continuous on the open quadrant. -/
theorem continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by funext p; rfl
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))).pow 2

/-- The `ℋ^k`-weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hfun]
  refine continuousOn_w_Q0.mul ?_
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-! ## The joint integrability of `(f w)²` in the open class -/

/-- **`(f w)²` is jointly integrable on the quadrant** for a datum `f` of class `C^∞` on the open
quadrant which is honestly in `ℋ²`.

The dominating function is the `D_z⁰`-summand `(f·w/√(sin(2θ)^η))²` of `HkIntegrand α 2 f`
(which is `≥ (f w)²` a.e.: off the null set `{sin(2θ) = 0}` one has
`sin(2θ)^{η/2} ∈ (0,1]`, hence `w ≤ w/√(sin(2θ)^η)`). -/
theorem integrableOn_f_sq_w_sq_open {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  -- the `η`-weighted dominating integrand, a summand of the `ℋ²`-integrand
  have hbig : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter 0 f z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
      ((hso.continuousOn_summand 0).pow 2)
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ 0 (by norm_num))
  -- a.e. strong measurability of `(f w)²`, from its continuity on the open quadrant
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hso.continuousOn
      have hfun : (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
          = fun p : ℝ × ℝ => f p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 := by
        funext p; ring
      rw [hfun]
      exact (h1.pow 2).mul continuousOn_w_sq_Q0
    have h2 := Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2) hcont
    rwa [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict] at h2
  -- the a.e. domination by the `η`-weighted summand
  have hle : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      ‖(f p.1 p.2 * Work.Spaces.w p.1) ^ 2‖
        ≤ ‖(f p.1 p.2 * (Work.Spaces.w p.1
            / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2‖ := by
    have hmem : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
        p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
      have h := Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo
      rwa [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict] at h
    filter_upwards [hmem] with p hp
    have hs : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.1]) (by linarith [hp.2, Real.pi_pos])
    have hs1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    have heta : 0 < Work.Spaces.eta / 2 := by rw [Work.Spaces.eta]; norm_num
    have hsle : Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hs) hs1 (le_of_lt heta)
    have hspos : 0 < Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos hs _
    have hw0 : 0 ≤ Work.Spaces.w p.1 := by rw [Work.Spaces.w]; positivity
    have hws : Work.Spaces.w p.1
        ≤ Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2) := by
      rw [le_div_iff₀ hspos]
      nlinarith [hw0, hsle]
    have h1 : |f p.1 p.2 * Work.Spaces.w p.1|
        ≤ |f p.1 p.2 * (Work.Spaces.w p.1
            / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw0,
        abs_of_nonneg (div_nonneg hw0 (le_of_lt hspos))]
      exact mul_le_mul_of_nonneg_left hws (abs_nonneg _)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
    calc (f p.1 p.2 * Work.Spaces.w p.1) ^ 2
        = |f p.1 p.2 * Work.Spaces.w p.1| ^ 2 := (sq_abs _).symm
      _ ≤ |f p.1 p.2 * (Work.Spaces.w p.1
            / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (f p.1 p.2 * (Work.Spaces.w p.1
            / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_abs _
  exact hbig.norm.mono' haesm hle

/-! ## The two comparisons -/

/-- `EDthW f ≤ EDth α f`: the unweighted angular energy is dominated by the
`sin(2θ)^{-γ}`-weighted one.

`EDthW f = ∫∫ (D_θ f)² w²` is the iterated integral of `(D_θf · w)²`; its angular majorant
`(D_θf · Wt α)²` is the `(i,j) = (1,0)` mixed summand of `HkIntegrand α 2 f`, so
`i2Mem_sq_of_le` (from the open-quadrant smoothness of `f` and `f ∈ ℋ²`) makes the iterated
integral of the majorant honest, and monotonicity of the iterated integral closes the bound. -/
theorem EDthW_le_EDth_open {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) :
    Work.Coercivity.EDthW f ≤ Work.Coercivity.EDth α f := by
  -- ## the angular majorant is honest
  have hB : Work.Coercivity.I2Mem
      (fun z θ => (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine Work.FTS.CoercivityFix.Coer1.i2Mem_sq_of_le α 2 hm ?_ ?_
    · exact (((hso.Dth).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
    · intro z _ θ _
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ 1 0 (by norm_num) (by norm_num)
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] using h
  -- ## the two energies as squared iterated `L²`-norms
  have hW : Work.Coercivity.EDthW f
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.w z) := by
    rw [Work.Coercivity.EDthW, Work.Coercivity.wip, Work.Spaces.L2Sq]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    ring
  have hD : Work.Coercivity.EDth α f
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) := rfl
  rw [hW, hD, Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  -- ## the outer integral
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hB.2 ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  -- ## the inner (angular) integral
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => sq_nonneg _) (hB.1 z hz) ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
  -- ## the pointwise comparison of the two angular weights
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hg : 0 ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith
  have hge1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Real.rpow_neg (le_of_lt hs)]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hs _)).mpr
      (Real.rpow_le_one (le_of_lt hs) hs1 hg)
  have hw0 : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hwle : Work.Spaces.w z ≤ Work.Spaces.Wt α z θ := by
    show Work.Spaces.w z ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
    calc Work.Spaces.w z = Work.Spaces.w z * 1 := (mul_one _).symm
      _ ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
          mul_le_mul_of_nonneg_left hge1 hw0
  have h1 : |Work.Spaces.Dth f z θ * Work.Spaces.w z|
      ≤ |Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (le_trans hw0 hwle)]
    exact mul_le_mul_of_nonneg_left hwle (abs_nonneg _)
  calc (Work.Spaces.Dth f z θ * Work.Spaces.w z) ^ 2
      = |Work.Spaces.Dth f z θ * Work.Spaces.w z| ^ 2 := (sq_abs _).symm
    _ ≤ |Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ| ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2 := sq_abs _

/-- **The open-class replacement of the two finite-dimensional inputs of the level-one
coercivity ledger**: `EDthW f ≤ EDth α f` and `EL12z f ≤ 16 Ef f`, from `SmoothOpen f`,
`f ∈ ℋ²` and the Hardy hypotheses `HardyHyp f` — no `SmoothQuad` (flatness at `z = 0`) is
needed. -/
theorem EDthW_EL12z_open {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f)
    (hHH : Work.Coercivity.HardyHyp f) :
    Work.Coercivity.EDthW f ≤ Work.Coercivity.EDth α f ∧
      Work.Coercivity.EL12z f ≤ 16 * Work.Coercivity.Ef f :=
  ⟨EDthW_le_EDth_open hα hso hm,
    Work.Coercivity.EL12z_le f hHH (integrableOn_f_sq_w_sq_open hso hm)⟩

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Dz_LGammaT_eq_Lhat_add_Zrest_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The pointwise decomposition of `D_z𝓛_Γ^T` in the interior class.**  With
`𝓛_Γ^T = 𝓛̂ + Corr` (`LGammaT_eq_Lhat_add_Corr`), the `z`-derivative splits as

  `D_z(𝓛_Γ^T f) = D_z(𝓛̂ f) + Z₃ + Z₄ + Z₇`,

where `Z₃, Z₄, Z₇` are the three nonlocal/projector terms of `Work.Coercivity.SumI`, in the
open-quadrant class `SmoothOpen` (the class of a localised datum). -/
theorem Dz_LGammaT_eq_Lhat_add_Zrest_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Work.FTS.Galerkin.Fn} (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hfH : Work.Coercivity.HardyHyp f) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ := by
  have hα1' : α ≤ 1 := by linarith [hα1]
  intro z θ hz hθ
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1'
  have hcdPz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.pz
  have hcdPth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.pth
  have hdiffF : DifferentiableAt ℝ (fun t : ℝ => f t θ) z :=
    (((hso.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz))
  have hdiffPz : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz f t θ) z :=
    (((Work.FTS.LocData.contDiffOn_slice_z hcdPz hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz))
  have hdiffPth : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pth f t θ) z :=
    (((Work.FTS.LocData.contDiffOn_slice_z hcdPth hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz))
  have hF : HasDerivAt (fun t : ℝ => f t θ) (Work.Spaces.pz f z θ) z := hdiffF.hasDerivAt
  have hPz : HasDerivAt (fun t : ℝ => Work.Spaces.pz f t θ)
      (Work.Spaces.pz (Work.Spaces.pz f) z θ) z := hdiffPz.hasDerivAt
  have hPth : HasDerivAt (fun t : ℝ => Work.Spaces.pth f t θ)
      (Work.Spaces.pz (Work.Spaces.pth f) z θ) z := hdiffPth.hasDerivAt
  have hden1 : HasDerivAt (fun t : ℝ => 1 + t) (1 : ℝ) z := (hasDerivAt_id z).const_add 1
  -- ## the derivative of the `𝓛̂`-slice
  have hDz : HasDerivAt (fun t : ℝ => t * Work.Spaces.pz f t θ)
      (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) z :=
    (hasDerivAt_id z).mul hPz
  have hq3 : HasDerivAt (fun t : ℝ => 2 * f t θ / (1 + t))
      ((2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2) z :=
    (hF.const_mul 2).div hden1 h1z
  have hq4 : HasDerivAt (fun t : ℝ => 3 * Real.sin (2 * θ) * Work.Spaces.pth f t θ / (1 + t))
      ((3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
        - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2) z :=
    ((hPth.const_mul (3 * Real.sin (2 * θ))).div hden1 h1z)
  have hLhatSlice : HasDerivAt (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ)
      (Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2) z := by
    have hmain := ((hF.add hDz).sub hq3).sub hq4
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Work.Spaces.Dz, Work.Spaces.Dth]
    ring
  -- ## the derivative of the `Corr`-slice
  have hL12 : HasDerivAt (fun t : ℝ => Work.Coercivity.L12f f t)
      (-(Work.Coercivity.Kavg f z / z)) z := Work.Coercivity.L12f_zDeriv f hfH hz
  have hsq : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + z)) z := by
    have hraw := hden1.pow 2
    have hfun : ((fun t : ℝ => 1 + t) ^ 2) =ᶠ[𝓝 z] (fun t : ℝ => (1 + t) ^ 2) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp)
  have hinv : HasDerivAt (fun t : ℝ => ((1 + t) ^ 2)⁻¹)
      (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2) z := hsq.inv (by positivity)
  have hprod : HasDerivAt (fun t : ℝ => t * ((1 + t) ^ 2)⁻¹)
      (1 * ((1 + z) ^ 2)⁻¹ + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) z :=
    (hasDerivAt_id z).mul hinv
  have hg1 : HasDerivAt
      (fun t : ℝ => (-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (t * ((1 + t) ^ 2)⁻¹)
        * Work.Coercivity.L12f f t)
      ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))) z :=
    (hprod.const_mul (-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹))).mul hL12
  have hsq2 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * z) z := by
    have hraw := ((hasDerivAt_id z).pow 2).const_mul 2
    have hfun : (fun y : ℝ => 2 * (id ^ 2) y) =ᶠ[𝓝 z] (fun t : ℝ => 2 * t ^ 2) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp; ring)
  have hcube : HasDerivAt (fun t : ℝ => (1 + t) ^ 3) (3 * (1 + z) ^ 2) z := by
    have hraw := hden1.pow 3
    have hfun : ((fun t : ℝ => 1 + t) ^ 3) =ᶠ[𝓝 z] (fun t : ℝ => (1 + t) ^ 3) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp)
  have hinv3 : HasDerivAt (fun t : ℝ => ((1 + t) ^ 3)⁻¹)
      (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2) z := hcube.inv (by positivity)
  have hinner : HasDerivAt (fun t : ℝ => 2 * t ^ 2 * ((1 + t) ^ 3)⁻¹)
      (4 * z * ((1 + z) ^ 3)⁻¹
        + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2)) z :=
    hsq2.mul hinv3
  have hg2 : HasDerivAt
      (fun t : ℝ => (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
        * (2 * t ^ 2 * ((1 + t) ^ 3)⁻¹))
      ((Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
        * (4 * z * ((1 + z) ^ 3)⁻¹
          + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2))) z :=
    hinner.const_mul _
  have hCorrSlice : HasDerivAt (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ)
      ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))
        + (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
          * (4 * z * ((1 + z) ^ 3)⁻¹
            + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2))) z := by
    have hmain := hg1.add hg2
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    have ht' : (0 : ℝ) < t := ht
    have h1t : (1 : ℝ) + t ≠ 0 := by linarith
    simp only [Pi.add_apply]
    rw [Work.FTS.CoercivityFix.Corr_eq, Work.Coercivity.C0]
    field_simp
  -- ## the sum
  have hsum : HasDerivAt (fun t : ℝ => Work.Coercivity.LGammaT α f t θ)
      ((Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2)
      + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))
        + (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
          * (4 * z * ((1 + z) ^ 3)⁻¹
            + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2)))) z := by
    have hmain := hLhatSlice.add hCorrSlice
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards with t
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr]
    rfl
  have hderiv := hsum.deriv
  -- ## conclusion
  show Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ = _
  rw [show Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
      = z * deriv (fun t : ℝ => Work.Coercivity.LGammaT α f t θ) z from rfl, hderiv,
    show Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = z * (Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2)
      from by
        rw [show Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
            = z * deriv (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ) z from rfl,
          hLhatSlice.deriv]]
  simp only [Work.Coercivity.Z3, Work.Coercivity.Z4, Work.Coercivity.Z7]
  field_simp
  ring

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.StepCoerO =====
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





end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz =====
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

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `D_θ`-port -/

/-- `D_θ` raises the angular order of the mixed derivatives by one:
`D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`. -/
private lemma mixed_Dth_shift_fts (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f := by
  simp only [Work.Spaces.mixed]
  have h : Work.Spaces.Dth f = Work.Spaces.DthIter 1 f := rfl
  rw [h, Work.Spaces.DthIter_add_right]

/-- **The boundary traces of `D_θ f`** from those of `f`, by the (global) reindexing of the
mixed derivatives: the traces of order `(a,b)` of `D_θ f` are the traces of order `(a+1,b)` of
`f`. -/
private lemma BdryTraces_Dth_fts {α : ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hbd : Work.FTS.Nonlin.BdryTraces α (n + 1) f) :
    Work.FTS.Nonlin.BdryTraces α n (Work.Spaces.Dth f) := by
  intro a b hab
  have key : ∀ z θ, Work.Spaces.mixed b a (Work.Spaces.Dth f) z θ
      = Work.Spaces.mixed b (a + 1) f z θ := fun z θ => by rw [mixed_Dth_shift_fts]
  simpa only [key] using hbd (a + 1) b (by omega)

/-- **The `ℋⁿ`-membership of `D_θ f`**, by domination of its integrand by the `(n+1)`-integrand
of `f` (`Work.Coercivity.HkIntegrand_Dth_le`), through `HkMem_of_majorant`, the measurability
input being the continuity of the integrand of `D_θ f` on the open quadrant. -/
private lemma HkMem_Dth_fts {α : ℝ} (hα : 0 < α) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
  Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ)
    (hsm.Dth.continuousOn_HkIntegrand α n)
    hmem.1 hmem.2
    (fun z hz θ hθ => Work.Coercivity.HkIntegrand_Dth_le α hα n f z θ hz hθ)

/-! ## The `D_z`-port -/

/-- **The boundary traces of `D_z f`** from those of `f`: the traces at order `(a,b)` of `D_z f`
are the traces at order `(a,b+1)` of `f`, because the mixed derivatives agree on the domain
(`Work.FTS.EllipticEst.UopHk.mixed_Dz_shift`) and every one-sided limit is taken through points
of the domain. -/
private lemma BdryTraces_Dz_fts {α : ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hbd : Work.FTS.Nonlin.BdryTraces α (n + 1) f) :
    Work.FTS.Nonlin.BdryTraces α n (Work.Spaces.Dz f) := by
  intro a b hab
  obtain ⟨hzlim, hθlim⟩ := hbd a (b + 1) (by omega)
  -- the two filters `𝓝[>] 0`, `𝓝[<] π/2` count the open interval as an eventual set
  have hmemGT : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    (nhdsGT_basis_of_exists_gt ⟨π / 2, Real.pi_div_two_pos⟩).mem_of_mem Real.pi_div_two_pos
  have hmemLT : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[<] (π / 2) :=
    (nhdsLT_basis_of_exists_lt ⟨0, by linarith [Real.pi_pos]⟩).mem_of_mem
      (by linarith [Real.pi_pos])
  constructor
  · intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    constructor
    · have hev : (fun z => z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun z => z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2 :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => by
          show z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
            = z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2
          rw [Work.FTS.EllipticEst.UopHk.mixed_Dz_shift hsm b a
            (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz))) hθIθ])
      exact (hzlim θ hθ).1.congr' hev
    · have hev : (fun z => z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2)
          =ᶠ[atTop]
          fun z => z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2 :=
        Filter.eventually_of_mem (Ioi_mem_atTop (0 : ℝ)) (fun z hz => by
          show z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
            = z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2
          rw [Work.FTS.EllipticEst.UopHk.mixed_Dz_shift hsm b a
            (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz))) hθIθ])
      exact (hzlim θ hθ).2.congr' hev
  · intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    constructor
    · have hev : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2 :=
        Filter.eventually_of_mem hmemGT (fun θ hθ => by
          show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
            = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2
          rw [Work.FTS.EllipticEst.UopHk.mixed_Dz_shift hsm b a hzIz
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩])
      exact (hθlim z hz).1.congr' hev
    · have hev : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2)
          =ᶠ[𝓝[<] (π / 2)]
          fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2 :=
        Filter.eventually_of_mem hmemLT (fun θ hθ => by
          show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
            = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2
          rw [Work.FTS.EllipticEst.UopHk.mixed_Dz_shift hsm b a hzIz
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩])
      exact (hθlim z hz).2.congr' hev

/-- **The `ℋⁿ`-membership of `D_z f`**, by domination of its integrand by the `(n+1)`-integrand
of `f` (`Work.FTS.EllipticEst.UopHk.HkIntegrand_Dz_le_succ`, i.e. the index shift
`D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f` on `Iz × Iθ`). -/
private lemma HkMem_Dz_fts {α : ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkMem α n (Work.Spaces.Dz f) :=
  Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α n hsm hmem

/-! ## The two ports, assembled -/

theorem regQo_dth_dz {α : ℝ} {n : ℕ} {f : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.Spaces.Dth f) ∧
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.Spaces.Dz f) := by
  obtain ⟨hsm, hmem, hbd⟩ := hf
  exact ⟨⟨hsm.Dth, HkMem_Dth_fts hα hsm hmem, BdryTraces_Dth_fts hbd⟩,
    ⟨hsm.Dz, HkMem_Dz_fts hsm hmem, BdryTraces_Dz_fts hsm hbd⟩⟩

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.slice_ibp_gen_O =====
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

set_option maxHeartbeats 1600000

/-- Differentiability of the `θ`-slice of a `SmoothOpen` function at an interior angle.  This is
the `SmoothOpen` analogue of `Work.FTS.CoercivityFix.Coer1.differentiableAt_slice_theta_Q`. -/
theorem differentiableAt_slice_theta_O {v : Fn} (hv : Work.FTS.EllipticEst.SmoothOpen v)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => v z θ') θ :=
  ((hv.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- The derivative of the angular boundary term `ψ θ = sin(2θ)^{-(β-1)}·v(z,θ)²` at an
interior angle, where `sin(2θ) > 0` so that the power is genuinely differentiable.  The
derivative is written in the form `2·(sin(2θ)^{-β} D_θ v · v) - 2(β-1)·(cos(2θ) sin(2θ)^{-β} v²)`
adapted to the two integrands of `slice_ibp_gen_O`.  This is
`Work.FTS.CoercivityFix.Coer1.slice_psi_hasDerivAt_gen_Q` with `SmoothOpen` in place of
`SmoothQuad`. -/
theorem slice_psi_hasDerivAt_gen_O (β : ℝ) (v : Fn) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (z θ : ℝ) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hsin : 0 < Real.sin (2 * θ)) :
    HasDerivAt (fun θ' => (Real.sin (2 * θ')) ^ (-(β - 1)) * (v z θ') ^ 2)
      (2 * ((Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ)
        - (2 * (β - 1)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2)) θ := by
  have hdiff : DifferentiableAt ℝ (fun θ' => v z θ') θ :=
    differentiableAt_slice_theta_O hv hz hθ
  have hu : HasDerivAt (fun θ' => v z θ') (Work.Spaces.pth v z θ) θ := hdiff.hasDerivAt
  have hs2 : HasDerivAt (fun θ' => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    convert h using 1
    · ext θ'; simp [Function.comp]
    · ring
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  have hφ : HasDerivAt (fun θ' => (Real.sin (2 * θ')) ^ (-(β - 1)))
      ((-(β - 1)) * (Real.sin (2 * θ)) ^ (-(β - 1) - 1)
        * (2 * Real.cos (2 * θ))) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ))
      (p := -(β - 1)) (Or.inl hsinne)).comp θ hs2
    convert h using 1
    · ext θ'; simp [Function.comp]
  have hu2 : HasDerivAt (fun θ' => (v z θ') ^ 2) (2 * (v z θ) * Work.Spaces.pth v z θ) θ := by
    have h := (hasDerivAt_pow 2 (v z θ)).comp θ hu
    convert h using 1
    · ext θ'; simp [Function.comp]
    · simp only [Nat.reduceSub, pow_one]; ring
  have hψ := hφ.mul hu2
  have key : ( (-(β - 1)) * Real.sin (2 * θ) ^ (-(β - 1) - 1)
          * (2 * Real.cos (2 * θ)) * (v z θ) ^ 2
        + Real.sin (2 * θ) ^ (-(β - 1)) * (2 * (v z θ) * Work.Spaces.pth v z θ) )
      = 2 * ((Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ)
        - (2 * (β - 1)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2) := by
    have hA : Real.sin (2 * θ) ^ (-(β - 1))
        = Real.sin (2 * θ) ^ (-β) * Real.sin (2 * θ) := by
      rw [show -(β - 1) = -β + 1 by ring, Real.rpow_add hsin, Real.rpow_one]
    have hB : Real.sin (2 * θ) ^ (-(β - 1) - 1)
        = Real.sin (2 * θ) ^ (-β) := by
      rw [show -(β - 1) - 1 = -β by ring]
    rw [hA, hB, Work.Spaces.Dth]
    ring
  rw [key] at hψ
  exact hψ

/-- **The one-dimensional angular integration by parts** for the weight `sin(2θ)^{-β}`, in the
open-quadrant class `SmoothOpen`: for `z > 0`,
`∫_θ sin(2θ)^{-β} D_θv · v = (β-1) ∫_θ cos(2θ) sin(2θ)^{-β} v²`,
the boundary term `sin(2θ)^{1-β}v²` vanishing at `0⁺` and `(π/2)⁻`. -/
theorem slice_ibp_gen_O (β : ℝ) (v : Work.FTS.Galerkin.Fn)
    (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hvan : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (v z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hvan2 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (v z θ) ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0))
    (z : ℝ) (hz : 0 < z)
    (hI : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ) Work.Spaces.Iθ)
    (hK : MeasureTheory.IntegrableOn
      (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2) Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ
      = (β - 1) * ∫ θ in Work.Spaces.Iθ,
          Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2 := by
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hpi2pos : (0 : ℝ) < Real.pi / 2 := by positivity
  set g : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ with hg
  set k : ℝ → ℝ := fun θ =>
    Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2 with hk
  have hIg : MeasureTheory.IntegrableOn g (Set.Icc 0 (Real.pi / 2)) := hI
  have hKg : MeasureTheory.IntegrableOn k (Set.Icc 0 (Real.pi / 2)) := hK
  have hgi : IntervalIntegrable g volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr (hIg.mono_set Set.Ioc_subset_Icc_self)
  have hki : IntervalIntegrable k volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr (hKg.mono_set Set.Ioc_subset_Icc_self)
  have hvan' : ∀ z, 0 < z → Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (-(β - 1)) * (v z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := fun z hz => by
    simpa only [neg_sub] using hvan z hz
  have hvan2' : ∀ z, 0 < z → Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (-(β - 1)) * (v z θ) ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := fun z hz => by
    simpa only [neg_sub] using hvan2 z hz
  have hpsi_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ => (Real.sin (2 * θ)) ^ (-(β - 1)) * (v z θ) ^ 2)
        (2 * ((Real.sin (2 * x)) ^ (-β) * Work.Spaces.Dth v z x * v z x)
          - (2 * (β - 1)) *
              (Real.cos (2 * x) * (Real.sin (2 * x)) ^ (-β) * (v z x) ^ 2)) x := by
    intro x hx
    have hsin : 0 < Real.sin (2 * x) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
    exact slice_psi_hasDerivAt_gen_O β v hv z x hz hx hsin
  have hf'int : IntervalIntegrable (fun y => 2 * g y - (2 * (β - 1)) * k y)
      volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
      (((hIg.mono_set Set.Ioc_subset_Icc_self).const_mul 2).sub
        ((hKg.mono_set Set.Ioc_subset_Icc_self).const_mul (2 * (β - 1))))
  have hFTC0 : ∫ y in (0 : ℝ)..(Real.pi / 2), (2 * g y - (2 * (β - 1)) * k y) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := 0) (b := Real.pi / 2)
      hpi2pos
      (f := fun θ => (Real.sin (2 * θ)) ^ (-(β - 1)) * (v z θ) ^ 2)
      (f' := fun y => 2 * g y - (2 * (β - 1)) * k y)
      hpsi_deriv hf'int (hvan' z hz) (hvan2' z hz)
    simpa using h
  have hsplit : ∫ y in (0 : ℝ)..(Real.pi / 2), (2 * g y - (2 * (β - 1)) * k y)
      = 2 * (∫ y in (0 : ℝ)..(Real.pi / 2), g y)
        - (2 * (β - 1)) * (∫ y in (0 : ℝ)..(Real.pi / 2), k y) := by
    rw [intervalIntegral.integral_sub (hgi.const_mul 2) (hki.const_mul (2 * (β - 1))),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hg_eq : ∫ y in Work.Spaces.Iθ, g y = ∫ y in (0 : ℝ)..(Real.pi / 2), g y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)))).symm
  have hk_eq : ∫ y in Work.Spaces.Iθ, k y = ∫ y in (0 : ℝ)..(Real.pi / 2), k y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)))).symm
  have hmain : ∫ y in (0 : ℝ)..(Real.pi / 2), g y
      = (β - 1) * ∫ y in (0 : ℝ)..(Real.pi / 2), k y := by
    have h2 : 2 * (∫ y in (0 : ℝ)..(Real.pi / 2), g y)
        = 2 * ((β - 1) * ∫ y in (0 : ℝ)..(Real.pi / 2), k y) := by
      rw [hsplit] at hFTC0
      linarith
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h2
  rw [hg_eq, hk_eq]
  exact hmain

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.QangDiff7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `QangDiff7` — the level-six `z`-differentiation of the angular moments

`Work.Elliptic.Qang g j z = ∫_θ Ktheta θ · (D_z^j g)(z,θ) dθ` is the `j`-th angular moment of
`g`.  The level-four chain (`Work.FTS.OpenPkg.QangOpen`) proves, for a datum which is `C^∞` on
the open quadrant and lies in `ℋ⁴`, the divided derivative

  `∂_z (Qang g j) z = Qang g (j+1) z / z`   (`z > 0`, `j ≤ 2`),

and `QangDiff6` pushes this to `j ≤ 4` for a datum in `ℋ⁶`, by transporting the level-four
chain to the shift `D_z²g` (using `Qang g (k+2) = Qang (D_z²g) k`).

Here we push one level further: for `g ∈ ℋ⁷` (and `C^∞` on the quadrant) the divided
derivative holds for `j ≤ 5`.  The extra level is obtained from the *first* shift, exactly as in
`Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four`: the level-six chain for `D_z g`
(available since `g ∈ ℋ⁷` gives `D_z g ∈ ℋ⁶` by `HkMem_Dz_of_smoothOpen`) yields

  `∂_z (Qang (D_z g) j) z = Qang (D_z g) (j+1) z / z`  for `j ≤ 4`,

which, after the identification `Qang (D_z g) k = Qang g (k+1)`, is precisely the statement for
`1 ≤ j ≤ 5`; the remaining case `j = 0` is the `j ≤ 4` instance of the chain for `g` itself.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- `D_z^i (D_z f) = D_z^{i+1} f`. -/
theorem DzIter_Dz_shift_one (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dz f) = Work.Spaces.DzIter (i + 1) f := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-- The angular-moment tower shifts by one under `f ↦ D_z f`:
`Qang (D_z f) i = Qang f (i + 1)`. -/
theorem Qang_Dz_shift_one (f : ℝ → ℝ → ℝ) (i : ℕ) (z : ℝ) :
    Work.Elliptic.Qang (Work.Spaces.Dz f) i z = Work.Elliptic.Qang f (i + 1) z := by
  rw [Work.Elliptic.Qang, Work.Elliptic.Qang]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
    rw [DzIter_Dz_shift_one i f])

theorem QangDiff7 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 7 g) :
    ∀ j : ℕ, j ≤ 5 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w)
        (Work.Elliptic.Qang g (j + 1) z / z) z := by
  -- the two `ℋ⁶`-data which the level-six chain consumes: `g` itself and its shift `D_z g`
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 6 (by norm_num) hmem
  have hmemDz : Work.Spaces.HkMem α 6 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 6 hO hmem
  have hOdz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hO.Dz
  -- the level-six divided derivatives for `g` (giving `j ≤ 4`) and for `D_z g` (giving the
  -- top level `j = 5` through the shift identification)
  have hderG : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w)
        (Work.Elliptic.Qang g (j + 1) z / z) z :=
    (Work.FTS.StrongPersist.QangDiff6 (α := α) hO hmem6).1
  have hderDz : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang (Work.Spaces.Dz g) j w)
        (Work.Elliptic.Qang (Work.Spaces.Dz g) (j + 1) z / z) z :=
    (Work.FTS.StrongPersist.QangDiff6 (α := α) hOdz hmemDz).1
  intro j hj z hz
  rcases Nat.lt_or_ge j 5 with hlt | hge
  · exact hderG j (by omega) z hz
  · have hj5 : j = 5 := by omega
    subst hj5
    -- `Qang g 5 = Qang (D_z g) 4` and `Qang (D_z g) 5 = Qang g 6`
    have h' : HasDerivAt (fun w => Work.Elliptic.Qang g 5 w)
        (Work.Elliptic.Qang (Work.Spaces.Dz g) 5 z / z) z :=
      (hderDz 4 (by norm_num) z hz).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun w => (Qang_Dz_shift_one g 4 w).symm))
    have hval : Work.Elliptic.Qang (Work.Spaces.Dz g) 5 z / z
        = Work.Elliptic.Qang g 6 z / z := by
      rw [Qang_Dz_shift_one g 5 z]
    rw [hval] at h'
    exact h'

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.slotPairCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

-- The product measure `(volume ↾ Iz) ⊗ (volume ↾ Iθ)` on which the slot pairing lives,
-- written once so that the proof below stays readable.  This is *notation only*: it
-- introduces no declaration and the theorem statement is unchanged.
local notation "μP" => MeasureTheory.Measure.prod (MeasureTheory.volume.restrict Work.Spaces.Iz)
  (MeasureTheory.volume.restrict Work.Spaces.Iθ)

theorem slotPairCS :
    ∀ (α : ℝ) (A f X Y Z : ℝ → ℝ → ℝ) (ρ : ℝ → ℝ → ℝ) (k : ℕ) (B : ℝ),
      α ∈ Set.Ioc 0 1 → k ≤ 6 →
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α k A →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      0 ≤ B →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ) →
      ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * |X p.1 p.2| * |Z p.1 p.2|)
        Work.FTS.LocData.Qd →
      ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2)
        Work.FTS.LocData.Qd →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Y z θ| ≤ B) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * |X z θ| * |Z z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α k A z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2
          * Z p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ B * (Real.sqrt (Work.Spaces.HkSq α k A)
            * Real.sqrt (Work.Spaces.HkSq α 6 f)) := by
  intro α A f X Y Z ρ k B _hα _hk hsmA hmA hsmf hmf hB hρnn _hcontAZ hcontXYZ hY hpt
  -- The two `ℋ^k`-integrands are product-integrable with integrals `HkSq`.
  obtain ⟨hintA, hvalA⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsmA hmA
  obtain ⟨hintF, hvalF⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsmf hmf
  -- Almost every point of the product measure lies in the open quadrant, where the
  -- pointwise hypotheses live.
  have haeQd : ∀ᵐ p ∂μP, p ∈ Work.FTS.LocData.Qd := by
    have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
    have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm
    have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
        =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] Work.FTS.LocData.Qd :=
      MeasureTheory.Measure.set_prod_ae_eq hz hθ
    have hμQd : μP = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
        Work.FTS.LocData.Qd := by
      rw [← MeasureTheory.Measure.restrict_congr_set hprod,
        ← MeasureTheory.Measure.prod_restrict]
    rw [hμQd]
    exact MeasureTheory.ae_restrict_mem ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)
  -- The pointwise domination almost everywhere: fold the `|Y| ≤ B` and the
  -- Cauchy–Schwarz input `ρ |X| |Z| ≤ √(HkIntegrand α k A) √(HkIntegrand α 6 f)`.
  have hdom : ∀ᵐ p ∂μP, ‖ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2‖ ≤
      B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) := by
    filter_upwards [haeQd] with p hp
    have hz : 0 < p.1 := hp.1
    have hθ1 : 0 < p.2 := hp.2.1
    have hθ2 : p.2 < Real.pi / 2 := hp.2.2
    rw [Real.norm_eq_abs]
    have hAZnn : 0 ≤ ρ p.1 p.2 * |X p.1 p.2| * |Z p.1 p.2| :=
      mul_nonneg (mul_nonneg (hρnn p.1 p.2 hz hθ1 hθ2) (abs_nonneg _)) (abs_nonneg _)
    calc |ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2|
        = (ρ p.1 p.2 * |X p.1 p.2| * |Z p.1 p.2|) * |Y p.1 p.2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hρnn p.1 p.2 hz hθ1 hθ2)]
          ring
      _ ≤ (ρ p.1 p.2 * |X p.1 p.2| * |Z p.1 p.2|) * B :=
          mul_le_mul_of_nonneg_left (hY p.1 p.2 hz hθ1 hθ2) hAZnn
      _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) * B :=
          mul_le_mul_of_nonneg_right (hpt p.1 p.2 hz hθ1 hθ2) hB
      _ = B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) := by ring
  have hdomAbs : ∀ᵐ p ∂μP, |ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ≤
      B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) := by
    simpa only [Real.norm_eq_abs] using hdom
  -- Measurability and square-integrability of the two square roots.
  have hAmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)) μP :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hintA.aestronglyMeasurable
  have hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) μP :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hintF.aestronglyMeasurable
  have hAsq : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2) ^ 2) μP :=
    hintA.congr (Filter.Eventually.of_forall
      (fun p => (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k A p.1 p.2)).symm))
  have hFsq : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ^ 2) μP :=
    hintF.congr (Filter.Eventually.of_forall
      (fun p => (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 6 f p.1 p.2)).symm))
  have hAlp : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)) 2 μP :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hAsq
  have hFlp : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) 2 μP :=
    (MeasureTheory.memLp_two_iff_integrable_sq hFmeas).mpr hFsq
  -- The product of the two square roots is integrable (Hölder), so the dominating
  -- function of the slot pairing is integrable.
  have hprodint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) μP :=
    MeasureTheory.memLp_one_iff_integrable.mp (hAlp.mul hFlp)
  have hdomInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2))) μP :=
    hprodint.const_mul B
  have hmeasXYZ : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) μP :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontXYZ
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) μP :=
    hdomInt.mono' hmeasXYZ hdom
  -- Cauchy–Schwarz for the two square roots, with the `HkSq` identification.
  have hcs := Work.Blocks.IMC.cs_integral_mul_le μP hAmeas hFmeas hAsq hFsq
  have eA : (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2) ^ 2 ∂μP)
      = Work.Spaces.HkSq α k A := by
    rw [← hvalA]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun p => Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k A p.1 p.2)))
  have eF : (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ^ 2 ∂μP)
      = Work.Spaces.HkSq α 6 f := by
    rw [← hvalF]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun p => Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 6 f p.1 p.2)))
  have hle : (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ∂μP) ≤
      Real.sqrt (Work.Spaces.HkSq α k A) * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
    rw [eA, eF] at hcs
    exact le_trans (le_abs_self _) hcs
  have h1 : |∫ p, ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂μP| ≤
      B * (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ∂μP) := by
    calc |∫ p, ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂μP|
        ≤ ∫ p, |ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂μP :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ p, B * (Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) ∂μP :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun p => abs_nonneg _)) hdomInt hdomAbs
      _ = B * (∫ p, Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2) ∂μP) :=
          MeasureTheory.integral_const_mul B
            (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α k A p.1 p.2)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2))
  exact ⟨hInt, le_trans h1 (mul_le_mul_of_nonneg_left hle hB)⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Shared tools for the mismatch coefficient estimate

Pointwise AM–GM tools, continuity of the weighted slot densities and the single-slot
integrability/bound lemmas used by the three index cases of
`Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCoefCase`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

/-- The product measure on the quadrant `[0,∞) × [0,π/2]`. -/
def pm : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- `2 |a| |b| ≤ lam·a² + b²/lam` for `lam > 0`. -/
lemma two_abs_mul_le (lam a b : ℝ) (hlam : 0 < lam) :
    2 * |a| * |b| ≤ lam * a ^ 2 + b ^ 2 / lam := by
  have h : (0 : ℝ) ≤ (lam * |a| - |b|) ^ 2 := sq_nonneg _
  have h1 : 2 * (lam * |a|) * |b| ≤ (lam * |a|) ^ 2 + |b| ^ 2 := by nlinarith [h]
  have h1' : 2 * lam * |a| * |b| ≤ lam ^ 2 * a ^ 2 + b ^ 2 := by
    have h2 := h1
    rw [mul_pow, sq_abs a, sq_abs b, mul_assoc] at h2
    nlinarith [h2]
  have h3 : (2 * lam * |a| * |b|) / lam ≤ (lam ^ 2 * a ^ 2 + b ^ 2) / lam :=
    div_le_div_of_nonneg_right h1' hlam.le
  have h4 : (2 * lam * |a| * |b|) / lam = 2 * |a| * |b| := by
    field_simp
  have h5 : (lam ^ 2 * a ^ 2 + b ^ 2) / lam = lam * a ^ 2 + b ^ 2 / lam := by
    field_simp
  rwa [h4, h5] at h3

/-- **The pointwise AM–GM majorant**: `W |a| |b| |c| ≤ ½ (lam (W a²) + lam⁻¹ (W b² c²))`. -/
lemma pt_le (W a b c lam : ℝ) (hW : 0 ≤ W) (hlam : 0 < lam) :
    W * |a| * (|b| * |c|) ≤ (1 / 2) * (lam * (W * a ^ 2) + lam⁻¹ * (W * (b ^ 2 * c ^ 2))) := by
  have h2 := two_abs_mul_le lam a (|b| * |c|) hlam
  have h3 : (|b| * |c|) ^ 2 / lam = lam⁻¹ * (b ^ 2 * c ^ 2) := by
    rw [mul_pow, sq_abs, sq_abs, div_eq_mul_inv]
    ring
  have h2' : 2 * |a| * (|b| * |c|) ≤ lam * a ^ 2 + (|b| * |c|) ^ 2 / lam := by
    simpa only [abs_mul, abs_of_nonneg (abs_nonneg b), abs_of_nonneg (abs_nonneg c)] using h2
  have h4 : 2 * |a| * (|b| * |c|) ≤ lam * a ^ 2 + lam⁻¹ * (b ^ 2 * c ^ 2) := by
    rw [← h3]; exact h2'
  have hab : |a| * (|b| * |c|) ≤ (1 / 2) * (lam * a ^ 2 + lam⁻¹ * (b ^ 2 * c ^ 2)) := by linarith
  have h5 := mul_le_mul_of_nonneg_left hab hW
  calc W * |a| * (|b| * |c|) = W * (|a| * (|b| * |c|)) := by ring
    _ ≤ W * ((1 / 2) * (lam * a ^ 2 + lam⁻¹ * (b ^ 2 * c ^ 2))) := h5
    _ = (1 / 2) * (lam * (W * a ^ 2) + lam⁻¹ * (W * (b ^ 2 * c ^ 2))) := by ring

/-- `√(x²+1) ≤ x+1` for `x ≥ 0`. -/
lemma sqrt_sq_add_one_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ 2 + 1) ≤ x + 1 := by
  have h : x ^ 2 + 1 ≤ (x + 1) ^ 2 := by nlinarith
  calc Real.sqrt (x ^ 2 + 1) ≤ Real.sqrt ((x + 1) ^ 2) := Real.sqrt_le_sqrt h
    _ = x + 1 := Real.sqrt_sq (by linarith)


/-- Continuity of `w(z)²` on the open quadrant. -/
lemma contOn_w : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
    Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div (((continuousOn_const.add continuousOn_id).pow 2).pow 2)
      ((continuousOn_id.pow 2).pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz))
  have h2 : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2 := by
    funext z
    rw [Work.Spaces.w, div_pow]
  have h3 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    rw [h2]; exact h1
  exact h3.comp continuous_fst.continuousOn (fun p hp => hp.1)

/-- Continuity of `sin(2θ)^{-γ}` on the open quadrant. -/
lemma contOn_sig (α : ℝ) : ContinuousOn
    (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
    Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  refine hsin.rpow_const ?_
  intro p hp
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
    (by linarith [hp.2.2, Real.pi_pos])))

/-- Continuity of the weighted slot density of a mixed slot. -/
lemma contOn_dens {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
  (contOn_w.mul (contOn_sig α)).mul ((hsm.mixed j i).continuousOn.pow 2)

/-- **One mixed slot with its `σ^{-γ}` weight**: integrability on the product measure and the
`ℋ^k`-bound. -/
lemma mixed_slot_le {α : ℝ} (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) pm ∧
      (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 ∂pm) ≤ Work.Spaces.HkSq α k f := by
  have hbase := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := k) hsm hmem
  have hbase' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k f p.1 p.2) pm := hbase.1
  have hval' : (∫ p, Work.Spaces.HkIntegrand α k f p.1 p.2 ∂pm) = Work.Spaces.HkSq α k f :=
    hbase.2
  have hpt : ∀ᵐ p ∂pm, (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hid : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [mul_pow, Work.FTS.TransportS.T3BadAux.Wt_sq_eq (α := α) (z := z) (θ := θ) hθI]
      ring
    rw [hid]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij
  have hnn : ∀ᵐ p ∂pm, 0 ≤ (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)) (sq_nonneg _)
    exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) pm := by
    refine MeasureTheory.Integrable.mono' hbase'
      (Work.Spaces.aesm_of_continuousOn_Qd _ (contOn_dens hsm j i)) ?_
    filter_upwards [hpt, hnn] with p hp hpn
    rw [Real.norm_eq_abs, abs_of_nonneg hpn]
    exact hp
  refine ⟨hint, ?_⟩
  rw [← hval']
  exact MeasureTheory.integral_mono_ae hint hbase' hpt

/-- **A pointwise majorant gives the integral bound**. -/
lemma abs_integral_le_of_pointwise {μ : MeasureTheory.Measure (ℝ × ℝ)}
    {F M : ℝ × ℝ → ℝ} (hM : MeasureTheory.Integrable M μ)
    (haesm : MeasureTheory.AEStronglyMeasurable F μ)
    (h : ∀ᵐ p ∂μ, |F p| ≤ M p) :
    |∫ p, F p ∂μ| ≤ ∫ p, M p ∂μ := by
  have hFint : MeasureTheory.Integrable F μ := by
    refine MeasureTheory.Integrable.mono' hM haesm ?_
    filter_upwards [h] with p hp
    rwa [Real.norm_eq_abs]
  calc |∫ p, F p ∂μ| ≤ ∫ p, |F p| ∂μ := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ p, M p ∂μ := MeasureTheory.integral_mono_ae hFint.abs hM h

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.mixedSlotL2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Auxiliary facts for the weighted mixed slot `(D_z^j D_θ f · W)²`

The two pieces of bookkeeping needed to turn the abstract "single slot" machinery
(`Work.Spaces.sq_le_HkIntegrand_mixed`, `intSlotLeHkSq`) into the statement below:

* the slot `(D_z^jD_θ f · W)²` is continuous on the open quadrant, so its `z`-marginal is
  a.e. strongly measurable and is dominated by the (integrable) marginal of `HkIntegrand`;
* the square of the weight factorises as `(w · s^{-γ/2})² = w² · s^{-γ}`, which identifies
  the slot's integral with the `θw = s^{-γ}` instance of `intSlotLeHkSq`. -/

/-- `sin(2θ) ≥ 0` on `[0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
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

/-- The squared weighted mixed slot `(D_z^jD_θ f · W)²` is continuous on the open quadrant. -/
private lemma contOn_mixed_sq {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
  ((((hsm.mixed j 1).forall 0).continuousOn.mul (continuousOn_Wt_Q0 α)) |>.pow 2)

/-- The `z`-marginal of a weighted mixed slot is a.e. strongly measurable. -/
private lemma aesm_mixed_slot (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _
    (contOn_mixed_sq hsm j α)).integral_prod_right'
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The square of the weight factorises: `(w · s^{-γ/2})² = w² · s^{-γ}` for `s ≥ 0`. -/
private lemma Wt_sq_eq (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The weighted mixed slot, in the `θw = s^{-γ}` form used by `intSlotLeHkSq`. -/
private lemma mixed_slot_sq_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ)
    (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j 1 f z θ) ^ 2 := by
  rw [mul_pow, Wt_sq_eq α z θ hs]
  ring

theorem mixedSlotL2 : ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (j : ℕ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → j ≤ 5 →
      MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f := by
  intro α _hα f j hsm hmem hj
  constructor
  · -- Integrability of the `z`-marginal, by domination by the `ℋ⁶`-integrand.
    refine MeasureTheory.Integrable.mono' hmem.2 (aesm_mixed_slot α hsm j) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
    have hAn : ‖∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2‖
        = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
      Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
    have hle : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ 1 j le_rfl (by omega))
    rw [hAn]
    exact hle
  · -- The value of the integral, via the `θw = sin(2θ)^{-γ}` slot of `intSlotLeHkSq`.
    have hEq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j 1 f z θ) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z _
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      exact mixed_slot_sq_eq α f j z θ (sin_two_nonneg_Iθ hθ)
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j 1 f z θ) ^ 2 :=
          MeasureTheory.integral_congr_ae hEq
      _ ≤ Work.Spaces.HkSq α 6 f :=
          (intSlotLeHkSq α hmem).2 j 1 le_rfl (by omega)
            (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            (fun θ hθ => Real.rpow_nonneg
              (sin_two_nonneg_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _)
            (fun _ _ => le_refl _)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
end
-- ===== merged: Submission.Work.FTS.StrongPersist.QangAe6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `QangAe6` — the level-six `z`-calculus of the angular moments, almost everywhere

`Work.Elliptic.Qang g i z = ∫_θ Kθ(θ)·(D_z^i g)(z,θ) dθ` is the `i`-th angular moment of `g`.
The level-four chain of `Work.FTS.OpenPkg.QangOpen` proves, for a datum which is `C^∞` on the
open quadrant and lies in `ℋ⁴`, that

  `D_z^i (Qang g 0) = Qang g i`  almost everywhere, for `i ≤ 4`

(`DzdIter_Qang_ae_open`), while `QangDiff6` of this directory upgrades the two ingredients of
that chain — the `z`-differentiation of the moments and their continuity on `(0,∞)` — to
levels `j ≤ 4` and `j ≤ 5` respectively, for a datum in `ℋ⁶`.

Here we assemble the two: the *pointwise* identity `D_z^i (Qang g 0) = Qang g i` for `i ≤ 5`
is the abstract induction `DzdIter_eq_of_hasDerivAt'` run on the level-`j ≤ 4` derivative
facts, and the last level `i = 6` follows by transporting the *level-four* a.e. statement to
the shift `D_z²g` (via `Qang g (k+2) = Qang (D_z²g) k`, `Qang_DzIter_two_shift`), which reads

  `D_z⁴ (Qang g 2) = Qang g 6`  a.e.,

and then replacing `Qang g 2` by `D_z²(Qang g 0)` on `(0,∞)` (the pointwise identity at level
`i = 2`), i.e. `D_z⁴(Qang g 2) = D_z⁶(Qang g 0)`.

The only Fubini/Hardy input is inherited: `HkMem α 6 g` gives `HkMem α 4 (D_z²g)`
(`HkMem_Dz_of_smoothOpen` twice), which is exactly what `DzdIter_Qang_ae_open` consumes.
-/

namespace Work.FTS.StrongPersist

open scoped Topology

/-! ## Transport of the `z ∂_z`-calculus along an equality on `(0,∞)` -/

/-- If two functions of `z` agree on the open half-line `(0,∞)`, then their `z∂_z`-derivatives
agree at every point of `(0,∞)` (the half-line is a neighbourhood). -/
theorem Dzd_congr_Ioi {u v : ℝ → ℝ} (h : ∀ y, 0 < y → u y = v y) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Dzd u z = Work.Elliptic.Dzd v z := by
  have hev : u =ᶠ[nhds z] v := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact h y hy
  rw [Work.Elliptic.Dzd, Work.Elliptic.Dzd, hev.deriv_eq]

/-- If two functions of `z` agree on the open half-line `(0,∞)`, then so do all their
iterated `z∂_z`-derivatives. -/
theorem DzdIter_congr_Ioi {u v : ℝ → ℝ} (h : ∀ y, 0 < y → u y = v y) :
    ∀ k : ℕ, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter k u z = Work.Elliptic.DzdIter k v z := by
  intro k
  induction k with
  | zero => intro z hz; exact h z hz
  | succ k ih =>
      intro z hz
      rw [Work.Elliptic.DzdIter_succ]
      exact Dzd_congr_Ioi (fun y hy => ih y hy) hz

/-- `DzdIter` is additive in its order: `DzdIter (m+n) u = DzdIter m (DzdIter n u)`. -/
theorem DzdIter_add (m n : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter (m + n) u
      = Work.Elliptic.DzdIter m (Work.Elliptic.DzdIter n u) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show (m + 1) + n = (m + n) + 1 from Nat.succ_add m n]
      show Work.Elliptic.Dzd (Work.Elliptic.DzdIter (m + n) u)
        = Work.Elliptic.Dzd (Work.Elliptic.DzdIter m (Work.Elliptic.DzdIter n u))
      rw [ih]

/-! ## The abstract induction: a divided derivative at every `z > 0` gives all iterates -/

/-- **Pointwise `z∂_z`-calculus from divided derivatives.**  If `u = Φ 0` and
`(Φ j)' z = Φ (j+1) z / z` for every `j ≤ N` and every `z > 0`, then
`D_z^i u = Φ i` for every `i ≤ N+1` at every `z > 0`.

(`D_z = z∂_z`, so `D_z^{i+1} u = z∂_z(D_z^i u)`; the induction step replaces `D_z^i u` by `Φ i`
in a neighbourhood of `z` — which is legitimate because `z > 0` — and then uses the divided
derivative of `Φ i`, the division by `z` being undone by the multiplication by `z`.) -/
theorem DzdIter_eq_of_hasDerivAt' {u : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ} (N : ℕ)
    (h0 : ∀ z, u z = Φ 0 z)
    (hder : ∀ j ≤ N, ∀ z, 0 < z → HasDerivAt (Φ j) (Φ (j + 1) z / z) z) :
    ∀ i ≤ N + 1, ∀ z, 0 < z → Work.Elliptic.DzdIter i u z = Φ i z := by
  intro i
  induction i with
  | zero => intro _ z _; exact h0 z
  | succ i ih =>
      intro hi z hz
      have hprev : Work.Elliptic.DzdIter i u =ᶠ[nhds z] Φ i := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih (by omega) w hw
      rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
      rw [hprev.deriv_eq, (hder i (by omega) z hz).deriv]
      rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hz)]

/-! ## The two level-six inputs -/

/-- The angular moments of the level-six datum are differentiable at every `z > 0` up to order
`j ≤ 4`, so the identity `D_z^i (Qang g 0) = Qang g i` holds **pointwise** for `i ≤ 5`. -/
theorem Qang_DzdIter_pointwise {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ i ≤ 5, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g i z :=
  DzdIter_eq_of_hasDerivAt' 4 (fun _ => rfl)
    (fun j hj z hz => (QangDiff6 hO hmem).1 j hj z hz)

/-- **The level-six identity transported to the shift `D_z²g`.**  The level-four a.e. theorem
`DzdIter_Qang_ae_open` applied to `D_z²g ∈ ℋ⁴` (which is `HkMem_Dz_of_smoothOpen` twice) gives
`D_z^i (Qang (D_z²g) 0) = Qang (D_z²g) i` a.e.; rewriting both sides with
`Qang_DzIter_two_shift` (`Qang g (k+2) = Qang (D_z²g) k`) yields the identity for the moments of
`g` shifted by two. -/
theorem Qang_DzdIter_shift_ae {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 2 z) z
        = Work.Elliptic.Qang g (i + 2) z := by
  -- `D_z²g` lies in `ℋ⁴`: descend twice along the `D_z`-shift.
  have hmem5 : Work.Spaces.HkMem α 5 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 5 hO hmem
  have hmem4₂ : Work.Spaces.HkMem α 4 (Work.Spaces.DzIter 2 g) := by
    have h : Work.Spaces.HkMem α 4 (Work.Spaces.Dz (Work.Spaces.Dz g)) :=
      Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hO.Dz hmem5
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h
  have hO₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 2 g) := hO.DzIter 2
  filter_upwards [Work.FTS.OpenPkg.QangOpen.DzdIter_Qang_ae_open hO₂ hmem4₂] with z hz
  intro hzpos i hi
  have h1 := hz hzpos i hi
  have hfun : (fun z => Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) 0 z)
      = fun z => Work.Elliptic.Qang g 2 z :=
    funext (fun z => (congrFun (Qang_DzIter_two_shift g 0) z).symm)
  rw [hfun] at h1
  rw [← congrFun (Qang_DzIter_two_shift g i) z] at h1
  exact h1

/-! ## The target -/

theorem QangAe6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 7,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z := by
  -- the pointwise identity at every level `i ≤ 5`
  have hpoint := Qang_DzdIter_pointwise hO hmem
  -- `Qang g 2` agrees on `(0,∞)` with `D_z²(Qang g 0)`, whence the fourth iterate of the
  -- former is the sixth iterate of the latter
  have htransfer : ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter 4 (fun w => Work.Elliptic.Qang g 2 w) z
        = Work.Elliptic.DzdIter 6 (fun w => Work.Elliptic.Qang g 0 w) z := by
    intro z hz
    have h2 : ∀ y, 0 < y → (fun w => Work.Elliptic.Qang g 2 w) y
        = Work.Elliptic.DzdIter 2 (fun w => Work.Elliptic.Qang g 0 w) y :=
      fun y hy => (hpoint 2 (by norm_num) y hy).symm
    calc Work.Elliptic.DzdIter 4 (fun w => Work.Elliptic.Qang g 2 w) z
        = Work.Elliptic.DzdIter 4
            (Work.Elliptic.DzdIter 2 (fun w => Work.Elliptic.Qang g 0 w)) z :=
          DzdIter_congr_Ioi h2 4 z hz
      _ = Work.Elliptic.DzdIter (4 + 2) (fun w => Work.Elliptic.Qang g 0 w) z :=
          congrFun (DzdIter_add 4 2 (fun w => Work.Elliptic.Qang g 0 w)).symm z
      _ = Work.Elliptic.DzdIter 6 (fun w => Work.Elliptic.Qang g 0 w) z := by norm_num
  filter_upwards [Qang_DzdIter_shift_ae hO hmem] with z hz
  intro hzpos i hi
  have hi6 : i ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rcases Nat.lt_or_ge i 6 with hlt | hge
  · exact hpoint i (by omega) z hzpos
  · have hieq : i = 6 := by omega
    subst hieq
    exact (htransfer z hzpos).symm.trans (hz hzpos 4 (by decide))

end Work.FTS.StrongPersist
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Work.FTS.TransportS.SlotT2


theorem Xn_sq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α g ^ 2 = Work.Spaces.HkSq α 4 g := by
  rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
    Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]

theorem one_div_sqrt_gam_sub_one {α : ℝ} (hα : 0 < α) :
    1 / Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  have h2 : Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt α / Real.sqrt 10 := by
    rw [Work.Spaces.gam_sub_one α, Real.sqrt_div hα.le (10:ℝ)]
  rw [h2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow (10:ℝ), Real.rpow_neg hα.le, one_div, inv_div]
  ring

/-- `SmoothQuad` implies `SmoothOpen`. -/
theorem SmoothQuad.smoothOpen {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  refine hg.mono ?_
  intro p hp
  rw [Work.FTS.EllipticEst.mem_Q0] at hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩⟩

/-- The double sum of the binomial coefficients is at most `256` (for slots `a, b ≤ 4`). -/
theorem choose_mul_le {a b a1 b1 : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) :
    (a.choose a1 : ℝ) * (b.choose b1 : ℝ) ≤ 256 := by
  have h1 : a.choose a1 ≤ 2 ^ a := Nat.choose_le_two_pow a a1
  have h2 : b.choose b1 ≤ 2 ^ b := Nat.choose_le_two_pow b b1
  have hpa : 2 ^ a ≤ 16 := by
    calc 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) ha
      _ = 16 := by norm_num
  have hpb : 2 ^ b ≤ 16 := by
    calc 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hb
      _ = 16 := by norm_num
  have h1' : (a.choose a1 : ℝ) ≤ 16 := by exact_mod_cast le_trans h1 hpa
  have h2' : (b.choose b1 : ℝ) ≤ 16 := by exact_mod_cast le_trans h2 hpb
  have h1'' : (0:ℝ) ≤ (a.choose a1 : ℝ) := Nat.cast_nonneg _
  have h2'' : (0:ℝ) ≤ (b.choose b1 : ℝ) := Nat.cast_nonneg _
  nlinarith [h1', h2', h1'', h2'']

end Work.FTS.TransportS.T2Sup
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.Ptwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2

/-- `η ≤ γ`. -/
theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith [hα, Work.Spaces.eta_lt_one]

/-! ## The three pointwise majorants -/

/-- **The "sup on the coefficient" pointwise majorant.**  If `|X| ≤ KF` on the open quadrant
and `G`, `Y` are canonical `q`-slots of `g`, then `canonW q |X| |G| |Y| ≤ KF · HkIntegrand g`. -/
theorem canonW_mul_abs_le_slotW {α q KF : ℝ} {X G Y g : ℝ → ℝ → ℝ}
    (hS2 : SlotWo α q G g) (hS3 : SlotWo α q Y g) (hKF : 0 ≤ KF)
    (hXb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |X z θ| ≤ KF) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |X z θ| * |G z θ| * |Y z θ|
        ≤ KF * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hGsq : canonW q z θ * (G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    hS2 z θ hz hθ hθ2
  have hYsq : canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    hS3 z θ hz hθ hθ2
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hGY : canonW q z θ * |G z θ| * |Y z θ| ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    rw [canonW_mul_abs_eq (q := q) (G := G) (Y := Y) hθI]
    calc Real.sqrt (canonW q z θ * (G z θ) ^ 2)
          * Real.sqrt (canonW q z θ * (Y z θ) ^ 2)
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
          mul_le_mul (Real.sqrt_le_sqrt hGsq) (Real.sqrt_le_sqrt hYsq)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Work.Spaces.HkIntegrand α 4 g z θ := Real.mul_self_sqrt hHnn
  calc canonW q z θ * |X z θ| * |G z θ| * |Y z θ|
      = |X z θ| * (canonW q z θ * |G z θ| * |Y z θ|) := by ring
    _ ≤ KF * Work.Spaces.HkIntegrand α 4 g z θ :=
        mul_le_mul (hXb z θ hz hθ hθ2) hGY
          (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _)) hKF

/-- **The σ-gain pointwise majorant.**  If `|X| ≤ CK · sin(2θ)` on the open quadrant with
`CK ≥ 0`, `q ≤ 1 + η`, and `G`, `Y` are canonical `η`- resp. `γ`-slots of `g`, then
`canonW q |X| |G| |Y| ≤ CK · HkIntegrand g`. -/
theorem canonW_mul_abs_le_slotSigma {α q CK : ℝ} {X G Y g : ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hCK : 0 ≤ CK) (hXb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |X z θ| ≤ CK * Real.sin (2 * θ))
    (hq : q ≤ 1 + Work.Spaces.eta)
    (hS2 : SlotWo α Work.Spaces.eta G g) (hS3 : SlotWo α (Work.Spaces.gam α) Y g) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |X z θ| * |G z θ| * |Y z θ|
        ≤ CK * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo ⟨hθ, hθ2⟩
  have hσ1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
  have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hGnn : 0 ≤ canonW q z θ * |G z θ| * |Y z θ| :=
    mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _)
  have hGsq : canonW Work.Spaces.eta z θ * (G z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := hS2 z θ hz hθ hθ2
  have hYsq : canonW (Work.Spaces.gam α) z θ * (Y z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := hS3 z θ hz hθ hθ2
  have hsplit : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
      = Real.sin (2 * θ) ^ (1 - q) := by
    rw [show (1:ℝ) - q = 1 + (-q) by ring, Real.rpow_add hσ0, Real.rpow_one]
  have hmix : Real.sin (2 * θ) ^ (1 - q) ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
    rpow_one_sub_le hσ0 hσ1 hq
  have hGY : Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h1 : Real.sin (2 * θ) * canonW q z θ
        = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (1 - q) := by
      rw [canonW]
      rw [show Real.sin (2 * θ) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-q))
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)) from by
        ring]
      rw [hsplit]
    have h3 : (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (1 - q)
        ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
      mul_le_mul_of_nonneg_left hmix hw
    have hstep1 : Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
            * (|G z θ| * |Y z θ|) := by
      rw [show Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
          = (Real.sin (2 * θ) * canonW q z θ) * (|G z θ| * |Y z θ|) from by ring, h1]
      exact mul_le_mul_of_nonneg_right h3 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hGYabs : |G z θ| * |Y z θ| ≤ (G z θ ^ 2 + Y z θ ^ 2) / 2 := by
      have h := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add (G z θ) (Y z θ)
      rwa [abs_mul] at h
    have hstep2 : (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
          * (|G z θ| * |Y z θ|)
        ≤ (1 / 2) * ((canonW Work.Spaces.eta z θ * (G z θ) ^ 2)
            + (canonW Work.Spaces.eta z θ * (Y z θ) ^ 2)) := by
      show (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
          * (|G z θ| * |Y z θ|)
        ≤ (1 / 2) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (G z θ) ^ 2
            + (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (Y z θ) ^ 2)
      refine le_trans (mul_le_mul_of_nonneg_left hGYabs
        (mul_nonneg hw (Real.rpow_nonneg hσ0.le _))) ?_
      rw [show (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
            * ((G z θ ^ 2 + Y z θ ^ 2) / 2)
          = (1 / 2) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (G z θ) ^ 2
            + (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (Y z θ) ^ 2) from by ring]
    have h3' : canonW Work.Spaces.eta z θ * (Y z θ) ^ 2
        ≤ canonW (Work.Spaces.gam α) z θ * (Y z θ) ^ 2 := by
      have hle : Real.sin (2 * θ) ^ (-Work.Spaces.eta)
          ≤ Real.sin (2 * θ) ^ (-Work.Spaces.gam α) :=
        rpow_neg_le_neg hσ0 hσ1 (eta_le_gam hα)
      rw [canonW, canonW]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle hw) (sq_nonneg _)
    exact le_trans (le_trans hstep1 hstep2) (by linarith [hGsq, le_trans h3' hYsq])
  calc canonW q z θ * |X z θ| * |G z θ| * |Y z θ|
      = |X z θ| * (canonW q z θ * |G z θ| * |Y z θ|) := by ring
    _ ≤ (CK * Real.sin (2 * θ)) * (canonW q z θ * |G z θ| * |Y z θ|) :=
        mul_le_mul_of_nonneg_right (hXb z θ hz hθ hθ2) hGnn
    _ = CK * (Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)) := by ring
    _ ≤ CK * Work.Spaces.HkIntegrand α 4 g z θ := mul_le_mul_of_nonneg_left hGY hCK

/-- **The "sup on a `g`-slot" pointwise majorant.**  If the middle factor is bounded by `KG`
and `F`, `Y` are canonical `q`-slots of `f` resp. `g`, then
`canonW q |F| |G| |Y| ≤ KG · √(HkIntegrand f) · √(HkIntegrand g)`. -/
theorem canonW_mul_abs_le_slotG {α q KG : ℝ} {F Gm Y f g : ℝ → ℝ → ℝ}
    (hS1 : SlotWo α q F f) (hS3 : SlotWo α q Y g) (hKG : 0 ≤ KG)
    (hGb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Gm z θ| ≤ KG) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |F z θ| * |Gm z θ| * |Y z θ|
        ≤ KG * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hFsq : canonW q z θ * (F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    hS1 z θ hz hθ hθ2
  have hYsq : canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    hS3 z θ hz hθ hθ2
  have hFY : canonW q z θ * |F z θ| * |Y z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) := by
    rw [canonW_mul_abs_eq (q := q) (G := F) (Y := Y) hθI]
    exact mul_le_mul (Real.sqrt_le_sqrt hFsq) (Real.sqrt_le_sqrt hYsq)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc canonW q z θ * |F z θ| * |Gm z θ| * |Y z θ|
      = (canonW q z θ * |F z θ| * |Y z θ|) * |Gm z θ| := by ring
    _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) * KG :=
        mul_le_mul hFY (hGb z θ hz hθ hθ2) (abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = KG * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by ring

end Work.FTS.TransportS.T2Sup
end
end
-- ===== merged: Submission.Work.FTS.TransportS.t3SlotGuarded =====
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
set_option maxHeartbeats 2000000


end Work.FTS.TransportS
end
end
