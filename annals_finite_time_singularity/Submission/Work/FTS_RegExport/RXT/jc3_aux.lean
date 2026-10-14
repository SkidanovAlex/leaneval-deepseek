import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.Apriori.Limit.HkNorm_le_of_tendstoLocUnif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)


end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.ClassC.exists_linear_selector =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

/-- **Linear selection from a linear relation.**  Let `C` be a class of profiles that contains `0`
and is closed under the operation `(g, g') ↦ g + c • g'` (hence, taking `c = 1` and, with `0 ∈ C`,
`c` arbitrary, it is a linear subspace), and let `P` be a relation which is likewise `0`-inhabited
and closed under the same operation in both variables.  If every `g ∈ C` is `P`-related to some
`Ψ`, then there is a *linear* selector `E` with `P g (E g)` for every `g ∈ C`.

The proof: the pairs `(g, Ψ)` with `g ∈ C` and `P g Ψ` form a submodule `S ≤ Fn × Fn`; its
first-coordinate projection `π : S →ₗ[ℝ] Fn` is onto the subspace `D = {g | C g}`, and since every
vector space over `ℝ` is a free (hence projective) module, `π` splits: there is a linear
`σ : D →ₗ[ℝ] S` with `π ∘ σ = id`.  Composing with the second coordinate gives a linear selector
`E₀ : D →ₗ[ℝ] Fn` over `D`; it is extended to all of `Fn` by `LinearMap.exists_extend`. -/
theorem exists_linear_selector {α : ℝ} {C : Work.FTS.Galerkin.Fn → Prop}
    {P : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → Prop}
    (hC0 : C 0)
    (hClin : ∀ g g' : Work.FTS.Galerkin.Fn, ∀ c : ℝ, C g → C g' → C (g + c • g'))
    (hP0 : P 0 0)
    (hPlin : ∀ g g' Ψ Ψ' : Work.FTS.Galerkin.Fn, ∀ c : ℝ, C g → C g' →
      P g Ψ → P g' Ψ' → P (g + c • g') (Ψ + c • Ψ'))
    (hex : ∀ g, C g → ∃ Ψ, P g Ψ) :
    ∃ E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn, ∀ g, C g → P g (E g) := by
  -- `C` is closed under addition and under scalar multiplication.
  have hCadd : ∀ g g', C g → C g' → C (g + g') := by
    intro g g' hg hg'
    have h := hClin g g' 1 hg hg'
    simpa using h
  have hCsmul : ∀ (c : ℝ) g, C g → C (c • g) := by
    intro c g hg
    have h := hClin 0 g c hC0 hg
    simpa using h
  -- The graph of the relation, restricted to `C`, is a submodule of `Fn × Fn`.
  let S : Submodule ℝ (Work.FTS.Galerkin.Fn × Work.FTS.Galerkin.Fn) :=
    { carrier := {x | C x.1 ∧ P x.1 x.2}
      zero_mem' := ⟨hC0, hP0⟩
      add_mem' := by
        rintro ⟨g, Ψ⟩ ⟨g', Ψ'⟩ ⟨hg, hP⟩ ⟨hg', hP'⟩
        refine ⟨hCadd g g' hg hg', ?_⟩
        have h := hPlin g g' Ψ Ψ' 1 hg hg' hP hP'
        simpa using h
      smul_mem' := by
        rintro c ⟨g, Ψ⟩ ⟨hg, hP⟩
        refine ⟨hCsmul c g hg, ?_⟩
        have h := hPlin 0 g 0 Ψ c hC0 hg hP0 hP
        simpa using h }
  -- First-coordinate projection of `S`, and its range `D`.
  let π : S →ₗ[ℝ] Work.FTS.Galerkin.Fn :=
    (LinearMap.fst ℝ Work.FTS.Galerkin.Fn Work.FTS.Galerkin.Fn).comp S.subtype
  let D : Submodule ℝ Work.FTS.Galerkin.Fn := LinearMap.range π
  have hmemD : ∀ g, g ∈ D ↔ C g := by
    intro g
    constructor
    · rintro ⟨x, hx⟩
      have hx' : x.1.1 = g := hx
      rw [← hx']
      exact x.2.1
    · intro hg
      obtain ⟨Ψ, hP⟩ := hex g hg
      exact ⟨⟨(g, Ψ), hg, hP⟩, rfl⟩
  let πD : S →ₗ[ℝ] D := π.codRestrict D (fun x => LinearMap.mem_range_self π x)
  have hsurj : Function.Surjective πD := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  -- `D` is a vector space over `ℝ`, hence free, hence projective.
  haveI : Module.Free ℝ D := Module.Free.of_divisionRing ℝ D
  -- Split the surjection `πD`.
  obtain ⟨σ, hσ⟩ := πD.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let E₀ : D →ₗ[ℝ] Work.FTS.Galerkin.Fn :=
    ((LinearMap.snd ℝ Work.FTS.Galerkin.Fn Work.FTS.Galerkin.Fn).comp S.subtype).comp σ
  have hE₀ : ∀ y : D, P y (E₀ y) := by
    intro y
    have hσy : πD (σ y) = y := LinearMap.congr_fun hσ y
    have h1 : (σ y).1.1 = y.1 := by
      have h := congrArg Subtype.val hσy
      simpa [πD, π] using h
    have h3 : P (σ y).1.1 (σ y).1.2 := (σ y).2.2
    rw [← h1]
    exact h3
  -- Extend the selector from `D` to the whole space.
  obtain ⟨E, hE⟩ := LinearMap.exists_extend E₀
  refine ⟨E, fun g hg => ?_⟩
  have hgD : g ∈ D := (hmemD g).mpr hg
  have hEeq : E g = E₀ ⟨g, hgD⟩ := by
    have := LinearMap.congr_fun hE ⟨g, hgD⟩
    simpa using this
  rw [hEeq]
  exact hE₀ ⟨g, hgD⟩

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.fstar_tendsto_atTop_zero_of_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Vanishing of the angular moment `F_* g` at `z = ∞`.**  For a profile `g` which is
`C^∞` on the open quadrant, honestly in `ℋ⁷` and decaying in `z` at every angle
`θ ∈ Iθ = [0,π/2]`, the angular moment `F_* g z = ∫_θ g z θ sin θ cos²θ` tends to `0` as
`z → ∞`.

Route.  Fix `θ ∈ (0,π/2)`.  The radial Hardy inequality (`Work.FTS.H2.HQ.HardyZQ`, packaged as
`zTail_hardy`) bounds the *value* `(g z θ)²` uniformly in `z > 0` by the weighted `L²`-mass of
the radial derivative,

  `(g z θ)² ≤ zTailR g θ`,   `zTailR g θ = (∫⁻_{s ∈ Iz} ofReal ((D_z g(s,θ))² w(s)²)).toReal`,

and `HkMem α 7 g` together with Tonelli (`zTail_lintegral_le_HkSq`) gives
`∫⁻_θ zTail g θ ≤ ofReal (HkSq α 7 g) < ∞`.  Hence `zTailR g` is an integrable function of `θ`
with `1 + zTailR g` dominating `θ ↦ g z θ · sin θ cos²θ` for all `z > 0`; the pointwise decay
`hdec` gives the a.e. pointwise convergence, and dominated convergence
(`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`) yields the claim. -/
theorem fstar_tendsto_atTop_zero_of_classC {α : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 7 g)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun z => Work.Elliptic.Fstar g z) Filter.atTop (nhds 0) := by
  -- (0) the a.e. set where the angle is interior
  have hIθmem : MeasurableSet Work.Spaces.Iθ := by simp [Work.Spaces.Iθ]
  have hIoo_restrict : volume.restrict (Set.Ioo (0 : ℝ) (π / 2))
      = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))
  have hθae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [← hIoo_restrict]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  -- (1) the lintegral bound `∫⁻_θ zTail g θ ≤ ofReal (HkSq α 7 g)`
  have hlin : (∫⁻ θ in Work.Spaces.Iθ, zTail g θ)
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 7 g) :=
    zTail_lintegral_le_HkSq hreg hmem (by norm_num)
  have htop : (∫⁻ θ in Work.Spaces.Iθ, zTail g θ) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
  -- (2) measurability of the tail weight
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.Dz g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      (Work.FTS.EllipticEst.Q0) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz g p.1 p.2)
        (Work.FTS.EllipticEst.Q0) := (hreg.Dz).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Work.FTS.EllipticEst.Q0) := by
      simp only [Work.Spaces.w]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact (h1.pow 2).mul (h2.pow 2)
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.Dz g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hjoint : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.Dz g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    haesm.aemeasurable.ennreal_ofReal
  have hmeasT : AEMeasurable (zTail g) (volume.restrict Work.Spaces.Iθ) :=
    hjoint.lintegral_prod_left'
  have hmeasR : AEMeasurable (zTailR g) (volume.restrict Work.Spaces.Iθ) :=
    ENNReal.measurable_toReal.comp_aemeasurable hmeasT
  -- (3) `zTail g` is finite a.e.
  have haefin : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), zTail g θ ≠ ⊤ :=
    (MeasureTheory.ae_lt_top' hmeasT htop).mono fun θ h => ne_of_lt h
  -- (4) `1 + zTailR g` is integrable
  have hbound_lin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (zTailR g θ)) ≠ ⊤ :=
    ne_top_of_le_ne_top htop (lintegral_mono fun θ => ENNReal.ofReal_toReal_le)
  have haesmR : AEStronglyMeasurable (zTailR g) (volume.restrict Work.Spaces.Iθ) :=
    hmeasR.aestronglyMeasurable
  have hintT : MeasureTheory.Integrable (zTailR g) (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesmR
      (Filter.Eventually.of_forall fun θ => zTailR_nonneg g θ)).mp hbound_lin
  have hInt1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.integrable_const_iff]
    right
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    show volume Work.Spaces.Iθ < ⊤
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hInt : MeasureTheory.Integrable (fun θ => 1 + zTailR g θ)
      (volume.restrict Work.Spaces.Iθ) := hInt1.add hintT
  -- (5) dominated convergence
  have hF_meas : ∀ᶠ z in Filter.atTop,
      AEStronglyMeasurable (fun θ => g z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with z hz
    have h1 : ContinuousOn (fun θ : ℝ => g z θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
      (hreg.curry_θ hz).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
      unfold Work.Elliptic.sinCos2
      exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
    exact (hIoo_restrict ▸ ((h1.mul h2).aestronglyMeasurable measurableSet_Ioo))
  have hsin1 : ∀ θ : ℝ, |Work.Elliptic.sinCos2 θ| ≤ 1 := by
    intro θ
    unfold Work.Elliptic.sinCos2
    rw [abs_mul]
    have h2 : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one (Real.cos θ)).mpr (Real.abs_cos_le_one θ)
    calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one θ) h2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have habs_le : ∀ a : ℝ, |a| ≤ a ^ 2 + 1 := by
    intro a
    nlinarith [sq_nonneg (|a| - 1 / 2), sq_abs a]
  have hbound : ∀ᶠ z in Filter.atTop,
      ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ‖g z θ * Work.Elliptic.sinCos2 θ‖ ≤ 1 + zTailR g θ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with z hz
    filter_upwards [haefin, hθae] with θ hfin hθ
    have hg : (g z θ) ^ 2 ≤ zTailR g θ := zTail_hardy hreg hdec hθ hfin z hz
    rw [Real.norm_eq_abs, abs_mul]
    calc |g z θ| * |Work.Elliptic.sinCos2 θ|
        ≤ ((g z θ) ^ 2 + 1) * 1 :=
          mul_le_mul (habs_le (g z θ)) (hsin1 θ) (abs_nonneg _) (by positivity)
      _ ≤ 1 + zTailR g θ := by nlinarith
  have hlim : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => g z θ * Work.Elliptic.sinCos2 θ) Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθmem] with θ hθ
    have h := (hdec θ hθ).mul_const (Work.Elliptic.sinCos2 θ)
    simpa using h
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ) (l := Filter.atTop)
    (F := fun z θ => g z θ * Work.Elliptic.sinCos2 θ) (f := fun _ => (0 : ℝ))
    (bound := fun θ => 1 + zTailR g θ) hF_meas hbound hInt hlim
  simpa [Work.Elliptic.Fstar] using hDCT

end

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Pieces.C0_sq_le_Ef_CoerAdm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.CoercivityFix.Coer1T

namespace Work.FTS.CoercivityFix.Transfer.E1Norm.Pieces

set_option autoImplicit false
set_option maxHeartbeats 1600000

end Work.FTS.CoercivityFix.Transfer.E1Norm.Pieces
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1_blocks =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## `BlocksCont` is monotone in the order -/

/-- `BlocksCont j g` follows from `BlocksCont k g` for `j ≤ k` (fewer blocks to control). -/
theorem blocksCont_mono {j k : ℕ} (hjk : j ≤ k) {g : Fn}
    (h : Work.FTS.CoercivityFix.Assembly.BlocksCont k g) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont j g :=
  fun a b hab => h a b (le_trans hab hjk)

/-! ## The radial factor `radA α f` is `C³` -/

/-- `ampA α = fun z => 2z/(c(1+z)²)` is `C³` on `(0,∞)` (`c α ≥ 1/10 > 0`). -/
theorem contDiffOn_ampA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 3 (ampA α) (Set.Ioi 0) := by
  have hcne : Work.Spaces.c α ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (Work.Spaces.c_bounds α hα hα1).1)
  have hnum : ContDiffOn ℝ 3 (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ 3 (fun z : ℝ => Work.Spaces.c α * (1 + z) ^ 2) (Set.Ioi 0) :=
    contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2)
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < z := hz
    exact mul_ne_zero hcne (pow_ne_zero 2 (by linarith))
  show ContDiffOn ℝ 3 (fun z : ℝ => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) (Set.Ioi 0)
  exact hnum.div hden hne

/-- `ampB α = fun z => 2z²/(1+z)³` is `C³` on `(0,∞)`. -/
theorem contDiffOn_ampB (α : ℝ) :
    ContDiffOn ℝ 3 (ampB α) (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ 3 (fun z : ℝ => 2 * z ^ 2) (Set.Ioi 0) :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hden : ContDiffOn ℝ 3 (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < z := hz
    exact pow_ne_zero 3 (by linarith)
  show ContDiffOn ℝ 3 (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi 0)
  exact hnum.div hden hne


/-! ## The angular factor `B(θ) = sin 2θ · Γ'(θ)` is `C^∞` on `(0,π/2)` -/

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C^∞` on `(0,π/2)`: there `sinθ·cos²θ > 0` and the real
power map is `C^∞` on `(0,∞)`. -/
theorem Gam_contDiffOn_infty (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.Spaces.Gam α) (Set.Ioo 0 (π / 2)) := by
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) := by
    fun_prop
  refine (hbase.rpow_const_of_ne (p := α / 3) ?_).congr (fun θ _ => rfl)
  intro θ hθ
  have h1 : (0 : ℝ) < θ := hθ.1
  have h2 : θ < π / 2 := hθ.2
  exact mul_ne_zero
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [h2, Real.pi_pos])))
    (pow_ne_zero 2 (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩)))

/-- **The angular factor is `C³` on `(0,π/2)`.**  It is `D_θ Γ` (the `z`-independent function),
which is `C^∞` there because `Γ` is. -/
theorem sinGam_contDiffOn_Ioo (α : ℝ) :
    ContDiffOn ℝ 3 (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (Set.Ioo 0 (π / 2)) := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hG : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun _ : ℝ => Work.Spaces.Gam α))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (Gam_contDiffOn_infty α).comp contDiffOn_snd (fun p hp => hp.2)
  have hD := Work.FTS.LocData.contDiffOn_Dth hV hG
  have hslice := Work.FTS.LocData.contDiffOn_slice_θ hD (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
  refine hslice.of_le (by simp) |>.congr (fun θ _ => ?_)
  simp only [Work.Spaces.Dth, Work.Spaces.pth]



end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTB3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c

/-- **The core estimate.**  Everything except the `TraceClass` bookkeeping. -/
theorem zmoll_ttDom_core (G : ℝ → ℝ → ℝ) (hF : FourInts G) (hsl : SliceData G)
    (hdom : LocallyIntegrable (fun t : ℝ => ∫ s in Iθ, |Hxyc G t s|) volume)
    (hsqrt : LocallyIntegrable (fun t : ℝ => Real.sqrt (E2s G (Real.exp t))) volume)
    (δ ε : ℝ) (hP : Params δ ε) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ θ ∈ Iθ,
        |Work.Spaces.pth (Work.Spaces.pth (zmoll G δ ε)) z θ|
          ≤ ∫ t : ℝ, sKer δ (Real.log z - t) *
              (∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) := by
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  have hSnfun : LocallyIntegrable (fun t : ℝ => SNg G t) volume := by
    have hfun : (fun t : ℝ => ∫ s in Iθ, |Hxyc G t s|) = (fun t : ℝ => SNg G t) := by
      funext t
      simp only [SNg]
      refine MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_)
      simp only [Hxyc, Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp t) s hs]
    rw [hfun] at hdom
    exact hdom
  obtain ⟨Mk, hMk0, hMk⟩ := kmθ_bdd hε0
  obtain ⟨Mk2, hMk20, hMk2⟩ := kmθθ_bdd hε0
  have hJboundB : ∀ y t : ℝ, ‖JB G ε y t‖ ≤ (Mk • SNg G) t := by
    intro y t
    simpa only [Real.norm_eq_abs, JB, Pi.smul_apply, smul_eq_mul] using
      abs_fold_le G hsl hMk0 (fun y s => hMk y s) y t
  have hJboundC : ∀ y t : ℝ, ‖JC G ε y t‖ ≤ (Mk2 • SNg G) t := by
    intro y t
    simpa only [Real.norm_eq_abs, JC, Pi.smul_apply, smul_eq_mul] using
      abs_fold_le G hsl hMk20 (fun y s => hMk2 y s) y t
  have hJboundA : ∀ y t : ℝ, ‖JA G ε y t‖ ≤ ((3 * (ε * sMass)⁻¹) • SNg G) t := by
    intro y t
    simpa only [Real.norm_eq_abs, JA, Pi.smul_apply, smul_eq_mul] using
      abs_fold_le G hsl (by have := sMass_pos; positivity)
        (fun y s => le_trans (abs_km_le_KJ hε0 y s)
          (Work.FTS.EllSol.EllPkgAux.KJ_le hε0 y s)) y t
  have hCjA : LocallyIntegrable (fun t : ℝ => (Mk • SNg G) t) volume := hSnfun.smul Mk
  have hCjB : LocallyIntegrable (fun t : ℝ => (Mk2 • SNg G) t) volume := hSnfun.smul Mk2
  have hJintA : ∀ x : ℝ, ∀ p q : ℝ,
      IntegrableOn (fun t : ℝ => JA G ε x t) (Set.Icc p q) := by
    intro x p q
    have hb : IntegrableOn (fun t : ℝ => ((3 * (ε * sMass)⁻¹) • SNg G) t) (Set.Icc p q) :=
      (hSnfun.integrableOn_isCompact isCompact_Icc).const_mul _
    refine Integrable.mono' hb ((aesm_JA G hsl.sm ε x).restrict) ?_
    exact Filter.Eventually.of_forall fun t => hJboundA x t
  have hJintB : ∀ x : ℝ, ∀ p q : ℝ,
      IntegrableOn (fun t : ℝ => JB G ε x t) (Set.Icc p q) := by
    intro x p q
    have hb : IntegrableOn (fun t : ℝ => (Mk • SNg G) t) (Set.Icc p q) :=
      (hSnfun.integrableOn_isCompact isCompact_Icc).const_mul _
    refine Integrable.mono' hb ((aesm_JB G hsl.sm ε x).restrict) ?_
    exact Filter.Eventually.of_forall fun t => hJboundB x t
  have hJintC : ∀ x : ℝ, ∀ p q : ℝ,
      IntegrableOn (fun t : ℝ => JC G ε x t) (Set.Icc p q) := by
    intro x p q
    have hb : IntegrableOn (fun t : ℝ => (Mk2 • SNg G) t) (Set.Icc p q) :=
      (hSnfun.integrableOn_isCompact isCompact_Icc).const_mul _
    refine Integrable.mono' hb ((aesm_JC G hsl.sm ε x).restrict) ?_
    exact Filter.Eventually.of_forall fun t => hJboundC x t
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  intro θ hθ
  have hθw : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hA : ∀ x ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4),
      HasDerivAt (fun x' : ℝ => ∫ t : ℝ, sKer δ (Real.log z - t) * JA G ε x' t)
        (∫ t : ℝ, sKer δ (Real.log z - t) * JB G ε x t) x := by
    intro x hx
    exact conv_t_step (JA G ε) (JB G ε) hδ0 (by linarith) hCjA
      (fun y => aesm_JA G hsl.sm ε y) (fun y => aesm_JB G hsl.sm ε y) hJintA
      (fun t y => inner_hasDerivAt (K := fun y s => km ε y s) (K' := fun y s => kmθ ε y s)
        (C := Mk) (fun y => continuous_km ε y) (fun y => continuous_kmθ ε y)
        (fun y s => hMk y s) (fun y s => hasDerivAt_km_theta ε y s)
        (hsl.cont (Real.exp t) (Real.exp_pos t)))
      hJboundB x
  have hB : ∀ x ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4),
      HasDerivAt (fun x' : ℝ => ∫ t : ℝ, sKer δ (Real.log z - t) * JB G ε x' t)
        (∫ t : ℝ, sKer δ (Real.log z - t) * JC G ε x t) x := by
    intro x hx
    exact conv_t_step (JB G ε) (JC G ε) hδ0 (by linarith) hCjB
      (fun y => aesm_JB G hsl.sm ε y) (fun y => aesm_JC G hsl.sm ε y) hJintB
      (fun t y => inner_hasDerivAt (K := fun y s => kmθ ε y s) (K' := fun y s => kmθθ ε y s)
        (C := Mk2) (fun y => continuous_kmθ ε y) (fun y => continuous_kmθθ ε y)
        (fun y s => hMk2 y s) (fun y s => hasDerivAt_kmθ_theta ε y s)
        (hsl.cont (Real.exp t) (Real.exp_pos t)))
      hJboundC x
  have hfold : ∀ x ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4),
      zmoll G δ ε z x = ∫ t : ℝ, sKer δ (Real.log z - t) * JA G ε x t := by
    intro x hx
    simp only [Work.FTS.EllSol.PkgK5.K5c.zmoll, JA]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    change sKer δ (Real.log z - t) * thMoll G ε (Real.exp t) x
      = sKer δ (Real.log z - t) * ∫ s in Iθ, km ε x s * G (Real.exp t) s
    rw [Work.FTS.EllSol.EllPkgAux.thMoll_fold (u := G) (z := Real.exp t) (θ' := x)
      hε0 hε1 (hsl.val0 _) (hsl.valpi _) (hsl.cont _ (Real.exp_pos t)) hx.1 hx.2]
    simp only [Work.FTS.EllSol.EllPkgAux.Kern, km]
  have hderiv1 : (fun x : ℝ => deriv (fun x' : ℝ => zmoll G δ ε z x') x)
      =ᶠ[𝓝 θ] fun x : ℝ => ∫ t : ℝ, sKer δ (Real.log z - t) * JB G ε x t := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4), isOpen_Ioo.mem_nhds hθw, ?_⟩
    intro x hx
    have h1 : (fun x' : ℝ => zmoll G δ ε z x')
        =ᶠ[𝓝 x] fun x' : ℝ => ∫ t : ℝ, sKer δ (Real.log z - t) * JA G ε x' t :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4), isOpen_Ioo.mem_nhds hx, hfold⟩
    show deriv (fun x' : ℝ => zmoll G δ ε z x') x
        = ∫ t : ℝ, sKer δ (Real.log z - t) * JB G ε x t
    rw [Filter.EventuallyEq.deriv_eq h1]
    exact (hA x hx).deriv
  have hd2 : deriv (deriv (fun x' : ℝ => zmoll G δ ε z x')) θ
      = ∫ t : ℝ, sKer δ (Real.log z - t) * JC G ε θ t := by
    rw [Filter.EventuallyEq.deriv_eq hderiv1, (hB θ hθw).deriv]
  have hd3 : Work.Spaces.pth (Work.Spaces.pth (zmoll G δ ε)) z θ
      = ∫ t : ℝ, sKer δ (Real.log z - t) *
          (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) := by
    rw [show Work.Spaces.pth (Work.Spaces.pth (zmoll G δ ε)) z θ
        = deriv (deriv (fun x' : ℝ => zmoll G δ ε z x')) θ from rfl, hd2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show sKer δ (Real.log z - t) * JC G ε θ t
        = sKer δ (Real.log z - t) *
          (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)
    rw [JC, ibp_km hsl hε0 hε1 (Real.exp_pos t) hθ]
    simp only [Work.Spaces.pth]
  rw [hd3]
  have hint : Integrable (fun t : ℝ => sKer δ (Real.log z - t) *
      ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) volume :=
    rhs_integrable G hsl hsqrt hδ0 hε0 hz
  calc |∫ t : ℝ, sKer δ (Real.log z - t) *
        (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)|
      ≤ ∫ t : ℝ, ‖sKer δ (Real.log z - t) *
          (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)‖ :=
        MeasureTheory.norm_integral_le_integral_norm (μ := volume)
          (fun t : ℝ => sKer δ (Real.log z - t) *
            (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s))
    _ = ∫ t : ℝ, sKer δ (Real.log z - t) *
          ‖∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s‖ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show ‖sKer δ (Real.log z - t) *
            (∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)‖
          = sKer δ (Real.log z - t) *
            ‖∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s‖
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sKer_nonneg hδ0 _)]
        simp only [Real.norm_eq_abs]
    _ ≤ ∫ t : ℝ, sKer δ (Real.log z - t) *
          (∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t =>
          mul_nonneg (sKer_nonneg hδ0 _) (norm_nonneg _)) hint ?_
        exact Filter.Eventually.of_forall fun t =>
          mul_le_mul_of_nonneg_left
            (by simpa only [Real.norm_eq_abs] using abs_inner_le_KJ G hsl hε0 θ t)
            (sKer_nonneg hδ0 _)

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_ae_value_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000



end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.aesm_deriv_U_mul_psi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint (a.e.) strong measurability of `(∂_θ(U u · ψ))^2 sin(2θ)^{-η}`

For a datum `u` of class `SmoothOpen` (i.e. `C^∞` on the open quadrant `(0,∞) × (0,π/2)`)
and a `C²` function `ψ`, the function

  `p ↦ (deriv (fun θ' => U u p.1 θ' * ψ θ') p.2)^2 * sin(2 p.2)^{-η}`

is almost everywhere strongly measurable for the product of the restrictions of Lebesgue
measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`.

The proof is a reduction to the open quadrant: `Iz ×ˢ Iθ` agrees a.e. with the open quadrant
`Q0`, on which the product rule `deriv_U_mul_eq` computes the derivative as the *continuous*
function `V u · ψ + U u · ∂ψ`; the uncurried expression is continuous on `Q0`
(`U` and `V` are uncurried `pz`-derivatives of a `SmoothOpen` datum, and `ψ`, `deriv ψ`,
`sin(2·)^{-η}` are continuous there), so `Work.Spaces.aesm_of_continuousOn_Qd` applies.
-/

namespace Work.FTS.EllipticEst.AeI1Fts


end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.cross_joint_h =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/cross_joint_h` — the `z`-integrated cross identity of `I₁` in the class `AeData`

The target `Work.FTS.EllipticEst.AeI1Fts.cross_joint_h`: for a datum
`h : H2W.Ae.AeData α u G` together with the two `ℋ⁰`-honesties of the slots

* `U u = z ∂_z u` (`Work.FTS.EllipticEst.AeI1Fts.U`) and
* `V u = z ∂_z ∂_θ u` (`Work.FTS.EllipticEst.AeI1Fts.V`, the Clairaut twin of `∂_θ(U u)`),

and the three *almost every* `z`-integrabilities of the slice integrands (`hintA`, `hintN`,
`hintC`) of the cross identity, one has

`∫_z w(z)² ∫_θ U·V·cos(2θ)·sin(2θ)^{-1-η}
   = ∫_z w(z)² ∫_θ U²·sin(2θ)^{-η}
     + (1+η) · ∫_z w(z)² ∫_θ U²·cos²(2θ)·sin(2θ)^{-2-η}`,

i.e. the `θ`-integration by parts `CROSS = ⟨U,U⟩ + (1+η)N` of `H2W.SlotA.cross_theta_ibp`
(Elgindi, Annals **194** (2021), tex 873–890) applied slice by slice and then integrated
against the radial weight `w²`.

## Route

* For a.e. `z > 0` the slice `v := U u z ·` is `C^∞` on the open interval and the three
  integrability hypotheses of `cross_theta_ibp` are exactly `hintA`, `hintN`, `hintC` (with
  `∂_θ(U u z ·) = V u z ·` from `N_bound.slice_deriv_eq`), so the slice identity
  `cross_theta_ibp` gives the pointwise identity of the two `z`-integrands.
* The two outer integrals on the right are *integrable*:
  * `∫_z w²∫_θ U²σ` and `∫_z w²∫_θ V²σ` come from the `ℋ⁰`-honesties `hU`, `hV`
    (`HkIntegrand α 0 f = w²f²σ` on `Iθ`, then restrict `Iz` to `(0,∞)`);
  * `∫_z w²∫_θ U²cos²σ₂` needs the sharp slicewise Hardy inequality `hardy_slice_ae`
    (`∫_θ U²cos²σ₂ ≤ (1+η)^{-2}∫_θ V²σ` for a.e. `z`), the `a.e.`-strong measurability of
    the partial integral (`AEStronglyMeasurable.integral_prod_right'` applied to the joint
    integrand, which is continuous on the open quadrant) and `Integrable.mono'`.
* `MeasureTheory.integral_add` + `MeasureTheory.integral_const_mul` then split the outer
  integral of the sum.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Integrability of the weighted slice energies -/



/-! ## The target -/


end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeDzNormLeaf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.MassBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces.AeGradRho

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## Two elementary facts -/

/-- The restriction of Lebesgue measure to `Iz = [0,∞)` is that to `(0,∞)`: the two sets differ
by the null singleton `{0}`. -/
private lemma restrict_Iz_eq_restrict_Ioi :
    (MeasureTheory.volume.restrict Work.Spaces.Iz)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

/-- The angular weight `σ = sin(2θ)^{-η}` dominates `1` off the two endpoints. -/
private lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc : (-(Work.Spaces.eta) : ℝ) ≤ 0 := by
    rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs h1 hc
  rw [Real.one_rpow] at h
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- `ofReal` of a nonnegative Bochner integral is dominated by the `lintegral` of its `ofReal`,
for any function (no measurability needed: a non-strongly-measurable function has integral `0`). -/
private lemma ofReal_integral_le_lintegral' {μ : MeasureTheory.Measure ℝ} {f : ℝ → ℝ}
    (hnn : ∀ θ, 0 ≤ f θ) :
    ENNReal.ofReal (∫ θ, f θ ∂μ) ≤ ∫⁻ θ, ENNReal.ofReal (f θ) ∂μ := by
  by_cases h : MeasureTheory.AEStronglyMeasurable f μ
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) h]
    exact ENNReal.ofReal_toReal_le
  · rw [MeasureTheory.integral_undef (fun hi => h hi.aestronglyMeasurable)]
    simp

/-! ## The `HkSq α 0`-mass of `u` against the `σ`-mass -/

/-- For `u` whatsoever, `ofReal (HkSq α 0 u)` is dominated by the `σ`-weighted angular mass
of `u`. -/
private theorem ofReal_HkSq_le_sigmaMass (α : ℝ) {u : ℝ → ℝ → ℝ} :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 u) ≤
      ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have step1 : ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      ≤ ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) :=
    ofReal_integral_le_lintegral'
      (fun z => integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
  have step2 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ) :=
    MeasureTheory.lintegral_mono
      (fun z => ofReal_integral_le_lintegral'
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
  have step3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ)
          = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        rw [Work.FTS.EllipticEst.H2W.AeU2.HkIntegrand_zero_eq α u hθ,
          ENNReal.ofReal_mul (sq_nonneg _)])
    rw [MeasureTheory.lintegral_congr_ae hae,
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (Work.Spaces.HkSq α 0 u)
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by
        rw [Work.Spaces.HkSq]
    _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
private lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

end

/-! **The `u`-mass bound of Step 1 of `prop:H2` in the `AeData` class**, from the paper's
`w²`-weighted radial energy inequality (★) — the statement of
`Work.FTS.EllipticEst.H2W.AeProof.AeEnergyExpl` / `Cores.Pieces.AeGradRho.ae_w2_energy` — taken
here as the hypothesis `hW2`.

Chain: (★) plus the constrained slice gap `9∫u² ≤ ∫(∂_θu)²` (a.e. in `z`) gives the bound.

The statement `Cores.Pieces.AeGradRho.ae_mass_bound_of` itself is provided elsewhere in the tree
(`Submission/Work/FTS/EllipticEst/H2W/ESV/MassBound.lean`, imported above) — the two copies were
identical duplicates (dedup of 2026-10-10, see `EllipticEst/NOTES_DEDUP_AUDIT.md`). -/

end Work.FTS.EllipticEst.Cores.Pieces.AeGradRho
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.RIFLimits =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1Ae/RIFLimits` — the limiting bookkeeping of the `I₁` expansion identity

This module collects the analytic limits needed to pass from the two *cut-off* identities
(`I1Ae.zibpChain`, `I1Ae.thetaChain`) to the un-truncated expansion identity
`I1Ae.radialIdentityFts`:

* `tendsto_II_cut` — the generic dominated-convergence limit removing the radial cut-off
  `Work.FTS.EllipticEst.cut n`;
* `psideriv_tendsto_zero` — the vanishing, as `ε → 0⁺`, of the angular cut-off derivative term
  `∫_z w²χ_n ∫_θ σ ψ_ε'(θ) (U V)` (the "collar" term of the `θ`-integration by parts);  the
  proof uses that `σ = tan(2θ)²σ₂cos²(2θ)`, whence on the transition window of `ψ_ε`
  `∫ σ U² ≤ 16ε² ∫ σ₂cos²(2θ)U²`, so the `1/ε` of the derivative is beaten by the `ε` of the
  window.
* the four `n → ∞` limits and the four `ε → 0` limits of the individual terms.

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

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ)

/-! ## The measure `nuQ` and its elementary properties -/




/-! ## The generic radial cut-off limit -/


section NT





end NT

/-! ## The angular cut-off: support, derivative bound, and the window domination -/





/-- `tan x ≤ 2x` on `(0, π/4]`. -/
private theorem tan_le_two_mul {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 4) :
    Real.tan x ≤ 2 * x := by
  have hcos : (1 / 2 : ℝ) ≤ Real.cos x := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
    have h2 : x ^ 2 ≤ 1 := by nlinarith [Real.pi_lt_four, hx, hx0]
    linarith
  have hsin : Real.sin x ≤ x := Real.sin_le hx0.le
  have hpos : 0 < Real.cos x := by linarith
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hpos]
  nlinarith [hsin, hcos, hx0, Real.cos_le_one x]




end Work.FTS.EllipticEst.I1Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.thetaChain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `thetaChain` — the angular chain identity of `I₁` with the two cut-offs

The datum of `Work.FTS.EllipticEst.H2W.Ae.AeData` is only `C^∞` on the *open* quadrant, so the
angular integration by parts `slice_theta_ibp_cut` is available only slice by slice (at a fixed
`z > 0`).  The target integrates it against the radial cut-off `χ_n = cut n`, which is constant
in `θ`; this file performs the bookkeeping:

* for every `z > 0` the constant `w(z)²·χ_n(z)` is pulled out of the `θ`-integral, the slice
  identity `slice_theta_ibp_cut` is applied, and the constant is pushed back in;
* the three `z`-marginals of the right-hand side are integrable, because each integrand is
  continuous on the open quadrant and vanishes off the compact rectangle
  `[1/(n+1), 3(n+1)] × [min (ε/2) (π/4), max (π/2 - ε/2) (π/4)]` (the first factor from `χ_n`,
  the second from `χ_ε` resp. `χ_ε'`), so Fubini (`Integrable.integral_prod_left`) applies;
* the outer `z`-integral is split with `integral_add` / `integral_sub` / `integral_neg` /
  `integral_const_mul` using those integrability facts.
-/

namespace Work.FTS.EllipticEst.I1Ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## A compactly supported continuous function is integrable for the product measure -/


/-! ## Continuity of the elementary factors on the open quadrant -/









/-! ## The vanishing of the cut-offs and of `χ_ε'` at the endpoints of their plateau -/



/-! ## The target -/


end

end Work.FTS.EllipticEst.I1Ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.zibpChain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1Ae/zibpChain` — the radial integration by parts in the `z`-outer iterated form

`AeI1Fts.zibp_cut` is the pointwise-in-`θ` identity

  `∫_z χ_n w² Fp u(·,θ) = -∫_z χ_n' (z∂_zu)(∂_θθu) w²`,

and `AeI1Fts.zibp_zouter` integrates it against the angular weight `σ·χ_ε` after pulling the
`z`-dependent factors out of the *inner* (`θ`-)integral.  The present target is the same
identity in the *opposite* grouping: both sides are `z`-outer iterated integrals whose inner
(`θ`-)integrands still carry the `z`-factors `χ_n z`, `w²z` and `χ_n'`.  The proof is therefore
two `integral_const_mul` pull-outs (`zibpChain_inner_lhs`, `zibpChain_inner_rhs`) turning the
two iterated integrals into the shape of `zibp_zouter`, followed by `zibp_zouter` itself.

The degenerate case `π/2 < ε` is handled separately: then `χ_ε` vanishes identically, because
its two plateaus `θ > ε/2` and `θ < π/2 - ε/2` are disjoint.
-/

namespace Work.FTS.EllipticEst.I1Ae

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false





end

end Work.FTS.EllipticEst.I1Ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.l2etaEndpointZeroLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2







end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.AeNj.sliceRateUniformFts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The uniform (`z`-free) slice rate of `U = z ∂_z u` at the two angular endpoints

`Work.FTS.EllipticEst.AeI1Fts.slice_rate` produces, for almost every `z > 0`, an *existential*
constant `C` with the two endpoint rates of the angular slice `θ ↦ U u z θ = z ∂_z u (z,θ)`.
That `C` comes from the *existential* constant `K` of
`Work.EllipticEst.Core.sliceBoundaryLimit` (`∃ K > 0, …`) and is therefore not usable in an
assembly that needs a *numerical* constant.

Here the same argument is re-run with the constant kept explicit.  The two ingredients carrying
the numerical constant are the *explicit* reciprocal-mass bound
`Work.EllipticEst.Core.thEtaInvIntegralBounds` (`∫_{(0,θ)} σ⁻¹ ≤ 2·θ^{1+η}` and its
`(π/2-θ)`-mirror) and weighted Cauchy–Schwarz `Work.EllipticEst.Core.weightedCS`; the endpoint
limit which Cauchy–Schwarz leaves over is identified with `0` through the trace lemma
`Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk`.  Since `√2 ≤ 2`, the constant `2` is uniform in
`z`, `θ`, `u` and `α`.

* `sliceRateTwoLeft` — the `0⁺` half for an arbitrary `C¹` slice `f` with finite weighted energy
  and vanishing trace at `0⁺` (proved here);
* `remov/AeNj/sliceRateTwoRight` — the mirror `(π/2)⁻` half;
* `sliceRateUniformFts` — the target, assembled from the two halves applied to the slice
  `θ ↦ U u z θ`, the derivative identity `∂_θ(U u z ·) = V u z ·` (`AeI1Fts.slice_deriv_eq`)
  and the a.e. trace vanishing `TT.AeI1.aeDzTraceHk`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.AeNj

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- **The `0⁺` half of the uniform slice rate.**  For `f` of class `C¹` on `(0,π/2)` whose
weighted derivative square `(f')²·σ` (`σ = thEta = sin(2θ)^{-η}`) is integrable there and whose
trace at `0⁺` vanishes,

`|f θ| ≤ 2 √(∫_{0<θ'<θ} (f')²σ) · θ^{(1+η)/2}`  for all `θ ∈ (0, π/2)`.

Proof: weighted Cauchy–Schwarz against the dual weight `σ⁻¹` applied to the exact
fundamental-theorem-of-calculus identity `f θ = ∫_{0<θ'<θ} f'` (`TT.sliceFtcKey`, the additive
constant being identified with `0` from the vanishing trace via `Core.tendstoSqBoundLeft`), the
explicit reciprocal-mass bound `thEtaInvIntegralBounds.2.1`, and finally `√2 ≤ 2`. -/
theorem sliceRateTwoLeft {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f Iθo)
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Iθo)
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ θ ∈ Iθo,
      |f θ| ≤ 2 * Real.sqrt (∫ θ' in Set.Ioo 0 θ,
          (deriv f θ') ^ 2 * Work.FTS.EllipticEst.thEta θ') * θ ^ ((1 + Work.Spaces.eta) / 2) := by
  have heta1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have heta0 : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  -- the weighted derivative square with the raw `sin`-power weight of `HeavyDerivIntegrable`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo := by
    simpa only [Work.FTS.EllipticEst.thEta] using hint
  -- `deriv f` is integrable on `(0,π/2)` and on every subinterval
  obtain ⟨_, hI⟩ := Work.FTS.EllipticEst.EllTwoAsm.HeavyDerivIntegrable
    (-(Work.Spaces.eta)) (by linarith) (by linarith) f hf hint'
  -- the exact FTC identity, with an additive constant `c₀`
  obtain ⟨c₀, hc₀⟩ := (Work.FTS.EllipticEst.TT.sliceFtcKey f hf hI).1
  -- weighted Cauchy–Schwarz on `(0, θ)`: the deviation bound with the constant `2`
  have hdev : ∀ θ ∈ Iθo, (f θ - c₀) ^ 2
      ≤ 2 * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by
    intro θ hθ
    have hsub : Set.Ioo 0 θ ⊆ Iθo := fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
    have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo 0 θ) measurableSet_Ioo
      (w := Work.FTS.EllipticEst.thEta) (g := fun t : ℝ => deriv f t)
      (fun t ht => Work.EllipticEst.Core.thEtaFacts.1 t (hsub ht))
      (Work.EllipticEst.Core.thEtaFacts.2.2.2.mono hsub)
      ((hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub)
      (hint.mono_set hsub)
      (Work.EllipticEst.Core.thEtaInvIntegralBounds.1 θ hθ)
    have hAnn : 0 ≤ ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt (hsub ht).1, le_of_lt (hsub ht).2⟩))
    rw [hc₀ θ hθ]
    calc (∫ t in Set.Ioo 0 θ, deriv f t) ^ 2
        ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
      _ ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (2 * θ ^ (1 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left (Work.EllipticEst.Core.thEtaInvIntegralBounds.2.1 θ hθ) hAnn
      _ = 2 * θ ^ (1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  -- the total energy is nonnegative and dominates every truncated one
  have hglob : 0 ≤ ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  have hbdd : ∀ θ ∈ Iθo, (f θ - c₀) ^ 2
      ≤ (2 * ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          * θ ^ (1 + Work.Spaces.eta) := by
    intro θ hθ
    have hsub : Set.Ioo 0 θ ⊆ Iθo := fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
    have hmono : (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        ≤ ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
      refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
        exact mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
      · filter_upwards with t ht
        exact ⟨ht.1, lt_trans ht.2 hθ.2⟩
    calc (f θ - c₀) ^ 2
        ≤ 2 * θ ^ (1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          hdev θ hθ
      _ ≤ 2 * θ ^ (1 + Work.Spaces.eta)
            * (∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          mul_le_mul_of_nonneg_left hmono
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hθ.1.le _))
      _ = (2 * ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * θ ^ (1 + Work.Spaces.eta) := by ring
  -- the additive constant is the trace of `f` at `0⁺`, hence `0`
  have hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c₀) :=
    Work.EllipticEst.Core.tendstoSqBoundLeft
      (M := 2 * ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (mul_nonneg (by norm_num) hglob) hbdd
  have hc0 : c₀ = 0 := tendsto_nhds_unique hlim h0
  -- the rate
  intro θ hθ
  have hsq : (f θ) ^ 2
      ≤ 2 * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by
    have h := hdev θ hθ
    rwa [hc0, sub_zero] at h
  calc |f θ| = Real.sqrt ((f θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * θ ^ (1 + Work.Spaces.eta)
          * ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * θ ^ ((1 + Work.Spaces.eta) / 2)
          * Real.sqrt (∫ t in Set.Ioo 0 θ,
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by
        have hsp : 0 ≤ θ ^ (1 + Work.Spaces.eta) := Real.rpow_nonneg hθ.1.le _
        rw [show 2 * θ ^ (1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            = 2 * (θ ^ (1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) from by
              ring]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _]
        rw [Real.sqrt_mul hsp _]
        rw [show Real.sqrt (θ ^ (1 + Work.Spaces.eta)) = θ ^ ((1 + Work.Spaces.eta) / 2) from by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hθ.1.le]
          congr 1
          ring]
        ring
    _ ≤ 2 * Real.sqrt (∫ t in Set.Ioo 0 θ,
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          * θ ^ ((1 + Work.Spaces.eta) / 2) := by
        have hsqrt2 : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        have hnn : 0 ≤ θ ^ ((1 + Work.Spaces.eta) / 2)
            * Real.sqrt (∫ t in Set.Ioo 0 θ,
                (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          mul_nonneg (Real.rpow_nonneg hθ.1.le _) (Real.sqrt_nonneg _)
        have hstep := mul_le_mul_of_nonneg_right hsqrt2 hnn
        calc Real.sqrt 2 * θ ^ ((1 + Work.Spaces.eta) / 2)
              * Real.sqrt (∫ t in Set.Ioo 0 θ,
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            = Real.sqrt 2 * (θ ^ ((1 + Work.Spaces.eta) / 2)
                * Real.sqrt (∫ t in Set.Ioo 0 θ,
                    (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := by ring
          _ ≤ 2 * (θ ^ ((1 + Work.Spaces.eta) / 2)
                * Real.sqrt (∫ t in Set.Ioo 0 θ,
                    (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := hstep
          _ = 2 * Real.sqrt (∫ t in Set.Ioo 0 θ,
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
                * θ ^ ((1 + Work.Spaces.eta) / 2) := by ring


end Work.FTS.EllipticEst.remov.AeNj
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.EllRopLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-- **The `EllPkgGo` piece of the `Rop` slot.** -/
theorem ell_Rop_le {α Ce Cpt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpt : 0 ≤ Cpt)
    (hpt : ∀ g : Fn, ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 g → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        |Work.Spaces.mixed b a g z θ| ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 g)
    {f : Fn} {E : Fn → Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
      ≤ Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by
  have hR : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) := (hEll f hf).1.R.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) := hR.1
  have hmem : Work.Spaces.HkMem α 4
      (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) := hR.2
  have h4 : ContDiffOn ℝ 4
      (Function.uncurry (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 4
  have h := hpt _ h4 hmem 0 0 (by norm_num) z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_zero] at h
  refine h.trans ?_
  have hmin : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hXn : Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) ≤ Ce * Work.FTS.Nonlin.Xn α f :=
    (hEll f hf).1.R.2
  calc Cpt * min z 1 * Work.Spaces.HkNorm α 4
        (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)))
      = Cpt * min z 1 * Work.FTS.Nonlin.Xn α
          (Work.Construction.Rop α (Work.Construction.PhiTil α f (E f))) := by
        rw [Work.FTS.Nonlin.Xn]
    _ ≤ Cpt * min z 1 * (Ce * Work.FTS.Nonlin.Xn α f) := by
        refine mul_le_mul_of_nonneg_left hXn (by positivity)
    _ = Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by ring

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.HkIntegrand_zslot_perz_six_noTraces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem HkIntegrand_zslot_perz_six_noTraces :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 8 f →
      ∀ i : ℕ, i ≤ 6 → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := by
  refine ⟨3, by norm_num, ?_⟩
  intro α hα f hF hmem i hi z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- ### `z = 0`: the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    have hzero : (fun θ : ℝ => (Work.Spaces.DzIter i f 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [hw0, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [hzero]
    have h1 : (∫ _θ in Work.Spaces.Iθ, (0 : ℝ)) = 0 := by simp
    rw [h1]
    have h2 : 0 ≤ (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (1 : ℝ) + (Work.Spaces.w 0) ^ 2 := by rw [hw0]; norm_num
    nlinarith [h2, h3]
  · -- ### `z > 0`: the window bound at every angle, then integrate in `θ`
    have hR : z ≤ max z 2 := le_max_left z 2
    have hRpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
    have h2max : (2 : ℝ) ≤ max z 2 := le_max_right z 2
    obtain ⟨hswap, hGint, hGslice⟩ := sda_HkSqSwap_open8 α f hF hmem
    -- almost every angle is interior
    have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)] with σ h
      exact fun hmem' => h.mpr hmem'
    -- the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 8 f s σ)) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact Work.FTS.StrongEps.E5Aux.zslot_window_perz α hF 8 i (by omega) hzpos hR hσθ hσint
    -- integrability of the two sides
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.integrableOn_zSummand α 8 hF hmem i (by omega)
        (Set.mem_Ici.mpr hzpos.le)
    have hRI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 8 f s σ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hGint.const_mul ((Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2))
    -- the integral bound
    have hmain : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 8 f := by
      have h1 := MeasureTheory.integral_mono_ae hLI hRI hle
      rw [MeasureTheory.integral_const_mul, hswap] at h1
      exact h1
    -- the coefficient is at most `3`
    have hcoef : 2 + 2 / max z 2 ≤ 3 := by
      have h : 2 / max z 2 ≤ 1 := by
        rw [div_le_one hRpos]
        exact h2max
      linarith
    have hHknn : 0 ≤ Work.Spaces.HkSq α 8 f := Work.Spaces.HkSq_nonneg α 8 f
    have hXnn : 0 ≤ Work.Spaces.HkNorm α 8 f := Work.Spaces.HkNorm_nonneg α 8 f
    have hXsq : Work.Spaces.HkSq α 8 f
        ≤ (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := by
      have h4 : Work.Spaces.HkNorm α 8 f = Real.sqrt (Work.Spaces.HkSq α 8 f) := rfl
      rw [h4]
      nlinarith [Real.sq_sqrt hHknn, hXnn, hHknn]
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 8 f := hmain
      _ ≤ (Work.Spaces.w z) ^ 2 * 3 * Work.Spaces.HkSq α 8 f := by
          have h := mul_le_mul_of_nonneg_right hcoef hHknn
          nlinarith [h, sq_nonneg (Work.Spaces.w z)]
      _ ≤ 3 * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := by
          have hstep : (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 8 f
              ≤ (1 + (Work.Spaces.w z) ^ 2)
                * (1 + Work.Spaces.HkNorm α 8 f) ^ 2 :=
            mul_le_mul (by linarith [sq_nonneg (Work.Spaces.w z)]) hXsq hHknn
              (by linarith [sq_nonneg (Work.Spaces.w z)])
          nlinarith [mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 3)]

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.UopSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-! ## The decomposition of the `Uop/sin 2θ` slot -/

/-- **The `Uop/sin 2θ` slot's decomposition into its three pieces.** -/
theorem Uop_div_decomp {α : ℝ} {f Φs : ℝ → ℝ → ℝ} {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz₁ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α f (E f) z' θ) z)
    (hz₂ : DifferentiableAt ℝ (fun z' => Φs z' θ) z)
    (hz₃ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z' θ) z)
    (hz₄ : DifferentiableAt ℝ (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z' θ) z)
    (hθ₁ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α f (E f) z θ') θ)
    (hθ₂ : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hθ₃ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z θ') θ)
    (hθ₄ : DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z θ') θ) :
    Work.Construction.Uop α (Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)) z θ
        / Work.Construction.s2 θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
          / Work.Construction.s2 θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          / Work.Construction.s2 θ
        + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
          / Work.Construction.s2 θ := by
  have hfun₁ : Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)
      = fun z θ => Work.Construction.PhiTil α f (E f) z θ + Φs z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  have hfun₂ : Φs = fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
      + Work.Construction.Theta α (Work.Construction.Fstar α) z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  rw [hfun₁]
  have h₁ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α f (E f)) (Ψ₂ := Φs) hz₁ hz₂ hθ₁ hθ₂).2.1
  rw [h₁]
  have h₂ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
    (Ψ₂ := Work.Construction.Theta α (Work.Construction.Fstar α)) hz₃ hz₄ hθ₃ hθ₄).2.1
  have hUΦ : Work.Construction.Uop α Φs z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
    conv_lhs => rw [hfun₂]
    exact h₂
  rw [hUΦ, add_div]
  ring

/-! ## The `EllPkgGo` piece -/

/-- **The `EllPkgGo` piece of the `Uop/sin 2θ` slot.** -/
theorem ell_Uop_le {α Ce Cpt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpt : 0 ≤ Cpt)
    (hpt : ∀ g : Fn, ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 g → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        |Work.Spaces.mixed b a g z θ| ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 g)
    {f : Fn} {E : Fn → Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ / Work.Construction.s2 θ|
      ≤ Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by
  have hU : Work.FTS.VocabO.HQo α 4
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ) := (hEll f hf).1.U.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ) := hU.1
  have hmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ) := hU.2
  have h4 : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f))
        z θ / Work.Construction.s2 θ)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 4
  have h := hpt _ h4 hmem 0 0 (by norm_num) z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_zero] at h
  refine h.trans ?_
  have hXn : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ) ≤ Ce * Work.FTS.Nonlin.Xn α f := (hEll f hf).1.U.2
  calc Cpt * min z 1 * Work.Spaces.HkNorm α 4
        (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
          / Work.Construction.s2 θ)
      = Cpt * min z 1 * Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
            / Work.Construction.s2 θ) := by
        rw [Work.FTS.Nonlin.Xn]
    _ ≤ Cpt * min z 1 * (Ce * Work.FTS.Nonlin.Xn α f) := by
        refine mul_le_mul_of_nonneg_left hXn (by positivity)
    _ = Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by ring

/-! ## The assembly -/

/-- **The `Uop/sin 2θ` slot of `EpsDecay`, with `C = 3`.**  With the decomposition
`Uop_div_decomp` and the two piece bounds, the block is `≤ P + Cs α + 3/2` in absolute value, where
`P = Cpt · Ce · C₀α²` bounds the `EllPkgGo` piece; the smallness `P + Cs α ≤ 1` gives `≤ 5/2 < 3`.

The star piece is `≤ Cs α` by `Work.FTS.EpsEngine.star_Uop_div_le` (extraction of
`StarPkgo2.UsW`) and the explicit piece is `∈ [−3/2, 0]` by
`Work.FTS.EpsEngine.Theta_Fstar_ops`. -/
theorem uop_slot_abs_le_three {α Cpt Ce Cs C₀ : ℝ} {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hCpt : 0 ≤ Cpt) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀)
    (hsmall : Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1)
    (hdec : Work.Construction.Uop α (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ / Work.Construction.s2 θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
            / Work.Construction.s2 θ
          + Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
              z θ / Work.Construction.s2 θ
          + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α))
              z θ / Work.Construction.s2 θ)
    (hE : |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ| ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1)
    (hS : |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        / Work.Construction.s2 θ| ≤ Cs * α) :
    |Work.Construction.Uop α (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ / Work.Construction.s2 θ| ≤ 3 := by
  have hΘ := (Work.FTS.EpsEngine.Theta_Fstar_ops (α := α) hα hα1).2.2 z θ hz hθ.1 hθ.2
  -- the explicit piece lies in `[-3/2, 0]`
  have hnum : 0 ≤ 3 * (1 + z) - α * z := by nlinarith [hα.le, hz.le]
  have hden : 0 < 2 * (1 + z) ^ 2 := by positivity
  have hkey : 0 ≤ 3 / (2 * (1 + z)) - α * z / (2 * (1 + z) ^ 2) := by
    have heq : 3 / (2 * (1 + z)) - α * z / (2 * (1 + z) ^ 2)
        = (3 * (1 + z) - α * z) / (2 * (1 + z) ^ 2) := by
      field_simp
      try ring
    rw [heq]
    exact div_nonneg hnum hden.le
  have hle32 : 3 / (2 * (1 + z)) ≤ 3 / 2 := by
    have heq : 3 / 2 - 3 / (2 * (1 + z)) = (3 * (2 * (1 + z)) - 3 * 2) / (2 * (2 * (1 + z))) := by
      field_simp
      try ring
    have hpos : 0 < 2 * (2 * (1 + z)) := by positivity
    have hnonneg : 0 ≤ 3 / 2 - 3 / (2 * (1 + z)) := by
      rw [heq]
      exact div_nonneg (by nlinarith [hz.le]) hpos.le
    linarith
  have hpiece : |Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α))
      z θ / Work.Construction.s2 θ| ≤ 3 / 2 := by
    rw [hΘ]
    have hval : -(3 / (2 * (1 + z))) + α * z / (2 * (1 + z) ^ 2)
        = -(3 / (2 * (1 + z)) - α * z / (2 * (1 + z) ^ 2)) := by ring
    rw [hval, abs_neg, abs_of_nonneg hkey]
    have hb : (0 : ℝ) ≤ α * z / (2 * (1 + z) ^ 2) := by positivity
    linarith [hle32, hb]
  rw [hdec]
  have hP : Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 ≤ Cpt * (Ce * (C₀ * α ^ 2)) := by
    have h1 : min z 1 ≤ 1 := min_le_right _ _
    have h2 : 0 ≤ Cpt * (Ce * (C₀ * α ^ 2)) := by positivity
    calc Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 ≤ Cpt * (Ce * (C₀ * α ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = Cpt * (Ce * (C₀ * α ^ 2)) := mul_one _
  calc |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
          / Work.Construction.s2 θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          / Work.Construction.s2 θ
        + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
          / Work.Construction.s2 θ|
      ≤ |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
            / Work.Construction.s2 θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
            z θ / Work.Construction.s2 θ|
        + |Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
            / Work.Construction.s2 θ| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add_left (abs_add_le _ _) _
    _ ≤ 3 := by
        linarith [hE.trans hP, hS, hpiece, hsmall]

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.IPGen.CoerDataOne =====
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


end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.shiftPath_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The fundamental-theorem-of-calculus identity along the mollifier path

`Work.FTS.StrongEps.DiffAux.shiftPath_sub`: for a profile `g` of class `C^∞` on the open quadrant,

`g (zShift z p₁) (thShift θ p₂) - g z θ
   = ∫₀¹ -(p₁ · D_z g (zShift z (t p₁)) (thShift θ (t p₂))
           + (p₂/2) · D_θ g (zShift z (t p₁)) (thShift θ (t p₂))) dt`.

This is the chain rule along the one-parameter curve

`t ↦ (z e^{-t p₁}, arctan (tan θ · e^{-t p₂}))`

(in log coordinates `(s,ζ) ↦ (s - t p₁, ζ - t p₂)`, i.e. the mollifier displacement), together with
the fundamental theorem of calculus.  The two ingredients of the integrand are exactly the
derivatives of the two components of the curve:

* `d/dt (zShift z (t p₁)) = -p₁ · zShift z (t p₁)`, so the `z`-term is `-p₁ D_z g`;
* `d/dt (thShift θ (t p₂)) = -(p₂/2) sin (2 · thShift θ (t p₂))`, and `D_θ = sin(2θ) ∂_θ`,
  so the `θ`-term is `-(p₂/2) D_θ g`.

The chain rule for the two-variable profile is taken in the Fréchet form
(`HasFDerivAt.comp_hasDerivAt`), with the value of `fderiv ℝ (uncurry g)` on the tangent vector
computed from `Work.FTS.EllipticEst.Prop.pz_eq_fderiv` / `pth_eq_fderiv` (linearity + the two
coordinate directions `(1,0)`, `(0,1)`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

open Work.FTS.StrongEps

set_option autoImplicit false

/-- The `z`-component of the mollifier path: `t ↦ z e^{-t p} = zShift z (t p)` has derivative
`-p · zShift z (t p)`, which is `-p` times the `D_z`-weight `z` of the point. -/
private lemma hasDerivAt_zShift_param (z p t : ℝ) :
    HasDerivAt (fun s : ℝ => zShift z (s * p)) (-p * zShift z (t * p)) t := by
  have hd : HasDerivAt (fun s : ℝ => s * p) p t := by
    simpa using (hasDerivAt_id t).mul_const p
  have hdn : HasDerivAt (fun s : ℝ => -(s * p)) (-p) t := hd.neg
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s * p)))
      (Real.exp (-(t * p)) * (-p)) t := by
    exact (Real.hasDerivAt_exp (-(t * p))).comp t hdn
  have h2 : HasDerivAt (fun s : ℝ => z * Real.exp (-(s * p)))
      (z * (Real.exp (-(t * p)) * (-p))) t := hexp.const_mul z
  have hder : z * (Real.exp (-(t * p)) * (-p)) = -p * (z * Real.exp (-(t * p))) := by ring
  rw [hder] at h2
  simpa only [zShift] using h2

/-- The `θ`-component of the mollifier path: `t ↦ arctan (tan θ · e^{-t p}) = thShift θ (t p)` has
derivative `-(p/2) sin (2 · thShift θ (t p))`, which is `-(p/2)` times `sin(2θ)` at the shifted
point, i.e. `-(p/2)` times the `D_θ`-weight. -/
private lemma hasDerivAt_thShift_param (θ p t : ℝ) :
    HasDerivAt (fun s : ℝ => thShift θ (s * p))
      (-(p / 2) * Real.sin (2 * thShift θ (t * p))) t := by
  have hd : HasDerivAt (fun s : ℝ => s * p) p t := by
    simpa using (hasDerivAt_id t).mul_const p
  have hdn : HasDerivAt (fun s : ℝ => -(s * p)) (-p) t := hd.neg
  have hexp : HasDerivAt (fun s : ℝ => Real.tan θ * Real.exp (-(s * p)))
      (Real.tan θ * (Real.exp (-(t * p)) * (-p))) t := by
    exact ((Real.hasDerivAt_exp (-(t * p))).comp t hdn).const_mul (Real.tan θ)
  have harct : HasDerivAt (fun s : ℝ => Real.arctan (Real.tan θ * Real.exp (-(s * p))))
      ((1 / (1 + (Real.tan θ * Real.exp (-(t * p))) ^ 2))
        * (Real.tan θ * (Real.exp (-(t * p)) * (-p)))) t := by
    exact (Real.hasDerivAt_arctan (Real.tan θ * Real.exp (-(t * p)))).comp t hexp
  have hval : (1 / (1 + (Real.tan θ * Real.exp (-(t * p))) ^ 2))
        * (Real.tan θ * (Real.exp (-(t * p)) * (-p)))
      = -(p / 2) * Real.sin (2 * Real.arctan (Real.tan θ * Real.exp (-(t * p)))) := by
    have hsin : Real.sin (2 * Real.arctan (Real.tan θ * Real.exp (-(t * p))))
        = 2 * (Real.tan θ * Real.exp (-(t * p)))
          / (1 + (Real.tan θ * Real.exp (-(t * p))) ^ 2) := by
      rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
      field_simp
      rw [show Real.sqrt (1 + Real.tan θ ^ 2 * Real.exp (-(t * p)) ^ 2) ^ 2
          = 1 + Real.tan θ ^ 2 * Real.exp (-(t * p)) ^ 2 from Real.sq_sqrt (by positivity)]
    rw [hsin]
    rw [show Real.tan θ * (Real.exp (-(t * p)) * (-p))
        = (Real.tan θ * Real.exp (-(t * p))) * (-p) by ring]
    field_simp
  rw [hval] at harct
  simpa only [thShift] using harct

/-- **The chain rule along the mollifier path.**  For `g` of class `C^∞` on the quadrant and
`(z,θ) ∈ Quad`, the function `t ↦ g (zShift z (t p₁)) (thShift θ (t p₂))` has derivative
`-(p₁ · D_z g + (p₂/2) · D_θ g)` at the shifted point. -/
private lemma hasDerivAt_shiftPath {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g (zShift z (s * p.1)) (thShift θ (s * p.2)))
      (-(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
        + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)))) t := by
  have hperm : (zShift z (t * p.1), thShift θ (t * p.2)) ∈ Quad :=
    ⟨zShift_pos hz, thShift_mem hθ⟩
  have hdiff : DifferentiableAt ℝ (Function.uncurry g) (zShift z (t * p.1), thShift θ (t * p.2)) :=
    ((hg 1).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hperm)
  have hG : HasFDerivAt (Function.uncurry g)
      (fderiv ℝ (Function.uncurry g) (zShift z (t * p.1), thShift θ (t * p.2)))
      (zShift z (t * p.1), thShift θ (t * p.2)) := hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => (zShift z (s * p.1), thShift θ (s * p.2)))
      ((-p.1 * zShift z (t * p.1)), (-(p.2 / 2) * Real.sin (2 * thShift θ (t * p.2)))) t :=
    (hasDerivAt_zShift_param z p.1 t).prodMk (hasDerivAt_thShift_param θ p.2 t)
  have hcomp := hG.comp_hasDerivAt t hcurve
  have hkey : (fderiv ℝ (Function.uncurry g) (zShift z (t * p.1), thShift θ (t * p.2)))
        ((-p.1 * zShift z (t * p.1)), (-(p.2 / 2) * Real.sin (2 * thShift θ (t * p.2))))
      = -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
        + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))) := by
    rw [show ((-p.1 * zShift z (t * p.1)), (-(p.2 / 2) * Real.sin (2 * thShift θ (t * p.2))))
        = (-p.1 * zShift z (t * p.1)) • ((1 : ℝ), (0 : ℝ))
          + (-(p.2 / 2) * Real.sin (2 * thShift θ (t * p.2))) • ((0 : ℝ), (1 : ℝ)) by
      ext <;> simp [Prod.smul_mk]]
    rw [map_add, map_smul, map_smul,
      ← Work.FTS.EllipticEst.Prop.pz_eq_fderiv hdiff,
      ← Work.FTS.EllipticEst.Prop.pth_eq_fderiv hdiff]
    simp only [Work.Spaces.Dz, Work.Spaces.Dth]
    ring
  rw [hkey] at hcomp
  simpa only [Function.comp_def, Function.uncurry] using hcomp

theorem shiftPath_sub {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) :
    g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - g z θ
      = ∫ t in (0 : ℝ)..1, (-(p.1 * Work.Spaces.Dz g (Work.FTS.StrongEps.zShift z (t * p.1))
            (Work.FTS.StrongEps.thShift θ (t * p.2))
          + (p.2 / 2) * Work.Spaces.Dth g (Work.FTS.StrongEps.zShift z (t * p.1))
            (Work.FTS.StrongEps.thShift θ (t * p.2)))) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => g (zShift z (s * p.1)) (thShift θ (s * p.2)))
      (-(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
        + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)))) t :=
    fun t => hasDerivAt_shiftPath hg hz hθ p t
  have hcont : Continuous fun t : ℝ => -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1))
          (thShift θ (t * p.2))
        + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))) := by
    have hP : Continuous fun t : ℝ => zShift z (t * p.1) := by
      have h : Continuous fun t : ℝ => z * Real.exp (-(t * p.1)) := by fun_prop
      simpa only [zShift] using h
    have hT : Continuous fun t : ℝ => thShift θ (t * p.2) := by
      have h : Continuous fun t : ℝ => Real.arctan (Real.tan θ * Real.exp (-(t * p.2))) := by
        fun_prop
      simpa only [thShift] using h
    have hpzc : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pz g q.1 q.2) Quad :=
      (Work.FTS.EllipticEst.Prop.contDiffOn_uncurry_pz_succ (G := g) (V := Quad) (n := 0)
        (isOpen_Ioi.prod isOpen_Ioo) (by simpa using hg 1)).continuousOn
    have hpthc : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pth g q.1 q.2) Quad :=
      (Work.FTS.EllipticEst.Prop.contDiffOn_uncurry_pth_succ (G := g) (V := Quad) (n := 0)
        (isOpen_Ioi.prod isOpen_Ioo) (by simpa using hg 1)).continuousOn
    have hquad : ∀ t : ℝ, (zShift z (t * p.1), thShift θ (t * p.2)) ∈ Quad :=
      fun t => ⟨zShift_pos hz, thShift_mem hθ⟩
    have hpz : Continuous fun t : ℝ =>
        Work.Spaces.pz g (zShift z (t * p.1)) (thShift θ (t * p.2)) := by
      have := hpzc.comp_continuous (hP.prodMk hT) hquad
      simpa only [Function.comp_def] using this
    have hpth : Continuous fun t : ℝ =>
        Work.Spaces.pth g (zShift z (t * p.1)) (thShift θ (t * p.2)) := by
      have := hpthc.comp_continuous (hP.prodMk hT) hquad
      simpa only [Function.comp_def] using this
    have h1 : Continuous fun t : ℝ =>
        Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
      hP.mul hpz
    have hsin : Continuous fun t : ℝ => Real.sin (2 * thShift θ (t * p.2)) :=
      Real.continuous_sin.comp (continuous_const.mul hT)
    have h2 : Continuous fun t : ℝ =>
        Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
      hsin.mul hpth
    have hsum : Continuous fun t : ℝ =>
        p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
          + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
      (h1.const_mul p.1).add (h2.const_mul (p.2 / 2))
    exact hsum.neg
  have hint : IntervalIntegrable (fun t : ℝ => -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1))
        (thShift θ (t * p.2))
      + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))))
      volume (0 : ℝ) 1 :=
    hcont.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ => g (zShift z (s * p.1)) (thShift θ (s * p.2)))
    (f' := fun t : ℝ => -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
      + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))))
    (fun x _ => hderiv x) hint
  have hF1 : g (zShift z (1 * p.1)) (thShift θ (1 * p.2))
      = g (zShift z p.1) (thShift θ p.2) := by simp
  have hF0 : g (zShift z (0 * p.1)) (thShift θ (0 * p.2)) = g z θ := by
    have key : Real.arctan (Real.tan θ) = θ :=
      Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2
    simp only [zero_mul, zShift, thShift, neg_zero, Real.exp_zero, mul_one, key]
  rw [hF1, hF0] at hftc
  rw [← hftc]

end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The per-`σ` window bound: for `0 < z ≤ R₀`, an interior angle and an `HkIntegrand`-slice
integrable on `Iz`, the weighted `i`-th `D_z`-slot at `(z,σ)` is bounded by
`w(z)²(2 + 2/R₀)` times the full radial integral of the `ℋ^k`-integrand at the angle `σ`. -/
private theorem zslot_window_perz_aux (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) (i : ℕ) (hi : i + 1 ≤ k)
    {z R₀ σ : ℝ} (hz : 0 < z) (hR : z ≤ R₀) (hσ : σ ∈ Set.Ioo 0 (Real.pi / 2))
    (hσint : MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.HkIntegrand α k f s σ)
      Work.Spaces.Iz) :
    (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  have hsinσ : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  -- the hypotheses of the one-dimensional window inequality
  have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
      HasDerivAt (fun x' : ℝ => Work.Spaces.DzIter i f x' σ)
        (Work.Spaces.pz (Work.Spaces.DzIter i f) x σ) x :=
    fun x hx => hF.hasDerivAt_slice_DzIter i hσ (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter i f x σ) (Set.Icc R₀ (2 * R₀)) :=
    ((hF.DzIter i).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter i f) x σ)
      (Set.Icc z (2 * R₀)) :=
    (((hF.DzIter i).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (Work.Spaces.DzIter i f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
    (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound
    (h := fun x : ℝ => Work.Spaces.DzIter i f x σ)
    (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter i f) x σ)
    hz hR hderiv hcont hcont' hint
  -- the weight factor `A = (w z / sin(2σ)^{η/2})²` is nonnegative
  have hAnn : 0 ≤ (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
    sq_nonneg _
  -- continuity of the two window integrands and of the `ℋ^k`-integrand on the windows
  have hcontW : ContinuousOn
      (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x)
      (Set.Icc z (2 * R₀)) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
  have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.Icc z (2 * R₀)) := by
    have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀)) Work.FTS.EllipticEst.Q0 :=
      fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
    have hc := (hF.continuousOn_HkIntegrand α k).comp
      (continuousOn_id.prodMk continuousOn_const) hmap
    simpa only [Function.comp_def, id_eq] using hc
  have hIntL1 : IntervalIntegrable
      (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ =>
      (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
      (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact hcontW.pow 2
  have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact hHkcont
  have hIntL2 : IntervalIntegrable
      (fun x : ℝ => (Work.Spaces.DzIter i f x σ) ^ 2) volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => (Work.Spaces.DzIter i f x σ) ^ 2)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hcont.pow 2
  have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
  -- the pointwise domination of the two weighted window integrands
  have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
      (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ
        = Work.Spaces.DzIter (i + 1) f x σ := rfl
    have hA : (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * σ)) Work.Spaces.eta hsinσ.le
        (ne_of_gt Work.Spaces.eta_pos)
    have hB : (Work.Spaces.DzIter (i + 1) f x σ
          * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter (i + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow, Work.FTS.H2.div_rpow_sq (Work.Spaces.w x) (Real.sin (2 * σ))
        Work.Spaces.eta hsinσ.le (ne_of_gt Work.Spaces.eta_pos)]
      ring
    calc (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter (i + 1) f x σ * Work.Spaces.w x) ^ 2 := by rw [hA, hcomm]
      _ = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DzIter (i + 1) f x σ
              * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [hB, mul_pow]; ring
      _ ≤ (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ :=
          mul_le_mul_of_nonneg_left
            (Work.Spaces.sq_le_HkIntegrand_z α k f x σ (i + 1) hi) (sq_nonneg _)
  have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
      (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (Work.Spaces.DzIter i f x σ) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos hx.1
    have hwx : 1 ≤ Work.Spaces.w x := Work.FTS.TransportS.one_le_w hx0
    have hA : (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * σ)) Work.Spaces.eta hsinσ.le
        (ne_of_gt Work.Spaces.eta_pos)
    have hB : (Work.Spaces.DzIter i f x σ
          * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow, Work.FTS.H2.div_rpow_sq (Work.Spaces.w x) (Real.sin (2 * σ))
        Work.Spaces.eta hsinσ.le (ne_of_gt Work.Spaces.eta_pos)]
      ring
    have hwx2 : (1 : ℝ) ≤ (Work.Spaces.w x) ^ 2 := one_le_pow₀ hwx
    have hXle : (Work.Spaces.DzIter i f x σ) ^ 2
        ≤ (Work.Spaces.DzIter i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hwx2
        (sq_nonneg (Work.Spaces.DzIter i f x σ))
      simpa using h
    calc (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter i f x σ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter i f x σ) ^ 2 := by rw [hA]
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          * ((Work.Spaces.DzIter i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2) :=
          mul_le_mul_of_nonneg_left hXle (by positivity)
      _ = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DzIter i f x σ
              * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [hB]; ring
      _ ≤ (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ :=
          mul_le_mul_of_nonneg_left
            (Work.Spaces.sq_le_HkIntegrand_z α k f x σ i (by omega)) (sq_nonneg _)
  -- the two window integrals are dominated by the full radial integral
  have hbigA : ∫ x in z..(2 * R₀), (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ
      ≤ (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [intervalIntegral.integral_of_le hz2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Filter.Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
  have hbigB : ∫ x in R₀..(2 * R₀), (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ
      ≤ (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [intervalIntegral.integral_of_le hR2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Filter.Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
  have hmonoA := intervalIntegral.integral_mono_on hz2R (hIntL1.const_mul _) (hIntR1.const_mul _)
    hptA
  have hmonoB := intervalIntegral.integral_mono_on hR2R (hIntL2.const_mul _) (hIntR2.const_mul _)
    hptB
  have hmAeq : (∫ x in z..(2 * R₀),
        (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
      = (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (∫ x in z..(2 * R₀),
            (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2) :=
    intervalIntegral.integral_const_mul _ _
  have hmBeq : (∫ x in R₀..(2 * R₀),
        (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter i f x σ) ^ 2)
      = (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter i f x σ) ^ 2) :=
    intervalIntegral.integral_const_mul _ _
  have hcoe : (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
      * (Work.Spaces.DzIter i f z σ) ^ 2
      = (Work.Spaces.DzIter i f z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [mul_pow]; ring
  rw [← hcoe]
  calc (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (Work.Spaces.DzIter i f z σ) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (2 * (∫ x in z..(2 * R₀),
              (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
          + (2 / R₀) * ∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter i f x σ) ^ 2) :=
        mul_le_mul_of_nonneg_left hwin hAnn
    _ = 2 * ((Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
            * (∫ x in z..(2 * R₀),
              (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2))
          + (2 / R₀) * ((Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
            * (∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter i f x σ) ^ 2)) := by ring
    _ = 2 * (∫ x in z..(2 * R₀),
            (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
          + (2 / R₀) * (∫ x in R₀..(2 * R₀),
            (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (Work.Spaces.DzIter i f x σ) ^ 2) := by rw [← hmAeq, ← hmBeq]
    _ ≤ 2 * ((Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
          + (2 / R₀) * ((Work.Spaces.w z) ^ 2
              * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num)
        · exact mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity)
    _ = (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by ring

theorem HkIntegrand_zslot_perz_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.Nonlin.BdryTraces α 6 f → ∀ i : ℕ, i ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
  refine ⟨3, by norm_num, ?_⟩
  intro α hα f hF hmem htr i hi z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- ### `z = 0`: the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    have hzero : (fun θ : ℝ => (Work.Spaces.DzIter i f 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [hw0, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [hzero]
    have h1 : (∫ _θ in Work.Spaces.Iθ, (0 : ℝ)) = 0 := by simp
    rw [h1]
    have h2 : 0 ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (1 : ℝ) + (Work.Spaces.w 0) ^ 2 := by rw [hw0]; norm_num
    nlinarith [h2, h3]
  · -- ### `z > 0`: the window bound at every angle, then integrate in `θ`
    have hR : z ≤ max z 2 := le_max_left z 2
    have hRpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
    have h2max : (2 : ℝ) ≤ max z 2 := le_max_right z 2
    obtain ⟨hswap, hGint, hGslice⟩ :=
      Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6 α f hF hmem
    -- almost every angle is interior
    have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)] with σ h
      exact fun hmem' => h.mpr hmem'
    -- the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 6 f s σ)) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact zslot_window_perz_aux α hF 6 i (by omega) hzpos hR hσθ hσint
    -- integrability of the two sides
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.integrableOn_zSummand α 6 hF hmem i (by omega)
        (Set.mem_Ici.mpr hzpos.le)
    have hRI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 6 f s σ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hGint.const_mul ((Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2))
    -- the integral bound
    have hmain : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 6 f := by
      have h1 := MeasureTheory.integral_mono_ae hLI hRI hle
      rw [MeasureTheory.integral_const_mul, hswap] at h1
      exact h1
    -- the coefficient is at most `3`
    have hcoef : 2 + 2 / max z 2 ≤ 3 := by
      have h : 2 / max z 2 ≤ 1 := by
        rw [div_le_one hRpos]
        exact h2max
      linarith
    have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
    have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hXsq : Work.Spaces.HkSq α 6 f
        ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
      have h4 : Work.FTS.StrongGlobal.Xn6 α f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
      rw [h4]
      nlinarith [Real.sq_sqrt hHknn, hXnn, hHknn]
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 6 f := hmain
      _ ≤ (Work.Spaces.w z) ^ 2 * 3 * Work.Spaces.HkSq α 6 f := by
          have h := mul_le_mul_of_nonneg_right hcoef hHknn
          nlinarith [h, sq_nonneg (Work.Spaces.w z)]
      _ ≤ 3 * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
          have hstep : (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 6 f
              ≤ (1 + (Work.Spaces.w z) ^ 2)
                * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 :=
            mul_le_mul (by linarith [sq_nonneg (Work.Spaces.w z)]) hXsq hHknn
              (by linarith [sq_nonneg (Work.Spaces.w z)])
          nlinarith [mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 3)]

end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroLayerTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open scoped Real Topology
open Filter

/-- **The boundary-layer error of the zero-mode cut-off tends to `0`.**

`δ_n = 1/(n+1)`, and the layer contributes the factor `(1 + 1/δ_n)·(2δ_n)^{(3+η)/2}`.  Since
`(1 + 1/δ_n)·(2δ_n)^{s} = 2^s·(δ_n^s + δ_n^{s-1})`, the whole product is a constant times a sum
of two negative powers of `δ_n`, hence tends to `0` as `n → ∞` (`tendsto_delta_rpow`). -/
theorem SlotsZeroLayerTendsto {A C M : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    Filter.Tendsto (fun n : ℕ =>
      A * (1 + 1 / Work.FTS.StrongEps.EComparison.delta n)
        * (2 * C * (2 * Work.FTS.StrongEps.EComparison.delta n) ^ ((3 + Work.Spaces.eta) / 2)
            * M))
      Filter.atTop (nhds 0) := by
  set s : ℝ := (3 + Work.Spaces.eta) / 2 with hsdef
  have hs : 0 < s := by
    rw [hsdef]; have := Work.Spaces.eta_pos; linarith
  have hs1 : 0 < s - 1 := by
    rw [hsdef]; have := Work.Spaces.eta_pos; linarith
  have hfun : (fun n : ℕ =>
        A * (1 + 1 / delta n) * (2 * C * (2 * delta n) ^ s * M))
      = fun n : ℕ => (A * 2 * C * M * 2 ^ s) * ((delta n) ^ s + (delta n) ^ (s - 1)) := by
    funext n
    have hδ : 0 < delta n := by rw [delta]; positivity
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le]
    have hsplit : (1 + 1 / delta n) * (delta n) ^ s
        = (delta n) ^ s + (delta n) ^ (s - 1) := by
      rw [add_mul, one_mul, one_div, ← Real.rpow_neg_one (delta n), mul_comm,
        ← Real.rpow_add hδ]
      rw [show s + (-1 : ℝ) = s - 1 from by ring]
    calc A * (1 + 1 / delta n) * (2 * C * (2 ^ s * (delta n) ^ s) * M)
        = (A * 2 * C * M * 2 ^ s) * ((1 + 1 / delta n) * (delta n) ^ s) := by ring
      _ = (A * 2 * C * M * 2 ^ s) * ((delta n) ^ s + (delta n) ^ (s - 1)) := by
            rw [hsplit]
  rw [hfun]
  have h1 : Tendsto (fun n : ℕ => (delta n) ^ s + (delta n) ^ (s - 1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_delta_rpow hs).add (tendsto_delta_rpow hs1)
    simpa using h
  simpa using h1.const_mul (A * 2 * C * M * 2 ^ s)

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsConv =====
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

/-- **The convergence package of the extraction.**  `ConvLocUnifH6 α B G f` says that the profiles
`G n` converge to `f` locally uniformly on the open quadrant *together with every slot of order
`≤ 4`*, that `f` is `C⁴` there, and that the `ℋ⁶`-bound of the sequence passes to the limit.

The slot clause is what `LocUnif.exists_subseq_deriv4_of_uniform_H6` produces; re-exposing it here
is what lets the limit of the *equation* be identified slot by slot. -/
def ConvLocUnifH6 (α B : ℝ) (G : ℕ → Fn) (f : Fn) : Prop :=
  (∀ (K : Set (ℝ × ℝ)), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ (j i : ℕ), j + i ≤ 4 →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G n) p.1 p.2)
          (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K) ∧
    ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkNorm α 6 f ≤ B

/-- The slot-convergence clause of `ConvLocUnifH6`, unbundled. -/
theorem ConvLocUnifH6.conv {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f) :
    ∀ (K : Set (ℝ × ℝ)), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ (j i : ℕ), j + i ≤ 4 →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G n) p.1 p.2)
          (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K := h.1

/-- The `C⁴`-clause of `ConvLocUnifH6`. -/
theorem ConvLocUnifH6.contDiffOn {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f) :
    ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := h.2.1

/-- The `ℋ⁶`-clause of `ConvLocUnifH6`. -/
theorem ConvLocUnifH6.hkNorm_le {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f) :
    Work.Spaces.HkNorm α 6 f ≤ B := h.2.2

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ThShiftAEMeasurable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. measurability of the angular shift on `Iθ × [-ε,ε]`

The angular shift `(θ, p) ↦ thShift θ p = arctan (tan θ · e^{-p})` of the log-coordinate
`ε`-mollifier is **not** continuous on `ℝ × ℝ` (at `θ = π/2` the `tan` has a pole, while Lean's
`tan (π/2) = 0`), but it *is* continuous on the conull set `{x | x.1 ∈ (0,π/2)}` for the product
measure `(volume.restrict Iθ).prod (volume.restrict (Icc (-ε) ε))`: with `Iθ = [0,π/2]`, the
complement of `(0,π/2)` inside `Iθ` is the two-point set `{0, π/2}`.

Following the pattern of `HkSqAux/aemeasurable_shift_slice.lean`, the composite is continuous on
that conull set, hence a.e. measurable there; multiplying by the indicator of the set and
removing it again with conullity gives a.e. measurability for the full measure.

This is the measurability input shared by `ThShiftPreimageNull` (the null-preimage statement) and
`LintegralProdThShift` (the product bound for `lintegral_thShift_le`).
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

set_option autoImplicit false

/-- `θ = 0` and `θ = π/2` are null for `volume.restrict Iθ` with `Iθ = [0, π/2]`. -/
theorem measure_Iθ_compl_Ioo_eq_zero :
    (volume.restrict Work.Spaces.Iθ) (Set.Ioo 0 (π / 2))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  refine measure_mono_null ?_ (measure_union_null (measure_singleton (0 : ℝ))
    (measure_singleton (π / 2)))
  intro x hx
  simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
    Set.mem_union, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨hxn, hxI⟩ := hx
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rcases lt_or_ge x (π / 2) with h2 | h2
    · exact absurd ⟨h, h2⟩ hxn
    · exact Or.inr (le_antisymm hxI.2 h2)
  · exact Or.inl (le_antisymm h hxI.1)

/-- **A.e. measurability of the angular shift** `x ↦ thShift x.1 x.2` for the product of the
angular measure on `Iθ = [0,π/2]` with the shift measure on `[-ε,ε]`. -/
theorem aemeasurable_thShift_prod {ε : ℝ} :
    AEMeasurable (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2)
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) := by
  classical
  set S : Set (ℝ × ℝ) := {x | x.1 ∈ Set.Ioo 0 (π / 2)} with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioo.preimage measurable_fst
  have hSnull :
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) Sᶜ = 0 := by
    rw [show Sᶜ = (Set.Ioo 0 (π / 2))ᶜ ×ˢ (Set.univ : Set ℝ) from by
      ext x; simp [S]]
    rw [Measure.prod_prod, measure_Iθ_compl_Ioo_eq_zero, zero_mul]
  have hcont : ContinuousOn (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2) S := by
    have hcos : ∀ x ∈ S, Real.cos x.1 ≠ 0 := fun x hx =>
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩).ne'
    have h1 : ContinuousOn (fun x : ℝ × ℝ => Real.tan x.1 * Real.exp (-x.2)) S :=
      (Real.continuousOn_tan.comp continuousOn_fst hcos).mul
        (Real.continuous_exp.comp_continuousOn (by fun_prop))
    simpa only [Work.FTS.StrongEps.thShift, Function.comp_def] using
      Real.continuous_arctan.comp_continuousOn h1
  have hA : AEMeasurable (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2)
      (((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))).restrict S) :=
    hcont.aemeasurable hSmeas
  have hind : AEMeasurable (S.indicator (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  refine hind.congr ?_
  filter_upwards [compl_mem_ae_iff.mpr hSnull] with x hx
  simp only [Set.mem_compl_iff, not_not] at hx
  exact Set.indicator_of_mem hx (fun x : ℝ × ℝ => Work.FTS.StrongEps.thShift x.1 x.2)

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.mixed_fam_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

/-! ## The joint derivative operators on `ℝ × (ℝ × ℝ)` -/

/-- The `z`-partial derivative of the slice `z ↦ Φ (t, (z, θ))`, at the point `q = (t, (z, θ))`. -/
def pzJ (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  deriv (fun z' => Φ (q.1, (z', q.2.2))) q.2.1

/-- The `θ`-partial derivative of the slice `θ ↦ Φ (t, (z, θ))`, at the point `q = (t, (z, θ))`. -/
def pthJ (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  deriv (fun θ' => Φ (q.1, (q.2.1, θ'))) q.2.2

/-- The joint `D_z`-operator: `z · ∂_z` on the slice. -/
def DzJ (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ := q.2.1 * pzJ Φ q

/-- The joint `D_θ`-operator: `sin (2θ) · ∂_θ` on the slice. -/
def DthJ (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  Real.sin (2 * q.2.2) * pthJ Φ q

/-- Iterated joint `D_z`. -/
def DzIterJ : ℕ → (ℝ × (ℝ × ℝ) → ℝ) → (ℝ × (ℝ × ℝ) → ℝ)
  | 0, Φ => Φ
  | n + 1, Φ => DzJ (DzIterJ n Φ)

/-- Iterated joint `D_θ`. -/
def DthIterJ : ℕ → (ℝ × (ℝ × ℝ) → ℝ) → (ℝ × (ℝ × ℝ) → ℝ)
  | 0, Φ => Φ
  | n + 1, Φ => DthJ (DthIterJ n Φ)


@[simp] theorem DzIterJ_zero (Φ : ℝ × (ℝ × ℝ) → ℝ) : DzIterJ 0 Φ = Φ := rfl

@[simp] theorem DzIterJ_succ (n : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ) :
    DzIterJ (n + 1) Φ = DzJ (DzIterJ n Φ) := rfl

@[simp] theorem DthIterJ_zero (Φ : ℝ × (ℝ × ℝ) → ℝ) : DthIterJ 0 Φ = Φ := rfl

@[simp] theorem DthIterJ_succ (n : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ) :
    DthIterJ (n + 1) Φ = DthJ (DthIterJ n Φ) := rfl

/-! ## `pzJ`, `pthJ` are Fréchet derivatives in fixed directions -/



/-! ## The operators lower the differentiability order by one -/








/-! ## The joint operators are the ordinary ones on the slices -/






/-! ## The main statement -/


end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `sin(2θ)^{-η}`-weighted angular `L²`-energy of the `k`-th `D_z`-iterate of `x`:
`Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² · sin(2θ)^{-η} dθ`. -/
def Pz (x : Work.FTS.Galerkin.Fn) (k : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter k x z θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The angular correlation of two consecutive `D_z`-iterates of `x`:
`Qz x k z = ∫_{Iθ} D_z^k x (z,θ) · D_z^{k+1} x (z,θ) · sin(2θ)^{-η} dθ`.

It is the numerator of the derivative of `Pz`: `z · (Pz x k)' z = 2 · Qz x k z`. -/
def Qz (x : Work.FTS.Galerkin.Fn) (k : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter k x z θ * Work.Spaces.DzIter (k + 1) x z θ
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `sin(2θ) ≥ 0` on the angular interval `Iθ`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  have h : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
  obtain ⟨h1, h2⟩ := h
  exact Real.sin_nonneg_of_mem_Icc
    ⟨by linarith, by linarith [h2, Real.pi_pos]⟩

/-- `Pz` is an integral of a nonnegative integrand, hence nonnegative. -/
theorem Pz_nonneg (x : Work.FTS.Galerkin.Fn) (k : ℕ) (z : ℝ) : 0 ≤ Pz x k z := by
  refine MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ)
    (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc) fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)

/-- **The angular weight identity.**  The weighted `D_z`-summand of `HkIntegrand` is the
`sin(2θ)^{-η}`-weighted square of the same derivative: on `Iθ`,
`(D_z^k x · w/ sin(2θ)^{η/2})² = (D_z^k x)² · sin(2θ)^{-η} · w²`. -/
theorem summand_sq_eq (x : Work.FTS.Galerkin.Fn) (k : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter k x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter k x z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.w z) ^ 2 := by
  have hs := sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    simp only [Real.zero_rpow (show (-(Work.Spaces.eta)) ≠ 0 by norm_num [Work.Spaces.eta]),
      Real.zero_rpow (show (Work.Spaces.eta / 2) ≠ 0 by norm_num [Work.Spaces.eta]),
      mul_zero, div_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add h]
      ring_nf
    rw [mul_pow, div_pow, hsq, Real.rpow_neg h.le]
    field_simp

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.ae_eq_comp_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux



end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.measurable_integral_sub_conv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux


end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Work.Jeps_smul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Work

open scoped Real
open Work.FTS.StrongEps
open MeasureTheory

/-- `Jeps` is `ℝ`-homogeneous in the profile: `J_ε(c f) = c · J_ε f`.

This is immediate from the definition: on the open quadrant `Jeps` is the log-coordinate
convolution `p ↦ Jker ρ ε p * f (zShift z p.1) (thShift θ p.2)`, and on the boundary both sides
vanish; the only ingredient is the linearity of the Bochner integral in the scalar factor. -/
theorem Jeps_smul (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (f : Work.FTS.Galerkin.Fn) :
    Work.FTS.StrongEps.Jeps ρ ε (c • f) = c • Work.FTS.StrongEps.Jeps ρ ε f := by
  funext z θ
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · rw [Jeps_eq_integral ρ ε (c • f) hc.1 hc.2, Jeps_eq_integral ρ ε f hc.1 hc.2]
    rw [← integral_const_mul c (fun p : ℝ × ℝ =>
      Jker ρ ε p * f (zShift z p.1) (thShift θ p.2))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring)
  · rw [Jeps_eq_zero ρ ε (c • f) hc, Jeps_eq_zero ρ ε f hc, mul_zero]

end Work.FTS.StrongEps.EpsE4Work
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.RhoMargFubini =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem RhoMargFubini {ρ : ℝ × ℝ → ℝ} {ε z : ℝ} (hε : 0 < ε) {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1))))) :
    ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1)))
      = ∫ s, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s))) := by
  -- (The sign of `ε` is irrelevant here; record the hypothesis so the binding is used.)
  have _hε : (0 : ℝ) < ε := hε
  -- The measure on `ℝ × ℝ` is the product of the two Lebesgue measures.
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  -- Fubini for the Bochner integral (the integrand is given as integrable).
  rw [MeasureTheory.integral_prod
    (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) hint]
  -- In the inner integral the factor `lam (z * exp (-(ε * s)))` is a constant, so it
  -- can be pulled out; the equality holds pointwise (hence a.e.).
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  exact MeasureTheory.integral_mul_const (lam (z * Real.exp (-(ε * s)))) (fun t => ρ (s, t))

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.RhoMargProps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.ThShiftSmall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `θ`-shift is small when `θ` is small.**  For `ε > 0` there is `θ₀ > 0` with

  `thShift θ p₂ = arctan (tan θ * exp (-p₂)) ∈ (0, π/4)`

for every `θ ∈ (0, θ₀)` and every `p₂` with `|p₂| ≤ ε`.  (`Work.FTS.StrongEps.thShift`.)

Route: `θ₀ := min (π/4) (arctan (exp (-ε))) > 0` works.  Lower bound: `tan θ > 0` for `θ > 0`
small and `exp (-p₂) > 0`, so the arctangent argument is positive; upper bound:
`arctan (tan θ * exp (-p₂)) ≤ arctan (tan θ * exp ε) < arctan 1 = π/4` because `exp (-p₂) ≤ exp ε`
(on `|p₂| ≤ ε`) and `tan` is strictly increasing below `π/2` with `tan (arctan (exp (-ε))) = exp (-ε)`,
so `θ < arctan (exp (-ε))` gives `tan θ * exp ε < 1`.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem ThShiftSmall {ε : ℝ} (hε : 0 < ε) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ ∈ Set.Ioo 0 θ₀, ∀ p₂ : ℝ, |p₂| ≤ ε →
      Work.FTS.StrongEps.thShift θ p₂ ∈ Set.Ioo 0 (Real.pi/4) := by
  -- `θ₀ := arctan (exp (-ε))` is positive, and `exp (-ε) < 1` (so `θ₀ < π/4`).
  have hexp_lt_one : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine ⟨Real.arctan (Real.exp (-ε)), Real.arctan_pos.mpr (Real.exp_pos _), ?_⟩
  intro θ hθ p₂ hp₂
  have hθ0 : 0 < θ := hθ.1
  have hθθ : θ < Real.arctan (Real.exp (-ε)) := hθ.2
  -- `θ < π/2`, so `tan θ > 0`
  have hθπ2 : θ < Real.pi / 2 := lt_trans hθθ (Real.arctan_lt_pi_div_two _)
  have htpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθπ2
  constructor
  · -- lower bound: the arctangent argument is positive
    rw [Work.FTS.StrongEps.thShift]
    exact Real.arctan_pos.mpr (mul_pos htpos (Real.exp_pos _))
  · -- upper bound: `tan θ * exp (-p₂) ≤ tan θ * exp ε < exp (-ε) * exp ε = 1`
    have htanθ : Real.tan θ < Real.exp (-ε) := by
      have h1 : Real.tan θ < Real.tan (Real.arctan (Real.exp (-ε))) :=
        Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos])
          (Real.arctan_lt_pi_div_two _) hθθ
      rwa [Real.tan_arctan] at h1
    have hexp_le : Real.exp (-p₂) ≤ Real.exp ε := by
      rw [Real.exp_le_exp]
      linarith [neg_le_abs p₂, hp₂]
    rw [Work.FTS.StrongEps.thShift, ← Real.arctan_one]
    apply Real.arctan_lt_arctan_iff.mpr
    calc Real.tan θ * Real.exp (-p₂) ≤ Real.tan θ * Real.exp ε :=
          mul_le_mul_of_nonneg_left hexp_le (le_of_lt htpos)
      _ < Real.exp (-ε) * Real.exp ε := mul_lt_mul_of_pos_right htanθ (Real.exp_pos ε)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceZeroOfConv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TraceZeroOfConv` — a vanishing test for the log-coordinate trace

If `ρ` is a mollifier kernel (`IsMollKernel`), `ε > 0`, `lam` measurable with
`u ↦ lam (exp u)` integrable, and for every `z > 0`

  `∫ s, (∫ t, ρ (s,t)) * lam (z * exp (-(ε * s))) = 0`,

then `lam = 0` a.e. on `(0,∞)`.

The argument: let `F` be the `s`-marginal of `ρ` (integrable, supported in `[-1,1]`, mass `1`),
and `L v := lam (exp (ε * v))`.  Writing `z = exp (ε σ)` the hypothesis says that `F ⋆ L = 0`
identically.  Both are integrable, so taking Fourier transforms gives `𝓕 F · 𝓕 L = 0`; by
`FourierZeroNull` the first factor is nonzero a.e., whence `𝓕 L = 0` a.e. and `L = 0` a.e.
(duality against Schwartz functions).  Finally the substitution `v ↦ exp (ε v)` carries the
null set back to `(0,∞)`.

The Fourier-injectivity step is `ConvInjective` in the form where its hypothesis
`Continuous ρ` — used there only to obtain `Integrable ρ` — is replaced by `Integrable ρ`.
-/

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology FourierTransform ContDiff SchwartzMap ENNReal
open MeasureTheory Set Filter

noncomputable section

/-- `ConvInjective` with the integrability of the kernel supplied directly (its continuity is used
in that proof only to deduce integrability).  Complex-valued version, in the multiplicative
form of the convolution matching `convolution_def`. -/
private theorem convInjective_int {ρ f : ℝ → ℂ} (hρ_int : MeasureTheory.Integrable ρ)
    (hF : ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 ρ ξ ≠ 0)
    (hf : MeasureTheory.Integrable f)
    (hconv : ∀ u : ℝ, ∫ s, ρ s * f (u - s) = 0) :
    f =ᵐ[MeasureTheory.volume] 0 := by
  have hconv_zero : convolution ρ f (ContinuousLinearMap.mul ℂ ℂ) volume = 0 := by
    funext u
    rw [convolution_def]
    have h1 : (fun t : ℝ => (ContinuousLinearMap.mul ℂ ℂ) (ρ t) (f (u - t))) =
        fun t => ρ t * f (u - t) := funext fun t => rfl
    rw [h1, hconv u]
    simp
  -- hence the Fourier transform of `f` vanishes a.e.
  have hprod : ∀ ξ : ℝ, 𝓕 ρ ξ * 𝓕 f ξ = 0 := by
    intro ξ
    rw [← Real.fourier_mul_convolution_eq (f₁ := ρ) (f₂ := f) hρ_int hf ξ, hconv_zero]
    simp [Real.fourier_eq]
  have hzero : (fun ξ => 𝓕 f ξ) =ᵐ[MeasureTheory.volume] 0 := by
    filter_upwards [hF] with ξ hξ
    exact (mul_eq_zero.mp (hprod ξ)).resolve_left hξ
  -- it remains to deduce `f = 0` a.e., by duality against compactly supported smooth tests
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable ?_
  intro ψ hψ hψc
  let Ψ : 𝓢(ℝ, ℂ) := (hψc.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)).toSchwartzMap
    (ContDiff.comp (ContinuousLinearMap.contDiff Complex.ofRealCLM) hψ)
  have hΨcoe : (Ψ : ℝ → ℂ) = fun x => (ψ x : ℂ) := by
    ext x; simp [Ψ]
  let g₀ : 𝓢(ℝ, ℂ) := 𝓕⁻ Ψ
  have hg₀ : (𝓕 (g₀ : ℝ → ℂ)) = fun x => (ψ x : ℂ) := by
    rw [← SchwartzMap.fourier_coe g₀, show 𝓕 g₀ = Ψ from FourierInvPair.fourier_fourierInv_eq Ψ]
    exact hΨcoe
  -- the Fourier duality identity `∫ f 𝓕 g = ∫ 𝓕 f g`
  have hdual : ∫ x, f x • (𝓕 (g₀ : ℝ → ℂ)) x =
      ∫ ξ, (𝓕 f) ξ • (g₀ : ℝ → ℂ) ξ := by
    have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul ℂ ℂ)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf
      (SchwartzMap.integrable (μ := volume) g₀)
    simpa [ContinuousLinearMap.lsmul_apply, VectorFourier.fourierIntegral, Real.fourier_eq,
      LinearMap.flip_apply] using h.symm
  have hrhs : ∫ ξ, (𝓕 f) ξ • (g₀ : ℝ → ℂ) ξ = 0 := by
    have : (fun ξ => (𝓕 f) ξ • (g₀ : ℝ → ℂ) ξ) =ᵐ[volume] 0 := by
      filter_upwards [hzero] with ξ hξ
      simp [hξ]
    rw [integral_congr_ae this]
    simp
  have key : (∫ x : ℝ, ψ x • f x) = 0 := by
    have h1 : (∫ x : ℝ, f x • (𝓕 (g₀ : ℝ → ℂ)) x) = ∫ x : ℝ, ψ x • f x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hg₀]
      simp only [Complex.real_smul]
      ring
    rw [← h1, hdual, hrhs]
  exact key

/-! ## The `s`-marginal of the kernel and the log-coordinate trace -/

/-- The `s`-marginal of a kernel `ρ : ℝ × ℝ → ℝ`. -/
private noncomputable def marg (ρ : ℝ × ℝ → ℝ) : ℝ → ℝ := fun s => ∫ t, ρ (s, t)

/-- The trace of `lam` in the log-coordinate `v` (with `z = exp (ε v)`). -/
private noncomputable def logTrace (lam : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun v => lam (Real.exp (ε * v))

private theorem marg_integrable {ρ : ℝ × ℝ → ℝ} (hρ : MeasureTheory.Integrable ρ) :
    MeasureTheory.Integrable (marg ρ) := by
  have h : MeasureTheory.Integrable ρ
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) := by
    rwa [← MeasureTheory.Measure.volume_eq_prod]
  exact h.integral_prod_left

private theorem marg_integral {ρ : ℝ × ℝ → ℝ} (hρ : MeasureTheory.Integrable ρ) :
    (∫ s : ℝ, marg ρ s) = ∫ p : ℝ × ℝ, ρ p := by
  have h : MeasureTheory.Integrable ρ
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) := by
    rwa [← MeasureTheory.Measure.volume_eq_prod]
  have hf : (∫ s : ℝ, ∫ t : ℝ, ρ (s, t)) = (∫ p : ℝ × ℝ, ρ p) := by
    have h2 := MeasureTheory.integral_prod (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) ρ h
    rw [← MeasureTheory.Measure.volume_eq_prod] at h2
    exact h2.symm
  simpa only [marg] using hf

private theorem marg_eq_zero_of_not_mem {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : marg ρ x = 0 := by
  have hzero : ∀ t : ℝ, ρ (x, t) = 0 := by
    intro t
    by_contra hne
    have hle : x ^ 2 + t ^ 2 ≤ 1 := hρ.support (x, t) hne
    have h1 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    exact hx (abs_le.mp ((sq_le_one_iff_abs_le_one x).mp h1))
  simp only [marg, hzero, integral_zero]

private theorem fourier_marg_ne_zero {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    (hρint : MeasureTheory.Integrable ρ) (hmass : (∫ p : ℝ × ℝ, ρ p) = 1) :
    ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 (fun x : ℝ => (marg ρ x : ℂ)) ξ ≠ 0 := by
  refine FourierZeroNull (marg_integrable hρint).ofReal ?_ ?_
  · intro x hx
    simp only [marg_eq_zero_of_not_mem hρ hx, Complex.ofReal_zero]
  · have h0 : (∫ x : ℝ, ((marg ρ x : ℝ) : ℂ)) = ((1 : ℝ) : ℂ) := by
      have h1 : (∫ x : ℝ, ((marg ρ x : ℝ) : ℂ)) = ((∫ x : ℝ, marg ρ x : ℝ) : ℂ) :=
        integral_ofReal
      rw [h1, marg_integral hρint, hmass]
    rw [h0]
    exact one_ne_zero

/-- Integrability of the log-coordinate trace, from the integrability of `u ↦ lam (exp u)`. -/
private theorem integrable_logTrace {ε : ℝ} (hε : 0 < ε) {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u))) :
    MeasureTheory.Integrable (logTrace lam ε) :=
  hint.comp_mul_left' hε.ne'

/-- A null set of log-coordinates has null image under `v ↦ exp (ε v)`. -/
private theorem ae_zero_on_Ioi_of_logTrace {ε : ℝ} (hε : 0 < ε) {lam : ℝ → ℝ}
    (hlamm : Measurable lam) (h : logTrace lam ε =ᵐ[MeasureTheory.volume] 0) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), lam z = 0 := by
  set S : Set ℝ := {z : ℝ | ¬ lam z = 0} ∩ Set.Ioi 0 with hSdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact ((hlamm (measurableSet_singleton 0)).compl).inter measurableSet_Ioi
  have hkey : MeasureTheory.volume S = 0 := by
    have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun v : ℝ => Real.exp (ε * v))
        (Real.exp (ε * x) * ε) Set.univ x := fun x _ => by
      simpa only [Function.comp_def] using
        ((Real.hasDerivAt_exp (ε * x)).comp x (hasDerivAt_const_mul (x := x) ε)).hasDerivWithinAt
          (s := Set.univ)
    have hinj : Set.InjOn (fun v : ℝ => Real.exp (ε * v)) Set.univ := by
      intro a _ b _ hab
      exact mul_left_cancel₀ hε.ne' (Real.exp_eq_exp.mp hab)
    have hrange : (fun v : ℝ => Real.exp (ε * v)) '' Set.univ = Set.Ioi 0 := by
      ext z
      constructor
      · rintro ⟨v, -, rfl⟩
        simpa using Real.exp_pos (ε * v)
      · intro hz
        refine ⟨Real.log z / ε, Set.mem_univ _, ?_⟩
        show Real.exp (ε * (Real.log z / ε)) = z
        rw [mul_div_cancel₀ (Real.log z) hε.ne', Real.exp_log hz]
    let g : ℝ → ℝ≥0∞ := S.indicator (fun _ => 1)
    have hlint := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ)
      (f := fun v : ℝ => Real.exp (ε * v)) (f' := fun x : ℝ => Real.exp (ε * x) * ε)
      MeasurableSet.univ hderiv hinj g
    rw [hrange, MeasureTheory.Measure.restrict_univ] at hlint
    have hlhs : (∫⁻ z in Set.Ioi (0 : ℝ), g z) = MeasureTheory.volume S := by
      have h1 : (∫⁻ z in Set.Ioi (0 : ℝ), g z) =
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) S :=
        MeasureTheory.lintegral_indicator_one hSmeas
      rw [h1, MeasureTheory.Measure.restrict_apply hSmeas,
        Set.inter_eq_left.mpr Set.inter_subset_right]
    have hrhs : (∫⁻ x : ℝ, ENNReal.ofReal |Real.exp (ε * x) * ε| * g (Real.exp (ε * x))) = 0 := by
      have hz : (fun x : ℝ => ENNReal.ofReal |Real.exp (ε * x) * ε| * g (Real.exp (ε * x)))
          =ᵐ[MeasureTheory.volume] 0 := by
        filter_upwards [h] with x hx
        have hxS : Real.exp (ε * x) ∉ S := by
          intro hmem
          exact hmem.1 (by simpa only [logTrace, Pi.zero_apply] using hx)
        simp only [g, Set.indicator_of_notMem hxS, mul_zero, Pi.zero_apply]
      rw [MeasureTheory.lintegral_congr_ae hz]
      simp
    rw [hlhs, hrhs] at hlint
    exact hlint
  rw [MeasureTheory.ae_iff]
  have hgoal : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) {z : ℝ | ¬ lam z = 0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioi, ← hSdef]
    exact hkey
  exact hgoal

theorem TraceZeroOfConv (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    (hlamm : Measurable lam)
    (hconv : ∀ z : ℝ, 0 < z →
      (∫ s : ℝ, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))) = 0) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), lam z = 0 := by
  have hρint : MeasureTheory.Integrable ρ := by
    refine hρ.cont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) (isCompact_Icc.prod isCompact_Icc) ?_
    intro p hp
    have hle : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := hρ.support p hp
    have h1 : p.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.2]
    have h2 : p.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.1]
    exact ⟨abs_le.mp ((sq_le_one_iff_abs_le_one p.1).mp h1),
      abs_le.mp ((sq_le_one_iff_abs_le_one p.2).mp h2)⟩
  have hFint : MeasureTheory.Integrable (marg ρ) := marg_integrable hρint
  have hFourier : ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 (fun x : ℝ => (marg ρ x : ℂ)) ξ ≠ 0 :=
    fourier_marg_ne_zero hρ hρint hρ.mass
  have hLint : MeasureTheory.Integrable (logTrace lam ε) := integrable_logTrace hε hint
  have hLzero : logTrace lam ε =ᵐ[MeasureTheory.volume] 0 := by
    have hLc : (fun v : ℝ => (logTrace lam ε v : ℂ)) =ᵐ[MeasureTheory.volume] 0 := by
      refine convInjective_int (ρ := fun x : ℝ => (marg ρ x : ℂ))
        (f := fun v : ℝ => (logTrace lam ε v : ℂ)) hFint.ofReal hFourier hLint.ofReal ?_
      intro σ
      have hpt : ∀ s : ℝ, lam (Real.exp (ε * σ) * Real.exp (-(ε * s))) =
          logTrace lam ε (σ - s) := by
        intro s
        have hxy : Real.exp (ε * σ) * Real.exp (-(ε * s)) = Real.exp (ε * (σ - s)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hxy, logTrace]
      have hreal : (∫ s : ℝ, marg ρ s * logTrace lam ε (σ - s)) = 0 := by
        have hbig := hconv (Real.exp (ε * σ)) (Real.exp_pos _)
        rw [← hbig]
        refine integral_congr_ae (Eventually.of_forall fun s => ?_)
        simp only [marg]
        rw [hpt s]
      have hcmul : (fun s : ℝ => (marg ρ s : ℂ) * ((logTrace lam ε (σ - s) : ℝ) : ℂ)) =
          fun s => ((marg ρ s * logTrace lam ε (σ - s) : ℝ) : ℂ) :=
        funext fun s => (Complex.ofReal_mul _ _).symm
      have h0 : (∫ s : ℝ, ((marg ρ s * logTrace lam ε (σ - s) : ℝ) : ℂ)) =
          ((∫ s : ℝ, marg ρ s * logTrace lam ε (σ - s) : ℝ) : ℂ) := integral_ofReal
      rw [hcmul, h0, hreal, Complex.ofReal_zero]
    filter_upwards [hLc] with v hv
    exact Complex.ofReal_eq_zero.mp hv
  exact ae_zero_on_Ioi_of_logTrace hε hlamm hLzero

end

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsSubDefs =====
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

set_option autoImplicit false






end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.Jker_integral_eq_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- **The change of variables `p ↦ ε⁻¹ • p` in `ℝ²`**, in the form used for `Jker`: the
Lebesgue integral of `p ↦ ρ (ε⁻¹ • p)` is `ε ^ 2` times the integral of `ρ` (`finrank ℝ (ℝ×ℝ) = 2`). -/
theorem integral_comp_inv_smul_two (ρ : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, ρ (ε⁻¹ • p) = ε ^ 2 * ∫ p : ℝ × ℝ, ρ p := by
  have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (μ := MeasureTheory.volume) (R := ε) (f := ρ) hε.le
  rw [show Module.finrank ℝ (ℝ × ℝ) = 2 from by simp [Module.finrank_prod], smul_eq_mul] at h
  exact h

/-- **The kernel `Jker ρ ε` has total mass one** for every admissible mollifier `ρ` and every
`ε > 0`. -/
theorem Jker_integral_eq_one (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := by
  have h1 : ∫ p : ℝ × ℝ, Jker ρ ε p = ε⁻¹ ^ 2 * ∫ p : ℝ × ℝ, ρ (ε⁻¹ • p) := by
    simp only [Jker]
    rw [MeasureTheory.integral_const_mul]
  rw [h1, integral_comp_inv_smul_two ρ hε, hρ.mass, mul_one, ← mul_pow,
    inv_mul_cancel₀ hε.ne', one_pow]

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.KernAux.contDiff_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.KernAux

/-- **The shifted profile is smooth.**  If `g` is `C^n` on the open quadrant `Quad` (for every
`n`, as a function of `(z, θ)`), then for fixed `(z, θ) ∈ Quad` the two-variable function

`p ↦ g (z e^{-p₁}) (arctan (tan θ · e^{-p₂}))`

is `C^n` on all of `ℝ²`.  The reason is that the shift map
`p ↦ (zShift z p₁, thShift θ p₂)` is smooth as a map `ℝ² → ℝ²` and takes *all* of `ℝ²` into the
open quadrant `Quad` (`zShift_pos`, `thShift_mem`), which is where the hypothesis on `g` lives. -/
theorem contDiff_shift (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad) :
    ∀ n : ℕ, ContDiff ℝ n
      (fun p : ℝ × ℝ => g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  intro n
  -- the shift map `p ↦ (zShift z p₁, thShift θ p₂)` is `C^n` on `ℝ²`:
  -- `p ↦ z e^{-p₁}` is a constant times `exp` of a linear function, and
  -- `p ↦ arctan (tan θ · e^{-p₂})` is `arctan` of a constant times `exp` of a linear function.
  have hφ : ContDiff ℝ n (fun p : ℝ × ℝ =>
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)) := by
    refine ContDiff.prodMk ?_ ?_
    · have hp1 : ContDiff ℝ n (fun p : ℝ × ℝ => -p.1) := contDiff_fst.neg
      exact contDiff_const.mul (Real.contDiff_exp.comp hp1)
    · have hp2 : ContDiff ℝ n (fun p : ℝ × ℝ => -p.2) := contDiff_snd.neg
      exact Real.contDiff_arctan.comp (contDiff_const.mul (Real.contDiff_exp.comp hp2))
  -- the shift map lands in the open quadrant, where `g` is `C^n`:
  have hmem : ∀ p : ℝ × ℝ,
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)
        ∈ Work.FTS.StrongEps.Quad :=
    fun p => ⟨Work.FTS.StrongEps.zShift_pos hz, Work.FTS.StrongEps.thShift_mem hθ⟩
  exact (hg n).comp_contDiff hφ hmem

end Work.FTS.StrongEps.KernAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.KernAux.deriv_shift_fst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The first partial derivative of the `(z,θ)`-shift

`Work.FTS.StrongEps.zShift z s = z * e^{-s}` is the `z`-component of the two-dimensional
translation `(s,ζ) ↦ (s - p₁, ζ - p₂)` of the log-coordinates of the mollifier `Jeps`.
Differentiating the shifted profile in the shift parameter `s` therefore differentiates it in
the *logarithmic* radial variable: since `d/ds (z e^{-s}) = -(z e^{-s})`,

  `∂_s [ g (z e^{-s}) θ' ] = -(z ∂_z g) (z e^{-s}, θ') = -D_z g (z e^{-s}, θ')`,

which is exactly the identity proved below.  It is the statement that the shift acts on the
profile by transport along `D_z` (up to sign), i.e. the first half of the commutation of `J_ε`
with `D_z` (see `Submission/Work/FTS/StrongEps/Commute.lean`) that the design of the
`StrongEps` area is built on.

Note on notation: this file was delivered with a bare `π`, which — `autoImplicit` being
`false` in this project — is not the notation for `Real.pi` unless the `Real` scope is open,
so the statement did not even elaborate.  Opening the scope is the (only) faithful reading of
the requested statement: the `π` of `Work.FTS.StrongEps.Quad`, `θ ∈ (0,π/2)`, is `Real.pi`.
-/

open scoped Real

namespace Work.FTS.StrongEps.KernAux

/-- **The `z`-shift differentiates the profile along `D_z`.**  For `g` of class `C¹` on the
open quadrant, `z > 0` and `θ ∈ (0,π/2)`, the derivative in the shift parameter `s` of
`s ↦ g (z e^{-s}) (thShift θ p₂)` at `s = p₁` is `-D_z g` evaluated at the shifted point. -/
theorem deriv_shift_fst (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.StrongEps.Quad) (p : ℝ × ℝ) :
    deriv (fun s : ℝ => g (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1
      = - Work.Spaces.Dz g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
  -- abbreviate the (constant) angular shift
  set c : ℝ := Work.FTS.StrongEps.thShift θ p.2 with hc
  -- the shifted angular variable stays in the open interval `(0,π/2)`
  have hcpos : 0 < c := by
    rw [hc, Work.FTS.StrongEps.thShift]
    exact (Real.arctan_pos).2
      (mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _))
  have hclt : c < π / 2 := by
    rw [hc, Work.FTS.StrongEps.thShift]; exact Real.arctan_lt_pi_div_two _
  -- the shifted radial variable stays positive
  have hapos : 0 < Work.FTS.StrongEps.zShift z p.1 := by
    rw [Work.FTS.StrongEps.zShift]; exact mul_pos hz (Real.exp_pos _)
  have hmem : (Work.FTS.StrongEps.zShift z p.1, c) ∈ Work.FTS.StrongEps.Quad :=
    ⟨hapos, hcpos, hclt⟩
  have hopen : IsOpen Work.FTS.StrongEps.Quad := isOpen_Ioi.prod isOpen_Ioo
  -- hence `g` is differentiable there, and so is its radial slice
  have hdiff : DifferentiableAt ℝ (Function.uncurry g) (Work.FTS.StrongEps.zShift z p.1, c) :=
    (hg.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hmem)
  have hslice : HasDerivAt (fun w : ℝ => g w c)
      (Work.Spaces.pz g (Work.FTS.StrongEps.zShift z p.1) c) (Work.FTS.StrongEps.zShift z p.1) := by
    have := (Work.Spaces.differentiableAt_curry_left hdiff).hasDerivAt
    simpa [Work.Spaces.pz] using this
  -- the shift itself: `d/ds (z e^{-s}) = -(z e^{-s})`
  have hzsh : HasDerivAt (fun s : ℝ => Work.FTS.StrongEps.zShift z s)
      (-(Work.FTS.StrongEps.zShift z p.1)) p.1 := by
    have h1 : HasDerivAt (fun s : ℝ => -s) (-1) p.1 := hasDerivAt_neg p.1
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-(Real.exp (-p.1))) p.1 :=
      h1.exp.congr_deriv (by ring)
    have h3 := h2.const_mul z
    simpa only [mul_neg, Work.FTS.StrongEps.zShift] using h3
  -- chain rule
  have hcomp := hslice.comp p.1 hzsh
  have hd : deriv (fun s : ℝ => g (Work.FTS.StrongEps.zShift z s) c) p.1
      = Work.Spaces.pz g (Work.FTS.StrongEps.zShift z p.1) c
        * (-(Work.FTS.StrongEps.zShift z p.1)) := hcomp.deriv
  rw [hd, Work.Spaces.Dz]
  ring

end Work.FTS.StrongEps.KernAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.KernAux.deriv_shift_snd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open Set

namespace Work.FTS.StrongEps.KernAux

set_option autoImplicit false

/-- `sin (2 · arctan x) = 2x / (1 + x²)`. -/
theorem sin_two_arctan (x : ℝ) : Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have hpos : 0 < √(1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-- **The derivative of the `θ`-shift in its parameter**: for the shift
`thShift θ t = arctan (tan θ · e^{-t})`, differentiating in `t` gives
`∂_t (thShift θ t) = -(1/2) sin (2 · thShift θ t)`. -/
theorem hasDerivAt_thShift_snd (θ t : ℝ) :
    HasDerivAt (fun s : ℝ => Work.FTS.StrongEps.thShift θ s)
      (-(1 / 2) * Real.sin (2 * Work.FTS.StrongEps.thShift θ t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have htan : HasDerivAt (fun s : ℝ => Real.tan θ * Real.exp (-s))
      (Real.tan θ * (Real.exp (-t) * (-1))) t := hexp.const_mul (Real.tan θ)
  have hval : -(1 / 2) * Real.sin (2 * Work.FTS.StrongEps.thShift θ t)
      = 1 / (1 + (Real.tan θ * Real.exp (-t)) ^ 2) *
        (Real.tan θ * (Real.exp (-t) * (-1))) := by
    have hsin : Real.sin (2 * Work.FTS.StrongEps.thShift θ t)
        = 2 * (Real.tan θ * Real.exp (-t)) / (1 + (Real.tan θ * Real.exp (-t)) ^ 2) := by
      rw [show Work.FTS.StrongEps.thShift θ t
          = Real.arctan (Real.tan θ * Real.exp (-t)) from rfl, sin_two_arctan]
    rw [hsin]
    simp only [div_eq_mul_inv, one_mul]
    ring
  have harc : HasDerivAt (fun s : ℝ => Real.arctan (Real.tan θ * Real.exp (-s)))
      (1 / (1 + (Real.tan θ * Real.exp (-t)) ^ 2) *
        (Real.tan θ * (Real.exp (-t) * (-1)))) t :=
    HasDerivAt.comp_of_eq t (Real.hasDerivAt_arctan (Real.tan θ * Real.exp (-t))) htan rfl
  have hfun : (fun s : ℝ => Work.FTS.StrongEps.thShift θ s)
      = fun s : ℝ => Real.arctan (Real.tan θ * Real.exp (-s)) := rfl
  rw [hfun, hval]
  exact harc

/-- **The `t`-derivative of the shifted profile**: because the `θ`-shift is the translation
`ζ ↦ ζ - t` in the log coordinate `ζ = log tan θ`, differentiating the shifted profile in the
shift parameter is differentiation along `D_θ = sin(2θ) ∂_θ`, up to the factor `-1/2`. -/
theorem deriv_shift_snd (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.StrongEps.Quad) (p : ℝ × ℝ) :
    deriv (fun t : ℝ => g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ t)) p.2
      = -(1 / 2) * Work.Spaces.Dth g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
  have hopen : IsOpen Work.FTS.StrongEps.Quad := isOpen_Ioi.prod isOpen_Ioo
  have hz₀ : 0 < Work.FTS.StrongEps.zShift z p.1 := Work.FTS.StrongEps.zShift_pos hz
  have hθ₀ : Work.FTS.StrongEps.thShift θ p.2 ∈ Set.Ioo 0 (π / 2) :=
    Work.FTS.StrongEps.thShift_mem hθ
  have hmem : (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)
      ∈ Work.FTS.StrongEps.Quad := ⟨hz₀, hθ₀⟩
  have hcont : ContDiffAt ℝ 1 (Function.uncurry g)
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2) :=
    hg.contDiffAt (hopen.mem_nhds hmem)
  have hpair : ContDiffAt ℝ 1 (fun y : ℝ => (Work.FTS.StrongEps.zShift z p.1, y))
      (Work.FTS.StrongEps.thShift θ p.2) := by fun_prop
  have hslice : DifferentiableAt ℝ (fun y : ℝ => g (Work.FTS.StrongEps.zShift z p.1) y)
      (Work.FTS.StrongEps.thShift θ p.2) :=
    (ContDiffAt.comp (Work.FTS.StrongEps.thShift θ p.2) hcont hpair).differentiableAt_one
  have hG : HasDerivAt (fun y : ℝ => g (Work.FTS.StrongEps.zShift z p.1) y)
      (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (Work.FTS.StrongEps.thShift θ p.2) := hslice.hasDerivAt
  have hmain : deriv (fun t : ℝ => g (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ t)) p.2
      = Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
        * (-(1 / 2) * Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) :=
    (HasDerivAt.comp_of_eq p.2 hG (hasDerivAt_thShift_snd θ p.2) rfl).deriv
  rw [hmain]
  unfold Work.Spaces.Dth
  ring

end Work.FTS.StrongEps.KernAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.OfRealTools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false

/-- **`ofReal` of a Bochner integral of a nonnegative function is bounded by the `lintegral`.**
No integrability hypothesis is needed: if `f` is not integrable then `∫ f = 0` by
`integral_undef` and the inequality is trivial. -/
theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hf)]
  · rw [MeasureTheory.integral_undef h]
    simp


/-- `ofReal` of a finite sum of nonnegative reals is the sum of the `ofReal`s. -/
theorem ofReal_sum_of_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) :=
  ENNReal.ofReal_sum_of_nonneg hf

/-- A finite sum of `ℝ≥0∞`-numbers each bounded by `C` is bounded by `card • C`. -/
theorem sum_le_card_nsmul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ i ∈ s, f i ≤ C) : ∑ i ∈ s, f i ≤ s.card • C :=
  Finset.sum_le_card_nsmul s f C h

/-- `n • C ≤ (n : ℝ≥0∞) * C`: the `nsmul` of `ℝ≥0∞` is multiplication by the natural number. -/
theorem nsmul_le_natCast_mul (n : ℕ) (C : ℝ≥0∞) : n • C ≤ (n : ℝ≥0∞) * C :=
  le_of_eq (nsmul_eq_mul n C)

/-- Numerical bookkeeping: `1 + n * x ≤ (n + 2) * x` for `1 ≤ x` and `0 ≤ x`. -/
theorem one_add_mul_le (n : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 + (n : ℝ) * x ≤ (n + 2) * x := by
  have h0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hm : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

end Work.FTS.StrongEps.StepFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.Traces.wtZ_shift_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.Traces

open scoped Real Topology

/-- The elementary inequality behind `wtZ_shift_mul_le`: for `|p| ≤ ε` and `z > 0`,
`1 + z ≤ e^{3(ε+p)/4}(1 + z e^{-p})`.

Writing `ε - b := 3(ε+p)/4` (so that `b = (3ε-p)/4 ∈ [0,ε]`, since `|p| ≤ ε`), the right hand
side is `e^{3(ε-b)} + z e^{b}` and both exponentials are `≥ 1`. -/
theorem one_add_le_exp_mul (z p ε : ℝ) (hz : 0 < z) (hε : 0 ≤ ε) (hp : |p| ≤ ε) :
    1 + z ≤ Real.exp (3 * (ε + p) / 4) * (1 + z * Real.exp (-p)) := by
  have hp1 : -ε ≤ p := (abs_le.mp hp).1
  have hp2 : p ≤ ε := (abs_le.mp hp).2
  have ht1 : (0 : ℝ) ≤ 3 * (ε + p) / 4 := by linarith
  have ht2 : (0 : ℝ) ≤ 3 * (ε + p) / 4 - p := by linarith
  have hA : 1 ≤ Real.exp (3 * (ε + p) / 4) := Real.one_le_exp ht1
  have hB : 1 ≤ Real.exp (3 * (ε + p) / 4 - p) := Real.one_le_exp ht2
  have hsplit : Real.exp (3 * (ε + p) / 4) * (1 + z * Real.exp (-p))
      = Real.exp (3 * (ε + p) / 4) + z * Real.exp (3 * (ε + p) / 4 - p) := by
    have h : Real.exp (3 * (ε + p) / 4) * Real.exp (-p) = Real.exp (3 * (ε + p) / 4 - p) := by
      rw [← Real.exp_add]
      congr 1
    calc Real.exp (3 * (ε + p) / 4) * (1 + z * Real.exp (-p))
        = Real.exp (3 * (ε + p) / 4) * 1
            + Real.exp (3 * (ε + p) / 4) * (z * Real.exp (-p)) := by rw [mul_add]
      _ = Real.exp (3 * (ε + p) / 4)
            + z * (Real.exp (3 * (ε + p) / 4) * Real.exp (-p)) := by ring
      _ = Real.exp (3 * (ε + p) / 4) + z * Real.exp (3 * (ε + p) / 4 - p) := by rw [h]
  rw [hsplit]
  refine add_le_add hA ?_
  have h := mul_le_mul_of_nonneg_left hB hz.le
  simpa using h

/-- The key inequality: for `|p| ≤ ε`, `z > 0`,
`(1 + z)^4 e^{-3p} ≤ e^{3ε} (1 + z e^{-p})^4`. -/
theorem pow_four_key (z p ε : ℝ) (hz : 0 < z) (hε : 0 ≤ ε) (hp : |p| ≤ ε) :
    (1 + z) ^ 4 * Real.exp (-p) ^ 3
      ≤ Real.exp (3 * ε) * (1 + z * Real.exp (-p)) ^ 4 := by
  have hheart := one_add_le_exp_mul z p ε hz hε hp
  have hexp_pow : (Real.exp (3 * (ε + p) / 4)) ^ 4 = Real.exp (3 * (ε + p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : (1 + z) ^ 4 ≤ Real.exp (3 * (ε + p)) * (1 + z * Real.exp (-p)) ^ 4 := by
    calc (1 + z) ^ 4
        ≤ (Real.exp (3 * (ε + p) / 4) * (1 + z * Real.exp (-p))) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hheart 4
      _ = (Real.exp (3 * (ε + p) / 4)) ^ 4 * (1 + z * Real.exp (-p)) ^ 4 := by rw [mul_pow]
      _ = Real.exp (3 * (ε + p)) * (1 + z * Real.exp (-p)) ^ 4 := by rw [hexp_pow]
  have hprod : Real.exp (3 * p) * Real.exp (-p) ^ 3 = 1 := by
    have h3 : Real.exp (-p) ^ 3 = Real.exp (-p + -p + -p) := by
      rw [show Real.exp (-p) ^ 3 = Real.exp (-p) * Real.exp (-p) * Real.exp (-p) by ring,
        ← Real.exp_add]
      rw [← Real.exp_add]
    rw [h3, ← Real.exp_add]
    rw [show 3 * p + (-p + -p + -p) = 0 by ring, Real.exp_zero]
  have h6 : Real.exp (3 * (ε + p)) * Real.exp (-p) ^ 3 = Real.exp (3 * ε) := by
    rw [show Real.exp (3 * (ε + p)) = Real.exp (3 * ε) * Real.exp (3 * p) by
          rw [← Real.exp_add]; congr 1; ring]
    rw [show Real.exp (3 * ε) * Real.exp (3 * p) * Real.exp (-p) ^ 3
          = Real.exp (3 * ε) * (Real.exp (3 * p) * Real.exp (-p) ^ 3) by ring, hprod, mul_one]
  have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ Real.exp (-p) ^ 3)
  calc (1 + z) ^ 4 * Real.exp (-p) ^ 3
      ≤ (Real.exp (3 * (ε + p)) * (1 + z * Real.exp (-p)) ^ 4) * Real.exp (-p) ^ 3 := h5
    _ = Real.exp (3 * ε) * (1 + z * Real.exp (-p)) ^ 4 := by
        rw [show (Real.exp (3 * (ε + p)) * (1 + z * Real.exp (-p)) ^ 4) * Real.exp (-p) ^ 3
              = (Real.exp (3 * (ε + p)) * Real.exp (-p) ^ 3)
                  * (1 + z * Real.exp (-p)) ^ 4 by ring, h6]

theorem wtZ_shift_mul_le (z p ε : ℝ) (hz : 0 < z) (hε : 0 ≤ ε) (hp : |p| ≤ ε) :
    z * Work.Spaces.w z ^ 2
      ≤ Real.exp (3 * ε) * (Work.FTS.StrongEps.zShift z p
          * Work.Spaces.w (Work.FTS.StrongEps.zShift z p) ^ 2) := by
  have hkey := pow_four_key z p ε hz hε hp
  have hL : z * Work.Spaces.w z ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
    change z * ((1 + z) ^ 2 / z ^ 2) ^ 2 = (1 + z) ^ 4 / z ^ 3
    field_simp
  have hR : Work.FTS.StrongEps.zShift z p * Work.Spaces.w (Work.FTS.StrongEps.zShift z p) ^ 2
      = (1 + z * Real.exp (-p)) ^ 4 / (z ^ 3 * Real.exp (-p) ^ 3) := by
    change z * Real.exp (-p) * ((1 + z * Real.exp (-p)) ^ 2 / (z * Real.exp (-p)) ^ 2) ^ 2
        = (1 + z * Real.exp (-p)) ^ 4 / (z ^ 3 * Real.exp (-p) ^ 3)
    field_simp
  rw [hL, hR, ← mul_div_assoc]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 3)
        (by positivity : (0 : ℝ) < z ^ 3 * Real.exp (-p) ^ 3)]
  have h7 := mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ z ^ 3)
  rw [show (1 + z) ^ 4 * (z ^ 3 * Real.exp (-p) ^ 3)
        = (1 + z) ^ 4 * Real.exp (-p) ^ 3 * z ^ 3 by ring]
  exact h7

end Work.FTS.StrongEps.Traces
end
-- ===== merged: Submission.Work.FTS.StrongEps.exists_shift_window_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps

theorem exists_shift_window_compact {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') := by
  -- the shift box `[-ε,ε]²` and the shift map
  let B : Set (ℝ × ℝ) := Set.Icc (-ε) ε ×ˢ Set.Icc (-ε) ε
  let Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ :=
    fun y => (zShift y.1.1 y.2.1, thShift y.1.2 y.2.2)
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  -- `Φ` is (jointly) continuous on `K × B`: the base angles of `K` lie in `(0,π/2)`
  have hΦc : ContinuousOn Φ (K ×ˢ B) := by
    refine ContinuousOn.prodMk ?_ ?_
    · simp only [zShift]
      exact (by fun_prop : Continuous fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
        y.1.1 * Real.exp (-y.2.1)).continuousOn
    · have htan : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) => Real.tan y.1.2) (K ×ˢ B) :=
        Real.continuousOn_tan.comp (continuous_fst.snd.continuousOn) (fun y hy => by
          have hyθ : y.1.2 ∈ Set.Ioo 0 (π / 2) := (Set.mem_prod.mp (hKQ hy.1)).2
          exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hyθ.1, Real.pi_pos], hyθ.2⟩).ne')
      have h1 : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
          Real.tan y.1.2 * Real.exp (-y.2.2)) (K ×ˢ B) :=
        htan.mul ((Real.continuous_exp.comp (continuous_neg.comp continuous_snd.snd)).continuousOn)
      have h2 := Real.continuous_arctan.comp_continuousOn h1
      simpa only [Φ, thShift, Function.comp_def] using h2
  refine ⟨Φ '' (K ×ˢ B), ?_, ?_, ?_, ?_⟩
  · -- compactness: the image of `K × B` under the continuous map `Φ`
    exact (hK.prod hBc).image_of_continuousOn hΦc
  · -- the window stays in the open quadrant
    rintro q ⟨y, hy, rfl⟩
    exact Set.mem_prod.mpr ⟨zShift_pos (Set.mem_prod.mp (hKQ hy.1)).1,
      thShift_mem (Set.mem_prod.mp (hKQ hy.1)).2⟩
  · -- `K` sits in the window: the zero shift is the identity
    intro p hp
    have hpQ := Set.mem_prod.mp (hKQ hp)
    refine ⟨(p, (0, 0)), ⟨hp, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩, ?_⟩
    have hz : zShift p.1 0 = p.1 := by simp [zShift]
    have hth : thShift p.2 0 = p.2 := by
      simp only [thShift, neg_zero, Real.exp_zero, mul_one]
      exact Real.arctan_tan (by linarith [hpQ.2.1, Real.pi_pos]) hpQ.2.2
    exact Prod.ext hz hth
  · -- the shift property, by definition of the window
    intro p hp q hq1 hq2
    obtain ⟨hq1', hq1''⟩ := abs_le.mp hq1
    obtain ⟨hq2', hq2''⟩ := abs_le.mp hq2
    exact ⟨(p, q), ⟨hp, ⟨⟨hq1', hq1''⟩, ⟨hq2', hq2''⟩⟩⟩, rfl⟩

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.AK6.Sharp6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.AK6

set_option autoImplicit false

/-! ## The angular jets of `Γ`, with the `α`-factor -/

/-- **`|D_θ^i Γ| ≤ α·10⁵·Γ` on `Iθ` for `1 ≤ i ≤ 6`.**  The `α`-factor is the point: it
comes from `Spaces.dthU_iter_Gam_abs_bound` (the `i`-th angular jet of `Γ` is
`α·Tfun_{i-1}·Γ`), and it is what makes the `γ`-weighted angular integral of the `ℋ⁶`-norm
uniformly bounded as `α → 0⁺`. -/
theorem dthU_Gam_abs_le_alpha (i : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ| ≤ α * 100000 * Work.Spaces.Gam α θ := by
  intro θ hθ
  exact Work.Spaces.dthU_iter_Gam_abs_bound i hi α hα 100000
    (fun θ' _ => Work.FTS.LocData6.Tfun_abs_le5 (i - 1) (by omega) α hα hα1 θ') θ hθ

/-- **`Γ² ≤ sin(2θ)^{2α/5}` on `Iθ`** (square of `Gam_le_sin_two_rpow`). -/
theorem Gam_sq_le_sin_two_rpow (α : ℝ) (hα : 0 < α) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
  have h := Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ
  have h2 := pow_le_pow_left₀ (Work.Spaces.Gam_bounds α θ hα hθ).1 h 2
  have heq : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
    congr 1
    ring
  rwa [heq] at h2

/-- **`Γ²·sin(2θ)^{-γ} ≤ sin(2θ)^{2α/5-γ}` on `Iθ`.**  This is the `rpow` bookkeeping that
converts the `γ`-weighted square of `Γ` into the uniformly integrable exponent
`2α/5 - γ = 3α/10 - 1` of `Work.Elliptic.WtoH_Angular`. -/
theorem Gam_sq_mul_rpow_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
  have hp : 2 * α / 5 + -(Work.Spaces.gam α) ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; nlinarith [hα, hα1]
  have hkey : (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    rw [← Real.rpow_add' (x := Real.sin (2 * θ)) hs0 hp,
      show 2 * α / 5 - Work.Spaces.gam α = 2 * α / 5 + -(Work.Spaces.gam α) by ring]
  calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right (Gam_sq_le_sin_two_rpow α hα θ hθ)
          (Real.rpow_nonneg hs0 _)
    _ = (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := hkey

/-! ## The sharp pointwise bound on the `ℋ⁶`-integrand of `AK α` -/

/-- **The pointwise `ℋ⁶`-bound for `AK α`.**  From the radial jet bound `hrad` (order `≤ 6`)
of `ρ = 2z²/(1+z)³` one gets, for every `0 < α ≤ 1` and every `(z,θ) ∈ Iz × Iθ`,

  `HkIntegrand α 6 (AK α) z θ ≤ (1+z)^{-2}·(700·R·sin(2θ)^{-η}
     + 49·10¹²·R·(α+sin 2θ)²·sin(2θ)^{2α/5-γ})`,

which is exactly the pointwise input of `WtoH_Angular`-type integration
(`AK6.hkSq_le_of_integrand_le6`). -/
theorem AK_integrand_le6 {R : ℝ} (hR : 0 ≤ R)
    (hrad : ∀ (j : ℕ), j ≤ 6 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ),
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ),
      θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 6 (Work.Construction.AK α) z θ
        ≤ (1 / (1 + z) ^ 2) *
          (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
  intro α hα hα1 z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
  obtain ⟨hc1, _hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  have hc10 : (1 / Work.Spaces.c α) ≤ 10 := by rw [div_le_iff₀ hc0]; linarith
  have hcsq : (1 / Work.Spaces.c α) ^ 2 ≤ 100 := by
    have h1 : (0 : ℝ) ≤ 1 / Work.Spaces.c α := by positivity
    nlinarith [hc10, h1]
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  -- `AK α` is the separable datum `Γ(θ)·(2z²/(1+z)³/c α)`
  have hAK : Work.Construction.AK α
      = fun z' θ' => Work.Spaces.Gam α θ' * (2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) := by
    funext z' θ'
    rw [Work.Construction.AK]
    ring
  rw [hAK]
  have hmain := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
    (C := fun θ' : ℝ => Work.Spaces.Gam α θ')
    (B := fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) (z := z) (θ := θ) hθ
  -- ### the radial block
  have hBfun : (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)
      = fun z' _ : ℝ => (1 / Work.Spaces.c α) * (2 * z' ^ 2 / (1 + z') ^ 3) := by
    funext z' θ'
    ring
  have hradq : ∀ q : ℕ, q ≤ 6 →
      (Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)
          z 0) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ 100 * R / (1 + z) ^ 2 := by
    intro q hq
    have hDzB : Work.Spaces.DzIter q
          (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) z 0
        = (1 / Work.Spaces.c α)
          * Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3) z 0 := by
      rw [hBfun, Work.FTS.LocDataExt.DzIter_const_mul]
    rw [hDzB]
    have h1 := hrad q hq z hz 0
    calc ((1 / Work.Spaces.c α)
            * Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2
        = (1 / Work.Spaces.c α) ^ 2
            * (Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3) z 0
              * Work.Spaces.w z) ^ 2 := by ring
      _ ≤ 100 * (R / (1 + z) ^ 2) := mul_le_mul hcsq h1 (sq_nonneg _) (by norm_num)
      _ = 100 * R / (1 + z) ^ 2 := by ring
  have hradsum : (∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)
            z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 700 * R / (1 + z) ^ 2 := by
    have h := Finset.sum_le_card_nsmul (Finset.range 7)
      (fun q => (Work.Spaces.DzIter q
          (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2) (100 * R / (1 + z) ^ 2)
      (fun q hq => hradq q (by have := Finset.mem_range.mp hq; omega))
    calc (∑ q ∈ Finset.range 7, (Work.Spaces.DzIter q
            (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        ≤ (Finset.range 7).card • (100 * R / (1 + z) ^ 2) := h
      _ = 700 * R / (1 + z) ^ 2 := by simp; ring
  have hradsum0 : 0 ≤ ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)
          z 0) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- ### the angular block
  have hang_term : ∀ i : ℕ, i ∈ Finset.range 7 →
      (if 1 ≤ i then (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
        ≤ 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    intro i hi
    by_cases h1i : 1 ≤ i
    · rw [if_pos h1i]
      have hb := dthU_Gam_abs_le_alpha i h1i
        (by have := Finset.mem_range.mp hi; omega) α hα hα1 θ hθ
      have hb2 : (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
          ≤ α ^ 2 * 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
        rw [sq_abs] at h
        calc (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
            ≤ (α * 100000 * Work.Spaces.Gam α θ) ^ 2 := h
          _ = α ^ 2 * 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by ring
      calc (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ (α ^ 2 * 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right hb2 (Real.rpow_nonneg hs0 _)
        _ = 10 ^ 10 * α ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ ≤ 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
            mul_le_mul_of_nonneg_left (Gam_sq_mul_rpow_le α hα hα1 θ hθ) (by positivity)
    · rw [if_neg h1i]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hs0 _)
  have hang : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 7 * 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    have h1 : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have h2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith [hG0, hG1]
      calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          ≤ 1 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hs0 _)
        _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
    have h2 : (∑ i ∈ Finset.range 7, (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        ≤ 7 * (10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
      have h := Finset.sum_le_card_nsmul (Finset.range 7)
        (fun i => (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        (10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) hang_term
      calc _ ≤ (Finset.range 7).card
            • (10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := h
        _ = _ := by simp
    calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 7 * (10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
          add_le_add h1 h2
      _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 7 * 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by ring
  have hang0 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := by
    refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases h : 1 ≤ i
    · rw [if_pos h]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    · rw [if_neg h]
  -- ### assemble
  have hangb0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 7 * 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    refine add_nonneg (Real.rpow_nonneg hs0 _) ?_
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hs0 _)
  calc Work.Spaces.HkIntegrand α 6
        (fun z' θ' => Work.Spaces.Gam α θ' * (2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α)) z θ
      ≤ ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t)) θ ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        * (∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q
              (fun z' _ : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / Work.Spaces.c α) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) := hmain
    _ ≤ ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 7 * 10 ^ 10 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
        * (700 * R / (1 + z) ^ 2) := mul_le_mul hang hradsum hradsum0 hangb0
    _ = (1 / (1 + z) ^ 2) * (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 700 * (7 * 10 ^ 10) * α ^ 2 * R
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by ring
    _ ≤ (1 / (1 + z) ^ 2) * (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hle : α ^ 2 ≤ (α + Real.sin (2 * θ)) ^ 2 := by nlinarith [hα, hs0]
        have h3 : (0 : ℝ) ≤ 700 * (7 * 10 ^ 10) * R := by positivity
        have h4 : α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
            ≤ (α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hs0 _)
        calc 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 700 * (7 * 10 ^ 10) * α ^ 2 * R
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
            = 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 700 * (7 * 10 ^ 10) * R * (α ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by ring
          _ ≤ 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 700 * (7 * 10 ^ 10) * R * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
              add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h4 h3)
          _ = 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by ring

end Work.FTS.StrongPersist.AK6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.gamQfun_angBlk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## The integrand, the majorant and the constants -/

/-- The angular integrand of the statement: the `η`-weighted square of `a·Γ·q` plus the
`γ`-weighted squares of its angular jets up to order six. -/
noncomputable def angBlk (α a : ℝ) : ℝ → ℝ := fun θ =>
  (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  + ∑ i ∈ Finset.range 7,
      (if 1 ≤ i then
        (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
       else 0)

/-- A uniform bound for the coefficient sequence `Tfun i α`, `i ≤ 6`, obtained from
`Work.Spaces.Tfun_iter_bounded`. -/
lemma Tfun_bound6 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 6 → ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → |Work.Spaces.Tfun i α θ| ≤ C := by
  choose M hM using fun i : ℕ => Work.Spaces.Tfun_iter_bounded i
  refine ⟨1 + ∑ i ∈ Finset.range 7, M i 0, ?_, ?_⟩
  · have h : 0 ≤ ∑ i ∈ Finset.range 7, M i 0 := Finset.sum_nonneg (fun i _ => (hM i).1 0)
    linarith
  · intro i _ α hαIoc θ hθ
    obtain ⟨hα, hα1⟩ := hαIoc
    have hMi : |Work.Spaces.Tfun i α θ| ≤ M i 0 := by
      have h := (hM i).2 α hα hα1 θ hθ 0
      simpa only [Function.iterate_zero_apply] using h
    have hsum : M i 0 ≤ ∑ l ∈ Finset.range 7, M l 0 :=
      Finset.single_le_sum (fun l _ => (hM l).1 0) (Finset.mem_range.mpr (by omega))
    linarith

/-- The numerical constant bounding all `Tfun i α` with `i ≤ 6`, `α ∈ (0,1]`, `θ ∈ Iθ`. -/
noncomputable def Ctf : ℝ := Classical.choose Tfun_bound6

lemma Ctf_pos : 0 < Ctf := (Classical.choose_spec Tfun_bound6).1

lemma Tfun_le_Ctf : ∀ i : ℕ, i ≤ 6 → ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → |Work.Spaces.Tfun i α θ| ≤ Ctf :=
  (Classical.choose_spec Tfun_bound6).2

/-- The constant of the jet bound: `|D_θ^i (a Γ q)| ≤ Kf·Γ` on `Iθ` for `|a| ≤ 20`, `i ≤ 6`. -/
noncomputable def Kf : ℝ := 20 * (Ctf + 1)

lemma Kf_pos : 0 < Kf := by
  have h := Ctf_pos
  rw [Kf]; nlinarith

/-- The angular majorant of `angBlk α a`: the two `Γ`-weighted weight blocks. -/
noncomputable def angMaj (α : ℝ) : ℝ → ℝ := fun θ =>
  Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    + (7 * Kf ^ 2) * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))

/-! ## The angular jets of `Γ·q` -/

/-- Continuity of `Γ(α,·)`, everywhere (so in particular on `Iθ` and on the open interval). -/
lemma gam_continuous (α : ℝ) (hα : 0 ≤ α) : Continuous (fun θ => Work.Spaces.Gam α θ) := by
  change Continuous (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
  have hbase : Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) := by fun_prop
  exact hbase.rpow_const (p := α / 3) (fun x => Or.inr (by linarith))

/-- **The angular jets of `Γ·q` on the open interval.**  `D_θ^i (Γ q) = Tfun i α · Γ` on
`(0,π/2)`: the product rule for `D_θ`, the identity `D_θ Γ = α q Γ` and the very definition
of the coefficient sequence `Tfun`. -/
lemma dthU_iter_GamQ {α : ℝ} (hα : 0 < α) (i : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t))
      (fun θ => Work.Spaces.Tfun i α θ * Work.Spaces.Gam α θ) (Set.Ioo 0 (Real.pi / 2)) := by
  induction i with
  | zero =>
      intro θ _
      simp only [Function.iterate_zero_apply, Work.Spaces.Tfun_zero]
      ring
  | succ i ih =>
      intro θ hθ
      have hev : (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t))
          =ᶠ[𝓝 θ] (fun t => Work.Spaces.Tfun i α t * Work.Spaces.Gam α t) :=
        ih.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hθ)
      have hder := hev.deriv_eq
      have hT : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.Tfun i α t) θ :=
        ((Work.Spaces.Tfun_smooth i α).differentiable (by simp)).differentiableAt
      have hG : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.Gam α t) θ :=
        Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
      calc Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ
          = Work.Spaces.dthU
              (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ := by
            rw [Function.iterate_succ_apply']
        _ = Work.Spaces.dthU (fun t => Work.Spaces.Tfun i α t * Work.Spaces.Gam α t) θ := by
            rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply, hder]
        _ = Work.Spaces.dthU (fun t : ℝ => Work.Spaces.Tfun i α t) θ * Work.Spaces.Gam α θ
              + Work.Spaces.Tfun i α θ * Work.Spaces.dthU (fun t : ℝ => Work.Spaces.Gam α t) θ :=
            Work.Spaces.dthU_mul_apply (fun t : ℝ => Work.Spaces.Tfun i α t)
              (fun t : ℝ => Work.Spaces.Gam α t) θ hT hG
        _ = Work.Spaces.Tfun (i + 1) α θ * Work.Spaces.Gam α θ := by
            rw [Work.Spaces.dthU_Gam α θ hα hθ, Work.Spaces.dthU_apply,
              Work.Spaces.Tfun_succ]
            ring

/-! ## Bounds and continuity of the angular jets -/

/-- **The jet bound.**  For `|a| ≤ 20` and `i ≤ 6` the `i`-th angular jet of `a·(Γ·q)` is
bounded by `Kf·Γ` on `Iθ`. -/
lemma GQjet_bound {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (ha : |a| ≤ 20)
    {i : ℕ} (hi : i ≤ 6) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ|
      ≤ Kf * Work.Spaces.Gam α θ := by
  have hG : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hT : |Work.Spaces.Tfun i α θ| ≤ Ctf := Tfun_le_Ctf i hi α ⟨hα, hα1⟩ θ hθ
  have hpi : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  have hinner : |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ|
      ≤ Ctf * Work.Spaces.Gam α θ := by
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · have hid := dthU_iter_GamQ hα i (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h0, h1⟩)
        rw [hid, abs_mul, abs_of_nonneg hG]
        exact mul_le_mul_of_nonneg_right hT hG
      · subst h1
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · subst hi0
          simp only [Function.iterate_zero_apply]
          rw [Work.Spaces.Gam_zero_right α (ne_of_gt hα)]
          simp
        · rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' _ hipos hpi,
            Work.Spaces.Gam_zero_right α (ne_of_gt hα)]
          simp
    · subst h0
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        simp only [Function.iterate_zero_apply]
        rw [Work.Spaces.Gam_zero_left α (ne_of_gt hα)]
        simp
      · rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' _ hipos (by simp),
          Work.Spaces.Gam_zero_left α (ne_of_gt hα)]
        simp
  rw [show Work.Spaces.dthU^[i] (fun t : ℝ => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t))
        = fun θ => a * Work.Spaces.dthU^[i]
            (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ from
      Work.Spaces.dthU_iter_const_mul i a
        (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t)]
  rw [abs_mul]
  calc |a| * |Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ|
      ≤ 20 * (Ctf * Work.Spaces.Gam α θ) :=
        mul_le_mul ha hinner (abs_nonneg _) (by norm_num)
    _ ≤ Kf * Work.Spaces.Gam α θ := by
        rw [Kf]
        nlinarith [hG, Ctf_pos.le]

/-- **Continuity of the angular jets on the open interval.**  On `(0,π/2)` the `i`-th jet of
`a·(Γ·q)` agrees with the continuous function `a·Tfun i α·Γ`. -/
lemma GQjet_continuousOn {α a : ℝ} (hα : 0 < α) (i : ℕ) :
    ContinuousOn (fun θ => Work.Spaces.dthU^[i]
        (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hcont_exp : Continuous
      (fun θ : ℝ => a * (Work.Spaces.Tfun i α θ * Work.Spaces.Gam α θ)) :=
    continuous_const.mul
      ((Work.Spaces.Tfun_smooth i α).continuous.mul (gam_continuous α (le_of_lt hα)))
  have heq : Set.EqOn
      (fun θ => Work.Spaces.dthU^[i]
        (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ)
      (fun θ => a * (Work.Spaces.Tfun i α θ * Work.Spaces.Gam α θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ hθ
    show Work.Spaces.dthU^[i]
        (fun t : ℝ => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ
      = a * (Work.Spaces.Tfun i α θ * Work.Spaces.Gam α θ)
    rw [show Work.Spaces.dthU^[i]
          (fun t : ℝ => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t))
        = fun θ => a * Work.Spaces.dthU^[i]
            (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ from
      Work.Spaces.dthU_iter_const_mul i a
        (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t)]
    simp only []
    rw [dthU_iter_GamQ hα i hθ]
  exact hcont_exp.continuousOn.congr heq

/-! ## The main theorem -/

theorem gamQfun_angBlk : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1, ∀ a : ℝ, |a| ≤ 20 →
    MeasureTheory.IntegrableOn (fun θ =>
        (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7,
            (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
             else 0)) Work.Spaces.Iθ := by
  refine ⟨1, one_pos, fun α hαIoc a ha => ?_⟩
  obtain ⟨hα, hα1⟩ := hαIoc
  change MeasureTheory.IntegrableOn (angBlk α a) Work.Spaces.Iθ
  have hs0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- the two weight blocks are integrable
  have hEtaInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
    simpa only [Work.Coercivity.CT.DthIterAng_zero] using
      Work.Coercivity.dthIterAng_sq_integrable_eta α hα hα1 0
  have hGamInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ := by
    simpa only [Work.Coercivity.CT.DthIterAng_zero] using
      Work.Coercivity.dthIterAng_sq_integrable_gam α hα hα1 0
  have hmaj : MeasureTheory.IntegrableOn (angMaj α) Work.Spaces.Iθ :=
    (hEtaInt.const_mul (Kf ^ 2)).add (hGamInt.const_mul (7 * Kf ^ 2))
  -- pointwise domination on `Iθ`
  have hdom : ∀ θ ∈ Work.Spaces.Iθ, angBlk α a θ ≤ angMaj α θ := by
    intro θ hθ
    have hsθ := hs0 θ hθ
    have hsE : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hsθ _
    have hsG : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsθ _
    have h0 : (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      have hb := GQjet_bound (i := 0) hα hα1 ha (Nat.zero_le 6) hθ
      have hb' : |a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)|
          ≤ Kf * Work.Spaces.Gam α θ := by
        simpa only [Function.iterate_zero_apply] using hb
      have hsq : (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
          ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := by
        calc (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
            = |a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)| ^ 2 := by rw [sq_abs]
          _ ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb' 2
      calc (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right hsq hsE
        _ = Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            ring
    have hsum : (∑ i ∈ Finset.range 7,
          (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
           else 0))
        ≤ ∑ _i ∈ Finset.range 7,
            Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1]
        have hi6 : i ≤ 6 := by have := Finset.mem_range.mp hi; omega
        have hb := GQjet_bound (i := i) hα hα1 ha hi6 hθ
        have hsq : (Work.Spaces.dthU^[i]
              (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
            ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := by
          calc (Work.Spaces.dthU^[i]
                (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
              = |Work.Spaces.dthU^[i]
                  (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ| ^ 2 := by
                rw [sq_abs]
            _ ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        calc (Work.Spaces.dthU^[i]
                (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            ≤ (Kf * Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
              mul_le_mul_of_nonneg_right hsq hsG
          _ = Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      · simpa only [if_neg h1] using
          mul_nonneg (sq_nonneg Kf) (mul_nonneg (sq_nonneg (Work.Spaces.Gam α θ)) hsG)
    have hsum2 : (∑ _i ∈ Finset.range 7,
          Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        = 7 * Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    simp only [angBlk, angMaj]
    linarith [h0, hsum, le_of_eq hsum2]
  -- measurability of the integrand
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hGamC : Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := gam_continuous α (le_of_lt hα)
  have hFmeas : AEStronglyMeasurable
      (fun θ : ℝ => a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ))
      (volume.restrict Work.Spaces.Iθ) :=
    (continuous_const.mul (hGamC.mul Work.Spaces.qfun_smooth.continuous)).aestronglyMeasurable
  have hEtaMeas : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) :=
    (Measurable.pow_const
        (Real.measurable_sin.comp (measurable_const.mul measurable_id)) (-(Work.Spaces.eta)))
      |>.aestronglyMeasurable
  have hmeasi : ∀ i : ℕ, i ≤ 6 → AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.dthU^[i]
          (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) := by
    intro i _
    have hcont_i := GQjet_continuousOn (α := α) (a := a) hα i
    have hcont_sin : ContinuousOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine ContinuousOn.rpow_const (by fun_prop) ?_
      intro θ hθ
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact ((hcont_i.pow 2).mul hcont_sin).aestronglyMeasurable measurableSet_Ioo
  have hsumMeas : AEStronglyMeasurable
      (∑ i ∈ Finset.range 7, fun θ : ℝ =>
        (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
         else 0)) (volume.restrict Work.Spaces.Iθ) := by
    refine Finset.aestronglyMeasurable_sum _ (fun i hi => ?_)
    by_cases h1 : 1 ≤ i
    · have hi6 : i ≤ 6 := by have := Finset.mem_range.mp hi; omega
      simpa only [if_pos h1] using hmeasi i hi6
    · simpa only [if_neg h1] using
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ))).aestronglyMeasurable
  have hstep : angBlk α a = (fun θ : ℝ => (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      + (∑ i ∈ Finset.range 7, fun θ : ℝ =>
        (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
         else 0)) := by
    funext θ
    simp only [angBlk, Pi.add_apply, Finset.sum_apply]
  have hmeas : AEStronglyMeasurable (angBlk α a) (volume.restrict Work.Spaces.Iθ) := by
    rw [hstep]
    exact (hFmeas.pow 2 |>.mul hEtaMeas).add hsumMeas
  -- conclude by domination
  refine hmaj.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hnn : 0 ≤ angBlk α a θ := by
    simp only [angBlk]
    refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hs0 θ hθ) _)) ?_
    refine Finset.sum_nonneg (fun i hi => ?_)
    by_cases h1 : 1 ≤ i
    · simpa only [if_pos h1] using
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hs0 θ hθ) _)
    · simpa only [if_neg h1] using le_refl (0 : ℝ)
  rw [Real.norm_of_nonneg hnn]
  exact hdom θ hθ

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6Gam.gamSliceSup11 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6Gam

set_option maxHeartbeats 4000000

/-- **The `θ`-slice of a mixed slot, uniformly in `z`, with the constant exposed.**  For a datum
`f` of the open class lying in `ℋ⁴`, and for `1 ≤ i`, `i + j ≤ 3`, the `γ`-weighted angular slice
of `D_z^j D_θ^i f` at any `z > 0` is at most `3 · |f|²_{ℋ⁴}`.  This is
`Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform` with the constant `C = 3` exposed. -/
theorem mixed_slice_z_le_three :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ 3 * Work.Spaces.HkSq α 4 f := by
  intro α f _hα _hα1 hF hmem j i hi hij z hz
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  -- almost every angle is interior
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo 0 (π / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π / 2)] with σ h
    exact fun hmem' => h.mpr hmem'
  -- the window bound, for every radius `R₀ ≥ z`
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π / 2) →
        IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ) Work.Spaces.Iz →
        (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 < Real.sin (2 * σ) := Work.FTS.TransportS.T2SupB2.sin_two_pos_of_mem_Ioo hσ
      have hlam : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_nonneg (le_of_lt hsinσ) _
      -- the hypotheses of the one-dimensional window inequality
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.mixed j i f x σ)
            (Work.Spaces.pz (Work.Spaces.mixed j i f) x σ) x :=
        fun x hx => (hF.mixed j i).hasDerivAt_slice hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.mixed j i f x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        ((hF.mixed j i).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn
          (fun x : ℝ => Work.Spaces.pz (Work.Spaces.mixed j i f) x σ)
          (Set.Icc z (2 * R₀)) :=
        (((hF.mixed j i).pz).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : IntegrableOn
          (fun x : ℝ => (Work.Spaces.mixed j i f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
        (hcont.pow 2).integrableOn_Icc
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.mixed j i f x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.mixed j i f) x σ)
        hz hR hderiv hcont hcont' hint
      -- continuity of the relevant slices
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x)
          (Set.Icc z (2 * R₀)) := by
        refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) ?_
        intro x hx
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
      have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.Icc z (2 * R₀)) := by
        have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
            Work.FTS.EllipticEst.Q0 :=
          fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
        have hc := (hF.continuousOn_HkIntegrand α 4).comp
          (continuousOn_id.prodMk continuousOn_const) hmap
        simpa only [Function.comp_def, id_eq] using hc
      -- interval integrability
      have hIntL1 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
            (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact ContinuousOn.mul continuousOn_const (hcontW.pow 2)
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact ContinuousOn.mul continuousOn_const (hcont.pow 2)
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      -- the pointwise domination of the two window integrands by the `ℋ⁴`-integrand
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
        have hcomm : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
            = Work.Spaces.mixed (j + 1) i f x σ := rfl
        rw [hcomm]
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed (j + 1) i f x σ * Work.Spaces.w x) ^ 2
            = (Work.Spaces.mixed (j + 1) i f x σ * Work.Spaces.w x) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by ring
        rw [h1]
        exact Work.FTS.TransportS.T2SupB2.mixed_succ_mul_w_sq_le_HkIntegrand hx0 hσ j i hi (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2
            = (Work.Spaces.mixed j i f x σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by ring
        rw [h1]
        exact Work.FTS.TransportS.T2SupB2.mixed_sq_le_HkIntegrand (lt_of_lt_of_le hRpos hx.1) hσ j i hi (by omega)
      -- the two window integrals are dominated by the full radial integral
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      -- the weight factors out of the interval integrals
      have hAeq : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                * Work.Spaces.w x) ^ 2)
          = ∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                * Work.Spaces.w x) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      have hBeq : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in R₀..(2 * R₀), (Work.Spaces.mixed j i f x σ) ^ 2)
          = ∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f x σ) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      calc (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f z σ) ^ 2 := by ring
        _ ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (2 * (∫ x in z..(2 * R₀),
                    (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                      * Work.Spaces.w x) ^ 2)
                + (2 / R₀) * ∫ x in R₀..(2 * R₀),
                    (Work.Spaces.mixed j i f x σ) ^ 2) :=
              mul_le_mul_of_nonneg_left hwin hlam
        _ = 2 * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                    * Work.Spaces.w x) ^ 2))
              + (2 / R₀) * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (∫ x in R₀..(2 * R₀), (Work.Spaces.mixed j i f x σ) ^ 2)) := by ring
        _ = 2 * (∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                    * Work.Spaces.w x) ^ 2)
              + (2 / R₀) * (∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed j i f x σ) ^ 2) := by
              rw [hAeq, hBeq]
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
              + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
              add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
                (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := by
              ring
    -- integrate the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.mixed j i f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hfae : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.mixed j i f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hσ.1],
            by linarith [hσ.2, Real.pi_pos]⟩) _)
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          integral_mono_of_nonneg hfae (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by rw [hswap]
  -- take `R₀ = max z 2`, so that the coefficient is at most `3`
  have hzmax : z ≤ max z 2 := le_max_left z 2
  have hbnd := hbound (max z 2) hzmax
  have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
  have h2max : 2 ≤ max z 2 := le_max_right z 2
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (2 + 2 / max z 2) * Work.Spaces.HkSq α 4 f := hbnd
    _ ≤ 3 * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

theorem gamSliceSup11 : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 1 1 f z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α 4 f := by
  intro α f hα hα1 hF hmem z hz
  have h := mixed_slice_z_le_three α f hα hα1 hF hmem 1 1 (by norm_num) (by norm_num) z hz
  have hcomm : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 1 1 f z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 1 1 f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  rw [hcomm]
  exact h

end Work.FTS.StrongPersist.H6Row6Gam
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDz =====
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

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth mixed DzIter DthIter HkIntegrand Wt w gam eta)
open Work.FTS.OpenPkg.WProdWin

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Vanishing of the `ℋᵏ`-integrand on the angular boundary

At `sin(2θ) = 0` both weights of `HkIntegrand` vanish (the `1/sin(2θ)^{η/2}` of the radial
block through Lean's division by zero, and `Wt = w·sin(2θ)^{-γ/2}` through `0^{negative}`), so
the integrand vanishes for *every* datum. -/
theorem HkIntegrand_eq_zero_of_sin_two {α : ℝ} (hα : 0 < α) (k : ℕ) (F : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) : HkIntegrand α k F z θ = 0 := by
  rw [HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [eta])]
  have hgam : 0 < gam α := by rw [gam]; linarith
  have hWt : Wt α z θ = 0 := by
    rw [Wt, Work.Spaces.wTheta, hs,
      Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (div_pos hgam (by norm_num)))), mul_zero]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (DzIter i F z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (mixed j i F z θ * Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [hWt, mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-! ## The two slot predicates -/

/-- The radial slots of the product `h·D_z f`, with an explicit constant. -/
def SlotZ (C : ℝ) : Prop :=
  ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ i : ℕ, i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    (DzIter i (fun z θ => h z θ * Dz f z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * HkIntegrand α 4 f z θ

/-- The mixed slots of the product `h·D_z f`, with an explicit constant. -/
def SlotM (C : ℝ) : Prop :=
  ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ I J : ℕ, 1 ≤ I → I + J ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    (mixed J I (fun z θ => h z θ * Dz f z θ) z θ * Wt α z θ) ^ 2
      ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ

/-! ## Summing the slots -/

/-- **The pointwise majorant of `HkIntegrand α 3 (h·D_z f)`.**  Each of the four radial slots
costs `C_z |h|²_{𝒲^{4,∞}} HkIntegrand α 4 f` and each of the sixteen (mostly vanishing) mixed
slots costs at most `C_m |h|²_{𝒲^{4,∞}} GmajW α f`; on the angular boundary and at `z = 0` the
integrand vanishes, so the inequality holds on all of `Iz × Iθ`. -/
theorem majorant_dz {Cz Cm : ℝ} (hCz : 0 < Cz) (hCm : 0 < Cm)
    (hzslot : SlotZ Cz) (hmslot : SlotM Cm)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {h f : ℝ → ℝ → ℝ}
    (hsmh : Work.FTS.EllipticEst.SmoothOpen h) (hWm : Work.Spaces.WlInfMem α 4 h)
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      HkIntegrand α 3 (fun z θ => h z θ * Dz f z θ) z θ
        ≤ (4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ := by
  set W : ℝ := Work.Spaces.WlInf α 4 h with hWdef
  set X : ℝ → ℝ → ℝ := fun z θ => h z θ * Dz f z θ with hXdef
  intro z hz θ hθ
  have hW : 0 ≤ W := Work.Spaces.WlInf_nonneg α 4 h hWm
  have hC0 : (0 : ℝ) < 4 * Cz + 16 * Cm := by linarith
  have hG : 0 ≤ GmajW α f z θ := GmajW_nonneg hα f hθ
  have hbase : ∀ z' : ℝ, 0 ≤ (4 * Cz + 16 * Cm) * W ^ 2 * GmajW α f z' θ :=
    fun z' => mul_nonneg (mul_nonneg hC0.le (sq_nonneg W))
      (GmajW_nonneg hα f hθ)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [show z = 0 from hz0.symm, Work.Spaces.HkIntegrand_zero_z]
    exact hbase 0
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : HkIntegrand α 4 f z θ ≤ GmajW α f z θ :=
        Work.FTS.OpenPkg.WProdWin.HkIntegrand_le_GmajW hα f hθ
      have hsum1 : (∑ i ∈ Finset.range (3 + 1),
            (DzIter i X z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          ≤ 4 * (Cz * W ^ 2 * HkIntegrand α 4 f z θ) := by
        calc (∑ i ∈ Finset.range (3 + 1),
              (DzIter i X z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (3 + 1),
                (Cz * W ^ 2 * HkIntegrand α 4 f z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi3 : i ≤ 3 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              exact hzslot α h f hα hα1 hsmh hWm hsmf hfm i hi3 z θ hzpos hθi.1 hθi.2
          _ = 4 * (Cz * W ^ 2 * HkIntegrand α 4 f z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
      have hsum2 : (∑ i ∈ Finset.range (3 + 1), ∑ j ∈ Finset.range (3 + 1),
            (if 1 ≤ i ∧ i + j ≤ 3 then (mixed j i X z θ * Wt α z θ) ^ 2 else 0))
          ≤ 16 * (Cm * W ^ 2 * GmajW α f z θ) := by
        calc (∑ i ∈ Finset.range (3 + 1), ∑ j ∈ Finset.range (3 + 1),
              (if 1 ≤ i ∧ i + j ≤ 3 then (mixed j i X z θ * Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (3 + 1), ∑ _j ∈ Finset.range (3 + 1),
                (Cm * W ^ 2 * GmajW α f z θ) := by
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 3
              · rw [if_pos hc]
                exact hmslot α h f hα hα1 hsmh hWm hsmf hfm i j hc.1 hc.2 z θ
                  hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm) (sq_nonneg W)) hG
          _ = 16 * (Cm * W ^ 2 * GmajW α f z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      rw [HkIntegrand]
      refine le_trans (add_le_add hsum1 hsum2) ?_
      have h1 : 4 * (Cz * W ^ 2 * HkIntegrand α 4 f z θ)
          ≤ 4 * (Cz * W ^ 2 * GmajW α f z θ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz) (sq_nonneg W)))
          (by norm_num)
      calc 4 * (Cz * W ^ 2 * HkIntegrand α 4 f z θ) + 16 * (Cm * W ^ 2 * GmajW α f z θ)
          ≤ 4 * (Cz * W ^ 2 * GmajW α f z θ) + 16 * (Cm * W ^ 2 * GmajW α f z θ) :=
            add_le_add h1 le_rfl
        _ = (4 * Cz + 16 * Cm) * W ^ 2 * GmajW α f z θ := by ring
    · have hsin : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [HkIntegrand_eq_zero_of_sin_two hα 3 X hsin]
      exact hbase z

/-! ## The estimate -/

/-- **`L3MulDz` from the two slot estimates.**  The pointwise majorant is integrated: the
`z`-integral of `GmajW α f` is `≤ (1 + 700(1 + 4(γ-1)^{-1}))|f|²_{ℋ⁴}`, and
`(γ-1)^{-1} = 10/α ≥ 1`, which produces the stated constant `C/(γ-1)`. -/
theorem L3MulDz_of_slots (Cz Cm : ℝ) (hCz : 0 < Cz) (hCm : 0 < Cm)
    (hzslot : SlotZ Cz) (hmslot : SlotM Cm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (h f : Fn), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
        Work.Spaces.HkMem α 3 (fun z θ => h z θ * Dz f z θ) ∧
        HkSq α 3 (fun z θ => h z θ * Dz f z θ)
          ≤ C / (gam α - 1) * (Work.Spaces.WlInf α 4 h) ^ 2 * HkSq α 4 f := by
  refine ⟨(4 * Cz + 16 * Cm) * 3501, by positivity, ?_⟩
  intro α h f hα hα1 hsmh hWm hsmf hfm
  set W : ℝ := Work.Spaces.WlInf α 4 h with hWdef
  set X : ℝ → ℝ → ℝ := fun z θ => h z θ * Dz f z θ with hXdef
  set K : ℝ := 4 * Cz + 16 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 4 * (gam α - 1)⁻¹) with hKgdef
  have hW : 0 ≤ W := Work.Spaces.WlInf_nonneg α 4 h hWm
  have hK : 0 < K := by rw [hKdef]; linarith
  have hγpos : 0 < gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγpos.le
  have hmaj := majorant_dz hCz hCm hzslot hmslot hα hα1 hsmh hWm hsmf hfm
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    smoothOpen_mul hsmh (Work.FTS.EllipticEst.SmoothOpen.Dz hsmf)
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => HkIntegrand α 3 X z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · have hzero : (fun θ => HkIntegrand α 3 X 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α 3 X θ
      rw [show z = 0 from hz0.symm, hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((GmajW_integrableOn_theta hα hα1 hfm hz).const_mul (K * W ^ 2)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (hXsm.continuousOn_HkIntegrand α 3) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 3 X z θ)]
        exact hmaj z hz θ hθ
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ) ≤ K * W ^ 2 * (Kg * HgInt α f z) := by
    intro z hz
    have hint : MeasureTheory.IntegrableOn (fun θ => (K * W ^ 2) * GmajW α f z θ)
        Work.Spaces.Iθ := (GmajW_integrableOn_theta hα hα1 hfm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K * W ^ 2) * GmajW α f z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 3 X z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmaj z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, GmajW α f z θ) ≤ Kg * HgInt α f z := by
      simpa only [hKgdef] using GmajW_theta_integral_le hα hα1 hfm hz
    calc (∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ)
        ≤ (K * W ^ 2) * (∫ θ in Work.Spaces.Iθ, GmajW α f z θ) := h1
      _ ≤ (K * W ^ 2) * (Kg * HgInt α f z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK.le (sq_nonneg W))
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ) ≤ (K * W ^ 2 * Kg) * HgInt α f z := by
    intro z hz
    refine le_trans (hinner z hz) (le_of_eq ?_)
    ring
  have hdom : MeasureTheory.IntegrableOn (fun z => (K * W ^ 2 * Kg) * HgInt α f z)
      Work.Spaces.Iz := hfm.2.const_mul _
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => HkIntegrand α 3 X p.1 p.2)
      (hXsm.continuousOn_HkIntegrand α 3)).integral_prod_right'
    have hfun : (fun z => ∫ θ, HkIntegrand α 3 X z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ) Work.Spaces.Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg
      (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 3 X z θ)]
    exact hbdd z hz
  refine ⟨⟨hslice, hzg⟩, ?_⟩
  have hHknn : 0 ≤ HkSq α 4 f :=
    integral_nonneg fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hSq : HkSq α 3 X ≤ (K * W ^ 2 * Kg) * HkSq α 4 f := by
    have h1 : HkSq α 3 X ≤ ∫ z in Work.Spaces.Iz, (K * W ^ 2 * Kg) * HgInt α f z := by
      rw [HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 3 X z θ)
        (fun z hz => hbdd z hz) hdom
    rw [MeasureTheory.integral_const_mul, Work.FTS.OpenPkg.WProdWin.HgInt_z_integral] at h1
    exact h1
  have hγ1 : (1 : ℝ) ≤ (gam α - 1)⁻¹ := by
    rw [Work.Spaces.gam_sub_one, one_le_inv₀ (by linarith : (0 : ℝ) < α / 10)]
    linarith
  have hKg_le : Kg ≤ 3501 * (gam α - 1)⁻¹ := by
    rw [hKgdef]
    nlinarith [hγ1]
  have hstep : K * W ^ 2 * Kg ≤ K * W ^ 2 * (3501 * (gam α - 1)⁻¹) :=
    mul_le_mul_of_nonneg_left hKg_le (mul_nonneg hK.le (sq_nonneg W))
  calc HkSq α 3 X ≤ (K * W ^ 2 * Kg) * HkSq α 4 f := hSq
    _ ≤ (K * W ^ 2 * (3501 * (gam α - 1)⁻¹)) * HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hstep hHknn
    _ = ((4 * Cz + 16 * Cm) * 3501) / (gam α - 1) * W ^ 2 * HkSq α 4 f := by
        rw [hKdef]; ring

theorem L3MulDz : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 3 (fun z θ => h z θ * Work.Spaces.Dz f z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => h z θ * Work.Spaces.Dz f z θ)
        ≤ C / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkSq α 4 f := by
  obtain ⟨Cz, hCz, hzslot⟩ := L3MulDzBackup.zslot_dz_le_b
  obtain ⟨Cm, hCm, hmslot⟩ := L3MulDzBackupM.mslot_dz_le_b
  exact L3MulDz_of_slots Cz Cm hCz hCm hzslot hmslot

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.Majorant6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

theorem prod_majorant6 : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → HkMem α 6 g →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K / (gam α - 1)
            * (HkSq α 6 f * HkIntegrand α 6 g z θ
              + HkSq α 6 g * HkIntegrand α 6 f z θ)
          + K * ((DzIter 5 f z θ * Dth g z θ) ^ 2
              + (Dth f z θ * DzIter 5 g z θ) ^ 2)
            * (Wt α z θ) ^ 2 := by
  obtain ⟨CZ, hCZpos, hZ⟩ := z_sum_bound6
  obtain ⟨CM, hCMpos, hM⟩ := m_sum_bound6
  refine ⟨7 * CZ + 49 * CM + 1, by positivity, ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG z θ hz hθ0 hθ1
  have hRnn : 0 ≤ Maj6 α f g z θ := Maj6_nonneg hα f g z θ
  have hZsum : ∑ i ∈ Finset.range 7, (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 ≤ 7 * (CZ * Maj6 α f g z θ) := by
    calc ∑ i ∈ Finset.range 7, (DzIter i (fun z θ => f z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ ∑ i ∈ Finset.range 7, (CZ * Maj6 α f g z θ) :=
          Finset.sum_le_sum (fun i hi => hZ α f g hα hα1 hF hmemF hG hmemG i
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z θ hz hθ0 hθ1)
      _ = 7 * (CZ * Maj6 α f g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hMsum : ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ 49 * (CM * Maj6 α f g z θ) := by
    have hper : ∀ i ∈ Finset.range 7, ∀ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ CM * Maj6 α f g z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 6
      · rw [if_pos hc]
        exact hM α f g hα hα1 hF hmemF hG hmemG i j hc.1 hc.2 z θ hz hθ0 hθ1
      · rw [if_neg hc]
        exact mul_nonneg hCMpos.le hRnn
    calc ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7, (CM * Maj6 α f g z θ) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hper i hi j hj))
      _ = 49 * (CM * Maj6 α f g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hcomb : 7 * (CZ * Maj6 α f g z θ) + 49 * (CM * Maj6 α f g z θ)
      ≤ (7 * CZ + 49 * CM + 1) * Maj6 α f g z θ := by nlinarith [hRnn]
  rw [HkIntegrand]
  refine le_trans (add_le_add hZsum hMsum) (le_trans hcomb (le_of_eq ?_))
  rw [Maj6, SInv6, Texc6, div_eq_mul_inv]
  ring

end Work.FTS.StrongPersist.N6
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2SliceAux.t2Mine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SliceAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The mixed slot with the `sin(2θ)^{-γ}` weight -/



/-! ## The `g`-side slice bound -/


/-! ## The slots of `HkIntegrand` on a slice -/



/-! ## The pointwise AM–GM bound for `Heasy` -/

/-- `2|a·b| ≤ a² + b²`. -/
theorem two_mul_abs_mul_le (a b : ℝ) : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]




theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) :=
  ContDiffOn.mul hf hg

/-- `D_z^n (D_z g) = D_z^{n+1} g`. -/
theorem DzIter_Dz (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (Work.Spaces.Dz g) = Work.Spaces.DzIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show Work.Spaces.Dz (Work.Spaces.DzIter k (Work.Spaces.Dz g))
        = Work.Spaces.Dz (Work.Spaces.DzIter (k + 1) g)
      rw [ih]







end Work.FTS.TransportS.T2SliceAux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The statement of the area (a verbatim copy of the lead's `EllLimOK`) -/

/-- **`E` passes to limits of `ℋ⁶`-bounded class-`C` sequences** (ruling v2 + the ruling of
2026-10-10): *verbatim copy* of `Work.FTS.StrongEps.EllLimOK`, with the `C⁴`-on-`Qd` hypothesis on
the limit.  The two definitions have the same body, hence are definitionally equal. -/
def EllLimOK (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

/-! ## Convergence of `C²`-jets on the quadrant -/


/-- The hypotheses of `EllLimOK` as a structure (the ruling's `LimSeq4`). -/
structure LimSeq4 (α : ℝ) (fn : ℕ → Fn) (f : Fn) : Prop where
  /-- every member of the sequence lies in the class `C` -/
  classC : ∀ n, Work.FTS.ClassC.ClassC α (fn n)
  /-- uniform `ℋ⁶`-bound -/
  bound : ∃ B : ℝ, ∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B
  /-- the limit is `C⁴` on the open quadrant -/
  c4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd
  /-- convergence of all `C⁴`-slots on the open quadrant -/
  conv : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i f z θ))



/-! ## The closure obligation -/


/-- **The two elliptic packages on the class `C`, at one operator** (`EllPkgGo` at level `4` and
`EllPkgK` at level `6`): the shape in which every statement of the area carries its hypothesis. -/
def HasPkg (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g →
    Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)



/-! ## Flat ("invisible") directions -/

/-- **`γ` is invisible to the limit process**: it vanishes identically on some *open*
neighbourhood of the open quadrant.  These are exactly the directions in which `EllLimOK` cannot
distinguish two candidate limits: replacing a limit `f` by `f + γ` changes nothing in the
hypotheses of `EllLimOK` (all mixed derivatives of the two agree on `Qd` by *locality*), while
`E (f + γ)` may differ from `E f`. -/
def QdZero (γ : Fn) : Prop :=
  ∃ V : Set (ℝ × ℝ), IsOpen V ∧ Work.Construction.Qd ⊆ V ∧ ∀ z θ, (z, θ) ∈ V → γ z θ = 0




/-- The open quadrant is open. -/
theorem isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## The limit points -/



/-! ## Two test objects for the obstruction -/


/-- The evaluation functional `f ↦ f z₀ θ₀` (linear). -/
def evalAt (z₀ θ₀ : ℝ) : Fn →ₗ[ℝ] ℝ where
  toFun f := f z₀ θ₀
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] theorem evalAt_apply (z₀ θ₀ : ℝ) (f : Fn) : evalAt z₀ θ₀ f = f z₀ θ₀ := rfl



end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.ThetaBoundBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Small monotonicity tools for the `ℋ^k`-integrand and the `ℋ^k`-norm

The target `Work.FTS_EllLimOK.PkgJets.thetaBound` needs the level-`0` and level-`4` memberships
`HkMem α 0 g`, `HkMem α 4 g` out of the class field `HkMem α 7 g`, together with the comparison
`HkSq α 0 g ≤ HkSq α 6 g` (so that the `ℋ⁶`-norm `Xn6` of the class can pay for everything).

All three are instances of the *pointwise* monotonicity of the `ℋ^k`-integrand in the order `k`
(every summand is a square and the index sets grow), which is
`Work.FTS.LocDataExt.HkIntegrand_mono`.  `HkMem_mono_le` re-exports the `HkMem`-monotonicity for
the open-quadrant class (`SmoothOpen`, not the analytic `SmoothQuad`), and `HkSq_mono_le` the
corresponding monotonicity of the integral.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false

/-- The `ℋ`-integrand is monotone in the order `k` (pointwise, no regularity needed). -/
theorem HkIntegrand_le {α : ℝ} {m k : ℕ} (hmk : m ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m f z θ ≤ Work.Spaces.HkIntegrand α k f z θ :=
  Work.FTS.LocDataExt.HkIntegrand_mono hmk f z θ

/-- `HkMem` is monotone in the order, for `SmoothOpen` data (open-quadrant version of
`Work.FTS.LocDataExt.HkMem_mono`, which asks for the analytic `SmoothQuad`). -/
theorem HkMem_mono_le {α : ℝ} {m k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmk : m ≤ k) (h : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α m f :=
  Work.FTS.LocData.HkMem_of_majorant α m (hf.continuousOn_HkIntegrand α m) h.1 h.2
    (fun z _ θ _ => HkIntegrand_le hmk f z θ)

/-- `HkSq` is monotone in the order: the level-`k` integrand dominates the level-`m` one, and it
is the integrable one. -/
theorem HkSq_mono_le {α : ℝ} {m k : ℕ} {f : ℝ → ℝ → ℝ} (hmk : m ≤ k)
    (h : Work.Spaces.HkMem α k f) : Work.Spaces.HkSq α m f ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ h.2 ?_
  · exact Filter.Eventually.of_forall
      (fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α m f z θ)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m f z θ)
      (h.1 z hz)
      (Filter.Eventually.of_forall fun θ => HkIntegrand_le hmk f z θ)

end Work.FTS_EllLimOK.PkgJets
end
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.kernel_exists_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves

open MeasureTheory Set Filter

noncomputable section

/-- The smooth bump, centred at the origin of `ℝ²`, with inner radius `1/4` and outer radius
`1/2`.  The outer radius is chosen so that its support — the max-norm ball of radius `1/2` — lies
inside the closed *Euclidean* unit ball. -/
def kerBump : ContDiffBump (0 : ℝ × ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The support condition of `IsMollKernel`, for the normalised bump: where the normalised bump
does not vanish, the Euclidean norm of the point is at most `1`. -/
theorem kerBump_support_pointwise (p : ℝ × ℝ)
    (hp : kerBump.normed volume p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
  have hp' : p ∈ Function.support (kerBump.normed volume) := hp
  rw [kerBump.support_normed_eq (μ := volume), Metric.mem_ball, dist_eq_norm, sub_zero,
    Prod.norm_def] at hp'
  obtain ⟨h1, h2⟩ := max_lt_iff.mp hp'
  have hR : kerBump.rOut = 1 / 2 := rfl
  rw [hR] at h1 h2
  have h1' : |p.1| < 1 / 2 := by simpa only [Real.norm_eq_abs] using h1
  have h2' : |p.2| < 1 / 2 := by simpa only [Real.norm_eq_abs] using h2
  have e1 : p.1 ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]; exact h1'
  have e2 : p.2 ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]; exact h2'
  nlinarith


end

end Work.FTS_FinalLeaves
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.DthIter_Gam_abs_le8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_LocDatum3a

open Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Derivative recursions for the coefficient polynomials `Qp` -/

/-- The third derivative recursion for the coefficient polynomials, obtained by
differentiating `(Qp (j+1) α)' = 4v·(Qp j)' - 2(1-v²)·(Qp j)'' + α·Qp j + α(v-1/3)·(Qp j)'
twice (equivalently: the general `k`-th derivative recursion at `k = 3`). -/
theorem Qp_deriv3_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2) * (Qp j α).derivative.derivative.derivative.derivative.eval v
        + 12 * v * (Qp j α).derivative.derivative.derivative.eval v
        + 12 * (Qp j α).derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp j α).derivative.derivative.derivative.eval v
        + 3 * α * (Qp j α).derivative.derivative.eval v := by
  simp [Qp]; ring

/-- The fourth derivative recursion (the general recursion at `k = 4`). -/
theorem Qp_deriv4_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).derivative.derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2)
          * (Qp j α).derivative.derivative.derivative.derivative.derivative.eval v
        + 16 * v * (Qp j α).derivative.derivative.derivative.derivative.eval v
        + 24 * (Qp j α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp j α).derivative.derivative.derivative.derivative.eval v
        + 4 * α * (Qp j α).derivative.derivative.derivative.eval v := by
  simp [Qp]; ring

/-- `Qp 2 α` has degree `3`, so its fourth derivative vanishes. -/
theorem Qp2_deriv4_eval (α v : ℝ) :
    (Qp 2 α).derivative.derivative.derivative.derivative.eval v = 0 := by
  simp [Qp]

/-- `Qp 2 α` has degree `3`, so its fifth derivative vanishes. -/
theorem Qp2_deriv5_eval (α v : ℝ) :
    (Qp 2 α).derivative.derivative.derivative.derivative.derivative.eval v = 0 := by
  simp [Qp]

/-! ## The concrete recursions used below -/

/-- The recursion for `(Qp 3 α)'''`. -/
theorem Qp3_d3_eval (α v : ℝ) :
    (Qp 3 α).derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        + 12 * v * (Qp 2 α).derivative.derivative.derivative.eval v
        + 12 * (Qp 2 α).derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.derivative.eval v
        + 3 * α * (Qp 2 α).derivative.derivative.eval v :=
  Qp_deriv3_succ_eval 2 α v

/-- The recursion for `(Qp 3 α)''''`. -/
theorem Qp3_d4_eval (α v : ℝ) :
    (Qp 3 α).derivative.derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2)
          * (Qp 2 α).derivative.derivative.derivative.derivative.derivative.eval v
        + 16 * v * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        + 24 * (Qp 2 α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        + 4 * α * (Qp 2 α).derivative.derivative.derivative.eval v :=
  Qp_deriv4_succ_eval 2 α v

/-- The recursion for `(Qp 4 α)''`. -/
theorem Qp4_d2_eval (α v : ℝ) :
    (Qp 4 α).derivative.derivative.eval v
      = (4 + 2 * α) * (Qp 3 α).derivative.eval v
        + 8 * v * (Qp 3 α).derivative.derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.eval v :=
  Work.FTS.LocData6.Qp_deriv_deriv_succ_eval 3 α v

/-- The recursion for `(Qp 4 α)'''`. -/
theorem Qp4_d3_eval (α v : ℝ) :
    (Qp 4 α).derivative.derivative.derivative.eval v
      = -2 * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.derivative.derivative.eval v
        + 12 * v * (Qp 3 α).derivative.derivative.derivative.eval v
        + 12 * (Qp 3 α).derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.derivative.eval v
        + 3 * α * (Qp 3 α).derivative.derivative.eval v :=
  Qp_deriv3_succ_eval 3 α v

/-- The recursion for `(Qp 5 α)'`. -/
theorem Qp5_d1_eval (α v : ℝ) :
    (Qp 5 α).derivative.eval v
      = 4 * v * (Qp 4 α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.eval v
        + α * (Qp 4 α).eval v
        + α * (v - 1 / 3) * (Qp 4 α).derivative.eval v :=
  Work.FTS.LocDataExt.Qp_deriv_succ_eval 4 α v

/-- The recursion for `(Qp 5 α)''`. -/
theorem Qp5_d2_eval (α v : ℝ) :
    (Qp 5 α).derivative.derivative.eval v
      = (4 + 2 * α) * (Qp 4 α).derivative.eval v
        + 8 * v * (Qp 4 α).derivative.derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 4 α).derivative.derivative.eval v :=
  Work.FTS.LocData6.Qp_deriv_deriv_succ_eval 4 α v

/-- The recursion for `Qp 6 α`. -/
theorem Qp6_eval (α v : ℝ) :
    (Qp 6 α).eval v
      = -2 * (1 - v ^ 2) * (Qp 5 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 5 α).eval v :=
  Qp_succ_eval 5 α v

/-- The recursion for `(Qp 6 α)'`. -/
theorem Qp6_d1_eval (α v : ℝ) :
    (Qp 6 α).derivative.eval v
      = 4 * v * (Qp 5 α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 5 α).derivative.derivative.eval v
        + α * (Qp 5 α).eval v
        + α * (v - 1 / 3) * (Qp 5 α).derivative.eval v :=
  Work.FTS.LocDataExt.Qp_deriv_succ_eval 5 α v

/-- The recursion for `Qp 7 α`. -/
theorem Qp7_eval (α v : ℝ) :
    (Qp 7 α).eval v
      = -2 * (1 - v ^ 2) * (Qp 6 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 6 α).eval v :=
  Qp_succ_eval 6 α v

/-! ## Assembling bounds from termwise bounds -/

/-- `|a + b| ≤ A + B` from termwise bounds. -/
theorem abs_sum_le2 {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a + b| ≤ A + B := by
  linarith [abs_add_le a b]

/-- `|a + b + c + d| ≤ A + B + C + D` from termwise bounds (left-associated sum). -/
theorem abs_sum_le4 {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) : |a + b + c + d| ≤ A + B + C + D := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-- `|a + b + c + d + e| ≤ A + B + C + D + E` from termwise bounds (left-associated sum). -/
theorem abs_sum_le5 {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) : |a + b + c + d + e| ≤ A + B + C + D + E := by
  have h1 : |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
  have h2 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h3 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h4 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-- `|α| ≤ 1` for `0 ≤ α ≤ 1`. -/
theorem abs_alpha_le_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : |α| ≤ 1 := by
  rwa [abs_of_nonneg hα0]

/-- `|α·(v - 1/3)| ≤ 4/3` for `0 ≤ α ≤ 1` and `|v| ≤ 1`. -/
theorem abs_alpha_sub_third_le {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |α * (v - 1 / 3)| ≤ 4 / 3 :=
  (abs_mul_le_of (A := 1) (B := 4 / 3) (abs_alpha_le_one hα0 hα1) (abs_sub_third_le hv)
    (by norm_num)).trans (by norm_num)

/-! ## The chain of derivative bounds

Each statement bounds the `k`-th derivative of `Qp j α` on `|v| ≤ 1` uniformly for
`0 ≤ α ≤ 1`. -/

/-- `B(3,3)`: the third derivative of `Qp 3 α`. -/
theorem Qp3_deriv3_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).derivative.derivative.derivative.eval v| ≤ 2640 := by
  rw [Qp3_d3_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hT : |(Qp 2 α).derivative.derivative.derivative.eval v| ≤ 90 :=
    Work.FTS.LocData6.Qp2_deriv3_bound hα0 hα1
  have hU : |(Qp 2 α).derivative.derivative.eval v| ≤ 96 :=
    Work.FTS.LocDataExt.Qp2_deriv2_bound hα0 hα1 hv
  have h4 : (Qp 2 α).derivative.derivative.derivative.derivative.eval v = 0 :=
    Qp2_deriv4_eval α v
  have hA : |(-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.derivative.eval v|
      ≤ 2 * 0 := by
    rw [h4, mul_zero, abs_zero]; norm_num
  have hB : |12 * v * (Qp 2 α).derivative.derivative.derivative.eval v| ≤ 12 * 90 := by
    rw [show 12 * v * (Qp 2 α).derivative.derivative.derivative.eval v
        = (12 * v) * (Qp 2 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 12) (B := 90)
      (by rw [abs_mul]; norm_num; exact hv) hT (by norm_num)
  have hC : |12 * (Qp 2 α).derivative.derivative.eval v| ≤ 12 * 96 :=
    abs_mul_le_of (A := 12) (B := 96) (by norm_num) hU (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.derivative.eval v|
      ≤ (4 / 3) * 90 := by
    rw [show α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 2 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 90)
      (abs_alpha_sub_third_le hα0 hα1 hv) hT (by norm_num)
  have hE : |3 * α * (Qp 2 α).derivative.derivative.eval v| ≤ 3 * 96 := by
    rw [show 3 * α * (Qp 2 α).derivative.derivative.eval v
        = (3 * α) * (Qp 2 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 3) (B := 96)
      (by rw [abs_mul]; norm_num; exact hαa) hU (by norm_num)
  have hsum := abs_sum_le5 hA hB hC hD hE
  linarith [hsum]

/-- `B(3,4)`: the fourth derivative of `Qp 3 α`. -/
theorem Qp3_deriv4_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).derivative.derivative.derivative.derivative.eval v| ≤ 2520 := by
  rw [Qp3_d4_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hT : |(Qp 2 α).derivative.derivative.derivative.eval v| ≤ 90 :=
    Work.FTS.LocData6.Qp2_deriv3_bound hα0 hα1
  have h4 : (Qp 2 α).derivative.derivative.derivative.derivative.eval v = 0 :=
    Qp2_deriv4_eval α v
  have h5 : (Qp 2 α).derivative.derivative.derivative.derivative.derivative.eval v = 0 :=
    Qp2_deriv5_eval α v
  have hA : |(-2) * (1 - v ^ 2)
      * (Qp 2 α).derivative.derivative.derivative.derivative.derivative.eval v| ≤ 2 * 0 := by
    rw [h5, mul_zero, abs_zero]; norm_num
  have hB : |16 * v * (Qp 2 α).derivative.derivative.derivative.derivative.eval v| ≤ 16 * 0 := by
    rw [show 16 * v * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        = (16 * v) * (Qp 2 α).derivative.derivative.derivative.derivative.eval v by ring]
    rw [h4, mul_zero, abs_zero]; norm_num
  have hC : |24 * (Qp 2 α).derivative.derivative.derivative.eval v| ≤ 24 * 90 :=
    abs_mul_le_of (A := 24) (B := 90) (by norm_num) hT (by norm_num)
  have hD : |α * (v - 1 / 3)
      * (Qp 2 α).derivative.derivative.derivative.derivative.eval v| ≤ (4 / 3) * 0 := by
    rw [show α * (v - 1 / 3)
        * (Qp 2 α).derivative.derivative.derivative.derivative.eval v
        = (α * (v - 1 / 3))
          * (Qp 2 α).derivative.derivative.derivative.derivative.eval v by ring]
    rw [h4, mul_zero, abs_zero]; norm_num
  have hE : |4 * α * (Qp 2 α).derivative.derivative.derivative.eval v| ≤ 4 * 90 := by
    rw [show 4 * α * (Qp 2 α).derivative.derivative.derivative.eval v
        = (4 * α) * (Qp 2 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4) (B := 90)
      (by rw [abs_mul]; norm_num; exact hαa) hT (by norm_num)
  have hsum := abs_sum_le5 hA hB hC hD hE
  linarith [hsum]

/-- `B(4,2)`: the second derivative of `Qp 4 α`. -/
theorem Qp4_deriv2_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).derivative.derivative.eval v| ≤ 21103 := by
  rw [Qp4_d2_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hS : |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 :=
    Work.FTS.LocDataExt.Qp3_deriv_bound hα0 hα1 hv
  have hU : |(Qp 3 α).derivative.derivative.eval v| ≤ 1384 :=
    Work.FTS.LocData6.Qp3_deriv2_bound hα0 hα1 hv
  have h3 : |(Qp 3 α).derivative.derivative.derivative.eval v| ≤ 2640 :=
    Qp3_deriv3_bound hα0 hα1 hv
  have hA : |(4 + 2 * α) * (Qp 3 α).derivative.eval v| ≤ 6 * (13072 / 27) :=
    abs_mul_le_of (A := 6) (B := 13072 / 27) h4 hS (by norm_num)
  have hB : |8 * v * (Qp 3 α).derivative.derivative.eval v| ≤ 8 * 1384 := by
    rw [show 8 * v * (Qp 3 α).derivative.derivative.eval v
        = (8 * v) * (Qp 3 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 8) (B := 1384)
      (by rw [abs_mul]; norm_num; exact hv) hU (by norm_num)
  have hC : |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.derivative.eval v|
      ≤ 2 * 2640 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 3 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 2640)
      (by rw [abs_mul]; norm_num; exact h1) h3 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.eval v| ≤ (4 / 3) * 1384 := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 1384)
      (abs_alpha_sub_third_le hα0 hα1 hv) hU (by norm_num)
  have hsum := abs_sum_le4 hA hB hC hD
  linarith [hsum]

/-- `B(4,3)`: the third derivative of `Qp 4 α`. -/
theorem Qp4_deriv3_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).derivative.derivative.derivative.eval v| ≤ 61000 := by
  rw [Qp4_d3_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hU : |(Qp 3 α).derivative.derivative.eval v| ≤ 1384 :=
    Work.FTS.LocData6.Qp3_deriv2_bound hα0 hα1 hv
  have h3 : |(Qp 3 α).derivative.derivative.derivative.eval v| ≤ 2640 :=
    Qp3_deriv3_bound hα0 hα1 hv
  have h4 : |(Qp 3 α).derivative.derivative.derivative.derivative.eval v| ≤ 2520 :=
    Qp3_deriv4_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2)
      * (Qp 3 α).derivative.derivative.derivative.derivative.eval v| ≤ 2 * 2520 := by
    rw [show (-2) * (1 - v ^ 2)
          * (Qp 3 α).derivative.derivative.derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2))
          * (Qp 3 α).derivative.derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 2520)
      (by rw [abs_mul]; norm_num; exact h1) h4 (by norm_num)
  have hB : |12 * v * (Qp 3 α).derivative.derivative.derivative.eval v| ≤ 12 * 2640 := by
    rw [show 12 * v * (Qp 3 α).derivative.derivative.derivative.eval v
        = (12 * v) * (Qp 3 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 12) (B := 2640)
      (by rw [abs_mul]; norm_num; exact hv) h3 (by norm_num)
  have hC : |12 * (Qp 3 α).derivative.derivative.eval v| ≤ 12 * 1384 :=
    abs_mul_le_of (A := 12) (B := 1384) (by norm_num) hU (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.derivative.eval v|
      ≤ (4 / 3) * 2640 := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).derivative.derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 2640)
      (abs_alpha_sub_third_le hα0 hα1 hv) h3 (by norm_num)
  have hE : |3 * α * (Qp 3 α).derivative.derivative.eval v| ≤ 3 * 1384 := by
    rw [show 3 * α * (Qp 3 α).derivative.derivative.eval v
        = (3 * α) * (Qp 3 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 3) (B := 1384)
      (by rw [abs_mul]; norm_num; exact hαa) hU (by norm_num)
  have hsum := abs_sum_le5 hA hB hC hD hE
  linarith [hsum]

/-- `B(5,1)`: the first derivative of `Qp 5 α`. -/
theorem Qp5_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 5 α).derivative.eval v| ≤ 72557 := by
  rw [Qp5_d1_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hS : |(Qp 4 α).derivative.eval v| ≤ 443660 / 81 :=
    Work.FTS.LocData6.Qp4_deriv_bound hα0 hα1 hv
  have hU : |(Qp 4 α).derivative.derivative.eval v| ≤ 21103 :=
    Qp4_deriv2_bound hα0 hα1 hv
  have hQ : |(Qp 4 α).eval v| ≤ 276496 / 243 :=
    Work.FTS.LocData6.Qp4_eval_bound_sharp hα0 hα1 hv
  have hA : |4 * v * (Qp 4 α).derivative.eval v| ≤ 4 * (443660 / 81) := by
    rw [show 4 * v * (Qp 4 α).derivative.eval v
        = (4 * v) * (Qp 4 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4) (B := 443660 / 81)
      (by rw [abs_mul]; norm_num; exact hv) hS (by norm_num)
  have hB : |(-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.eval v| ≤ 2 * 21103 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 4 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 21103)
      (by rw [abs_mul]; norm_num; exact h1) hU (by norm_num)
  have hC : |α * (Qp 4 α).eval v| ≤ 1 * (276496 / 243) :=
    abs_mul_le_of (A := 1) (B := 276496 / 243) hαa hQ (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 4 α).derivative.eval v| ≤ (4 / 3) * (443660 / 81) := by
    rw [show α * (v - 1 / 3) * (Qp 4 α).derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 4 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 443660 / 81)
      (abs_alpha_sub_third_le hα0 hα1 hv) hS (by norm_num)
  have hsum := abs_sum_le4 hA hB hC hD
  linarith [hsum]

/-- `B(5,2)`: the second derivative of `Qp 5 α`. -/
theorem Qp5_deriv2_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 5 α).derivative.derivative.eval v| ≤ 351830 := by
  rw [Qp5_d2_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hS : |(Qp 4 α).derivative.eval v| ≤ 443660 / 81 :=
    Work.FTS.LocData6.Qp4_deriv_bound hα0 hα1 hv
  have hU : |(Qp 4 α).derivative.derivative.eval v| ≤ 21103 :=
    Qp4_deriv2_bound hα0 hα1 hv
  have h3 : |(Qp 4 α).derivative.derivative.derivative.eval v| ≤ 61000 :=
    Qp4_deriv3_bound hα0 hα1 hv
  have hA : |(4 + 2 * α) * (Qp 4 α).derivative.eval v| ≤ 6 * (443660 / 81) :=
    abs_mul_le_of (A := 6) (B := 443660 / 81) h4 hS (by norm_num)
  have hB : |8 * v * (Qp 4 α).derivative.derivative.eval v| ≤ 8 * 21103 := by
    rw [show 8 * v * (Qp 4 α).derivative.derivative.eval v
        = (8 * v) * (Qp 4 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 8) (B := 21103)
      (by rw [abs_mul]; norm_num; exact hv) hU (by norm_num)
  have hC : |(-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.derivative.eval v|
      ≤ 2 * 61000 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 4 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 61000)
      (by rw [abs_mul]; norm_num; exact h1) h3 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 4 α).derivative.derivative.eval v| ≤ (4 / 3) * 21103 := by
    rw [show α * (v - 1 / 3) * (Qp 4 α).derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 4 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 21103)
      (abs_alpha_sub_third_le hα0 hα1 hv) hU (by norm_num)
  have hsum := abs_sum_le4 hA hB hC hD
  linarith [hsum]

/-- `B(6,0)`: `Qp 6 α` on `[-1,1]`. -/
theorem Qp6_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 6 α).eval v| ≤ 278500 := by
  rw [Qp6_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hS : |(Qp 5 α).derivative.eval v| ≤ 72557 := Qp5_deriv_bound hα0 hα1 hv
  have hQ : |(Qp 5 α).eval v| ≤ 100000 := Work.FTS.LocData6.Qp5_eval_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 5 α).derivative.eval v| ≤ 2 * 72557 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 5 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 5 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 72557)
      (by rw [abs_mul]; norm_num; exact h1) hS (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 5 α).eval v| ≤ (4 / 3) * 100000 := by
    rw [show α * (v - 1 / 3) * (Qp 5 α).eval v
        = (α * (v - 1 / 3)) * (Qp 5 α).eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 100000)
      (abs_alpha_sub_third_le hα0 hα1 hv) hQ (by norm_num)
  have hsum := abs_sum_le2 hA hB
  linarith [hsum]

/-- `B(6,1)`: the first derivative of `Qp 6 α`. -/
theorem Qp6_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 6 α).derivative.eval v| ≤ 1190700 := by
  rw [Qp6_d1_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hS : |(Qp 5 α).derivative.eval v| ≤ 72557 := Qp5_deriv_bound hα0 hα1 hv
  have hU : |(Qp 5 α).derivative.derivative.eval v| ≤ 351830 := Qp5_deriv2_bound hα0 hα1 hv
  have hQ : |(Qp 5 α).eval v| ≤ 100000 := Work.FTS.LocData6.Qp5_eval_bound hα0 hα1 hv
  have hA : |4 * v * (Qp 5 α).derivative.eval v| ≤ 4 * 72557 := by
    rw [show 4 * v * (Qp 5 α).derivative.eval v
        = (4 * v) * (Qp 5 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4) (B := 72557)
      (by rw [abs_mul]; norm_num; exact hv) hS (by norm_num)
  have hB : |(-2) * (1 - v ^ 2) * (Qp 5 α).derivative.derivative.eval v| ≤ 2 * 351830 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 5 α).derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 5 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 351830)
      (by rw [abs_mul]; norm_num; exact h1) hU (by norm_num)
  have hC : |α * (Qp 5 α).eval v| ≤ 1 * 100000 :=
    abs_mul_le_of (A := 1) (B := 100000) hαa hQ (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 5 α).derivative.eval v| ≤ (4 / 3) * 72557 := by
    rw [show α * (v - 1 / 3) * (Qp 5 α).derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 5 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 72557)
      (abs_alpha_sub_third_le hα0 hα1 hv) hS (by norm_num)
  have hsum := abs_sum_le4 hA hB hC hD
  linarith [hsum]

/-- `B(7,0)`: `Qp 7 α` on `[-1,1]`. -/
theorem Qp7_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 7 α).eval v| ≤ 2752800 := by
  rw [Qp7_eval α v]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hαa : |α| ≤ 1 := abs_alpha_le_one hα0 hα1
  have hS : |(Qp 6 α).derivative.eval v| ≤ 1190700 := Qp6_deriv_bound hα0 hα1 hv
  have hQ : |(Qp 6 α).eval v| ≤ 278500 := Qp6_eval_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 6 α).derivative.eval v| ≤ 2 * 1190700 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 6 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 6 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2) (B := 1190700)
      (by rw [abs_mul]; norm_num; exact h1) hS (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 6 α).eval v| ≤ (4 / 3) * 278500 := by
    rw [show α * (v - 1 / 3) * (Qp 6 α).eval v
        = (α * (v - 1 / 3)) * (Qp 6 α).eval v by ring]
    exact abs_mul_le_of (A := 4 / 3) (B := 278500)
      (abs_alpha_sub_third_le hα0 hα1 hv) hQ (by norm_num)
  have hsum := abs_sum_le2 hA hB
  linarith [hsum]

/-! ## The coefficient bound and the main theorem -/

/-- **The coefficient bound `|Tfun j α θ| ≤ 10⁷` for `j ≤ 7`**, extending
`Work.FTS.LocData6.Tfun_abs_le5` by two orders. -/
theorem Tfun_abs_le7 (j : ℕ) (hj : j ≤ 7) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    |Work.Spaces.Tfun j α θ| ≤ 10000000 := by
  have hα0 : 0 ≤ α := le_of_lt hα
  have hv : |Real.cos (2 * θ)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  by_cases h5 : j ≤ 5
  · exact (Work.FTS.LocData6.Tfun_abs_le5 j h5 α hα hα1 θ).trans (by norm_num)
  · have h6 : 6 ≤ j := by omega
    interval_cases j
    · rw [Tfun_eq_Qp 6 α]
      exact (Qp6_eval_bound hα0 hα1 hv).trans (by norm_num)
    · rw [Tfun_eq_Qp 7 α]
      exact (Qp7_eval_bound hα0 hα1 hv).trans (by norm_num)

/-- The angular jet bound `|D_θ^i Γ| ≤ 10⁷·Γ` on `Iθ`, for `i ≤ 8`.  As in the lower-order
files, the statement is reduced through `Work.Spaces.dthU_iter_Gam_abs_bound` to the
coefficient bound `|Tfun (i-1) α| ≤ 10⁷` (`Tfun_abs_le7`). -/
theorem DthIter_Gam_abs_le8 (i : ℕ) (hi : i ≤ 8) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 10000000 * Work.Spaces.Gam α θ := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
    nlinarith
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 10000000 :=
      fun θ' _ => Tfun_abs_le7 (i - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα 10000000 hT θ hθ
    rw [DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
    calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 10000000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 10000000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG0]

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.OneSubChi_deriv_bound8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

/-! ## The weighted derivatives of `1 - χ`, up to order `8`

The order-`5` chapter (`Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5`) and the order-`6`
chapter (`Submission.Work.FTS.LocData6.oneSubChi_jet_le6`) prove
`|x ^ k · ∂^k (1 - χ)(x)| ≤ M` for `k ≤ 5` resp. `k ≤ 6` by a crude argument: for `k = 0` the
bound is `1`, and for `k ≥ 1` the function `x ↦ x ^ k · ∂^k (1 - χ)(x)` is continuous (χ is
`C^∞`) and vanishes off `|x| ≤ 2`, hence is bounded on the compact `[-2,2]`.  Nothing in that
argument uses the order bound, so the same proof yields every order; here we collect the terms
`k ≤ 8`. -/

theorem OneSubChi_deriv_bound8 :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 8, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ M := by
  have hsm : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  -- For every single order `k` the weighted derivative is bounded.
  have key : ∀ k : ℕ, ∃ Mk : ℝ, 0 ≤ Mk ∧
      ∀ x : ℝ, |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ Mk := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · -- `k = 0`: the bound `|1 - χ x| ≤ 1`
      subst h0
      refine ⟨1, zero_le_one, fun x => ?_⟩
      have hxg : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
          = 1 - Work.Stability.chi x :=
        congrFun (iteratedDeriv_zero (f := fun x : ℝ => (1 : ℝ) - Work.Stability.chi x)) x
      rw [hxg]
      simp only [pow_zero, one_mul]
      rw [abs_le]
      constructor
      · linarith [Work.Stability.chi_le_one x]
      · linarith [Work.Stability.chi_nonneg x]
    · -- `k ≥ 1`: continuity on the compact set `[-2,2]` plus vanishing off `(-2,2)`
      have hcont : Continuous (fun x : ℝ =>
          x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x) :=
        (continuous_id.pow k).mul (hsm.continuous_iteratedDeriv k (by simp))
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := fun x : ℝ =>
          x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x)
        hcont.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
      by_cases hx : |x| ≤ 2
      · have hxmem : x ∈ Set.Icc (-2 : ℝ) 2 := by
          rw [Set.mem_Icc, ← abs_le]; exact hx
        have hbound := hC x hxmem
        rw [Real.norm_eq_abs] at hbound
        exact le_trans hbound (le_max_left _ _)
      · -- `|x| > 2`: `χ ≡ 0` on a neighbourhood of `x`, so all its derivatives vanish there
        have hx2 : 2 < |x| := not_le.mp hx
        have hvan : iteratedDeriv k Work.Stability.chi x = 0 := by
          have hev : Work.Stability.chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
            have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| :=
              (isOpen_lt continuous_const continuous_abs).mem_nhds (by simpa using hx2)
            filter_upwards [hmem] with y hy
            exact Work.Stability.chi_eq_zero (le_of_lt hy)
          rw [hev.iteratedDeriv_eq k, Work.Spaces.iteratedDeriv_zero_fun k x]
        have hgk : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
            = - iteratedDeriv k Work.Stability.chi x := by
          rw [iteratedDeriv_const_sub hpos (1 : ℝ)]
          simp
        rw [hgk, hvan]
        simp
  let Mf : ℕ → ℝ := fun k => Classical.choose (key k)
  have hMf_nn : ∀ k : ℕ, 0 ≤ Mf k := fun k => (Classical.choose_spec (key k)).1
  have hMf : ∀ k : ℕ, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ Mf k :=
    fun k x => (Classical.choose_spec (key k)).2 x
  refine ⟨∑ k ∈ Finset.range 9, Mf k, Finset.sum_nonneg (fun k _ => hMf_nn k), fun k hk x => ?_⟩
  have hk9 : k ∈ Finset.range 9 := Finset.mem_range.mpr (by omega)
  exact le_trans (hMf k x) (Finset.single_le_sum (fun i _ => hMf_nn i) hk9)

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.zfarR_jet_le8_of_jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_LocDatum3a

set_option maxHeartbeats 1600000

/-! ## The order-`8` jet bound of the far factor `zfarR L`

`zfarR L z = (1 - χ(z/L))·FM.Fstar z` is a product of two functions of `z` alone whose
`z`-slices are `C^∞` on `(-1,∞)` (`Work.FTS.LocData.ZFBase.contDiffOn_slice_oneSubChi`,
`...contDiffOn_slice_FM_Fstar`), so the Leibniz rule
`Work.FTS.LocData.DzIter_mul_smoothQuad` applies at every order; the `j`-th jet (`j ≤ 8`)
is `∑_{b≤j} (j choose b)·(jet_b u)·(jet_{j-b} v)`, and the two jet bounds supplied as
hypotheses (`Cu` for the cut-off factor, `Cv/z` for `FM.Fstar`) give
`|jet_j| ≤ (∑_{b≤j} (j choose b))·Cu·Cv/z = 2^j·Cu·Cv/z ≤ 256·Cu·Cv/z`.

This is the order-`8` instance of the chain
`Work.FTS.LocDataExt.zfarR_jet_le5_of_jets` (order `5`) and
`Work.FTS.LocData6.zfarR_jet_le6_of_jets` (order `6`); only the binomial constant changes. -/

/-- The binomial sum in closed form: `∑_{b≤j} (j choose b) = 2^j`. -/
private theorem sum_range_choose_real8 (j : ℕ) :
    (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) = 2 ^ j := by
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

/-- **The assembly**: from a bound `Cu` for the `D_z`-jets of the cut-off factor
`1 - χ(·/L)` (uniform in the scale `L ≥ 1`) up to order `8` and a bound `Cv/z` for the
`D_z`-jets of `FM.Fstar` up to order `8`, the jets of `zfarR L = (1 - χ(·/L))·FM.Fstar`
decay like `(256·Cu·Cv)/z` on `[L, 2L]`, uniformly in `L ≥ 1` (`2^8 = 256`). -/
theorem zfarR_jet_le8_of_jets {Cu Cv : ℝ} (hCu1 : 1 ≤ Cu) (hCv : 0 < Cv)
    (hCu : ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 8 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu)
    (hCvM : ∀ a : ℕ, a ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ| ≤ Cv / z) :
    ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 8 → ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ|
        ≤ 256 * Cu * Cv / z := by
  intro L hL j hj z hz θ
  have hz1 : 1 ≤ z := le_trans hL hz.1
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hz0 : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hCu0 : 0 ≤ Cu := le_trans zero_le_one hCu1
  have hCvz : 0 ≤ Cv / z := div_nonneg (le_of_lt hCv) (le_of_lt hzpos)
  rw [Work.FTS.LocDataExt.DzIter_zfarR_eq_sum L j hz0 θ]
  have hstep : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
          * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ)|
        ≤ (j.choose b : ℝ) * (Cu * (Cv / z)) := by
    intro b hb
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have h1 : b ≤ 8 := le_trans hbj hj
    have h2 : j - b ≤ 8 := by omega
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [abs_mul]
    exact mul_le_mul (hCu L hL b h1 z hz0 θ) (hCvM (j - b) h2 z hz1 θ)
      (abs_nonneg _) hCu0
  calc |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
        (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
          * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ)|
      ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * (Cu * (Cv / z)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep)
    _ = (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) * (Cu * (Cv / z)) := by
        rw [Finset.sum_mul]
    _ = 2 ^ j * (Cu * (Cv / z)) := by rw [sum_range_choose_real8]
    _ ≤ 256 * Cu * Cv / z := by
        have h256 : (2 : ℝ) ^ j ≤ 256 := by
          have h : (2 : ℝ) ^ j ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
          norm_num at h
          exact h
        have hnn : 0 ≤ Cu * (Cv / z) := mul_nonneg hCu0 hCvz
        calc 2 ^ j * (Cu * (Cv / z)) ≤ 256 * (Cu * (Cv / z)) :=
              mul_le_mul_of_nonneg_right h256 hnn
          _ = 256 * Cu * Cv / z := by ring

end Work.FTS_LocDatum3a
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_mul_fin_local =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys.GdotAux

set_option maxHeartbeats 1600000

/-!
# The Leibniz rule for `D_z^j D_θ^i` at finite order on an open set

`Work.Spaces.mixed j i f = D_z^j D_θ^i f`, where `D_z f = z ∂_z f` and `D_θ f = sin(2θ) ∂_θ f`
are derivations for the pointwise product, so the iterated Leibniz rule

`D_z^j D_θ^i (f·h) = ∑_{a ≤ i} ∑_{b ≤ j} C(i,a) C(j,b) (D_z^b D_θ^a f)(D_z^{j-b} D_θ^{i-a} h)`

holds.  Here it is proved for `f`, `h` that are jointly `C^{j+i}` on an *arbitrary open* set
`V ⊆ ℝ²`, at a point of `V`; the consumer
`Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_mul_le2` specialises it to `V = Q0` and `C²` data.

The proof is the direct induction on the pair `(a,b)`: `D_z^a D_θ^b = D_z (D_z^{a-1} D_θ^b)`
resp. `D_θ (D_z^a D_θ^{b-1})`, one application of the product rule for `D_z` resp. `D_θ`, and
the Pascal identity `Work.Spaces.leibniz_step` to recombine the two shifted binomial sums.
The differentiability side conditions are discharged from the local `C^{a+b}` hypothesis
through `Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le` (every mixed
block costs its total order in regularity), and the induction hypothesis, which holds only on
`V`, is transported across `D_z`/`D_θ` by the locality of the derivative on the open set `V`.
-/

/-! ## Pointwise product rules and linearity for `D_z` and `D_θ` -/


private lemma Dz_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ) := by
  show z * deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
      = cc * (z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z))
  rw [show deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
        = deriv (fun y => cc * ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) y) z
        from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dz_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => A i z' θ) z) :
    Work.Spaces.Dz (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dz (A i) z θ := by
  have hfun : (fun z' : ℝ => ∑ i ∈ s, A i z' θ) = (∑ i ∈ s, fun z' : ℝ => A i z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  show z * deriv (fun z' : ℝ => ∑ i ∈ s, A i z' θ) z
      = ∑ i ∈ s, z * deriv (fun z' : ℝ => A i z' θ) z
  rw [hfun, deriv_sum h, Finset.mul_sum]


private lemma Dth_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ) := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
      = cc * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ))
  rw [show deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
        = deriv (fun y => cc * ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) y) θ
        from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dth_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun θ' => A i z θ') θ) :
    Work.Spaces.Dth (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dth (A i) z θ := by
  have hfun : (fun θ' : ℝ => ∑ i ∈ s, A i z θ') = (∑ i ∈ s, fun θ' : ℝ => A i z θ') := by
    funext θ'
    rw [Finset.sum_apply]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => ∑ i ∈ s, A i z θ') θ
      = ∑ i ∈ s, Real.sin (2 * θ) * deriv (fun θ' : ℝ => A i z θ') θ
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma differentiableAt_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {z : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) z) :
    DifferentiableAt ℝ (fun z' => ∑ i ∈ s, A i z') z := by
  have hfun : (fun z' => ∑ i ∈ s, A i z') = (∑ i ∈ s, A i) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

private lemma differentiableAt_sum_θ {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) θ) :
    DifferentiableAt ℝ (fun θ' => ∑ i ∈ s, A i θ') θ := by
  have hfun : (fun θ' => ∑ i ∈ s, A i θ') = (∑ i ∈ s, A i) := by
    funext θ'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

/-! ## Locality of `D_z` and `D_θ` on an open set -/

private lemma Dz_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) :
    ∀ p ∈ V, Work.Spaces.Dz f p.1 p.2 = Work.Spaces.Dz g p.1 p.2 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have htend : Tendsto (fun z' : ℝ => ((z', θ) : ℝ × ℝ)) (𝓝 z) (𝓝 (z, θ)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmem : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    filter_upwards [htend.eventually (hV.mem_nhds hp)] with z' hz'
    exact h (z', θ) hz'
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hmem.deriv_eq]

private lemma Dth_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) :
    ∀ p ∈ V, Work.Spaces.Dth f p.1 p.2 = Work.Spaces.Dth g p.1 p.2 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have htend : Tendsto (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) (𝓝 θ) (𝓝 (z, θ)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hmem : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [htend.eventually (hV.mem_nhds hp)] with θ' hθ'
    exact h (z, θ') hθ'
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hmem.deriv_eq]

/-! ## Differentiability of the mixed blocks at a point of `V` -/

private lemma diffAt_mixed_z {N : ℕ} {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ N (Function.uncurry F) V) {i j : ℕ} (hij : i + j + 1 ≤ N)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j F z' θ) z := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed i j F)) V :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le hV j i 1 (by omega) hF
  have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed i j F)) (z, θ) :=
    (h1.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz)
  exact Work.Spaces.differentiableAt_slice_fst hd

private lemma diffAt_mixed_θ {N : ℕ} {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ N (Function.uncurry F) V) {i j : ℕ} (hij : i + j + 1 ≤ N)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j F z θ') θ := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed i j F)) V :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le hV j i 1 (by omega) hF
  have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed i j F)) (z, θ) :=
    (h1.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz)
  exact Work.Spaces.differentiableAt_slice_snd hd

/-! ## The finite-order Leibniz rule -/

theorem mixedMulFinAuxLocal {N : ℕ} {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ N (Function.uncurry f) V)
    (hg : ContDiffOn ℝ N (Function.uncurry g) V) :
    ∀ a b : ℕ, a + b ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
  have hfz : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j f z' θ) z :=
    fun i j hij z θ hz => diffAt_mixed_z hV hf hij hz
  have hgz : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j g z' θ) z :=
    fun i j hij z θ hz => diffAt_mixed_z hV hg hij hz
  have hfθ : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j f z θ') θ :=
    fun i j hij z θ hz => diffAt_mixed_θ hV hf hij hz
  have hgθ : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j g z θ') θ :=
    fun i j hij z θ hz => diffAt_mixed_θ hV hg hij hz
  have key : ∀ n : ℕ, ∀ a b : ℕ, a + b ≤ n → a + b ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
    intro n
    induction n with
    | zero =>
        intro a b hsum hN z θ hz
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha
        subst hb
        simp [Work.Spaces.mixed]
    | succ n ih =>
        intro a b hsum hN z θ hz
        rcases Nat.eq_zero_or_pos a with ha | ha
        · subst ha
          rcases Nat.eq_zero_or_pos b with hb | hb
          · subst hb
            simp [Work.Spaces.mixed]
          · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            have hs : 0 + b' ≤ n := by omega
            have hN' : 0 + b' ≤ N := by omega
            have hEqOn : ∀ p ∈ V,
                Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ) p.1 p.2
                  = (fun z θ => ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) p.1 p.2 :=
              fun p hp => ih 0 b' hs hN' p.1 p.2 hp
            have hL : Work.Spaces.mixed 0 (b' + 1) (fun z θ => f z θ * g z θ) z θ
                = Work.Spaces.Dth
                    (Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ)) z θ := by
              simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero]
            have hcong := Dth_congr_of_eqOn
              (f := Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ))
              (g := fun z θ => ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
              hV hEqOn (z, θ) hz
            rw [hL, hcong]
            have hstep1 : Work.Spaces.Dth (fun z θ => ∑ i ∈ Finset.range (0 + 1),
                  ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) z θ
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i (j + 1) f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ) := by
              rw [Dth_sum (Finset.range (0 + 1))
                    (fun i z θ => ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun i hi => differentiableAt_sum_θ (Finset.range (b' + 1))
                      (fun j θ' => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ'
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ'))
                      (fun j hj => ((hfθ i j (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hz).mul
                        (hgθ (0 - i) (b' - j) (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hz)).const_mul _))]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [Dth_sum (Finset.range (b' + 1))
                    (fun j z θ => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun j hj => ((hfθ i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz).mul
                      (hgθ (0 - i) (b' - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz)).const_mul _)]
              refine Finset.sum_congr rfl fun j hj => ?_
              have hi0 : i = 0 := by have := Finset.mem_range.mp hi; omega
              rw [Dth_cmul (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ))
                    (hfθ i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)
                    (hgθ (0 - i) (b' - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)]
              rw [show Work.Spaces.Dth (Work.Spaces.mixed i j f) z θ
                    = Work.Spaces.mixed i (j + 1) f z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero],
                  show Work.Spaces.Dth (Work.Spaces.mixed (0 - i) (b' - j) g) z θ
                    = Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero, Nat.sub_zero]]
            have hstep2 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1 + 1),
                    (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
              refine Finset.sum_congr rfl fun i hi => ?_
              have h1 : (∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                  = ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1),
                      (b'.choose j : ℝ) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ)) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              rw [h1, Work.Spaces.leibniz_step b' (fun j => Work.Spaces.mixed i j f z θ)
                    (fun m => Work.Spaces.mixed (0 - i) m g z θ)]
              have h2 : ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1 + 1),
                    ((b' + 1).choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ))
                  = ∑ j ∈ Finset.range (b' + 1 + 1),
                      (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              exact h2
            rw [hstep1, hstep2]
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hs : a' + b ≤ n := by omega
          have hN' : a' + b ≤ N := by omega
          have hEqOn : ∀ p ∈ V,
              Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ) p.1 p.2
                = (fun z θ => ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ)) p.1 p.2 :=
            fun p hp => ih a' b hs hN' p.1 p.2 hp
          have hL : Work.Spaces.mixed (a' + 1) b (fun z θ => f z θ * g z θ) z θ
              = Work.Spaces.Dz
                  (Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ)) z θ := by
            simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
          have hcong := Dz_congr_of_eqOn
            (f := Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ))
            (g := fun z θ => ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ))
            hV hEqOn (z, θ) hz
          rw [hL, hcong]
          have hstep1 : Work.Spaces.Dz (fun z θ => ∑ i ∈ Finset.range (a' + 1),
                ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ)) z θ
              = ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed (i + 1) j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ
                    + Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ) := by
            rw [Dz_sum (Finset.range (a' + 1))
                  (fun i z θ => ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun i hi => differentiableAt_sum (Finset.range (b + 1))
                    (fun j z' => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z' θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z' θ))
                    (fun j hj => ((hfz i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz).mul
                      (hgz (a' - i) (b - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz)).const_mul _))]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Dz_sum (Finset.range (b + 1))
                  (fun j z θ => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun j hj => ((hfz i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz).mul
                    (hgz (a' - i) (b - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)).const_mul _)]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Dz_cmul ((a'.choose i : ℝ) * (b.choose j : ℝ))
                  (hfz i j (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hz)
                  (hgz (a' - i) (b - j) (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hz)]
            rw [show Work.Spaces.Dz (Work.Spaces.mixed i j f) z θ
                  = Work.Spaces.mixed (i + 1) j f z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ],
                show Work.Spaces.Dz (Work.Spaces.mixed (a' - i) (b - j) g) z θ
                  = Work.Spaces.mixed (a' - i + 1) (b - j) g z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]]
          have hstep2 : (∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
              = ∑ i ∈ Finset.range (a' + 1 + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
            have hkey1 := Finset.sum_comm (s := Finset.range (a' + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                (Work.Spaces.mixed (i + 1) j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ
                  + Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
            have hkey2 := Finset.sum_comm (s := Finset.range (a' + 1 + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                (Work.Spaces.mixed i j f z θ
                  * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
            rw [hkey1, hkey2]
            refine Finset.sum_congr rfl fun j hj => ?_
            have h1 : (∑ i ∈ Finset.range (a' + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
                = (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1), (a'.choose i : ℝ) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [h1, Work.Spaces.leibniz_step a' (fun i => Work.Spaces.mixed i j f z θ)
                  (fun m => Work.Spaces.mixed m (b - j) g z θ)]
            have h2 : (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1 + 1),
                  ((a' + 1).choose i : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
                = ∑ i ∈ Finset.range (a' + 1 + 1),
                    ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            exact h2
          rw [hstep1, hstep2]
  intro a b hab z θ hz
  exact key (a + b) a b le_rfl hab z θ hz

/-! ## The requested statement -/

theorem mixedMulFinLocal {j i : ℕ} {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V)
    (hf : ContDiffOn ℝ (j + i) (Function.uncurry f) V)
    (hg : ContDiffOn ℝ (j + i) (Function.uncurry g) V) :
    ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro z θ hz
  have h := mixedMulFinAuxLocal (N := j + i) hV hf hg j i le_rfl z θ hz
  rw [h]
  have h2 : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ))
      = ∑ b ∈ Finset.range (j + 1), ∑ a ∈ Finset.range (i + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) :=
    Finset.sum_comm
  rw [h2]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
  ring


end Work.FTS_RegExport.RXT.Sys.GdotAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12_FK_jets_of_datum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12_FK_jets_of_datum` — the `z∂_z`-jets of `L₁₂(F)` and `𝔽K(F)` from the datum hypotheses

`DatumHyp F C` supplies, on the open quadrant `Q0 = (0,∞) × (0,π/2)`, the `C²`-smoothness of
the datum `F`, the pointwise bounds `|D_z^k F| ≤ C` (`k ≤ 2`) and the `L¹`-control
`∫_0^∞ |L12dens F| ≤ C` of the `L₁₂`-density.  From those hypotheses alone the two radial
transforms

* `L₁₂(F)(z) = ∫_z^∞ ∫_θ K(θ)F(s,θ)/s dθ ds`,
* `𝔽K(F)(z)  = ∫_θ F(z,θ)K(θ) dθ`

satisfy the whole order-`≤ 2` jet package: the pointwise bounds `|D_z^j| ≤ 64C⁴` (`j ≤ 2`,
`D_z = z∂_z`), the same for linear combinations, the fundamental-model identity
`D_z L₁₂(F) = -𝔽K(F)`, and the two derivative identities
`∂_z L₁₂(F) = -𝔽K(F)/z`, `∂_z 𝔽K(F)(z) = ∫_θ ∂_zF(z,θ)K(θ) dθ`.

The ingredients live in `L12FKjet.Basic`, `L12FKjet.L12`, `L12FKjet.Jets`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem L12_FK_jets_of_datum :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℝ → ℝ → ℝ) (C : ℝ), 1 ≤ C →
      Work.FTS_RegExport.RXT.Sys.DatumHyp F C →
      ∀ z : ℝ, 0 < z →
        (∀ j : ℕ, j ≤ 2 →
          |Work.Elliptic.DzdIter j (Work.Construction.L12 F) z| ≤ K * C ^ 4 ∧
          |Work.Elliptic.DzdIter j (Work.Construction.FK F) z| ≤ K * C ^ 4 ∧
          (∀ a b : ℝ, |Work.Elliptic.DzdIter j (fun z => a * Work.Construction.L12 F z
              + b * Work.Construction.FK F z) z| ≤ (|a| + |b|) * (K * C ^ 4))) ∧
        (Work.Elliptic.DzdIter 1 (Work.Construction.L12 F) z = - Work.Construction.FK F z) ∧
        HasDerivAt (fun z' => Work.Construction.L12 F z') (- (Work.Construction.FK F z) / z) z ∧
        HasDerivAt (fun z' => Work.Construction.FK F z')
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * Work.Spaces.K θ) z := by
  refine ⟨64, by norm_num, ?_⟩
  intro F C hC1 hD z hz
  have hC : (0 : ℝ) ≤ C := by linarith
  have h2 : ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0 := hD.smooth
  have hb : DatumBnd F C := hD.bnd
  have hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k F z θ| ≤ C :=
    fun k hk z θ hz' hθ0 hθ1 => hb.DzIter_le hk hz' hθ0 hθ1
  have hint : IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := hD.integrable
  have hmass : (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|) ≤ C := hD.mass
  -- the derivative of `𝔽K F`, and hence of `Qang F 0 = 𝔽K F`, at every point of `(0,∞)`
  have hFKd : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Construction.FK F z)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F u θ * Work.Spaces.K θ) u :=
    fun u hu => lfj_hasDerivAt_FK h2 hbd hC hu
  have hQ0d : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Qang F 0) (Work.Elliptic.Qang F 1 u / u) u := by
    intro u hu
    have h := hFKd u hu
    rw [show (fun z => Work.Construction.FK F z) = Work.Elliptic.Qang F 0 from
      funext fun z => (lfj_Qang_zero_eq_FK F z).symm] at h
    have hval : Work.Elliptic.Qang F 1 u / u
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F u θ * Work.Spaces.K θ := by
      rw [lfj_Qang_one_eq F u, mul_div_cancel_left₀ _ (ne_of_gt hu)]
    rwa [hval]
  -- the derivative of `L₁₂ F`
  have hL12d : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Construction.L12 F z)
      (-(Work.Construction.L12dens F u)) u :=
    fun u hu => lfj_L12_hasDerivAt hint
      (lfj_L12dens_continuousAt ((hQ0d u hu).continuousAt) hu) hu
  -- the derivative of `Qang F 1`
  have hQ1d : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Qang F 1) (Work.Elliptic.Qang F 2 u / u) u :=
    fun u hu => lfj_Qang_one_hasDerivAt h2 hbd hC hu
  -- the eventual identities and their pointwise forms
  have hL12_1e := lfj_DzdIter_one_L12_eq hz hL12d
  have hFK_1e := lfj_DzdIter_one_FK_eq hz hFKd
  have hL12_1 : Work.Elliptic.DzdIter 1 (Work.Construction.L12 F) z
      = - Work.Construction.FK F z := lfj_DzdIter_one_L12 hz (hL12d z hz)
  have hL12_2 : Work.Elliptic.DzdIter 2 (Work.Construction.L12 F) z
      = -(Work.Elliptic.Qang F 1 z) := lfj_DzdIter_two_L12 hL12_1e (hQ0d z hz) hz
  have hFK_1 : Work.Elliptic.DzdIter 1 (Work.Construction.FK F) z
      = Work.Elliptic.Qang F 1 z := lfj_DzdIter_one_FK hz (hFKd z hz)
  have hFK_2 : Work.Elliptic.DzdIter 2 (Work.Construction.FK F) z
      = Work.Elliptic.Qang F 2 z := lfj_DzdIter_two_FK hFK_1e (hQ1d z hz) hz
  -- the jet bounds
  have hQ1b : |Work.Elliptic.Qang F 1 z| ≤ 18 * C :=
    lfj_Qang_abs_le hC hbd (m := 1) (by norm_num) hz
  have hQ2b : |Work.Elliptic.Qang F 2 z| ≤ 18 * C :=
    lfj_Qang_abs_le hC hbd (m := 2) (by norm_num) hz
  have hFK0b : |Work.Construction.FK F z| ≤ 18 * C := by
    rw [← lfj_Qang_zero_eq_FK F z]
    exact lfj_Qang_abs_le hC hbd (m := 0) (by norm_num) hz
  have hL0b : |Work.Construction.L12 F z| ≤ C := lfj_L12_abs_le hint hmass hz
  have hC18 : C ≤ 18 * C := by nlinarith [hC, hC1]
  have hBL : ∀ j : ℕ, j ≤ 2 →
      |Work.Elliptic.DzdIter j (Work.Construction.L12 F) z| ≤ 64 * C ^ 4 := by
    intro j hj
    interval_cases j
    · simpa only [Work.Elliptic.DzdIter_zero] using lfj_le_const hC1 (le_trans hL0b hC18)
    · rw [hL12_1]
      simpa only [abs_neg] using lfj_le_const hC1 hFK0b
    · rw [hL12_2]
      simpa only [abs_neg] using lfj_le_const hC1 hQ1b
  have hBF : ∀ j : ℕ, j ≤ 2 →
      |Work.Elliptic.DzdIter j (Work.Construction.FK F) z| ≤ 64 * C ^ 4 := by
    intro j hj
    interval_cases j
    · simpa only [Work.Elliptic.DzdIter_zero] using lfj_le_const hC1 hFK0b
    · rw [hFK_1]
      exact lfj_le_const hC1 hQ1b
    · rw [hFK_2]
      exact lfj_le_const hC1 hQ2b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    refine ⟨hBL j hj, hBF j hj, ?_⟩
    intro a b
    have hlin := lfj_DzdIter_linear (u := fun w => Work.Construction.L12 F w)
      (v := fun w => Work.Construction.FK F w) (a := a) (b := b) (z := z)
      (hL12d z hz).differentiableAt (hFKd z hz).differentiableAt
      (by filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw; exact (hL12d w hw).differentiableAt)
      (by filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw; exact (hFKd w hw).differentiableAt)
      (hL12_1e.differentiableAt_iff.mpr ((hQ0d z hz).differentiableAt.neg))
      (hFK_1e.differentiableAt_iff.mpr (hQ1d z hz).differentiableAt)
    exact lfj_DzdIter_lin_bound hlin hBL hBF j hj
  · exact hL12_1
  · have hval : -(Work.Construction.FK F z) / z = -(Work.Construction.L12dens F z) := by
      rw [← Work.Construction.mul_L12dens_eq_FK (F := F) (ne_of_gt hz), neg_div,
        mul_div_cancel_left₀ _ (ne_of_gt hz)]
    rw [hval]
    exact hL12d z hz
  · exact hFKd z hz

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.jc3_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ## §1 Slice derivatives at finite order -/

/-- For a function which is `C¹` on an open set, the `z`-slice is differentiable and its
derivative is `pz`. -/
lemma hasDerivAt_slice_fst_of_contDiffOn {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry g) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    HasDerivAt (fun z' => g z' θ) (Work.Spaces.pz g z θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    (h.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)
  have h2 : HasFDerivAt (fun z' : ℝ => (z', θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
    hasFDerivAt_prodMk_left z θ
  have h3 : HasDerivAt (fun z' : ℝ => Function.uncurry g (z', θ))
      ((fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1) z := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp z h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1
      = Work.Spaces.pz g z θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact (Work.Spaces.deriv_slice_fst (Function.uncurry g) z θ hd).symm
  rw [hval] at h3
  exact h3

/-- For a function which is `C¹` on an open set, the `θ`-slice is differentiable and its
derivative is `pth`. -/
lemma hasDerivAt_slice_snd_of_contDiffOn {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry g) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    HasDerivAt (fun θ' => g z θ') (Work.Spaces.pth g z θ) θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    (h.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)
  have h2 : HasFDerivAt (fun θ' : ℝ => (z, θ')) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun θ' : ℝ => Function.uncurry g (z, θ'))
      ((fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1) θ := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp θ h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1
      = Work.Spaces.pth g z θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact (Work.Spaces.deriv_slice_snd (Function.uncurry g) z θ hd).symm
  rw [hval] at h3
  exact h3

/-- The definitional relation `mixed (k+1) i f (z,θ) = z · ∂_z (mixed k i f) (z,θ)`. -/
lemma mixed_succ_fst_eq (f : ℝ → ℝ → ℝ) (k i : ℕ) :
    Work.Spaces.mixed (k + 1) i f
      = fun z θ => z * Work.Spaces.pz (Work.Spaces.mixed k i f) z θ := by
  funext z θ
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz]

/-- `D_z` picks out the `z`-derivative: `mixed k i f z θ = z · ∂_z (mixed (k-1) i f) z θ`
for `1 ≤ k`. -/
lemma mixed_fst_eq_mul_pz (f : ℝ → ℝ → ℝ) {k i : ℕ} (hk : 1 ≤ k) (z θ : ℝ) :
    Work.Spaces.mixed k i f z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed (k - 1) i f) z θ := by
  conv_lhs => rw [← Nat.succ_pred_eq_of_pos hk]
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Nat.pred_eq_sub_one]

/-- `D_θ` picks out the `θ`-derivative: `mixed 0 3 f z θ = sin(2θ) · ∂_θ (mixed 0 2 f) z θ`. -/
lemma mixed_zero_three_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 3 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed 0 2 f) z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dth]

/-- `C⁴` spatial regularity gives `C¹` regularity of the mixed slots of order `≤ 3`. -/
lemma contDiffOn_mixed_of_four {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 3) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i f)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le (n := 4)
    Work.FTS.EllipticEst.isOpen_Q0 i j 1 (by omega) h4

/-- `C⁴` spatial regularity gives continuity of the mixed slots of order `≤ 4`. -/
lemma continuousOn_mixed_of_four {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 4) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le (n := 4)
    Work.FTS.EllipticEst.isOpen_Q0 i j 0 (by omega) h4).continuousOn

/-! ## §2 The Landau step on `[0,T]` -/

/-- The abstract Landau step, with the time variable restricted to `[0,T]`.  The passage from
the halfline statement to the interval statement is by clamping `τ` at `T`: the hypotheses on
the primitive are pointwise in `τ` and are inherited by the clamp, while the Lipschitz
hypothesis survives because `|min τ T - min τ' T| ≤ |τ - τ'|`. -/
lemma tau_lip_sqrt_of_primitive_Icc {T : ℝ} (hT : 0 < T)
    (hLandau : ∀ {V W : ℝ → ℝ → ℝ} {x₀ δc L K : ℝ}, 0 < δc → 0 ≤ L → 0 ≤ K →
      (∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |V x τ - V x τ'| ≤ L * |τ - τ'|) →
      (∀ τ : ℝ, 0 ≤ τ → ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δc))) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |W x τ - W x₀ τ| ≤ K * |x - x₀|) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        HasDerivAt (fun x' => V x' τ) (W x τ) x) →
      ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → |τ - τ'| ≤ δc ^ 2 →
        |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'|)
    {V W : ℝ → ℝ → ℝ} {x₀ δc L K : ℝ} (hδc : 0 < δc) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hV : ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc x₀ (x₀ + δc),
      |V x τ - V x τ'| ≤ L * |τ - τ'|)
    (hcont : ∀ τ ∈ Set.Icc (0:ℝ) T, ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δc)))
    (hW : ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc x₀ (x₀ + δc),
      |W x τ - W x₀ τ| ≤ K * |x - x₀|)
    (hderiv : ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc x₀ (x₀ + δc),
      HasDerivAt (fun x' => V x' τ) (W x τ) x) :
    ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T, |τ - τ'| ≤ δc ^ 2 →
      |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'| := by
  intro τ hτ τ' hτ' hdiff
  have hmm : ∀ σ : ℝ, 0 ≤ σ → min σ T ∈ Set.Icc (0:ℝ) T := fun σ hσ =>
    ⟨le_min hσ hT.le, min_le_right _ _⟩
  have hminτ : min τ T = τ := min_eq_left hτ.2
  have hminτ' : min τ' T = τ' := min_eq_left hτ'.2
  have hmin_lip : ∀ σ σ' : ℝ, |min σ T - min σ' T| ≤ |σ - σ'| := by
    intro σ σ'
    have h := abs_min_sub_min_le_max σ T σ' T
    rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h
  have hLand := hLandau (V := fun x σ => V x (min σ T)) (W := fun x σ => W x (min σ T))
    hδc hL hK
    (fun σ σ' hσ hσ' x hx => by
      have h1 := hV (min σ T) (hmm σ hσ) (min σ' T) (hmm σ' hσ') x hx
      exact le_trans h1 (mul_le_mul_of_nonneg_left (hmin_lip σ σ') hL))
    (fun σ hσ => hcont (min σ T) (hmm σ hσ))
    (fun σ hσ x hx => hW (min σ T) (hmm σ hσ) x hx)
    (fun σ hσ x hx => hderiv (min σ T) (hmm σ hσ) x hx)
    τ τ' hτ.1 hτ'.1 hdiff
  simpa [hminτ, hminτ'] using hLand

end Work.FTS_RegExport.RXT
end
end
