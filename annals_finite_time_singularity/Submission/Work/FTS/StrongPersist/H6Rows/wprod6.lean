import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1_norm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

set_option autoImplicit false


end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.AuxInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1Ae/AuxInt` — the integrability toolbox of the `I₁` cut-off expansion

The `ε → 0` and `n → ∞` limits of the cut-off identity `I1Ae.auxCutOff` both need *joint*
integrability (for the product measure `nuQ` on `(0,∞) × (0,π/2)`) of the several integrands
produced by the two integrations by parts:

* the `σ`-slots `f·g·w²σ` — supplied here by `H2W.WeakAux.prod_integrable_mul`, transported
  across the null-set difference between the open and the closed product measure
  (`integrable_w2_sig_mul`);
* the singular `σ₁`-slot `U·V·cos(2θ)·w²σ₁` — supplied by the pointwise AM–GM inequality
  `two_mul_sig1_mul_le` together with the two quadratic dominators (`integrable_w2sig1_cos`);
* bounded multipliers (`χ_n`, `z·χ_n'`) preserve integrability (`integrable_mul_of_bound`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Qd0" => Work.FTS.EllipticEst.H2W.WeakAux.Qd0
local notation "muP" => Work.FTS.EllipticEst.H2W.WeakAux.muP

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)

/-! ## The two product measures -/


/-! ## Bounded multipliers -/


/-! ## The `σ`-slots: `L² · L² ⊆ L¹` for the weight `w²σ` -/


/-! ## The singular `σ₁`-slot -/




end Work.FTS.EllipticEst.I1Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Straight_DzHk_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The straightened solution -/

/-- **The straightened solution** `V = Ψ + Gsing α F · sin 2θ` (the `Straight α F Ψ` of
`StraightDefs`), written out so that it is *definitionally* the function appearing in the
statement of `Straight_DzHk_le`. -/
def Vf (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)

@[simp] theorem Vf_apply (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Vf α F Ψ z θ = Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ) := rfl


/-! ## The elementary `∂_θ`-calculus -/

/-- `SmoothOpen` is closed under the `∂_θ`-iterates. -/
theorem SmoothOpen_pthIter {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (i : ℕ) :
    SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `∂_θ`-iterates are additive on data which are `C^∞` on the open quadrant. -/
theorem pthIter_add_of_smoothOpen {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
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


/-! ## The transfers -/



/-! ## Three-term subadditivity -/






/-! ## The assembly -/




end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.HkIntegrand_perz_le_of_traces =====
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
set_option maxHeartbeats 800000

/-! ## Integrability of a finite sum of integrable functions -/

private lemma integrable_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ} (h : ∀ i ∈ s, MeasureTheory.Integrable (g i) μ) :
    MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MeasureTheory.integrable_zero ℝ ℝ μ
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (g a) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [show (fun x : ℝ => ∑ i ∈ insert a s, g i x)
          = fun x : ℝ => g a x + ∑ i ∈ s, g i x from by
        funext x; rw [Finset.sum_insert ha]]
      exact h1.add h2

/-! ## Integrability of the individual summands of the level-4 integrand -/

private lemma integrableOn_if_mixed (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      Work.Spaces.Iθ := by
  by_cases h : 1 ≤ i ∧ i + j ≤ 4
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 from by
      funext θ; rw [if_pos h]]
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      (Work.FTS.GalBasis.cc.aesm_slice_mixed_Wt_sq hF α j i hz) ?_
    rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j h.1 (by omega)
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [if_neg h]]
    exact MeasureTheory.integrableOn_zero

/-! ## The target -/


end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzNoTraces =====
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

/-! ## Integrability of a finite sum of integrable functions -/

private lemma integrable_finsetSum_nt {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ} (h : ∀ i ∈ s, MeasureTheory.Integrable (g i) μ) :
    MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MeasureTheory.integrable_zero ℝ ℝ μ
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (g a) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [show (fun x : ℝ => ∑ i ∈ insert a s, g i x)
          = fun x : ℝ => g a x + ∑ i ∈ s, g i x from by
        funext x; rw [Finset.sum_insert ha]]
      exact h1.add h2

private lemma integrableOn_if_mixed_nt (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      Work.Spaces.Iθ := by
  by_cases h : 1 ≤ i ∧ i + j ≤ 4
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 from by
      funext θ; rw [if_pos h]]
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      (Work.FTS.GalBasis.cc.aesm_slice_mixed_Wt_sq hF α j i hz) ?_
    rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j h.1 (by omega)
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [if_neg h]]
    exact MeasureTheory.integrableOn_zero

/-! ## The `z`-slots, without traces -/

/-- **The `z`-slots of the level-`4` integrand, per `z`, with no boundary-trace hypothesis.** -/
theorem HkIntegrand_zslot_perz_le_noTraces :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      ∀ i : ℕ, i ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
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
      exact Work.FTS.StrongEps.E5Aux.zslot_window_perz α hF 6 i (by omega) hzpos hR hσθ hσint
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

/-! ## The level-`4` per-`z` bound, without traces -/

/-- **The per-`z` bound of the level-`4` `ℋ`-integrand, with no boundary-trace hypothesis.** -/
theorem HkIntegrand_perz_le_noTraces :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
      α ∈ Set.Ioc 0 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
  obtain ⟨Cz, hCzpos, hCz⟩ := HkIntegrand_zslot_perz_le_noTraces
  obtain ⟨Cm, hCmpos, hCm⟩ := Work.FTS.StrongEps.E5Aux.mixed_slot_perz_le
  refine ⟨5 * Cz + 25 * Cm, by positivity, ?_⟩
  intro α f hα hreg hmem6 z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 4 (by norm_num) hmem6
  have hXsq : Work.Spaces.HkSq α 6 f ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
    have h2 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
    have h3 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have h4 : Work.FTS.StrongGlobal.Xn6 α f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
    rw [h4]
    nlinarith [Real.sq_sqrt h2, h3, h2]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate case `z = 0`
    subst hz0
    have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f 0 θ) = 0 := by
      rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f 0 θ) = fun _ => (0 : ℝ) from
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α 4 f θ]
      simp
    rw [hzero]
    have hw0 : (Work.Spaces.w 0) ^ 2 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0]
    have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hcoef : 0 < 5 * Cz + 25 * Cm := by positivity
    nlinarith [hX0]
  · -- the main case `z > 0`
    have hPint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum_nt _ (fun i hi => Work.FTS.EllipticEst.integrableOn_zSummand α 4 hreg
        hmem4 i (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))
    have hMint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum_nt _
        (fun i _ => integrable_finsetSum_nt _
          (fun j _ => integrableOn_if_mixed_nt α hreg hmem4 i j hzpos))
    have hdef : (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        = fun θ : ℝ => (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      funext θ; rw [Work.Spaces.HkIntegrand]
    rw [hdef, MeasureTheory.integral_add hPint hMint]
    -- the bound for the pure-`z` part
    have hPbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (Cz * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hreg hmem4 i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))]
      calc ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 5, (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) :=
            Finset.sum_le_sum fun i hi => hCz α hαI hreg hmem6 i
              (by rw [Finset.mem_range] at hi; omega) z hz
        _ = 5 * (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    -- the bound for the mixed part
    have hMbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun i _ =>
        integrable_finsetSum_nt _ (fun j _ => integrableOn_if_mixed_nt α hreg hmem4 i j hzpos))]
      calc ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range 5, (5 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
              * Work.Spaces.HkSq α 6 f)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun j _ =>
              integrableOn_if_mixed_nt α hreg hmem4 i j hzpos)]
            calc ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ,
                    (if 1 ≤ i ∧ i + j ≤ 4
                      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
                ≤ ∑ _j ∈ Finset.range 5, (Cm * (1 + (Work.Spaces.w z) ^ 2)
                    * Work.Spaces.HkSq α 6 f) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  by_cases hij : 1 ≤ i ∧ i + j ≤ 4
                  · simp only [if_pos hij]
                    exact hCm α hαI hreg hmem6 i j hij.1 (by omega) hzpos
                  · simp only [if_neg hij]
                    have h1 : 0 ≤ Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f := by
                      have := Work.Spaces.HkSq_nonneg α 6 f
                      positivity
                    simpa using h1
              _ = 5 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    refine le_trans (add_le_add hPbound hMbound) ?_
    have hPnn : 0 ≤ (1 : ℝ) + (Work.Spaces.w z) ^ 2 := by positivity
    have hX2nn : 0 ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := sq_nonneg _
    have hkey : 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f)
        ≤ 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
      have h1 : Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f
          ≤ Cm * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 :=
        mul_le_mul_of_nonneg_left hXsq (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hsum : 5 * (Cz * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2)
        + 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2)
        = (5 * Cz + 25 * Cm) * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by ring
    exact le_trans (add_le_add le_rfl hkey) (le_of_eq hsum)

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.Hk5SlotTriangle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Elementary tools -/

/-- The Euclidean inequality for two finite sums of squares:

  `√(∑ᵢ (xᵢ + yᵢ)²) ≤ √(∑ᵢ xᵢ²) + √(∑ᵢ yᵢ²)`.

It is the discrete Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` followed by
`Real.sqrt_le_sqrt`. -/
theorem hk5_sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2) := by
  have hA : 0 ≤ ∑ i ∈ s, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i ∈ s, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCS : (∑ i ∈ s, x i * y i) ^ 2 ≤ (∑ i ∈ s, x i ^ 2) * (∑ i ∈ s, y i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s x y
  have hC : ∑ i ∈ s, x i * y i
      ≤ Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, y i ^ 2) := by
    refine le_trans (Real.le_sqrt_of_sq_le hCS) ?_
    rw [Real.sqrt_mul hA]
  have hsum : ∑ i ∈ s, (x i + y i) ^ 2
      = (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, x i * y i) + ∑ i ∈ s, y i ^ 2 := by
    have h1 : ∑ i ∈ s, (x i + y i) ^ 2
        = ∑ i ∈ s, (x i ^ 2 + 2 * (x i * y i) + y i ^ 2) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hkey : (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, x i * y i) + ∑ i ∈ s, y i ^ 2
      ≤ (Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2)) ^ 2 := by
    have hsqA := Real.sq_sqrt hA
    have hsqB := Real.sq_sqrt hB
    nlinarith [hC, Real.sqrt_nonneg (∑ i ∈ s, x i ^ 2),
      Real.sqrt_nonneg (∑ i ∈ s, y i ^ 2)]
  rw [hsum]
  calc Real.sqrt ((∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, x i * y i) + ∑ i ∈ s, y i ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i ∈ s, x i ^ 2)
          + Real.sqrt (∑ i ∈ s, y i ^ 2)) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt (∑ i ∈ s, x i ^ 2) + Real.sqrt (∑ i ∈ s, y i ^ 2) :=
        Real.sqrt_sq (by positivity)




/-! ## The slot vector of the `ℋ^k`-integrand -/

/-- The weighted `D_z`-slot of order `i`. -/
def hk5_slotZ (h : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) : ℝ :=
  Work.Spaces.DzIter i h z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))

/-- The mixed slot `D_z^{p.2} D_θ^{p.1}`, set to `0` outside the range `1 ≤ i`, `i + j ≤ k`. -/
def hk5_slotM (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    then Work.Spaces.mixed p.2 p.1 h z θ * Work.Spaces.Wt α z θ else 0

/-- The slot vector of the `ℋ^k`-integrand. -/
def hk5_slotVec (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1))) → ℝ
  | Sum.inl i => hk5_slotZ h z θ (i : ℕ)
  | Sum.inr p => hk5_slotM α k h z θ ((p.1 : ℕ), (p.2 : ℕ))

/-- The `ℋ^k`-integrand is the sum of the squares of the entries of the slot vector. -/
theorem hk5_HkIntegrand_eq_sum_slotVec (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k h z θ
      = ∑ x : Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1)), (hk5_slotVec α k h z θ x) ^ 2 := by
  rw [Work.Spaces.HkIntegrand, Fintype.sum_sum_type]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (Work.Spaces.DzIter i h z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) (k + 1)]
    rfl
  · rw [Fintype.sum_prod_type]
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) (k + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => (if 1 ≤ (i : ℕ) ∧ (i : ℕ) + j ≤ k
      then (Work.Spaces.mixed j (i : ℕ) h z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) (k + 1)]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hc : 1 ≤ (i : ℕ) ∧ (i : ℕ) + (y : ℕ) ≤ k
    · simp only [hk5_slotVec, hk5_slotM, if_pos hc]
    · simp only [hk5_slotVec, hk5_slotM, if_neg hc]
      ring

/-- On the open quadrant the slot vector of a sum is the sum of the slot vectors. -/
theorem hk5_slotVec_add (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2)
    (x : Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1))) :
    hk5_slotVec α k (fun z θ => f z θ + g z θ) z θ x
      = hk5_slotVec α k f z θ x + hk5_slotVec α k g z θ x := by
  cases x with
  | inl i =>
      simp only [hk5_slotVec, hk5_slotZ]
      rw [Work.FTS.EllipticEst.SmoothOpen.DzIter_add hf hg (i : ℕ) z θ hz h1 h2]
      ring
  | inr p =>
      simp only [hk5_slotVec, hk5_slotM]
      by_cases hc : 1 ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) + (p.2 : ℕ) ≤ k
      · simp only [if_pos hc]
        rw [Work.FTS.EllipticEst.SmoothOpen.mixed_add hf hg (p.2 : ℕ) (p.1 : ℕ) z θ hz h1 h2]
        ring
      · simp only [if_neg hc]
        ring

/-- **The pointwise triangle inequality for the `ℋ^k`-integrand** on the open quadrant. -/
theorem hk5_sqrt_HkIntegrand_add_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
          + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) := by
  intro z θ hz h1 h2
  rw [hk5_HkIntegrand_eq_sum_slotVec α k (fun z θ => f z θ + g z θ) z θ,
    hk5_HkIntegrand_eq_sum_slotVec α k f z θ,
    hk5_HkIntegrand_eq_sum_slotVec α k g z θ]
  have hsum : (∑ x : Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1)),
        (hk5_slotVec α k (fun z θ => f z θ + g z θ) z θ x) ^ 2)
      = ∑ x : Fin (k + 1) ⊕ (Fin (k + 1) × Fin (k + 1)),
        (hk5_slotVec α k f z θ x + hk5_slotVec α k g z θ x) ^ 2 :=
    Finset.sum_congr rfl fun x _ => by rw [hk5_slotVec_add α k hf hg hz h1 h2 x]
  rw [hsum]
  exact hk5_sqrt_sum_sq_add_le Finset.univ (hk5_slotVec α k f z θ) (hk5_slotVec α k g z θ)



/-! ## The finite-sum upgrade -/




end Work.FTS.GalFields.Norm
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.RadA4.Own =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm.RadA4

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `(0,∞)`-form of the order-`4` integrability -/


/-! ## Integrability of the order-`4` radial slot of `radA α f` -/


/-! ## The projecter profile's slot sum at order `5` -/

/-- **The `α`-independent order-`5` slot sum of `ampB`.**  `ampB β z = 2z²/(1+z)³` does not
depend on `β` at all, so the value of the slot sum at `β = 1`, increased by `1`, is a uniform
bound.  (No integrability input is needed: the two integrals are *equal* because the
integrands agree, and the bound is therefore trivial.) -/
theorem ampB_slotSum5_bound : ∃ Kb : ℝ, 0 < Kb ∧ ∀ β : ℝ, 0 < β → β ≤ 1 →
    (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB β) z) ^ 2
        * (Work.Spaces.w z) ^ 2)
      ≤ Kb := by
  refine ⟨(∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB 1) z) ^ 2
        * (Work.Spaces.w z) ^ 2) + 1, ?_, ?_⟩
  · have hnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB 1) z) ^ 2
          * (Work.Spaces.w z) ^ 2 :=
      integral_nonneg (fun z => Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    linarith
  intro β _hβ _hβ1
  have hfunβ : Work.FTS.CoercivityFix.Transfer.ampB β
      = Work.FTS.CoercivityFix.Transfer.ampB 1 := by
    funext z
    simp only [Work.FTS.CoercivityFix.Transfer.ampB]
  rw [hfunβ]
  linarith

/-! ## The level-`4` assembly -/


end Work.FTS.GalFields.Norm.RadA4
end
end
-- ===== merged: Submission.Work.FTS.GalLimit.Closure.phi_HQo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalLimit.Closure

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Globally `C^∞` functions: `SmoothOpen` and `SmoothQuad` -/



/-! ## Vanishing of the iterated derivatives on a neighbourhood

A function which vanishes in a (one-sided-agnostic) neighbourhood of the foot of the derivative
has vanishing derivative there; iterating, this is the only smoothness input needed to transport a
support condition to `D_z^j D_θ^i f`. -/

/-- If `f · θ` vanishes on a neighbourhood `U` of `z`, then every `D_z`-iterate of `f` vanishes
at `(z,θ)`. -/
theorem DzIter_eq_zero_of_isOpen_z {f : ℝ → ℝ → ℝ} :
    ∀ (k : ℕ) (U : Set ℝ) (z θ : ℝ), IsOpen U → z ∈ U → (∀ z' ∈ U, f z' θ = 0) →
      Work.Spaces.DzIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => intro U z θ _ hzU h; exact h z hzU
  | succ k ih =>
      intro U z θ hU hzU h
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      have hp : Work.Spaces.pz (Work.Spaces.DzIter k f) z θ = 0 := by
        rw [Work.Spaces.pz]
        have hev : (fun z' => Work.Spaces.DzIter k f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [hU.mem_nhds hzU] with z' hz'
          exact ih U z' θ hU hz' h
        rw [hev.deriv_eq, deriv_const]
      rw [hp, mul_zero]

/-- If `f z ·` vanishes on a neighbourhood `U` of `θ`, then every `D_θ`-iterate of `f` vanishes
at `(z,θ)`. -/
theorem DthIter_eq_zero_of_isOpen_th {f : ℝ → ℝ → ℝ} :
    ∀ (k : ℕ) (U : Set ℝ) (z θ : ℝ), IsOpen U → θ ∈ U → (∀ θ' ∈ U, f z θ' = 0) →
      Work.Spaces.DthIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => intro U z θ _ hθU h; exact h θ hθU
  | succ k ih =>
      intro U z θ hU hθU h
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      have hp : Work.Spaces.pth (Work.Spaces.DthIter k f) z θ = 0 := by
        rw [Work.Spaces.pth]
        have hev : (fun θ' => Work.Spaces.DthIter k f z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
          filter_upwards [hU.mem_nhds hθU] with θ' hθ'
          exact ih U z θ' hU hθ' h
        rw [hev.deriv_eq, deriv_const]
      rw [hp, mul_zero]

/-! ## Support of the iterated derivatives

`SuppIn f a b δ` is `Work.FTS.GalBasis.SuppIn`: `f` vanishes off the closed box
`[a,b] × [δ, π/2-δ]`.  It is exactly the support clause of `CcBasis`. -/

/-- Every `D_z`-iterate of a function supported in `[a,b] × [δ,π/2-δ]` vanishes off that box. -/
theorem dzIter_eq_zero_of_suppIn {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0)
    {z θ : ℝ} (h : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) (k : ℕ) :
    Work.Spaces.DzIter k f z θ = 0 := by
  rcases h with h | h
  · exact DzIter_eq_zero_of_isOpen_z k _ z θ isClosed_Icc.isOpen_compl h
      (fun z' hz' => hSupp z' θ (Or.inl hz'))
  · exact DzIter_eq_zero_of_isOpen_z k Set.univ z θ isOpen_univ (Set.mem_univ z)
      (fun z' _ => hSupp z' θ (Or.inr h))

/-- Every mixed derivative `D_z^j D_θ^i` of a function supported in `[a,b] × [δ,π/2-δ]` vanishes
off that box. -/
theorem mixed_eq_zero_of_suppIn {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0)
    {z θ : ℝ} (h : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) (j i : ℕ) :
    Work.Spaces.mixed j i f z θ = 0 := by
  rw [Work.Spaces.mixed]
  rcases h with h | h
  · -- `z` outside: `f` vanishes on the whole `θ`-line through `z'`, for every `z'` off the box
    refine DzIter_eq_zero_of_isOpen_z j _ z θ isClosed_Icc.isOpen_compl h (fun z' hz' => ?_)
    exact DthIter_eq_zero_of_isOpen_th i Set.univ z' θ isOpen_univ (Set.mem_univ θ)
      (fun θ' _ => hSupp z' θ' (Or.inl hz'))
  · refine DzIter_eq_zero_of_isOpen_z j Set.univ z θ isOpen_univ (Set.mem_univ z)
      (fun z' _ => DthIter_eq_zero_of_isOpen_th i _ z' θ isClosed_Icc.isOpen_compl h
        (fun θ' hθ' => hSupp z' θ' (Or.inr hθ')))

/-- The `ℋ^k`-integrand of a function supported in `[a,b] × [δ,π/2-δ]` vanishes off that box
(every summand carries a derivative factor). -/
theorem HkIntegrand_eq_zero_of_suppIn (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0)
    {z θ : ℝ} (h : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ *
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [dzIter_eq_zero_of_suppIn hSupp h i]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [ite_eq_left hc, mixed_eq_zero_of_suppIn hSupp h j i]; ring
      · rw [ite_eq_right hc]
  rw [Work.Spaces.HkIntegrand, h1, h2, add_zero]

/-! ## The pointwise bound on the box -/

/-- On the whole plane, the `ℋ^k`-integrand of a function supported in `[a,b] × [δ,π/2-δ]`
(`0 < a`, `0 < δ`, `f` smooth on the open quadrant) is bounded by a constant.  Off the box it
vanishes, and on the box it is continuous on a compact set: there `z ≥ a > 0` and
`sin(2δ) ≤ sin(2θ)`, so the weights `w` and `sin(2θ)^{-η/2}`, `sin(2θ)^{-γ/2}` are finite and
continuous. -/
theorem exists_bound_HkIntegrand_of_suppIn (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hsmooth : Work.FTS.LocData.SmoothQuad f)
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z θ : ℝ, Work.Spaces.HkIntegrand α k f z θ ≤ M := by
  have hcont := Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k f hsmooth
  have hbox_sub : Set.Icc a b ×ˢ Set.Icc δ (π / 2 - δ) ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) := by
    intro p hp
    rw [Set.mem_prod] at hp
    obtain ⟨hz, hθ⟩ := hp
    rw [Set.mem_Icc] at hz hθ
    rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨by linarith [hz.1], by linarith [hθ.1], by linarith [hθ.2]⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image (hcont.mono hbox_sub)
  have hMbdd : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc δ (π / 2 - δ),
      Work.Spaces.HkIntegrand α k f p.1 p.2 ≤ M := fun p hp =>
    hM (Set.mem_image_of_mem (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) hp)
  refine ⟨max M 0, le_max_right _ _, fun z θ => ?_⟩
  by_cases hmem : (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc δ (π / 2 - δ)
  · exact le_trans (hMbdd (z, θ) hmem) (le_max_left _ _)
  · have hoff : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ) := by
      by_contra hc
      push Not at hc
      exact hmem (Set.mem_prod.mpr ⟨hc.1, hc.2⟩)
    rw [HkIntegrand_eq_zero_of_suppIn α k hSupp hoff]
    exact le_max_right _ _

/-! ## Membership in `ℋ^k` -/

/-- **A smooth function supported in a compact box strictly inside the open quadrant lies in
`ℋ^k`, for every `α`.**  Domination by the global constant on the box `[0,b] × [0,π/2]`, which is
integrable in `z` because it is supported in the finite-measure set `[0,b]`. -/
theorem hkMem_of_suppIn (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hsmooth : Work.FTS.LocData.SmoothQuad f)
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0) :
    Work.Spaces.HkMem α k f := by
  obtain ⟨M, hMnn, hM⟩ := exists_bound_HkIntegrand_of_suppIn α k ha hδ hsmooth hSupp
  have hbb : (0 : ℝ) < b := lt_trans ha hab
  -- the majorant: the constant `M` on the box `[0,b] × [0,π/2]`, zero beyond
  set Maj : ℝ → ℝ → ℝ := fun z _ => if z ∈ Set.Icc (0 : ℝ) b then M else 0 with hMaj
  have hunfold : ∀ z θ : ℝ, Maj z θ = if z ∈ Set.Icc (0 : ℝ) b then M else 0 := by
    intro z θ; simp only [hMaj]
  have hIntθ : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Maj z θ)
      = if z ∈ Set.Icc (0 : ℝ) b then M * (π / 2) else 0 := by
    intro z
    by_cases hz : z ∈ Set.Icc (0 : ℝ) b
    · have hfun : (fun θ : ℝ => Maj z θ) = fun _ => M := by
        funext θ; rw [hunfold z θ, ite_eq_left hz]
      rw [hfun, setIntegral_const, Work.Spaces.volume_real_Iθ, ite_eq_left hz, smul_eq_mul]
      ring
    · have hfun : (fun θ : ℝ => Maj z θ) = fun _ => (0 : ℝ) := by
        funext θ; rw [hunfold z θ, ite_eq_right hz]
      rw [hfun, integral_zero, ite_eq_right hz]
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Maj z θ) Work.Spaces.Iθ := by
    intro z hz
    by_cases hb : z ∈ Set.Icc (0 : ℝ) b
    · have hfun : (fun θ : ℝ => Maj z θ) = fun _ => M := by
        funext θ; rw [hunfold z θ, ite_eq_left hb]
      rw [hfun]
      exact integrableOn_const (C := M) Work.Spaces.volume_Iθ_lt_top.ne
    · have hfun : (fun θ : ℝ => Maj z θ) = fun _ => (0 : ℝ) := by
        funext θ; rw [hunfold z θ, ite_eq_right hb]
      rw [hfun]
      exact integrableOn_zero
  have hzint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Maj z θ) Work.Spaces.Iz := by
    rw [show (fun z => ∫ θ in Work.Spaces.Iθ, Maj z θ)
        = fun z => if z ∈ Set.Icc (0 : ℝ) b then M * (π / 2) else 0 from funext hIntθ]
    have h1 : IntegrableOn (fun z => if z ∈ Set.Icc (0 : ℝ) b then M * (π / 2) else 0)
        (Set.Icc 0 b) :=
      IntegrableOn.congr_fun
        (integrableOn_const (C := M * (π / 2))
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        (fun z hz => by rw [ite_eq_left hz]) measurableSet_Icc
    have h2 : IntegrableOn (fun z => if z ∈ Set.Icc (0 : ℝ) b then M * (π / 2) else 0)
        (Set.Ioi b) :=
      IntegrableOn.congr_fun integrableOn_zero (fun z hz => by
        have hz' : ¬ (z ∈ Set.Icc (0 : ℝ) b) := fun hc => absurd hc.2 (not_le.mpr hz)
        rw [ite_eq_right hz']) measurableSet_Ioi
    refine (h1.union h2).mono_set ?_
    intro z hz
    by_cases h : z ≤ b
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr (lt_of_not_ge h)
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k f hsmooth) hslice hzint ?_
  intro z hz θ hθ
  by_cases hb : z ∈ Set.Icc (0 : ℝ) b
  · rw [hunfold z θ, ite_eq_left hb]
    exact hM z θ
  · have hzb : b < z := by
      rcases lt_or_ge b z with h | h
      · exact h
      · exact absurd ⟨hz, h⟩ hb
    have hoff : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ) :=
      Or.inl fun hc => absurd hc.2 (not_le.mpr hzb)
    rw [HkIntegrand_eq_zero_of_suppIn α k hSupp hoff, hunfold z θ, ite_eq_right hb]

/-! ## The target -/


end Work.FTS.GalLimit.Closure
end
end
-- ===== merged: Submission.Work.FTS.GalLimit.GalWeak.bslOp_galPsi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalLimit.GalWeak

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Homogeneity of the slots of `bslOp` in a constant -/

/-- `∂_z` commutes with multiplication by a constant. -/
lemma pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.pz f z θ := by
  simp only [Work.Spaces.pz]
  exact deriv_const_mul_field c

/-- Function-level form of `pz_const_mul`. -/
lemma pz_const_mul_fun (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z' θ' => c * f z' θ') = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ; exact pz_const_mul c f z θ

/-- `∂_θ` commutes with multiplication by a constant. -/
lemma pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.pth f z θ := by
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

/-- Function-level form of `pth_const_mul`. -/
lemma pth_const_mul_fun (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z' θ' => c * f z' θ') = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ; exact pth_const_mul c f z θ

/-- `∂_z^k` commutes with multiplication by a constant. -/
lemma pzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter n f z θ := by
  induction n with
  | zero => funext z θ; simp [Work.Spaces.pzIter]
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ, pz_const_mul_fun]

/-- `∂_θ^k` commutes with multiplication by a constant. -/
lemma pthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pthIter n (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pthIter n f z θ := by
  induction n with
  | zero => funext z θ; simp [Work.Spaces.pthIter]
  | succ n ih =>
    rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ, pth_const_mul_fun]

/-- `L₀` is homogeneous in a constant: `L₀ (c · f) = c · L₀ f`. -/
lemma Lzero_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun z θ => c * f z θ) z θ = c * Work.Elliptic.Lzero f z θ := by
  have h2 : Work.Spaces.pthIter 2 (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.pthIter 2 f z θ := congrFun (congrFun (pthIter_const_mul c f 2) z) θ
  have htan : (fun z' θ' => Real.tan θ' * (c * f z' θ'))
      = (fun z' θ' => c * (Real.tan θ' * f z' θ')) := by funext z' θ'; ring
  have h3 : Work.Spaces.pth (fun z' θ' => c * (Real.tan θ' * f z' θ')) z θ
      = c * Work.Spaces.pth (fun z' θ' => Real.tan θ' * f z' θ') z θ :=
    congrFun (congrFun (pth_const_mul_fun c (fun z' θ' => Real.tan θ' * f z' θ')) z) θ
  simp only [Work.Elliptic.Lzero]
  rw [h2, htan, h3]
  ring

/-- `bslOp` is homogeneous in a constant.  Unlike additivity this needs **no** differentiability
hypothesis: `deriv_const_mul_field` is unconditional (at a non-differentiable point both sides
vanish). -/
lemma bslOp_const_mul (α c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp α (fun z θ => c * f z θ) z θ
      = c * Work.Elliptic.bslOp α f z θ := by
  have h2 := congrFun (congrFun (pzIter_const_mul c f 2) z) θ
  have h1 := pz_const_mul c f z θ
  have hL := Lzero_const_mul c f z θ
  simp only [Work.Elliptic.bslOp_apply]
  rw [h2, h1, hL]
  ring

/-- `bslOp` kills the zero function. -/
lemma bslOp_zero (α z θ : ℝ) :
    Work.Elliptic.bslOp α (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, Work.Spaces.pzIter,
    Work.Spaces.pz, Work.Spaces.pthIter, Work.Spaces.pth]

/-! ## `C²` bookkeeping for constant multiples and finite sums -/

/-- A constant multiple of a jointly `C²` function is jointly `C²`. -/
lemma contDiffAt_uncurry_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ 2 (Function.uncurry (fun z' θ' => c * f z' θ')) (z, θ) := by
  have key : Function.uncurry (fun z' θ' => c * f z' θ')
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; simp only [Function.uncurry]
  rw [key]
  exact contDiffAt_const.mul hf


/-! ## Additivity of `bslOp` over a finite sum -/


/-! ## The Galerkin superposition solves the summed equation -/


end Work.FTS.GalLimit.GalWeak
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Construction

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# Row 1 of the primed §8 table: the `F_*`-quadratic block `N₀₁ + N₀₂`

`N0fix α = N₀₁ + N₀₂` is *unconditional*: it involves only `F_*`, never the data `g, Φs, Φg`.
On the open quadrant it collapses to the separable datum

  `F(z,θ) = Kfac α · rhoR z · psiA α θ`,
  `Kfac α = 8α²/c(α)`,  `rhoR z = z²/(1+z)⁴`,  `psiA α θ = c2m(θ)·Γ(α,θ)`

(`Work.Construction.N0_first_two_eq'`), and the two conjuncts of the row are

* the `ℋ⁴`-honesty `HkMem α 4 (N0fix α)`: the `ℋ⁴`-integrand of `F` is dominated by the
  separable majorant `Kfac α²·(M/(1+z)²)²·gammaAngMaj α D θ`, where `M` and `D` price the radial jets
  of `rhoR` (`Work.Construction.H4N_GammaTerm_rho_bound`) and the angular jets of `psiA`
  (`Work.Construction.H4N_GammaTerm_Lop_bound`); the majorant is integrable because
  `sin(2θ)^{−η}`, `sin(2θ)^{2α/3−γ}` are integrable on `Iθ` (`Work.Spaces.sin_two_rpow`) and
  `(1+z)^{−4}` is integrable on `Iz` (`Work.Elliptic.WtoH_IntZ`), so
  `Work.FTS.LocData.HkMem_of_majorant` applies; the transfer from `F` to `N0fix α` is the
  a.e.-congruence on the open quadrant (`Work.Construction.N0_first_two_eq'` via
  `HkMem_congr_Q0`);
* the norm bound `Xn α (N0fix α) ≤ K·α²`, which is `RowsN0Aux.N0fix_bound` verbatim.

Neither conjunct uses `N4Norm'`, `N4Extra'` or the data `g, Φs, Φg`: the constant `K` is the one
of `RowsN0Aux.N0fix_bound`.

The proof of the pointwise domination is the estimate `hpt` of
`Work.Construction.H4N_GammaTerm_le_of_cores`, re-exposed here as the standalone lemma
`HkIntegrand_sep_le` (with the two cores as hypotheses, so that the constants `M`, `D` are the
existential ones of `H4N_GammaTerm_rho_bound` / `H4N_GammaTerm_Lop_bound`).
-/

/-- The angular majorant of the separable datum `F = Kfac α · rhoR · psiA α`: the two angular
weights of the paper's `ℋ⁴`-integrand, with the angular jet constant `D`. -/
noncomputable def gammaAngMaj (α D θ : ℝ) : ℝ :=
  (20 + 50 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + 50 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)

/-- **`N0fix α` is the separable datum `Kfac α · rhoR · psiA α` on the open quadrant**
(`Work.Construction.N0_first_two_eq'`). -/
private theorem N0fix_eq_sep (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N0fix α z θ
        = Work.Construction.Kfac α * Work.Construction.rhoR z * Work.Construction.psiA α θ := by
  intro z θ hz hθ hθ2
  rw [Work.FTS.Nonlin.N0fix]
  simp only [Work.Construction.N01, Work.Construction.N02]
  rw [show (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + -Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ from by ring]
  rw [Work.Construction.N0_first_two_eq' hα hα1 hz.le ⟨hθ.le, hθ2.le⟩]
  simp only [Work.Construction.Kfac, Work.Construction.rhoR, Work.Construction.psiA]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

/-- `F` is `C⁴` on the open quadrant: the product of the smooth radial factor
`Kfac α·rhoR` (a rational function whose only pole is at `z = -1`) and the smooth angular
factor `psiA α = c2m·Γ` (`Γ = (sinθcos²θ)^{α/3}` is smooth on the quadrant). -/
private theorem contDiffOn_uncurry_sep (α : ℝ) :
    ContDiffOn ℝ (4 : ℕ)
      (Function.uncurry (Work.Construction.sepF
        (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
        (Work.Construction.psiA α))) Work.FTS.OpenPkg.Q0 := by
  have hrad : ContDiffOn ℝ (4 : ℕ)
      (fun p : ℝ × ℝ => Work.Construction.Kfac α * Work.Construction.rhoR p.1)
      Work.FTS.OpenPkg.Q0 := by
    have h1 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => p.1 ^ 2)
        Work.FTS.OpenPkg.Q0 := contDiffOn_fst.pow 2
    have h2 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => (1 + p.1) ^ 4)
        Work.FTS.OpenPkg.Q0 := (contDiffOn_const.add contDiffOn_fst).pow 4
    have h3 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => p.1 ^ 2 / (1 + p.1) ^ 4)
        Work.FTS.OpenPkg.Q0 :=
      h1.div h2 (fun p hp => pow_ne_zero 4 (ne_of_gt (by
        have hmem : (0 : ℝ) < p.1 := by
          rw [Work.FTS.OpenPkg.Q0] at hp; exact hp.1
        linarith)))
    have h4 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Work.Construction.rhoR p.1)
        Work.FTS.OpenPkg.Q0 := by
      simpa only [Work.Construction.rhoR] using h3
    exact contDiffOn_const.mul h4
  have hang : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Work.Construction.psiA α p.2)
      Work.FTS.OpenPkg.Q0 := by
    have hc2m : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
        Work.FTS.OpenPkg.Q0 := by
      have h1 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Real.cos (2 * p.2))
          Work.FTS.OpenPkg.Q0 :=
        (((Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)).contDiffOn).of_le le_top)
      have h2 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
          Work.FTS.OpenPkg.Q0 :=
        ((((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn).of_le le_top)
      simpa only [Work.Construction.c2m] using h1.sub h2
    have hGam : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
        Work.FTS.OpenPkg.Q0 := Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 4
    exact hc2m.mul hGam
  refine (hrad.mul hang).congr ?_
  intro p _
  rfl

/-- `z ↦ (1+z)^{-4}` is integrable on `Iz` (the bound `(1+z)^{-2} ≤ 1` on `Iz` and
`Work.Elliptic.WtoH_IntZ`). -/
private theorem integrableOn_inv_one_add_pow_four :
    IntegrableOn (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2) Work.Spaces.Iz := by
  refine Work.Elliptic.WtoH_IntZ.1.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    have h1 : (0 : ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
    have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [h1, h2]

/-- The angular majorant `gammaAngMaj α D` is integrable on `Iθ`. -/
private theorem integrableOn_gammaAngMaj (α D : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (gammaAngMaj α D) Work.Spaces.Iθ := by
  have hη1 : -1 < -(Work.Spaces.eta) := by
    have := Work.Spaces.eta_lt_one; linarith
  have hη2 : -(Work.Spaces.eta) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  have hg1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hg2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by
    rw [Work.Spaces.gam]; linarith
  have hunfold : gammaAngMaj α D = fun θ => (20 + 50 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 50 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := rfl
  rw [hunfold]
  exact ((Work.Spaces.sin_two_rpow _ hη1 hη2).1.const_mul _).add
    ((Work.Spaces.sin_two_rpow _ hg1 hg2).1.const_mul _)

/-- **The pointwise domination of the `ℋ⁴`-integrand of the separable `Γ`-term.**  The analytic
core of row 1: given the radial jet bound `hMr` (priced by
`Work.Construction.H4N_GammaTerm_rho_bound`) and the angular jet bound `hDl` (priced by
`Work.Construction.H4N_GammaTerm_Lop_bound`), the `ℋ⁴`-integrand of
`F = sepF (Kfac α·rhoR) (psiA α)` is dominated by the separable majorant
`(Kfac α)²·(M/(1+z)²)²·gammaAngMaj α D θ`.

This is the estimate `hpt` of `Work.Construction.H4N_GammaTerm_le_of_cores`, re-exposed as a
standalone lemma with the two cores as hypotheses. -/
theorem HkIntegrand_sep_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D)
    (hMr : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z|
        ≤ M / (1 + z) ^ 2)
    (hDl : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
        ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4
          (Work.Construction.sepF (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
            (Work.Construction.psiA α)) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj α D θ := by
  set Kf : ℝ := Work.Construction.Kfac α with hKfdef
  have hDnn : 0 ≤ D := hD.le
  set F : ℝ → ℝ → ℝ := Work.Construction.sepF (fun z => Kf * Work.Construction.rhoR z)
    (Work.Construction.psiA α) with hFdef
  have hFsep : F = Work.Construction.sepF (fun z => Kf * Work.Construction.rhoR z)
      (Work.Construction.psiA α) := hFdef
  set Big : ℝ → ℝ := fun θ => (20 + 50 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 50 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) with hBigdef
  -- pointwise bound on the integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 F z θ
        ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ := by
    intro z hz θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := Work.Construction.sin_two_nonneg_of_mem_Iθ hθ
    have h1z : 0 < 1 + z := by have hz0 : (0:ℝ) ≤ z := hz; linarith
    rcases em (θ ∈ Set.Ioo 0 (π / 2)) with hθi | hθi
    · -- interior: use the two cores termwise
      have hbnd : ∀ j : ℕ, j ≤ 4 →
          ((Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2 ≤ (M / (1 + z) ^ 2) ^ 2 := by
        intro j hj
        have hb := hMr j hj z hz
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0:ℝ) ≤ M / (1 + z) ^ 2)]
        exact hb
      have hψ2 : (Work.Construction.psiA α θ) ^ 2 ≤ 4 := by
        have h := mul_self_le_mul_self (abs_nonneg (Work.Construction.psiA α θ)) (Work.Construction.psiA_abs_le_two hα hθ)
        have h2 := sq_abs (Work.Construction.psiA α θ)
        nlinarith [h, h2]
      have hpure : ∀ i : ℕ, i ≤ 4 →
          (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        intro i hi
        have hsep : Work.Spaces.DzIter i F z θ
            = Kf * (Work.Spaces.Zop^[i] Work.Construction.rhoR) z * Work.Construction.psiA α θ := by
          rw [hFsep, Work.Construction.sepF_DzIter, Work.Construction.Zop_iter_const_mul, sepF]
        have hsq := hbnd i hi
        have hψs : (Kf * Work.Construction.psiA α θ) ^ 2 ≤ Kf ^ 2 * 4 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left hψ2 (sq_nonneg Kf)
        calc (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = ((Work.Spaces.Zop^[i] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2
                * (Kf * Work.Construction.psiA α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
              rw [hsep]
              rw [Work.Elliptic.sq_mul_div_sin (z := z) (θ := θ)
                (a := Kf * (Work.Spaces.Zop^[i] Work.Construction.rhoR) z * Work.Construction.psiA α θ) hθ]
              ring
          _ ≤ (M / (1 + z) ^ 2) ^ 2 * (Kf ^ 2 * 4)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul hsq hψs (sq_nonneg _) (sq_nonneg _))
                (Real.rpow_nonneg hs0 _)
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hmixed : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
          (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
        intro i j hi hij
        have hsep : Work.Spaces.mixed j i F z θ
            = Kf * (Work.Spaces.Zop^[j] Work.Construction.rhoR) z * (Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ := by
          rw [hFsep, Work.Construction.sepF_mixed, Work.Construction.Zop_iter_const_mul, sepF]
        have hsq := hbnd j (by omega)
        have hcore := hDl i hi (by omega) θ hθi
        have hang := Work.Construction.mixed_angle_le hα hα1 hDnn hθ hcore
        calc (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
            = Kf ^ 2 * ((Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2
                * (((Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [hsep, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
              ring
          _ ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg Kf)) hang
                (by positivity) (by positivity)
      rw [Work.Spaces.HkIntegrand]
      have hZsum : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        calc ∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ ∑ _i ∈ Finset.range (4 + 1),
                (Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
              Finset.sum_le_sum fun i hi =>
                hpure i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          _ = 5 * (Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hMsum : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
        set Y : ℝ := Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) with hYdef
        have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
        calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), Y :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
                by_cases hc : 1 ≤ i ∧ i + j ≤ 4
                · rw [if_pos hc]; exact hmixed i j hc.1 hc.2
                · rw [if_neg hc]; exact hYnn
          _ = 25 * Y := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
              rw [hYdef]; ring
      calc ∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
            add_le_add hZsum hMsum
        _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ := by simp only [hBigdef]; ring
    · -- boundary: every term vanishes
      have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      rw [Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hs]
      have h0 : Big θ = 0 := by
        simp only [hBigdef, hs,
          Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : (-(Work.Spaces.eta)) ≠ 0),
          Real.zero_rpow (by rw [Work.Spaces.gam]; intro hh; linarith :
            (2 * α / 3 - Work.Spaces.gam α) ≠ 0)]
        ring
      rw [h0]; norm_num
  intro z hz θ hθ
  exact hpt z hz θ hθ

/-- **The `ℋ⁴`-honesty of `N0fix α`** (`0 < α ≤ 1`): transfer from the separable datum
`F = Kfac α · rhoR · psiA α`, whose `ℋ⁴`-integrand is dominated by the separable majorant, so
that `Work.FTS.LocData.HkMem_of_majorant` applies. -/
theorem HkMem_N0fix (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) := by
  obtain ⟨M, hM, hMr⟩ := Work.Construction.H4N_GammaTerm_rho_bound
  obtain ⟨D, hD, hDl⟩ := Work.Construction.H4N_GammaTerm_Lop_bound
  set F : ℝ → ℝ → ℝ := Work.Construction.sepF
    (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
    (Work.Construction.psiA α) with hF
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 F z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj α D θ := by
    intro z hz θ hθ
    rw [hF]
    exact HkIntegrand_sep_le α hα hα1 hM hD hMr (hDl α hα hα1) z hz θ hθ
  have hmem : Work.Spaces.HkMem α 4 F := by
    refine Work.FTS.LocData.HkMem_of_majorant α 4
      (M := fun z θ => (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj α D θ)
      ?_ ?_ ?_ ?_
    · exact Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 4) (k := 4) le_rfl
        (contDiffOn_uncurry_sep α)
    · intro z hz
      exact (integrableOn_gammaAngMaj α D hα hα1).const_mul _
    · have hbase : IntegrableOn (fun z : ℝ => ((Work.Construction.Kfac α) ^ 2 * M ^ 2
          * (∫ θ in Work.Spaces.Iθ, gammaAngMaj α D θ)) * (1 / (1 + z) ^ 2) ^ 2) Work.Spaces.Iz :=
        integrableOn_inv_one_add_pow_four.const_mul _
      refine hbase.congr_fun ?_ measurableSet_Ici
      intro z hz
      dsimp only
      rw [MeasureTheory.integral_const_mul]
      ring
    · intro z hz θ hθ
      exact hpt z hz θ hθ
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hmem ?_
  intro z hz θ hθ
  exact (N0fix_eq_sep α hα hα1 z θ hz hθ.1 hθ.2).symm


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow15T2Aux.Jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## The radial factor and its two pieces -/

/-- `u(z) = z/(1+z)`. -/
def u15 (z : ℝ) : ℝ := z / (1 + z)

/-- `k(z) = z/(1+z)²` (the kernel `Work.Spaces.hKer`). -/
def k15 (z : ℝ) : ℝ := z / (1 + z) ^ 2

/-- The radial factor of row 15: `ψ = u·k = z²/(1+z)³`. -/
def psi15 (z : ℝ) : ℝ := u15 z * k15 z

theorem psi15_eq (z : ℝ) : psi15 z = z ^ 2 / (1 + z) ^ 3 := by
  rw [psi15, u15, k15]
  rcases eq_or_ne (1 + z) 0 with h | h
  · have hz : z = -1 := by linarith
    subst hz
    norm_num
  · field_simp

theorem smoothOpen_u15 : Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => u15 z) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z / (1 + z)) (Set.Ioi 0) := by
    refine ContDiffOn.div contDiffOn_id (contDiffOn_const.add contDiffOn_id) ?_
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  have hfun : (fun z : ℝ => z / (1 + z)) = fun z : ℝ => u15 z := by
    funext z; rw [u15]
  rw [hfun] at h
  exact smoothOpen_z_only h

theorem smoothOpen_k15 : Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => k15 z) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) := by
    refine ContDiffOn.div contDiffOn_id ((contDiffOn_const.add contDiffOn_id).pow 2) ?_
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  have hfun : (fun z : ℝ => z / (1 + z) ^ 2) = fun z : ℝ => k15 z := by
    funext z; rw [k15]
  rw [hfun] at h
  exact smoothOpen_z_only h

theorem smoothOpen_psi15 : Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => psi15 z) := by
  have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl smoothOpen_u15 smoothOpen_k15
  have hfun : (fun z θ : ℝ => u15 z * k15 z) = fun z _ => psi15 z := by
    funext z θ; rw [psi15]
  rw [hfun] at h
  exact h

/-! ## Iterated derivatives of a `z`-only function -/

/-- The iterated `∂_z`-derivatives of a `z`-only function are the iterated derivatives of the
one-variable function. -/
theorem pzIter_radial_fn (r : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => r z) z θ = deriv^[k] r z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      have hfun : (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) = deriv^[k] r :=
        funext fun z' => ih z'
      rw [hfun, Function.iterate_succ_apply']

/-! ## The explicit iterated derivatives -/

/-- `∂_z (z/(1+z)) = 1/(1+z)²`. -/
theorem deriv_u15 (z : ℝ) (hz : (1 : ℝ) + z ≠ 0) :
    deriv (fun w : ℝ => u15 w) z = 1 / (1 + z) ^ 2 := by
  have hfun : (fun w : ℝ => u15 w) = fun w : ℝ => w / (1 + w) := by
    funext w; rw [u15]
  rw [hfun]
  have h1 : HasDerivAt (fun w : ℝ => w) 1 z := hasDerivAt_id z
  have h2 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
  have h3 := h1.div h2 hz
  rw [show (fun w : ℝ => w / (1 + w)) = (fun w : ℝ => w) / fun w : ℝ => 1 + w from rfl,
    h3.deriv]
  field_simp
  ring

/-- `∂_z (c/(1+z)^n) = -c·n/(1+z)^{n+1}`. -/
theorem deriv_const_div_pow (c : ℝ) (n : ℕ) (z : ℝ) (hz : (1 : ℝ) + z ≠ 0) :
    deriv (fun w : ℝ => c / (1 + w) ^ n) z = -c * (n : ℝ) / (1 + z) ^ (n + 1) := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1) * 1) z :=
    h1.pow n
  have h3 : HasDerivAt (fun w : ℝ => c / (1 + w) ^ n)
      ((0 * (1 + z) ^ n - c * ((n : ℝ) * (1 + z) ^ (n - 1) * 1)) / ((1 + z) ^ n) ^ 2) z :=
    (hasDerivAt_const z c).div h2 (by positivity)
  rw [h3.deriv]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (1 + z) ^ (n - 1) * (1 + z) ^ (n + 1) = (1 + z) ^ (2 * n) := by
      rw [← pow_add]; congr 1; omega
    have hsq : ((1 + z) ^ n) ^ 2 = (1 + z) ^ (2 * n) := by
      rw [show 2 * n = n + n from by ring, pow_add, pow_two]
    rw [hsq]
    rw [show (0 * (1 + z) ^ n - c * ((n : ℝ) * (1 + z) ^ (n - 1) * 1)) / (1 + z) ^ (2 * n)
        = -(c * (n : ℝ) * (1 + z) ^ (n - 1)) / (1 + z) ^ (2 * n) from by ring]
    rw [div_eq_iff (by positivity : (1 + z) ^ (2 * n) ≠ 0)]
    rw [show -c * (n : ℝ) / (1 + z) ^ (n + 1) * (1 + z) ^ (2 * n)
        = (-c * (n : ℝ)) * ((1 + z) ^ (2 * n) / (1 + z) ^ (n + 1)) from by ring]
    rw [show (1 + z) ^ (2 * n) / (1 + z) ^ (n + 1) = (1 + z) ^ (n - 1) from by
      rw [div_eq_iff (by positivity : (1 + z) ^ (n + 1) ≠ 0), ← hpow]]
    ring

/-- The iterated derivatives of `u`: `deriv^[j] u = (-1)^{j-1} j!/(1+z)^{j+1}` for `j ≥ 1`. -/
theorem iter_deriv_u15_pos (j : ℕ) (hj : 1 ≤ j) :
    ∀ z : ℝ, (1 : ℝ) + z ≠ 0 →
      deriv^[j] (fun z : ℝ => u15 z) z
        = (-1 : ℝ) ^ (j - 1) * (j.factorial : ℝ) / (1 + z) ^ (j + 1) := by
  induction j with
  | zero => omega
  | succ j ih =>
      intro z hz
      rcases eq_or_ne j 0 with hj0 | hj0
      · subst hj0
        rw [Function.iterate_one, deriv_u15 z hz]
        norm_num
      · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        rw [Function.iterate_succ_apply']
        have hev : deriv^[j] (fun z : ℝ => u15 z)
            =ᶠ[𝓝 z] fun w => (-1 : ℝ) ^ (j - 1) * ((j.factorial : ℝ)) / (1 + w) ^ (j + 1) := by
          have hset : IsOpen {w : ℝ | (1 : ℝ) + w ≠ 0} := isOpen_ne.preimage (by continuity)
          filter_upwards [hset.mem_nhds (by simpa using hz)] with w hw
          exact ih hj1 w hw
        rw [hev.deriv_eq, deriv_const_div_pow _ _ z hz]
        have hsign : (-1 : ℝ) ^ j = (-1) ^ (j - 1) * (-1) := by
          rw [show j = (j - 1) + 1 from by omega, pow_succ]
          rw [show j - 1 + 1 - 1 = j - 1 from by omega]
        have hnum : -((-1 : ℝ) ^ (j - 1) * ((j.factorial : ℝ))) * ((j + 1 : ℕ) : ℝ)
            = (-1 : ℝ) ^ (j + 1 - 1) * (((j + 1).factorial : ℝ)) := by
          rw [Nat.factorial_succ]
          push_cast
          rw [hsign]
          ring
        rw [hnum]

/-! ## The two refined jet bounds -/

/-- `(1+z)^{j+1}|∂_z^j u| ≤ C` for `1 ≤ j ≤ 4`, `z > 0`. -/
theorem deriv_iter_u15_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ), 1 ≤ j → j ≤ 4 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ (j + 1) * |deriv^[j] (fun z : ℝ => u15 z) z| ≤ C := by
  refine ⟨1000, by norm_num, ?_⟩
  intro j hj hj4 z hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  have hz2 : (0 : ℝ) < 1 + z := by linarith
  have h1 : |deriv^[j] (fun z : ℝ => u15 z) z| = (j.factorial : ℝ) / (1 + z) ^ (j + 1) := by
    rw [iter_deriv_u15_pos j hj z hz1, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg (Nat.cast_nonneg (j.factorial)), abs_of_pos (pow_pos hz2 _)]
  rw [h1, div_eq_mul_inv]
  rw [show (1 + z) ^ (j + 1) * ((j.factorial : ℝ) * ((1 + z) ^ (j + 1))⁻¹) = (j.factorial : ℝ) from by
    rw [← mul_assoc, mul_comm ((1 + z) ^ (j + 1)) (j.factorial : ℝ), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hz1), mul_one]]
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ 1000 := by
    have h24 : ((j.factorial : ℕ) : ℝ) ≤ 24 := by
      have : j.factorial ≤ 24 := by interval_cases j <;> norm_num
      exact_mod_cast this
    linarith
  linarith

/-- `(1+z)^{m+1}|∂_z^m k| ≤ C` for `m ≤ 4`, `z > 0`. -/
theorem deriv_iter_k15_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), m ≤ 4 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ (m + 1) * |deriv^[m] (fun z : ℝ => k15 z) z| ≤ C := by
  refine ⟨1000, by norm_num, ?_⟩
  intro m hm z hz
  have hz1 : -1 < z := by linarith
  have hz1' : (0 : ℝ) < 1 + z := by linarith
  have hfun : (fun z : ℝ => k15 z) = fun z : ℝ => z / (1 + z) ^ 2 := by funext w; rw [k15]
  have hk : deriv^[m] (fun z : ℝ => z / (1 + z) ^ 2) z
      = (-1 : ℝ) ^ m * (m.factorial : ℝ)
          * ((z - (m : ℝ)) * ((1 + z) ^ (m + 2))⁻¹) := by
    rw [Work.Spaces.iter_deriv_hKerClosed m z hz1]
    rw [Work.Spaces.hKerClosed, inv_pow]
  rw [hfun, hk]
  have h1 : |(-1 : ℝ) ^ m * (m.factorial : ℝ) * ((z - (m : ℝ)) * ((1 + z) ^ (m + 2))⁻¹)|
      = (m.factorial : ℝ) * |(z - (m : ℝ)) * ((1 + z) ^ (m + 2))⁻¹| := by
    rw [abs_mul]
    congr 1
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Nat.cast_nonneg m.factorial)]
  rw [h1]
  have h2 : |(z - (m : ℝ)) * ((1 + z) ^ (m + 2))⁻¹| = |z - (m : ℝ)| * ((1 + z) ^ (m + 2))⁻¹ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hz1' _))]
  rw [h2]
  have hkey : |z - (m:ℝ)| / (1 + z) ≤ (m : ℝ) + 1 := by
    rcases le_total (m : ℝ) z with hmz | hmz
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z - m)]
      rw [div_le_iff₀ hz1']
      nlinarith
    · rw [abs_of_nonpos (by linarith : z - m ≤ 0), neg_sub]
      rw [div_le_iff₀ hz1']
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
  have hpowa : (1 + z) ^ (m + 1) * ((1 + z) ^ (m + 2))⁻¹ = (1 + z)⁻¹ := by
    have h1 : (1 + z) ^ (m + 2) = (1 + z) ^ (m + 1) * (1 + z) := by
      have h2 : m + 2 = (m + 1) + 1 := by omega
      rw [h2, pow_succ]
    rw [h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hz1')), one_mul]
  have hshape : (1 + z) ^ (m + 1) * ((m.factorial : ℝ) * (|z - (m:ℝ)| * ((1 + z) ^ (m + 2))⁻¹))
      = (m.factorial : ℝ) * (|z - (m:ℝ)| / (1 + z)) := by
    rw [show (1 + z) ^ (m + 1) * ((m.factorial : ℝ) * (|z - (m:ℝ)| * ((1 + z) ^ (m + 2))⁻¹))
        = (m.factorial : ℝ) * (|z - (m:ℝ)| * ((1 + z) ^ (m + 1) * ((1 + z) ^ (m + 2))⁻¹))
        from by ring]
    rw [hpowa, div_eq_mul_inv]
  rw [hshape]
  have hfac : (m.factorial : ℝ) * ((m : ℝ) + 1) ≤ 1000 := by
    have h : m.factorial * (m + 1) ≤ 120 := by interval_cases m <;> norm_num
    have h2 : ((m.factorial * (m + 1) : ℕ) : ℝ) ≤ 120 := by exact_mod_cast h
    push_cast at h2
    linarith
  calc (m.factorial : ℝ) * (|z - (m:ℝ)| / (1 + z))
      ≤ (m.factorial : ℝ) * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ 1000 := hfac

/-! ## The jet bound of `ψ` -/

/-- **The jet bound of `ψ`**: `(1+z)^{c+1}|∂_z^c ψ(z)| ≤ C` for `c ≤ 4`, `z > 0`. -/
theorem pzIter_psi15_main :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ), c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      (1 + z) ^ (c + 1) * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ| ≤ C := by
  obtain ⟨Cu0, hCu0, hCu0b⟩ := deriv_iter_u15_le
  obtain ⟨Ck0, hCk0, hCk0b⟩ := deriv_iter_k15_le
  set Cu : ℝ := max Cu0 1 with hCud
  set Ck : ℝ := max Ck0 1 with hCkd
  have hCu1 : (1 : ℝ) ≤ Cu := le_max_right _ _
  have hCk1 : (1 : ℝ) ≤ Ck := le_max_right _ _
  have hCupos : (0 : ℝ) < Cu := lt_of_lt_of_le zero_lt_one hCu1
  have hCkpos : (0 : ℝ) < Ck := lt_of_lt_of_le zero_lt_one hCk1
  have hCu : ∀ (j : ℕ), 1 ≤ j → j ≤ 4 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ (j + 1) * |deriv^[j] (fun z : ℝ => u15 z) z| ≤ Cu :=
    fun j hj hj4 z hz => le_trans (hCu0b j hj hj4 z hz) (le_max_left _ _)
  have hCk : ∀ (m : ℕ), m ≤ 4 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ (m + 1) * |deriv^[m] (fun z : ℝ => k15 z) z| ≤ Ck :=
    fun m hm z hz => le_trans (hCk0b m hm z hz) (le_max_left _ _)
  refine ⟨16 * (Cu * Ck + 1), by positivity, ?_⟩
  intro c hc z hz θ
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hcont : ContDiffAt ℝ ((c : ℕ) : WithTop ℕ∞) (fun z : ℝ => u15 z) z ∧
      ContDiffAt ℝ ((c : ℕ) : WithTop ℕ∞) (fun z : ℝ => k15 z) z := by
    constructor
    · have hfun : (fun z : ℝ => u15 z) = fun z : ℝ => z / (1 + z) := by funext w; rw [u15]
      rw [hfun]
      refine ContDiffAt.div ?_ ?_ (by linarith : (1 : ℝ) + z ≠ 0)
      · fun_prop
      · fun_prop
    · have hfun : (fun z : ℝ => k15 z) = fun z : ℝ => z / (1 + z) ^ 2 := by funext w; rw [k15]
      rw [hfun]
      refine ContDiffAt.div ?_ ?_ (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0))
      · fun_prop
      · fun_prop
  have hleib : deriv^[c] ((fun z : ℝ => u15 z) * fun z : ℝ => k15 z) z
      = ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * deriv^[i] (fun z : ℝ => u15 z) z
          * deriv^[c - i] (fun z : ℝ => k15 z) z := by
    have h := iteratedDeriv_mul (n := c) (x := z) (f := fun z : ℝ => u15 z)
      (g := fun z : ℝ => k15 z) (by simpa using hcont.1) (by simpa using hcont.2)
    simpa only [iteratedDeriv_eq_iterate] using h
  have hpsi : Work.Spaces.pzIter c (fun z _ => psi15 z) z θ
      = deriv^[c] ((fun z : ℝ => u15 z) * fun z : ℝ => k15 z) z := by
    rw [pzIter_radial_fn]
    rfl
  rw [hpsi, hleib]
  have hterm : ∀ i ∈ Finset.range (c + 1),
      (1 + z) ^ (c + 1) * |(c.choose i : ℝ) * deriv^[i] (fun z : ℝ => u15 z) z
          * deriv^[c - i] (fun z : ℝ => k15 z) z|
        ≤ (c.choose i : ℝ) * (Cu * Ck + 1) := by
    intro i hi
    have hic : i ≤ c := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hk' : |deriv^[c - i] (fun z : ℝ => k15 z) z| ≤ Ck / (1 + z) ^ (c - i + 1) := by
      rw [le_div_iff₀ (pow_pos hz1 _), mul_comm]
      exact hCk (c - i) (by omega) z hz
    have hmain : (1 + z) ^ (c + 1) * (|deriv^[i] (fun z : ℝ => u15 z) z|
        * |deriv^[c - i] (fun z : ℝ => k15 z) z|) ≤ Cu * Ck + 1 := by
      rcases eq_or_ne i 0 with hi0 | hi0
      · subst hi0
        rw [Function.iterate_zero, id_eq]
        have hu' : |u15 z| ≤ 1 := by
          rw [u15, abs_div, abs_of_pos hz1, abs_of_nonneg hz.le, div_le_one hz1]
          linarith
        have hck : |deriv^[c] (fun z : ℝ => k15 z) z| ≤ Ck / (1 + z) ^ (c + 1) := by
          simpa using hk'
        calc (1 + z) ^ (c + 1) * (|u15 z| * |deriv^[c] (fun z : ℝ => k15 z) z|)
            ≤ (1 + z) ^ (c + 1) * (1 * (Ck / (1 + z) ^ (c + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hu' hck (abs_nonneg _) (by norm_num)) (by positivity)
          _ = Ck := by
              rw [one_mul, div_eq_mul_inv]
              rw [show (1 + z) ^ (c + 1) * ((Ck : ℝ) * ((1 + z) ^ (c + 1))⁻¹) = Ck from by
                rw [← mul_assoc, mul_comm ((1 + z) ^ (c + 1)) (Ck : ℝ), mul_assoc,
                  mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hz1)), mul_one]]
          _ ≤ Cu * Ck + 1 := by nlinarith [hCu1, hCk1]
      · have hu' : |deriv^[i] (fun z : ℝ => u15 z) z| ≤ Cu / (1 + z) ^ (i + 1) := by
          rw [le_div_iff₀ (pow_pos hz1 _), mul_comm]
          exact hCu i (Nat.one_le_iff_ne_zero.mpr hi0) (by omega) z hz
        calc (1 + z) ^ (c + 1) * (|deriv^[i] (fun z : ℝ => u15 z) z|
              * |deriv^[c - i] (fun z : ℝ => k15 z) z|)
            ≤ (1 + z) ^ (c + 1) * ((Cu / (1 + z) ^ (i + 1)) * (Ck / (1 + z) ^ (c - i + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hu' hk' (abs_nonneg _)
                  (div_nonneg hCupos.le (pow_nonneg hz1.le _))) (by positivity)
          _ ≤ Cu * Ck + 1 := by
              have heq : (1 + z) ^ (c + 1) * ((Cu / (1 + z) ^ (i + 1))
                    * (Ck / (1 + z) ^ (c - i + 1))) = Cu * Ck / (1 + z) := by
                field_simp
                rw [← pow_succ', ← pow_add,
                  show i + 1 + (c - i + 1) = c + 1 + 1 from by omega]
              rw [heq]
              have hCK : (0 : ℝ) ≤ Cu * Ck := mul_nonneg hCupos.le hCkpos.le
              have hlt : Cu * Ck / (1 + z) ≤ Cu * Ck := by
                rw [div_le_iff₀ hz1]
                nlinarith [hCK, hz]
              linarith
    have habs : |(c.choose i : ℝ) * deriv^[i] (fun z : ℝ => u15 z) z
          * deriv^[c - i] (fun z : ℝ => k15 z) z|
        = (c.choose i : ℝ) * (|deriv^[i] (fun z : ℝ => u15 z) z|
          * |deriv^[c - i] (fun z : ℝ => k15 z) z|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (c.choose i))]
      ring
    rw [habs,
      show (1 + z) ^ (c + 1) * ((c.choose i : ℝ) * (|deriv^[i] (fun z : ℝ => u15 z) z|
            * |deriv^[c - i] (fun z : ℝ => k15 z) z|))
          = (c.choose i : ℝ) * ((1 + z) ^ (c + 1) * (|deriv^[i] (fun z : ℝ => u15 z) z|
            * |deriv^[c - i] (fun z : ℝ => k15 z) z|)) from by ring]
    exact mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
  have hsum : (∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * (Cu * Ck + 1))
      = (2 : ℝ) ^ c * (Cu * Ck + 1) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  calc (1 + z) ^ (c + 1) * |∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ)
        * deriv^[i] (fun z : ℝ => u15 z) z * deriv^[c - i] (fun z : ℝ => k15 z) z|
      ≤ (1 + z) ^ (c + 1) * ∑ i ∈ Finset.range (c + 1), |(c.choose i : ℝ)
          * deriv^[i] (fun z : ℝ => u15 z) z * deriv^[c - i] (fun z : ℝ => k15 z) z| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑ i ∈ Finset.range (c + 1), (1 + z) ^ (c + 1) * |(c.choose i : ℝ)
          * deriv^[i] (fun z : ℝ => u15 z) z * deriv^[c - i] (fun z : ℝ => k15 z) z| := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * (Cu * Ck + 1) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ c * (Cu * Ck + 1) := hsum
    _ ≤ 16 * (Cu * Ck + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h2 : (2 : ℕ) ^ c ≤ 16 := by interval_cases c <;> norm_num
        exact_mod_cast h2

/-- `∂_z ψ(z) = (2z - z²)/(1+z)^4`. -/
theorem deriv_psi15 (z : ℝ) (hz : (1 : ℝ) + z ≠ 0) :
    deriv (fun w : ℝ => psi15 w) z = (2 * z - z ^ 2) / (1 + z) ^ 4 := by
  have hev : (fun w : ℝ => psi15 w) =ᶠ[𝓝 z] fun w : ℝ => w ^ 2 / (1 + w) ^ 3 := by
    have hset : IsOpen {w : ℝ | (1 : ℝ) + w ≠ 0} := isOpen_ne.preimage (by continuity)
    filter_upwards [hset.mem_nhds (by simpa using hz)] with w hw
    rw [psi15_eq]
  rw [hev.deriv_eq]
  change deriv ((fun w : ℝ => w ^ 2) / (fun w : ℝ => (1 + w) ^ 3)) z
      = (2 * z - z ^ 2) / (1 + z) ^ 4
  rw [deriv_div]
  · rw [show deriv (fun w : ℝ => w ^ 2) z = 2 * z from by simp]
    have h2 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h3 : deriv (fun w : ℝ => (1 + w) ^ 3) z = 3 * (1 + z) ^ 2 * 1 := (h2.pow 3).deriv
    rw [h3]
    field_simp
    ring
  · fun_prop
  · fun_prop
  · exact pow_ne_zero 3 hz

/-- **The radial bound for `ψ`**: for `c ≤ m ≤ 4`, `z > 0`,
`(1+z)·w(z)·z^m·|∂_z^c ψ(z)| ≤ C·(1+z)^{m-c}`. -/
theorem pzIter_psi15_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (c m : ℕ), c ≤ m → m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      (1 + z) * Work.Spaces.w z * z ^ m * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ|
        ≤ C * (1 + z) ^ (m - c) := by
  obtain ⟨C1, hC1pos, hC1⟩ := pzIter_psi15_main
  refine ⟨max (C1 + 1000) 10, lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro c m hcm hm z hz θ
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hCmax : (1000 : ℝ) ≤ max (C1 + 1000) 10 := le_trans (by linarith) (le_max_left _ _)
  rcases lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · -- `m = 0`
      have hc0 : c = 0 := by omega
      subst hc0
      rw [pow_zero, mul_one, pzIter_radial_fn, Function.iterate_zero, id_eq, psi15_eq,
        Work.Spaces.w]
      have hval : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * |z ^ 2 / (1 + z) ^ 3| = 1 := by
        rw [abs_of_pos (div_pos (pow_pos hz 2) (pow_pos hz1 3))]
        field_simp
      have hexp : (1 + z) ^ (0 - 0) = 1 := by norm_num
      rw [hval, hexp, mul_one]
      exact le_trans (by norm_num : (1 : ℝ) ≤ 1000) hCmax
    · -- `m = 1`
      have hc1 : c = 0 ∨ c = 1 := by omega
      rcases hc1 with hc | hc
      · subst hc
        rw [pow_one, pzIter_radial_fn, Function.iterate_zero, id_eq, psi15_eq, Work.Spaces.w]
        have hval : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * z * |z ^ 2 / (1 + z) ^ 3| = z := by
          rw [abs_of_pos (div_pos (pow_pos hz 2) (pow_pos hz1 3))]
          field_simp
        have hexp : (1 + z) ^ (1 - 0) = 1 + z := by norm_num
        rw [hval, hexp]
        have hl : z ≤ 1000 * (1 + z) := by nlinarith
        have h2 : z ≤ max (C1 + 1000) 10 * (1 + z) :=
          le_trans hl (mul_le_mul_of_nonneg_right hCmax (by positivity))
        linarith
      · subst hc
        rw [pow_one, pzIter_radial_fn, Function.iterate_one,
          deriv_psi15 z (by linarith : (1 : ℝ) + z ≠ 0), Work.Spaces.w]
        have hval : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * z * |(2 * z - z ^ 2) / (1 + z) ^ 4|
            = |2 - z| / (1 + z) := by
          rw [abs_div, abs_of_pos (pow_pos hz1 4),
            show |2 * z - z ^ 2| = z * |2 - z| from by
              rw [show (2 * z - z ^ 2) = z * (2 - z) from by ring, abs_mul,
                abs_of_nonneg hz.le]]
          field_simp
        have hexp : (1 + z) ^ (1 - 1) = 1 := by norm_num
        rw [hval, hexp, mul_one]
        have h2 : |2 - z| / (1 + z) ≤ 2 := by
          rw [div_le_iff₀ hz1]
          rcases le_total z 2 with h | h
          · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - z)]; linarith
          · rw [abs_of_nonpos (by linarith : 2 - z ≤ 0)]; linarith
        have h3 : (2 : ℝ) ≤ max (C1 + 1000) 10 :=
          le_trans (by norm_num) (le_trans (le_add_of_nonneg_left hC1pos.le) (le_max_left _ _))
        linarith
  · -- `m ≥ 2`
    have hstep : (1 + z) * Work.Spaces.w z * z ^ m ≤ (1 + z) ^ (m + 1) := by
      rw [Work.Spaces.w]
      have hzm : z ^ m = z ^ 2 * z ^ (m - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hzm]
      rw [show (1 + z) * ((1 + z) ^ 2 / z ^ 2) * (z ^ 2 * z ^ (m - 2))
          = (1 + z) ^ 3 * z ^ (m - 2) from by
        field_simp]
      have h1 : z ^ (m - 2) ≤ (1 + z) ^ (m - 2) :=
        pow_le_pow_left₀ hz.le (by linarith) _
      calc (1 + z) ^ 3 * z ^ (m - 2) ≤ (1 + z) ^ 3 * (1 + z) ^ (m - 2) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) 3)
        _ = (1 + z) ^ (m + 1) := by
            rw [← pow_add, show 3 + (m - 2) = m + 1 from by omega]
    have hpow : (1 + z) ^ (m - c) * (1 + z) ^ (c + 1) = (1 + z) ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc (1 + z) * Work.Spaces.w z * z ^ m * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ|
        ≤ (1 + z) ^ (m + 1) * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ| :=
          mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
      _ = (1 + z) ^ (m - c) * ((1 + z) ^ (c + 1)
            * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ|) := by
          rw [hpow.symm, mul_assoc]
      _ ≤ (1 + z) ^ (m - c) * (C1 + 1000) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
          exact le_trans (hC1 c (by omega) z hz θ) (by linarith)
      _ ≤ max (C1 + 1000) 10 * (1 + z) ^ (m - c) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow19T2Parts.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## The vocabulary -/

/-- `A = ((z+1)/z)·𝒱(Φ̃_*)`: the weighted star coefficient whose `𝒲^{4,∞}`-membership (with
bound `≤ Cs·α`) is the field `VocabO2.StarPkgo2.VzW`. -/
def A19 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z * Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ

/-- The `z`-only factor `H₂(z) = 2z²(1-z)/(1+z)⁴` of the row-19 piece, lifted to `Fn`. -/
def H2f : Fn := fun z _ => Work.FTS.Nonlinear.Open.Row19Prep.H2b z

/-- `c₁₉(θ) = (α/c(α))·Γ(θ)`: the angular factor of `Z19`. -/
def c19 (α : ℝ) : ℝ → ℝ := fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ

/-- `K₁₉ = A·H₂`: the `(z,θ)`-factor of `Z19`. -/
def K19 (α : ℝ) (Φs : Fn) : Fn := fun z θ => A19 α Φs z θ * H2f z θ

/-- The row-19 piece `Z = 𝒱(Φ̃_*)·∂_zF_*` in its factorised form. -/
def Z19 (α : ℝ) (Φs : Fn) : Fn := fun z θ => c19 α θ * K19 α Φs z θ

/-- `Φ(θ) = (α + sin 2θ)·sin(2θ)^{α/5}`: the angular weight of the `𝒲^{l,∞}`-norm. -/
def PhiAng (α θ : ℝ) : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- The angular factor attached to the `A`-derivatives of the (γ)-family: `1` for `b = 0` and
`Φ(θ)` for `b ≥ 1`. -/
def Psi19 (α : ℝ) (b : ℕ) (θ : ℝ) : ℝ := if b = 0 then 1 else PhiAng α θ

/-- `TB = Σ_{j<5} tBound j 0`, an upper bound for `tBound (a-1) 0`, `a ≤ 4`. -/
def TB19 : ℝ := ∑ j ∈ Finset.range 5, Work.Spaces.tBound j 0

/-- The angular-jet factor of `D_θ^a Γ`: `1` for `a = 0` and `α·TB` for `a ≥ 1`. -/
def MGa (α : ℝ) (a : ℕ) : ℝ := if a = 0 then 1 else α * TB19

/-! ## Elementary facts -/

lemma TB19_nonneg : 0 ≤ TB19 :=
  Finset.sum_nonneg fun j _ => Work.Spaces.tBound_nonneg j 0

lemma tBound_le_TB19 {a : ℕ} (ha : 1 ≤ a) (ha4 : a ≤ 4) : Work.Spaces.tBound (a - 1) 0 ≤ TB19 := by
  refine Finset.single_le_sum (f := fun j : ℕ => Work.Spaces.tBound j 0)
    (fun j _ => Work.Spaces.tBound_nonneg j 0) ?_
  rw [Finset.mem_range]
  omega


lemma MGa_le {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (a : ℕ) : MGa α a ≤ 1 + TB19 := by
  rw [MGa]
  split_ifs with h
  · linarith [TB19_nonneg]
  · nlinarith [TB19_nonneg, hα, hα1]

lemma PhiAng_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ PhiAng α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [PhiAng]
  exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)

lemma Psi19_nonneg {α : ℝ} (hα : 0 < α) {b : ℕ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Psi19 α b θ := by
  rw [Psi19]
  split_ifs with h
  · norm_num
  · exact PhiAng_nonneg hα hθ


/-- `α·Γ(θ) ≤ Φ(θ)` on `Iθ`. -/
lemma alpha_Gam_le_PhiAng {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ ≤ PhiAng α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [PhiAng]
  rcases eq_or_lt_of_le hs with h | h
  · have hzero : Real.sin (2 * θ) = 0 := h.symm
    have hsc : Real.sin θ * Real.cos θ = 0 := by
      have h2 := Real.sin_two_mul θ
      rw [h2] at hzero
      linarith
    have hGam : Work.Spaces.Gam α θ = 0 := by
      rw [Work.Spaces.Gam]
      have hz : Real.sin θ * Real.cos θ ^ 2 = 0 := by
        rw [show Real.sin θ * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) * Real.cos θ by ring,
          hsc, zero_mul]
      rw [hz]
      exact Real.zero_rpow (by linarith : α / 3 ≠ 0)
    rw [hGam, mul_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)
  · have hw := Work.Spaces.Gam_mul_weight_le α θ hα hθ
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hkey : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        ≤ α + Real.sin (2 * θ) := by
      rw [div_le_iff₀ hden] at hw
      simpa using hw
    have hs' : 0 < (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_pos_of_pos h _
    calc α * Work.Spaces.Gam α θ
        = α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos h _)), mul_one]
      _ = α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            * (Real.sin (2 * θ)) ^ (α / 5) := by
          rw [Real.rpow_neg h.le, inv_inv]
      _ ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_le_mul_of_nonneg_right hkey hs'.le

lemma Gam_nonneg' {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1

lemma Gam_le_one' {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2

/-! ## The equivalence of the two forms of `Z` on the open quadrant -/

theorem Z19_eq_Vs_Gs {α : ℝ} {Φs : Fn} (hα : 0 < α) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      Z19 α Φs z θ
        = Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
            * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ := by
  intro z hz θ
  have hz1 : (-1 : ℝ) < z := by linarith
  have hH : Work.FTS.Nonlinear.Open.Row19Prep.H2b z
      = z / (z + 1) * Work.FTS.Nonlinear.FstarPkg.Hz z := by
    rw [Work.FTS.Nonlinear.Open.Row19Prep.H2b, Work.FTS.Nonlinear.FstarPkg.Hz]
    field_simp
    ring
  rw [Z19, K19, c19, A19, H2f, hH, Work.FTS.Nonlinear.Pieces.RNP.Gs,
    Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα hz1]
  field_simp

/-! ## The `z`-only Leibniz rule for `∂_z^k` -/

theorem pzIter_zOnly (r : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => r z) = fun z θ => deriv^[k] r z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      exact (congrFun (Function.iterate_succ_apply' deriv k r) z).symm

/-! ## Smoothness -/

theorem contDiffOn_H2b : ContDiffOn ℝ Work.Stability.smoothOrder
    Work.FTS.Nonlinear.Open.Row19Prep.H2b (Set.Ioi 0) := by
  have h : Work.FTS.Nonlinear.Open.Row19Prep.H2b
      = fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4 := rfl
  rw [h]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact ((contDiffOn_const (c := (2 : ℝ)).mul (contDiffOn_id.pow 2)).mul
      (contDiffOn_const.sub contDiffOn_id))
  · exact (contDiffOn_const.add contDiffOn_id).pow 4
  · intro z hz
    have hz1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity

theorem smoothOpen_H2f : Work.FTS.EllipticEst.SmoothOpen H2f :=
  Work.FTS.NonlinRows.smoothOpen_z_only contDiffOn_H2b

theorem contDiffOn_zdiv : ContDiffOn ℝ Work.Stability.smoothOrder
    (fun z : ℝ => (z + 1) / z) (Set.Ioi 0) := by
  refine ContDiffOn.div (contDiffOn_id.add contDiffOn_const) contDiffOn_id ?_
  intro z hz
  exact ne_of_gt (Set.mem_Ioi.mp hz)

theorem smoothOpen_A19 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs) := by
  have hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_Vop (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs)
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) :=
    Work.FTS.NonlinRows.smoothOpen_z_only contDiffOn_zdiv
  exact hz.mul hV

theorem smoothOpen_c19 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => c19 α θ) :=
  Work.FTS.NonlinRows.smoothOpen_theta_only
    (by
      have h := (Work.FTS.NonlinRows.contDiffOn_Gam α).const_smul (α / Work.Spaces.c α)
      have hfun : c19 α = fun y : ℝ => α / Work.Spaces.c α * Work.Spaces.Gam α y := by
        funext y; rw [c19]
      rw [hfun]
      exact h)

theorem smoothOpen_K19 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) : Work.FTS.EllipticEst.SmoothOpen (K19 α Φs) :=
  (smoothOpen_A19 hα hα1 hs).mul smoothOpen_H2f

theorem smoothOpen_Z19 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) : Work.FTS.EllipticEst.SmoothOpen (Z19 α Φs) :=
  (smoothOpen_c19 α).mul (smoothOpen_K19 hα hα1 hs)

/-! ## The angular jet bounds -/

/-- `|D_θ^a Γ| ≤ MΓ(a)·Γ` on `Iθ`, for `a ≤ 4`. -/
theorem dthU_Gam_le_MGa {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} (ha : a ≤ 4) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (fun t : ℝ => Work.Spaces.Gam α t) θ|
        ≤ MGa α a * Work.Spaces.Gam α θ := by
  intro θ hθ
  have hG := Gam_nonneg' hα hθ
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h
    rw [Function.iterate_zero_apply, MGa, if_pos rfl, one_mul, abs_of_nonneg hG]
  · rw [MGa, if_neg (Nat.pos_iff_ne_zero.mp h)]
    have hd := Work.Spaces.dthU_Gam_le a h α hα hα1 θ hθ
    have hb := tBound_le_TB19 h ha
    calc |Work.Spaces.dthU^[a] (fun t : ℝ => Work.Spaces.Gam α t) θ|
        ≤ α * Work.Spaces.tBound (a - 1) 0 * Work.Spaces.Gam α θ := hd
      _ ≤ α * TB19 * Work.Spaces.Gam α θ := by
          refine mul_le_mul_of_nonneg_right ?_ hG
          exact mul_le_mul_of_nonneg_left hb hα.le

/-- `|D_θ^a c₁₉| ≤ 10·α·MΓ(a)·Γ` on `Iθ`, for `a ≤ 4`. -/
theorem dthU_c19_le_MGa {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} (ha : a ≤ 4) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (c19 α) θ| ≤ 10 * α * MGa α a * Work.Spaces.Gam α θ := by
  intro θ hθ
  have hc : (0 : ℝ) < Work.Spaces.c α := by
    have := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hk : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hc.le), div_le_iff₀ hc]
    nlinarith [(Work.Spaces.c_bounds α hα hα1).1]
  have hfun : c19 α = fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
    funext t; rw [c19]
  rw [hfun, Work.Spaces.dthU_iter_const_mul]
  rw [abs_mul]
  calc |α / Work.Spaces.c α| * |Work.Spaces.dthU^[a] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ (10 * α) * (MGa α a * Work.Spaces.Gam α θ) :=
        mul_le_mul hk (dthU_Gam_le_MGa hα hα1 ha θ hθ) (abs_nonneg _) (by positivity)
    _ = 10 * α * MGa α a * Work.Spaces.Gam α θ := by ring

theorem WlInf_nonneg' (α : ℝ) (l : ℕ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α l h) :
    0 ≤ Work.Spaces.WlInf α l h := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α l h hmem) (Work.Spaces.wlThSum_nonneg α l h hmem)

/-- `∂_z^k` of the zero function is zero. -/
theorem pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz, deriv_const]

/-- The constant of the pointwise families, chosen so that both the (η)- and the (γ)-bounds
of `Z19` fit into the `200000·W` shape required by `wtoHQ_of_pointwise_open`. -/
def CZ19 (C : ℝ) : ℝ := 10 ^ 20 * (1 + C) * (1 + TB19)

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.SplitsAll_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.NonlinRows


end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row10 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# Row 10 of the §8 table, in the `StarPkgo2` vocabulary (open quadrant)

`N1sg α Φs g = 2·ℛ(Φ̃_*)·g`, with `ℛ := Rop`, `Φ̃_* := PhiTs α Φs`.  Writing
`H := ((z+1)/z)·ℛ(Φ̃_*)` for the weighted star coefficient, the row is the product rule for
`H · ((z/(1+z))·g)`:

* `RW` of `VocabO2.StarPkgo2` prices `H` by the `𝒲^{4,∞}`-norm, `WlInf α 4 H ≤ Cs·α`
  (the paper's `PhiStarRegularity2`);
* `N4Norm'.wprod` is exactly the multiplication rule for a `𝒲^{4,∞}`-coefficient, with the
  loss `Ci·α^{-1/2}`, and `NRow10aux.mul_phi_Hk` disposes of the bounded radial factor
  `z/(1+z)`;
* `α^{-1/2}·α = √α` gives the rate.

The `StarH` here is the coefficient of `NRow10.StarH`; it is redeclared locally only so that
this file does not depend on the unfinished module `NonlinRows.NRow10`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false



end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.F0_to_WDp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `WDp`-grid bound at a general order -/

/-- **Pointwise bounds give the `WDp` estimate at any order `n`.**  If every mixed derivative
`D_z^b D_θ^j f` with `b + j ≤ n` is bounded by `M ≥ 0` on the whole open quadrant, then the
double sum of the corresponding open-quadrant suprema is at most the number `(n+1)²` of grid
entries times `M` (the entries with `b + j > n` contribute the junk value `0 ≤ M`).

This is the general-`n` form of `Work.FTS.OpenPkg.WDp_le_of_pointwise` (which is the case
`n = 4`, with the loose constant `25`); the only point to note is that the supremum `supAbsO`
ranges over exactly the same open quadrant on which the hypothesis bounds `f`. -/
theorem WDp_le_of_pointwise_gen {n : ℕ} {M : ℝ} (hM : 0 ≤ M) {f : ℝ → ℝ → ℝ}
    (h : ∀ b j : ℕ, b + j ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b j f z θ| ≤ M) :
    Work.FTS.VocabO.WDp n f ≤ ((n : ℝ) + 1) ^ 2 * M := by
  classical
  rw [Work.FTS.VocabO.WDp]
  calc
    ∑ b ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (if b + j ≤ n then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) else 0)
      ≤ ∑ _b ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (n + 1), M := by
        refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs with hbj
        · exact Work.FTS.H2.supAbsO_le (fun z θ hz hθ hθ' => h b j hbj z θ hz hθ hθ')
        · exact hM
    _ = ((n : ℝ) + 1) ^ 2 * M := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ## The bridge `F0 → WDp` -/

theorem F0_to_WDp (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (f : ℝ → ℝ → ℝ), 0 ≤ K → Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.PhiStar.F0 n K f → Work.FTS.VocabO.WDMem n f ∧ Work.FTS.VocabO.WDp n f ≤ C * K := by
  classical
  -- the constant: `(n+1)² · (∑_{m ≤ n} bell m + 1)`, which dominates every `bell b` with `b ≤ n`
  set B : ℝ := ∑ m ∈ Finset.range (n + 1), (Work.Spaces.bell m : ℝ) with hBdef
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact Finset.sum_nonneg fun m _ => Nat.cast_nonneg (Work.Spaces.bell m)
  refine ⟨((n : ℝ) + 1) ^ 2 * (B + 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact mul_pos (pow_pos h1 2) (by linarith)
  · intro K f hK hsf hf
    -- `bell b ≤ B` for `b ≤ n`: the term `b` occurs in the defining sum of `B`
    have hBle : ∀ m ≤ n, (Work.Spaces.bell m : ℝ) ≤ B := by
      intro m hm
      rw [hBdef]
      exact Finset.single_le_sum (fun i _ => Nat.cast_nonneg (Work.Spaces.bell i))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    have hBK : (0 : ℝ) ≤ B * K := mul_nonneg hBnn hK
    -- the pointwise bound on the open quadrant
    have hpt : ∀ b j : ℕ, b + j ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b j f z θ| ≤ B * K := by
      intro b j hbj z θ hz hθ hθ'
      -- the Stirling expansion of `D_z^b` on the open half-line, for the slice `D_θ^j f`
      have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun z' => Work.Spaces.DthIter j f z' θ) (Set.Ioi 0) :=
        Work.FTS.OpenPkg.smoothOpen_DthIter_slice_z hsf j ⟨hθ, hθ'⟩
      rw [Work.Spaces.mixed,
        Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := Work.Spaces.DthIter j f) hslice b z
          (Set.mem_Ioi.mpr hz)]
      -- each summand is bounded by `K`, because `z ≤ z+1` and `k + j ≤ n`
      have hterm : ∀ k ≤ b,
          |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| ≤ K := by
        intro k hk
        have hkj : k + j ≤ n := by omega
        have h2 : (z + 1) ^ k
            * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| ≤ K := by
          have h1 := hf k j hkj z θ hz hθ hθ'
          rwa [abs_mul, abs_of_pos (pow_pos (by linarith : (0 : ℝ) < z + 1) k)] at h1
        have h3 : z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            ≤ (z + 1) ^ k
              * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz.le (by linarith) k) (abs_nonneg _)
        calc |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            = z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| := by
              rw [abs_mul, abs_of_nonneg (pow_nonneg hz.le k)]
          _ ≤ (z + 1) ^ k
                * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| := h3
          _ ≤ K := h2
      refine le_trans (Work.Spaces.abs_sum_scoef_mul_le b K
        (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ) hterm) ?_
      exact mul_le_mul_of_nonneg_right (hBle b (le_trans (Nat.le_add_right b j) hbj)) hK
    refine ⟨?_, ?_⟩
    · intro b j hbj
      exact ⟨B * K, fun z θ hz hθ hθ' => hpt b j hbj z θ hz hθ hθ'⟩
    · have hgrid := WDp_le_of_pointwise_gen (n := n) (M := B * K) hBK (f := f) hpt
      refine le_trans hgrid ?_
      have h1 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
      have h2 : B * K ≤ (B + 1) * K := by
        rw [add_mul, one_mul]
        exact le_add_of_nonneg_right hK
      calc ((n : ℝ) + 1) ^ 2 * (B * K)
          ≤ ((n : ℝ) + 1) ^ 2 * ((B + 1) * K) := mul_le_mul_of_nonneg_left h2 h1
        _ = ((n : ℝ) + 1) ^ 2 * (B + 1) * K := by ring

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Product-integrability of the `ℋ^k`-integrand, over the *half-open* product measure.**

`HkMem α k f` is stated with the closed intervals `Iz = [0,∞)` and `Iθ = [0,π/2]`: the
angular slices of `HkIntegrand α k f` are integrable on `Iθ` for every `z ∈ Iz`, and the
`z`-integral of those slices is integrable on `Iz`.  Since `f` is smooth on the open quadrant,
the uncurried integrand is continuous there, hence a.e. strongly measurable; Tonelli
(`Work.Spaces.integrable_prod_of_iterated`) then gives product-integrability for the product
of the two restricted measures. -/
theorem integrable_HkIntegrand_prod {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- a.e. strong measurability: the integrand is continuous on the open quadrant
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    exact Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad α k
      (fun n => hsm.forall n)
  -- the angular slices are integrable for a.e. `z`, and the outer integral is integrable
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    exact Filter.Eventually.of_forall fun z hz => hmem.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α k f z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  exact (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    haesm hslice houter).1

theorem integrable_HkIntegrand {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := by
  have hint := integrable_HkIntegrand_prod hsm hmem
  -- `Quad = (0,∞) × (0,π/2)` agrees with `Iz ×ˢ Iθ` up to the coordinate hyperplanes and the
  -- two boundary lines `θ = 0`, `θ = π/2`, all of which are null for the planar Lebesgue measure.
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π / 2)).symm
  have hset : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hμ : MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    change (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    rw [← MeasureTheory.Measure.prod_restrict (Set.Ioi (0 : ℝ))
      (Set.Ioo (0 : ℝ) (π / 2))]
    rw [← MeasureTheory.Measure.restrict_congr_set hz,
      ← MeasureTheory.Measure.restrict_congr_set hθ]
  rw [hμ]
  exact hint

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.fderiv_logPull_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two slots of `fderiv (logPull g)`

In the log coordinates `(s, ζ) = (log z, log tan θ)` the pull-back
`logPull g (s, ζ) = g (e^s) (arctan (e^ζ))` of a profile `g` has
the two directional derivatives

  `∂_s (logPull g) = D_z g (e^s) (arctan (e^ζ))`,
  `∂_ζ (logPull g) = D_θ g (e^s) (arctan (e^ζ)) / 2`,

which is the statement below.  The factor `1/2` is
`∂_ζ (arctan (e^ζ)) = e^ζ/(1 + e^{2ζ}) = sin (2 arctan (e^ζ)) / 2`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts

open scoped Real Topology

/-- The `θ`-slice of a function that is `C^∞` on the open quadrant is differentiable at every
interior angle, with derivative the `θ`-partial `pth`.  (The `θ`-analogue of
`Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`.) -/
private lemma hasDerivAt_thslice {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ :=
  ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt

theorem fderiv_logPull_slots {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
        (ContinuousLinearMap.inl ℝ ℝ ℝ (1 : ℝ))
      = Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))
    ∧ fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
        (ContinuousLinearMap.inr ℝ ℝ ℝ (1 : ℝ))
      = Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2 := by
  have hgS : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hmem : Real.arctan (Real.exp y.2) ∈ Set.Ioo 0 (π / 2) :=
    ⟨Real.arctan_pos.mpr (Real.exp_pos y.2), Real.arctan_lt_pi_div_two _⟩
  -- `logPull g` is smooth (it is `C^n` for every `n`), hence differentiable everywhere.
  have hdiff : DifferentiableAt ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y :=
    ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.contDiff_logPull hg
      1).differentiable (by simp)).differentiableAt
  have hL : HasFDerivAt (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y) y := hdiff.hasFDerivAt
  constructor
  · -- first slot: the direction `(1,0)`, i.e. the `s = log z` derivative
    have hA : HasDerivAt (fun s : ℝ => (s, y.2)) (1, 0) y.1 := by
      simpa using (hasDerivAt_id y.1).prodMk (hasDerivAt_const (c := y.2) (x := y.1))
    have c1 := HasFDerivAt.comp_hasDerivAt_of_eq
      (l := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (l' := fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y) (y := y)
      (f := fun s : ℝ => (s, y.2)) (f' := (1, 0)) (x := y.1) hL hA (by rfl)
    -- the same derivative, computed with the chain rule
    have c2 : HasDerivAt ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
        ∘ (fun s : ℝ => (s, y.2)))
        (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) y.1 := by
      have hslice := hgS.hasDerivAt_slice hmem (Real.exp_pos y.1)
      have hderiv : Work.Spaces.pz g (Real.exp y.1) (Real.arctan (Real.exp y.2)) * Real.exp y.1
          = Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2)) := by
        simp only [Work.Spaces.Dz]; ring
      rw [← hderiv]
      exact hslice.comp y.1 (Real.hasDerivAt_exp y.1)
    simpa only [ContinuousLinearMap.inl_apply] using c1.unique c2
  · -- second slot: the direction `(0,1)`, i.e. the `ζ = log tan θ` derivative
    have hA : HasDerivAt (fun s : ℝ => (y.1, s)) (0, 1) y.2 := by
      simpa using (hasDerivAt_const (c := y.1) (x := y.2)).prodMk (hasDerivAt_id y.2)
    have c1 := HasFDerivAt.comp_hasDerivAt_of_eq
      (l := Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (l' := fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y) (y := y)
      (f := fun s : ℝ => (y.1, s)) (f' := (0, 1)) (x := y.2) hL hA (by rfl)
    have c2 : HasDerivAt ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
        ∘ (fun s : ℝ => (y.1, s)))
        (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2) y.2 := by
      have hslice := hasDerivAt_thslice hgS (Real.exp_pos y.1) hmem
      -- `∂_ζ (arctan (e^ζ)) = e^ζ / (1 + e^{2ζ})`
      have hinner : HasDerivAt (fun s : ℝ => Real.arctan (Real.exp s))
          (1 / (1 + (Real.exp y.2) ^ 2) * Real.exp y.2) y.2 :=
        (Real.hasDerivAt_arctan (Real.exp y.2)).comp y.2 (Real.hasDerivAt_exp y.2)
      have hcomp := hslice.comp y.2 hinner
      -- the trigonometric form of the same scalar
      have hsc : Real.sin (2 * Real.arctan (Real.exp y.2)) / 2
          = Real.exp y.2 / (1 + (Real.exp y.2) ^ 2) := by
        rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
        have h1 : (0:ℝ) < 1 + (Real.exp y.2)^2 := by positivity
        have hs : Real.sqrt (1 + (Real.exp y.2)^2) ≠ 0 := by positivity
        field_simp
        rw [Real.sq_sqrt h1.le]
      have hderiv : Work.Spaces.pth g (Real.exp y.1) (Real.arctan (Real.exp y.2))
            * (1 / (1 + (Real.exp y.2) ^ 2) * Real.exp y.2)
          = Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2 := by
        have h1 : (1:ℝ) / (1 + (Real.exp y.2) ^ 2) * Real.exp y.2
            = Real.exp y.2 / (1 + (Real.exp y.2) ^ 2) := by
          rw [div_mul_eq_mul_div, one_mul]
        rw [h1, ← hsc]
        simp only [Work.Spaces.Dth]
        ring
      rw [hderiv] at hcomp
      exact hcomp
    simpa only [ContinuousLinearMap.inr_apply] using c1.unique c2

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.integrable_slot_of_dom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of a dominated slot, from integrability of the dominator on the open quadrant

The slot transfer consumes `Integrable`-certificates over the *whole* plane for slot integrands
`ρ · (D_z^bD_θ^a A)²`.  The datum `A` is smooth on the open quadrant `Q0` and vanishes off the
closed quadrant (`hA0`), so every mixed slot of `A` vanishes off `Q0` as well
(`IP4Prep.mixed_eq_zero_of_zero_off`), and the slot integrand is supported on `Q0`; on `Q0` the
weight `ρ` is nonnegative (`hρ0`) and continuous (`hρc`), and the slot integrand is dominated by
the `H^m`-integrand of the target `D` (`hdom`).  Hence integrability of the latter on `Q0` gives
integrability of the slot integrand over the whole plane.

The only measure-theoretic content is the passage "integrable on `Q0` + supported on `Q0` ⟹
integrable over the plane", which is the indicator form of `IntegrableOn`:

`Integrable (Q0.indicator F) volume ↔ IntegrableOn F Q0 volume` (`integrable_indicator_iff`)
together with `Q0.indicator F = F` (because `F` vanishes off `Q0`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem integrable_slot_of_dom {α : ℝ} {m a b : ℕ} {ρ : ℝ → ℝ → ℝ} {A D : Work.FTS.Galerkin.Fn} (hAsm : Work.FTS.EllipticEst.SmoothOpen A) (hA0 : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → A z θ = 0) (hρc : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0) (hρ0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ) (hdom : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → ρ z θ * (Work.Spaces.mixed b a A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α m D z θ) (hint : MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α m D)) (MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0)) : MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ * (Work.Spaces.mixed b a A z θ) ^ 2)) MeasureTheory.volume := by
  set F : ℝ × ℝ → ℝ :=
    Function.uncurry (fun z θ => ρ z θ * (Work.Spaces.mixed b a A z θ) ^ 2) with hF
  have hQ0m : MeasurableSet Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- the slot integrand vanishes off the open quadrant
  have hF0 : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 → F p = 0 := by
    intro p hp
    have h : ¬ (0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2) :=
      fun hc => hp (Work.FTS.EllipticEst.mem_Q0.mpr hc)
    have hz : Work.Spaces.mixed b a A p.1 p.2 = 0 :=
      mixed_eq_zero_of_zero_off hA0 b a p.1 p.2 h
    show ρ p.1 p.2 * (Work.Spaces.mixed b a A p.1 p.2) ^ 2 = 0
    rw [hz]
    ring
  -- nonnegativity on the open quadrant
  have hFnn : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 ≤ F p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show 0 ≤ ρ p.1 p.2 * (Work.Spaces.mixed b a A p.1 p.2) ^ 2
    exact mul_nonneg (hρ0 p.1 (le_of_lt hz) p.2 ⟨le_of_lt hθ0, le_of_lt hθ1⟩) (sq_nonneg _)
  -- continuity on the open quadrant (hence a.e. strong measurability for the restricted measure)
  have hcont : ContinuousOn F Work.FTS.EllipticEst.Q0 := by
    change ContinuousOn
      (Function.uncurry (fun z θ => ρ z θ * (Work.Spaces.mixed b a A z θ) ^ 2))
      Work.FTS.EllipticEst.Q0
    exact hρc.mul ((hAsm.mixed b a).continuousOn.pow 2)
  have haesm : AEStronglyMeasurable F (MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0) :=
    hcont.aestronglyMeasurable hQ0m
  -- the domination, a.e. for the restricted measure
  have hbnd : ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      ‖F p‖ ≤ Function.uncurry (Work.Spaces.HkIntegrand α m D) p :=
    MeasureTheory.ae_restrict_of_forall_mem hQ0m (fun p hp => by
      have hle : F p ≤ Function.uncurry (Work.Spaces.HkIntegrand α m D) p := by
        show ρ p.1 p.2 * (Work.Spaces.mixed b a A p.1 p.2) ^ 2
          ≤ Work.Spaces.HkIntegrand α m D p.1 p.2
        exact hdom p.1 p.2 hp
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn p hp)]
      exact hle)
  -- integrability on the quadrant, from the dominator
  have hon : MeasureTheory.Integrable F (MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0) :=
    hint.mono' haesm hbnd
  -- transfer to the whole plane through the indicator
  have hsupp : Function.support F ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    by_contra h
    exact hp (hF0 p h)
  have hon' : MeasureTheory.IntegrableOn F Work.FTS.EllipticEst.Q0 MeasureTheory.volume := hon
  have hind : MeasureTheory.Integrable (Work.FTS.EllipticEst.Q0.indicator F) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hQ0m).mpr hon'
  rwa [Set.indicator_eq_self.mpr hsupp] at hind

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row3u =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row3`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

theorem n0row3u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α g) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04aF α g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨CF, hCF, hF⟩ := Work.FTS.Nonlin.DthFstar_W
  refine ⟨(3 / 2) * CF * Ci ^ 2 + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hgSm hg4 hg5 hL12zero hdec hs hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hHQo : Work.FTS.VocabO.HQo α 4 g := ⟨hgSm, hg4⟩
  -- `D_θF_*` is `C^∞` on the open quadrant and in `𝒲^{4,∞}` with norm `≤ CF·α²`
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFsm.Dth
  obtain ⟨hDthMem, hDthLe⟩ := hF α hα hα1
  -- the radial coefficient `(3/(2α))·L₁₂(g)`
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hL12 := hN.l12H α hIoc g hHQo hL12zero
  have hc0 : (0 : ℝ) < 3 / (2 * α) := by positivity
  have hcoefSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hcoefMem : Work.Spaces.HkMem α 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12.1
  have hcoefXn : Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ (3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg hc0.le]
    exact mul_le_mul_of_nonneg_left hL12.2 hc0.le
  -- the `𝒲^{4,∞}`-product rule on `D_θF_* · ((3/(2α))L₁₂(g))`
  have hprod := hN.wprod α hIoc (Work.Spaces.Dth (Work.Construction.Fstar α))
    (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
    hDthSm hDthMem ⟨hcoefSm, hcoefMem⟩
  -- the exact factorisation of the piece
  have hid : Work.FTS.Nonlin.N04aF α g = fun z θ =>
      Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        * ((3 / (2 * α)) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Spaces.Dth,
      Work.Spaces.pth, Work.Construction.s2]
    ring
  rw [hid]
  refine ⟨hprod.1, ?_⟩
  -- the chain of bounds
  have hXcf : 0 ≤ Work.FTS.Nonlin.Xn α
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  have hk : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCi.le (Real.rpow_nonneg hα.le _)
  have hstep1 : Ci * α ^ (-(1 / 2 : ℝ))
        * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
        * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
        * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDthLe hk) hXcf
  have hstep2 : Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
        * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
        * ((3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g)) :=
    mul_le_mul_of_nonneg_left hcoefXn
      (mul_nonneg hk (mul_nonneg hCF.le (pow_nonneg hα.le 2)))
  -- the `α`-bookkeeping
  have hαpow : α ^ (-(1 / 2 : ℝ)) * α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ)) = Real.sqrt α := by
    have h1 : α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ)) = α := by
      rw [← Real.rpow_add hα,
        show (((2 : ℕ) : ℝ) + (-(1 : ℝ))) = 1 by norm_num, Real.rpow_one]
    have h2 : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [show -(1 / 2 : ℝ) + 1 = (1 / 2 : ℝ) by norm_num, Real.rpow_one] at h
      rw [Real.sqrt_eq_rpow, ← h]
    rw [show α ^ (-(1 / 2 : ℝ)) * α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ))
          = α ^ (-(1 / 2 : ℝ)) * (α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ))) from by ring,
      h1, h2]
  have hkey : Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
        * ((3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g))
      = ((3 / 2) * CF * Ci ^ 2) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    rw [show (3 : ℝ) / (2 * α) = (3 / 2) * α ^ (-(1 : ℝ)) by
      rw [Real.rpow_neg_one]; field_simp]
    rw [show Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
          * (((3 / 2) * α ^ (-(1 : ℝ))) * (Ci * Work.FTS.Nonlin.Xn α g))
        = ((3 / 2) * CF * Ci ^ 2)
            * (α ^ (-(1 / 2 : ℝ)) * α ^ (((2 : ℕ) : ℝ)) * α ^ (-(1 : ℝ)))
            * Work.FTS.Nonlin.Xn α g from by rw [Real.rpow_natCast]; ring]
    rw [hαpow]
    ring
  have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.sqrt_nonneg α) hXg
  calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 g z))
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
          * ((3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g)) :=
        hprod.2.trans (hstep1.trans hstep2)
    _ = ((3 / 2) * CF * Ci ^ 2) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := hkey
    _ ≤ ((3 / 2) * CF * Ci ^ 2 + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
        mul_le_mul_of_nonneg_right (by linarith) hS

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row5u =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row5`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- Row 5 of the §8 table in the **honest** (open-quadrant) class: the `ℋ⁴`-honesty and the
`ℋ⁴`-norm bound of `N₀₅ᵃ = -c2m(θ)·L₁₂(g)(z)·D_zF_*`.  The proof is the exact honest
transcription of `Work.FTS.NonlinRows.NRow5`: the `𝒲^{4,∞}`-factor `D_zF_*` (norm `≤ Cα`,
`Work.FTS.Nonlin.DzFstar_W`) is priced by the `wprod` clause of `N4Norm'`, and the coefficient
`c2m·L₁₂(g)` is handled by `angmul_field` (`c2m` is bounded, its `D_θ`-iterates vanish like
`sin 2θ`, and `L₁₂(g)` is honest with norm `≤ Ci·Xn α g` by `N4Norm'.l12H`). -/
theorem n0row5u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨_, _⟩ := hE.pos
  obtain ⟨Cdz, hCdz, hDzF⟩ := Work.FTS.Nonlin.DzFstar_W
  obtain ⟨Ca, hCa, hang⟩ := Work.FTS.OpenPkg.angmul_field
  refine ⟨Ci * Ci * (Cdz + 1) * (Ca * 1000) + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hgsm hgm4 hgm5 hL12zero hdec hstar hell
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hQo4g : Work.FTS.VocabO.HQo α 4 g := ⟨hgsm, hgm4⟩
  -- ---------------------------------------------------------------------
  -- the radial factor `L₁₂(g)`: smoothness, honesty, norm bound
  -- ---------------------------------------------------------------------
  have hLsm : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  obtain ⟨hLmem, hLle⟩ := hN.l12H α hIoc g hQo4g hL12zero
  -- ---------------------------------------------------------------------
  -- the fixed profile: `D_zF_*` is `SmoothOpen` and `𝒲^{4,∞}` with norm `≤ Cdz·α`
  -- ---------------------------------------------------------------------
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDzFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFsm.Dz
  obtain ⟨hDzFmem, hDzFle⟩ := hDzF α hα hα1
  have hDzFle' : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
      ≤ (Cdz + 1) * α :=
    le_trans hDzFle (mul_le_mul_of_nonneg_right (by linarith) hα.le)
  -- ---------------------------------------------------------------------
  -- the coefficient `coef = c2m·L₁₂(g)`: `HQo α 4` with `Xn ≤ Ca·1000·Ci·Xn g`
  -- ---------------------------------------------------------------------
  set coef : Fn := fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z with hcoef
  have hcoefSm : Work.FTS.EllipticEst.SmoothOpen coef := by
    rw [hcoef]
    exact Work.FTS.NonlinRows.smoothOpen_c2m_L12 hα hell.smooth hell.V.1.1
  have hangc := hang α hα hα1 (fun θ => Work.Construction.c2m θ)
    (fun z (_ : ℝ) => Work.Construction.L12 g z) 1000 Work.FTS.NonlinRows.smoothOpen_c2m
    (fun θ hθ => le_trans (Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ) (by norm_num))
    (fun i hi hi4 θ hθ => Work.FTS.NonlinRows.DthIter_c2m_le_sin i hi hi4 hθ) hLsm hLmem
  have hcoefHk : Work.Spaces.HkMem α 4 coef := by
    rw [hcoef]
    exact hangc.1
  have hcoefXn : Work.FTS.Nonlin.Xn α coef
      ≤ (Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [hcoef]
    refine hangc.2.trans ?_
    exact mul_le_mul_of_nonneg_left hLle (by positivity)
  have hQo : Work.FTS.VocabO.HQo α 4 coef := ⟨hcoefSm, hcoefHk⟩
  -- ---------------------------------------------------------------------
  -- the `𝒲^{4,∞}`-product rule
  -- ---------------------------------------------------------------------
  have hprod := hN.wprod α hIoc (Work.Spaces.Dz (Work.Construction.Fstar α)) coef
    hDzFsm hDzFmem hQo
  -- ---------------------------------------------------------------------
  -- `N₀₅ᵃ` is `-` the product
  -- ---------------------------------------------------------------------
  have heq : Work.FTS.Nonlin.N05aF α g
      = -(fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a, hcoef, Pi.neg_apply]
    ring
  constructor
  · rw [heq]
    exact Work.FTS.NonlinRows.HkMem_neg' α 4 hprod.1
  · -- the norm bound
    have hXnprod : Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g)) := by
      refine hprod.2.trans ?_
      refine mul_le_mul ?_ hcoefXn (Work.Spaces.HkNorm_nonneg α 4 coef) ?_
      · exact mul_le_mul_of_nonneg_left hDzFle'
          (mul_nonneg hCi.le (Real.rpow_nonneg hα.le _))
      · exact mul_nonneg (mul_nonneg hCi.le (Real.rpow_nonneg hα.le _))
          (mul_nonneg (by linarith : (0 : ℝ) ≤ Cdz + 1) hα.le)
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    have hkey : Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
          * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g))
        = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
      rw [show Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g))
          = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (α ^ (-(1 / 2 : ℝ)) * α)
              * Work.FTS.Nonlin.Xn α g from by ring, hsqrt]
      ring
    have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hXg
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α g)
        = Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ) := by
          rw [heq]
          exact Work.FTS.EllipticEst.HkNorm_neg α 4
            (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ * coef z θ)
      _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((Cdz + 1) * α)
            * ((Ca * 1000) * (Ci * Work.FTS.Nonlin.Xn α g)) := hXnprod
      _ = (Ci * Ci * (Cdz + 1) * (Ca * 1000)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := hkey
      _ ≤ (Ci * Ci * (Cdz + 1) * (Ca * 1000) + 1)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right (by linarith) hS

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row7u =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row7`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

open Work.FTS.Galerkin (Fn)

open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular factor: `∂_θ c2m(θ) = -3 sin 2θ` and its `D_θ`-iterates -/

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

/-! ## Row 7 of the honest `N₀`-table -/

theorem n0row7u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α g) ∧
        |IP α (Work.FTS.Nonlin.N06F α g) g|
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨Cw, hCwpos, hW⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  refine ⟨Ct * (Cw + 11059200) + 1, by nlinarith [hE.pos.1, hCwpos], ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hgsm hg4 hg5 hL120 hdec hstar hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  obtain ⟨hWmem, hWle⟩ := hW α hα hα1
  set f : Fn := fun z θ => Work.Construction.c2m θ *
    Work.Construction.L12 (Work.Construction.Fstar α) z with hf
  have hfsm : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hf]; exact smoothOpen_c2mL12 α hα hα1
  have hWmem' : Work.Spaces.WlInfMem α 4 f := by rw [hf]; exact hWmem
  have hCTmem : Work.FTS.VocabO.CoefThMem 3 f := by
    rw [hf]; exact coefThMem_c2mL12 α hα hα1
  have hCTle : Work.FTS.VocabO.CoefTh 3 f ≤ 11059200 * α := by
    rw [hf]; exact coefTh_c2mL12_le α hα hα1
  have hDzgSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hgsm.Dz
  have hDzgMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.IPGen.HkMem_Dz_le hgsm hg5
  have hHQoDz : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dz g) := ⟨hDzgSm, hDzgMem⟩
  have hprod := hN.wprod α hIoc f (Work.Spaces.Dz g) hfsm hWmem' hHQoDz
  have hfun : Work.FTS.Nonlin.N06F α g = fun z θ => -(f z θ * Work.Spaces.Dz g z θ) := by
    funext z θ
    rw [hf]
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  constructor
  · have hneg : Work.Spaces.HkMem α 4 (-(fun z θ => f z θ * Work.Spaces.Dz g z θ)) := by
      unfold Work.Spaces.HkMem
      rw [Work.FTS.EllipticEst.HkIntegrand_neg]
      exact hprod.1
    rwa [hfun]
  · rw [hfun]
    have hQoprod : Work.FTS.VocabO.HQo α 4 (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
      ⟨Work.FTS.NonlinRows.smoothOpen_mul hfsm hDzgSm, hprod.1⟩
    have hQog : Work.FTS.VocabO.HQo α 4 g := ⟨hgsm, hg4⟩
    rw [hE.neg α hIoc (fun z θ => f z θ * Work.Spaces.Dz g z θ) g hQoprod hQog, abs_neg]
    have ht3 := hE.t3 α hIoc f g hfsm hWmem' hCTmem hgsm hg4 hg5 hdec
    refine ht3.trans ?_
    have hsum : Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f
        ≤ (Cw + 11059200) * α := by
      linarith
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) 1
      rw [Real.rpow_one] at h
      rw [Real.sqrt_eq_rpow, ← h]
      norm_num
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    calc Ct * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * ((Cw + 11059200) * α)
            * Work.FTS.Nonlin.Xn α g ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum ?_)
            (pow_nonneg hX 2)
          exact mul_nonneg hE.pos.1.le (Real.rpow_nonneg hα.le _)
      _ = (Ct * (Cw + 11059200)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
          rw [← hsqrt]; ring
      _ ≤ (Ct * (Cw + 11059200) + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
          refine mul_le_mul_of_nonneg_right (by linarith) ?_
          exact mul_nonneg (Real.sqrt_nonneg α) (pow_nonneg hX 2)

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.L12AbsLeHon =====
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
set_option linter.unusedVariables false

/-- **The uniform bounds on the `D_z`-iterates of `L₁₂(g)` in the honest class.**
`|D_z^b L₁₂(g)(z)| ≤ KL·Xn α g` for `b ≤ 4` and every `z > 0`: the `b = 0` case is the growth
estimate `(L₁₂ g z)² ≤ Kc X² min(z³, 1/z)`, and `b ≥ 1` is the angular-moment recursion
`D_z^{k+1}L₁₂(g) = -Qang g k` together with `(Qang g k z)² ≤ (∫Kθ²)·HkSq α 4 g`. -/
theorem L12_dzdIter_abs_le_open :
    ∃ KL : ℝ, 0 < KL ∧ ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
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
  intro α g hα hα1 hsm hmem h0 b hb z hz
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hXs : (Work.Spaces.HkSq α 4 g) = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    obtain ⟨hgrowth1, hgrowth2⟩ :=
      Work.FTS.StrongEps.E4R3.L12_sq_le_growth_honest α hα hα1 hsm hmem h0
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
  · have hrec := (Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest α hα hα1 hsm hmem h0).1
      (b - 1) (by omega) z hz
    have hbsucc : b = (b - 1) + 1 := by omega
    rw [hbsucc, hrec, abs_neg]
    have hq := Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open (α := α) (g := g) hα hα1
      hsm hmem (i := b - 1) (by omega) (z := z) hz
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

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon =====
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

/-! ## Smoothness, honesty and the `ℋ^k`-norms of the profile -/

/-- `ClassC` gives open-quadrant `C^∞`. -/
theorem CtxT.hSmoothOpen {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn}
    (h : CtxT Cs Ce α₂ α g Φs Φg) : Work.FTS.EllipticEst.SmoothOpen g := h.hg.reg

/-- The `ℋ^k`-honesty of the profile, for every `k ≤ 10`. -/
theorem CtxT.hkMem {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg)
    {k : ℕ} (hk : k ≤ 10) : Work.Spaces.HkMem α k g :=
  Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg k hk h.hg.mem10

theorem CtxT.hkMem4 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 4 g := h.hkMem (by norm_num)

theorem CtxT.hkMem5 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 5 g := h.hkMem (by norm_num)



/-- The honest `ℋ⁴`-class of the profile. -/
theorem CtxT.hqo {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg)
    {k : ℕ} (hk : k ≤ 10) : Work.FTS.VocabO.HQo α k g := ⟨h.hSmoothOpen, h.hkMem hk⟩


theorem CtxT.regQo5 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 g := h.hco.1


/-- `RegQo α (n+1) g` gives the ports `D_θ g` and `D_z g` in `RegQo α n` (hence in `ℋ^n`). -/
theorem CtxT.regQo_dth_dz {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 (Work.Spaces.Dth g) ∧
      Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 (Work.Spaces.Dz g) :=
  Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz h.hα h.regQo5

/-- The `D_θ`-slot of the profile is honest. -/
theorem CtxT.hkMemDth {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
  (h.regQo_dth_dz).1.2.1

/-- The `D_z`-slot of the profile is honest. -/
theorem CtxT.hkMemDz {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
  (h.regQo_dth_dz).2.2.1

theorem CtxT.hqoDth {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth g) :=
  ⟨(h.regQo_dth_dz).1.1, h.hkMemDth⟩

theorem CtxT.hvanish {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.VanishTheta g := h.hco.2.1

theorem CtxT.haxis {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    ∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 ∧ Work.Spaces.pz g 0 θ = 0 := h.hco.2.2.1

theorem CtxT.hL12 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Construction.L12 g 0 = 0 := h.hco.2.2.2

theorem CtxT.hbdry {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.Nonlin.BdryTraces α 6 g := h.hg.tr

/-! ## The two elliptic packages -/

theorem CtxT.hstar {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs := h.hs

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.NRow2_honest_Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **The `z`-slices of the mixed derivatives of a `SmoothOpen` function are differentiable
on the open half-line.**  This is the open-quadrant analogue of
`Work.FTS.LocData.SmoothQuad.differentiableAt_slice_mixed`. -/
theorem smoothOpen_differentiableAt_slice_mixed {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (b i : ℕ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.mixed b i G z' θ) z :=
  (((hG.mixed b i).curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- **The pointwise Leibniz rule for a radial factor, in the open-quadrant class.**  For
`j ≤ 4`, `z > 0`, `θ ∈ (0,π/2)`, if the iterates `D_z^b r`, `b ≤ 3`, of the radial function `r`
are differentiable on the open half-line and `h` is `C^∞` on the open quadrant, then

  `mixed j i (r·h) z θ = Σ_{b≤j} C(j,b)·(D_z^b r z)·(mixed (j-b) i h z θ)`.

This is `Work.FTS.Nonlinear.Pieces.radial_leibniz` with the interior class
`Work.FTS.LocData.SmoothQuad h` weakened to `SmoothOpen h`. -/
theorem radial_leibniz_open (r : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (j i : ℕ) (hj : j ≤ 4) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hr : ∀ b : ℕ, b ≤ 3 → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b r) z') :
    Work.Spaces.mixed j i (fun z θ => r z * h z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i h z θ) := by
  have hθrule : Work.Spaces.DthIter i (fun z θ => r z * h z θ)
      = fun z θ => r z * Work.Spaces.DthIter i h z θ :=
    Work.FTS.Nonlinear.Pieces.dthIter_mul_radial r h i
  have hmix : Work.Spaces.mixed j i (fun z θ => r z * h z θ) z θ
      = Work.Elliptic.DzdIter j
          (fun z' => r z' * Work.Spaces.DthIter i h z' θ) z := by
    rw [Work.Spaces.mixed, hθrule]
    exact Work.FTS.Nonlinear.Pieces.DzIter_slice
      (fun z θ' => r z * Work.Spaces.DthIter i h z θ') j z θ
  rw [hmix]
  -- the `h`-side is differentiable on the open half-line
  have hdiff : ∀ b : ℕ, b < j → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z' => Work.Spaces.DthIter i h z' θ)) z' := by
    intro b hb z' hz'
    have h1 : DifferentiableAt ℝ (fun u => Work.Spaces.mixed b i h u θ) z' :=
      smoothOpen_differentiableAt_slice_mixed hsm b i (by rw [Set.mem_Ioi] at hz'; exact hz') hθ
    have h2 : (fun u => Work.Spaces.mixed b i h u θ)
        = fun u => Work.Elliptic.DzdIter b (fun z' => Work.Spaces.DthIter i h z' θ) u := by
      funext u
      exact Work.FTS.Nonlinear.Pieces.DzIter_slice (Work.Spaces.DthIter i h) b u θ
    rwa [h2] at h1
  have hr' : ∀ b : ℕ, b < j → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b r) z' :=
    fun b hb z' hz' => hr b (by omega) z' hz'
  rw [Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j r
    (fun z' => Work.Spaces.DthIter i h z' θ) hr' hdiff z hz]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [show Work.Elliptic.DzdIter (j - b) (fun z' => Work.Spaces.DthIter i h z' θ) z
      = Work.Spaces.mixed (j - b) i h z θ from
    (Work.FTS.Nonlinear.Pieces.DzIter_slice (Work.Spaces.DthIter i h) (j - b) z θ).symm]

/-- Cauchy–Schwarz for a binomial slot sum: `(∑ c_b(x_by_b))² ≤ 256·card·Kc·∑ y_b²` when the
coefficients `c_b` are bounded by `16` and the first factors satisfy `x_b² ≤ Kc`. -/
theorem slot_sum_sq_le {ι : Type*} (s : Finset ι) (c x y : ι → ℝ) {Kc : ℝ} (hK : 0 ≤ Kc)
    (hc : ∀ b ∈ s, |c b| ≤ 16) (hx : ∀ b ∈ s, (x b) ^ 2 ≤ Kc) :
    (∑ b ∈ s, c b * (x b * y b)) ^ 2 ≤ 256 * (s.card : ℝ) * Kc * ∑ b ∈ s, (y b) ^ 2 := by
  have h1 : (∑ b ∈ s, c b * (x b * y b)) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (c b * (x b * y b)) ^ 2 :=
    _root_.sq_sum_le_card_mul_sum_sq
  have h2 : ∑ b ∈ s, (c b * (x b * y b)) ^ 2 ≤ ∑ b ∈ s, 256 * (Kc * (y b) ^ 2) := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hc2 : (c b) ^ 2 ≤ 256 := by
      have h := hc b hb
      nlinarith [sq_nonneg (c b), sq_abs (c b), abs_nonneg (c b)]
    have hx2 := hx b hb
    have hy2 : 0 ≤ (y b) ^ 2 := sq_nonneg _
    have hxy : (x b) ^ 2 * (y b) ^ 2 ≤ Kc * (y b) ^ 2 :=
      mul_le_mul_of_nonneg_right hx2 hy2
    have hcx : (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * (Kc * (y b) ^ 2) := by
      have h1 : (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * ((x b) ^ 2 * (y b) ^ 2) :=
        mul_le_mul_of_nonneg_right hc2 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      calc (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * ((x b) ^ 2 * (y b) ^ 2) := h1
        _ ≤ 256 * (Kc * (y b) ^ 2) := mul_le_mul_of_nonneg_left hxy (by norm_num)
    calc (c b * (x b * y b)) ^ 2 = (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) := by ring
      _ ≤ 256 * (Kc * (y b) ^ 2) := hcx
  have h3 : ∑ b ∈ s, 256 * (Kc * (y b) ^ 2) = 256 * Kc * ∑ b ∈ s, (y b) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  calc (∑ b ∈ s, c b * (x b * y b)) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (c b * (x b * y b)) ^ 2 := h1
    _ ≤ (s.card : ℝ) * (256 * Kc * ∑ b ∈ s, (y b) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_of_eq h3)) (Nat.cast_nonneg _)
    _ = 256 * (s.card : ℝ) * Kc * ∑ b ∈ s, (y b) ^ 2 := by ring

end Work.FTS.StrongEps.E4R3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.gam_rad_package_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GamRadAux

open Work.FTS.CoercivityFix.Transfer.E2pkg

/-- The angular majorant `angMaj α θ = sin(2θ)^{-η} + sin(2θ)^{2α/5-γ}` is integrable on `Iθ`.
(This is the local copy of the `private` lemma `integrableOn_angMaj` of `HkMemGam.lean`.) -/
lemma integrableOn_angMaj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => angMaj α θ) Work.Spaces.Iθ := by
  have h1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have h2 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
      Work.Spaces.Iθ := by
    refine (Work.Spaces.sin_two_rpow (2 * α / 5 - Work.Spaces.gam α) ?_ ?_).1
    · rw [Work.Spaces.gam]; linarith
    · rw [Work.Spaces.gam]; linarith
  refine (h1.add h2).congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Pi.add_apply, angMaj, Work.FTS.Nonlinear.RadialProd.smE]

end GamRadAux

open Work.FTS.CoercivityFix.Transfer.E2pkg (angMaj radMaj Qd)

theorem gam_rad_package_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} {n : ℕ}
    (hn : n ≤ 3)
    (hA : ContDiffOn ℝ 4 (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => Work.Spaces.Gam α θ
        * Work.FTS.CoercivityFix.Transfer.radS α f z)) Work.FTS.CoercivityFix.Transfer.E2pkg.Qd ∧
      Work.Spaces.HkMem α n (fun z θ => Work.Spaces.Gam α θ
        * Work.FTS.CoercivityFix.Transfer.radS α f z) := by
  have hR : ContDiffOn ℝ 3 (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.radS α f z)
      (Set.Ioi 0) :=
    Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three α hα hα1 hA
  have hR' : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Transfer.radS α f p.1)
      Qd :=
    (hR.comp contDiffOn_fst (fun p hp => hp.1)).of_le (by exact_mod_cast hn)
  have hG : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Qd :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_Gam_Qd α n
  have hfun : Function.uncurry
        (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
      = fun p : ℝ × ℝ => Work.Spaces.Gam α p.2
          * Work.FTS.CoercivityFix.Transfer.radS α f p.1 := rfl
  have hsm : ContDiffOn ℝ n (Function.uncurry
      (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)) Qd := by
    rw [hfun]
    exact hG.mul hR'
  refine ⟨hsm, ?_⟩
  -- ### The `ℋ^n` membership, via `HkMem_of_majorant` and the majorant `M`
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z))
        Work.Spaces.Iθ := by
    intro z hz
    have h := MeasureTheory.Integrable.mul_const
      (GamRadAux.integrableOn_angMaj α hα hα1) (radMaj α f n z)
    exact MeasureTheory.Integrable.const_mul h (4 * 10 ^ 10)
  have hMz : IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z))
      Work.Spaces.Iz := by
    have h0 : IntegrableOn (fun z : ℝ => radMaj α f n z) Work.Spaces.Iz := hint
    have hconst : IntegrableOn (fun z : ℝ =>
        (4 * 10 ^ 10 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * radMaj α f n z)
        Work.Spaces.Iz :=
      MeasureTheory.Integrable.const_mul h0 _
    refine MeasureTheory.IntegrableOn.congr_fun hconst (fun z hz => ?_) measurableSet_Ici
    have h1 : (∫ θ in Work.Spaces.Iθ, 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z))
        = 4 * 10 ^ 10 * (∫ θ in Work.Spaces.Iθ, angMaj α θ * radMaj α f n z) :=
      MeasureTheory.integral_const_mul _ _
    have h2 : (∫ θ in Work.Spaces.Iθ, angMaj α θ * radMaj α f n z)
        = (∫ θ in Work.Spaces.Iθ, angMaj α θ) * radMaj α f n z :=
      MeasureTheory.integral_mul_const _ _
    rw [h1, h2]
    ring
  refine Work.FTS.LocData.HkMem_of_majorant α n ?_ hMslice hMz ?_
  · exact Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont
      (Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn hsm) α
  · intro z hz θ hθ
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.HkIntegrand_gam_rad_le α hα hα1 hn f z hz θ hθ

end Work.FTS.StrongEps.EpsE4Thr.E2O
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSExp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000


/-- **The expansion of `D_z^j (radS α f)`** on `(0,∞)`, `j ≤ 3`, in the open class. -/
theorem radS_DzdIter_eq_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f)
    (hl12 : Work.Construction.L12 f 0 = 0) {j : ℕ} (hj : j ≤ 3) :
    ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z
      = -(Work.FTS.CoercivityFix.Transfer.E2pkg.W1 α f j z)
        + Work.FTS.CoercivityFix.Transfer.E2pkg.W2 α f j z
        + Work.FTS.CoercivityFix.Transfer.E2pkg.W3 α f j z := by
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem5
  have hsmA5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) IoiA :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α
  have hsmB5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) IoiA :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampB_five α
  -- the three summands
  set U1 : ℝ → ℝ := fun z =>
    -(Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) with hU1
  set U2 : ℝ → ℝ := fun z =>
    Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Elliptic.Qang f 0 z with hU2
  set U3 : ℝ → ℝ := fun z =>
    (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
      * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 with hU3
  -- differentiability of the coefficient iterates
  have hA1diff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ
        (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)) z := by
    intro c hc z hz
    have hdc : Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)
        = Work.Elliptic.DzdIter (c + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) := by
      rw [show Work.FTS.CoercivityFix.Transfer.dAmpA α
          = Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampA α) from rfl]
      exact Work.FTS.Nonlinear.Pieces.DzdIter_add c 1 _
    rw [hdc]
    have hc4 : c + 1 ≤ 4 := by omega
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_five
      hsmA5 hc4 hz
  have hA2diff : ∀ c ≤ 4, ∀ z ∈ IoiA,
      DifferentiableAt ℝ
        (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampA α)) z :=
    fun c hc z hz =>
      Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_five
        hsmA5 hc hz
  have hsmL : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) IoiA :=
    contDiffOn_four_L12f α hα hα1 hO hmem5
  have hLdiff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f)) z := by
    intro c hc z hz
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_general
      (N := 4) hsmL (by omega) hz
  have hQdiff : ∀ c ≤ 2, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Elliptic.Qang f 0 z)) z := by
    intro c hc z hz
    refine (differentiableAt_Qang_open hO hmem4 hc hz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact DzdIter_Qang_open hO hmem4 c (by omega) w hw
  have hA3sm : ContDiffOn ℝ 4
      (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α) IoiA := by
    have h1 : (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
        = fun z => Work.Spaces.Zop^[1] (Work.FTS.CoercivityFix.Transfer.ampB α) z
            / Work.Spaces.c α := by
      funext z; rfl
    rw [h1]
    exact (Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' 1 4
      (hsmB5.of_le (Nat.cast_le.mpr (by norm_num : 5 ≤ 5)))).div_const _
  have hA3diff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z : ℝ =>
        Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)) z := by
    intro c hc z hz
    have hc4 : c + 1 ≤ 4 := by omega
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_general
      (N := 4) hA3sm hc4 hz
  have hU12 : ∀ b < j, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (U1 + U2)) z := by
    intro b hb z hz
    have hu : ∀ c ≤ b, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c U1) z' := by
      intro c hc z' hz'
      have hcons : U1 = fun z => (-1 : ℝ) *
          (Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) := by
        rw [hU1]; funext w; ring
      rw [hcons]
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
      exact (Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA1diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hLdiff c (by omega) z'' hz'') hz').const_mul (-1)
    have hv : ∀ c ≤ b, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c U2) z' := by
      intro c hc z' hz'
      exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA2diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hQdiff c (by omega) z'' hz'') hz'
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_add_of (j := b) hu hv hz
  have hU3diff : ∀ b < j, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b U3) z := by
    intro b hb z hz
    have hcons : U3 = fun z => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        * (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α) := by
      rw [hU3]; funext w; ring
    rw [hcons, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
    exact (hA3diff b (by omega) z hz).const_mul _
  -- the expansion
  have hsplit : ∀ z ∈ IoiA,
      Work.FTS.CoercivityFix.Transfer.radS α f z = (U1 + U2 + U3) z := by
    intro z hz
    have h := radS_split_O α hα hα1 hO hmem4 hl12 z hz
    rw [h]
    simp only [hU1, hU2, hU3, Pi.add_apply]
  have hexp : ∀ z ∈ IoiA,
      Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z
        = Work.Elliptic.DzdIter j (U1 + U2 + U3) z :=
    fun z hz => Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hsplit j z hz
  have e1 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (U1 + U2 + U3) z
      = Work.Elliptic.DzdIter j (U1 + U2) z + Work.Elliptic.DzdIter j U3 z := by
    intro z hz
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j (U1 + U2) U3 hU12 hU3diff
      z hz
  have e2 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (U1 + U2) z
      = Work.Elliptic.DzdIter j U1 z + Work.Elliptic.DzdIter j U2 z := by
    intro z hz
    have h1 : ∀ b < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b U1) z' := by
      intro b hb z' hz'
      have hcons : U1 = fun z => (-1 : ℝ) *
          (Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) := by
        rw [hU1]; funext w; ring
      rw [hcons]
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
      exact (Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA1diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hLdiff c (by omega) z'' hz'') hz').const_mul (-1)
    have h2 : ∀ b < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b U2) z' := by
      intro b hb z' hz'
      exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA2diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hQdiff c (by omega) z'' hz'') hz'
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j U1 U2 h1 h2 z hz
  have e3 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U1 z
      = -(Work.FTS.CoercivityFix.Transfer.E2pkg.W1 α f j z) := by
    intro z hz
    have hub : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ
          (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)) z' :=
      fun c hc z' hz' => hA1diff c (by omega) z' hz'
    have hvb : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f)) z' :=
      fun c hc z' hz' => hLdiff c (by omega) z' hz'
    have hlei := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j
      (Work.FTS.CoercivityFix.Transfer.dAmpA α) (Work.Coercivity.L12f f) hub hvb z hz
    have hA1 : ∀ b, Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.dAmpA α)
        = Work.Elliptic.DzdIter (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) := by
      intro b
      rw [show Work.FTS.CoercivityFix.Transfer.dAmpA α
          = Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampA α) from rfl]
      exact Work.FTS.Nonlinear.Pieces.DzdIter_add b 1 _
    have hneg : Work.Elliptic.DzdIter j U1 z = - Work.Elliptic.DzdIter j (fun w =>
        Work.FTS.CoercivityFix.Transfer.dAmpA α w * Work.Coercivity.L12f f w) z := by
      rw [hU1, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_neg]
    rw [hneg, hlei, Work.FTS.CoercivityFix.Transfer.E2pkg.W1]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hA1 b]
    ring
  have e4 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U2 z
      = Work.FTS.CoercivityFix.Transfer.E2pkg.W2 α f j z := by
    intro z hz
    have hub : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ
          (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampA α)) z' :=
      fun c hc z' hz' => hA2diff c (by omega) z' hz'
    have hvb : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Elliptic.Qang f 0 z)) z' :=
      fun c hc z' hz' => hQdiff c (by omega) z' hz'
    have hlei := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j
      (Work.FTS.CoercivityFix.Transfer.ampA α) (fun z => Work.Elliptic.Qang f 0 z) hub hvb z hz
    rw [show U2 = fun z => Work.FTS.CoercivityFix.Transfer.ampA α z
        * Work.Elliptic.Qang f 0 z from hU2, hlei, Work.FTS.CoercivityFix.Transfer.E2pkg.W2]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [DzdIter_Qang_open hO hmem4 (j - b) (by
      have := Finset.mem_range.mp hb; omega) z hz]
    ring
  have e5 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U3 z
      = Work.FTS.CoercivityFix.Transfer.E2pkg.W3 α f j z := by
    intro z hz
    have hfun : U3 = fun z => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        * ((Work.Spaces.c α)⁻¹
            * Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampB α) z) := by
      rw [hU3]; funext w
      simp only [Work.FTS.CoercivityFix.Transfer.dAmpB, Work.Elliptic.DzdIter_succ,
        Work.Elliptic.DzdIter_zero, Work.Elliptic.Dzd]
      ring
    rw [hfun, Work.FTS.CoercivityFix.Transfer.E2pkg.W3,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul,
      show Work.Elliptic.DzdIter j (Work.Elliptic.DzdIter 1
            (Work.FTS.CoercivityFix.Transfer.ampB α))
          = Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) from
        Work.FTS.Nonlinear.Pieces.DzdIter_add j 1 _]
    ring
  intro z hz
  rw [hexp z hz, e1 z hz, e2 z hz, e3 z hz, e4 z hz, e5 z hz]

/-! ## The pointwise majorant -/

end Work.FTS.StrongEps.EpsE4Thr.E2O
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.LintegralProdThShiftLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The product bound for the angular shift `lintegral_thShift_le`

`JepsHkMem.lintegral_thShift_le` bounds the *angular* lintegral of a shifted profile:

  `∫⁻_{θ ∈ Iθ} U (thShift θ p) ≤ e^{3|p|} ∫⁻_{θ ∈ Iθ} U θ`     (`Iθ = [0, π/2]`).

Here we integrate the same inequality in `p` over the shift interval `[-ε, ε]`.  Since the
inequality is *uniform in* `θ` (`thShift` acts on `θ` alone), Fubini on the product measure
gives, for every `Measurable U`,

  `∫⁻_{(θ,p) ∈ Iθ × [-ε,ε]} U (thShift θ p) ≤ e^{3ε} · (2ε) · ∫⁻_{θ ∈ Iθ} U θ`.

## Proof

1. **Fubini.** `MeasureTheory.lintegral_prod_symm` turns the integral over
   `(volume.restrict Iθ).prod (volume.restrict [-ε,ε])` into `∫⁻ p, ∫⁻ θ ∈ Iθ, …`.  The required
   a.e. measurability of the uncurried integrand is
   `Measurable.aemeasurable.comp_aemeasurable` applied to
   `FstarJepsSmoothAux.aemeasurable_thShift_prod` (the angular shift is a.e. continuous on the
   conull set `{θ ∈ (0,π/2)}` of `Iθ`).

2. **Pointwise-a.e. bound in `p`.**  For a.e. `p` (namely for `p ∈ [-ε,ε]`, where `|p| ≤ ε`)
   the inner integral is `≤ ofReal (e^{3|p|}) · J ≤ ofReal (e^{3ε}) · J`
   (`J := ∫⁻ θ ∈ Iθ, U θ`).

3. **Integration in `p`.**  The bound is a constant in `p`, so
   `∫⁻ p, C * J = C * J * μ([-ε,ε]) = C * J * ofReal (2ε)`, and
   `ofReal (e^{3ε}) * ofReal (2ε) = ofReal (e^{3ε} · 2ε)`.

`hε` is not needed: the statement also holds for `ε ≤ 0` (the shift interval is then empty and
`2ε ≤ 0` makes the constant `ofReal (…) = 0`).
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

theorem LintegralProdThShiftLe {ε : ℝ} (hε : 0 < ε) {U : ℝ → ENNReal} (hU : Measurable U) :
    (∫⁻ x : ℝ × ℝ, U (Work.FTS.StrongEps.thShift x.1 x.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))))
      ≤ ENNReal.ofReal (Real.exp (3 * ε) * (2 * ε)) * ∫⁻ θ in Work.Spaces.Iθ, U θ := by
  have _hε := hε
  classical
  -- a.e. measurability of the uncurried integrand, from `aemeasurable_thShift_prod`
  have hAEM : AEMeasurable (fun z : ℝ × ℝ => U (Work.FTS.StrongEps.thShift z.1 z.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) := by
    simpa only [Function.comp_def] using
      hU.aemeasurable.comp_aemeasurable
        (Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.aemeasurable_thShift_prod (ε := ε))
  -- Fubini on the product measure
  have hswap : (∫⁻ z : ℝ × ℝ, U (Work.FTS.StrongEps.thShift z.1 z.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))))
      = ∫⁻ p, (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p))
          ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε)) :=
    MeasureTheory.lintegral_prod_symm
      (fun z : ℝ × ℝ => U (Work.FTS.StrongEps.thShift z.1 z.2)) hAEM
  rw [hswap]
  set J : ENNReal := ∫⁻ θ in Work.Spaces.Iθ, U θ with hJ
  set C : ENNReal := ENNReal.ofReal (Real.exp (3 * ε)) with hC
  -- the pointwise-a.e. bound in `p`
  have hinner : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε)),
      (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p)) ≤ C * J := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with p hp
    have habs : |p| ≤ ε := abs_le.mpr hp
    calc (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p))
        ≤ ENNReal.ofReal (Real.exp (3 * |p|)) * J :=
          Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le U p
      _ ≤ C * J := by
          rw [hC]
          exact mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))) zero_le
  calc ∫⁻ p, (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p))
        ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε))
      ≤ ∫⁻ p, C * J ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε)) :=
        MeasureTheory.lintegral_mono_ae hinner
    _ = C * J * ENNReal.ofReal (2 * ε) := by
        rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Icc, show ε - (-ε) = 2 * ε by ring]
    _ = ENNReal.ofReal (Real.exp (3 * ε) * (2 * ε)) * J := by
        rw [hC, ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ThShiftSubst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThShiftSubst`

The angular substitution bound used in the smoothness of `Fstar (Jeps ρ ε W)`: the critical
weight `sinCos2 θ = sin θ cos²θ` is bounded by `1`, and the log-coordinate shift
`θ ↦ thShift θ q = arctan (tan θ · e^{-q})` changes the angular measure by at most `e^{3|q|}`
(`JepsHkMem.lintegral_thShift_le`).  Hence

  `∫_{θ ∈ (0,π/2)} sinCos2 θ · H (thShift θ q) ≤ e^{3|q|} ∫_{θ ∈ (0,π/2)} H θ`
  `  ≤ e^{3ε} ∫_{θ ∈ (0,π/2)} H θ`   for `|q| ≤ ε`,

for every nonnegative `H` which is integrable on `(0, π/2)`.

Everything is first done for `lintegral`s (`ofReal` of the integrand), where no measurability of
`H ∘ thShift` is ever needed, and only at the very end is the Bochner integral compared with the
`toReal` of the corresponding `lintegral` (`integral_le_toReal_lintegral_of_nonneg_ae`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux




/-- The closed angular interval `Iθ = [0, π/2]` and the open one `(0, π/2)` differ by a null
set, so their `lintegral`s agree. -/
theorem lintegral_Iθ_eq_Ioo (U : ℝ → ENNReal) :
    (∫⁻ θ in Work.Spaces.Iθ, U θ) = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), U θ :=
  MeasureTheory.setLIntegral_congr
    (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := (Real.pi / 2))).symm


end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.ProjSlotDerivRaw =====
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


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Hadd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.EpsZero

theorem Hadd {α Ce Cs μ lam : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {Φs : Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hLin : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PLin α f)) (Set.Ioi 0))
    (hN0 : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PN0 α f)) (Set.Ioi 0))
    (hN : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PN α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f))) (Set.Ioi 0))
    (hNs : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PNs μ lam f)) (Set.Ioi 0))
    (hK : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PK (Work.FTS.StrongEps.EpsZero.Pmubar α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f)) α)) (Set.Ioi 0))
    (hLinθ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PLin α f z θ / z) Work.Spaces.Iθ)
    (hN0θ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PN0 α f z θ / z) Work.Spaces.Iθ)
    (hNθ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PN α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f) z θ / z) Work.Spaces.Iθ)
    (hNsθ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PNs μ lam f z θ / z) Work.Spaces.Iθ)
    (hKθ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PK (Work.FTS.StrongEps.EpsZero.Pmubar α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f)) α z θ / z) Work.Spaces.Iθ) :
    Work.Construction.L12 (fun z θ => Work.FTS.StrongEps.EpsZero.PLin α f z θ + Work.FTS.StrongEps.EpsZero.PgRHS α μ lam f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f) z θ) 0
      = Work.Construction.L12 (Work.FTS.StrongEps.EpsZero.PLin α f) 0
        - Work.FTS.StrongEps.EpsZero.Pmubar α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f) * Work.Construction.L12 (Work.Construction.AK α) 0
        + Work.Construction.L12 (Work.FTS.StrongEps.EpsZero.PN0 α f) 0
        + Work.Construction.L12 (Work.FTS.StrongEps.EpsZero.PN α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f)) 0
        + Work.Construction.L12 (Work.FTS.StrongEps.EpsZero.PNs μ lam f) 0 := by
  -- The five summands of `L₁₂(PLin + PgRHS)`: `PLin`, the `μ̄`-piece `PK μ̄ α = -μ̄·AK α`,
  -- then `N₀`, `N`, `N_*`.
  let F : Fin 5 → ℝ → ℝ → ℝ :=
    ![PLin α f, PK (Pmubar α f (PPsi E Φs f)) α, PN0 α f,
      PN α f (PPsi E Φs f), PNs μ lam f]
  -- The integrability inputs of the sum rule: the angular slices for `z > 0`,
  -- and the radial densities on `Ioi 0`.
  have hθ : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * F i z θ / z)
        Work.Spaces.Iθ := by
    intro i _ z hz
    fin_cases i
    · exact hLinθ z hz
    · exact hKθ z hz
    · exact hN0θ z hz
    · exact hNθ z hz
    · exact hNsθ z hz
  have hdens : ∀ i ∈ (Finset.univ : Finset (Fin 5)),
      MeasureTheory.IntegrableOn (fun z => Work.Construction.L12dens (F i) z)
        (Set.Ioi 0) := by
    intro i _
    fin_cases i
    · exact hLin
    · exact hK
    · exact hN0
    · exact hN
    · exact hNs
  -- Additivity of `L₁₂` over the five summands.
  have hsum := Work.FTS.Apriori.ZeroMode.L12_sum_zero (Finset.univ : Finset (Fin 5)) F hθ hdens
  -- The pointwise identity `PLin + PgRHS = ∑_i F_i`.
  have hsplit : (fun z θ : ℝ => PLin α f z θ + PgRHS α μ lam f (PPsi E Φs f) z θ)
      = fun z θ : ℝ => ∑ i ∈ (Finset.univ : Finset (Fin 5)), F i z θ := by
    funext z θ
    simp only [Fin.sum_univ_five, F, Fin.isValue, Matrix.cons_val, PgRHS, Work.Construction.gRHS, Pmubar, PK, PN0, PN,
      PNs, PLin]
    ring
  -- The `μ̄`-piece: homogeneity of `L₁₂` in a constant.
  have hKterm : Work.Construction.L12 (PK (Pmubar α f (PPsi E Φs f)) α) 0
      = -Pmubar α f (PPsi E Φs f) * Work.Construction.L12 (Work.Construction.AK α) 0 := by
    show Work.FM.L12 Work.Spaces.K
        (fun s θ => -Pmubar α f (PPsi E Φs f) * Work.Construction.AK α s θ) 0
      = -Pmubar α f (PPsi E Φs f)
        * Work.FM.L12 Work.Spaces.K (Work.Construction.AK α) 0
    exact Work.FM.L12_const_mul
  rw [hsplit, hsum, Fin.sum_univ_five]
  simp only [F, Fin.isValue, Matrix.cons_val]
  rw [hKterm]
  ring

end Work.FTS.StrongEps.EpsZero
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.AngRad5.AngRadHkMem5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.AngRad5

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The angular majorant of the engine -/

/-- The angular majorant of the level-`5` engine:
`B0²·sin(2θ)^{-η} + 5·B1²·G(θ)²·sin(2θ)^{-γ(α)}`.  It is the `θ`-only factor produced by the
pointwise separation lemma `HkIntegrand_ang_rad_le5`. -/
def AngMaj (α B0 B1 : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ :=
  B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
    + 5 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ


/-- Integrability in `θ` of the angular majorant on `Iθ`: `smE` is integrable
(`AuxAngRad.integrableOn_smE`) and `G²·smG` is integrable by hypothesis. -/
theorem integrableOn_AngMaj {α B0 B1 : ℝ} {G : ℝ → ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (AngMaj α B0 B1 G) Work.Spaces.Iθ := by
  have h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        + (5 * B1 ^ 2) * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
      Work.Spaces.Iθ :=
    (Work.FTS.NonlinRows.AuxAngRad.integrableOn_smE.const_mul (B0 ^ 2)).add
      (hGint.const_mul (5 * B1 ^ 2))
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Icc
  rw [AngMaj]
  ring

/-- The `θ`-integral of the angular majorant splits into the two pieces
`B0²·K_θ + 5·B1²·∫_θ G²·smG`. -/
theorem integral_AngMaj {α B0 B1 : ℝ} {G : ℝ → ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ)
      = B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth
        + 5 * B1 ^ 2 * (∫ θ in Work.Spaces.Iθ,
            G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
  have hEq : (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ)
      = ∫ θ in Work.Spaces.Iθ, (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + (5 * B1 ^ 2) * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [AngMaj]
    ring
  rw [hEq, MeasureTheory.integral_add
      (Work.FTS.NonlinRows.AuxAngRad.integrableOn_smE.const_mul (B0 ^ 2))
      (hGint.const_mul (5 * B1 ^ 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  simp only [Work.FTS.Nonlinear.RadialProd.Kth]

/-- The `θ`-integral of the angular majorant is at most `B0²·10⁴ + 5·B1²·M`, using
`K_θ ≤ 10⁴` (`StrongEps.H5.Kth_le_1e4`) and the mass bound `∫_θ G²·smG ≤ M`. -/
theorem integral_AngMaj_le {α B0 B1 M : ℝ} {G : ℝ → ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hmass : (∫ θ in Work.Spaces.Iθ,
        G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ M)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) :
    (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ) ≤ B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M := by
  rw [integral_AngMaj hGint]
  have hKth : Work.FTS.Nonlinear.RadialProd.Kth ≤ 10 ^ 4 := Work.FTS.StrongEps.H5.Kth_le_1e4
  have h1 : B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth ≤ B0 ^ 2 * 10 ^ 4 :=
    mul_le_mul_of_nonneg_left hKth (sq_nonneg B0)
  have h2 : 5 * B1 ^ 2 * (∫ θ in Work.Spaces.Iθ,
        G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ 5 * B1 ^ 2 * M :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  linarith

/-! ## The pointwise separation -/

/-- The pointwise separation of the `ℋ⁵`-integrand of the product `a·r`, with the general
angular majorant `G` of the engine: the statement of `HkIntegrand_ang_rad_le5` with `n = 5`
and its angular factor replaced by `Rint₅ · AngMaj`. -/
theorem hkIntegrand_ang_le5 {α B0 B1 : ℝ} {a r G : ℝ → ℝ}
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) z θ
      ≤ Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ := by
  have h := Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5 (n := 5) le_rfl
    (α := α) (a := a) (r := r) (G := G) (B0 := B0) (B1 := B1) (z := z) ha0 ha1 hθ
  simpa only [Work.FTS.StrongEps.H5.Rint5, AngMaj] using h

/-! ## The level-`5` radial density -/

/-- For a radial lift that is `ℋ⁵`-honest, the level-`5` radial density `Rint₅ r` is integrable
on `Iz` and its integral is at most `HkSq α 5` of the lift.  This is the exact value
`HkSq_rad_eq5` (`HkSq α 5 (radial) = (∫_z Rint₅ r)·K_θ`) together with `K_θ ≥ 1`. -/
theorem rint5_mem {α : ℝ} {r : ℝ → ℝ}
    (hrmem : Work.Spaces.HkMem α 5 (fun z (_ : ℝ) => r z)) :
    MeasureTheory.IntegrableOn (Work.FTS.StrongEps.H5.Rint5 r) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
        ≤ Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z) := by
  have hKth : Work.FTS.Nonlinear.RadialProd.Kth ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one Work.FTS.Nonlinear.RadialProd.one_le_Kth)
  -- the `θ`-slice integral of the radial lift's integrand
  have hinner : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 5 (fun z θ => r z) z θ)
      = Work.FTS.StrongEps.H5.Rint5 r z * Work.FTS.Nonlinear.RadialProd.Kth := by
    intro z
    have hkey : (fun θ : ℝ => Work.Spaces.HkIntegrand α 5 (fun z θ => r z) z θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => Work.FTS.StrongEps.H5.Rint5 r z
            * Work.FTS.Nonlinear.RadialProd.smE θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Work.Elliptic.HkIntegrand_rad α 5 r z hθ, Work.FTS.StrongEps.H5.Rint5,
        Finset.sum_mul]
      simp only [Work.FTS.Nonlinear.RadialProd.smE]
    rw [MeasureTheory.integral_congr_ae hkey, MeasureTheory.integral_const_mul]
    rfl
  have h1 : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 5 (fun z θ => r z) z θ) Work.Spaces.Iz := hrmem.2
  have h2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.StrongEps.H5.Rint5 r z
        * Work.FTS.Nonlinear.RadialProd.Kth) Work.Spaces.Iz :=
    h1.congr (Filter.Eventually.of_forall hinner)
  refine ⟨?_, ?_⟩
  · have h3 := h2.div_const Work.FTS.Nonlinear.RadialProd.Kth
    refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
    show Work.FTS.StrongEps.H5.Rint5 r z * Work.FTS.Nonlinear.RadialProd.Kth
      / Work.FTS.Nonlinear.RadialProd.Kth = Work.FTS.StrongEps.H5.Rint5 r z
    rw [mul_div_cancel_right₀ _ hKth]
  · have hSq : Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)
        = (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
            * Work.FTS.Nonlinear.RadialProd.Kth := Work.FTS.StrongEps.H5.HkSq_rad_eq5 α r
    have hnn : 0 ≤ ∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z :=
      MeasureTheory.integral_nonneg (fun z => Work.FTS.StrongEps.H5.Rint5_nonneg r z)
    calc (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
        ≤ (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
            * Work.FTS.Nonlinear.RadialProd.Kth := by
          nth_rewrite 1 [← mul_one (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongEps.H5.Rint5 r z)]
          exact mul_le_mul_of_nonneg_left Work.FTS.Nonlinear.RadialProd.one_le_Kth hnn
      _ = Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z) := hSq.symm

/-! ## The engine -/

theorem AngRadHkMem5 : Work.FTS.StrongEps.H5.AngRad5.AngRadEngine5 := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα hα1 a r G B0 B1 M Crad ha hr hGnn hGint hB0 hB1 hM hCrad ha0 ha1 hmass
    hrmem hCradbd
  -- ### the angular data
  have hAi : MeasureTheory.IntegrableOn (AngMaj α B0 B1 G) Work.Spaces.Iθ :=
    integrableOn_AngMaj (α := α) (B0 := B0) (B1 := B1) (G := G) hGint
  have hAint : (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ)
      ≤ B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M :=
    integral_AngMaj_le (α := α) (B0 := B0) (B1 := B1) (M := M) (G := G) hGint hmass hB0 hB1
  have hMAnn : 0 ≤ B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M :=
    add_nonneg (mul_nonneg (sq_nonneg B0) (by norm_num))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B1)) hM)
  -- ### the pointwise domination
  have hdom : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) z θ
        ≤ Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ :=
    fun z _ θ hθ => hkIntegrand_ang_le5 (α := α) (B0 := B0) (B1 := B1) (a := a) (r := r)
      (G := G) ha0 ha1 hθ
  -- ### the radial data
  obtain ⟨hRint_int, hRint_le⟩ := rint5_mem (α := α) hrmem
  -- ### membership, by the majorant criterion
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad ha hr).continuousOn_HkIntegrand
      α 5).mono (fun p hp => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hp.1, hp.2.1, hp.2.2⟩)
  have hmem : Work.Spaces.HkMem α 5 (fun z θ => a θ * r z) := by
    refine Work.FTS.LocData.HkMem_of_majorant α 5 (f := fun z θ => a θ * r z)
      (M := fun z θ => Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ)
      hcont ?_ ?_ ?_
    · intro z _
      exact hAi.const_mul (Work.FTS.StrongEps.H5.Rint5 r z)
    · have hz : MeasureTheory.IntegrableOn
          (fun z : ℝ => Work.FTS.StrongEps.H5.Rint5 r z
            * (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ)) Work.Spaces.Iz :=
        hRint_int.mul_const _
      refine hz.congr (Filter.Eventually.of_forall fun z => ?_)
      exact (MeasureTheory.integral_const_mul (Work.FTS.StrongEps.H5.Rint5 r z)
        (AngMaj α B0 B1 G)).symm
    · intro z hz θ hθ
      exact hdom z hz θ hθ
  refine ⟨hmem, ?_⟩
  -- ### the norm bound
  have hslices : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) z θ)
        ≤ Work.FTS.StrongEps.H5.Rint5 r z * (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) := by
    intro z hz
    have hAint' : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ)
        Work.Spaces.Iθ := hAi.const_mul _
    have h1 := MeasureTheory.integral_mono_ae (hmem.1 z hz) hAint'
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hdom z hz θ hθ))
    have h2 : (∫ θ in Work.Spaces.Iθ,
          Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ)
        = Work.FTS.StrongEps.H5.Rint5 r z
          * (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ) :=
      MeasureTheory.integral_const_mul _ _
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hAint
      (Work.FTS.StrongEps.H5.Rint5_nonneg r z))
  have hSq : Work.Spaces.HkSq α 5 (fun z θ => a θ * r z)
      ≤ (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M)
        * Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z) := by
    calc Work.Spaces.HkSq α 5 (fun z θ => a θ * r z)
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) z θ) := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z
            * (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) :=
          MeasureTheory.integral_mono_ae hmem.2 (hRint_int.mul_const _)
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hslices)
      _ = (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
            * (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) := MeasureTheory.integral_mul_const _ _
      _ ≤ Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)
            * (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) :=
          mul_le_mul_of_nonneg_right hRint_le hMAnn
      _ = (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M)
            * Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z) := by ring
  have hCrad' : Real.sqrt (Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)) ≤ Crad := hCradbd
  have hnorm : Work.Spaces.HkNorm α 5 (fun z θ => a θ * r z)
      ≤ Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad := by
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => a θ * r z))
        ≤ Real.sqrt ((B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M)
            * Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)) := Real.sqrt_le_sqrt hSq
      _ = Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M)
            * Real.sqrt (Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)) :=
          Real.sqrt_mul hMAnn _
      _ ≤ Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad :=
          mul_le_mul_of_nonneg_left hCrad' (Real.sqrt_nonneg _)
  calc Work.Spaces.HkNorm α 5 (fun z θ => a θ * r z)
      ≤ Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad := hnorm
    _ = 1 * Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad := by ring

end Work.FTS.StrongEps.H5.AngRad5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.Pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : ℝ → ℝ → ℝ}

/-! ## The two shifts in the log coordinates -/



/-! ## Continuity of the weights on the compact shift region -/

theorem continuousOn_w_region {z θ : ℝ} (hz : 0 < z) (hε : 0 < ε) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1) (Kz z ε ×ˢ Kth θ ε) := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun q hq => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Kz_subset_pos hz hε hq.1))

theorem continuousOn_sin_rpow_region {z θ ε c : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun q : ℝ × ℝ => (Real.sin (2 * q.2)) ^ c) (Kz z ε ×ˢ Kth θ ε) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun q hq => Or.inl (ne_of_gt (sin_two_pos (Kth_subset hθ hq.2))))

theorem continuousOn_wdiv_region {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))
      (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_w_region hz hε).div (continuousOn_sin_rpow_region (z := z) (ε := ε) hθ)
    (fun q hq => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos (Kth_subset hθ hq.2)) _))

theorem continuousOn_Wt_region {α z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2) (Kz z ε ×ˢ Kth θ ε) := by
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact (continuousOn_w_region hz hε).mul
    (continuousOn_sin_rpow_region (z := z) (ε := ε) (c := -(Work.Spaces.gam α / 2)) hθ)

/-! ## Continuity of the weighted slots on the compact region -/

theorem continuousOn_wdiv_mixed_region {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ =>
        Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.mixed j i f q.1 q.2) (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_wdiv_region hz hε hθ).mul
    ((continuousOn_mixed_Quad hf j i).mono (Kz_prod_Kth_subset_Quad hz hε hθ))

theorem continuousOn_Wt_mixed_region {α z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ =>
        Work.Spaces.Wt α q.1 q.2 * Work.Spaces.mixed j i f q.1 q.2)
      (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_Wt_region hz hε hθ).mul
    ((continuousOn_mixed_Quad hf j i).mono (Kz_prod_Kth_subset_Quad hz hε hθ))

/-! ## Continuity of the weighted slots on the ball of the shift -/

theorem continuousOn_shift_ball {z θ ε : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {A : ℝ → ℝ → ℝ} (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) (Kz z ε ×ˢ Kth θ ε)) :
    ContinuousOn (fun p : ℝ × ℝ => A (zShift z p.1) (thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
  hA.comp (continuous_shift_pair z θ).continuousOn
    (mapsTo_ball_region hθ (self_mem_Ioo_div_two hz))

/-- Continuity of the unweighted `D_z`-iterates and of the mixed derivatives on the compact
    shift region. -/
theorem continuousOn_DzIter_region {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.DzIter i f q.1 q.2) (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_mixed_Quad hf i 0).mono (Kz_prod_Kth_subset_Quad hz hε hθ)

theorem continuousOn_mixed_region {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) (Kz z ε ×ˢ Kth θ ε) :=
  (continuousOn_mixed_Quad hf j i).mono (Kz_prod_Kth_subset_Quad hz hε hθ)

/-! ## The two slot bounds -/

theorem exp_sq_eq (c X : ℝ) : (Real.exp (c * X)) ^ 2 = Real.exp (2 * c * X) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The *unweighted* slot bound: `D (J_ε f)` is, in `L²` at a fixed point, dominated by the
average of `D f` at the shifted point.  This is `slot_sq_bound` with the constant weight `1`. -/
theorem slot_z_base (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) :
    (Work.Spaces.DzIter i (Jeps ρ ε f) z θ) ^ 2
      ≤ ∫ p : ℝ × ℝ,
          Jker ρ ε p * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2 := by
  have hcomm : Work.Spaces.DzIter i (Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p
          * Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2) := by
    have h : Work.Spaces.DzIter i (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.DzIter i f) z θ := by
      have h0 := mixed_Jeps ρ hρ hε hf hz hθ i 0
      simpa only [Work.Spaces.mixed_zero_right] using h0
    rw [h, Jeps_eq_integral ρ ε _ hz hθ]
  have hb := slot_sq_bound (c := 0) ρ hρ hε (fun g => Work.Spaces.DzIter i g)
    (fun _ _ => (1 : ℝ)) f hcomm zero_le_one (fun p => by simp)
    (by
      have h := continuousOn_shift_ball (ε := ε) hz hθ
        (A := fun z' θ' => Work.Spaces.DzIter i f z' θ')
        (continuousOn_DzIter_region hz hε hθ hf i)
      simpa using h)
  simpa using hb

theorem slot_mixed_base (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    (Work.Spaces.mixed j i (Jeps ρ ε f) z θ) ^ 2
      ≤ ∫ p : ℝ × ℝ,
          Jker ρ ε p * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2 := by
  have hcomm : Work.Spaces.mixed j i (Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p
          * Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2) := by
    rw [mixed_Jeps ρ hρ hε hf hz hθ j i, Jeps_eq_integral ρ ε _ hz hθ]
  have hb := slot_sq_bound (c := 0) ρ hρ hε (fun g => Work.Spaces.mixed j i g)
    (fun _ _ => (1 : ℝ)) f hcomm zero_le_one (fun p => by simp)
    (by
      have h := continuousOn_shift_ball (ε := ε) hz hθ
        (A := fun z' θ' => Work.Spaces.mixed j i f z' θ')
        (continuousOn_mixed_region hz hε hθ hf j i)
      simpa using h)
  simpa using hb

/-- **The `z`-slot bound**: the weighted `i`-th `D_z`-derivative of `J_ε f`, squared, is bounded
by the average of the same slot of `f` at the shifted point, with the weight ratio `e^{2c|p|}`
taken inside the integral (where `|p| ≤ 2ε` on the support of the kernel). -/
theorem slot_z_exp (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z θ c : ℝ}
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (zShift z p.1)
            / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) :
    (Work.Spaces.DzIter i (Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hWdef
  have hWnn : 0 ≤ W := by
    rw [hWdef]
    exact div_nonneg (by rw [Work.Spaces.w]; positivity)
      (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)
  have hbase := slot_z_base (f := f) hρ hε hf hz hθ i
  -- integrability of the two integrands
  have h1int : Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      (W ^ 2 * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2)) :=
    integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      W ^ 2 * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2)
      (((continuousOn_shift_ball (ε := ε) hz hθ
        (A := fun z' θ' => Work.Spaces.DzIter i f z' θ')
        (continuousOn_DzIter_region hz hε hθ hf i)).pow 2).const_mul (W ^ 2))
  have h2int : Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      (Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.w (zShift z p.1)
        / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2)) := by
    refine integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.w (zShift z p.1)
        / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2) ?_
    have hcont := continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun z' θ' => Work.Spaces.w z' / (Real.sin (2 * θ')) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter i f z' θ') (continuousOn_wdiv_mixed_region hz hε hθ hf i 0)
    have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by fun_prop
    exact hexp.continuousOn.mul (hcont.pow 2)
  calc (Work.Spaces.DzIter i (Jeps ρ ε f) z θ * W) ^ 2
      = W ^ 2 * (Work.Spaces.DzIter i (Jeps ρ ε f) z θ) ^ 2 := by ring
    _ ≤ W ^ 2 * ∫ p : ℝ × ℝ,
          Jker ρ ε p * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg W)
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (W ^ 2 * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring
    _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.w (zShift z p.1)
            / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)
              * Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)) ^ 2) :=
        integral_mono h1int h2int (fun p => by
          refine mul_le_mul_of_nonneg_left ?_ (Jker_nonneg ρ hρ ε p)
          have hWs : 0 ≤ Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2) :=
            div_nonneg (by rw [Work.Spaces.w]; positivity)
              (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
          have h1 : W ≤ Real.exp (c * (|p.1| + |p.2|))
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)) := by
            rw [hWdef]
            exact hW p
          have hsq : W ^ 2 ≤ (Real.exp (c * (|p.1| + |p.2|))
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2 :=
            pow_le_pow_left₀ hWnn h1 2
          refine mul_le_mul_of_nonneg_right hsq (sq_nonneg _) |>.trans (le_of_eq ?_)
          rw [mul_pow, exp_sq_eq]
          ring)
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring

/-- **The mixed-slot bound**, the companion of `slot_z_exp` for the mixed derivatives
`D_z^j D_θ^i f`. -/
theorem slot_mixed_exp (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {z θ c : ℝ}
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ
      ≤ Real.exp (c * (|p.1| + |p.2|)) * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    (Work.Spaces.mixed j i (Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2 := by
  set W : ℝ := Work.Spaces.Wt α z θ with hWdef
  have hWnn : 0 ≤ W := by
    rw [hWdef, Work.Spaces.Wt]
    exact mul_nonneg (by rw [Work.Spaces.w]; positivity)
      (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)
  have hbase := slot_mixed_base (f := f) hρ hε hf hz hθ j i
  have h1int : Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      (W ^ 2 * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2)) :=
    integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      W ^ 2 * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2)
      (((continuousOn_shift_ball (ε := ε) hz hθ
        (A := fun z' θ' => Work.Spaces.mixed j i f z' θ')
        (continuousOn_mixed_region hz hε hθ hf j i)).pow 2).const_mul (W ^ 2))
  have h2int : Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      (Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)
          * Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2)) := by
    refine integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)
          * Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2) ?_
    have hcont := continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun z' θ' => Work.Spaces.Wt α z' θ' * Work.Spaces.mixed j i f z' θ')
      (continuousOn_Wt_mixed_region hz hε hθ hf j i)
    have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by fun_prop
    exact hexp.continuousOn.mul (hcont.pow 2)
  calc (Work.Spaces.mixed j i (Jeps ρ ε f) z θ * W) ^ 2
      = W ^ 2 * (Work.Spaces.mixed j i (Jeps ρ ε f) z θ) ^ 2 := by ring
    _ ≤ W ^ 2 * ∫ p : ℝ × ℝ,
          Jker ρ ε p * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg W)
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (W ^ 2 * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring
    _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Real.exp (2 * c * (|p.1| + |p.2|)) * (Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)) ^ 2) :=
        integral_mono h1int h2int (fun p => by
          refine mul_le_mul_of_nonneg_left ?_ (Jker_nonneg ρ hρ ε p)
          have hWs : 0 ≤ Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := by
            rw [Work.Spaces.Wt]
            exact mul_nonneg (by rw [Work.Spaces.w]; positivity)
              (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
          have h1 : W ≤ Real.exp (c * (|p.1| + |p.2|))
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := by
            rw [hWdef]
            exact hW p
          have hsq : W ^ 2 ≤ (Real.exp (c * (|p.1| + |p.2|))
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2 :=
            pow_le_pow_left₀ hWnn h1 2
          refine mul_le_mul_of_nonneg_right hsq (sq_nonneg _) |>.trans (le_of_eq ?_)
          rw [mul_pow, exp_sq_eq]
          ring)
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring

end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

open MeasureTheory

/-- **The two-dimensional log-coordinate substitution** `z = e^s`, `θ = arctan (e^ζ)` in
`lintegral` form, for an **arbitrary** `ENNReal`-valued function `V` (no measurability or
integrability hypothesis): the iterated integral over the open quadrant `(0,∞) × (0,π/2)`
becomes an integral over the plane with the Jacobian weight `logJac s ζ = e^s · kappa ζ`.

The proof is a two-step application of the one-dimensional substitutions
`lintegral_exp_subst_gen` (for `z = e^s`) and `lintegral_arctan_exp_subst_gen`
(for `θ = arctan (e^ζ)`), followed by the measurability-free identity
`lintegral_const_mul'` which moves the constant factor `e^s` inside the `ζ`-integral. -/
theorem lintegral_quad_log_subst (V : ℝ → ℝ → ENNReal) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), V z θ)
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * V (Real.exp s) (Real.arctan (Real.exp ζ)) := by
  -- (1) the angular substitution `θ = arctan (e^ζ)`, slice by slice
  rw [show (fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), V z θ)
      = fun z => ∫⁻ ζ, ENNReal.ofReal (kappa ζ) * V z (Real.arctan (Real.exp ζ)) from
        funext (fun z => lintegral_arctan_exp_subst_gen (V z))]
  -- (2) the radial substitution `z = e^s` in the outer integral
  rw [lintegral_exp_subst_gen (fun z => ∫⁻ ζ, ENNReal.ofReal (kappa ζ)
        * V z (Real.arctan (Real.exp ζ)))]
  refine MeasureTheory.lintegral_congr fun s => ?_
  -- (3) pull the constant `e^s` inside the `ζ`-integral (no measurability needed)
  rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Real.exp s))
        (fun ζ => ENNReal.ofReal (kappa ζ) * V (Real.exp s) (Real.arctan (Real.exp ζ)))
        ENNReal.ofReal_ne_top]
  refine MeasureTheory.lintegral_congr fun ζ => ?_
  -- (4) identify the product of the two Jacobians
  rw [logJac, ENNReal.ofReal_mul (Real.exp_pos s).le]
  ring

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.mixed_Jeps_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter MeasureTheory Set

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The peak estimate with local smoothness instead of global measurability -/

/-- **The quantitative core of the peak estimate, in the `ContinuousOn`-form used by the slots.**
If `X` is continuous on the open quadrant and deviates from its value at the base point `(z,θ)` by
at most `η` on the whole ball `‖p‖ ≤ ε` (which contains the support of `Jker ρ ε`), then the
mollified value at `(z,θ)` is within `η` of `X z θ`:

  `|Jeps ρ ε X z θ - X z θ| ≤ η`.

Only `z > 0`, `θ ∈ (0,π/2)` and `ε > 0` are needed; no limit in `ε` is involved.  The hypothesis
`ContinuousOn (uncurry X) Quad` replaces the global a.e. strong measurability of
`abs_Jeps_sub_le_of_bound`: it is exactly what makes the shifted profile continuous (hence
locally bounded and a.e. strongly measurable), and it is what the slots actually satisfy. -/
theorem abs_Jeps_sub_le_of_bound_of_continuousOn (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ)
    {X : ℝ → ℝ → ℝ} {ε z θ η : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hε : 0 < ε)
    (hXc : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Quad)
    (hη : ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → |X (zShift z p.1) (thShift θ p.2) - X z θ| ≤ η) :
    |Jeps ρ ε X z θ - X z θ| ≤ η := by
  have hJint : Integrable (Jker ρ ε) := Jker_integrable hρ hε
  have hJmass : ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := Jker_integral_eq_one ρ hρ hε
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := fun p => by
    simp only [Jker]
    exact mul_nonneg (by positivity) (hρ.nonneg (ε⁻¹ • p))
  have hsPhi : ∀ p : ℝ × ℝ, (zShift z p.1, thShift θ p.2) ∈ Quad := fun p =>
    ⟨zShift_pos hz, thShift_mem hθ⟩
  -- the shifted profile is continuous (it is the composition of the continuous shift with a
  -- function continuous on the quadrant, whose image lies in the quadrant)
  have hAcont : Continuous (fun p : ℝ × ℝ => X (zShift z p.1) (thShift θ p.2)) := by
    have h := hXc.comp_continuous (continuous_shift_pair z θ) (fun p => hsPhi p)
    simpa only [Function.comp_def] using h
  have hAesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => X (zShift z p.1) (thShift θ p.2)) volume := hAcont.aestronglyMeasurable
  -- the kernel vanishes off the ball of radius `ε`
  have hle_of_Jker : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → ‖p‖ ≤ ε := by
    intro p hp
    by_contra hc
    exact hp (Jker_eq_zero_of_not_mem hρ hε (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact not_le.mpr (not_le.mp hc)))
  -- integrability of the mollified profile: the kernel has compact support and the shifted
  -- profile is bounded there by `η + |X z θ|`
  have hFint : Integrable
      (fun p : ℝ × ℝ => Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) := by
    refine Integrable.mono' (hJint.mul_const (η + |X z θ|)) ?_ ?_
    · exact (Jker_continuous hρ ε).aestronglyMeasurable.mul hAesm
    · filter_upwards with p
      by_cases hp : Jker ρ ε p = 0
      · simp [hp]
      · have hb := hη p (hle_of_Jker p hp)
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
        refine mul_le_mul_of_nonneg_left ?_ (hJnn p)
        have h1 : |X (zShift z p.1) (thShift θ p.2)|
            ≤ |X (zShift z p.1) (thShift θ p.2) - X z θ| + |X z θ| := by
          simpa only [sub_add_cancel, Real.norm_eq_abs] using
            norm_add_le (X (zShift z p.1) (thShift θ p.2) - X z θ) (X z θ)
        linarith
  -- `X z θ` is the average of the constant profile `X z θ` against the kernel
  have hsplit : (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) - X z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ) := by
    have h2 : (∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ))
        = (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2))
          - ∫ p : ℝ × ℝ, Jker ρ ε p * X z θ := by
      rw [← integral_sub hFint (hJint.mul_const (X z θ))]
      exact integral_congr_ae (Eventually.of_forall fun p => by ring)
    calc (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) - X z θ
        = (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2))
          - ∫ p : ℝ × ℝ, Jker ρ ε p * X z θ := by
          rw [integral_mul_const, hJmass, one_mul]
      _ = ∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ) := h2.symm
  -- and the difference is bounded by `η` times the total mass of the kernel
  have hbd : |∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)| ≤ η := by
    have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
        ‖Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)‖ ≤ Jker ρ ε p * η := by
      filter_upwards with p
      by_cases hp : Jker ρ ε p = 0
      · simp [hp]
      · have hb := hη p (hle_of_Jker p hp)
        have h1 : ‖Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)‖
            = Jker ρ ε p * |X (zShift z p.1) (thShift θ p.2) - X z θ| := by
          simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
        rw [h1]
        exact mul_le_mul_of_nonneg_left hb (hJnn p)
    have h := norm_integral_le_of_norm_le (hJint.mul_const η) hae
    rw [integral_mul_const, hJmass, one_mul] at h
    simpa only [Real.norm_eq_abs] using h
  rw [Jeps_eq_integral ρ ε X hz hθ, hsplit]
  exact hbd

/-- **The sequential peak estimate, `ContinuousOn`-form**: if the profiles `X n` are continuous on
the open quadrant and asymptotically uniformly within `η` of their value at `(z,θ)` on the ball of
radius `ε n`, and `X n z θ → Xlim z θ`, then `Jeps ρ (ε n) (X n) z θ → Xlim z θ`. -/
theorem tendsto_Jeps_of_continuousOn (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ)
    {X : ℕ → ℝ → ℝ → ℝ} {Xlim : ℝ → ℝ → ℝ} {ε : ℕ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hXc : ∀ n : ℕ, ContinuousOn (fun q : ℝ × ℝ => X n q.1 q.2) Quad)
    (hεpos : ∀ n : ℕ, 0 < ε n)
    (huc : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ p : ℝ × ℝ, ‖p‖ ≤ ε n →
      |X n (zShift z p.1) (thShift θ p.2) - X n z θ| ≤ η)
    (hlim : Filter.Tendsto (fun n : ℕ => X n z θ) Filter.atTop (nhds (Xlim z θ))) :
    Filter.Tendsto (fun n : ℕ => Jeps ρ (ε n) (X n) z θ) Filter.atTop (nhds (Xlim z θ)) := by
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop,
      |Jeps ρ (ε n) (X n) z θ - X n z θ| ≤ η := by
    intro η hη
    filter_upwards [huc η hη] with n hn
    exact abs_Jeps_sub_le_of_bound_of_continuousOn ρ hρ hz hθ (hεpos n) (hXc n) hn
  rw [Metric.tendsto_atTop]
  intro γ hγ
  have h2 : 0 < γ / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (key (γ / 2) h2)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hlim (γ / 2) h2
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : dist (Jeps ρ (ε n) (X n) z θ) (X n z θ) ≤ γ / 2 := by
    rw [Real.dist_eq]
    exact hN₁ n (le_trans (le_max_left _ _) hn)
  have hn2 : dist (X n z θ) (Xlim z θ) < γ / 2 :=
    hN₂ n (le_trans (le_max_right _ _) hn)
  calc dist (Jeps ρ (ε n) (X n) z θ) (Xlim z θ)
      ≤ dist (Jeps ρ (ε n) (X n) z θ) (X n z θ) + dist (X n z θ) (Xlim z θ) :=
        dist_triangle _ _ _
    _ < γ / 2 + γ / 2 := add_lt_add_of_le_of_lt hn1 hn2
    _ = γ := by ring

/-! ## The target -/

theorem mixed_Jeps_tendsto {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {α B : ℝ} {G : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn} {ε : ℕ → ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B G f)
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    {j i : ℕ} (hji : j + i ≤ 4) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ (ε n) (G n))
        p.1 p.2) Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
  -- the approximating slots are continuous on the open quadrant
  have hXc : ∀ n : ℕ,
      ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i (G n) q.1 q.2) Quad :=
    fun n => Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad (hsm n) j i
  -- a compact neighbourhood of the base point inside the quadrant
  obtain ⟨r, hr, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (p.1, p.2) r ⊆ Quad := by
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp isOpen_Quad (p.1, p.2) hp
    exact ⟨ρ₀ / 2, by linarith, fun x hx =>
      hball (Metric.closedBall_subset_ball (by linarith) hx)⟩
  -- the uniform convergence of the slots on that compact set
  have hKc : IsCompact (Metric.closedBall (p.1, p.2) r) := isCompact_closedBall _ _
  have hU := hconv.1 (Metric.closedBall (p.1, p.2) r) hKc hrsub j i hji
  have hmemK0 : (p.1, p.2) ∈ Metric.closedBall (p.1, p.2) r := by
    rw [Metric.mem_closedBall, dist_self]
    exact hr.le
  -- hence the limit slot is continuous at the base point
  have hKcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2)
      (Metric.closedBall (p.1, p.2) r) :=
    hU.continuousOn (Filter.Frequently.of_forall fun n => (hXc n).mono hrsub)
  have hlimc : ContinuousAt (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) (p.1, p.2) :=
    hKcont.continuousAt (by
      refine mem_of_superset (Metric.ball_mem_nhds (p.1, p.2) hr) ?_
      exact Metric.ball_subset_closedBall)
  -- the asymptotic uniform closeness of the approximating slots to their value at the base point
  have huc : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ q : ℝ × ℝ, ‖q‖ ≤ ε n →
      |Work.Spaces.mixed j i (G n) (zShift p.1 q.1) (thShift p.2 q.2)
        - Work.Spaces.mixed j i (G n) p.1 p.2| ≤ η := by
    intro η hη
    have hη3 : 0 < η / 3 := by linarith
    have hev : ∀ᶠ n in Filter.atTop, ∀ x ∈ Metric.closedBall (p.1, p.2) r,
        dist (Work.Spaces.mixed j i (G n) x.1 x.2) (Work.Spaces.mixed j i f x.1 x.2)
          < η / 3 := by
      filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) (η / 3) hη3] with n hn x hx
      rw [dist_comm]
      exact hn x hx
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp hlimc (η / 3) hη3
    have hsPhi0 : sPhi p.1 p.2 0 = (p.1, p.2) := sPhi_zero hp.2
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
      Metric.continuousAt_iff.mp (continuous_sPhi p.1 p.2).continuousAt (min δ₁ r)
        (lt_min hδ₁pos hr)
    have hεsmall : ∀ᶠ n in Filter.atTop, ε n < δ₂ := by
      obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hε0 δ₂ hδ₂pos
      filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
      have h := hN₀ n hn
      rw [Real.dist_eq, sub_zero, abs_of_pos (hεpos n)] at h
      exact h
    filter_upwards [hεsmall, hev] with n hεn hnN q hq
    have hqq : dist q (0 : ℝ × ℝ) < δ₂ := by
      rw [dist_zero_right]
      exact lt_of_le_of_lt hq hεn
    have hsPhiq : dist (sPhi p.1 p.2 q) (p.1, p.2) < min δ₁ r := by
      have h := hδ₂ hqq
      rwa [hsPhi0] at h
    have hmemK : sPhi p.1 p.2 q ∈ Metric.closedBall (p.1, p.2) r := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (lt_of_lt_of_le hsPhiq (min_le_right _ _))
    have h1 : dist (Work.Spaces.mixed j i (G n) (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i f (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2) < η / 3 :=
      hnN _ hmemK
    have h2 : dist (Work.Spaces.mixed j i f (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i f p.1 p.2) < η / 3 :=
      hδ₁ (lt_of_lt_of_le hsPhiq (min_le_left _ _))
    have h3 : dist (Work.Spaces.mixed j i f p.1 p.2)
        (Work.Spaces.mixed j i (G n) p.1 p.2) < η / 3 := by
      rw [dist_comm]
      exact hnN _ hmemK0
    have hkey : dist (Work.Spaces.mixed j i (G n) (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i (G n) p.1 p.2) < η := by
      have h4 := dist_triangle4
        (Work.Spaces.mixed j i (G n) (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i f (sPhi p.1 p.2 q).1 (sPhi p.1 p.2 q).2)
        (Work.Spaces.mixed j i f p.1 p.2)
        (Work.Spaces.mixed j i (G n) p.1 p.2)
      linarith
    have hkey' : |Work.Spaces.mixed j i (G n) (zShift p.1 q.1) (thShift p.2 q.2)
        - Work.Spaces.mixed j i (G n) p.1 p.2| < η := by
      rw [Real.dist_eq] at hkey
      exact hkey
    exact hkey'.le
  -- pointwise convergence of the slots at the base point
  have hlim : Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (G n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hU) η hη)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn (p.1, p.2) hmemK0
    rwa [dist_comm] at h
  -- assemble: `E1` turns the slot of the mollified profile into the mollified slot
  have hmain : Filter.Tendsto
      (fun n : ℕ => Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.mixed j i f p.1 p.2)) :=
    tendsto_Jeps_of_continuousOn ρ hρ hp.1 hp.2 hXc hεpos huc hlim
  refine Filter.Tendsto.congr' (Eventually.of_forall fun n => ?_) hmain
  exact (mixed_Jeps ρ hρ (hεpos n) (fun k => hsm n k) hp.1 hp.2 j i).symm

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.AK6.HkMem_AK6 =====
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
set_option maxHeartbeats 1600000

/-- `AK α` in the *separable* shape `ρ(z)·Γ(θ)` consumed by
`LocDataExt.HkIntegrand_sepGam_le`. -/
theorem AK_eq_sep (α : ℝ) :
    Work.Construction.AK α = fun z θ =>
      (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
  funext z θ
  rw [Work.Construction.AK]
  ring

/-- **`AK α` is `C⁶` on the open quadrant.**  A product of `Γ(θ)/c α` and `2z²/(1+z)³`, both
smooth there (`OpenPkg.contDiffOn_Gam_Q0` and the rational factor). -/
theorem contDiffOn_six_AK (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.AK α)) Work.FTS.EllipticEst.Q0 := by
  have hcne : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0
    rw [h0] at h
    norm_num at h
  have hGam := (Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 6).div contDiffOn_const
    (fun _ _ => hcne)
  have hrad : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (contDiffOn_fst.pow 2)).div
      ((contDiffOn_const.add contDiffOn_fst).pow 3)
      (fun p hp => pow_ne_zero 3 (ne_of_gt
        (by linarith [Set.mem_Ioi.mp hp.1] : (0 : ℝ) < 1 + p.1)))
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)) = Function.uncurry (Work.Construction.AK α) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.AK]
  rw [← hfun]
  exact hGam.mul hrad

/-- **`HkMem α 6 (AK α)`** from the radial jet bound `hrad` for the profile `2z²/(1+z)³`. -/
theorem HkMem_AK6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {R : ℝ} (hR : 0 ≤ R) (hrad : ∀ (j : ℕ), j ≤ 6 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2) : Work.Spaces.HkMem α 6 (Work.Construction.AK α) := by
  obtain ⟨hc1, _hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : (0 : ℝ) < Work.Spaces.c α := by linarith
  have hR0 : (0 : ℝ) ≤ 100 * R := by linarith
  -- ## The radial jets of `ρ₀/c α`, from `hrad` rescaled by `(1/c)² ≤ 100`
  have hB : ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) z θ'
        * Work.Spaces.w z) ^ 2 ≤ 100 * R / (1 + z) ^ 2 := by
    intro j hj z hz θ'
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
      rw [hw0, mul_zero, sq, zero_mul]
      exact div_nonneg hR0 (by norm_num)
    · have hfun : (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α)
          = fun z _ : ℝ => (1 / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) := by
        funext z θ''
        ring
      have hmult := congrFun (congrFun (Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul j
        (1 / Work.Spaces.c α) (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3)) z) θ'
      rw [hfun, hmult]
      have hc10 : (1 / Work.Spaces.c α) ≤ 10 := by
        rw [div_le_iff₀ hc0]
        linarith
      have hsq : (1 / Work.Spaces.c α) ^ 2 ≤ 100 := by
        have h1 : (0 : ℝ) ≤ 1 / Work.Spaces.c α := by positivity
        nlinarith [hc10, h1]
      calc ((1 / Work.Spaces.c α)
              * Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
              * Work.Spaces.w z) ^ 2
          = (1 / Work.Spaces.c α) ^ 2
              * (Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
                * Work.Spaces.w z) ^ 2 := by ring
        _ ≤ 100 * (R / (1 + z) ^ 2) :=
            mul_le_mul hsq (hrad j hj z hz θ') (sq_nonneg _) (by norm_num)
        _ = 100 * R / (1 + z) ^ 2 := by ring
  -- ## The angular jets of `Γ`, up to order `6`
  have hΓ : ∀ i ≤ 6, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ') ^ 2 := by
    intro i hi θ' hθ'
    have h := Work.FTS.LocData6.DthIter_Gam_abs_le6 i hi α hα hα1 hθ'
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow] at h2
    have h10 : ((100000 : ℝ)) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
    calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (100000 : ℝ) ^ 2 * (Work.Spaces.Gam α θ') ^ 2 := h2
      _ = (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ') ^ 2 := by rw [h10]
  -- ## The domination criterion, with the separable majorant
  refine Work.FTS.LocData.HkMem_of_majorant (f := Work.Construction.AK α)
    (M := fun z θ => (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R) / (1 + z) ^ 2)
      * Work.FTS.LocData.angMaj α θ) α 6 ?_ ?_ ?_ ?_
  · -- interior regularity of the integrand
    exact Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 6) (k := 6) le_rfl
      (contDiffOn_six_AK α hα hα1)
  · -- integrable `θ`-slices of the majorant
    intro z _hz
    exact ((Work.FTS.LocData.angMaj_mem α hα hα1).1).const_mul
      (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R) / (1 + z) ^ 2)
  · -- integrable `z`-integral of the majorant
    have hkey : IntegrableOn (fun z : ℝ => (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ioi 0) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul
        (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R)
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ))
    have hkeyIz : IntegrableOn (fun z : ℝ => (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ici 0) :=
      hkey.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have heqfun : (fun z : ℝ => (((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            ((((7 : ℝ) + 49 * (10 : ℝ) ^ 10) * (100 * R) / (1 + z) ^ 2)
              * Work.FTS.LocData.angMaj α θ) := by
      funext z
      rw [MeasureTheory.integral_const_mul]
      rw [one_div, inv_pow, div_eq_mul_inv]
      ring
    rw [← heqfun]
    exact hkeyIz
  · -- pointwise domination by the separable majorant
    intro z hz θ hθ
    rw [AK_eq_sep]
    have h1 := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 6 hR0 (by norm_num) hB hΓ hz hθ
    refine le_trans h1 (le_of_eq ?_)
    rw [div_eq_mul_inv]
    ring

end Work.FTS.StrongPersist.AK6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseGe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `a = a₁` case of the mismatch coefficient estimate

`theorem mismatchCaseGe`: the pairing

  `∫ leafGam α · D_z^{b₁}D_θ^{a₁}A · D_z^{b-b₁}D_θ^{a-a₁}f · D_z^bD_θ^af`

with `a = a₁`, `1 ≤ a₁`, `a₁ + b₁ ≤ 2` and `¬(a₁ = 1 ∧ b₁ = 0)` is bounded by
`C α^{-3} (1 + K₀ + K₄)(1 + |f|_{ℋ⁶})`, where the two slots `D_z^{b₁}D_θ^{a₁}A`
(`A` elliptic datum, controlled by `K₀` and `K₄ = Xn α A`) and `D_z^b D_θ^af` are
estimated by the weighted `L²` slots of the norms `ℋ⁴(A)` and `ℋ⁶(f)`, the remaining
`D_z^{b-b₁}f` factor by the pointwise Agmon bound `PwAny6` of the level-six norm, and
the product assembled by weighted Cauchy–Schwarz (`slotAmgm`).

The only auxiliary index fact is `a = a₁` together with `¬(a₁ = 1 ∧ b₁ = 0)`, which
forces `b - b₁ ≤ 4` so that `PwAny6` applies to `D_z^{b-b₁}f`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

/-- The elementary `α`-arithmetic closing the two factors produced by the weighted
Cauchy–Schwarz: `√(K₄²+1) ≤ K₄+1`, `α^{-1} ≤ α^{-6}`, `HkSq² ≤ (1+HkSq)²` and
`1 ≤ α^{-6}(1+HkSq)²` combine into the stated `α^{-3}`-bound. -/
private lemma slotArithBound {α Cpw K0 K4 HkSq : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hCpw : 0 < Cpw) (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hH : 0 ≤ HkSq) :
    Real.sqrt (K4 ^ 2 + 1) * Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ (Real.sqrt (10 * Cpw + 1) + 1) * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)) := by
  have h1 : Real.sqrt (K4 ^ 2 + 1) ≤ K4 + 1 := sqrt_sq_add_one_le hK4
  have hE1 : α ^ (-(1 : ℝ)) ≤ α ^ (-(6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hE2 : (1 : ℝ) ≤ α ^ (-(6 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(6 : ℝ)) ≤ 0 by norm_num)
    simpa using h
  have h6nn : 0 ≤ α ^ (-(6 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hrpow : (α ^ (-(3 : ℝ))) ^ 2 = α ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hα0.le]
    norm_num
  have hB2 : (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) ^ 2
      = (10 * Cpw + 1) * α ^ (-(6 : ℝ)) * (1 + HkSq) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hrpow]
  have hE3 : Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1
      ≤ (10 * Cpw + 1) * α ^ (-(6 : ℝ)) * (1 + HkSq) ^ 2 := by
    have hc : (0 : ℝ) ≤ Cpw * 10 := by positivity
    have hHH : HkSq * HkSq ≤ (1 + HkSq) * (1 + HkSq) := by nlinarith
    have hA : α ^ (-(1 : ℝ)) * (HkSq * HkSq)
        ≤ α ^ (-(6 : ℝ)) * ((1 + HkSq) * (1 + HkSq)) :=
      mul_le_mul hE1 hHH (by positivity) h6nn
    have hA' : Cpw * 10 * (α ^ (-(1 : ℝ)) * (HkSq * HkSq))
        ≤ Cpw * 10 * (α ^ (-(6 : ℝ)) * ((1 + HkSq) * (1 + HkSq))) :=
      mul_le_mul_of_nonneg_left hA hc
    have hP1 : (1 : ℝ) ≤ (1 + HkSq) * (1 + HkSq) := by nlinarith
    have hB : (1 : ℝ) ≤ α ^ (-(6 : ℝ)) * ((1 + HkSq) * (1 + HkSq)) := by
      have h := mul_le_mul hE2 hP1 zero_le_one h6nn
      simpa using h
    nlinarith [hA', hB, hc, h6nn, sq_nonneg HkSq]
  have h2 : Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq) := by
    have hB : 0 ≤ Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq) := by positivity
    have hE3' : Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1
        ≤ (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) ^ 2 := by
      rw [hB2]; exact hE3
    have h3 := Real.sqrt_le_sqrt hE3'
    rwa [Real.sqrt_sq hB] at h3
  have h4 : Real.sqrt (K4 ^ 2 + 1) * Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ (K4 + 1) * (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) :=
    mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by linarith)
  refine h4.trans ?_
  have hK : K4 + 1 ≤ 1 + K0 + K4 := by linarith
  have hKnn : 0 ≤ 1 + K0 + K4 := by linarith
  have hP : 0 ≤ 1 + HkSq := by linarith
  have hα3 : 0 ≤ α ^ (-(3 : ℝ)) := (Real.rpow_pos_of_pos hα0 _).le
  have hS : Real.sqrt (10 * Cpw + 1) ≤ Real.sqrt (10 * Cpw + 1) + 1 := by
    linarith [Real.sqrt_nonneg (10 * Cpw + 1)]
  calc (K4 + 1) * (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq))
      ≤ (1 + K0 + K4) * (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) :=
        mul_le_mul_of_nonneg_right hK (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hα3) hP)
    _ ≤ (1 + K0 + K4) * ((Real.sqrt (10 * Cpw + 1) + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hα3) hP) hKnn
    _ = (Real.sqrt (10 * Cpw + 1) + 1) * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)) := by
        ring

theorem mismatchCaseGe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 →
      a = a₁ → ¬ (a₁ = 1 ∧ b₁ = 0) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨Cpw, hCpwpos, hCpw⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨Real.sqrt (10 * Cpw + 1) + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm hf7 hfv
    ha₁ hab₁ ha₁a hb₁b hab haeq hnot
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd
  have h6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hfsm 6 (by norm_num) hf7
  have hH : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hC0 : 0 ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f :=
    mul_nonneg (mul_nonneg (mul_nonneg hCpwpos.le (by norm_num))
      (le_of_lt (Real.rpow_pos_of_pos hα0 _))) hH
  -- the index reductions: `a = a₁` and `b - b₁ ≤ 4`
  have hsub : a - a₁ = 0 := by omega
  have hc4 : b - b₁ ≤ 4 := by
    have hb1 : b₁ ≤ 1 := by omega
    rcases (show a₁ ≠ 1 ∨ b₁ ≠ 0 from by tauto) with h | h
    · have ha2 : a₁ = 2 := by omega
      omega
    · have hb1' : b₁ = 1 := by omega
      omega
  -- #### the `A`-slot
  have hXsl := mixed_slot_le (α := α) 4 hAsm hA4 (i := a₁) (j := b₁) ha₁ (by omega)
  have hX4 : Work.Spaces.HkSq α 4 A = (Work.FTS.Nonlin.Xn α A) ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 A)]
  have hXint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2 ^ 2) pm := by
    simpa only [Work.FTS.TransportS.leafGam] using hXsl.1
  have hXv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2 ^ 2 ∂pm) ≤ K4 ^ 2 + 1 := by
    have h2 : (Work.FTS.Nonlin.Xn α A) ^ 2 ≤ K4 ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd 2
    have h3 : (∫ p, Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.gam α))
        * Work.Spaces.mixed b₁ a₁ A p.1 p.2 ^ 2 ∂pm) ≤ K4 ^ 2 + 1 := by
      rw [hX4] at hXsl
      linarith [hXsl.2]
    simpa only [Work.FTS.TransportS.leafGam] using h3
  -- #### the top `f`-slot
  have hZsl := mixed_slot_le (α := α) 6 hfsm h6 (i := a) (j := b) (by omega) (by omega)
  have hZint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2) pm := by
    simpa only [Work.FTS.TransportS.leafGam] using hZsl.1
  have hZv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 6 f := by
    simpa only [Work.FTS.TransportS.leafGam] using hZsl.2
  -- #### the remaining `D_z`-factor, pointwise
  have hGnn : ∀ᵐ p ∂pm, 0 ≤ Work.FTS.TransportS.leafGam α p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ _ hθ0 hθ1 => ?_)
    exact Work.FTS.TransportS.leafGam_nonneg α
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
  have hY2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
        ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f := by
    intro z θ hz hθ0 hθ1
    rw [hsub, Work.Spaces.mixed_zero_right]
    have h := hCpw α f (b - b₁) 0 hα0 hα1 hfsm h6 (by omega) z hz θ ⟨hθ0, hθ1⟩
    have hval : Cpw / (Work.Spaces.gam α - 1) = Cpw * 10 * α ^ (-(1 : ℝ)) := by
      rw [Work.Spaces.gam_sub_one]
      rw [Real.rpow_neg_one]
      field_simp
    rwa [hval] at h
  -- #### integrability and bound of the middle slot
  have hYZmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    exact (h1.mul ((hfsm.mixed (b - b₁) (a - a₁)).continuousOn.pow 2)).mul
      ((hfsm.mixed b a).continuousOn.pow 2)
  have hYZpt : ∀ᵐ p ∂pm, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2
      ≤ (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
        * (Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hG : 0 ≤ Work.FTS.TransportS.leafGam α z θ :=
      Work.FTS.TransportS.leafGam_nonneg α hs.le
    have hY := hY2 z θ hz hθ0 hθ1
    have hZ2 : 0 ≤ (Work.Spaces.mixed b a f z θ) ^ 2 := sq_nonneg _
    calc Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed (b - b₁) (a - a₁) f z θ ^ 2
          * Work.Spaces.mixed b a f z θ ^ 2
        = (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.FTS.TransportS.leafGam α z θ
            * Work.Spaces.mixed (b - b₁) (a - a₁) f z θ ^ 2) := by ring
      _ ≤ (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.FTS.TransportS.leafGam α z θ
            * (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hG) hZ2
      _ = (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b a f z θ ^ 2) := by ring
  have hYZint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2) pm := by
    refine MeasureTheory.Integrable.mono' (hZint.const_mul
      (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)) hYZmeas ?_
    filter_upwards [hYZpt, hGnn] with p hp hgn
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg hgn (sq_nonneg _)) (sq_nonneg _))]
    exact hp
  have hYZv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2 ∂pm)
      ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f * Work.Spaces.HkSq α 6 f + 1 := by
    calc (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
          * Work.Spaces.mixed b a f p.1 p.2 ^ 2 ∂pm)
        ≤ ∫ p, (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ^ 2) ∂pm :=
          MeasureTheory.integral_mono_ae hYZint (hZint.const_mul _) hYZpt
      _ = (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ^ 2 ∂pm) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left hZv hC0
      _ ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f * Work.Spaces.HkSq α 6 f + 1 := by
          linarith
  -- #### measurability of the full integrand
  have hFmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    exact ((h1.mul (hAsm.mixed b₁ a₁).continuousOn).mul
      (hfsm.mixed (b - b₁) (a - a₁)).continuousOn).mul (hfsm.mixed b a).continuousOn
  -- #### weighted Cauchy–Schwarz
  have hApos : 0 < K4 ^ 2 + 1 := by nlinarith [sq_nonneg K4]
  have hBpos : 0 < Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
      * Work.Spaces.HkSq α 6 f + 1 := by
    have h1 : 0 ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
        * Work.Spaces.HkSq α 6 f := mul_nonneg hC0 hH
    linarith
  obtain ⟨hFint, hFbnd⟩ := slotAmgm (G := Work.FTS.TransportS.leafGam α)
    (X := fun z θ => Work.Spaces.mixed b₁ a₁ A z θ)
    (Y := fun z θ => Work.Spaces.mixed (b - b₁) (a - a₁) f z θ)
    (Z := fun z θ => Work.Spaces.mixed b a f z θ)
    (A := K4 ^ 2 + 1)
    (B := Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
      * Work.Spaces.HkSq α 6 f + 1)
    hXint hYZint hXv hYZv hApos hBpos hGnn hFmeas
  exact ⟨hFint, hFbnd.trans (slotArithBound hα0 hα1 hCpwpos hK0 hK4 hH)⟩

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The three forms of the datum, and the majorant -/

/-- The separable form `a(z)·b(θ)` of the collapsed pair, with `a = Kfac α · rhoR` and
`b = psiA α`. -/
noncomputable def sep6 (α : ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.sepF (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
    (Work.Construction.psiA α)

/-- The closed form `8α² c2m(θ) z² Γ(θ)/(c(α)(1+z)⁴)` of the collapsed pair
(`Work.Construction.N0_first_two_eq'`). -/
noncomputable def close6 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
    / (Work.Spaces.c α * (1 + z) ^ 4)

/-- The literal function appearing in the target statement: the `I₁ + I₂` combination of
`N₀`. -/
noncomputable def N012 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
    * Work.Spaces.pth (Work.Construction.Fstar α) z θ
  - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
    * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- The angular majorant of the level-six `ℋ⁶`-integrand of the separable datum: the `7`
radial slots contribute `28 sin(2θ)^{-η}` and the `49` entries of the mixed double sum
contribute `98 D²(sin(2θ)^{-η} + α² sin(2θ)^{2α/3-γ})`. -/
noncomputable def gammaAngMaj6 (α D θ : ℝ) : ℝ :=
  (28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + 98 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)

/-- The value of the `θ`-integral of `gammaAngMaj6`: `(28+98D²)·10⁴ + 98D²·(3000/17)`
(from `∫ sin(2θ)^{-η} ≤ 10⁴` and `α² ∫ sin(2θ)^{2α/3-γ} ≤ 3000/17`). -/
noncomputable def H6AngConst (D : ℝ) : ℝ :=
  (28 + 98 * D ^ 2) * 10000 + 98 * D ^ 2 * (3000 / 17)

/-! ## Elementary properties of the majorant -/

theorem H6AngConst_pos {D : ℝ} (hD : 0 < D) : 0 < H6AngConst D := by
  rw [H6AngConst]
  nlinarith [sq_nonneg D, hD]

theorem gammaAngMaj6_nonneg {α D θ : ℝ} (hD : 0 ≤ D) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ gammaAngMaj6 α D θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Construction.sin_two_nonneg_of_mem_Iθ hθ
  rw [gammaAngMaj6]
  exact add_nonneg
    (mul_nonneg (by nlinarith [sq_nonneg D]) (Real.rpow_nonneg hs _))
    (mul_nonneg (by positivity) (Real.rpow_nonneg hs _))

theorem integrableOn_gammaAngMaj6 {α D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ => gammaAngMaj6 α D θ) Work.Spaces.Iθ := by
  have hη1 : -1 < -(Work.Spaces.eta) := by have := Work.Spaces.eta_lt_one; linarith
  have hη2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
  have hg1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hg2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hunfold : gammaAngMaj6 α D = fun θ =>
      (28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 98 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := rfl
  rw [hunfold]
  exact ((Work.Spaces.sin_two_rpow _ hη1 hη2).1.const_mul _).add
    ((Work.Spaces.sin_two_rpow _ hg1 hg2).1.const_mul _)

theorem integral_gammaAngMaj6_le {α D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ ≤ H6AngConst D := by
  have hη1 : -1 < -(Work.Spaces.eta) := by have := Work.Spaces.eta_lt_one; linarith
  have hη2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
  have hp : 2 * α / 3 - Work.Spaces.gam α = -1 + 17 * α / 30 := by
    rw [Work.Spaces.gam]; ring
  have hpe1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by rw [hp]; linarith
  have hpe2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by rw [hp]; linarith
  have hint1 : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := (Work.Spaces.sin_two_rpow _ hη1 hη2).1
  have hint2 : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) := (Work.Spaces.sin_two_rpow _ hpe1 hpe2).1
  have hval1 : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10000 := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_nonneg])).2
    have hden : (-(Work.Spaces.eta)) + 1 = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hden] at h
    norm_num at h
    linarith
  have hval2 : α ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 3000 / 17 := by
    have h := (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hpe1 hpe2).2
    have hden : (2 * α / 3 - Work.Spaces.gam α) + 1 = 17 * α / 30 := by
      rw [Work.Spaces.gam]; ring
    rw [hden] at h
    calc α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        ≤ α ^ 2 * (100 / (17 * α / 30)) := mul_le_mul_of_nonneg_left h (sq_nonneg α)
      _ = 3000 * α / 17 := by field_simp; ring
      _ ≤ 3000 / 17 := by nlinarith [hα1]
  have hunfold : gammaAngMaj6 α D = fun θ =>
      (28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 98 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := rfl
  rw [hunfold, MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have h1 : (28 + 98 * D ^ 2) * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ (28 + 98 * D ^ 2) * 10000 :=
    mul_le_mul_of_nonneg_left hval1 (by nlinarith [sq_nonneg D])
  have h2 : 98 * D ^ 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      ≤ 98 * D ^ 2 * (3000 / 17) := by
    calc 98 * D ^ 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        = 98 * D ^ 2 * (α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by ring
      _ ≤ 98 * D ^ 2 * (3000 / 17) := mul_le_mul_of_nonneg_left hval2 (by positivity)
  rw [H6AngConst]
  linarith

/-! ## The closed and separable forms on the open quadrant -/

theorem sep6_eq_close6 (α z θ : ℝ) : sep6 α z θ = close6 α z θ := by
  simp only [sep6, close6, Work.Construction.sepF, Work.Construction.Kfac,
    Work.Construction.rhoR, Work.Construction.psiA]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

theorem sep6_eq_N012 {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) : sep6 α z θ = N012 α z θ := by
  rw [sep6_eq_close6, N012]
  exact (Work.Construction.N0_first_two_eq' hα hα1 hz hθ).symm

/-! ## The `C⁶`-regularity of the separable datum on the open quadrant -/

/-- `sep6 α` is `C⁶` on the open quadrant: the radial factor `Kfac α · rhoR` is a rational
function with its only pole at `z = -1`, and the angular factor `psiA α = c2m · Gam α` is
`C⁶` there. -/
theorem contDiffOn_uncurry_sep6 (α : ℝ) :
    ContDiffOn ℝ (6 : ℕ) (Function.uncurry (sep6 α)) Work.FTS.OpenPkg.Q0 := by
  have hrad : ContDiffOn ℝ (6 : ℕ)
      (fun p : ℝ × ℝ => Work.Construction.Kfac α * Work.Construction.rhoR p.1)
      Work.FTS.OpenPkg.Q0 := by
    have h1 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.OpenPkg.Q0 :=
      contDiffOn_fst.pow 2
    have h2 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => (1 + p.1) ^ 4)
        Work.FTS.OpenPkg.Q0 := (contDiffOn_const.add contDiffOn_fst).pow 4
    have h3 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => p.1 ^ 2 / (1 + p.1) ^ 4)
        Work.FTS.OpenPkg.Q0 :=
      h1.div h2 (fun p hp => pow_ne_zero 4 (ne_of_gt (by
        have hmem : (0 : ℝ) < p.1 := by
          rw [Work.FTS.OpenPkg.Q0] at hp; exact hp.1
        linarith)))
    have h4 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Work.Construction.rhoR p.1)
        Work.FTS.OpenPkg.Q0 := by
      simpa only [Work.Construction.rhoR] using h3
    exact contDiffOn_const.mul h4
  have hang : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Work.Construction.psiA α p.2)
      Work.FTS.OpenPkg.Q0 := by
    have hc2m : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
        Work.FTS.OpenPkg.Q0 := by
      have h1 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Real.cos (2 * p.2))
          Work.FTS.OpenPkg.Q0 :=
        (((Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)).contDiffOn).of_le le_top)
      have h2 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
          Work.FTS.OpenPkg.Q0 :=
        ((((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn).of_le le_top)
      simpa only [Work.Construction.c2m] using h1.sub h2
    have hGam : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
        Work.FTS.OpenPkg.Q0 := Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 6
    simpa only [Work.Construction.psiA] using hc2m.mul hGam
  refine (hrad.mul hang).congr ?_
  intro p _
  rfl

/-! ## The `ℋ⁶`-membership of the separable datum -/

/-- `z ↦ (1/(1+z)²)²` is integrable on `Iz` (it is bounded by `1/(1+z)²`, whose integral is
`≤ 2`, `Work.Elliptic.WtoH_IntZ`). -/
theorem integrableOn_inv_one_add_pow_four :
    IntegrableOn (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2) Work.Spaces.Iz := by
  refine Work.Elliptic.WtoH_IntZ.1.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    have h1 : (0 : ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
    have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [h1, h2]

theorem HkMem_sep6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ) :
    Work.Spaces.HkMem α 6 (sep6 α) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 6
    (M := fun z θ => (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
      * gammaAngMaj6 α D θ) ?_ ?_ ?_ ?_
  · exact Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 6) (k := 6) le_rfl
      (contDiffOn_uncurry_sep6 α)
  · intro z hz
    exact (integrableOn_gammaAngMaj6 (α := α) (D := D) hα hα1).const_mul _
  · have hbase : IntegrableOn (fun z : ℝ => ((Work.Construction.Kfac α) ^ 2 * M ^ 2
        * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)) * (1 / (1 + z) ^ 2) ^ 2)
        Work.Spaces.Iz := integrableOn_inv_one_add_pow_four.const_mul _
    refine hbase.congr_fun ?_ measurableSet_Ici
    intro z hz
    dsimp only
    rw [MeasureTheory.integral_const_mul]
    ring
  · intro z hz θ hθ
    exact hpt z hz θ hθ

/-! ## The `ℋ⁶`-square bound -/

theorem Kfac_nonneg {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 ≤ Work.Construction.Kfac α := by
  have hc : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  rw [Work.Construction.Kfac]
  positivity

theorem Kfac_sq_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (Work.Construction.Kfac α) ^ 2 ≤ 6400 * α ^ 4 := by
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hc2 : (1 / 100 : ℝ) ≤ (Work.Spaces.c α) ^ 2 := by nlinarith
  have hα4 : (0 : ℝ) < α ^ 4 := pow_pos hα 4
  rw [Work.Construction.Kfac, div_pow]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Work.Spaces.c α) ^ 2)]
  nlinarith [hc2, hα4]

theorem HkSq_sep6_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ) :
    Work.Spaces.HkSq α 6 (sep6 α) ≤ 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 := by
  have hKfSq : (Work.Construction.Kfac α) ^ 2 ≤ 6400 * α ^ 4 := Kfac_sq_le hα hα1
  have hKfnn : 0 ≤ Work.Construction.Kfac α := Kfac_nonneg hα hα1
  have hBigint : Integrable (fun θ : ℝ => gammaAngMaj6 α D θ)
      (volume.restrict Work.Spaces.Iθ) := integrableOn_gammaAngMaj6 hα hα1
  have hBigval : ∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ ≤ H6AngConst D :=
    integral_gammaAngMaj6_le hα hα1
  have hBignn : 0 ≤ ∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      gammaAngMaj6_nonneg (le_of_lt hD) hθ
  have hzint : Integrable (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) := integrableOn_inv_one_add_pow_four
  have hzval : ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2 ≤ 2 := by
    have hle : (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z : ℝ => 1 / (1 + z) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      have hz0 : (0 : ℝ) ≤ z := hz
      have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      have h3 : (0 : ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
      nlinarith [h2, h3]
    exact le_trans (MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun z => by positivity) Work.Elliptic.WtoH_IntZ.1 hle)
      Work.Elliptic.WtoH_IntZ.2
  have hWint : 0 ≤ ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z hz => by positivity
  have hinner_eq : ∀ z : ℝ, ∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ
      = (Work.Construction.Kfac α) ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
          * (1 / (1 + z) ^ 2) ^ 2 := by
    intro z
    rw [MeasureTheory.integral_const_mul]
    ring
  have houter_eq : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ
      = (Work.Construction.Kfac α) ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
          * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ)
        = fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2
            * ((Work.Construction.Kfac α) ^ 2 * M ^ 2
              * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)) from by
      funext z; rw [hinner_eq z]; ring]
    rw [MeasureTheory.integral_mul_const]
    ring
  have hMajint : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ)
      (volume.restrict Work.Spaces.Iz) := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ)
        = fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2
            * ((Work.Construction.Kfac α) ^ 2 * M ^ 2
              * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)) from by
      funext z; rw [hinner_eq z]; ring]
    exact hzint.mul_const _
  have hmono : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 6 (sep6 α) z θ))
      hMajint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ =>
            Work.Spaces.HkIntegrand_nonneg α 6 (sep6 α) z θ))
          (hBigint.const_mul _)
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (hpt z hz))))
  have hfinal : (Work.Construction.Kfac α) ^ 2 * M ^ 2
        * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
        * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2)
      ≤ 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 := by
    have h1 : (Work.Construction.Kfac α) ^ 2 * M ^ 2
          * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
        ≤ (Work.Construction.Kfac α) ^ 2 * M ^ 2 * H6AngConst D :=
      mul_le_mul_of_nonneg_left hBigval
        (mul_nonneg (sq_nonneg (Work.Construction.Kfac α)) (sq_nonneg M))
    have h2 : (Work.Construction.Kfac α) ^ 2 * M ^ 2
          * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
          * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2)
        ≤ (Work.Construction.Kfac α) ^ 2 * M ^ 2 * H6AngConst D * 2 :=
      mul_le_mul h1 hzval hWint
        (mul_nonneg (mul_nonneg (sq_nonneg (Work.Construction.Kfac α)) (sq_nonneg M))
          (le_of_lt (H6AngConst_pos hD)))
    have hnn : 0 ≤ M ^ 2 * H6AngConst D * 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg M) (le_of_lt (H6AngConst_pos hD))) (by norm_num)
    have h3 : (Work.Construction.Kfac α) ^ 2 * M ^ 2 * H6AngConst D * 2
        ≤ 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 := by
      calc (Work.Construction.Kfac α) ^ 2 * M ^ 2 * H6AngConst D * 2
          = (Work.Construction.Kfac α) ^ 2 * (M ^ 2 * H6AngConst D * 2) := by ring
        _ ≤ (6400 * α ^ 4) * (M ^ 2 * H6AngConst D * 2) :=
            mul_le_mul_of_nonneg_right hKfSq hnn
        _ = 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 := by ring
    linarith
  rw [Work.Spaces.HkSq]
  exact le_trans (le_trans hmono (le_of_eq houter_eq)) hfinal

/-! ## The target -/

/-- The target, with the two computational cores supplied as hypotheses (`M`, `D` price the
radial and angular jets of the separable datum). -/
theorem FstarI12H6_of_sep {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hpt : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ) :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.HkMem α 6 (N012 α) ∧
      Work.Spaces.HkNorm α 6 (N012 α) ≤ K * α ^ 2 := by
  refine ⟨Real.sqrt (6400 * M ^ 2 * (2 * H6AngConst D)), ?_, fun α hα hα1 => ?_⟩
  · have h1 : 0 < M ^ 2 := pow_pos hM 2
    have h2 : 0 < H6AngConst D := H6AngConst_pos hD
    exact Real.sqrt_pos.mpr (by positivity)
  · have hptα : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
          ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ :=
      hpt α hα hα1
    have hmem : Work.Spaces.HkMem α 6 (sep6 α) := HkMem_sep6 α hα hα1 hM hD hptα
    have hSq : Work.Spaces.HkSq α 6 (sep6 α) ≤ 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 :=
      HkSq_sep6_le α hα hα1 hM hD hptα
    have hnorm : Work.Spaces.HkNorm α 6 (sep6 α)
        ≤ Real.sqrt (6400 * M ^ 2 * (2 * H6AngConst D)) * α ^ 2 := by
      rw [Work.Spaces.HkNorm]
      calc Real.sqrt (Work.Spaces.HkSq α 6 (sep6 α))
          ≤ Real.sqrt (6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4) := Real.sqrt_le_sqrt hSq
        _ = Real.sqrt (6400 * M ^ 2 * (2 * H6AngConst D)) * α ^ 2 := by
            have hpos : (0 : ℝ) ≤ 6400 * M ^ 2 * (2 * H6AngConst D) :=
              mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M))
                (by have := H6AngConst_pos hD; linarith)
            rw [Real.sqrt_mul hpos]
            congr 1
            rw [show α ^ 4 = (α ^ 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    have hsqeq : Work.Spaces.HkSq α 6 (N012 α) = Work.Spaces.HkSq α 6 (sep6 α) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 6
        (fun z θ hz hθ hθ2 => (sep6_eq_N012 hα hα1 hz.le ⟨hθ.le, hθ2.le⟩).symm)
    constructor
    · exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6 hmem
        (fun z hz θ hθ => sep6_eq_N012 hα hα1 hz.le ⟨hθ.1.le, hθ.2.le⟩)
    · rw [Work.Spaces.HkNorm, hsqeq]
      exact hnorm

/-- The `I₁ + I₂` combination of `N₀` (`Construction.N0`, paper tex 1398--1402): by the
exact form of `Γ = Spaces.Gam α` one has the identity `3 sin 2θ ∂_θΓ = 2α c2m Γ`, and the sum
`(3/(2α)) sin2θ L₁₂(F_*) ∂_θF_* - c2m L₁₂(F_*) D_zF_*` collapses to
`8α² z² c2m(θ) Γ(θ)/(c(α)(1+z)⁴)` — in particular it is `O(α²)` with bounded `D`-derivatives
and `ℋ⁶`-norm `≤ K α²`.  (The closed form is already in the tree as
`Work.Construction.N0_first_two_eq'`; only the `ℋ⁶`-membership and the norm bound are new.) -/
theorem FstarI12H6 : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.HkMem α 6 (fun z θ =>
        (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
    Work.Spaces.HkNorm α 6 (fun z θ =>
        (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ K * α ^ 2 := by
  obtain ⟨M, hM, hMr⟩ := Work.Construction.H6N_GammaTerm_rho_bound
  obtain ⟨D, hD, hDl⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
  refine FstarI12H6_of_sep hM hD ?_
  intro α hα hα1 z hz θ hθ
  simpa only [sep6, gammaAngMaj6] using
    (Work.Construction.H6N_GammaTerm_sep_le α hα hα1 hM hD hMr (hDl α hα hα1) z hz θ hθ)

end Work.FTS.StrongPersist.H6Rows
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary angular and weight algebra -/

private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le

/-- The square of the `f`-side angular factor `(α + sin 2θ) sin(2θ)^{α/5}` is
`(α + sin 2θ)² sin(2θ)^{2α/5}`. -/
private theorem phi_sq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [mul_pow]
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2 : ℝ)) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hs, show (α / 5) * (2 : ℝ) = 2 * α / 5 by ring]
  rw [hss]

/-- `(α + sin 2θ)² sin(2θ)^{2α/5} ≤ 4` for `0 < α ≤ 1` and `0 < θ < π/2`. -/
private theorem psi2_le_four {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 4 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
    Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    nlinarith [hs, Real.sin_le_one (2 * θ), hα, hα1]
  nlinarith [h1, h2, Real.rpow_nonneg hs (2 * α / 5)]

/-- On the open quadrant, `(x·W)² = (x·w)² sin(2θ)^{-γ}`. -/
private theorem mul_Wt_sq {α z θ x : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (x * Work.Spaces.Wt α z θ) ^ 2
      = (x * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hstep]
  ring

/-! ## The `g`-side step: the mean-term hypothesis produces the `TW`-block of `GmajW6` -/

private theorem mslot_gside_le6 {α CB : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hgm : Work.Spaces.HkMem α 6 g)
    (hCB : ∀ d : ℕ, d ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
    {d : ℕ} (hd : d ≤ 5) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * (Work.Spaces.DzIter d g z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ max CB 1 * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hCBle : CB ≤ max CB 1 := le_max_left CB 1
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTWnn : 0 ≤ Work.FTS.OpenPkg.WProdWin.TW α θ :=
    Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθI
  -- the mean-term block is nonnegative
  have hX0 : 0 ≤ (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
      + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z :=
    add_nonneg (mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc (fun σ _ => sq_nonneg _)))
      (mul_nonneg hγinv (Work.FTS.H2.WPQ.Aang_nonneg α g d z))
  have hg1 : (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      ≤ max CB 1 * ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) :=
    le_trans (hCB d hd z θ hz hθ.1 hθ.2) (mul_le_mul_of_nonneg_right hCBle hX0)
  -- the mean term and the single `Aang` term are both dominated by `HgInt6`/`∑Aang`
  have hmem : d ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hAang_le : Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ d' ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d' z :=
    Finset.single_le_sum (fun d' _ => Work.FTS.H2.WPQ.Aang_nonneg α g d' z) hmem
  have hw : (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
      ≤ Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z :=
    Work.FTS.StrongPersist.H6Rows.WProd6.w_sq_mul_slice_le_HgInt6 hgm (by omega) hz
  have hXle : (Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z
      ≤ Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z + (Work.Spaces.gam α - 1)⁻¹
          * ∑ d' ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d' z :=
    add_le_add hw (mul_le_mul_of_nonneg_left hAang_le hγinv)
  -- `(D_z^d g · W)² · (α+sin2θ)²sin(2θ)^{2α/5} = (D_z^d g · w)² · TW`
  rw [mul_Wt_sq hθ]
  have hBS : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
      = Work.FTS.OpenPkg.WProdWin.TW α θ := by
    rw [Work.FTS.OpenPkg.WProdWin.TW_eq_mul hθ]; ring
  rw [show ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * ((Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          * Work.FTS.OpenPkg.WProdWin.TW α θ from by rw [← hBS]; ring]
  refine le_trans (mul_le_mul_of_nonneg_right hg1 hTWnn) ?_
  have hXTW : ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)
          * Work.FTS.OpenPkg.WProdWin.TW α θ
      ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    simp only [Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6]
    exact le_trans (mul_le_mul_of_nonneg_right hXle hTWnn)
      (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 6 g z θ))
  calc (max CB 1 * ((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
          * Work.FTS.OpenPkg.WProdWin.TW α θ
      = max CB 1 * (((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)
            * Work.FTS.OpenPkg.WProdWin.TW α θ) := by ring
    _ ≤ max CB 1 * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
        mul_le_mul_of_nonneg_left hXTW hCBB0

/-! ## The mixed slots -/

theorem mslot_le_winf6_cd6 (CB : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.WlInfMem α 6 f →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 6 g →
      (∀ d : ℕ, d ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) →
      ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
  have hCpos : (0 : ℝ) < 2 * 10 ^ 17 * (1 + max CB 1) := by
    have h2 : (0 : ℝ) < 2 * 10 ^ 17 := by norm_num
    have h1 : (1 : ℝ) ≤ max CB 1 := le_max_right CB 1
    have h3 : (0 : ℝ) < 1 + max CB 1 := by linarith
    exact mul_pos h2 h3
  refine ⟨2 * 10 ^ 17 * (1 + max CB 1), hCpos, ?_⟩
  intro α f g hα hα1 hf hfm hg hgm hCB I J hI hIJ z θ hz hθ0 hθ1
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  have hWsq : 0 ≤ (Work.Spaces.WlInf α 6 f) ^ 2 := sq_nonneg _
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ :=
    inv_nonneg.mpr (by rw [Work.Spaces.gam_sub_one]; linarith)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hGnn : 0 ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
    Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_nonneg hα g hθI
  have hTWnn : 0 ≤ Work.FTS.OpenPkg.WProdWin.TW α θ :=
    Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθI
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hHkG : Work.Spaces.HkIntegrand α 6 g z θ
      ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
    Work.FTS.StrongPersist.H6Rows.WProd6.HkIntegrand_le_GmajW6 hα g hθI
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hKper_nn : (0 : ℝ) ≤ 16777216 * 4000000 * (1 + max CB 1) :=
    mul_nonneg (by norm_num) (by linarith)
  have hJ6 : J ≤ 6 := by omega
  have hI6 : I ≤ 6 := by omega
  have hA2nn : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  -- Leibniz in the finite-order open class
  have heq := mixedMul_cd6 (f := f) (g := g) hf hg J I (by omega) z θ hz hθ0 hθ1
  -- `mixedMul_cd6` nests the two sums as `∑_{D_z} ∑_{D_θ}`; swap them to match `Y`
  have heq' : Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ
      = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          (I.choose a : ℝ) * (J.choose b : ℝ)
            * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (J - b) (I - a) g z θ) := by
    rw [heq, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((Work.Spaces.mixed b a f z θ)
        * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) with hYdef
  have hYsplit : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ)
          * Work.Spaces.Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq', Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  -- the pointwise bound for each summand of the double sum
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ (16777216 * 4000000 * (1 + max CB 1))
        * (Work.Spaces.WlInf α 6 f) ^ 2
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 16777216 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 4096 * 4096 :=
            mul_le_mul (Work.FTS.StrongPersist.N6.binom_sq_le_4096 I a (by omega) hI6)
              (Work.FTS.StrongPersist.N6.binom_sq_le_4096 J b (by omega) hJ6)
              (by positivity) (by norm_num)
        _ = 16777216 := by norm_num
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    by_cases hlt : a < I
    · -- at least one `θ`-derivative falls on `g`
      have hIa : 1 ≤ I - a := by omega
      have hma : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ 4000000 * (Work.Spaces.WlInf α 6 f) ^ 2 := by
        rcases eq_or_ne a 0 with ha0 | ha0
        · subst ha0
          have h : |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f :=
            dzIter_le_WlInf6_cd6 (α := α) (f := f) (b := b)
              (z := z) (θ := θ) hf hfm (by omega) hz hθ
          have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
              ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 := Work.Spaces.sq_le_sq_of_abs_le h
          show (Work.Spaces.DzIter b f z θ) ^ 2 ≤ 4000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          nlinarith [h1, sq_nonneg (1000 * Work.Spaces.WlInf α 6 f),
            sq_nonneg (Work.Spaces.WlInf α 6 f)]
        · have ha1 : 1 ≤ a := by omega
          have h := mixed_le_WlInf6_cd6 (α := α) (f := f)
            (a := a) (b := b) (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
          calc (Work.Spaces.mixed b a f z θ) ^ 2
              ≤ (1000 * (Work.Spaces.WlInf α 6 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
                Work.Spaces.sq_le_sq_of_abs_le h
            _ = (1000 * Work.Spaces.WlInf α 6 f) ^ 2
                  * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
                rw [mul_pow, mul_pow, phi_sq hθ]; ring
            _ ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 * 4 :=
                mul_le_mul_of_nonneg_left (psi2_le_four hα hα1 hθ) (sq_nonneg _)
            _ = 4000000 * (Work.Spaces.WlInf α 6 f) ^ 2 := by ring
      have hmg : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ (I - a) (J - b) hIa (by omega)
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (4000000 * (Work.Spaces.WlInf α 6 f) ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ (4000000 * (Work.Spaces.WlInf α 6 f) ^ 2)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hma (sq_nonneg _)
          _ ≤ (4000000 * (Work.Spaces.WlInf α 6 f) ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ :=
              mul_le_mul_of_nonneg_left hmg (by nlinarith [hWsq])
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 16777216 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 16777216 * ((4000000 * (Work.Spaces.WlInf α 6 f) ^ 2)
              * Work.Spaces.HkIntegrand α 6 g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 16777216 * 4000000 * (1 + max CB 1) * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
            rw [show 16777216 * ((4000000 * (Work.Spaces.WlInf α 6 f) ^ 2)
                  * Work.Spaces.HkIntegrand α 6 g z θ)
                = (16777216 * 4000000 : ℝ) * ((Work.Spaces.WlInf α 6 f) ^ 2
                  * Work.Spaces.HkIntegrand α 6 g z θ) from by ring]
            calc (16777216 * 4000000 : ℝ) * ((Work.Spaces.WlInf α 6 f) ^ 2
                  * Work.Spaces.HkIntegrand α 6 g z θ)
                ≤ (16777216 * 4000000 : ℝ) * ((Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHkG hWsq) (by norm_num)
              _ ≤ (16777216 * 4000000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 6 f) ^ 2
                      * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
                  mul_le_mul_of_nonneg_right (by nlinarith [hCBB0]) (mul_nonneg hWsq hGnn)
              _ = 16777216 * 4000000 * (1 + max CB 1) * (Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring
    · -- all `θ`-derivatives fall on `f`: the mean-term hypothesis is used
      have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hdJ : J - b ≤ 5 := by omega
      have hmb : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
        have ha1 : 1 ≤ a := by omega
        have h := mixed_le_WlInf6_cd6 (α := α) (f := f)
          (a := a) (b := b) (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
        calc (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ (1000 * (Work.Spaces.WlInf α 6 f
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le h
          _ = (1000 * Work.Spaces.WlInf α 6 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq hθ]; ring
      have hT : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        have he : Work.Spaces.mixed (J - b) (I - a) g = Work.Spaces.DzIter (J - b) g := by
          rw [hsub, Work.Spaces.mixed_zero_right]
        rw [he]
      have hgside : ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
            * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ max CB 1 * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
        mslot_gside_le6 (α := α) (CB := CB) (g := g) (d := J - b) hα hgm hCB hdJ hz hθ
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 * (max CB 1)
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hT]
          _ ≤ ((1000 * Work.Spaces.WlInf α 6 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hmb (sq_nonneg _)
          _ = (1000 * Work.Spaces.WlInf α 6 f) ^ 2
              * (((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
                * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2) := by ring
          _ ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2
                * (max CB 1 * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
              mul_le_mul_of_nonneg_left hgside (sq_nonneg _)
          _ = (1000 * Work.Spaces.WlInf α 6 f) ^ 2 * (max CB 1)
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 16777216 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 16777216 * ((1000 * Work.Spaces.WlInf α 6 f) ^ 2 * (max CB 1)
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 16777216 * 4000000 * (1 + max CB 1) * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
            rw [show 16777216 * ((1000 * Work.Spaces.WlInf α 6 f) ^ 2 * (max CB 1)
                  * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
                = (16777216 * 1000000 * (max CB 1)) * ((Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) from by ring]
            have hAB : (16777216 * 1000000 * (max CB 1) : ℝ)
                ≤ 16777216 * 4000000 * (1 + max CB 1) := by nlinarith [hCBB0]
            calc (16777216 * 1000000 * (max CB 1)) * ((Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
                ≤ (16777216 * 4000000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 6 f) ^ 2
                      * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
                  mul_le_mul_of_nonneg_right hAB (mul_nonneg hWsq hGnn)
              _ = 16777216 * 4000000 * (1 + max CB 1) * (Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring
  -- Cauchy–Schwarz on the double sum
  have hIJ49 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 49 := by
    have h1 : (I : ℝ) ≤ 6 := by exact_mod_cast hI6
    have h2 : (J : ℝ) ≤ 6 := by exact_mod_cast hJ6
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
    Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hper a ha b hb))
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
          * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
        rw [hsumconst]; ring
    _ ≤ 2401 * ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hKper_nn hWsq) hGnn)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ49, h0]
    _ ≤ (2 * 10 ^ 17 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
          * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
        rw [show 2401 * ((16777216 * 4000000 * (1 + max CB 1))
              * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
            = (2401 * (16777216 * 4000000 * (1 + max CB 1)))
                * ((Work.Spaces.WlInf α 6 f) ^ 2
                  * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) from by ring]
        have hle : 2401 * (16777216 * 4000000 * (1 + max CB 1))
            ≤ 2 * 10 ^ 17 * (1 + max CB 1) := by nlinarith [hCBB0]
        calc (2401 * (16777216 * 4000000 * (1 + max CB 1)))
              * ((Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
            ≤ (2 * 10 ^ 17 * (1 + max CB 1))
              * ((Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hWsq hGnn)
          _ = (2 * 10 ^ 17 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `zslot_le_winf6_cd6` — the radial `D_z`-slots of the `𝒲^{6,∞}`-priced product rule,
in the `C⁶`-on-the-open-quadrant class

This is the finite-order (`C⁶` on `Q0 = (0,∞) × (0,π/2)`, rather than `C^∞`) version of
`Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6`.  For `f` of class
`ContDiffOn ℝ 6 (uncurry f) Q0` and of class `𝒲^{6,∞}` (`WlInfMem α 6 f`), and for an
arbitrary `C⁶` `g`, every pure radial slot of the product `f·g` is dominated pointwise by the
`𝒲^{6,∞}`-norm of the coefficient times the `ℋ⁶`-integrand of `g`:

`(D_z^i (f·g)(z,θ) · w(z)/sin(2θ)^{η/2})² ≤ C |f|²_{𝒲^{6,∞}} · HkIntegrand α 6 g z θ`,
`i ≤ 6`,

with a universal constant `C` (here `10^12`), at every *interior* point `z > 0`,
`0 < θ < π/2`.

The proof is the same as in the `SmoothOpen` case; the only change is that the Leibniz
expansion of `D_z^i` in the open quadrant is taken from `mixedMul_cd6` (the `b = 0` case,
isolated as `DzIter_mul_cd6` below) instead of
`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`:

* expand `D_z^i (f·g)` with the Leibniz rule for `D_z = z∂_z`;
* bound the square of the finite sum by `card • Σ (·)²` (`sq_sum_le_card_mul_sum_sq`);
* bound each `f`-factor by `1000 |f|_𝒲` (`dzIter_le_WlInf6_cd6`) and each `g`-factor by the
  corresponding slot of `HkIntegrand α 6 g` (`Work.Spaces.sq_le_HkIntegrand_z`);
* bound the binomial coefficients by `4096` (`Nat.choose_le_two_pow`, `n ≤ 6`).

-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

/-- The binomial coefficients of the rows `0 ≤ n ≤ 6` are at most `64`, in particular
`squared` they are at most `4096` (via the coarse but purely structural bound
`n.choose k ≤ 2^n ≤ 2^6 = 64`). -/
private theorem choose_sq_le_4096 (n k : ℕ) (_hkn : k ≤ n) (hn : n ≤ 6) :
    ((n.choose k : ℕ) : ℝ) ^ 2 ≤ 4096 := by
  have h1 : n.choose k ≤ 64 := by
    have h2 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
    have h3 : 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : (2 : ℕ) ^ 6 = 64 := by norm_num
    omega
  have h1' : ((n.choose k : ℕ) : ℝ) ≤ 64 := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ ((n.choose k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := mul_self_le_mul_self h0 h1'
  rw [sq]
  norm_num at hm ⊢
  linarith [hm]

/-- **The Leibniz rule for `D_z^i` in the `C⁶`-class on the open quadrant.**
Isolated from `mixedMul_cd6` at `b = 0` (where `D_θ^0 = id`). -/
theorem DzIter_mul_cd6 {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {i : ℕ} (hi : i ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i - b) g z θ) := by
  have h := mixedMul_cd6 hf hg i 0 (by omega) z θ hz hθ0 hθ1
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Nat.zero_sub] at h
  rw [h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num

theorem zslot_le_winf6_cd6 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.WlInfMem α 6 f →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α f g _hα _hα1 hf hfm hg i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  -- the Leibniz expansion of `D_z^i (f·g)` in the open quadrant
  have heq := DzIter_mul_cd6 hf hg hi hz hθ0 hθ1
  have hsplit : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  -- Cauchy-Schwarz for the finite sum
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
      * (Work.Spaces.DzIter (i - b) g z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  -- the per-term bound: the `f`-factor costs `1000 |f|_𝒲`, the binomial coefficient costs `4096`
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f :=
      dzIter_le_WlInf6_cd6 hf hfm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 := by
      have hB : (0 : ℝ) ≤ 1000 * Work.Spaces.WlInf α 6 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 i b hbi hi
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 4096 * (1000 * Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by gcongr
      _ = 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  -- each surviving `g`-factor is a pure slot of `HkIntegrand α 6 g`
  have hsumsq : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 7 * Work.Spaces.HkIntegrand α 6 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 6 g z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 6 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 7 * Work.Spaces.HkIntegrand α 6 g z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 6 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : i + 1 ≤ 7)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
              * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          * (7 * (7 * Work.Spaces.HkIntegrand α 6 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : i + 1 ≤ 7)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 12 * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 6 g z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 6 f) ^ 2 := sq_nonneg _
        have hh : 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
              * (7 * (7 * Work.Spaces.HkIntegrand α 6 g z θ))
            = 200704000000 * ((Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 12 * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ
            = 10 ^ 12 * ((Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.wprod6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows

theorem wprod6 : ∃ Ci α₂ : ℝ, 0 < Ci ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.HQo α 6 g →
      Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g :=
  Work.FTS.StrongPersist.H6Rows.WProd6.wprod6_of_slots
    Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6
    Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6
    Work.FTS.StrongPersist.H6Rows.wprod6.mslot_le_winf6

end Work.FTS.StrongPersist.H6Rows
end
