import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
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
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderSlots
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts.sigTruncId
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.momentChainAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.ClassC.Fstar_eq_zero_of_bslOp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set MeasureTheory

namespace Work.FTS.ClassC

set_option autoImplicit false


/-- **The moment of the equation.**  If `bslOp α Ψ = F` on the *open* angular interval at the
radius `z`, then the two have the same angular moment at `z`: the two functions agree a.e. on
`Iθ` (they can differ only at `θ = 0` and `θ = π/2`), and a.e.-equal functions have equal
integrals.  (No measurability hypothesis is needed: `MeasureTheory.integral_congr_ae` is an
a.e.-congruence.) -/
theorem Fstar_bslOp_eq_Fstar {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (heq : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) z = Work.Elliptic.Fstar F z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  rw [MeasureTheory.ae_iff]
  have hset : {θ : ℝ | ¬ (θ ∈ Set.Icc 0 (Real.pi / 2)
      → Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ
        = F z θ * Work.Elliptic.sinCos2 θ)} ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp] at hθ
    obtain ⟨hIcc, hne⟩ := hθ
    by_contra hcon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
    obtain ⟨h0, h1⟩ := hcon
    exact hne (by rw [heq θ (lt_of_le_of_ne hIcc.1 (Ne.symm h0))
      (lt_of_le_of_ne hIcc.2 h1)])
  refine MeasureTheory.measure_mono_null hset ?_
  have hset2 : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [hset2]
  exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
    (MeasureTheory.measure_singleton _)



end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.CSQ_one =====
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

/-- **Cauchy–Schwarz at level `1`** for `H1IP`, with an `α`-free constant. -/
theorem CSQ_one (α : ℝ) (hα : 0 < α) :
    ∃ CC : ℝ, 0 < CC ∧ CSQ α 1 (Work.Coercivity.H1IP α) CC := by
  exact ⟨(10 : ℝ) ^ 22, by norm_num, fun X Y _ _ hX hY => H1IP_cs_of_mem α hα X Y hX hY⟩

end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.CSQ_one_unif =====
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

/-- **Cauchy–Schwarz for `H1IP` with the constant `10 ^ 22` pinned, for every `α > 0`.**

The witness chosen in the proof of `H1IP_cs_of_mem` is literally `(10 : ℝ) ^ 22`, so the
existential can be re-read with the constant instantiated; `α` occurs only in the
hypotheses, never in the constant. -/
theorem H1IP_cs_fixed (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.HkMem α 1 f) (hg : Work.Spaces.HkMem α 1 g) :
    |Work.Coercivity.H1IP α f g|
      ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g :=
  H1IP_cs_of_mem α hα f g hf hg

/-- **Cauchy–Schwarz at level `1` with an `α`-free constant.**  Unlike
`Transfer.CSQ_one` — which produces a (possibly `α`-dependent) constant for each `α > 0` —
this exhibits a single `CC = 10 ^ 22` that works for every `α > 0`.  The `Q0Sm`-smoothness
hypotheses of `CSQ` are simply unused at level `1`. -/
theorem CSQ_one_unif :
    ∃ CC : ℝ, 0 < CC ∧ ∀ (α : ℝ), 0 < α →
      Work.FTS.CoercivityFix.Transfer.CSQ α 1 (Work.Coercivity.H1IP α) CC := by
  refine ⟨(10 : ℝ) ^ 22, by norm_num, fun α hα X Y _ _ hX hY => ?_⟩
  exact H1IP_cs_fixed α hα X Y hX hY

end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.CommSm_L1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

noncomputable section

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-1 algebraic inputs of the transfer, in `Q0Sm` form.** -/
theorem CommSm_L1 (α : ℝ) (hα : 0 < α) :
    Work.FTS.CoercivityFix.Transfer.CommSm α 1 (Work.Coercivity.H1IP α) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Work.FTS.CoercivityFix.Assembly.Comm2_L1 α hα).congr
  · intro f₁ f₂ g h
    obtain ⟨h1, h2, hg, hm1, hm2, hmg⟩ := h
    exact H1IP_add_weak α hm1 hm2 hmg
      (h1.mixed_continuousOn (a := 0) (b := 0) (by norm_num))
      (h2.mixed_continuousOn (a := 0) (b := 0) (by norm_num))
      (hg.mixed_continuousOn (a := 0) (b := 0) (by norm_num))
      (h1.mixed_continuousOn (a := 0) (b := 1) (by norm_num))
      (h2.mixed_continuousOn (a := 0) (b := 1) (by norm_num))
      (hg.mixed_continuousOn (a := 0) (b := 1) (by norm_num))
      (h1.mixed_continuousOn (a := 1) (b := 0) (by norm_num))
      (h2.mixed_continuousOn (a := 1) (b := 0) (by norm_num))
      (hg.mixed_continuousOn (a := 1) (b := 0) (by norm_num))
      (Q0Sm.dz_add h1 h2) (Q0Sm.dth_add h1 h2)
  · exact (Work.FTS.CoercivityFix.Assembly.Comm2_L1 α hα).dthC
  · exact (Work.FTS.CoercivityFix.Assembly.Comm2_L1 α hα).dzC

end

end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.CommSm_succ =====
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

/-! ## Locality of the two derivatives on the open quadrant

Both facts are *pointwise on `Qd`*, which is the form in which the `congr` clause of
`CommSm` is stated.  (The corresponding helpers of `Assembly/Comm2_succ.lean` are `private`
there, hence re-proved here.) -/

/-- Two functions that agree on the open quadrant have the same `D_θ` there: the derivative
is local and `Qd` is open in the `θ`-variable. -/
private lemma Dth_congr_Qd_prv {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' ⟨hz, hθ'⟩
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [heq.deriv_eq]

/-- Two functions that agree on the open quadrant have the same `D_z` there. -/
private lemma Dz_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ ⟨hz', hθ⟩
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [heq.deriv_eq]

/-! ## The induction step of the package -/

/-- **`CommSm` climbs one level under the paper's recursion `HkIPStep c₁ c₂`.**

The congruence clause is transported through the two derivative-locality facts above; the
additivity clause through the two derivative-linearity facts `Q0Sm.dth_add` /
`Q0Sm.dz_add` together with the descent `HkMem_descent_Q0Sm` (and `Q0Sm.mono`, `Q0Sm.dth`,
`Q0Sm.dz`) from level `n+1` to level `n`; the two commutator clauses are inherited
verbatim, since they mention neither `n` nor `IP`. -/
theorem CommSm_succ (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {c₁ c₂ : ℝ}
    (h : Work.FTS.CoercivityFix.Transfer.CommSm α n IP) :
    Work.FTS.CoercivityFix.Transfer.CommSm α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP) := by
  refine ⟨?congr, ?add, h.dthC, h.dzC⟩
  case congr =>
    intro f f' g hfg
    have e0 := h.congr f f' g hfg
    have e1 := h.congr (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
      (Dth_congr_Qd_prv hfg)
    have e2 := h.congr (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
      (Dz_congr_Qd hfg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
  case add =>
    intro f₁ f₂ g hf
    obtain ⟨hf₁, hf₂, hg, hm₁, hm₂, hmg⟩ := hf
    -- the descent of both hypotheses from level `n + 1` to level `n`
    obtain ⟨hd₁, hd₁θ, hd₁z⟩ := HkMem_descent_Q0Sm α hα n hf₁ hm₁
    obtain ⟨hd₂, hd₂θ, hd₂z⟩ := HkMem_descent_Q0Sm α hα n hf₂ hm₂
    obtain ⟨hdg, hdgθ, hdgz⟩ := HkMem_descent_Q0Sm α hα n hg hmg
    have e0 := h.add f₁ f₂ g
      ⟨hf₁.mono (Nat.le_succ n), hf₂.mono (Nat.le_succ n), hg.mono (Nat.le_succ n),
        hd₁, hd₂, hdg⟩
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [h.congr (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (fun z θ hzθ =>
          Q0Sm.dth_add (hf₁.mono (by omega : 1 ≤ n + 1))
            (hf₂.mono (by omega : 1 ≤ n + 1)) z θ hzθ)]
      exact h.add (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        ⟨hf₁.dth, hf₂.dth, hg.dth, hd₁θ, hd₂θ, hdgθ⟩
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [h.congr (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (fun z θ hzθ =>
          Q0Sm.dz_add (hf₁.mono (by omega : 1 ≤ n + 1))
            (hf₂.mono (by omega : 1 ≤ n + 1)) z θ hzθ)]
      exact h.add (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        ⟨hf₁.dz, hf₂.dz, hg.dz, hd₁z, hd₂z, hdgz⟩
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
    ring

end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.Dth_LGammaT_eq =====
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

set_option autoImplicit false

/-- **The `T2`/`T4` pair of `Coer1T` is the defect `E1`**: the two `D_θΓ`-terms of the
`θ`-expansion of `D_θ(𝓛_Γ^T f)` add up to `sin(2θ)·Γ'(θ)·radA α f z`. -/
theorem T2_add_T4_eq_E1 (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ
      = Work.FTS.CoercivityFix.Transfer.E1 α f z θ := by
  rw [Work.Coercivity.T2, Work.Coercivity.T4, Work.Coercivity.C0,
    Work.FTS.CoercivityFix.Transfer.E1_eq, Work.FTS.CoercivityFix.Transfer.radA_eq,
    Work.Coercivity.DthGam_eq]
  ring


end Work.FTS.CoercivityFix.Transfer

end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.E1_angRad_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E1Norm.E1_angRad_le` — the angular/radial separation for the transfer defect `E1`

The transfer defect is the separated product

  `E1 α f = (D_θΓ) · (radA α f)`,   `D_θΓ = Lop (Gam α)`,

so write `a θ := Work.Spaces.Lop (Work.Spaces.Gam α) θ` and `r z := radA α f z`.  Since `D_z`
and `D_θ` only see the variable they differentiate, the pure slots of the weighted `ℋⁿ`-integrand
of `a·r` are exactly `a(θ)²·σ(θ)·(D_z^j r(z))²w(z)²` and the mixed slots are exactly
`(D_θ^i a)(θ)²·τ(θ)·(D_z^j r(z))²w(z)²` (`Nonlinear.Pieces.dzIter_ang_rad`,
`Nonlinear.Pieces.mixed_ang_rad`, `RadialProd.light_sq`, `RadialProd.heavy_sq`), where
`σ = sin(2θ)^{-η}` and `τ = sin(2θ)^{-γ}`.  Hence, on the open quadrant,

  `HkIntegrand α n (E1 α f) z θ ≤ R(z)·((K₁α)²σ(θ) + (n+1)(K₂α)² G(θ)²τ(θ))`,

with `R(z) = ∑_{j≤n} (D_z^j r(z))²w(z)²` and `G = Γ(θ)(sin²2θ + α)`, whenever
`|a| ≤ K₁α` and `|D_θ^i a| ≤ K₂α G` for `1 ≤ i ≤ 3`.  Both angular masses are `α`-independent
(and `f`-independent): `∫_θ σ ≤ 10⁴` (`Work.Spaces.sin_two_rpow`) and
`∫_θ G²τ ≤ 1000` (`GaugeMass.gauge_mass`), so integrating in `θ` and then in `z` gives

  `HkSq α n (E1 α f) ≤ C·α²·∫_z R(z)`.

The angular data is supplied by `Lop_iter_LopGam_Gamma_bound` (`i = 0`) and
`Lop_iter_LopGam_gauge_bound`, the `α²` being the `α`-smallness of `D_θΓ`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The angular factor of the pointwise bound: `(K₁α)²σ + (4(K₂α)²)G²τ`, written so that the
two angular masses factor out of the `θ`-integral with `integral_const_mul`. -/
private noncomputable def angF (α K₁ K₂ : ℝ) (θ : ℝ) : ℝ :=
  (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
    + (4 * (K₂ * α) ^ 2)
        * ((Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ)

/-- The radial density `∑_{j≤n} (D_z^j r)²w²`. -/
private noncomputable def rsum (n : ℕ) (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2

private lemma rsum_nonneg (n : ℕ) (r : ℝ → ℝ) (z : ℝ) : 0 ≤ rsum n r z := by
  rw [rsum]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The gauge profile `Γ(θ)(sin²2θ + α)` is integrable against `sin(2θ)^{-γ}` on `Iθ`, with
mass at most `1000` (`GaugeMass.gauge_mass`, rewritten in the form used below). -/
private lemma gauge_pair (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ 1000 := by
  obtain ⟨hint, hbd⟩ := gauge_mass α hα hα1
  have key : ∀ θ : ℝ,
      (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    intro θ
    rw [Work.FTS.Nonlinear.RadialProd.smG]
    ring
  refine ⟨hint.congr_fun (fun θ _ => key θ) measurableSet_Icc, ?_⟩
  have hcongr : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2
        * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ :=
    integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => key θ))
  rw [← hcongr]
  exact hbd

/-- Integrability of the angular factor `angF` on `Iθ` (stated for the unfolded form; the
`angF`-form is definitionally the same function). -/
private lemma angF_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K₁ K₂ : ℝ) :
    Integrable ((fun θ : ℝ => (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
      + fun θ : ℝ => (4 * (K₂ * α) ^ 2)
          * ((Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hE := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])
  have hsmE : Integrable (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hE.1
  have hGs : Integrable (fun θ : ℝ =>
      (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (gauge_pair α hα hα1).1
  exact (hsmE.const_mul ((K₁ * α) ^ 2)).add (hGs.const_mul (4 * (K₂ * α) ^ 2))

/-- The angular mass bound: `∫_θ angF ≤ α²(K₁²10⁴ + 4K₂²10³)` (for the unfolded form). -/
private lemma angF_integral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K₁ K₂ : ℝ) :
    (∫ θ in Work.Spaces.Iθ, (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + (4 * (K₂ * α) ^ 2) * ((Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ))
      ≤ α ^ 2 * (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3) := by
  have hE := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])
  have hsmE : Integrable (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hE.1
  have hEbd : (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ) ≤ 10 ^ 4 := by
    calc (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ)
        = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
      _ ≤ 100 / (-(Work.Spaces.eta) + 1) := hE.2
      _ = 10 ^ 4 := by rw [Work.Spaces.eta]; norm_num
  obtain ⟨hGsint, hGsbd⟩ := gauge_pair α hα hα1
  have hstep : (∫ θ in Work.Spaces.Iθ, (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + (4 * (K₂ * α) ^ 2) * ((Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ))
      ≤ (K₁ * α) ^ 2 * 10 ^ 4 + (4 * (K₂ * α) ^ 2) * 1000 := by
    rw [MeasureTheory.integral_add (hsmE.const_mul _) (hGsint.const_mul _)]
    simp only [MeasureTheory.integral_const_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hEbd (by positivity))
      (mul_le_mul_of_nonneg_left hGsbd (by positivity))
  refine le_trans hstep (le_of_eq ?_)
  ring

/-- **The pointwise (in `θ`) separation of the `ℋⁿ`-integrand of `E1`.** -/
private lemma HkIntegrand_E1_le (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : n ≤ 3)
    {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (ha : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Lop (Work.Spaces.Gam α) θ| ≤ K₁ * α)
    (hb : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ|
        ≤ K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)))
    (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.HkIntegrand α n (E1 α f) z θ
      ≤ rsum n (radA α f) z * angF α K₁ K₂ θ := by
  change Work.Spaces.HkIntegrand α n
      (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
    ≤ rsum n (radA α f) z * angF α K₁ K₂ θ
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg hθI
  have hsmGnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
    Work.FTS.Nonlinear.RadialProd.smG_nonneg hθI
  have hGnn : 0 ≤ Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α) := by
    refine mul_nonneg (Work.Spaces.Gam_bounds α θ hα hθI).1 ?_
    nlinarith [hα, sq_nonneg (Real.sin (2 * θ))]
  have hRnn : 0 ≤ rsum n (radA α f) z := rsum_nonneg n (radA α f) z
  -- ### the two angular bounds
  have ha2 : (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 ≤ (K₁ * α) ^ 2 := by
    have h1 : 0 ≤ K₁ * α := mul_nonneg hK₁ hα.le
    have h2 : |Work.Spaces.Lop (Work.Spaces.Gam α) θ| ≤ |K₁ * α| := by
      rw [abs_of_nonneg h1]
      exact ha θ hθI
    calc (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2
        = |Work.Spaces.Lop (Work.Spaces.Gam α) θ| ^ 2 := by rw [sq_abs]
      _ ≤ |K₁ * α| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (K₁ * α) ^ 2 := by rw [sq_abs]
  have hb2 : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
        ≤ (K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))) ^ 2 := by
    intro i hi1 hin
    have hi3 : i ≤ 3 := by omega
    have h1 : 0 ≤ K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) :=
      mul_nonneg (mul_nonneg hK₂ hα.le) hGnn
    have h2 : |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ|
        ≤ |K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))| := by
      rw [abs_of_nonneg h1]
      exact hb i hi1 hi3 θ hθI
    calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
        = |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ| ^ 2 :=
          by rw [sq_abs]
      _ ≤ |K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))) ^ 2 := by rw [sq_abs]
  -- ### the pure `D_z`-slots
  have hpure : (∑ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        * rsum n (radA α f) z := by
    have hterm : ∀ i : ℕ,
        (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          * ((Work.Elliptic.DzdIter i (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i
      rw [Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
        show (Work.Spaces.Lop (Work.Spaces.Gam α) θ * Work.Elliptic.DzdIter i (radA α f) z
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = ((Work.Spaces.Lop (Work.Spaces.Gam α) θ
                * Work.Elliptic.DzdIter i (radA α f) z)
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          from by ring,
        Work.FTS.Nonlinear.RadialProd.light_sq _ z θ hsin]
      ring
    calc (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (n + 1),
            (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              * ((Work.Elliptic.DzdIter i (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            * rsum n (radA α f) z := by
          rw [← Finset.mul_sum, rsum]
  have hpure' : (∑ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ * rsum n (radA α f) z := by
    rw [hpure]
    exact mul_le_mul_of_nonneg_right (mul_le_mul ha2 le_rfl hsmEnn (sq_nonneg _)) hRnn
  -- ### the mixed `D_θ`-slots
  have hmix : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ rsum n (radA α f) z
        * (∑ i ∈ Finset.range (n + 1), if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ else 0) := by
    have hterm2 : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ (if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
          * ((Work.Elliptic.DzdIter j (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i hi j hj
      by_cases h1 : 1 ≤ i
      · by_cases h2 : i + j ≤ n
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
          rw [Work.FTS.Nonlinear.Pieces.mixed_ang_rad,
            show (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ
                  * Work.Elliptic.DzdIter j (radA α f) z * Work.Spaces.Wt α z θ) ^ 2
                = ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ
                    * Work.Elliptic.DzdIter j (radA α f) z) * Work.Spaces.Wt α z θ) ^ 2
              from by ring,
            Work.FTS.Nonlinear.RadialProd.heavy_sq α _ z θ hsin]
          exact le_of_eq (by ring)
        · rw [if_neg (fun h => h2 h.2), if_pos h1]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) hsmGnn)
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
        simp
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n then
            (Work.Spaces.mixed j i
                (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
                  * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
              * ((Work.Elliptic.DzdIter j (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = rsum n (radA α f) z
            * (∑ i ∈ Finset.range (n + 1), if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
                  * Work.FTS.Nonlinear.RadialProd.smG α θ else 0) := by
          rw [← Finset.sum_mul_sum, rsum]
          ring
  -- ### the comparison of the angular profiles
  have hMsum : (∑ i ∈ Finset.range (n + 1), if 1 ≤ i then
        (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
      ≤ ((n : ℝ) + 1) * ((K₂ * α) ^ 2
          * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
    have hCEnn : 0 ≤ (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsmGnn
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
        ≤ (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      intro i hi
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1]
        have hin : i ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        have hb2i := hb2 i h1 hin
        have hkey : (K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))) ^ 2
            = (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2 := by
          ring
        calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ
            ≤ (K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ :=
              mul_le_mul_of_nonneg_right hb2i hsmGnn
          _ = (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ := by rw [hkey]
      · rw [if_neg h1]
        exact hCEnn
    calc (∑ i ∈ Finset.range (n + 1), if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
        ≤ ∑ i ∈ Finset.range (n + 1),
            (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ := Finset.sum_le_sum hterm
      _ = ((n : ℝ) + 1) * ((K₂ * α) ^ 2
              * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hn4 : ((n : ℝ) + 1) ≤ 4 := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  have hCEnn : 0 ≤ (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smG α θ :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsmGnn
  have hmix' : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ rsum n (radA α f) z
        * (((n : ℝ) + 1) * ((K₂ * α) ^ 2
            * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ)) :=
    le_trans hmix (mul_le_mul_of_nonneg_left hMsum hRnn)
  -- ### assembly
  have hHk : Work.Spaces.HkIntegrand α n
      (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
      = (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            if 1 ≤ i ∧ i + j ≤ n then
              (Work.Spaces.mixed j i
                  (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0 := by
    rw [Work.Spaces.HkIntegrand]
  calc Work.Spaces.HkIntegrand α n
        (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
      = (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            if 1 ≤ i ∧ i + j ≤ n then
              (Work.Spaces.mixed j i
                  (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0 := hHk
    _ ≤ (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ * rsum n (radA α f) z
          + rsum n (radA α f) z
            * (((n : ℝ) + 1) * ((K₂ * α) ^ 2
                * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ)) := add_le_add hpure' hmix'
    _ = rsum n (radA α f) z
          * ((K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            + ((n : ℝ) + 1) * ((K₂ * α) ^ 2
                * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by ring
    _ ≤ rsum n (radA α f) z
          * ((K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * ((K₂ * α) ^ 2
                * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hRnn
        exact mul_le_mul_of_nonneg_right hn4 hCEnn
    _ = rsum n (radA α f) z * angF α K₁ K₂ θ := by
        rw [angF]
        ring

theorem E1_angRad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz →
      Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
        ≤ C * α ^ 2 * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Lop_iter_LopGam_Gamma_bound
  obtain ⟨K₂, hK₂pos, hK₂⟩ := Lop_iter_LopGam_gauge_bound
  refine ⟨K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3 + 1, by positivity, ?_⟩
  intro α n f hα hα1 hn hint
  -- ## the angular data of the profile `D_θΓ = Lop (Gam α)`
  have ha : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Lop (Work.Spaces.Gam α) θ| ≤ K₁ * α := by
    intro θ hθ
    have h := hK₁ α hα hα1 0 (by norm_num) θ hθ
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hKα : 0 ≤ K₁ * α := mul_nonneg hK₁pos.le hα.le
    calc |Work.Spaces.Lop (Work.Spaces.Gam α) θ|
        = |(Work.Spaces.Lop^[0] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ| := rfl
      _ ≤ K₁ * α * Work.Spaces.Gam α θ := h
      _ ≤ K₁ * α * 1 := by nlinarith [hKα, hG]
      _ = K₁ * α := by ring
  have hb : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ|
        ≤ K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) := by
    intro i hi1 hi3 θ hθ
    have h := hK₂ α hα hα1 i hi1 hi3 θ hθ
    have htl : Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ
        = (Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ := by
      rw [Work.Spaces.DthIter_eq_iterate_Lop]
    calc |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ|
        = |(Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ| := by rw [htl]
      _ ≤ K₂ * α * Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α) := h
      _ = K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) := by ring
  -- ## the angular factor
  have hPHIint : MeasureTheory.IntegrableOn (angF α K₁ K₂) Work.Spaces.Iθ :=
    angF_integrable α hα hα1 K₁ K₂
  have hPHIbd : (∫ θ in Work.Spaces.Iθ, angF α K₁ K₂ θ)
      ≤ α ^ 2 * (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3) :=
    angF_integral_le α hα hα1 K₁ K₂
  have hradsum_int : Integrable (fun z => rsum n (radA α f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hint
  -- ## the angular integral, slice by slice
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (E1 α f) z θ)
        ≤ rsum n (radA α f) z * (∫ θ in Work.Spaces.Iθ, angF α K₁ K₂ θ) := by
    intro z hz
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        Work.Spaces.HkIntegrand α n (E1 α f) z θ
          ≤ rsum n (radA α f) z * angF α K₁ K₂ θ :=
      fun θ hθ => HkIntegrand_E1_le α hα n hn hK₁pos.le hK₂pos.le ha hb f z θ hθ
    have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
      exact MeasureTheory.Ioo_ae_eq_Icc
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α n (E1 α f) z θ
          ≤ rsum n (radA α f) z * angF α K₁ K₂ θ := by
      have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))),
          Work.Spaces.HkIntegrand α n (E1 α f) z θ
            ≤ rsum n (radA α f) z * angF α K₁ K₂ θ :=
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hpt
      rwa [MeasureTheory.Measure.restrict_congr_set hIoo] at h1
    have h1 := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α n (E1 α f) z θ)
      (g := fun θ => rsum n (radA α f) z * angF α K₁ K₂ θ)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (E1 α f) z θ)
      (hPHIint.const_mul (rsum n (radA α f) z))
      hae
    rwa [MeasureTheory.integral_const_mul] at h1
  -- ## the radial integral
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (E1 α f) z θ)
    (g := fun z => rsum n (radA α f) z * (∫ θ in Work.Spaces.Iθ, angF α K₁ K₂ θ))
    (Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n (E1 α f) z θ)
    (hradsum_int.mul_const _)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
  rw [MeasureTheory.integral_mul_const] at houter
  -- ## assembly
  have hRnn : 0 ≤ ∫ z in Work.Spaces.Iz, rsum n (radA α f) z :=
    integral_nonneg fun z => rsum_nonneg n (radA α f) z
  rw [Work.Spaces.HkSq]
  refine le_trans houter ?_
  calc (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)
        * (∫ θ in Work.Spaces.Iθ, angF α K₁ K₂ θ)
      ≤ (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)
          * (α ^ 2 * (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3)) :=
        mul_le_mul_of_nonneg_left hPHIbd hRnn
    _ ≤ (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3 + 1) * α ^ 2
          * (∫ z in Work.Spaces.Iz, rsum n (radA α f) z) := by
        rw [show (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)
              * (α ^ 2 * (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3))
            = (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3)
              * (α ^ 2 * (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)) by ring]
        rw [show (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3 + 1) * α ^ 2
              * (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)
            = (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3 + 1)
              * (α ^ 2 * (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg (sq_nonneg _) hRnn)

end Work.FTS.CoercivityFix.Transfer.E1Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.HkMemE1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The radial majorant `Rint(z) = ∑_{j<4} (D_z^j r z)² w(z)²`. -/
private noncomputable def radMaj (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 4, (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2

/-- The angular majorant `G(θ) = Γ(θ)² sin(2θ)^{-η} + Γ(θ)² sin(2θ)^{-γ}`. -/
private noncomputable def angMaj (α : ℝ) (θ : ℝ) : ℝ :=
  (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
    + (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ

private theorem angMaj_eq (α θ : ℝ) :
    angMaj α θ = (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := rfl

private theorem radMaj_eq (r : ℝ → ℝ) (z : ℝ) :
    radMaj r z = ∑ j ∈ Finset.range 4,
      (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl

private theorem radMaj_nonneg (r : ℝ → ℝ) (z : ℝ) : 0 ≤ radMaj r z :=
  Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem angMaj_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angMaj α θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have h1 : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ := by
    rw [Work.FTS.Nonlinear.RadialProd.smE]; exact Real.rpow_nonneg hsin _
  have h2 : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ := by
    rw [Work.FTS.Nonlinear.RadialProd.smG]; exact Real.rpow_nonneg hsin _
  rw [angMaj_eq]
  exact add_nonneg (mul_nonneg (sq_nonneg _) h1) (mul_nonneg (sq_nonneg _) h2)

/-- The Gamman bound `Γ ≥ 0` on `Iθ`. -/
private theorem Gam_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.Gam α θ := by
  rw [show Work.Spaces.Gam α = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl]
  exact Real.rpow_nonneg (mul_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
    (sq_nonneg _)) _

/-! ## The pointwise domination -/

theorem HkIntegrand_E1_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (n : ℕ) (hn : n ≤ 3) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.Transfer.E1 α f) z θ
        ≤ 10 ^ 18 * angMaj α θ * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
  obtain ⟨hAng, hAngE, hAngG⟩ := AngGam α hα hα1
  set a : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ with ha
  set r : ℝ → ℝ := Work.FTS.CoercivityFix.Transfer.radA α f with hr
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hE1 : Work.FTS.CoercivityFix.Transfer.E1 α f = fun z θ => a θ * r z := rfl
  have hsmE_nn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ := by
    rw [Work.FTS.Nonlinear.RadialProd.smE]; exact Real.rpow_nonneg hsin _
  have hsmG_nn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ := by
    rw [Work.FTS.Nonlinear.RadialProd.smG]; exact Real.rpow_nonneg hsin _
  have hΓnn : 0 ≤ Work.Spaces.Gam α θ := Gam_nonneg hθ
  have hGnn : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ :=
    mul_nonneg (sq_nonneg _) hsmE_nn
  have hGnn' : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ :=
    mul_nonneg (sq_nonneg _) hsmG_nn
  have hAngnn : 0 ≤ angMaj α θ := angMaj_nonneg α hθ
  have hRnn : 0 ≤ radMaj r z := radMaj_nonneg r z
  -- the bound on the angular factor `a = D_θ Γ`
  have ha_lop : a = Work.Spaces.Lop (Work.Spaces.Gam α) := rfl
  have ha_bound : |a θ| ≤ 10 ^ 8 * Work.Spaces.Gam α θ := by
    have h := hAng 1 (by norm_num) (by norm_num) θ hθ
    rw [Function.iterate_one] at h
    rwa [← ha_lop] at h
  have ha_sq : (a θ) ^ 2 ≤ (10 ^ 8 * Work.Spaces.Gam α θ) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg (by norm_num) hΓnn)]
    exact ha_bound
  -- the `D_θ`-blocks of the angular factor
  have hbang_bound : ∀ i : ℕ, i ≤ 3 →
      |Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ| ≤ 10 ^ 8 * Work.Spaces.Gam α θ := by
    intro i hi
    have hconv : Work.Spaces.Lop^[i] (fun θ' : ℝ => a θ')
        = Work.Spaces.Lop^[i + 1] (Work.Spaces.Gam α) := by
      have : (fun θ' : ℝ => a θ') = Work.Spaces.Lop (Work.Spaces.Gam α) := rfl
      rw [this, ← Function.iterate_succ_apply]
    have h1 : Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ
        = (Work.Spaces.Lop^[i + 1] (Work.Spaces.Gam α)) θ := by
      rw [Work.Spaces.DthIter_eq_iterate_Lop]
      show (Work.Spaces.Lop^[i] (fun θ' : ℝ => a θ')) θ = _
      rw [hconv]
    rw [h1]
    exact hAng (i + 1) (by omega) (by omega) θ hθ
  have hbang_sq : ∀ i : ℕ, i ≤ 3 →
      (Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ) ^ 2
        ≤ (10 ^ 8 * Work.Spaces.Gam α θ) ^ 2 := by
    intro i hi
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg (by norm_num) hΓnn)]
    exact hbang_bound i hi
  -- the per-term bounds
  have hterm1 : ∀ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ 10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
            * radMaj r z := by
    intro i hi
    have hi3 : i ≤ 3 := by
      have := Finset.mem_range.mp hi
      omega
    have hRle : (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ radMaj r z := by
      refine Finset.single_le_sum (f := fun j => (Work.Elliptic.DzdIter j r z) ^ 2
        * (Work.Spaces.w z) ^ 2) (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
      exact Finset.mem_range.mpr (by omega)
    have hwk : 0 ≤ (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [Work.FTS.Nonlinear.Pieces.dzIter_ang_rad a r i z θ,
      Work.FTS.NonlinRows.AuxAngRad.light_sq_nn (a θ * Work.Elliptic.DzdIter i r z) z θ hsin]
    have hkey : (a θ * Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smE θ
        = ((a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
          * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      ring
    rw [hkey]
    calc ((a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
          * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ((10 ^ 8 * Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
            * radMaj r z :=
          mul_le_mul (mul_le_mul ha_sq le_rfl hsmE_nn (sq_nonneg _)) hRle hwk
            (mul_nonneg (sq_nonneg _) hsmE_nn)
      _ = 10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
            * radMaj r z := by ring
  have hterm2 : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ 10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * radMaj r z := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc]
      have hi3 : i ≤ 3 := by
        have := Finset.mem_range.mp hi
        omega
      have hj3 : j ≤ 3 := by
        have := Finset.mem_range.mp hj
        omega
      have hRle : (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ radMaj r z := by
        refine Finset.single_le_sum (f := fun j => (Work.Elliptic.DzdIter j r z) ^ 2
          * (Work.Spaces.w z) ^ 2) (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
        exact Finset.mem_range.mpr (by omega)
      have hwk : 0 ≤ (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      rw [Work.FTS.Nonlinear.Pieces.mixed_ang_rad a r j i z θ,
        Work.FTS.NonlinRows.AuxAngRad.heavy_sq_nn α
          (Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ * Work.Elliptic.DzdIter j r z) z θ hsin]
      have hkey : (Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ
              * Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ
          = ((Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
      rw [hkey]
      calc ((Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ((10 ^ 8 * Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
              * radMaj r z :=
            mul_le_mul (mul_le_mul (hbang_sq i hi3) le_rfl hsmG_nn (sq_nonneg _)) hRle hwk
              (mul_nonneg (sq_nonneg _) hsmG_nn)
        _ = 10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
              * radMaj r z := by ring
    · rw [if_neg hc]
      exact mul_nonneg (mul_nonneg (by norm_num) hGnn') hRnn
  -- the two sums
  have hsum1 : (∑ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
          * radMaj r z) := by
    have h := Finset.sum_le_sum hterm1
    have hcard : (∑ _i ∈ Finset.range (n + 1),
        (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
          * radMaj r z))
        = ((n : ℝ) + 1) * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smE θ) * radMaj r z) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [hcard] at h
    have hn4 : ((n : ℝ) + 1) ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    refine le_trans h (mul_le_mul_of_nonneg_right hn4 ?_)
    exact mul_nonneg (mul_nonneg (by norm_num) hGnn) hRnn
  have hsum2 : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 16 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
          * radMaj r z) := by
    have hinner : ∀ i ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1),
          (if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0))
          ≤ 4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
              * radMaj r z) := by
      intro i hi
      have h := Finset.sum_le_sum (fun j hj => hterm2 i hi j hj)
      have hcard : (∑ _j ∈ Finset.range (n + 1),
          (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * radMaj r z))
          = ((n : ℝ) + 1) * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      rw [hcard] at h
      have hn4 : ((n : ℝ) + 1) ≤ 4 := by
        have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
        linarith
      refine le_trans h (mul_le_mul_of_nonneg_right hn4 ?_)
      exact mul_nonneg (mul_nonneg (by norm_num) hGnn') hRnn
    have h := Finset.sum_le_sum hinner
    have hcard : (∑ _i ∈ Finset.range (n + 1),
        (4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
          * radMaj r z)))
        = ((n : ℝ) + 1) * (4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [hcard] at h
    have hn4 : ((n : ℝ) + 1) ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    refine le_trans h ?_
    have hb : 0 ≤ 4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hGnn') hRnn)
    calc ((n : ℝ) + 1) * (4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z))
        ≤ 4 * (4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z)) :=
          mul_le_mul_of_nonneg_right hn4 hb
      _ = 16 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * radMaj r z) := by ring
  rw [hE1, Work.Spaces.HkIntegrand, angMaj_eq α θ]
  refine le_trans (add_le_add hsum1 hsum2) ?_
  nlinarith [hsum1, hsum2, hGnn, hGnn', hRnn]

/-! ## `HkMem` from the radial input -/

theorem HkMem_E1_of (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (n : ℕ) (hn : n ≤ 3)
    (hcont : Work.FTS.CoercivityFix.Assembly.BlocksCont n
      (Work.FTS.CoercivityFix.Transfer.E1 α f))
    (hrad : ∀ j : ℕ, j ≤ 3 → IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E1 α f) := by
  obtain ⟨hAng, hAngE, hAngG⟩ := AngGam α hα hα1
  have hGint : IntegrableOn (fun θ : ℝ => angMaj α θ) Work.Spaces.Iθ := by
    have h := hAngE.add hAngG
    have hfun : (fun θ : ℝ => angMaj α θ) = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smE θ
        + (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      funext θ; rw [angMaj_eq]
    rw [hfun]
    exact h
  have hRint : IntegrableOn (fun z : ℝ => radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      Work.Spaces.Iz := by
    have hfun : (fun z : ℝ => radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        = fun z : ℝ => ∑ j ∈ Finset.range 4,
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2 := by
      funext z; rw [radMaj_eq]
    rw [hfun]
    exact MeasureTheory.integrable_finsetSum (Finset.range 4)
      (fun j hj => hrad j (by have := Finset.mem_range.mp hj; omega))
  refine Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.FTS.CoercivityFix.Transfer.E1 α f)
    (M := fun z θ => 10 ^ 18 * angMaj α θ * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
    ?_ ?_ ?_ ?_
  · exact Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont hcont α
  · intro z _
    have hfun : (fun θ : ℝ => 10 ^ 18 * angMaj α θ
        * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        = fun θ : ℝ => (10 ^ 18 * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
            * angMaj α θ := by
      funext θ; ring
    rw [hfun]
    exact hGint.const_mul _
  · have hfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        10 ^ 18 * angMaj α θ * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        = fun z : ℝ => (10 ^ 18 * (∫ θ in Work.Spaces.Iθ, angMaj α θ))
            * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
      funext z
      have h1 : (fun θ : ℝ => 10 ^ 18 * angMaj α θ
          * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          = fun θ : ℝ => (10 ^ 18 * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
              * angMaj α θ := by
        funext θ; ring
      rw [h1, MeasureTheory.integral_const_mul]
      ring
    rw [hfun]
    exact hRint.const_mul _
  · intro z hz θ hθ
    exact HkIntegrand_E1_le α hα hα1 n hn z hz θ hθ

end Work.FTS.CoercivityFix.Transfer.E1Parts
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAId =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000






end Work.FTS.CoercivityFix.Transfer.E1Parts
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixIntS_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- The `∂_θ²`-slice functional `ttIntS` is pointwise nonnegative. -/
theorem ttIntS_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Work.EllipticEst.Core.ttIntS u z := by
  rw [Work.EllipticEst.Core.ttIntS]
  refine mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae ?_)
  exact MeasureTheory.ae_restrict_of_forall_mem
    (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))

/-- `mixIntS Φ 0 = 0` because the radial weight vanishes at `z = 0`. -/
theorem mixIntS_zero (u : ℝ → ℝ → ℝ) : Work.EllipticEst.Core.mixIntS u 0 = 0 := by
  rw [Work.EllipticEst.Core.mixIntS, Work.Spaces.w]
  norm_num

/-- **Integrability of the mixed functional of the log-mollified datum** (this is conjunct 4 of
`Work.FTS.EllSol.EllPkgAux.mollDom_fts`).

For `G` in the trace class with honest functionals and `δ, ε ∈ (0,1/2]`,

  `IntegrableOn (fun z => ∫_θ (D_z ∂_θ (zmoll G δ ε)(z,θ))² σ_η(θ) · w(z)²) Iz`.

Here the constant may depend on `δ, ε` (only finiteness/integrability is claimed).

Intended route: `D_z ∂_θ Φ = ∂_θ (D_z Φ)` (Clairaut, `Φ = zmoll G δ ε` is `C^∞` on the strip by
`mollAdm`), then the log-mollification commutation and the `θ`-fold
`D_z Φ(z,θ) = ∫_t sKer δ (log z - t) (∫_{Iθ} km ε θ s D_zG (e^t) s ds) dt`
(`km` the signed three-image kernel), whose `θ`-derivative is
`∂_θ (D_z Φ)(z,θ) = ∫_t sKer δ (log z - t)(∫_{Iθ} ∂_θ km ε θ s · D_zG (e^t) s ds)dt`
(derivative on the kernel, so that only `∫_{Iθ}|D_zG w s| ds < ∞` — available from
`SliceHonestOpen G` — is needed).  Cauchy–Schwarz in `s` with the splitting
`∂_θ km ε θ s = (∂_θ km ε θ s σ_η(s)^{-1/2})·σ_η(s)^{1/2}` gives
`(∫_s ∂_θ km · D_zG)² ≤ A_ε(θ) · ∫_s σ_η(s)(D_zG w s)² ds` with `A_ε(θ) = ∫_{Iθ}(∂_θ km ε θ s)² σ_η(s)^{-1} ds`,
and `A_ε(θ) ≤ C/ε³` uniformly in `θ` (since `|∂_θ km| ≤ 3 sup|sKerd ε| ≤ C/ε²` and
`σ_η^{-1} = sin(2·)^{η} ≤ 1`).  Then Jensen in `t` (the kernel `sKer δ` is a probability density),
integrate `θ` against `σ_η` (finite measure), and finally integrate over `z` with the weight
comparison `w(z)² ≤ 5 w(e^t)²` (`wExpCmp`) and the change of variables `y = e^t`, which bounds the
whole thing by `(C'/ε³) ∫_z w(z)² ∫_θ σ_η(θ)(D_zG z θ)² = (C'/ε³) ∫ dIntS G < ∞` (this is
`FourInts G`).  Hence (nonnegative, measurable) the functional is integrable. -/
theorem zmoll_mixIntS_integrable (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    MeasureTheory.IntegrableOn (fun z : ℝ =>
      Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) Work.Spaces.Iz := by
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  have hPr : Work.FTS.EllSol.EllPkgAux.Params δ ε := ⟨hε0, hε1, hδ0, hδ1⟩
  set Φ : ℝ → ℝ → ℝ := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε with hΦ
  -- strip-admissibility of the mollified datum (this is `mollAdm`)
  have hstrip : Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε :=
    Work.FTS.EllSol.EllPkgAux.MollAssem.mollAdmMFA G hT hF δ ε hPr
  -- hence it is `C^∞` on the open quadrant, so the slice functional is a.e. strongly measurable
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.FTS.EllSol.EllPkgAux.Strp := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ⟨hp1, by linarith, by linarith [hp3, Real.pi_pos]⟩
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => (hstrip.1 n).mono hsub)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ =>
      Work.EllipticEst.Core.mixIntS Φ z) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := Work.Blocks.StripMajorantAux.aesm_mixIntS_dzIter hsm 0
    simpa only [Work.Spaces.DzIter_zero] using h
  -- the pointwise domination by the logarithmic window average of `ttIntS G`
  obtain ⟨C, hC, hbound⟩ :=
    Work.FTS.EllSol.EllPkgAux.MollDom.mixIntS_zmoll_le_indicator G hT hF δ ε hPr
  -- the majorant is integrable on `(0,∞)`
  have htt : MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z)
      (Set.Ioi (0 : ℝ)) := hF.2.2.1.mono_set Set.Ioi_subset_Ici_self
  have hMajIoi : MeasureTheory.IntegrableOn (fun z : ℝ => C * ∫ t : ℝ,
      (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0))
      (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.EllSol.EllPkgAux.MollDom.indicatorLog_integrable hδ0 htt (ttIntS_nonneg G)).const_mul C
  have hMajIz : MeasureTheory.IntegrableOn (fun z : ℝ => C * ∫ t : ℝ,
      (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0))
      Work.Spaces.Iz := by
    have hEq : (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    rw [Work.Spaces.Iz]
    show MeasureTheory.Integrable (fun z : ℝ => C * ∫ t : ℝ,
      (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0))
      (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))
    rw [hEq]
    exact hMajIoi
  -- assemble with the pointwise domination
  refine MeasureTheory.Integrable.mono' hMajIz haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)]
    with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Work.FTS.EllSol.EllPkgAux.MollAssem.mixIntS_nonneg_mfa Φ z)]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
  · rw [← h0, mixIntS_zero]
    refine mul_nonneg hC.le (MeasureTheory.integral_nonneg (fun t => ?_))
    split_ifs with ht
    · exact ttIntS_nonneg G _
    · exact le_rfl
  · exact hbound z hpos

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMSliceA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)






end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.sigFirstOrderD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeS1

/-!
**The σ-weighted first-order energy inequality** for the almost-everywhere class
`H2W.Ae.AeData` (Elgindi, Annals 194 (2021), Step 1/Step 2 hybrid): it bounds both
`α²‖z∂_zu‖²_ρ` (the radial slot) and `‖u/cos θ‖²_ρ` (the `Ψ`-slot) by `C(‖G‖²_ρ + ‖u‖²_ρ)`.

## Route (all ingredients are proved and axiom-clean; nothing here is a duplicate statement)

Pair `bslOp α u = G` with `u·w²σ`, `σ = sin(2θ)^{-η}` (the *first-order* pairing, not the
`-∂_θθu` pairing of Step 2), i.e. use the **σ-weighted slice self-form**
  `∫_θ (Lzero1 u z ·)(u z ·) σ  =  ∫_θ (∂_θu)²σ + ½∫_θ (u/cos θ)²σ - 6∫_θ u²σ`
(proved for the unweighted case as `Honest.HonSliceSelfForm` / `H2W.AeProof.AeSliceSelfForm`;
the σ-weighted case follows by the same primitive
`F θ = -(v'θ)v θ·σ - ½ v θ²·(∂_θ(σ))-type` computation, with the two ingredients
  * `∂_θθ(sin(2θ)^{-η}) = 4η(η+1)cos²(2θ)sin^{-(2+η)}(2θ) + 4η sin^{-η}(2θ)` (the paper's
    identity), and
  * the sharp Hardy inequality `Work.FTS.EllipticEst.hardy_shift_two_same_weight`
    (`∫f²sin^{-(2+η)}(2θ) ≤ (1+η)^{-2}∫(f')²σ + C∫f²σ`, proved) applied to the slice `u z ·`,
    together with the elementary bound `|tan θ·∂_θσ| ≤ η sec²θ·σ`;
  these give, a.e. in `z`,
  `((1-η)/(1+η))∫_θ(∂_θu)²σ + ((1-η)/2)∫_θ(u/cos θ)²σ ≤ ∫_θ (Lzero1 u·u)σ + C∫_θ u²σ`
  (the numerical gains `(1-η)/(1+η) = 1/199 > 0` and `(1-η)/2 > 0` are exactly the ones used in
  the paper's `I₁`).
Then multiply by `Wcut χ = χ·w²` for the cutoff family `Work.FTS.EllipticEst.cut n`, integrate in
`z`, and use the θ-sliced radial integration by parts
`Work.FTS.EllipticEst.Dispatch.sliceZibpD` / `remov.ibpZZ`/`ibpZ` (`χ` compactly supported in
`(0,∞)`):
  `∫_z χw²z²u''u = -∫_zχw²(D_zu)² + ½∫_z(z²χw²)''u²`,  `∫_zχw²zu'u = -½∫_z(zχw²)'u²`;
AM–GM (`2|ab| ≤ εa² + b²/ε`) absorbs every cross term into the two positive slots, and
`∫∫χw²|G||u| ≤ ½∫∫χw²G²σ + ½∫∫χw²u²` (`1/σ ≤ 1`) gives the source slot.  Passing to the limit
`χ = cut n` (monotone convergence for the nonnegative slots, `AeCutErr` for the truncation
error, the case `∫⁻w²∫⁻u²σ = ⊤` being trivial) gives the two inequalities of the statement.
The first `L2Mem` conjunct is `HkMem α 0 (grad u)`, available as
`Work.FTS.EllipticEst.AeS1.hkMem_gradU` (`Dispatch.hkMemGradU`).
The third conjunct (`u/cos θ`) follows from the same σ-weighted pairing: the
`sec²θ`-slot above controls `∫_θ(u/cos θ)²σ` directly (no further Hardy is needed here, since
`sec²θ ≥ 1`).
-/

set_option autoImplicit false

/-- At level `0` the `ℋ⁰`-integrand is the square of the `σ^{1/2}`-weighted profile. -/
theorem hkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num

/-- `L2Mem` of the `σ^{1/2}`-weighted profile is `HkMem α 0`. -/
theorem l2mem_iff_hkMem {α : ℝ} {f : ℝ → ℝ → ℝ} :
    Work.Spaces.L2Mem (fun z θ => f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ↔ Work.Spaces.HkMem α 0 f := by
  constructor
  · intro h
    exact ⟨fun z hz => by simpa only [hkIntegrand_zero_eq] using h.1 z hz,
      by simpa only [hkIntegrand_zero_eq] using h.2⟩
  · intro h
    exact ⟨fun z hz => by simpa only [hkIntegrand_zero_eq] using h.1 z hz,
      by simpa only [hkIntegrand_zero_eq] using h.2⟩

theorem sigFirstOrderD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) ∧
      Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
  obtain ⟨Cz, hCzpos, hz⟩ := zSlotBound
  obtain ⟨Cc, hCcpos, hc⟩ := cSlotBound
  refine ⟨max Cz Cc, lt_of_lt_of_le hCzpos (le_max_left _ _), ?_⟩
  intro α u G hAe
  have hsum0 : 0 ≤ Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u :=
    add_nonneg (Work.Spaces.HkSq_nonneg α 0 G) (Work.Spaces.HkSq_nonneg α 0 u)
  have hgrad : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hAe
  refine ⟨?_, ?_, ?_⟩
  · exact (l2mem_iff_hkMem (α := α) (f := Work.FTS.EllipticEst.H2W.Ae.grad u)).mpr hgrad
  · calc α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ Cz * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := hz α u G hAe
      _ ≤ max Cz Cc * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0
  · calc Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
        ≤ Cc * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := hc α u G hAe
      _ ≤ max Cz Cc * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hsum0

end Work.FTS.EllipticEst.AeS1
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueRate.sliceGradSq_rate_of_trace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueRate

set_option autoImplicit false

/-- **Squaring a square-root rate.**  From `|f| ≤ 2 √B · c^{(1+η)/2}` with `c > 0` and `B ≥ 0`
deduce `f² ≤ 4 c^{1+η} B` (the two constants `2` and `√B` are squared with
`(√B)² = B`, and `(c^{(1+η)/2})² = c^{1+η}` by `rpow_add`). -/
private theorem sq_le_of_abs_le_sqrt {f B c : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (h : |f| ≤ 2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2)) :
    f ^ 2 ≤ 4 * c ^ (1 + Work.Spaces.eta) * B := by
  have hc0 : 0 ≤ c := hc.le
  have hRnn : 0 ≤ 2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg B)) (Real.rpow_nonneg hc0 _)
  have hsq : |f| ^ 2 ≤ (2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg f) h 2
  have hc2 : (c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2 = c ^ (1 + Work.Spaces.eta) := by
    rw [sq, ← Real.rpow_add hc]
    congr 1
    ring
  have hR2 : (2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2
      = 4 * B * c ^ (1 + Work.Spaces.eta) := by
    calc (2 * Real.sqrt B * c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2
        = 4 * (Real.sqrt B) ^ 2 * (c ^ ((1 + Work.Spaces.eta) / 2)) ^ 2 := by ring
      _ = 4 * B * c ^ (1 + Work.Spaces.eta) := by rw [Real.sq_sqrt hB, hc2]
  rw [sq_abs, hR2] at hsq
  calc f ^ 2 ≤ 4 * B * c ^ (1 + Work.Spaces.eta) := hsq
    _ = 4 * c ^ (1 + Work.Spaces.eta) * B := by ring

theorem sliceGradSq_rate_of_trace {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)))
    (htrL : Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htrR : Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2
        ≤ 4 * θ ^ (1 + Work.Spaces.eta)
          * ∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
    ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (z * Work.Spaces.pz u z θ) ^ 2
        ≤ 4 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          * ∫ t in Set.Ioo θ (Real.pi / 2), (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) := by
  -- The slice `θ ↦ U u z θ` is `C¹` on the open interval.
  have hf : ContDiffOn ℝ 1 (fun θ : ℝ => Work.FTS.EllipticEst.AeI1Fts.U u z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.AeI1Fts.contDiffOn_slice_U_one hS hz
  -- Transport the integrability of the weighted derivative square along Clairaut.
  have hintD : MeasureTheory.IntegrableOn
      (fun θ : ℝ =>
        (deriv (fun θ' : ℝ => Work.FTS.EllipticEst.AeI1Fts.U u z θ') θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine hint.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hz hθ]
    rfl
  -- the two square-root rates
  have hL := Work.FTS.EllipticEst.remov.AeNj.sliceRateTwoLeft hf hintD htrL
  have hR := Work.FTS.EllipticEst.remov.AeNj.sliceRateTwoRight hf hintD htrR
  -- the two truncated energies, rewritten with the mixed slot
  have hintEqL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo 0 θ,
          (deriv (fun θ' : ℝ => Work.FTS.EllipticEst.AeI1Fts.U u z θ') t) ^ 2
            * Work.FTS.EllipticEst.thEta t)
        = ∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
            * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hz ⟨ht.1, lt_trans ht.2 hθ.2⟩]
    rfl
  have hintEqR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ' : ℝ => Work.FTS.EllipticEst.AeI1Fts.U u z θ') t) ^ 2
            * Work.FTS.EllipticEst.thEta t)
        = ∫ t in Set.Ioo θ (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hz
      ⟨lt_trans hθ.1 ht.1, ht.2⟩]
    rfl
  constructor
  · -- the `0⁺` half
    intro θ hθ
    have h := hL θ hθ
    rw [hintEqL θ hθ] at h
    have hE : 0 ≤ ∫ t in Set.Ioo 0 θ,
        (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [ht.1]) (by linarith [ht.2, hθ.2, Real.pi_pos])) _)
    exact sq_le_of_abs_le_sqrt hθ.1 hE h
  · -- the `(π/2)⁻` half
    intro θ hθ
    have h := hR θ hθ
    rw [hintEqR θ hθ] at h
    have hE : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
        (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [hθ.1, ht.1]) (by linarith [ht.2, Real.pi_pos])) _)
    exact sq_le_of_abs_le_sqrt (by linarith [hθ.2]) hE h

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueRate
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.gradTraceAeUnw =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-trace of `z ∂_z u` vanishes at both endpoints, a.e. in `z` — *unweighted* version

`Work.FTS.EllipticEst.H2W.AeProof.gradTraceAeUnw` is the statement
`Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe` with the *unweighted* third hypothesis: the radial
weight `w(z)² = ((1+z)/z)⁴` is dropped, so the hypothesis asks only that
`z ↦ ∫_θ (z ∂_θ∂_z u(z,θ))² σ(θ)` be integrable on `Iz = [0,∞)` (and it is written with the
mixed derivative in the order `∂_z∂_θ` rather than `∂_θ∂_z`).

The two halves of the proof are the two halves of that module (`aeGradTraceLeft`,
`aeGradTraceRightMine`), replayed with the unweighted hypothesis.  The weighted case used the
weight only to obtain the *local* integrability in `z` of the dominating function
`boundU u K = |∂_z u(·,1)| + M √(sliceE u ·)/·` of its dominated-convergence step; here that
local integrability is obtained directly from the unweighted hypothesis, because on `Iz` that
hypothesis *is* the defining integral of the slice energy `sliceE u` (Clairaut's theorem,
`sliceE_eq`), while `√(sliceE u) ≤ 1 + sliceE u` upgrades local `L¹` to local `L¹` of the root.

The only other difference is notational: the hypotheses of the target carry the mixed derivative
as `∂_z∂_θ u = pz (pth u)`, whereas the machinery of `AngAWeak` is phrased with `∂_θ∂_z u =
pth (pz u)`; the two agree on the open quadrant by Clairaut's theorem and both integrands vanish
at the two endpoints because `σ` does (`mixed_order_eq`, `mixed_order_integral_eq`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AngAWeak

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## 1. The two orders of the mixed derivative give the same weighted square -/



/-! ## 2. The local integrability inputs, from the *unweighted* hypothesis

In the weighted case (`GradTraceAux`) the hypothesis `hint` was used only through
`integrableOn_sliceE_of_hint` / `integrableOn_sqrtSliceE_of_hint` / `integrableOn_boundU`, whose
sole purpose is the local integrability in `z` of the slice energy and of its square root.  Here
the unweighted hypothesis *is* the local integrability of the slice energy, and the AM–GM bound
`√x ≤ 1 + x` transfers it to the square root. -/











end Work.FTS.EllipticEst.H2W.AeProof
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.RIFPsi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

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

/-! ## The vanishing of the angular cut-off derivative term -/












end Work.FTS.EllipticEst.I1Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.Rtilde.BSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Prop.Rtilde.BSlot`: the top angular slot of `∂_θθΨ`

This is `TT.ESW.Assembly.B_slot_bound` with the two unproved inputs (`TT.ESW.source_le` and
`remov.slice_ang_gen`) replaced by explicit hypotheses:
`hSrc` (the source slot, proved in parallel as `Prop.Rtilde.SourceLe`) and `hOneD` (the
one-dimensional angular estimate, produced by `Prop.Rtilde.oneD_of_far` from the far-window
bound).  Assembling the pieces — the sharp angular chain, the lower angular slots, the
one-dimensional far-region estimate applied slicewise, the source domination, the high angular
slots of `Ψ` and the low-order terms — gives `√(Tk α k (∂_θθΨ)) ≤ C(D,k) |F|_k`: the `B`-half of
the induction step of `prop:Hk`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000






/-- The source slot. -/
abbrev Gsum (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Gsl α F Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)


end Work.FTS.EllipticEst.TT.ESW
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.i1_bare_hh =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "IP" => Work.FTS.EllipticEst.AngSecond.IP

/-!
# `Prop/i1_bare_hh` — the `I₁` lower bound of Step 2, with the second-order mixed honesty

Target: `∃ C > 0, ∀ α u G, AeData α u G → HkMem α 0 (z ∂_z u) → HkMem α 0 (z ∂_z∂_θθ u) →
  -C α² (⟨U,U⟩ + √⟨U,U⟩√⟨B,B⟩) ≤ α² ⟨Q,B⟩` with `U = z ∂_z u`,
`B = ∂_θθ u`, `Q = z² ∂_zz u` and `⟨g,h⟩ = AngSecond.IP g h = ∫_z∫_θ g h w²σ`.

The three inputs are all *proved* in the workspace:

* `H2W.WeakAux.I1ZibpOpenAbs` — the radial integration by parts, whose hypothesis list is
  exactly `AeData` plus the two honesties `HkMem α 0 (z ∂_z u)`,
  `HkMem α 0 (z ∂_z∂_θθ u)`;
* `TT.aeHtermOpen` — the angular `θ`-integration by parts of the slices of `U`, with the
  *same* mixed honesty as hypothesis, giving
  `⟨U, z∂_z∂_θθu⟩ ≤ C₁⟨U,U⟩`;
* `remov.AeI1CSPiece` — the Cauchy–Schwarz bound for the drift term.

The only content of this file is the assembly, namely the arithmetic
`⟨Q,B⟩ ≥ -C₁⟨U,U⟩ - 2√⟨U,U⟩√⟨B,B⟩ ≥ -(C₁+2)(⟨U,U⟩ + √⟨U,U⟩√⟨B,B⟩)`.
-/

/-- The final arithmetic step: from `P ≥ -C·A - 2√A√B`, `A ≥ 0` and `0 < C` one has
`-(C+2)·α²·(A + √A√B) ≤ α²·P`, because `2A + C√A√B ≥ 0`. -/
private theorem arith_ibh (C α A B P : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hP : - C * A - 2 * (Real.sqrt A * Real.sqrt B) ≤ P) :
    - (C + 2) * α ^ 2 * (A + Real.sqrt A * Real.sqrt B) ≤ α ^ 2 * P := by
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hmul : 0 ≤ Real.sqrt A * Real.sqrt B := mul_nonneg hsA hsB
  have hkey : - (C + 2) * (A + Real.sqrt A * Real.sqrt B) ≤ P := by
    nlinarith [hC, hA, hmul, hP]
  calc - (C + 2) * α ^ 2 * (A + Real.sqrt A * Real.sqrt B)
      = α ^ 2 * (- (C + 2) * (A + Real.sqrt A * Real.sqrt B)) := by ring
    _ ≤ α ^ 2 * P := mul_le_mul_of_nonneg_left hkey (sq_nonneg α)

theorem i1_bare_hh : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) →
      - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz u z θ)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
                (fun z θ => z * Work.Spaces.pz u z θ))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u)))
        ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.EllipticEst.TT.aeHtermOpen
  refine ⟨C₁ + 2, by linarith, ?_⟩
  intro α u G hA hU hH
  -- ## (Z) the radial integration by parts
  have hZ₀ := Work.FTS.EllipticEst.H2W.WeakAux.I1ZibpOpenAbs α u
    (Work.FTS.EllipticEst.H2W.Ae.AeData.hα hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.hα4 hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.dirPi hA)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 hA) hU
    (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hH
  have hZ : IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        (Work.Spaces.pthIter 2 u)
      = - IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
        - IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ) := by
    have h1 : IP (Work.Spaces.Dz u)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
        = IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) := rfl
    have h2 : IP (Work.Spaces.Dz u)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.Spaces.pthIter 2 u z θ)
        = IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ) :=
      Work.FTS.EllipticEst.AngSecond.IP_congr (fun _ _ => rfl) (fun z θ => by
        simp only [Work.FTS.EllipticEst.AngSecond.cw])
    rw [hZ₀, h1, h2]
  -- ## (M) the angular pairing bound `⟨U, z∂_z∂_θθu⟩ ≤ C₁⟨U,U⟩`
  have hHr := hC₁ α u G hA hU hH
  have hHr' : IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      ≤ - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
            Work.Spaces.HkSq α 0 (Work.Spaces.pth (fun z θ => z * Work.Spaces.pz u z θ))
        + C₁ * IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz u z θ) := hHr
  have hUH : IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      ≤ C₁ * IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => z * Work.Spaces.pz u z θ) := by
    have hnn : (0 : ℝ) ≤ ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
        Work.Spaces.HkSq α 0
          (Work.Spaces.pth (fun z θ => z * Work.Spaces.pz u z θ)) :=
      mul_nonneg (div_nonneg (by linarith [Work.Spaces.eta_lt_one])
        (by linarith [Work.Spaces.eta_pos])) (Work.Spaces.HkSq_nonneg α 0 _)
    linarith [hHr', hnn]
  -- ## (CS) the Cauchy–Schwarz bound for the drift term
  --
  -- `AngAWeak.aeI1CwBound` is the `H2W.Ae.AeData`-class Cauchy–Schwarz of the drift term in the
  -- order `IP (cw·U) B`; here we need it in the order `IP U (cw·B)` produced by the radial
  -- integration by parts, so we swap the two slots of the pairing.
  have hcs₀ := Work.FTS.EllipticEst.AngAWeak.aeI1CwBound hA hU
  have hcs₁ : IP (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * (z * Work.Spaces.pz u z θ)) (Work.Spaces.pthIter 2 u)
      ≤ 2 * Real.sqrt (IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ))
          * Real.sqrt (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)) := hcs₀
  have hswap : IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ)
      = IP (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * (z * Work.Spaces.pz u z θ)) (Work.Spaces.pthIter 2 u) := by
    rw [Work.FTS.EllipticEst.AngSecond.IP, Work.FTS.EllipticEst.AngSecond.IP]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp only [Work.FTS.EllipticEst.AngSecond.cw]
    ring
  have hcs' : - IP (fun z θ => z * Work.Spaces.pz u z θ)
        (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ)
      ≥ - 2 * (Real.sqrt (IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ))
          * Real.sqrt (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u))) := by
    rw [hswap]
    linarith [hcs₁]
  -- ## the assembly
  have hP : - C₁ * IP (fun z θ => z * Work.Spaces.pz u z θ)
          (fun z θ => z * Work.Spaces.pz u z θ)
        - 2 * (Real.sqrt (IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ))
            * Real.sqrt (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
      ≤ IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          (Work.Spaces.pthIter 2 u) := by
    rw [hZ]
    linarith [hUH, hcs']
  exact arith_ibh C₁ α
    (IP (fun z θ => z * Work.Spaces.pz u z θ) (fun z θ => z * Work.Spaces.pz u z θ))
    (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u))
    (IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u))
    hC₁pos
    (Work.FTS.EllipticEst.AngSecond.IP_self_nonneg (fun z θ => z * Work.Spaces.pz u z θ))
    hP

end

end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.EllUnifBslot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EllUnifBslot`: the `B`-slot of the induction step, on the live `ESW` route

`remov/EllEstUnif_step.lean` (the frozen target of this workspace area) needs, as the last
missing input, the top angular slot estimate

  `√(Tk α k (∂_θθΨ)) ≤ C(D,k) |F|_k`

(`Tk α k f = ∫∫(D_θ^k f · Wt α)²`), under `TT.EllWeakPos α k F Ψ` and the two level-`(k-1)`
bounds with constant `D`, for `k ≥ 3`.

Two routes to it existed in the workspace:

* `remov/B_top_slot_bound` — via `remov.Rtilde_Tk_bound` (`R̃ = ∂_θθΨ + α²z²∂_zzΨ`).  The lead's
  design note `Submission/Work/FTS/ELL_H2_LEAD.md` (§0, item 1) has since declared the `Rtilde`
  route **off-route** ("the top angular slot needs *no* coercive sign, no flux, no
  anti-degeneracy and no `Rtilde`"), so that route is dead;
* `TT/ESW/Assembly.lean`, `ESW.B_slot_bound`, proving the same thing from the one-dimensional
  estimate `remov.slice_ang_gen` + the source slot `TT/ESW.source_le`.  This is the live route.

This module reproduces the live route **independently of `remov/slice_ang_gen.lean`**, whose
source does not currently compile (a one-token type ascription in the `hV` it builds — see
`remov/NOTE_slice_ang_gen_broken.md`; without its `.olean` the whole `TT/ESW/Assembly.lean` is
unimportable).  Concretely:

* `slice_ang_gen_live` is the same 30-line assembly, with the ascription written correctly, so
  that it produces `OneD k` (the type `TT/ESW/U_le_of_1d` consumes);
* `BSlotBound` is the `B`-slot, assembled exactly as `TT/ESW/Assembly.lean` does but from
  `slice_ang_gen_live`.

Nothing here is new mathematics: the two lemmas are transcriptions of
`remov/slice_ang_gen.lean` and `TT/ESW/Assembly.lean` with the (unbuildable) file
`remov/slice_ang_gen.lean` replaced by the local copy.  The remaining inputs
(`remov.slice_ang_v_far`, `remov.slice_ang_gen_final`, `TT/ESW.source_le`, and the pieces they
rest on) are unchanged.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.EllUnifBslot

set_option autoImplicit false
set_option maxHeartbeats 1600000


/-! ## The slot sums of the `B`-assembly (transcribed from `TT/ESW/Assembly.lean`) -/






/-- The source slot. -/
abbrev Gsum (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)


end Work.FTS.EllipticEst.remov.EllUnifBslot

end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.stripLo_stripHi_eq_of_logrel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

theorem stripLo_stripHi_eq_of_logrel {g : Work.FTS.Galerkin.Fn} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {ε : ℝ} (hε : 0 < ε)
    {z' θ' p₂ : ℝ} (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2)) (hp₂ : |p₂| ≤ ε)
    (hrel : p₂ = Real.log (Real.tan θ) - Real.log (Real.tan θ')) :
    Work.FTS.EpsEngine.ThetaFromEps.stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g z' θ' = g z' θ' ∧
    Work.FTS.EpsEngine.ThetaFromEps.stripHi (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g z' θ'
      = g z' θ' := by
  -- `tan θ' = tan θ · e^{-p₂}`, so `tan θ'` lies between `tan θ · e^{-ε}` and `tan θ · e^{ε}`;
  -- applying the increasing `arctan` and using `arctan (tan θ') = θ'` gives the two strip
  -- conditions `θ' ≤ thShift θ (-ε)` and `thShift θ ε ≤ θ'`.
  have hT : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  have hT' : 0 < Real.tan θ' := Real.tan_pos_of_pos_of_lt_pi_div_two hθ'.1 hθ'.2
  have hlog : Real.log (Real.tan θ') = Real.log (Real.tan θ) - p₂ := by linarith
  have htan : Real.tan θ' = Real.tan θ * Real.exp (-p₂) := by
    have h := congrArg Real.exp hlog
    rwa [Real.exp_log hT', Real.exp_sub, Real.exp_log hT, div_eq_mul_inv, ← Real.exp_neg] at h
  have hle : -p₂ ≤ ε := by have h := (abs_le.mp hp₂).1; linarith
  have hge : -ε ≤ -p₂ := by have h := (abs_le.mp hp₂).2; linarith
  have harctan : Real.arctan (Real.tan θ') = θ' :=
    Real.arctan_tan (by linarith [hθ'.1, Real.pi_pos]) hθ'.2
  have hA : Real.tan θ' ≤ Real.tan θ * Real.exp ε := by
    rw [htan]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hT.le
  have hB : Real.tan θ * Real.exp (-ε) ≤ Real.tan θ' := by
    rw [htan]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hge) hT.le
  have h1 : θ' ≤ Work.FTS.StrongEps.thShift θ (-ε) := by
    rw [Work.FTS.StrongEps.thShift, neg_neg]
    calc θ' = Real.arctan (Real.tan θ') := harctan.symm
      _ ≤ Real.arctan (Real.tan θ * Real.exp ε) := Real.arctan_mono hA
  have h2 : Work.FTS.StrongEps.thShift θ ε ≤ θ' := by
    rw [Work.FTS.StrongEps.thShift]
    calc Real.arctan (Real.tan θ * Real.exp (-ε)) ≤ Real.arctan (Real.tan θ') := Real.arctan_mono hB
      _ = θ' := harctan
  constructor
  · simp only [Work.FTS.EpsEngine.ThetaFromEps.stripLo]
    rw [if_pos h1]
  · simp only [Work.FTS.EpsEngine.ThetaFromEps.stripHi]
    rw [if_pos (by linarith)]

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
end
-- ===== merged: Submission.Work.FTS.IPGen.IP4Smul =====
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
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false

/-- **One step of the recursion is homogeneous**: if `IP (c·f) g = c·IP f g`, then the same
holds for `HkIPStep c₁ c₂ IP`. -/
theorem HkIPStep_homog (c₁ c₂ c : ℝ) (IP : Fn → Fn → ℝ)
    (hIP : ∀ f g : Fn, IP (fun z θ => c * f z θ) g = c * IP f g) (f g : Fn) :
    Work.Coercivity.HkIPStep c₁ c₂ IP (fun z θ => c * f z θ) g
      = c * Work.Coercivity.HkIPStep c₁ c₂ IP f g := by
  have hdth : Work.Spaces.Dth (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.Dth f z θ := Work.Coercivity.Dth_smul c f
  have hdz : Work.Spaces.Dz (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.Dz f z θ := Work.Coercivity.Dz_smul c f
  simp only [Work.Coercivity.HkIPStep, hdth, hdz, hIP]
  ring

/-- Homogeneity of the iterated recursion `IPnG c₁ c₂ α n`. -/
theorem IPnG_homog (c₁ c₂ c α : ℝ) :
    ∀ (n : ℕ) (f g : Fn),
      IPnG c₁ c₂ α n (fun z θ => c * f z θ) g = c * IPnG c₁ c₂ α n f g := by
  intro n
  induction n with
  | zero => intro f g; exact Work.Coercivity.H1IP_homog α c f g
  | succ n ih =>
      intro f g
      exact HkIPStep_homog c₁ c₂ c (IPnG c₁ c₂ α n) ih f g



/-- **Homogeneity of the coercive `IP4` in its first argument**, with no regularity
hypothesis. -/
theorem IP4_homog (c₁ c₂ c₁' c₂' c₁'' c₂'' c α : ℝ) (f g : Fn) :
    Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => c * f z θ) g
      = c * Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g :=
  HkIPStep_homog c₁'' c₂'' c (Work.Coercivity.HkIPStep c₁' c₂' (IPnG c₁ c₂ α 1))
    (HkIPStep_homog c₁' c₂' c (IPnG c₁ c₂ α 1) (IPnG_homog c₁ c₂ c α 1)) f g

/-- The `smul` clause of `N4ExtraQ` for `Assembly.IP4`, in its strongest form (no `HQo`
hypothesis, no restriction on `α`). -/
theorem ip4_smul (c₁ c₂ c₁' c₂' c₁'' c₂'' c α : ℝ) (f g : Fn) :
    Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => c * f z θ) g
      = c * Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g :=
  IP4_homog c₁ c₂ c₁' c₂' c₁'' c₂'' c α f g

/-- The `neg` clause of `N4ExtraQ` for `Assembly.IP4` (the `c = -1` instance of `ip4_smul`). -/
theorem ip4_neg (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (f g : Fn) :
    Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => -f z θ) g
      = -Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g := by
  have h := IP4_homog c₁ c₂ c₁' c₂' c₁'' c₂'' (-1) α f g
  simpa using h

end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzIter_mixed_mul_rad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24

/-! ## The iterated Leibniz rule for the radial factor `R z`

`D_z = z ∂_z` and `D_θ = sin 2θ ∂_θ` are derivations; a factor `R z` depending only on `z`
is invisible to `D_θ`, and for `D_z` the binomial rule

  `D_z^i (R · h) = Σ_{b ≤ i} C(i,b) · (D_z^b R) · (D_z^{i-b} h)`

holds pointwise wherever the two factors are differentiable often enough.  Since here `R` is
only `C⁴` (not `C^∞`), the abstract `DerivLike` machinery of `Work.Spaces` (which is stated
for the analytic class `⊤`) does not apply; instead we use the one-variable Leibniz rule
`dzdIter_mul_leibniz` of `Pieces/rowsN0Q`, which only asks for the differentiability of the
iterates and is therefore available. -/






end Work.FTS.Nonlinear.Pieces.RNP.RNP24
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Uop_PhiTs_slice_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-! ## 0. Elementary facts on the angular interval -/

/-- `cos θ ≠ 0` for `θ ∈ (0,π/2)`. -/
theorem cos_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)


/-! ## 1. The profile identity with the normalisation `c/c` kept -/






/-! ## 2. The calculus of the angular slice -/

/-- The product rule for `tan θ · u` at an interior angle. -/
theorem deriv_tan_mul {u : ℝ → ℝ} {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hu : DifferentiableAt ℝ u θ) :
    deriv (fun t : ℝ => Real.tan t * u t) θ
      = 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ :=
  (((Real.hasDerivAt_tan hcos).mul hu.hasDerivAt).deriv)

/-- The unfolding of `L₀` on a function of `θ` alone. -/
theorem Lzero_theta_unfold (u : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => u θ') z θ
      = -(deriv (deriv u) θ) + deriv (fun t : ℝ => Real.tan t * u t) θ - 6 * u θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]




/-- Congruence of `L₀` on a `θ`-only function under eventual equality. -/
theorem Lzero_congr_of_eventuallyEq {f g : ℝ → ℝ} {z θ : ℝ} (h : f =ᶠ[𝓝 θ] g) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = Work.Elliptic.Lzero (fun _ θ' => g θ') z θ := by
  have h3 : (fun t : ℝ => Real.tan t * f t) =ᶠ[𝓝 θ] (fun t : ℝ => Real.tan t * g t) := by
    filter_upwards [h] with t ht
    rw [ht]
  have h1 : deriv f =ᶠ[𝓝 θ] deriv g := h.deriv
  have h2 : deriv (deriv f) =ᶠ[𝓝 θ] deriv (deriv g) := h1.deriv
  rw [Lzero_theta_unfold, Lzero_theta_unfold, h2.eq_of_nhds, h3.deriv_eq, h.eq_of_nhds]


/-! ## 3. The two limits at `z = 0⁺` -/




/-! ## 4. The `θ`-slice at `z = 0` of `Φ̃_*` is identically zero -/



/-! ## 5. The lemma -/


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.HkNorm_le_of_tendstoLocUnif_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Work.FTS.Apriori.Limit

/-! ## The bridge from the closed strip to the open quadrant -/


/-! ## The slot functions in the open-quadrant class -/



/-! ## Integration by parts in the open-quadrant class -/

/-- The adjointness of `mixed j i = D_z^j D_θ^i` for a profile smooth on the open quadrant. -/
theorem integral_mixed_mul_adjMixed_of_contDiffOn {g ψ : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) (hψ : TestQ ψ)
    (j i : ℕ) :
    (∫ p, Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2 ∂Qμ)
      = ∫ p, g p.1 p.2 * adjMixed (j, i) ψ p.1 p.2 ∂Qμ := by
  have h1 := integral_DzIter_mul_adjDzIter
    (u := Work.Spaces.DthIter i g) (v := ψ)
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_Qd hg i) hψ j
  have h2 := integral_DthIter_mul_adjDthIter (u := g) (v := adjDzIter j ψ) hg
    (TestQ_adjDzIter j hψ) i
  exact h1.trans h2

/-! ## Passing a locally uniform limit through the pairing -/


/-! ## Continuity of the `ℋ⁴`-integrand in the open-quadrant class -/


/-! ## `ofReal` of `HkSq` against the `lintegral` of the integrand -/


/-! ## Fatou for an exhausting family of cut-offs -/


/-! ## The target -/


end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.Jeps_sub_eq_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

theorem Jeps_sub_eq_integral (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.StrongEps.Jeps ρ ε g z θ - g z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - g z θ) := by
  -- the shifted point stays in the open quadrant, whatever the shift `p`
  have hmem : ∀ p : ℝ × ℝ, (zShift z p.1, thShift θ p.2) ∈ Quad :=
    fun _ => ⟨zShift_pos hz, thShift_mem hθ⟩
  -- hence the `p ↦ g (zShift z p.1) (thShift θ p.2)` is continuous on all of `ℝ²`
  have hcont_g : Continuous fun p : ℝ × ℝ => g (zShift z p.1) (thShift θ p.2) := by
    simpa only [Function.comp_def, Function.uncurry] using
      hg.comp_continuous (continuous_shift_pair z θ) hmem
  -- the product is continuous with compact support (the kernel is supported in the ball
  -- of radius `ε`), so it is integrable
  have hInt : Integrable fun p : ℝ × ℝ => Jker ρ ε p * g (zShift z p.1) (thShift θ p.2) :=
    ((Jker_continuous hρ ε).mul hcont_g).integrable_of_hasCompactSupport
      (Jker_hasCompactSupport hρ hε).mul_right
  have hInt2 : Integrable fun p : ℝ × ℝ => Jker ρ ε p * g z θ :=
    (Jker_integrable hρ hε).mul_const _
  -- the kernel has mass one
  have hc : ∫ p : ℝ × ℝ, Jker ρ ε p * g z θ = g z θ := by
    rw [integral_mul_const, Jker_integral_eq_one ρ hρ hε, one_mul]
  -- `J_ε g` is the convolution `∫ p, Jker ρ ε p * g (shift p)`
  rw [Jeps_eq_integral ρ ε g hz hθ]
  refine Eq.symm ?_
  conv_rhs => rw [← hc]
  rw [← integral_sub hInt hInt2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JepsNegComp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

set_option autoImplicit false

/-!
# `JepsNegComp` — the negation symmetry of the log-coordinate mollifier

The log-coordinate mollifier `Jeps ρ ε` is the convolution with the rescaled kernel
`Jker ρ ε p = ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)` (`Basic.lean`, `Kernel.lean`), and neither the kernel nor the
shift depends on the *orientation* of the mollifier coordinates.  This module records the two
consequences of that fact:

* if `ρ` is an admissible smooth kernel (`IsSmoothKernel ρ`), so is the reflected kernel
  `p ↦ ρ (-p)` — smoothness is preserved by the linear isometry `p ↦ -p`, and the mass is
  preserved because `volume` on `ℝ × ℝ` is invariant under negation
  (`MeasureTheory.integral_neg_eq_self`);
* for *negative* `ε` the reflected kernel at scale `-ε` reproduces `Jeps ρ ε` exactly:
  `(-ε)⁻¹ = -(ε⁻¹)`, so `-((-ε)⁻¹ • p) = ε⁻¹ • p` and `((-ε)⁻¹) ^ 2 = (ε⁻¹) ^ 2`, i.e. the two
  integrands agree **pointwise** and the integrals are literally equal.

The statement is the `ε < 0` half of the "reflection bookkeeping" of the `Apriori4` transfer: the
`ε`-scheme itself is only run for `ε > 0`, and reflection lets a *negative* scale be re-read as a
positive one applied to the reflected kernel.
-/

/-- **Reflection of an admissible smooth kernel.**  If `ρ` is a smooth admissible mollifier
kernel, so is `p ↦ ρ (-p)`: the linear isometry `p ↦ -p` preserves `C^∞`, continuity, the support
condition and nonnegativity, while the total mass is preserved by the negation invariance of
Lebesgue measure on `ℝ × ℝ`. -/
theorem isSmoothKernel_neg_comp {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    Work.FTS.StrongEps.IsSmoothKernel (fun p : ℝ × ℝ => ρ (-p)) := by
  refine ⟨?_, ?_⟩
  · intro n
    exact (hρ.smooth n).comp (contDiff_neg (𝕜 := ℝ) (F := ℝ × ℝ))
  · refine ⟨hρ.moll.cont.comp continuous_neg, ?_, ?_, ?_⟩
    · intro p hp
      have h := hρ.moll.support (-p) hp
      simpa using h
    · intro p
      exact hρ.moll.nonneg (-p)
    · simpa using (MeasureTheory.integral_neg_eq_self ρ volume).trans hρ.moll.mass

/-- **The reflected kernel at the negated scale is the original mollifier.**  For every `ε` and
every profile `f`, `Jeps ρ ε f = Jeps (p ↦ ρ (-p)) (-ε) f`: the two `p`-integrands agree
pointwise, since `(-ε)⁻¹ = -(ε⁻¹)` entails `-((-ε)⁻¹ • p) = ε⁻¹ • p` and
`((-ε)⁻¹) ^ 2 = (ε⁻¹) ^ 2`. -/
theorem Jeps_neg_comp {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (f : Work.FTS.Galerkin.Fn) :
    Work.FTS.StrongEps.Jeps ρ ε f
      = Work.FTS.StrongEps.Jeps (fun p : ℝ × ℝ => ρ (-p)) (-ε) f := by
  funext z θ
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε f hc.1 hc.2,
      Work.FTS.StrongEps.Jeps_eq_integral (fun p : ℝ × ℝ => ρ (-p)) (-ε) f hc.1 hc.2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.FTS.StrongEps.Jker]
    have h1 : (-ε)⁻¹ • p = -(ε⁻¹ • p) := by rw [inv_neg, neg_smul]
    rw [h1, neg_neg, inv_neg, neg_sq]
  · rw [Work.FTS.StrongEps.Jeps_eq_zero ρ ε f hc,
      Work.FTS.StrongEps.Jeps_eq_zero (fun p : ℝ × ℝ => ρ (-p)) (-ε) f hc]

theorem JepsNegComp {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : ε < 0) :
    Work.FTS.StrongEps.IsSmoothKernel (fun p : ℝ × ℝ => ρ (-p)) ∧
      ∀ f : Work.FTS.Galerkin.Fn,
        Work.FTS.StrongEps.Jeps ρ ε f
          = Work.FTS.StrongEps.Jeps (fun p : ℝ × ℝ => ρ (-p)) (-ε) f :=
  ⟨isSmoothKernel_neg_comp hρ, fun f => Jeps_neg_comp f⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JepsZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-! ## The degenerate values of the `ε`-scheme

These are the boundary cases in which a quantity of the transfer estimate is *identically* zero:
the mollifier at scale `ε = 0` (where the rescaled kernel `Jker` collapses, since `(0:ℝ)⁻¹ = 0`),
the projected zero profile, and the `ℋ⁴`/`ℋ⁶`-sizes of the zero profile.  They are used to
discharge the degenerate branches of the transfer/defect estimates (the `ε → 0` and `g ≡ 0`
cases). -/

/-- The `L₁₂`-operator of the fundamental model vanishes on the zero profile.  (This is the
`L₁₂(0)(0) = 0` instance; it is proved here by unfolding, so that this module needs no import of
the Galerkin vocabulary.) -/
theorem l12_zero : Work.Construction.L12 (0 : Work.FTS.Galerkin.Fn) 0 = 0 := by
  simp [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]


theorem JepsZero (ρ : ℝ × ℝ → ℝ) (f : Work.FTS.Galerkin.Fn) :
    Work.FTS.StrongEps.Jeps ρ 0 f = 0 ∧ Work.FTS.StrongEps.Pz (0 : Work.FTS.Galerkin.Fn) = 0 ∧
      (∀ α : ℝ, Work.Spaces.HkNorm α 4 (0 : Work.FTS.Galerkin.Fn) = 0) ∧
      (∀ α : ℝ, Work.FTS.StrongGlobal.Xn6 α (0 : Work.FTS.Galerkin.Fn) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `ε = 0`: the integrand of `Jeps` is `0 · ρ (0 • p) · ·  = 0`.
    funext z θ
    simp only [Work.FTS.StrongEps.Jeps]
    split <;> simp
  · -- `Pz` subtracts a multiple of `bump`; on the zero profile the multiple is `0`.
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    simp only [Pi.zero_apply, l12_zero, zero_div, zero_mul, sub_zero]
  · intro α
    exact Work.FTS.EllipticEst.HkNorm_zero α 4
  · intro α
    exact Work.FTS.EllipticEst.HkNorm_zero α 6

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.dthU_iter_Gfun_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary

/-!
# The `D_θ`-iterates of `sin²·Γ` are dominated by `Γ·(α + B_i·sin²2θ)`

The operator is `D_θ φ = sin(2θ)·φ'` (`Work.Spaces.dthU`), and
`Γ(θ) = (sin θ cos²θ)^{α/3}` (`Work.Spaces.Gam`).  Given the Leibniz expansion of
`D_θ^i (sin²·Γ)` (`hlei`), the goal is the pointwise bound

`|D_θ^i (sin²·Γ) θ| ≤ Γ θ · (α·10⁵ + B_i·sin²(2θ))`,  `1 ≤ i ≤ 6`, `α ∈ (0,1]`, `θ ∈ Iθ`,

with constants `B_i` depending on `i` only.  This is the *α-weighted* form in which the
`i`-fold `D_θ`-derivative of `sin²·Γ` is controlled by `Γ` times a coefficient: the term of
the Leibniz sum on which all `i` derivatives fall on `Γ` carries the factor `α` (because
`D_θ^j Γ = α·T_j·Γ`, `j ≥ 1`), while every other term carries at least one derivative of
`sin²`, hence a factor `sin²(2θ)` (`dthUiter_sin_sq_iter`: `D_θ^j (sin²) θ =
cos²θ·sin²θ·R_{j-1}(cos²θ)` for `j ≥ 1`).

Consequently the *only* place where the coefficient `sin²(2θ)` is not available is the group
of terms with `j = 0` on `sin²`, i.e. the single term `r = 0` (all `i` derivatives on `Γ`),
and there the factor `α` of `D_θ^i Γ` is used instead — this is why the statement bounds by
`Γ·(α·10⁵ + B_i·sin²2θ)` and not by `Γ·B_i·sin²2θ` alone.

The endpoint `θ ∈ {0, π/2}` is harmless: `D_θ^i φ θ = sin(2θ)·(…) = 0` for `i ≥ 1`
(`dthU_iter_eq_zero_of_sin_eq_zero'`) while `Γ` vanishes there (`Gam_zero_left`,
`Gam_zero_right`), so both sides are `0`.
-/

/-- **Endpoint vanishing of the `D_θ`-iterates of `sin²`.**  For every `j ≥ 1` and every real
`θ`, `|D_θ^j (sin²) θ| ≤ 1095801216·sin²(2θ)`.  This is
`Work.FTS.PhiStar.Psi0Aux.dthUiter_sin_sq_iter` together with the coefficient bound
`∑_k |c_k| ≤ 1095801216` of the explicit polynomial `R_{j-1}`. -/
lemma abs_dthU_iter_sin_sq_le (j : ℕ) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) (θ : ℝ) :
    |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
      ≤ 1095801216 * Real.sin (2 * θ) ^ 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i ≤ 6 := by omega
  rw [Work.FTS.PhiStar.Psi0Aux.dthUiter_sin_sq_iter i hi θ]
  have hb : |Polynomial.eval (Real.cos θ ^ 2) (Work.FTS.PhiStar.Psi0Aux.dthUiterPR i)|
      ≤ 1095801216 := by
    rw [Work.FTS.PhiStar.Psi0Aux.dthUiterPR_eval]
    exact le_trans
      (Work.FTS.PhiStar.Psi0Aux.dthUiter_abs_sum_pow_le _ _ _
        (sq_nonneg (Real.cos θ)) (Real.cos_sq_le_one θ))
      (Work.FTS.PhiStar.Psi0Aux.dthUiterPRcoef_sum_le i hi)
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ)),
    abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hcs : Real.cos θ ^ 2 * Real.sin θ ^ 2 = Real.sin (2 * θ) ^ 2 / 4 := by
    rw [Real.sin_two_mul]; ring
  calc Real.cos θ ^ 2 * Real.sin θ ^ 2
        * |Polynomial.eval (Real.cos θ ^ 2) (Work.FTS.PhiStar.Psi0Aux.dthUiterPR i)|
      = Real.sin (2 * θ) ^ 2 / 4
        * |Polynomial.eval (Real.cos θ ^ 2) (Work.FTS.PhiStar.Psi0Aux.dthUiterPR i)| := by rw [hcs]
    _ ≤ Real.sin (2 * θ) ^ 2 * 1095801216 :=
        mul_le_mul (by nlinarith [sq_nonneg (Real.sin (2 * θ))]) hb (abs_nonneg _) (sq_nonneg _)
    _ = 1095801216 * Real.sin (2 * θ) ^ 2 := by ring

/-- **The `Γ`-iterates are dominated by `100000·Γ`**  (`j ≤ 6`, `θ ∈ Iθ`, `0 < α ≤ 1`). -/
lemma abs_dthU_iter_Gam_le (j : ℕ) (hj : j ≤ 6) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[j] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [Function.iterate_zero_apply,
      abs_of_nonneg (Work.Spaces.Gam_bounds α θ hα hθ).1]
    nlinarith [(Work.Spaces.Gam_bounds α θ hα hθ).1]
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (j - 1) α θ'| ≤ 100000 :=
      fun θ' _ => Work.FTS.LocData6.Tfun_abs_le5 (j - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound j h α hα 100000 hT θ hθ
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).1
    calc |Work.Spaces.dthU^[j] (fun t : ℝ => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG]

/-- **The `α`-weighted bound for the `Γ`-iterates**: for `j ≥ 1`, `D_θ^j Γ = α·T_{j-1}·Γ`
with `|T_{j-1}| ≤ 100000` on `Iθ`, hence `|D_θ^j Γ| ≤ α·100000·Γ`. -/
lemma abs_dthU_iter_Gam_le_alpha (j : ℕ) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[j] (fun t : ℝ => Work.Spaces.Gam α t) θ| ≤ α * 100000 * Work.Spaces.Gam α θ := by
  have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (j - 1) α θ'| ≤ 100000 :=
    fun θ' _ => Work.FTS.LocData6.Tfun_abs_le5 (j - 1) (by omega) α hα hα1 θ'
  exact Work.Spaces.dthU_iter_Gam_abs_bound j hj1 α hα 100000 hT θ hθ

theorem dthU_iter_Gfun_bound
    (hlei : ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ i : ℕ, i ≤ 6 →
      Set.EqOn (Work.Spaces.dthU^[i] (fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ))
        (fun θ => ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
          (Work.Spaces.dthU^[r] (fun θ => Real.sin θ ^ 2) θ *
            Work.Spaces.dthU^[i - r] (fun θ => Work.Spaces.Gam α θ) θ))
        (Set.Ioo 0 (Real.pi / 2))) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[i] (fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ) θ|
          ≤ Work.Spaces.Gam α θ * (α * 100000 + B i * (Real.sin (2 * θ)) ^ 2) := by
  refine ⟨fun i => 100000 * 1095801216 * ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ),
    fun i => ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) :=
      Finset.sum_nonneg fun r _ => Nat.cast_nonneg _
    exact mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) h1
  · intro α hα i hi1 hi6 θ hθ
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα0 hθ).1
    by_cases hθm : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · -- The open interval: expand with the Leibniz rule and bound term by term.
      have heq : Work.Spaces.dthU^[i] (fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ) θ
          = ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
              (Work.Spaces.dthU^[r] (fun θ => Real.sin θ ^ 2) θ *
                Work.Spaces.dthU^[i - r] (fun θ => Work.Spaces.Gam α θ) θ) :=
        (hlei α hα i hi6) hθm
      -- separate the `r = 0` term (all derivatives on `Γ`)
      have hswap : (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
              (Work.Spaces.dthU^[r] (fun θ => Real.sin θ ^ 2) θ *
                Work.Spaces.dthU^[i - r] (fun θ => Work.Spaces.Gam α θ) θ))
          = (∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) *
              (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
                Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ))
            + (i.choose 0 : ℝ) *
              (Work.Spaces.dthU^[0] (fun θ => Real.sin θ ^ 2) θ *
                Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ) := by
        rw [Finset.sum_range_succ', Nat.sub_zero]
      have hZ : 0 ≤ Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2 :=
        mul_nonneg hG0 (sq_nonneg _)
      have hGj : ∀ j ≤ 6, |Work.Spaces.dthU^[j] (fun t : ℝ => Work.Spaces.Gam α t) θ|
          ≤ 100000 * Work.Spaces.Gam α θ := fun j hj => abs_dthU_iter_Gam_le j hj α hα0 hα1 hθ
      have hGi : |Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ|
          ≤ α * 100000 * Work.Spaces.Gam α θ := abs_dthU_iter_Gam_le_alpha i hi1 hi6 α hα0 hα1 hθ
      have hP0 : |(i.choose 0 : ℝ) *
            (Work.Spaces.dthU^[0] (fun θ => Real.sin θ ^ 2) θ *
              Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ)|
          ≤ α * 100000 * Work.Spaces.Gam α θ := by
        rw [Nat.choose_zero_right, Nat.cast_one, one_mul, abs_mul,
          Function.iterate_zero_apply, abs_of_nonneg (sq_nonneg (Real.sin θ))]
        calc Real.sin θ ^ 2 * |Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ|
            ≤ 1 * (α * 100000 * Work.Spaces.Gam α θ) :=
              mul_le_mul (Real.sin_sq_le_one θ) hGi (abs_nonneg _) (by norm_num)
          _ = α * 100000 * Work.Spaces.Gam α θ := by ring
      have hPr : ∀ r ∈ Finset.range i,
          |(i.choose (r + 1) : ℝ) *
            (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
              Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ)|
          ≤ ((i.choose (r + 1) : ℝ) * (1095801216 * 100000))
            * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2) := by
        intro r hr
        have hrlt : r < i := Finset.mem_range.mp hr
        have h1 : 1 ≤ r + 1 := by omega
        have h6 : r + 1 ≤ 6 := by omega
        have hj6 : i - (r + 1) ≤ 6 := by omega
        have hA := abs_dthU_iter_sin_sq_le (r + 1) h1 h6 θ
        have hG := hGj (i - (r + 1)) hj6
        have hc0 : (0 : ℝ) ≤ (i.choose (r + 1) : ℝ) := Nat.cast_nonneg _
        rw [abs_mul, abs_mul, abs_of_nonneg hc0]
        calc (i.choose (r + 1) : ℝ)
              * (|Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ|
                * |Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ|)
            ≤ (i.choose (r + 1) : ℝ)
              * ((1095801216 * Real.sin (2 * θ) ^ 2) * (100000 * Work.Spaces.Gam α θ)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hA hG (abs_nonneg _) (by positivity)) hc0
          _ = ((i.choose (r + 1) : ℝ) * (1095801216 * 100000))
              * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2) := by ring
      have hle : (∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ))
          ≤ ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) := by
        have h := Finset.sum_range_succ' (fun r : ℕ => (i.choose r : ℝ)) i
        have hc : (0 : ℝ) ≤ (i.choose 0 : ℝ) := Nat.cast_nonneg _
        linarith [h]
      calc |Work.Spaces.dthU^[i] (fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ) θ|
          = |(∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) *
                (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ))
              + (i.choose 0 : ℝ) *
                (Work.Spaces.dthU^[0] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ)| := by
              rw [heq, hswap]
        _ ≤ |∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) *
                (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ)|
              + |(i.choose 0 : ℝ) *
                (Work.Spaces.dthU^[0] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ)| := abs_add_le _ _
        _ ≤ (∑ r ∈ Finset.range i, |(i.choose (r + 1) : ℝ) *
                (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ)|)
              + α * 100000 * Work.Spaces.Gam α θ :=
              add_le_add (Finset.abs_sum_le_sum_abs _ _) hP0
        _ ≤ (∑ r ∈ Finset.range i, ((i.choose (r + 1) : ℝ) * (1095801216 * 100000))
                * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2))
              + α * 100000 * Work.Spaces.Gam α θ :=
              add_le_add (Finset.sum_le_sum hPr) le_rfl
        _ = ((∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) * (1095801216 * 100000))
                * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2))
              + α * 100000 * Work.Spaces.Gam α θ := by rw [Finset.sum_mul]
        _ ≤ ((100000 * 1095801216 * ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ))
                * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2))
              + α * 100000 * Work.Spaces.Gam α θ := by
              have h1 : (∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) * (1095801216 * 100000))
                  ≤ 100000 * 1095801216 * (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) := by
                rw [← Finset.sum_mul]
                calc (∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ)) * (1095801216 * 100000)
                    ≤ (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) * (1095801216 * 100000) :=
                      mul_le_mul_of_nonneg_right hle (by norm_num)
                  _ = 100000 * 1095801216 * (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) := by ring
              exact add_le_add (mul_le_mul_of_nonneg_right h1 hZ) le_rfl
        _ = Work.Spaces.Gam α θ * (α * 100000
              + (100000 * 1095801216 * ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ))
                * (Real.sin (2 * θ)) ^ 2) := by ring
    · -- The two endpoints, where both sides vanish.
      have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases hθ with ⟨h0, h1⟩
        rcases lt_or_eq_of_le h0 with h0' | h0'
        · rcases lt_or_eq_of_le h1 with h1' | h1'
          · exact absurd ⟨h0', h1'⟩ hθm
          · exact Or.inr h1'
        · exact Or.inl h0'.symm
      rcases hcases with rfl | rfl
      · rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' _ hi1 (by simp), abs_zero,
          Work.Spaces.Gam_zero_left α (ne_of_gt hα0)]
        simp
      · rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' _ hi1
            (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]), abs_zero,
          Work.Spaces.Gam_zero_right α (ne_of_gt hα0)]
        simp

end Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_IsEpsSolP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Aux3/L12_slice_eq_zero_of_IsEpsSolP.lean`

**The zero mode of `L₁₂` is conserved along an `IsEpsSolP`-solution.**

The `P₀`-scheme's right-hand side is `Pz`-projected, so `L₁₂(∂_τ g)(0) = 0` at every fake time
(`PZeroAux.Pz_l12`); together with the derivative-under-the-integral lemma
`E5Aux3.hasDerivWithinAt_L12_slice_of_majorant` this says that the function

    φ(τ) = L₁₂(slice g τ)(0)

is continuous on `[0,T]`, has vanishing one-sided derivative on `(0,T)`, and starts at
`L₁₂ g₀ (0) = 0`.  Hence `φ ≡ 0`: the unmollified zero mode vanishes at every fake time.  That is
the input `hl12` of the E5 assembly needs (see `L12_Jeps_slice_tendsto_of_zero`).

The only mathematics is the elementary constancy lemma
`eq_zero_of_hasDerivWithinAt_zero_Icc` (a continuous function on `[0,T]` with vanishing
within-derivative on the interior and vanishing at `0` is zero), proved from
`monotoneOn_of_deriv_nonneg` / `antitoneOn_of_deriv_nonpos`: `φ` is simultaneously monotone and
antitone on the convex set `[0,T]`, hence constant there.
-/

open scoped Topology

namespace Work.FTS.StrongEps.E5Aux3



end Work.FTS.StrongEps.E5Aux3
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.hasDerivWithinAt_L12_slice_of_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.E5Aux3.hasDerivWithinAt_L12_slice_of_majorant`

The fake-time derivative of the `L₁₂`-zero mode of the (unmollified) family:

  `∂_τ L₁₂ (slice g τ)(0) = L₁₂ (epsRHSP … g τ)(0)`,

i.e. the `(j,i) = (0,0)` slot of the chain rule for `IsEpsSolP` families, with the *σ-uniform*
majorant `hmaj` replacing the window bounds that the mollified siblings need.

Two differentiations under the integral:

* **inner** (`θ`-level, `hasDerivAt_L12dens_slice`): for every `r > 0`, the map
  `σ ↦ L12dens K (slice g σ) r = ∫_θ K(θ)·g(r,θ,σ)/r dθ` has derivative
  `L12dens K (epsRHSP … g τ) r` at interior points of `Icc 0 T`.  The pointwise-in-`θ`
  derivative is `hsol`; the domination is the pointwise bound of `hmaj`, and the
  integrability of the value integrand is `hmaj`'s `θ`-integrability of `G`.
* **outer** (`r`-level): `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the majorant
  `bound r := ∫_θ G r θ ds` (integrable by `hmaj`), the value integrability `hval` and the
  a.e.-measurability of the derived density `hder`.

The only genuinely non-elementary input is the **a.e. strong measurability in `θ`** of the
right-hand side slice `θ ↦ K(θ)·epsRHSP … g τ r θ / r`
(`aeStronglyMeasurable_K_mul_epsRHSP_slice`): no hypothesis states it, and a derivative of a
function that is merely differentiable in the time variable need not be measurable.  It is
*produced* here from the joint `C¹`-regularity `hcont` of the family, by exhibiting the slice as an
a.e. limit of the continuous difference quotients `(σₙ - τ)⁻¹(g(r,θ,σₙ) - g(r,θ,τ))` along the
sequences `σₙ = τ + (T-τ)/(n+1) ↓ τ` and using the pointwise derivative `hsol`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Auxiliary facts about the angular interval and the family -/

/-- `K` is continuous. -/
lemma continuous_K : Continuous Work.Spaces.K := by
  show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

/-- `a / r * x = a * x / r`, the form in which the angular density is written. -/
lemma K_div_mul_eq_mul_div (a x r : ℝ) : a / r * x = a * x / r := by ring

/-- `volume.restrict (Ioo 0 (π/2)) = volume.restrict Iθ`. -/
lemma restrict_Ioo_eq_restrict_Icc :
    volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict (Set.Icc 0 (π / 2)) :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc' (μ := volume) (by simp) (by simp))

/-- Almost every point of `Iθ` lies in the open interval. -/
lemma ae_mem_Ioo_Icc :
    ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo

/-- A function continuous on the open angular interval is a.e.-strongly measurable on `Iθ`. -/
lemma aestronglyMeasurable_restrict_Icc_of_continuousOn_Ioo {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable f (volume.restrict (Set.Icc 0 (π / 2))) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact hf.aestronglyMeasurable measurableSet_Ioo

/-- **The `θ`-slice of the family is continuous on the open angular interval.**
This is the `θ ↦ (r, θ, σ)`-slice of the joint `C¹`-regularity `hcont` of the family. -/
lemma continuousOn_slice_of_contDiffOn {T : ℝ} {g : Fam}
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    {r σ : ℝ} (hr : 0 < r) (hσ : σ ∈ Set.Icc 0 T) :
    ContinuousOn (fun θ : ℝ => g r θ σ) (Set.Ioo 0 (π / 2)) := by
  have hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) := hcont.continuousOn
  have hmap : ContinuousOn (fun θ : ℝ => (r, (θ, σ))) (Set.Ioo 0 (π / 2)) :=
    (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
  refine (hF.comp hmap ?_)
  intro θ hθ
  exact ⟨hr, hθ, hσ⟩



/-! ## Measurability in `θ` of the right-hand-side slice -/

/-- **The `θ`-slice of the right-hand side is a.e.-strongly measurable on `Iθ`.**

The scheme `hsol` gives, at every interior point `x` of the time interval and every `θ` in the
open angular interval, the pointwise derivative of `σ ↦ g r θ σ`; since the slices
`θ ↦ g r θ σₙ` are continuous on the open angular interval (`hcont`), the difference quotients are
continuous, hence a.e.-strongly measurable on `Iθ`, and their a.e. limit — the slice of the right
hand side — inherits measurability. -/
lemma aeStronglyMeasurable_K_mul_epsRHSP_slice {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Set.Ioo 0 T) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.K θ * epsRHSP α ρ ε Φs E g x r θ / r)
      (volume.restrict (Set.Icc 0 (π / 2))) := by
  have hxI : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx.2.le⟩
  have hTx : 0 < T - x := by linarith [hx.2]
  set σ : ℕ → ℝ := fun n => x + (T - x) / ((n : ℝ) + 1) with hσ
  have hσn : ∀ n : ℕ, σ n = x + (T - x) / ((n : ℝ) + 1) := fun n => by rw [hσ]
  have hσmem : ∀ n, σ n ∈ Set.Icc (0 : ℝ) T := by
    intro n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hq0 : 0 < (T - x) / ((n : ℝ) + 1) := div_pos hTx hden
    have hq : (T - x) / ((n : ℝ) + 1) ≤ T - x := by
      rw [div_le_iff₀ hden]
      nlinarith
    rw [hσn n]
    exact ⟨by linarith [hx.1], by linarith⟩
  have hσne : ∀ n, σ n ≠ x := by
    intro n h
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hq0 : 0 < (T - x) / ((n : ℝ) + 1) := div_pos hTx hden
    rw [hσn n] at h
    linarith
  have hσtend : Tendsto σ atTop (𝓝 x) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 : Tendsto (fun n : ℕ => (T - x) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h1
    have h3 : Tendsto (fun n : ℕ => x + (T - x) / ((n : ℝ) + 1)) atTop (𝓝 (x + 0)) :=
      h2.const_add x
    simpa only [hσ, add_zero] using h3
  have hσwithin : Tendsto σ atTop (𝓝[Set.Icc (0 : ℝ) T \ {x}] x) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within σ hσtend
      (Eventually.of_forall fun n => ⟨hσmem n, hσne n⟩)
  have hsl : ∀ n, ContinuousOn (fun θ : ℝ => g r θ (σ n)) (Set.Ioo 0 (π / 2)) :=
    fun n => continuousOn_slice_of_contDiffOn hcont hr (hσmem n)
  have hmeas : ∀ n, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => slope (fun s => (Work.Spaces.K θ / r) * g r θ s) x (σ n))
      (volume.restrict (Set.Icc 0 (π / 2))) := by
    intro n
    refine aestronglyMeasurable_restrict_Icc_of_continuousOn_Ioo ?_
    have h1 : ContinuousOn (fun θ : ℝ => (Work.Spaces.K θ / r) * g r θ (σ n))
        (Set.Ioo 0 (π / 2)) :=
      (continuous_K.div_const r).continuousOn.mul (hsl n)
    have h2 : ContinuousOn (fun θ : ℝ => (Work.Spaces.K θ / r) * g r θ x)
        (Set.Ioo 0 (π / 2)) :=
      (continuous_K.div_const r).continuousOn.mul
        (continuousOn_slice_of_contDiffOn hcont hr hxI)
    refine ((h1.sub h2).const_mul ((σ n - x)⁻¹)).congr ?_
    intro θ hθ
    simp only [Pi.sub_apply, slope, smul_eq_mul, vsub_eq_sub]
  have hlim : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))),
      Tendsto (fun n : ℕ => slope (fun s => (Work.Spaces.K θ / r) * g r θ s) x (σ n)) atTop
        (𝓝 (Work.Spaces.K θ * epsRHSP α ρ ε Φs E g x r θ / r)) := by
    filter_upwards [ae_mem_Ioo_Icc] with θ hθ
    have h1 : HasDerivWithinAt (fun s => (Work.Spaces.K θ / r) * g r θ s)
        ((Work.Spaces.K θ / r) * epsRHSP α ρ ε Φs E g x r θ) (Set.Icc 0 T) x :=
      (hsol.2 r θ x hr hθ hxI).const_mul (Work.Spaces.K θ / r)
    have h2 := (hasDerivWithinAt_iff_tendsto_slope.mp h1).comp hσwithin
    have h3 : (Work.Spaces.K θ / r) * epsRHSP α ρ ε Φs E g x r θ
        = Work.Spaces.K θ * epsRHSP α ρ ε Φs E g x r θ / r :=
      K_div_mul_eq_mul_div ..
    rw [h3] at h2
    exact h2
  exact aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim

/-! ## The inner (`θ`-level) differentiation -/



end Work.FTS.StrongEps.E5Aux3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.shift_modulus_of_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.StrongEps.E5G

theorem shift_modulus_of_holder {Y : ℕ → ℝ → ℝ → ℝ} {A z θ ρ : ℝ}
    (hA : 0 ≤ A) (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (hρ : 0 < ρ)
    (hρQ : Metric.closedBall (z, θ) ρ ⊆ Work.FTS.EllipticEst.Q0)
    (hholder : ∀ n : ℕ, ∀ q ∈ Metric.closedBall (z, θ) ρ,
      ∀ q' ∈ Metric.closedBall (z, θ) ρ,
      |Y n q.1 q.2 - Y n q'.1 q'.2| ≤ A * Real.sqrt ‖q - q'‖) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p : ℝ × ℝ, ‖p‖ ≤ δ →
      |Y n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - Y n z θ| ≤ η := by
  -- The two shifts are continuous at `p = 0` with value `(z, θ)`; a small parameter `p`
  -- therefore moves the base point inside the ball of Hölder-regularity and by a distance
  -- at most `(η/(A+1))²`, which is what the Hölder bound needs.
  intro η hη
  set F : ℝ × ℝ → ℝ × ℝ :=
    fun p => (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2) with hF
  have hθtan : Real.arctan (Real.tan θ) = θ :=
    Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2
  have hF0 : F 0 = (z, θ) := by
    simp only [hF, Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift,
      Prod.fst_zero, Prod.snd_zero, neg_zero, Real.exp_zero, mul_one, hθtan]
  have hcont : Continuous F := by
    rw [hF]
    refine Continuous.prodMk ?_ ?_
    · simp only [Work.FTS.StrongEps.zShift]
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_neg.comp continuous_fst))
    · simp only [Work.FTS.StrongEps.thShift]
      exact Real.continuous_arctan.comp
        (continuous_const.mul (Real.continuous_exp.comp (continuous_neg.comp continuous_snd)))
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ p : ℝ × ℝ, ‖p‖ ≤ δ →
      dist (F p) (F 0) < min ρ ((η / (A + 1)) ^ 2) := by
    have hτpos : 0 < min ρ ((η / (A + 1)) ^ 2) :=
      lt_min hρ (pow_pos (div_pos hη hA1) 2)
    have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (0 : ℝ × ℝ),
        F p ∈ Metric.ball (F 0) (min ρ ((η / (A + 1)) ^ 2)) :=
      hcont.continuousAt (Metric.ball_mem_nhds (F 0) hτpos)
    obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨δ₀ / 2, by linarith, fun p hp => ?_⟩
    have hp' : p ∈ Metric.ball (0 : ℝ × ℝ) δ₀ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      linarith
    exact Metric.mem_ball.mp (hδ₀sub hp')
  refine ⟨δ, hδpos, ?_⟩
  intro n p hp
  have hdist : dist (F p) (F 0) < min ρ ((η / (A + 1)) ^ 2) := hδ p hp
  have hq : F p ∈ Metric.closedBall (z, θ) ρ := by
    rw [Metric.mem_closedBall, ← hF0]
    exact le_trans hdist.le (min_le_left _ _)
  have hq' : (z, θ) ∈ Metric.closedBall (z, θ) ρ := by
    rw [Metric.mem_closedBall, dist_self]
    exact hρ.le
  have hb := hholder n (F p) hq (z, θ) hq'
  have hnorm : ‖F p - (z, θ)‖ ≤ (η / (A + 1)) ^ 2 := by
    rw [← hF0, ← dist_eq_norm]
    exact le_trans hdist.le (min_le_right _ _)
  have hsqrt : Real.sqrt ‖F p - (z, θ)‖ ≤ η / (A + 1) :=
    calc Real.sqrt ‖F p - (z, θ)‖ ≤ Real.sqrt ((η / (A + 1)) ^ 2) := Real.sqrt_le_sqrt hnorm
      _ = η / (A + 1) := Real.sqrt_sq (le_of_lt (div_pos hη hA1))
  have hcoef : A * (η / (A + 1)) ≤ η := by
    have h1 : A * (η / (A + 1)) = A * η / (A + 1) := by ring
    rw [h1, div_le_iff₀ hA1]
    nlinarith
  calc |Y n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - Y n z θ|
      = |Y n (F p).1 (F p).2 - Y n (z, θ).1 (z, θ).2| := by simp only [hF]
    _ ≤ A * Real.sqrt ‖F p - (z, θ)‖ := hb
    _ ≤ A * (η / (A + 1)) := mul_le_mul_of_nonneg_left hsqrt hA
    _ ≤ η := hcoef

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroDiffBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The pointwise difference bound with a constant independent of `n` -/

/-- **The difference of the cut-off integrand and the model integrand**, with a constant that is
independent of the cut-off index `n`.  This is the uniform-in-`n` form of
`SlotsZeroModeKey2.abs_sub_modeTest_le` (whose constant is the same but is not stated to be
`n`-independent); it is what allows a single `A` to serve all `n` in `SlotsZeroDiffBound`. -/
theorem abs_sub_modeTest_le_uniform {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ} (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b) (hCut : CutFacts m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.EllipticEst.Q0 →
      |Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
        - Φ p.1 p.2 * Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
          * bslWeight α p|
        ≤ C * (1 + 1 / delta n) * (|Φ p.1 p.2|
            * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_bslOp_Psi (α := α) hρ hsub
  obtain ⟨Cr, hCr0, hCr⟩ := exists_bound_abs_rho hρ hsub
  obtain ⟨Cc, hCc0, hCc⟩ := hCut.2.2.2.2.2.2
  obtain ⟨W, hW0, hW⟩ := abs_bslWeight_mul_indicator_le (α := α) ha
  refine ⟨(B + Cr * Cc) * W, by positivity, fun n p hp => ?_⟩
  have hδ : 0 < delta n := hCut.delta_pos n
  classical
  obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hcos : Real.cos p.2 ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  -- split the difference
  have hsplit : Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
      - Φ p.1 p.2 * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p
      = Φ p.1 p.2 * ((angCut n p.2 - 1) * Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
          + ρ p.1 * comm m n p.2) * bslWeight α p := by
    rw [bslOp_modeTest (α := α) hcos]
    ring
  rw [hsplit, abs_mul, abs_mul]
  -- bound each factor
  have hA : |angCut n p.2 - 1| ≤ layerInd n p.2 := by
    by_cases h : 2 * delta n ≤ p.2 ∧ p.2 ≤ π / 2 - 2 * delta n
    · have h1 := hCut.eq_one_off_layer n h.1 h.2
      rw [h1, sub_self, abs_zero]
      exact indicator_one_nonneg p.2
    · rw [abs_sub_le_iff, layerInd, Set.indicator_apply]
      split_ifs with hmem
      · exact ⟨by linarith [(hCut.bounds n p.2).2], by linarith [(hCut.bounds n p.2).1]⟩
      · have h2δ : 2 * delta n ≤ p.2 := by
          by_contra hcon
          simp only [not_le] at hcon
          exact hmem (Or.inl ⟨hθ0, hcon⟩)
        have hπ : p.2 ≤ π / 2 - 2 * delta n := by
          by_contra hcon
          simp only [not_le] at hcon
          exact hmem (Or.inr ⟨hcon, hθ1⟩)
        rw [hCut.eq_one_off_layer n h2δ hπ]
        norm_num
  have hBp : |Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      p.1 p.2| ≤ B * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := hB p hp
  have hcomm := hCc n p.2 hθ0 hθ1
  have hρb : |ρ p.1| ≤ Cr * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := hCr p.1
  -- assemble
  have hI : 0 ≤ (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := indicator_one_nonneg p.1
  have hL : 0 ≤ layerInd n p.2 := indicator_one_nonneg p.2
  have hstep1 : |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
        (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      + ρ p.1 * comm m n p.2|
      ≤ (B + Cr * (Cc / delta n)) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
        * layerInd n p.2 := by
    calc |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
          + ρ p.1 * comm m n p.2|
        ≤ |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2|
          + |ρ p.1 * comm m n p.2| := abs_add_le _ _
      _ = |angCut n p.2 - 1| * |Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2|
          + |ρ p.1| * |comm m n p.2| := by rw [abs_mul, abs_mul]
      _ ≤ layerInd n p.2 * (B * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
          + (Cr * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
            * (Cc / delta n * layerInd n p.2) := by
          refine add_le_add (mul_le_mul hA hBp (abs_nonneg _) hL) (mul_le_mul hρb hcomm
            (abs_nonneg _) (mul_nonneg hCr0 hI))
      _ = (B + Cr * (Cc / delta n)) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
            * layerInd n p.2 := by ring
  have hfinal : |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
        (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      + ρ p.1 * comm m n p.2|
      ≤ (B + Cr * Cc) * (1 + 1 / delta n) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
        * layerInd n p.2 := by
    refine hstep1.trans ?_
    have h2 : B + Cr * (Cc / delta n) ≤ (B + Cr * Cc) * (1 + 1 / delta n) := by
      have hδinv : 0 < (delta n)⁻¹ := inv_pos.mpr hδ
      have hexp : (B + Cr * Cc) * (1 + 1 / delta n)
          = B + B * (delta n)⁻¹ + Cr * Cc + Cr * Cc * (delta n)⁻¹ := by
        rw [div_eq_mul_inv]; ring
      rw [div_eq_mul_inv, hexp]
      nlinarith [mul_nonneg hB0 hδinv.le, mul_nonneg (mul_nonneg hCr0 hCc0.le) hδinv.le]
    calc (B + Cr * (Cc / delta n)) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * layerInd n p.2
        ≤ ((B + Cr * Cc) * (1 + 1 / delta n)) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * layerInd n p.2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hI) hL
      _ = (B + Cr * Cc) * (1 + 1 / delta n) * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * layerInd n p.2 := by ring
  calc |Φ p.1 p.2| * |(angCut n p.2 - 1) * Work.Elliptic.bslOp α
        (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
        + ρ p.1 * comm m n p.2| * |bslWeight α p|
      ≤ |Φ p.1 p.2| * ((B + Cr * Cc) * (1 + 1 / delta n)
          * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2) * |bslWeight α p| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfinal (abs_nonneg _)) (abs_nonneg _)
    _ = (B + Cr * Cc) * (1 + 1 / delta n)
          * (|Φ p.1 p.2| * ((Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * |bslWeight α p|)
            * layerInd n p.2) := by ring
    _ ≤ (B + Cr * Cc) * (1 + 1 / delta n)
          * (|Φ p.1 p.2| * (W * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
            * layerInd n p.2) := by
        have hconst : (0 : ℝ) ≤ (B + Cr * Cc) * (1 + 1 / delta n) :=
          mul_nonneg (add_nonneg hB0 (mul_nonneg hCr0 hCc0.le))
            (add_nonneg zero_le_one (div_nonneg zero_le_one hδ.le))
        refine mul_le_mul_of_nonneg_left ?_ hconst
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hL
        exact (mul_comm _ _).trans_le (hW p)
    _ = ((B + Cr * Cc) * W) * (1 + 1 / delta n)
          * (|Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
            * layerInd n p.2) := by ring

/-! ## The `L¹` bound -/

theorem SlotsZeroDiffBound {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ} {a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (hCut : Work.FTS.StrongEps.EComparison.CutFacts m)
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b))
    (ha : 0 < a) (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ,
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        Φ p.1 p.2
            * Work.Elliptic.bslOp α (Work.FTS.StrongEps.EComparison.modeTest m ρ n) p.1 p.2
            * Work.FTS.StrongEps.EComparison.bslWeight α p
          - Φ p.1 p.2
            * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                p.1 p.2
            * Work.FTS.StrongEps.EComparison.bslWeight α p)
        Work.FTS.EllipticEst.Q0 ∧
      (∫ p in Work.FTS.EllipticEst.Q0, |Φ p.1 p.2
          * Work.Elliptic.bslOp α (Work.FTS.StrongEps.EComparison.modeTest m ρ n) p.1 p.2
          * Work.FTS.StrongEps.EComparison.bslWeight α p
          - Φ p.1 p.2
            * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                p.1 p.2
            * Work.FTS.StrongEps.EComparison.bslWeight α p|)
        ≤ A * (1 + 1 / Work.FTS.StrongEps.EComparison.delta n)
          * (∫ p in Work.FTS.EllipticEst.Q0,
              |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
                * Work.FTS.StrongEps.EComparison.layerInd n p.2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := abs_sub_modeTest_le_uniform (α := α) (Φ := Φ) (ρ := ρ) (m := m)
    hρ ha hsub hCut
  -- product-measure integrability of `|Φ| · 1_{[a,b]}(z)`
  have hbox : MeasureTheory.Integrable (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
      (volume.restrict Work.FTS.EllipticEst.Q0) :=
    integrableOn_absPhi_box hsm hΦint hEint
  have hQ0m : MeasurableSet (Work.FTS.EllipticEst.Q0) :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- continuity of the relevant factors on the open quadrant
  have hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr hsm).continuousOn
  have hψ2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun k =>
      ((Work.FTS.ClassC.contDiffOn_uncurry_fst (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
          ((hρ k).contDiffOn)).mul
        (Work.FTS.ClassC.contDiffOn_uncurry_snd (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
          (Work.FTS.ClassC.contDiff_eFam_nat m k)))
  have hc2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α
      (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_bslOp_of_smoothOpen hψ2
  refine ⟨C, hC0, fun n => ?_⟩
  -- the difference integrand `F` and the dominating function `G`
  set F : ℝ × ℝ → ℝ := fun p =>
      Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
      - Φ p.1 p.2 * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p
    with hFdef
  set G : ℝ × ℝ → ℝ := fun p => C * (1 + 1 / delta n)
      * (|Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
    with hGdef
  have hδ : 0 < delta n := hCut.delta_pos n
  have hψ1 : Work.FTS.EllipticEst.SmoothOpen (modeTest m ρ n) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun k =>
      (modeTest_contDiff hρ hCut k).contDiffOn
  have hFcont : ContinuousOn F Work.FTS.EllipticEst.Q0 := by
    rw [hFdef]
    exact ((hΦc.mul (continuousOn_bslOp_of_smoothOpen hψ1)).mul (continuousOn_weight α)).sub
      ((hΦc.mul hc2).mul (continuousOn_weight α))
  have hFmeas : AEStronglyMeasurable F (volume.restrict Work.FTS.EllipticEst.Q0) :=
    hFcont.aestronglyMeasurable (μ := volume) hQ0m
  -- the layer weight is an indicator of a measurable set
  have hlayerMeas : MeasurableSet (layer n) := by
    rw [layer]
    exact measurableSet_Ioo.union measurableSet_Ioo
  have hlayerInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      (volume.restrict Work.FTS.EllipticEst.Q0) := by
    have hfun : (fun p : ℝ × ℝ => |Φ p.1 p.2|
        * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
        = (Set.univ ×ˢ layer n).indicator (fun p : ℝ × ℝ => |Φ p.1 p.2|
            * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) := by
      funext p
      simp only [layerInd, Set.indicator_apply, Set.mem_prod, Set.mem_univ, true_and]
      by_cases h : p.2 ∈ layer n <;> simp [h]
    rw [hfun]
    exact hbox.indicator (MeasurableSet.univ.prod hlayerMeas)
  have hGint : MeasureTheory.Integrable G (volume.restrict Work.FTS.EllipticEst.Q0) := by
    rw [hGdef]
    exact hlayerInt.const_mul (C * (1 + 1 / delta n))
  -- the pointwise domination
  have hFG : ∀ᵐ p ∂(volume.restrict Work.FTS.EllipticEst.Q0), ‖F p‖ ≤ G p := by
    refine MeasureTheory.ae_restrict_of_forall_mem hQ0m fun p hp => ?_
    have h1 : F p = Φ p.1 p.2 * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2 * bslWeight α p
        - Φ p.1 p.2 * Work.Elliptic.bslOp α
            (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2 * bslWeight α p := by
      simp only [hFdef]
    have h2 : G p = C * (1 + 1 / delta n)
        * (|Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * layerInd n p.2) := by
      simp only [hGdef]
    rw [Real.norm_eq_abs, h1, h2]
    exact hC n p hp
  have hIntF : MeasureTheory.Integrable F (volume.restrict Work.FTS.EllipticEst.Q0) :=
    hGint.mono' hFmeas hFG
  constructor
  · exact hIntF
  · have hFnorm : MeasureTheory.Integrable (fun p : ℝ × ℝ => |F p|)
        (volume.restrict Work.FTS.EllipticEst.Q0) := by
      simpa only [Real.norm_eq_abs] using hIntF.norm
    have hFG2 : ∀ᵐ p ∂(volume.restrict Work.FTS.EllipticEst.Q0), |F p| ≤ G p := by
      filter_upwards [hFG] with p hp
      simpa only [Real.norm_eq_abs] using hp
    have hmono : ∫ p in Work.FTS.EllipticEst.Q0, |F p|
        ≤ ∫ p in Work.FTS.EllipticEst.Q0, G p :=
      integral_mono_ae hFnorm hGint hFG2
    have hGval : ∫ p in Work.FTS.EllipticEst.Q0, G p
        = C * (1 + 1 / delta n) * (∫ p in Work.FTS.EllipticEst.Q0,
            |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
              * layerInd n p.2) := by
      rw [hGdef, integral_const_mul]
    calc ∫ p in Work.FTS.EllipticEst.Q0, |F p|
        ≤ ∫ p in Work.FTS.EllipticEst.Q0, G p := hmono
      _ = C * (1 + 1 / delta n) * (∫ p in Work.FTS.EllipticEst.Q0,
            |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
              * layerInd n p.2) := hGval

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.Jeps_eq_iterated =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open MeasureTheory Set Filter

theorem Jeps_eq_iterated {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W) {s θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.StrongEps.Jeps ρ ε W (Real.exp s) θ
      = ∫ q in Set.Icc (-ε) ε, ∫ a : ℝ,
          Work.FTS.StrongEps.Jker ρ ε (a, q) * W (Real.exp (s - a))
            (Work.FTS.StrongEps.thShift θ q) := by
  rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε W (Real.exp_pos s) hθ]
  have hshift : ∀ p : ℝ × ℝ,
      Work.FTS.StrongEps.zShift (Real.exp s) p.1 = Real.exp (s - p.1) := by
    intro p
    simp only [Work.FTS.StrongEps.zShift, sub_eq_add_neg, Real.exp_add]
  simp only [hshift]
  -- the integrand is integrable: the kernel has compact support and the profile is continuous
  -- and bounded on the (compact) image of that support.
  have hInt : Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
      W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2)) := by
    have hΦcont : Continuous fun p : ℝ × ℝ =>
        (Real.exp (s - p.1), Work.FTS.StrongEps.thShift θ p.2) :=
      (Real.continuous_exp.comp (continuous_const.sub continuous_fst)).prodMk
        ((Work.FTS.StrongEps.continuous_thShift θ).comp continuous_snd)
    have hmap : MapsTo (fun p : ℝ × ℝ =>
        (Real.exp (s - p.1), Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) Work.FTS.EllipticEst.Q0 := by
      intro p _
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨Real.exp_pos _, Work.FTS.StrongEps.thShift_mem hθ⟩
    have hcontA : ContinuousOn (fun p : ℝ × ℝ =>
        W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      hsm.continuousOn.comp hΦcont.continuousOn hmap
    have hIntOn : IntegrableOn (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      Work.FTS.StrongEps.integrableOn_Jker_mul_ball hρ hε hcontA
    have hzero : ∀ p : ℝ × ℝ, p ∉ Metric.closedBall (0 : ℝ × ℝ) ε →
        Work.FTS.StrongEps.Jker ρ ε p *
          W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2) = 0 := fun p hp => by
      rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul]
    have hfun : (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2))
        = (Metric.closedBall (0 : ℝ × ℝ) ε).indicator (fun p : ℝ × ℝ =>
            Work.FTS.StrongEps.Jker ρ ε p *
              W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2)) := by
      funext p
      by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp, hzero p hp]
    rw [hfun]
    exact (MeasureTheory.integrable_indicator_iff measurableSet_closedBall).2 hIntOn
  rw [show (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p *
        W (Real.exp (s - p.1)) (Work.FTS.StrongEps.thShift θ p.2))
      = ∫ y : ℝ, ∫ x : ℝ, Work.FTS.StrongEps.Jker ρ ε (x, y) *
        W (Real.exp (s - x)) (Work.FTS.StrongEps.thShift θ y) from
    MeasureTheory.integral_prod_symm (μ := volume) (ν := volume) _ hInt]
  -- the inner integral vanishes unless `q ∈ [-ε, ε]`
  have hH : ∀ q : ℝ, q ∉ Set.Icc (-ε) ε →
      (∫ a : ℝ, Work.FTS.StrongEps.Jker ρ ε (a, q) * W (Real.exp (s - a))
        (Work.FTS.StrongEps.thShift θ q)) = 0 := by
    intro q hq
    have hqabs : ε < |q| := by
      have hq' : q < -ε ∨ ε < q := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hq
      rcases hq' with h | h
      · have hεq : ε < -q := by linarith
        exact lt_of_lt_of_le hεq (neg_le_abs q)
      · exact lt_of_lt_of_le h (le_abs_self q)
    have hJ : ∀ a : ℝ, Work.FTS.StrongEps.Jker ρ ε (a, q) = 0 := by
      intro a
      by_contra hne
      have hb := Work.FTS.StrongEps.Jker_ne_zero_support hρ hε hne
      have h1 : q ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg a]
      have h2 : |q| ≤ ε := by
        rw [sq_le_sq] at h1
        rwa [abs_of_nonneg hε.le] at h1
      linarith
    simp [hJ]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hH]

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.exists_bound_integral_Jker_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-- The kernel `Jker ρ ε` is nonnegative, because `ρ` is. -/
theorem Jker_slice_nonneg {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    (ε : ℝ) (p : ℝ × ℝ) : 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := by
  rw [Work.FTS.StrongEps.Jker]
  exact mul_nonneg (sq_nonneg _) (hρ.nonneg _)

/-- **The `p₁`-slices of the rescaled kernel have uniformly bounded integrals.**

`Jker ρ ε` is supported in the closed ball of radius `ε`, so for every fixed `p₂ = q` the slice
`p₁ ↦ Jker ρ ε (p₁, q)` is continuous and vanishes off `[-ε, ε]`; continuity on the compact box
`[-ε, ε] × [-ε, ε]` supplies a bound `M` on the box, and off the box the slice vanishes in each
variable.  Hence every slice integral is at most `M · 2ε`. -/
theorem exists_bound_integral_Jker_slice {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : ℝ, ∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, q) ≤ B := by
  have hcont : Continuous (Work.FTS.StrongEps.Jker ρ ε) :=
    Work.FTS.StrongEps.Jker_continuous hρ ε
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hcont.continuousOn :
      ContinuousOn (Work.FTS.StrongEps.Jker ρ ε)
        (Set.Icc (-ε) ε ×ˢ Set.Icc (-ε) ε))
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _)
      (hM (0, 0) ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
  have hsmall : ∀ x : ℝ, x ∉ Set.Icc (-ε) ε → ε < |x| := by
    intro x hx
    by_contra hc
    push Not at hc
    exact hx ⟨by linarith [neg_abs_le x, hc], by linarith [le_abs_self x, hc]⟩
  -- the slice vanishes in each variable off `[-ε, ε]`
  have hzero_snd : ∀ (x y : ℝ), y ∉ Set.Icc (-ε) ε → Work.FTS.StrongEps.Jker ρ ε (x, y) = 0 := by
    intro x y hy
    refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε ?_
    intro hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have h1 : |y| ≤ ε := by
      have := norm_snd_le ((x, y) : ℝ × ℝ)
      rw [Real.norm_eq_abs] at this
      exact le_trans this hmem
    exact absurd h1 (not_le.2 (hsmall y hy))
  have hzero_fst : ∀ (x y : ℝ), x ∉ Set.Icc (-ε) ε → Work.FTS.StrongEps.Jker ρ ε (x, y) = 0 := by
    intro x y hx
    refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε ?_
    intro hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have h1 : |x| ≤ ε := by
      have := norm_fst_le ((x, y) : ℝ × ℝ)
      rw [Real.norm_eq_abs] at this
      exact le_trans this hmem
    exact absurd h1 (not_le.2 (hsmall x hx))
  refine ⟨M * (2 * ε), mul_nonneg hM0 (by linarith), fun q => ?_⟩
  have hrestrict : (∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, q))
      = ∫ p₁ in Set.Icc (-ε) ε, Work.FTS.StrongEps.Jker ρ ε (p₁, q) :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun p₁ : ℝ => Work.FTS.StrongEps.Jker ρ ε (p₁, q))
      (s := Set.Icc (-ε) ε) (fun x hx => hzero_fst x q hx)).symm
  rw [hrestrict]
  calc ∫ x in Set.Icc (-ε) ε, Work.FTS.StrongEps.Jker ρ ε (x, q)
      ≤ ∫ _ in Set.Icc (-ε) ε, M := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => Jker_slice_nonneg hρ ε (x, q))
          (MeasureTheory.integrableOn_const (C := M) ?_) ?_
        · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
          by_cases hq : q ∈ Set.Icc (-ε) ε
          · have h := hM (x, q) ⟨hx, hq⟩
            exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h)
          · rw [hzero_snd x q hq]
            exact hM0
    _ = M * (2 * ε) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real_def,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.IP_perturb =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.aesm_Jeps_slice_of_aesm_logPull =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux


end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Repair.aestronglyMeasurable_Jker_mul_epsRHSP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.EpsE4Thr.Repair


end Work.FTS.StrongEps.EpsE4Thr.Repair
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLimCont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem EpsLimCont {α B T : ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {F : ℝ → Work.FTS.Galerkin.Fn}
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongEps.ConvLev0H6 α B (fun n => Work.FTS.Galerkin.slice (G n) τ) (F τ))
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
        |Work.FTS.Galerkin.slice (G n) τ p.1 p.2 - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2|
          ≤ C * |τ - τ'|) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => F τ z θ) (Set.Icc (0 : ℝ) T) := by
  intro z θ hQ
  -- `Qd` and `Q0` are the same set (the open quadrant `(0,∞) × (0,π/2)`).
  have hQ0 : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hQ
  have hKsub : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Set.mem_singleton_iff.mp hp ▸ hQ0
  -- the `τ`-Lipschitz constant of the scheme, valid for all `n` at the *single* point `(z,θ)`.
  obtain ⟨C, hC0, hC⟩ := hlip {(z, θ)} isCompact_singleton hKsub
  -- local uniform convergence at the singleton `{(z,θ)}` is pointwise convergence at `(z,θ)`.
  have hpt : ∀ τ ∈ Set.Icc (0 : ℝ) T, Tendsto (fun n => G n z θ τ) atTop (𝓝 (F τ z θ)) := by
    intro τ hτ
    have h1 := (hconv τ hτ).conv {(z, θ)} isCompact_singleton hKsub
    have h2 := h1.tendsto_at (Set.mem_singleton _)
    simpa [Work.FTS.Galerkin.slice_apply] using h2
  refine LipschitzOnWith.continuousOn (K := ⟨C, hC0⟩) ?_
  refine LipschitzOnWith.of_dist_le_mul (K := ⟨C, hC0⟩) ?_
  intro x hx y hy
  have hxy : ∀ n, |G n z θ x - G n z θ y| ≤ C * |x - y| := by
    intro n
    have h := hC n (z, θ) (Set.mem_singleton _) x hx y hy
    simpa [Work.FTS.Galerkin.slice_apply] using h
  have hlim : Tendsto (fun n => |G n z θ x - G n z θ y|) atTop (𝓝 |F x z θ - F y z θ|) :=
    ((hpt x hx).sub (hpt y hy)).abs
  have := le_of_tendsto' hlim hxy
  rw [Real.dist_eq, Real.dist_eq]
  exact this

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.AEShiftProfile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Measurability of the shifted profile.**  If `f` is smooth on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen f`, i.e. `ContDiffOn ℝ smoothOrder (uncurry f) (Ioi 0 ×ˢ Ioo 0 (π/2))`),
then for `z > 0` and `θ ∈ (0,π/2)` the function
`p ↦ f (z * exp (-p.1)) (arctan (tan θ * exp (-p.2)))` is a.e. strongly measurable on `ℝ²`.

Route: the shift `p ↦ (z * exp (-p.1), arctan (tan θ * exp (-p.2)))` is continuous, and for
`z > 0`, `θ ∈ (0,π/2)` it maps `ℝ²` into the open quadrant `Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)`
(`z * exp (-p.1) > 0`, `0 < arctan (tan θ * exp (-p.2)) < π/2`), on which `uncurry f` is
continuous (`SmoothOpen` gives `ContDiffOn`, hence `ContinuousOn`).  Hence the composite is
continuous at every point (`ContinuousOn.comp_continuous` with the shift continuous), so it is
a.e. strongly measurable for Lebesgue measure.  No quasi-measure-preserving input is needed —
`Work.FTS.StrongEps.qmp_sPhi` lies in a module not imported here.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem AEShiftProfile {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
  -- `SmoothOpen f` is `C^∞` on the open quadrant, hence continuous there.
  have hcont : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hso.continuousOn
  -- The shift `p ↦ (z * exp (-p.1), arctan (tan θ * exp (-p.2)))` is continuous.
  have hshift : Continuous (fun p : ℝ × ℝ =>
      (z * Real.exp (-p.1), Real.arctan (Real.tan θ * Real.exp (-p.2)))) := by
    fun_prop
  -- For `z > 0` and `θ ∈ (0,π/2)` it lands in the open quadrant.
  have hmaps : ∀ p : ℝ × ℝ,
      (z * Real.exp (-p.1), Real.arctan (Real.tan θ * Real.exp (-p.2))) ∈
        Work.FTS.EllipticEst.Q0 := by
    intro p
    rw [Work.FTS.EllipticEst.mem_Q0]
    refine ⟨mul_pos hz (Real.exp_pos _), ?_, Real.arctan_lt_pi_div_two _⟩
    rw [Real.arctan_pos]
    exact mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _)
  -- Hence the composite is continuous everywhere, and a fortiori a.e. strongly measurable.
  have hcomp : Continuous (fun p : ℝ × ℝ =>
      f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))) := by
    simpa [Function.comp_def, Function.uncurry, Prod.fst, Prod.snd] using
      hcont.comp_continuous hshift hmaps
  exact hcomp.aestronglyMeasurable

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsRhoForm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory

/-- **The scaling substitution behind `Jker`.**  For every `h : ℝ × ℝ → ℝ` (no measurability or
integrability hypothesis: both sides use the Bochner convention `integral_undef`),

  `∫ p, (ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)) * h p = ∫ q, ρ q * h (ε • q)`,

i.e. the rescaled kernel can be traded for the plain kernel at the price of evaluating the
integrand at the scaled point `ε • q`. -/
theorem integral_inv_smul_mollify (ρ : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (h : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ, (ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)) * h p)
      = ∫ q : ℝ × ℝ, ρ q * h (ε • q) := by
  -- the two-dimensional Haar scaling `∫ p, F (ε⁻¹ • p) = (ε⁻¹)² • ∫ p, F p`
  have hkey := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (μ := (volume : Measure (ℝ × ℝ))) (fun u : ℝ × ℝ => ρ u * h (ε • u)) (R := ε) hε.le
  rw [show Module.finrank ℝ (ℝ × ℝ) = 2 from by simp [Module.finrank_prod]] at hkey
  -- `ε⁻¹ • (ε • x) = x`, so the left-hand side is the integral of `ρ (ε⁻¹ • x) * h x`
  have hleft : (∫ x : ℝ × ℝ, (fun u : ℝ × ℝ => ρ u * h (ε • u)) (ε⁻¹ • x))
      = ∫ x : ℝ × ℝ, ρ (ε⁻¹ • x) * h x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ρ (ε⁻¹ • x) * h (ε • (ε⁻¹ • x)) = ρ (ε⁻¹ • x) * h x
    rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  rw [hleft, smul_eq_mul] at hkey
  calc (∫ p : ℝ × ℝ, (ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)) * h p)
      = ε⁻¹ ^ 2 * ∫ p : ℝ × ℝ, ρ (ε⁻¹ • p) * h p := by
        rw [← MeasureTheory.integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    _ = ε⁻¹ ^ 2 * (ε ^ 2 * ∫ q : ℝ × ℝ, ρ q * h (ε • q)) := by rw [hkey]
    _ = ∫ q : ℝ × ℝ, ρ q * h (ε • q) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]

/-- **`Jeps` with the unshifted kernel.**  On the open quadrant the mollifier equals the
`ρ`-average of the profile along the *scaled* shifts `z e^{-ε q₁}`, `arctan (tan θ e^{-ε q₂})`:
the factor `ε⁻¹ ^ 2` of `Jker` is exactly the Jacobian of `p = ε q`. -/
theorem JepsRhoForm (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hε : 0 < ε) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.StrongEps.Jeps ρ ε f z θ
      = ∫ q : ℝ × ℝ, ρ q * f (z * Real.exp (-(ε * q.1)))
          (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2)))) := by
  rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε f hz hθ]
  simp only [Work.FTS.StrongEps.Jker, Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]
  have hmain := integral_inv_smul_mollify ρ hε
    (fun u : ℝ × ℝ => f (z * Real.exp (-u.1)) (Real.arctan (Real.tan θ * Real.exp (-u.2))))
  rw [hmain]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JkerEqZeroOfAbsGt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

/-- **The kernel vanishes outside the square of side `2ε`.**  If one of the two coordinates of `p`
exceeds `ε` in absolute value, then `p` lies outside the closed ball of radius `ε`, so the rescaled
kernel `Jker ρ ε` vanishes at `p` (`Jker_eq_zero_of_not_mem`, which only needs the mollifier part
`IsMollKernel ρ` of the hypothesis). -/
theorem JkerEqZeroOfAbsGt {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : ε < |p.1| ∨ ε < |p.2|) :
    Work.FTS.StrongEps.Jker ρ ε p = 0 := by
  refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ.moll hε ?_
  simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, not_le]
  rcases hp with hp | hp
  · exact lt_of_lt_of_le hp (le_max_left _ _)
  · exact lt_of_lt_of_le hp (le_max_right _ _)

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JkerNormBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem JkerNormBound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℝ × ℝ, ‖Work.FTS.StrongEps.Jker ρ ε p‖ ≤ M := by
  -- `Jker ρ ε` is continuous (as a rescaling of the `C^∞` kernel `ρ`) and compactly supported
  -- (the support of `ρ` is contained in the unit ball, so `Jker ρ ε` is supported in the ball
  -- of radius `ε`); a continuous compactly supported function on `ℝ × ℝ` is bounded in norm.
  obtain ⟨C, hC⟩ :=
    (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).bounded_above_of_compact_support
      (Work.FTS.StrongEps.Jker_hasCompactSupport hρ.moll hε)
  exact ⟨max C 0, le_max_right C 0, fun p => le_trans (hC p) (le_max_left C 0)⟩

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.MarginalTransferIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two elementary facts used by the transfer identity

`ρ` is supported in the closed unit ball (`IsMollKernel.support`), so every point at which `ρ` does
not vanish lies in `Metric.closedBall 0 1`; and the `log z`-shift `x ↦ log z - εx` of an integrable
log-coordinate trace stays integrable on the line (translation invariance of the Lebesgue measure
plus the dilation `x ↦ -ε x`). -/

/-- A point at which an admissible kernel does not vanish lies in the closed unit ball. -/
lemma mti_mem_ball_of_support {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {q : ℝ × ℝ} (hq : ρ q ≠ 0) : q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  have hs := hρ.support q hq
  have h1 : q.1 ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg q.2]
  have h2 : q.2 ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg q.1]
  refine max_le ?_ ?_
  · simpa using ((sq_le_sq.mp h1) : |q.1| ≤ |(1 : ℝ)|)
  · simpa using ((sq_le_sq.mp h2) : |q.2| ≤ |(1 : ℝ)|)

/-- **Integrability of the shifted absolute trace.**  If `u ↦ lam (exp u)` is integrable on the
line and `ε > 0`, `z > 0`, then so is `x ↦ |lam (z exp (-(ε x)))|`.  Indeed
`z exp (-(ε x)) = exp (log z - ε x)`, and the affine map `x ↦ log z - ε x` preserves
integrability (`MeasureTheory.MeasurePreserving.integrable_comp_emb` for the translation,
`Integrable.comp_mul_left'` for the dilation). -/
lemma mti_integrable_shift_abs {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) :
    MeasureTheory.Integrable (fun x : ℝ => |lam (z * Real.exp (-(ε * x)))|) volume := by
  have hshift : MeasureTheory.Integrable (fun y : ℝ => lam (Real.exp (y + Real.log z))) volume := by
    have hmp : MeasureTheory.MeasurePreserving (fun y : ℝ => y + Real.log z) volume volume :=
      MeasureTheory.measurePreserving_add_right volume (Real.log z)
    have hemb : MeasurableEmbedding (fun y : ℝ => y + Real.log z) :=
      measurableEmbedding_addRight (Real.log z)
    exact (hmp.integrable_comp_emb hemb).mpr hint
  have hscale : MeasureTheory.Integrable (fun x : ℝ => lam (Real.exp ((-ε) * x + Real.log z)))
      volume :=
    hshift.comp_mul_left' (by linarith : (-ε) ≠ 0)
  have hfun : ∀ x : ℝ, lam (Real.exp ((-ε) * x + Real.log z)) = lam (z * Real.exp (-(ε * x))) := by
    intro x
    congr 1
    rw [show (-ε) * x + Real.log z = Real.log z - ε * x by ring, Real.exp_sub, Real.exp_log hz]
    rw [div_eq_mul_inv, Real.exp_neg]
  have hscale' : MeasureTheory.Integrable (fun x : ℝ => lam (z * Real.exp (-(ε * x)))) volume :=
    hscale.congr (Filter.Eventually.of_forall hfun)
  simpa only [Real.norm_eq_abs] using hscale'.norm

/-- **The transfer identity for the log-coordinate kernel.**  For an admissible mollifier kernel
`ρ` (`Work.FTS.StrongEps.IsMollKernel`: continuous, supported in the closed unit ball,
nonnegative, total mass one), `ε > 0`, `z > 0` and a measurable `lam` whose log-coordinate trace
is integrable,

  `∫ p, Jker ρ ε p * lam (z * exp (-p.1)) = ∫ s, (∫ t, ρ (s,t)) * lam (z * exp (-(ε * s)))`.

Route: the change of variables `p ↦ ε⁻¹ • p`
(`MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg`, unconditional), followed by Fubini on
the `s`-marginal of `ρ`.  The absolute convergence needed by Fubini follows from `hint`: `ρ` is
bounded and supported in the unit ball, so `|q₁| ≤ 1` on its support and
`∫_{|q₁| ≤ 1} |lam (z exp (-ε q₁))| dq₁ = ε⁻¹ ∫_{log z - ε}^{log z + ε} |lam (exp u)| du`.
The same identity with a *local bound* on `lam`, `hC : ∀ q, ρ q ≠ 0 → |lam (z exp (-ε q.1))| ≤ C`,
is already proved as `integral_Jker_mul_eq_marginal` in
`Submission/Work/FTS/StrongEps/EpsLocalPStar/JepsTraceTransfer.lean` — do NOT import that module
(it contains an unproved declaration); reproduce the argument with `hint` in place of `hC`.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem MarginalTransferIntegrable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) {lam : ℝ → ℝ} (hlamm : Measurable lam)
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u))) :
    (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
      = ∫ s : ℝ, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s))) := by
  classical
  -- a uniform bound for `ρ` on the unit ball (continuity + compact support)
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn
    hρ.cont.continuousOn
  set Cρ : ℝ := |C₀| with hCρdef
  have hCρnn : 0 ≤ Cρ := by rw [hCρdef]; exact abs_nonneg _
  have hCρ : ∀ q : ℝ × ℝ, q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 → ‖ρ q‖ ≤ Cρ :=
    fun q hq => (hC₀ q hq).trans (le_abs_self _)
  have hΛabs : MeasureTheory.Integrable (fun x : ℝ => |lam (z * Real.exp (-(ε * x)))|) volume :=
    mti_integrable_shift_abs hint hε hz
  -- the dominating function `Cρ * |lam (z exp (-ε q₁))|` is integrable over the unit square
  have hbox : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => Cρ * |lam (z * Real.exp (-(ε * q.1)))|)
      (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) volume := by
    have h1 : MeasureTheory.Integrable (fun x : ℝ => Cρ * |lam (z * Real.exp (-(ε * x)))|)
        (volume.restrict (Set.Icc (-1 : ℝ) 1)) := (hΛabs.const_mul Cρ).integrableOn
    have h2 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Set.Icc (-1 : ℝ) 1)) :=
      integrableOn_const (by simp)
    have h3 := h1.mul_prod h2
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at h3
    simpa only [MeasureTheory.IntegrableOn, mul_one] using h3
  have hsub : Metric.closedBall (0 : ℝ × ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro q hq
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hq
    have h1 : |q.1| ≤ 1 := by
      have h : ‖q.1‖ ≤ 1 := (le_max_left (‖q.1‖) (‖q.2‖)).trans hq
      simpa using h
    have h2 : |q.2| ≤ 1 := by
      have h : ‖q.2‖ ≤ 1 := (le_max_right (‖q.1‖) (‖q.2‖)).trans hq
      simpa using h
    exact ⟨by rw [Set.mem_Icc]; exact abs_le.mp h1, by rw [Set.mem_Icc]; exact abs_le.mp h2⟩
  have hball : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => Cρ * |lam (z * Real.exp (-(ε * q.1)))|)
      (Metric.closedBall (0 : ℝ × ℝ) 1) volume := hbox.mono_set hsub
  have hg : MeasureTheory.Integrable
      ((Metric.closedBall (0 : ℝ × ℝ) 1).indicator
        (fun q : ℝ × ℝ => Cρ * |lam (z * Real.exp (-(ε * q.1)))|)) volume :=
    hball.integrable_indicator Metric.isClosed_closedBall.measurableSet
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) volume :=
    hρ.cont.aestronglyMeasurable.mul (hlamm.comp (by fun_prop)).aestronglyMeasurable
  -- hence the `q`-integrand of the marginal is integrable
  have hGint : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) volume := by
    refine hg.mono' haesm ?_
    filter_upwards with q
    by_cases hq : ρ q = 0
    · rw [hq, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun a _ => mul_nonneg hCρnn (abs_nonneg _)) q
    · have hmem : q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := mti_mem_ball_of_support hρ hq
      rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa using hCρ q hmem) (abs_nonneg _)
  -- step 1: the change of variables `p ↦ ε⁻¹ • p` (unconditional)
  have hstep : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
      = ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
    let g : ℝ × ℝ → ℝ := fun q => ε⁻¹ ^ 2 * (ρ q * lam (z * Real.exp (-(ε * q.1))))
    have h1 : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
        = ∫ p : ℝ × ℝ, g (ε⁻¹ • p) := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      have hε1 : ε * (ε⁻¹ * p.1) = p.1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
      have hfst : (ε⁻¹ • p).1 = ε⁻¹ * p.1 := rfl
      simp only [Work.FTS.StrongEps.Jker, g, hfst, hε1]
      ring
    have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (μ := (volume : Measure (ℝ × ℝ))) g hε.le
    rw [show Module.finrank ℝ (ℝ × ℝ) = 2 from by simp [Module.finrank_prod],
      smul_eq_mul] at h2
    rw [h1, h2]
    have h3 : (∫ q : ℝ × ℝ, g q)
        = ε⁻¹ ^ 2 * ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
      simp only [g]
      rw [MeasureTheory.integral_const_mul]
    rw [h3]
    have h4 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hε.ne', one_pow]
    rw [← mul_assoc, h4, one_mul]
  -- step 2: Fubini on the `s`-marginal of `ρ`
  have hGint' : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] using hGint
  have hR : (∫ s, (∫ t, ρ (s, t)) * lam (z * Real.exp (-(ε * s))))
      = ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) := by
    have hinner : ∀ s : ℝ, (∫ t, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))
        = ∫ t, ρ (s, t) * lam (z * Real.exp (-(ε * s))) := fun s => by
      rw [MeasureTheory.integral_mul_const]
    simp only [hinner]
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact (MeasureTheory.integral_prod _ hGint').symm
  rw [hstep, hR]

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.hKerConstWlInf_l =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

set_option linter.unusedVariables false

/-- The quantitative half of `hKerConstWlInf_l`: for the radial profile `hKer` and an arbitrary
level `l`, the function `(z,θ) ↦ c·hKer z` lies in `𝒲^{l,∞}` and its norm is at most
`|c|·Σ_{k≤l} k!(k+1)`, uniformly in `α`.

All positive `D_θ`-iterates of a `θ`-independent function vanish identically, so the second
(angular) block of `WlInf` is `0` and only the `l+1` radial summands survive, each bounded by
`|c|·k!·(k+1)` (`Work.Spaces.pzIter_hKer_bound`). -/
theorem hKerConstWlInf_l_aux (l : ℕ) (α c : ℝ) :
    Work.Spaces.WlInfMem α l (fun z _ : ℝ => c * Work.Spaces.hKer z) ∧
      Work.Spaces.WlInf α l (fun z _ : ℝ => c * Work.Spaces.hKer z)
        ≤ |c| * (∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ) * (k + 1))) := by
  -- every positive `D_θ`-iterate of a `θ`-independent function vanishes
  have hDth : ∀ j : ℕ, Work.Spaces.DthIter (j + 1) (fun z θ => c * Work.Spaces.hKer z)
      = fun _ _ => (0 : ℝ) := by
    intro j
    induction j with
    | zero => funext z θ; simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    | succ j ih =>
        rw [show j + 1 + 1 = (j + 1) + 1 from rfl, Work.Spaces.DthIter_succ, ih]
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]
  have hpzIter0 : ∀ k : ℕ, Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]
  -- the pointwise bounds of the radial summands
  have hrad : ∀ k : ℕ, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ|
        ≤ |c| * ((k.factorial : ℝ) * (k + 1)) := by
    intro k z hz θ hθ
    rw [Work.Spaces.pzIter_decomp k (fun _ : ℝ => c) Work.Spaces.hKer z θ]
    rw [show (z + 1) ^ k * (c * deriv^[k] Work.Spaces.hKer z)
        = c * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Work.Spaces.pzIter_hKer_bound k z hz) (abs_nonneg c)
  have hmem : Work.Spaces.WlInfMem α l (fun z θ => c * Work.Spaces.hKer z) := by
    constructor
    · intro k hk
      exact ⟨|c| * ((k.factorial : ℝ) * (k + 1)), fun y hy => by
        rcases hy with ⟨z, hz, θ, hθ, rfl⟩
        exact hrad k z hz θ hθ⟩
    · intro j hj k hk hj1 hjk
      have hDj : Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z) = fun _ _ => (0 : ℝ) := by
        rw [← Nat.sub_add_cancel hj1]
        exact hDth (j - 1)
      refine ⟨0, fun y hy => ?_⟩
      rcases hy with ⟨z, hz', θ, hθ, rfl⟩
      simp only []
      rw [hDj]
      have h0 : Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
        congrFun (congrFun (hpzIter0 k) z) θ
      rw [h0, mul_zero, zero_mul, zero_div, abs_zero]
  refine ⟨hmem, ?_⟩
  rw [Work.Spaces.WlInf]
  have h1 : (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
      (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ))
      ≤ ∑ k ∈ Finset.range (l + 1), (|c| * ((k.factorial : ℝ) * (k + 1))) :=
    Finset.sum_le_sum fun k _ => Work.Spaces.supAbs_le (hrad k)
  have h2 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
      if 1 ≤ j ∧ k + j ≤ l then Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0) ≤ 0 := by
    refine Finset.sum_nonpos (fun j _ => Finset.sum_nonpos (fun k _ => ?_))
    by_cases hc : 1 ≤ j ∧ k + j ≤ l
    · rw [if_pos hc]
      refine Work.Spaces.supAbs_le (fun z hz' θ hθ => ?_)
      have hDj : Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z) = fun _ _ => (0 : ℝ) := by
        rw [← Nat.sub_add_cancel hc.1]
        exact hDth (j - 1)
      rw [hDj]
      have h0 : Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
        congrFun (congrFun (hpzIter0 k) z) θ
      rw [h0, mul_zero, zero_mul, zero_div, abs_zero]
    · rw [if_neg hc]
  calc (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
          (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ))
        + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then Work.Spaces.supAbs
              (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
                  (Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)
      ≤ (∑ k ∈ Finset.range (l + 1), (|c| * ((k.factorial : ℝ) * (k + 1)))) + 0 := add_le_add h1 h2
    _ = |c| * (∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ) * (k + 1))) := by
        rw [add_zero, Finset.mul_sum]

/-- The `𝒲^{l,∞}`-norm of a constant multiple of the radial profile `hKer(z) = z/(1+z)²`, at an
*arbitrary* level `l`: `(z,θ) ↦ c·hKer z` is `θ`-independent, so all its positive `D_θ`-iterates
vanish identically and only the `l+1` radial summands `sup |(z+1)^k hKer^{(k)}|` survive, each
bounded by `|c|·k!·(k+1)` (`Work.Spaces.pzIter_hKer_bound`).  Hence
`WlInfMem α l (fun z _ => c * hKer z)` and `WlInf α l (fun z _ => c * hKer z) ≤ C_l·|c|` with
`C_l = Σ_{k≤l} k!(k+1)`, for every `α` and every `c` (no `α`-dependence at all).

This is the level-`l` version of the proved `Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf`
(the case `l = 4`, constant `200`). -/
theorem hKerConstWlInf_l (l : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α c : ℝ),
    Work.Spaces.WlInfMem α l (fun z _ : ℝ => c * Work.Spaces.hKer z) ∧
      Work.Spaces.WlInf α l (fun z _ : ℝ => c * Work.Spaces.hKer z) ≤ C * |c| := by
  refine ⟨max 1 (∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ) * (k + 1))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun α c => ?_⟩
  obtain ⟨hmem, hb⟩ := hKerConstWlInf_l_aux l α c
  refine ⟨hmem, le_trans hb ?_⟩
  rw [mul_comm |c| (∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ) * (k + 1)))]
  exact mul_le_mul_of_nonneg_right (le_max_right 1 _) (abs_nonneg c)

end Work.FTS.StrongEps.H5
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.Defs =====
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


/-- The derivative `ζ ↦ e^ζ / (1 + e^{2ζ})` of the map `ζ ↦ arctan (e^ζ)`. -/
def kappa (ζ : ℝ) : ℝ := Real.exp ζ / (1 + Real.exp (2 * ζ))

/-- The Jacobian factor `e^s · (arctan ∘ exp)'(ζ) = e^s · kappa ζ` of the log-coordinate
substitution. -/
def logJac (s ζ : ℝ) : ℝ := Real.exp s * kappa ζ

theorem kappa_pos (ζ : ℝ) : 0 < kappa ζ := by
  rw [kappa]
  positivity

theorem kappa_nonneg (ζ : ℝ) : 0 ≤ kappa ζ := (kappa_pos ζ).le

theorem logJac_pos (s ζ : ℝ) : 0 < logJac s ζ := by
  rw [logJac]
  exact mul_pos (Real.exp_pos s) (kappa_pos ζ)

theorem logJac_nonneg (s ζ : ℝ) : 0 ≤ logJac s ζ := (logJac_pos s ζ).le


/-- The range of `ζ ↦ arctan (e^ζ)` is the open interval `(0, π/2)`. -/
theorem range_arctan_exp : (fun ζ : ℝ => Real.arctan (Real.exp ζ)) '' Set.univ
    = Set.Ioo 0 (π / 2) := by
  ext θ
  constructor
  · rintro ⟨ζ, -, rfl⟩
    exact ⟨Real.arctan_pos.2 (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩
  · intro hθ
    refine ⟨Real.log (Real.tan θ), trivial, ?_⟩
    have hpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
    have hlt : -(π / 2) < θ := by linarith [hθ.1, Real.pi_pos]
    show Real.arctan (Real.exp (Real.log (Real.tan θ))) = θ
    rw [Real.exp_log hpos, Real.arctan_tan hlt hθ.2]

/-- The range of `Real.exp` is `(0, ∞)`. -/
theorem range_exp : Real.exp '' Set.univ = Set.Ioi (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨s, -, rfl⟩
    exact Real.exp_pos s
  · intro hx
    exact ⟨Real.log x, trivial, Real.exp_log hx⟩


end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_pair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

open Work.FTS.StrongEps
open Work.Spaces

/-! ## Elementary facts about `Jker`, the shifts and the quadrant -/

/-- `Jker ρ ε` is continuous as soon as `ρ` is: no support/mass hypothesis is needed here. -/
private lemma continuous_Jker_of_continuous (ρ : ℝ × ℝ → ℝ) (hρc : Continuous ρ) (ε : ℝ) :
    Continuous (Jker ρ ε) := by
  have h : Jker ρ ε = fun p : ℝ × ℝ => ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) := by
    funext p; simp only [Jker]
  rw [h]
  exact continuous_const.mul (hρc.comp (continuous_const_smul ε⁻¹))

/-- On the quadrant, `cos` does not vanish, so `tan` is continuous there. -/
private lemma cos_ne_zero_of_mem_quad {q : (ℝ × ℝ) × (ℝ × ℝ)} (hq : q.1 ∈ Quad) :
    Real.cos q.1.2 ≠ 0 := by
  have h2 : q.1.2 ∈ Set.Ioo 0 (π / 2) := hq.2
  exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h2.1], h2.2⟩).ne'

/-- The `θ`-shift map is continuous on the set of base points in the quadrant
(the monotone `tan` factor is harmless there because `cos ≠ 0`). -/
private lemma continuousOn_tan_quad :
    ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => Real.tan q.1.2) {q | q.1 ∈ Quad} :=
  Real.continuousOn_tan.comp (by fun_prop) (fun q hq => cos_ne_zero_of_mem_quad hq)

/-- The `θ`-shift is continuous on the set of base points in the quadrant. -/
private lemma continuousOn_thShift_quad :
    ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => thShift q.1.2 q.2.2) {q | q.1 ∈ Quad} := by
  have h1 : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.tan q.1.2 * Real.exp (-q.2.2)) {q | q.1 ∈ Quad} :=
    continuousOn_tan_quad.mul (Real.continuous_exp.comp_continuousOn (by fun_prop))
  have := Real.continuous_arctan.comp_continuousOn h1
  simpa only [thShift, Function.comp_def] using this

/-- The pair of shifts is continuous on the set of base points in the quadrant. -/
private lemma continuousOn_shift_quad :
    ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (zShift q.1.1 q.2.1, thShift q.1.2 q.2.2)) {q | q.1 ∈ Quad} := by
  refine ContinuousOn.prodMk ?_ continuousOn_thShift_quad
  simp only [zShift]
  fun_prop

/-- The shifted point of a base point of the quadrant lies again in the quadrant. -/
private lemma shift_mem_Quad {q : (ℝ × ℝ) × (ℝ × ℝ)} (hq : q.1 ∈ Quad) :
    (zShift q.1.1 q.2.1, thShift q.1.2 q.2.2) ∈ Quad :=
  ⟨zShift_pos hq.1, thShift_mem hq.2⟩

/-! ## The two null sets of the boundary -/

/-- `z = 0` is null for `volume.restrict Iz` with `Iz = [0, ∞)`. -/
private lemma measure_Iz_compl_Ioi : (volume.restrict Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioi.compl]
  refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
  intro x hx
  simp only [Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Ioi,
    Set.mem_singleton_iff] at hx ⊢
  exact le_antisymm (not_lt.mp hx.1) hx.2

/-- `θ = 0` and `θ = π/2` are null for `volume.restrict Iθ` with `Iθ = [0, π/2]`. -/
private lemma measure_Iθ_compl_Ioo : (volume.restrict Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  have h0 : (volume : Measure ℝ) ({0} ∪ {π / 2}) = 0 :=
    measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
  refine measure_mono_null ?_ h0
  intro x hx
  simp only [Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
    Set.mem_union, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨hxn, hxI⟩ := hx
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rcases lt_or_ge x (π / 2) with h2 | h2
    · exact absurd ⟨h, h2⟩ hxn
    · exact Or.inr (le_antisymm hxI.2 h2)
  · exact Or.inl (le_antisymm h hxI.1)

/-- The complement of the quadrant is null for `(volume.restrict Iz).prod (volume.restrict Iθ)`:
it is contained in the union of the two coordinate hyperplanes. -/
private lemma measure_quad_compl :
    (volume.restrict Iz).prod (volume.restrict Iθ) Quadᶜ = 0 := by
  have hsub : Quadᶜ ⊆ (Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ := by
    intro x hx
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and] at hx ⊢
    tauto
  have h1 : (volume.restrict Iz).prod (volume.restrict Iθ)
      ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
        (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) = 0 := by
    rw [measure_union_null_iff]
    constructor
    · rw [Measure.prod_prod, measure_Iz_compl_Ioi, zero_mul]
    · rw [Measure.prod_prod, measure_Iθ_compl_Ioo, mul_zero]
  exact measure_mono_null hsub h1

/-- The set of pairs whose base point is *not* in the quadrant is null for the full
three-dimensional measure `((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume`. -/
private lemma measure_compl_quad_prod :
    (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume)
      ({q : (ℝ × ℝ) × (ℝ × ℝ) | q.1 ∈ Quad}ᶜ) = 0 := by
  have hset : ({q : (ℝ × ℝ) × (ℝ × ℝ) | q.1 ∈ Quad}ᶜ : Set ((ℝ × ℝ) × (ℝ × ℝ))) =
      Quadᶜ ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
  rw [hset, Measure.prod_prod, measure_quad_compl]
  simp

/-! ## The target -/

theorem aemeasurable_shift_pair {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun q : ℝ × ℝ => G q.1 q.2) Work.FTS.StrongEps.Quad)
    (ρ : ℝ × ℝ → ℝ) (hρc : Continuous ρ) (ε : ℝ) :
    AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Work.FTS.StrongEps.Jker ρ ε q.2) *
          ENNReal.ofReal (G (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
            (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
  classical
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {q | q.1 ∈ Quad} with hSdef
  -- `S` is the (measurable) set of base points in the quadrant, and it is conull.
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact ((isOpen_Ioi.prod isOpen_Ioo).preimage continuous_fst).measurableSet
  have hnull : (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) Sᶜ = 0 := by
    rw [hSdef]
    exact measure_compl_quad_prod
  -- On `S` the composed profile is continuous.
  have hcont : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)) S := by
    rw [hSdef]
    exact hG.comp continuousOn_shift_quad (fun q hq => shift_mem_Quad hq)
  have hA : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2))
      (Measure.restrict (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) S) :=
    hcont.aemeasurable hSmeas
  -- Multiplication by the indicator of `S`, and removal of the indicator with the conullity.
  have hind : AEMeasurable (S.indicator (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)))
      (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  have hcongr : (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)) =ᵐ[
        (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume)]
      S.indicator (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)) := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
    simp only [Set.mem_compl_iff, not_not] at hq
    exact (Set.indicator_of_mem hq (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2))).symm
  have hGae : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2))
      (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) :=
    hind.congr hcongr.symm
  -- `ENNReal.ofReal` preserves a.e. measurability, as does the pointwise product.
  have hGenn : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (G (zShift q.1.1 q.2.1) (thShift q.1.2 q.2.2)))
      (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hGae
  have hJnn : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Jker ρ ε q.2))
      (((volume.restrict Iz).prod (volume.restrict Iθ)).prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuous_Jker_of_continuous ρ hρc ε).comp continuous_snd).aemeasurable)
  exact hJnn.mul hGenn

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le =====
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

/-! ## The abstract weighted Cauchy–Schwarz inequality -/

/-- **Cauchy–Schwarz (completed–square form) for a probability density.**  If `k` is a
nonnegative integrable function of total mass `1`, and `k A`, `k A²` are integrable, then
`(∫ k A)² ≤ ∫ k A²`.

The proof expands `∫ k (A - m)² ≥ 0` for `m := ∫ k A`. -/
theorem sq_integral_mul_le_of_prob {α : Type*} [MeasurableSpace α] {μ : Measure α} {k A : α → ℝ}
    (hk_nn : ∀ p, 0 ≤ k p) (hk_int : Integrable k μ)
    (hA_int : Integrable (fun p => k p * A p) μ)
    (hA2_int : Integrable (fun p => k p * (A p) ^ 2) μ)
    (hk_mass : ∫ p, k p ∂μ = 1) :
    (∫ p, k p * A p ∂μ) ^ 2 ≤ ∫ p, k p * (A p) ^ 2 ∂μ := by
  set m : ℝ := ∫ p, k p * A p ∂μ with hm
  have hsq : 0 ≤ ∫ p, k p * (A p - m) ^ 2 ∂μ :=
    integral_nonneg fun p => mul_nonneg (hk_nn p) (sq_nonneg _)
  have hexp : ∫ p, k p * (A p - m) ^ 2 ∂μ
      = (∫ p, k p * (A p) ^ 2 ∂μ) - m ^ 2 := by
    have hI1 : Integrable (fun p => k p * (A p) ^ 2 - (2 * m) * (k p * A p)) μ :=
      hA2_int.sub (hA_int.const_mul (2 * m))
    have hI2 : Integrable (fun p => m ^ 2 * k p) μ := hk_int.const_mul (m ^ 2)
    calc ∫ p, k p * (A p - m) ^ 2 ∂μ
        = ∫ p, (k p * (A p) ^ 2 - (2 * m) * (k p * A p)) + m ^ 2 * k p ∂μ :=
          integral_congr_ae (Eventually.of_forall fun p => by ring)
      _ = (∫ p, k p * (A p) ^ 2 - (2 * m) * (k p * A p) ∂μ) + ∫ p, m ^ 2 * k p ∂μ := by
          rw [integral_add hI1 hI2]
      _ = ((∫ p, k p * (A p) ^ 2 ∂μ) - ∫ p, (2 * m) * (k p * A p) ∂μ)
            + ∫ p, m ^ 2 * k p ∂μ := by
          rw [integral_sub hA2_int (hA_int.const_mul (2 * m))]
      _ = ((∫ p, k p * (A p) ^ 2 ∂μ) - (2 * m) * ∫ p, k p * A p ∂μ)
            + m ^ 2 * ∫ p, k p ∂μ := by
          rw [integral_const_mul, integral_const_mul]
      _ = (∫ p, k p * (A p) ^ 2 ∂μ) - m ^ 2 := by
          rw [← hm, hk_mass]; ring
  linarith

/-! ## Integrability of `Jker ρ ε * A` for `A` continuous on the ball -/

/-- **Global integrability of a kernel–test-function product.**  If `A` is continuous on the
closed ball of radius `ε`, then `p ↦ Jker ρ ε p * A p` is integrable on all of `ℝ²`: it is
integrable on the ball by compactness, and it vanishes off the ball since the kernel does. -/
theorem integrable_Jker_mul (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {A : ℝ × ℝ → ℝ} (hA : ContinuousOn A (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => Jker ρ ε p * A p) :=
  (integrableOn_Jker_mul_ball hρ hε hA).integrable_of_forall_notMem_eq_zero
    (fun p hp => by rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])

/-- The kernel is nonnegative. -/
theorem Jker_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) (ε : ℝ) :
    ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p :=
  fun _ => mul_nonneg (sq_nonneg _) (hρ.nonneg _)

/-! ## The estimate -/

theorem sq_integral_Jker_mul_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * g p) ^ 2
      ≤ ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * (g p) ^ 2 :=
  sq_integral_mul_le_of_prob (μ := volume) (k := fun p : ℝ × ℝ => Jker ρ ε p) (A := g)
    (Jker_nonneg ρ hρ ε) (Jker_integrable hρ hε)
    (integrable_Jker_mul ρ hρ hε hg)
    (integrable_Jker_mul ρ hρ hε (hg.pow 2))
    (Jker_integral_eq_one ρ hρ hε)

end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSq_four_le_of_conv =====
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
set_option maxHeartbeats 800000

/-- **The `ℋ⁴`-energy of the limit is bounded by the uniform bound of the sequence.**  From the
slotwise locally uniform convergence of the `ConvLocUnifH6`-package (`Q0`-compactness, no bound on
the boundary behaviour of the approximants is needed), the `ℋ⁴`-membership and the uniform
`ℋ⁴`-bound of the sequence, the limit `f` satisfies `HkSq α 4 f ≤ B4`.

Proof: Fatou's lemma, twice (see the module documentation). -/
theorem HkSq_four_le_of_conv {α B B4 : ℝ} {G : ℕ → Work.FTS.Galerkin.Fn}
    {f : Work.FTS.Galerkin.Fn}
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B G f)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 4 (G n))
    (hbsq : ∀ n : ℕ, Work.Spaces.HkSq α 4 (G n) ≤ B4) :
    Work.Spaces.HkSq α 4 f ≤ B4 := by
  -- `B4` dominates the nonnegative energy `HkSq α 4 (G 0)`
  have hB4 : 0 ≤ B4 := le_trans (Work.Spaces.HkSq_nonneg α 4 (G 0)) (hbsq 0)
  -- the slotwise convergence is pointwise on the open quadrant: a singleton is compact
  have hslot : ∀ (j i : ℕ), j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (G n) z θ) atTop
        (nhds (Work.Spaces.mixed j i f z θ)) := by
    intro j i hji z θ hzθ
    have hK : IsCompact ({(z, θ)} : Set (ℝ × ℝ)) := isCompact_singleton
    have hsub : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact hzθ
    exact (hconv.1 _ hK hsub j i hji).tendsto_at (Set.mem_singleton _)
  -- **the angular Fatou step**: for every `z ∈ Iz` the `θ`-slice of the integrand of `f` is
  -- dominated in `lintegral` by the `liminf` of the slices of the approximants
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ))
        ≤ Filter.liminf (fun n : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop := by
    intro z hz
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | hz0
    · -- `z > 0`: the comparison holds for a.e. `θ`, and Fatou's lemma applies
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ)
            ≤ Filter.liminf (fun n : ℕ =>
                ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop := by
        -- it suffices to test the open interval, the two endpoints being null
        have hμ : MeasureTheory.volume.restrict Work.Spaces.Iθ
            = MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)) :=
          (MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
              (b := (π/2)))).symm
        rw [hμ]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
        -- pointwise convergence of the integrands, hence `liminf = HkIntegrand α 4 f`
        have hlim : Filter.liminf (fun n : ℕ => Work.Spaces.HkIntegrand α 4 (G n) z θ)
            Filter.atTop = Work.Spaces.HkIntegrand α 4 f z θ :=
          (Work.FTS.StrongEps.HkIntegrand_tendsto_of_mixed (α := α) (k := 4) (F := f) (Fs := G)
            (z := z) (θ := θ) (fun j i hji => hslot j i hji z θ
              (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩))).liminf_eq
        exact Work.FTS.EllExist.Honesty.ofReal_le_liminf_ofReal
          (fun n => Work.Spaces.HkIntegrand_nonneg α 4 (G n) z θ) (le_of_eq hlim.symm)
      refine le_trans (MeasureTheory.lintegral_mono_ae hae) ?_
      exact MeasureTheory.lintegral_liminf_le'
        (fun n => (((hmem n).1 z hz).aemeasurable).ennreal_ofReal)
    · -- `z = 0` (or `z < 0`): both sides degenerate, the integrand vanishing at `z = 0`
      subst hz0
      have hzero : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f 0 θ)) = 0 := by
        simp [Work.Spaces.HkIntegrand_zero_z]
      rw [hzero]
      exact zero_le
  -- **the outer Fatou step**
  have hstep1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun n : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop :=
    MeasureTheory.lintegral_mono_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hslice)
  have hstep2 : (∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun n : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop)
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop :=
    MeasureTheory.lintegral_liminf_le' (fun n => by
      -- the `z`-function `∫⁻_θ ofReal (HkIntegrand α 4 (G n) z θ)` is measurable, being the
      -- `ofReal`-image of the (integrable) angular integral of `HkIntegrand α 4 (G n)`
      have h1 : AEMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (G n) z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        ((hmem n).2).aemeasurable
      refine (h1.ennreal_ofReal).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n).1 z hz)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 (G n) z θ))
  -- the double `lintegral` of an approximant is `ofReal` of its energy
  have hEq : ∀ n : ℕ, (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 4 (G n)) := by
    intro n
    have h1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ))
        = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (G n) z θ) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n).1 z hz)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 (G n) z θ)).symm
    rw [h1, Work.Spaces.HkSq]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n).2)
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 (G n) z θ)).symm
  -- the `liminf` of a sequence bounded by `ofReal B4` is bounded by `ofReal B4`
  have hliminf_le : Filter.liminf (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
        ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop
      ≤ ENNReal.ofReal B4 := by
    refine Filter.liminf_le_of_le ⟨0, ?_⟩ ?_
    · rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall fun n => zero_le
    · intro b hb
      obtain ⟨n, hn⟩ := hb.exists
      exact le_trans (hEq n ▸ hn) (ENNReal.ofReal_le_ofReal (hbsq n))
  have hmain : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ)) ≤ ENNReal.ofReal B4 :=
    le_trans hstep1 (le_trans hstep2 hliminf_le)
  -- **comparison of the Bochner integral with the double `lintegral`**
  by_cases hint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iz
  · have h1 : Work.Spaces.HkSq α 4 f = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)).toReal := by
      rw [Work.Spaces.HkSq]
      exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hint.aestronglyMeasurable
    have hpt : ∀ z : ℝ, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ) := by
      intro z
      by_cases hz : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iθ
      · exact le_of_eq (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hz
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
      · rw [MeasureTheory.integral_undef hz]; simp
    rw [h1]
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)).toReal
        ≤ (ENNReal.ofReal B4).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top
            ((MeasureTheory.lintegral_mono hpt).trans hmain)
      _ = B4 := ENNReal.toReal_ofReal hB4
  · -- the energy is the junk value `0`, and `B4` is nonnegative
    have h0 : Work.Spaces.HkSq α 4 f = 0 := by
      rw [Work.Spaces.HkSq]
      exact MeasureTheory.integral_undef hint
    rw [h0]
    exact hB4

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsBasic =====
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



/-- **`J_ε` is dominated by the sup over the shifted region**: the exact form in which the
mollified quantities are bounded in the limit arguments (`E5`). -/
theorem abs_Jeps_le_sup (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : Fn} {z θ M : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hM : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε → |f (zShift z p.1) (thShift θ p.2)| ≤ M)
    (hM0 : 0 ≤ M) :
    |Jeps ρ ε f z θ| ≤ M := by
  rw [Jeps_eq_integral ρ ε _ hz hθ]
  have hknn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := by
    intro p; simp only [Jker]; exact mul_nonneg (by positivity) (hρ.nonneg _)
  have hpt : ∀ᵐ p ∂volume,
      ‖Jker ρ ε p * f (zShift z p.1) (thShift θ p.2)‖ ≤ Jker ρ ε p * M := by
    refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · have hp' : max |p.1| |p.2| ≤ ε := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
          using hp
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hknn p)]
      exact mul_le_mul_of_nonneg_left
        (hM p (le_trans (le_max_left _ _) hp') (le_trans (le_max_right _ _) hp')) (hknn p)
    · rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul, norm_zero, zero_mul]
  by_cases hint : Integrable (fun p : ℝ × ℝ => Jker ρ ε p * f (zShift z p.1) (thShift θ p.2))
  · have hmaj : Integrable (fun p : ℝ × ℝ => Jker ρ ε p * M) :=
      (Jker_integrable hρ hε).mul_const M
    calc |∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ p.2)|
        ≤ ∫ p : ℝ × ℝ, ‖Jker ρ ε p * f (zShift z p.1) (thShift θ p.2)‖ :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p * M := MeasureTheory.integral_mono_ae hint.norm hmaj hpt
      _ = M := by
          rw [show (fun p : ℝ × ℝ => Jker ρ ε p * M) = fun p => M * Jker ρ ε p from
            funext fun p => mul_comm _ _]
          rw [MeasureTheory.integral_const_mul, Jker_integral_eq_one ρ hρ hε, mul_one]
  · rw [MeasureTheory.integral_undef hint, abs_zero]
    exact hM0

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsHkMem.Jker_comp_zShift_lt_top =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.JepsHkMem

open MeasureTheory Set

set_option maxHeartbeats 800000

/-- **The one-dimensional substitution `u = z * exp (-x)` on `[-ε, ε]`.**  For any
`G : ℝ → ℝ≥0∞` (no measurability needed) and `ε, z > 0`,

  `∫⁻ x in Icc (-ε) ε, G (z * exp (-x)) ≤ (exp ε / z) * ∫⁻ u in Ioi 0, G u`.

The constant is the inverse of the pointwise lower bound `z * exp (-ε)` of the stretching factor
`|d/dx (z exp (-x))| = z exp (-x)`. -/
private lemma lintegral_Icc_expNeg_le {G : ℝ → ENNReal} {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) :
    (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
  have hzε : 0 < z * Real.exp (-ε) := mul_pos hz (Real.exp_pos _)
  -- the derivative of the substitution
  have hderiv : ∀ x ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x)))
        (Set.Icc (-ε) ε) x := by
    intro x _
    have h' : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      simpa using h1
    have h2 : HasDerivAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x))) x := by
      have h3 := h'.const_mul z
      simpa using h3
    exact h2.hasDerivWithinAt
  -- the substitution is injective
  have hinj : Set.InjOn (fun x : ℝ => z * Real.exp (-x)) (Set.Icc (-ε) ε) := by
    intro x _ y _ hxy
    have hexp : Real.exp (-x) = Real.exp (-y) := mul_left_cancel₀ hz.ne' hxy
    have h2 : -x = -y := Real.exp_injective hexp
    linarith
  have hkey := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.Icc (-ε) ε) (f := fun x : ℝ => z * Real.exp (-x))
    (f' := fun x : ℝ => -(z * Real.exp (-x))) measurableSet_Icc hderiv hinj G
  have himage_sub : (fun x : ℝ => z * Real.exp (-x)) '' Set.Icc (-ε) ε ⊆ Set.Ioi 0 := by
    rintro u ⟨x, _, rfl⟩
    exact mul_pos hz (Real.exp_pos _)
  have hpt : ∀ x : ℝ, ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x))
      = ENNReal.ofReal (z * Real.exp (-x)) * G (z * Real.exp (-x)) := by
    intro x
    rw [abs_neg, abs_of_pos (mul_pos hz (Real.exp_pos _))]
  have h1 : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ x in Set.Icc (-ε) ε,
          ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (z * Real.exp (-ε)))
      (fun x => G (z * Real.exp (-x))) ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc ?_
    intro x hx
    rw [hpt x]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hx.2])) hz.le)
  have h2 : (∫⁻ x in Set.Icc (-ε) ε,
        ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := by
    rw [← hkey]
    exact lintegral_mono_set himage_sub
  have hfin' : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := le_trans h1 h2
  have hne0 : ENNReal.ofReal (z * Real.exp (-ε)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hzε
  have hneTop : ENNReal.ofReal (z * Real.exp (-ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstep : (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u := by
    calc (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
        = 1 * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := (one_mul _).symm
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ENNReal.ofReal (z * Real.exp (-ε))
            * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := by
          rw [ENNReal.inv_mul_cancel hne0 hneTop]
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ *
            (ENNReal.ofReal (z * Real.exp (-ε))
              * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))) := by
          rw [mul_assoc]
      _ ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u :=
          mul_le_mul_of_nonneg_left hfin' zero_le
  have hreal : (z * Real.exp (-ε))⁻¹ = Real.exp ε / z := by
    rw [Real.exp_neg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hconst_eq : (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ = ENNReal.ofReal (Real.exp ε / z) := by
    rw [← ENNReal.ofReal_inv_of_pos hzε, hreal]
  rwa [hconst_eq] at hstep

theorem Jker_comp_zShift_lt_top {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) {G : ℝ → ENNReal}
    (hmeas : AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume)
    (hfin : (∫⁻ z' in Set.Ioi 0, G z') < ⊤) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker ρ ε p)
      * G (z * Real.exp (-(p.1)))) < ⊤ := by
  set s : Set ℝ := Set.Icc (-ε) ε with hs
  set Φ : ℝ × ℝ → ENNReal := fun p => G (z * Real.exp (-(p.1))) with hΦ
  have hΦa : ∀ p : ℝ × ℝ, Φ p = G (z * Real.exp (-(p.1))) := fun p => by simp only [hΦ]
  -- the kernel is bounded on its compact support
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ × ℝ) ε).exists_bound_of_continuousOn
    (Jker_continuous hρ ε).continuousOn
  have hJle : ∀ p : ℝ × ℝ, Jker ρ ε p ≤ max C 0 := by
    intro p
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · have h := hC p hp
      rw [Real.norm_eq_abs] at h
      exact le_trans (le_abs_self _) (le_trans h (le_max_left _ _))
    · rw [Jker_eq_zero_of_not_mem hρ hε hp]
      exact le_max_right _ _
  -- (1) replace the kernel by its supremum on the ball
  have hstep1 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p)
      ≤ ENNReal.ofReal (max C 0) * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := by
    have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p
        ≤ ENNReal.ofReal (max C 0) * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p := by
      intro p
      by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
      · rw [indicator_of_mem hp]
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hJle p)) zero_le
      · rw [indicator_of_notMem hp, Jker_eq_zero_of_not_mem hρ hε hp]
        simp
    calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p)
        ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max C 0)
            * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p := lintegral_mono hpt
      _ = ENNReal.ofReal (max C 0)
            * ∫⁻ p : ℝ × ℝ, (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (max C 0) * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := by
          rw [lintegral_indicator (Metric.isClosed_closedBall.measurableSet) Φ]
  -- (2) the ball sits inside the square `s ×ˢ s`
  have hball_sub : Metric.closedBall (0 : ℝ × ℝ) ε ⊆ s ×ˢ s := by
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hp
    have hp' : max |p.1| |p.2| ≤ ε := by simpa only [Real.norm_eq_abs] using hp
    have h1 : |p.1| ≤ ε := le_trans (le_max_left _ _) hp'
    have h2 : |p.2| ≤ ε := le_trans (le_max_right _ _) hp'
    rw [hs]
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have hstep2 : (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p) ≤ ∫⁻ p in s ×ˢ s, Φ p :=
    lintegral_mono_set hball_sub
  -- (3) pass to the product of the two restricted lines
  have hstep3 : (∫⁻ p in s ×ˢ s, Φ p)
      = ∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)) := by
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_restrict]
  -- (4) Tonelli's inequality
  have hstep4 : (∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)))
      ≤ ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) := lintegral_prod_le Φ
  -- (5) the `p₂`-integration contributes only the length `2ε`
  have hinner : ∀ x : ℝ, (∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) := by
    intro x
    have hpt : ∀ y : ℝ, Φ (x, y) = G (z * Real.exp (-x)) := by
      intro y
      rw [hΦa]
    rw [show (∫⁻ y in s, Φ (x, y)) = ∫⁻ y in s, G (z * Real.exp (-x)) from
      lintegral_congr (fun y => hpt y)]
    rw [setLIntegral_const, hs, Real.volume_Icc]
    have : (ε : ℝ) - -ε = 2 * ε := by ring
    rw [this]
    exact mul_comm _ _
  have hstep5 : (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x)) := by
    rw [show (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
        = ∫⁻ x in s, ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) from
      lintegral_congr (fun x => hinner x)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (6) the one-dimensional substitution
  have hstep6 : (∫⁻ x in s, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
    simpa only [hs] using lintegral_Icc_expNeg_le (G := G) hε hz
  -- the goal, rewritten in terms of `Φ`
  have hstart : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p)
      = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * G (z * Real.exp (-(p.1)))) :=
    lintegral_congr (fun p => by rw [hΦa p])
  have hK : ENNReal.ofReal (max C 0) * (ENNReal.ofReal (2 * ε)
      * (ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u)) < ⊤ := by
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) ?_
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) ?_
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) hfin
  rw [← hstart]
  refine lt_of_le_of_lt ?_ hK
  calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p)
      ≤ ENNReal.ofReal (max C 0) * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := hstep1
    _ ≤ ENNReal.ofReal (max C 0) * ∫⁻ p in s ×ˢ s, Φ p :=
        mul_le_mul_of_nonneg_left hstep2 zero_le
    _ = ENNReal.ofReal (max C 0)
          * ∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)) := by rw [hstep3]
    _ ≤ ENNReal.ofReal (max C 0) * ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) :=
        mul_le_mul_of_nonneg_left hstep4 zero_le
    _ = ENNReal.ofReal (max C 0)
          * (ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x))) := by rw [hstep5]
    _ ≤ ENNReal.ofReal (max C 0) * (ENNReal.ofReal (2 * ε)
          * (ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep6 zero_le) zero_le

end Work.FTS.StrongEps.JepsHkMem
end
-- ===== merged: Submission.Work.FTS.StrongEps.Jeps_tendsto =====
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
set_option maxHeartbeats 800000

/-! ## The shift `Φ` of the mollifier and its inverse `Ψ` -/

/-- The shift `p ↦ (z e^{-p₁}, arctan (tan θ · e^{-p₂}))` defining the point at which the profile
is evaluated in `Jeps`. -/
def sPhi (z θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (zShift z p.1, thShift θ p.2)



theorem continuous_sPhi (z θ : ℝ) : Continuous (sPhi z θ) :=
  continuous_shift_pair z θ

theorem sPhi_zero {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : sPhi z θ 0 = (z, θ) := by
  refine Prod.ext ?_ ?_
  · simp only [sPhi, zShift, Prod.fst_zero, neg_zero, Real.exp_zero, mul_one]
  · simp only [sPhi, thShift, Prod.snd_zero, neg_zero, Real.exp_zero, mul_one]
    exact Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2


/-! ## `Ψ ∘ Φ = id` -/


/-! ## Differentiability of `Ψ` -/


/-! ## `Φ` is quasi-measure-preserving -/


/-! ## The peak-function argument in the `p`-coordinates -/


/-! ## The target -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.integrableOn_L12dens_bump =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.PZeroAux

open MeasureTheory

/-- The angular density of `bump`, `s ↦ ∫_θ K θ · bump s θ / s`, is integrable on `(0, ∞)`.

Equivalently: `L₁₂(bump)` is absolutely convergent, so that `L₁₂` is an honest integral of
`bump` and the projection `Pz` is linear on `bump` (`pzNorm_pos`,
`PZeroAux/PzNormPos.lean`). -/
theorem integrableOn_L12dens_bump :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s)
      (Set.Ioi 0) := by
  -- The two integrands agree pointwise: `L12dens K bump s = ∫_θ KB s θ` and the set integral
  -- over `Iθ` involves the same body (`KB`), which vanishes off `Iθ`.
  have hfun : (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s)
      = fun s : ℝ => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s := by
    funext s
    rw [PzNormAux.L12dens_eq s]
    rw [show (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s)
        = (fun θ : ℝ => PzNormAux.KB s θ) from rfl]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun θ hθ => PzNormAux.KB_eq_zero_of_not_mem_Iθ hθ)
  rw [hfun]
  exact PzNormAux.integrableOn_L12dens

end Work.FTS.StrongEps.PZeroAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.Jker_moment_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

/-- A continuous function supported in the closed unit ball of `ℝ × ℝ`, multiplied by
`exp (c * (|t.1| + |t.2|))`, is integrable: it is continuous and compactly supported. -/
private lemma integrable_sigma_exp (σ : ℝ × ℝ → ℝ) (hσc : Continuous σ)
    (hσsupp : ∀ p : ℝ × ℝ, σ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1) (c : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ × ℝ => σ t * Real.exp (c * (|t.1| + |t.2|))) := by
  have hexp : Continuous fun t : ℝ × ℝ => Real.exp (c * (|t.1| + |t.2|)) := by fun_prop
  have hsupp : Function.support (fun t : ℝ × ℝ => σ t * Real.exp (c * (|t.1| + |t.2|)))
      ⊆ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    intro t ht
    rw [Function.mem_support] at ht
    have hσne : σ t ≠ 0 := fun h => ht (by rw [h, zero_mul])
    have h := hσsupp t hσne
    have h1 : |t.1| ≤ 1 := by
      have h2 : t.1 ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [h, sq_nonneg t.2]
      rwa [sq_le_sq, abs_one] at h2
    have h2 : |t.2| ≤ 1 := by
      have h3 : t.2 ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [h, sq_nonneg t.1]
      rwa [sq_le_sq, abs_one] at h3
    rw [Metric.mem_closedBall, dist_zero_right]
    exact max_le h1 h2
  exact (hσc.mul hexp).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ × ℝ) 1) isClosed_closure
      (closure_minimal hsupp Metric.isClosed_closedBall))

set_option maxHeartbeats 800000 in
-- context: namespace Work.FTS.StrongEps.StepFacts. `Jker σ ε p = ε⁻¹^2 * σ (ε⁻¹ • p)` is the `ε`-rescaled kernel; `σ` is an arbitrary nonnegative continuous function supported in the closed unit ball. The conclusion is a conjunction.
theorem Jker_moment_le (σ : ℝ × ℝ → ℝ) (hσ0 : ∀ p : ℝ × ℝ, 0 ≤ σ p)
    (hσc : Continuous σ)
    (hσsupp : ∀ p : ℝ × ℝ, σ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1)
    {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 ≤ γ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker σ ε p * Real.exp (γ * (|p.1| + |p.2|)))
    ∧ (∫ p : ℝ × ℝ,
        Work.FTS.StrongEps.Jker σ ε p * Real.exp (γ * (|p.1| + |p.2|)))
      ≤ ∫ t : ℝ × ℝ, σ t * Real.exp (γ * (|t.1| + |t.2|)) := by
  -- the right-hand sides with the two exponents are integrable
  have hG : MeasureTheory.Integrable
      (fun t : ℝ × ℝ => σ t * Real.exp (γ * (|t.1| + |t.2|))) :=
    integrable_sigma_exp σ hσc hσsupp γ
  have hG' : MeasureTheory.Integrable
      (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) :=
    integrable_sigma_exp σ hσc hσsupp (γ * ε)
  -- `ε * (ε⁻¹ * a + ε⁻¹ * b) = a + b`, the cancellation behind the change of variables
  have harg : ∀ a b : ℝ, γ * ε * (ε⁻¹ * a + ε⁻¹ * b) = γ * (a + b) := by
    intro a b
    have hne : ε ≠ 0 := hε.ne'
    field_simp
  -- unfolding the kernel, keeping the exponential as it is
  have hpt : ∀ p : ℝ × ℝ,
      Work.FTS.StrongEps.Jker σ ε p * Real.exp (γ * (|p.1| + |p.2|))
        = ε⁻¹ ^ 2 * (σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|))) := by
    intro p
    simp only [Work.FTS.StrongEps.Jker]
    ring
  -- the same integrand with the variable scaled by `ε⁻¹`
  have hpoint : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|))
      = (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p) := by
    intro p
    have h : γ * (|p.1| + |p.2|) = γ * ε * (|(ε⁻¹ • p).1| + |(ε⁻¹ • p).2|) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hε.le)]
      exact (harg |p.1| |p.2|).symm
    rw [h]
  -- the change of variables `p ↦ ε⁻¹ p`
  have hcv : (∫ p : ℝ × ℝ, σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)))
      = ε ^ 2 * ∫ t : ℝ × ℝ, σ t * Real.exp (γ * ε * (|t.1| + |t.2|)) := by
    rw [show (fun p : ℝ × ℝ => σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)))
        = (fun p : ℝ × ℝ =>
            (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p))
        from funext hpoint]
    rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) hε.le]
    rw [Module.finrank_prod, Module.finrank_self]
    norm_num
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p)) :=
      hG'.comp_smul (inv_ne_zero hε.ne')
    have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ε⁻¹ ^ 2 *
        ((fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p))) :=
      h1.const_mul _
    have h3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ε⁻¹ ^ 2 *
        (σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)))) :=
      h2.congr (Filter.Eventually.of_forall fun p => by
        show ε⁻¹ ^ 2 * ((fun t : ℝ × ℝ => σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p))
          = ε⁻¹ ^ 2 * (σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)))
        rw [hpoint p])
    exact h3.congr (Filter.Eventually.of_forall fun p => (hpt p).symm)
  · have hle : ∀ t : ℝ × ℝ, σ t * Real.exp (γ * ε * (|t.1| + |t.2|))
        ≤ σ t * Real.exp (γ * (|t.1| + |t.2|)) := by
      intro t
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hσ0 t)
      have hS : 0 ≤ |t.1| + |t.2| := by positivity
      have h1 : γ * ε ≤ γ := by simpa using mul_le_mul_of_nonneg_left hε1 hγ
      calc γ * ε * (|t.1| + |t.2|) = (γ * ε) * (|t.1| + |t.2|) := by ring
        _ ≤ γ * (|t.1| + |t.2|) := mul_le_mul_of_nonneg_right h1 hS
    calc (∫ p : ℝ × ℝ,
          Work.FTS.StrongEps.Jker σ ε p * Real.exp (γ * (|p.1| + |p.2|)))
        = ∫ p : ℝ × ℝ, ε⁻¹ ^ 2 * (σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|))) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => hpt p)
      _ = ε⁻¹ ^ 2 * ∫ p : ℝ × ℝ, σ (ε⁻¹ • p) * Real.exp (γ * (|p.1| + |p.2|)) :=
          MeasureTheory.integral_const_mul _ _
      _ = ε⁻¹ ^ 2 * (ε ^ 2 * ∫ t : ℝ × ℝ, σ t * Real.exp (γ * ε * (|t.1| + |t.2|))) := by
          rw [hcv]
      _ = ∫ t : ℝ × ℝ, σ t * Real.exp (γ * ε * (|t.1| + |t.2|)) := by
          have h2 : ε⁻¹ ^ 2 * ε ^ 2 = (1 : ℝ) := by
            rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
          rw [← mul_assoc, h2, one_mul]
      _ ≤ ∫ t : ℝ × ℝ, σ t * Real.exp (γ * (|t.1| + |t.2|)) :=
          MeasureTheory.integral_mono hG' hG (fun t => hle t)

end Work.FTS.StrongEps.StepFacts
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.abs_deriv_Jker =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# The two partial derivatives of the rescaled kernel `Jker ρ ε`

This file collects the elementary calculus of the kernel `Jker ρ ε p = ε⁻¹^2 • ρ (p/ε)`:

* the two scaling identities `∂₁ (Jker ρ ε) = ε⁻¹ • Jker (|∂₁ρ|) ε` (and likewise for `∂₂`),
  which express the fact that differentiating the rescaled kernel is the same as rescaling the
  kernel of the derivative (with the absolute value taken on the kernel side, since all the
  later estimates only ever see `|∂₁ρ|`);
* the continuity of the two partial derivatives of a smooth `ρ` (they are the Fréchet
  derivative applied to the two unit vectors `(1,0)`, `(0,1)`);
* the support of the two partial derivatives of `ρ`: since `ρ` is supported in the closed unit
  ball and is smooth, its partial derivatives vanish off that ball as well.

The proofs rest on the elementary slice-calculus of `ℝ × ℝ` (`deriv_slice_fst_eq`,
`deriv_slice_snd_eq`) and on the chain rule in one variable.
-/

/-! ## The slice calculus of `ℝ × ℝ` -/

/-- The derivative of the first-coordinate slice of a function on `ℝ × ℝ` is the Fréchet
derivative at the point, evaluated at the unit vector `(1, 0)`. -/
private lemma deriv_slice_fst_eq {f : ℝ × ℝ → ℝ} {x y : ℝ} (hf : DifferentiableAt ℝ f (x, y)) :
    deriv (fun s : ℝ => f (s, y)) x = fderiv ℝ f (x, y) (1, 0) := by
  have hγ : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) x := by
    simpa using (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y).hasDerivAt
  have h := hf.hasFDerivAt.comp_hasDerivAt x hγ
  simpa [Function.comp_def] using h.deriv

/-- The derivative of the second-coordinate slice of a function on `ℝ × ℝ` is the Fréchet
derivative at the point, evaluated at the unit vector `(0, 1)`. -/
private lemma deriv_slice_snd_eq {f : ℝ × ℝ → ℝ} {x y : ℝ} (hf : DifferentiableAt ℝ f (x, y)) :
    deriv (fun t : ℝ => f (x, t)) y = fderiv ℝ f (x, y) (0, 1) := by
  have hγ : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y := by
    simpa using (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y).hasDerivAt
  have h := hf.hasFDerivAt.comp_hasDerivAt y hγ
  simpa [Function.comp_def] using h.deriv

/-- The first-coordinate slice of a `C¹` function on `ℝ × ℝ` is `C¹`. -/
private lemma contDiff_slice_fst₁ {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (y : ℝ) :
    ContDiff ℝ 1 (fun x : ℝ => f (x, y)) :=
  hf.comp (contDiff_id.prodMk (contDiff_const (c := y)))

/-- The second-coordinate slice of a `C¹` function on `ℝ × ℝ` is `C¹`. -/
private lemma contDiff_slice_snd₁ {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => f (x, t)) :=
  hf.comp ((contDiff_const (c := x)).prodMk contDiff_id)

/-- For a `C¹` function on `ℝ × ℝ`, the pointwise first-coordinate slice derivative is
continuous. -/
private lemma continuous_deriv_slice_fst {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s : ℝ => f (s, p.2)) p.1) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ f p (1, 0)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h1.congr (fun p => (deriv_slice_fst_eq (x := p.1) (y := p.2)
    hf.differentiable_one.differentiableAt).symm)

/-- For a `C¹` function on `ℝ × ℝ`, the pointwise second-coordinate slice derivative is
continuous. -/
private lemma continuous_deriv_slice_snd {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × ℝ => deriv (fun t : ℝ => f (p.1, t)) p.2) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ f p (0, 1)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h1.congr (fun p => (deriv_slice_snd_eq (x := p.1) (y := p.2)
    hf.differentiable_one.differentiableAt).symm)

/-! ## The chain rule for the rescaled kernel -/

/-- **The first scaling identity, in non-absolute-value form**: differentiating
`ε⁻¹^2 * σ (ε⁻¹·, ε⁻¹ p₂)` in the first variable produces the extra factor `ε⁻¹`. -/
private lemma deriv_Jker_fst (σ : ℝ × ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (ε : ℝ) (p : ℝ × ℝ) :
    deriv (fun s : ℝ => ε⁻¹ ^ 2 * σ (ε⁻¹ * s, ε⁻¹ * p.2)) p.1
      = ε⁻¹ ^ 2 * (ε⁻¹ * deriv (fun u : ℝ => σ (u, ε⁻¹ * p.2)) (ε⁻¹ * p.1)) := by
  have hsm : ContDiff ℝ 1 (fun u : ℝ => σ (u, ε⁻¹ * p.2)) := contDiff_slice_fst₁ hσ _
  have houter : HasDerivAt (fun u : ℝ => σ (u, ε⁻¹ * p.2))
      (deriv (fun u : ℝ => σ (u, ε⁻¹ * p.2)) (ε⁻¹ * p.1)) (ε⁻¹ * p.1) :=
    hsm.differentiable_one.differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun s : ℝ => ε⁻¹ * s) ε⁻¹ p.1 := by
    simpa using (hasDerivAt_id p.1).const_mul ε⁻¹
  have hcomp : HasDerivAt (fun s : ℝ => σ (ε⁻¹ * s, ε⁻¹ * p.2))
      (deriv (fun u : ℝ => σ (u, ε⁻¹ * p.2)) (ε⁻¹ * p.1) * ε⁻¹) p.1 := by
    simpa [Function.comp_def] using houter.comp p.1 hinner
  rw [(hcomp.const_mul (ε⁻¹ ^ 2)).deriv]
  ring

/-- **The second scaling identity, in non-absolute-value form**. -/
private lemma deriv_Jker_snd (σ : ℝ × ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (ε : ℝ) (p : ℝ × ℝ) :
    deriv (fun t : ℝ => ε⁻¹ ^ 2 * σ (ε⁻¹ * p.1, ε⁻¹ * t)) p.2
      = ε⁻¹ ^ 2 * (ε⁻¹ * deriv (fun u : ℝ => σ (ε⁻¹ * p.1, u)) (ε⁻¹ * p.2)) := by
  have hsm : ContDiff ℝ 1 (fun u : ℝ => σ (ε⁻¹ * p.1, u)) := contDiff_slice_snd₁ hσ _
  have houter : HasDerivAt (fun u : ℝ => σ (ε⁻¹ * p.1, u))
      (deriv (fun u : ℝ => σ (ε⁻¹ * p.1, u)) (ε⁻¹ * p.2)) (ε⁻¹ * p.2) :=
    hsm.differentiable_one.differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun t : ℝ => ε⁻¹ * t) ε⁻¹ p.2 := by
    simpa using (hasDerivAt_id p.2).const_mul ε⁻¹
  have hcomp : HasDerivAt (fun t : ℝ => σ (ε⁻¹ * p.1, ε⁻¹ * t))
      (deriv (fun u : ℝ => σ (ε⁻¹ * p.1, u)) (ε⁻¹ * p.2) * ε⁻¹) p.2 := by
    simpa [Function.comp_def] using houter.comp p.2 hinner
  rw [(hcomp.const_mul (ε⁻¹ ^ 2)).deriv]
  ring

-- context: namespace Work.FTS.StrongEps.StepFacts. `Jker ρ ε p = ε⁻¹^2 * ρ (ε⁻¹ • p)`; `IsSmoothKernel ρ` = `∀n, ContDiff ℝ n ρ` plus continuous/supported-in-closed-unit-ball/nonneg/mass-one. The conclusion is a six-fold conjunction (scaling identities for the two partial derivatives, joint continuity of the two partials of ρ, and support of the two partials).
theorem abs_deriv_Jker (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
        = ε⁻¹ * Work.FTS.StrongEps.Jker
            (fun q : ℝ × ℝ => |deriv (fun s : ℝ => ρ (s, q.2)) q.1|) ε p)
    ∧ (∀ p : ℝ × ℝ, |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
        = ε⁻¹ * Work.FTS.StrongEps.Jker
            (fun q : ℝ × ℝ => |deriv (fun t : ℝ => ρ (q.1, t)) q.2|) ε p)
    ∧ Continuous (fun q : ℝ × ℝ => deriv (fun s : ℝ => ρ (s, q.2)) q.1)
    ∧ Continuous (fun q : ℝ × ℝ => deriv (fun t : ℝ => ρ (q.1, t)) q.2)
    ∧ (∀ p : ℝ × ℝ, deriv (fun s : ℝ => ρ (s, p.2)) p.1 ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1)
    ∧ (∀ p : ℝ × ℝ, deriv (fun t : ℝ => ρ (p.1, t)) p.2 ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1) := by
  have hsmooth : ContDiff ℝ 1 ρ := hρ.smooth 1
  -- the two scaling identities
  have hsc1 : ∀ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      = ε⁻¹ * Work.FTS.StrongEps.Jker
          (fun q : ℝ × ℝ => |deriv (fun s : ℝ => ρ (s, q.2)) q.1|) ε p := by
    intro p
    simp only [Work.FTS.StrongEps.Jker, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [deriv_Jker_fst ρ hsmooth ε p]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹)]
    ring
  have hsc2 : ∀ p : ℝ × ℝ, |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
      = ε⁻¹ * Work.FTS.StrongEps.Jker
          (fun q : ℝ × ℝ => |deriv (fun t : ℝ => ρ (q.1, t)) q.2|) ε p := by
    intro p
    simp only [Work.FTS.StrongEps.Jker, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [deriv_Jker_snd ρ hsmooth ε p]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹)]
    ring
  -- the two partial derivatives are continuous
  have hcont1 : Continuous (fun q : ℝ × ℝ => deriv (fun s : ℝ => ρ (s, q.2)) q.1) :=
    continuous_deriv_slice_fst hsmooth
  have hcont2 : Continuous (fun q : ℝ × ℝ => deriv (fun t : ℝ => ρ (q.1, t)) q.2) :=
    continuous_deriv_slice_snd hsmooth
  -- both partial derivatives vanish off the closed unit ball
  have htsupport : tsupport ρ ⊆ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ 1} :=
    closure_minimal (fun q hq => hρ.moll.support q hq)
      (isClosed_le (by continuity) continuous_const)
  have hsupp1 : ∀ p : ℝ × ℝ, deriv (fun s : ℝ => ρ (s, p.2)) p.1 ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
    intro p hp
    by_contra hcon
    have hlt : 1 < p.1 ^ 2 + p.2 ^ 2 := not_le.mp hcon
    have hpnot : p ∉ tsupport ρ := fun h => absurd (htsupport h) (not_le.mpr hlt)
    have hev : ρ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hpnot
    have hcont : Tendsto (fun s : ℝ => (s, p.2)) (𝓝 p.1) (𝓝 p) :=
      (continuous_id.prodMk continuous_const).tendsto p.1
    have hslice : (fun s : ℝ => ρ (s, p.2)) =ᶠ[𝓝 p.1] (fun _ : ℝ => (0 : ℝ)) :=
      hcont.eventually hev
    exact hp (by rw [hslice.deriv_eq]; simp)
  have hsupp2 : ∀ p : ℝ × ℝ, deriv (fun t : ℝ => ρ (p.1, t)) p.2 ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
    intro p hp
    by_contra hcon
    have hlt : 1 < p.1 ^ 2 + p.2 ^ 2 := not_le.mp hcon
    have hpnot : p ∉ tsupport ρ := fun h => absurd (htsupport h) (not_le.mpr hlt)
    have hev : ρ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hpnot
    have hcont : Tendsto (fun t : ℝ => (p.1, t)) (𝓝 p.2) (𝓝 p) :=
      (continuous_const.prodMk continuous_id).tendsto p.2
    have hslice : (fun t : ℝ => ρ (p.1, t)) =ᶠ[𝓝 p.2] (fun _ : ℝ => (0 : ℝ)) :=
      hcont.eventually hev
    exact hp (by rw [hslice.deriv_eq]; simp)
  exact ⟨hsc1, hsc2, hcont1, hcont2, hsupp1, hsupp2⟩

end

end Work.FTS.StrongEps.StepFacts
end
-- ===== merged: Submission.Work.FTS.StrongEps.Traces.eventually_thShift_gt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.Traces

open scoped Real Topology
open Filter

/-- As `θ → π/2⁻`, the shift `thShift θ p = arctan (tan θ · e^{-p})` tends to `π/2` uniformly
for `p` in a bounded set: `tan θ · e^{-p} → +∞` (for `p ≤ ε` bounded below by `-ε`, the factor
`e^{-p}` is bounded below by `e^{-ε}`), and `arctan → π/2` at `+∞`.  Monotonicity of `thShift`
in `p` shows that the worst case is `p = ε`. -/
theorem eventually_thShift_gt (ε δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ θ in 𝓝[<] (Real.pi / 2), ∀ p : ℝ, |p| ≤ ε →
      Real.pi / 2 - δ < Work.FTS.StrongEps.thShift θ p := by
  -- `tan θ · e^{-ε} → +∞` as `θ → π/2⁻`
  have htan : Tendsto (fun θ : ℝ => Real.tan θ * Real.exp (-ε)) (𝓝[<] (Real.pi / 2)) atTop :=
    Real.tendsto_tan_pi_div_two.atTop_mul_const (Real.exp_pos (-ε))
  -- hence `thShift θ ε = arctan (tan θ · e^{-ε}) → π/2`
  have hcomp : Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-ε)))
      (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp htan
  have hmem : Real.pi / 2 ∈ Set.Ioi (Real.pi / 2 - δ) := by
    show Real.pi / 2 - δ < Real.pi / 2
    linarith
  have h2 : ∀ᶠ θ in 𝓝[<] (Real.pi / 2),
      Real.pi / 2 - δ < Work.FTS.StrongEps.thShift θ ε := by
    filter_upwards [hcomp.eventually (isOpen_Ioi.mem_nhds hmem)] with θ hθ
    simpa only [Work.FTS.StrongEps.thShift] using hθ
  -- and eventually `θ ∈ (0, π/2)`, where `p ↦ thShift θ p` is antitone
  have h1 : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (by positivity : (0:ℝ) < Real.pi / 2)),
      (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2))] with θ hgt hlt
    exact ⟨hgt, hlt⟩
  filter_upwards [h1, h2] with θ hθ hlt p hp
  exact lt_of_lt_of_le hlt
    (Work.FTS.StrongEps.thShift_anti hθ (le_trans (le_abs_self p) hp))

end Work.FTS.StrongEps.Traces
end
-- ===== merged: Submission.Work.FTS.StrongEps.Traces.eventually_thShift_lt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.Traces

open scoped Real Topology
open Filter

/-- For `|p| ≤ ε` and `θ ∈ [0, π/2]` the shift `thShift θ p` is dominated by the shift at the
extreme value `p = -ε`, which is an explicit function of `θ` alone (tending to `0` as
`θ → 0⁺`). -/
private theorem thShift_le_arctan_exp (ε : ℝ) {θ p : ℝ} (hθ0 : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi / 2) (hp : |p| ≤ ε) :
    Work.FTS.StrongEps.thShift θ p ≤ Real.arctan (Real.tan θ * Real.exp ε) := by
  have htan : 0 ≤ Real.tan θ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0 hθπ
  have hp' : -p ≤ ε := by linarith [(abs_le.mp hp).1]
  have hexp : Real.exp (-p) ≤ Real.exp ε := Real.exp_le_exp.mpr hp'
  exact Real.arctan_le_arctan_iff.mpr (mul_le_mul_of_nonneg_left hexp htan)

theorem eventually_thShift_lt (ε δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → Work.FTS.StrongEps.thShift θ p < δ := by
  -- `arctan (tan θ * e ^ ε) → 0` as `θ → 0⁺`
  have htan0 : Tendsto Real.tan (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : ContinuousAt Real.tan 0 := Real.continuousAt_tan.mpr (by rw [Real.cos_zero]; norm_num)
    have h' : Tendsto Real.tan (𝓝 (0 : ℝ)) (𝓝 (Real.tan 0)) := h.tendsto
    rw [Real.tan_zero] at h'
    exact h'.mono_left inf_le_left
  have hmul : Tendsto (fun θ : ℝ => Real.tan θ * Real.exp ε) (𝓝[>] (0 : ℝ))
      (𝓝 (0 * Real.exp ε)) := htan0.mul tendsto_const_nhds
  have hg : Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp ε)) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have h := (Real.continuous_arctan.tendsto (0 * Real.exp ε)).comp hmul
    simpa only [Function.comp_def, zero_mul, Real.arctan_zero] using h
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Real.arctan (Real.tan θ * Real.exp ε) < δ :=
    hg.eventually (eventually_lt_nhds hδ)
  have hlt : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < Real.pi / 2 :=
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
  filter_upwards [hev, self_mem_nhdsWithin, hlt] with θ hevθ hθpos hθlt
  intro p hp
  exact lt_of_le_of_lt (thShift_le_arctan_exp ε (le_of_lt hθpos) (le_of_lt hθlt) hp) hevθ

end Work.FTS.StrongEps.Traces
end
-- ===== merged: Submission.Work.FTS.StrongEps.Traces.sin_rpow_thShift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.Traces

open scoped Real Topology

/-!
# `Work.FTS.StrongEps.Traces.sin_rpow_thShift_le`

The angular weight `sin(2θ)^{-γ}` (and its `e`-powers) changes by at most `e^{ε|e|}` under the
`θ`-shift `thShift θ p = arctan (tan θ · e^{-p})` whenever `|p| ≤ ε`.

The whole content is the two-sided bound

  `e^{-|p|} sin(2θ) ≤ sin(2·thShift θ p) ≤ e^{|p|} sin(2θ)`

(`Work.FTS.StrongEps.sinTwo_thShift_bounds`), which says exactly that the ratio
`sin(2θ)/sin(2·thShift θ p)` lies in `[e^{-|p|}, e^{|p|}]`; its logarithm is therefore bounded by
`|p| ≤ ε` in absolute value, and `x ^ e = exp (e · log x)` for `x > 0` turns that into the
claimed `e^{ε|e|}` multiplicative factor.
-/

theorem sin_rpow_thShift_le (θ p ε e : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hε : 0 ≤ ε)
    (hp : |p| ≤ ε) :
    Real.sin (2 * θ) ^ e
      ≤ Real.exp (ε * |e|) * Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ e := by
  set s := Real.sin (2 * θ) with hsdef
  set s' := Real.sin (2 * Work.FTS.StrongEps.thShift θ p) with hs'def
  have hs : 0 < s := by
    rw [hsdef]; exact Work.FTS.StrongEps.sin_two_pos hθ
  have hs' : 0 < s' := by
    rw [hs'def]
    exact Work.FTS.StrongEps.sin_two_pos (Work.FTS.StrongEps.thShift_mem hθ)
  obtain ⟨hlo, hhi⟩ := Work.FTS.StrongEps.sinTwo_thShift_bounds (θ := θ) (p := p) hθ
  -- `hlo : exp (-|p|) * s ≤ s'`, `hhi : s' ≤ exp |p| * s`
  have hRpos : 0 < s / s' := div_pos hs hs'
  have hRge : Real.exp (-|p|) ≤ s / s' := by
    rw [le_div_iff₀ hs']
    calc Real.exp (-|p|) * s'
        ≤ Real.exp (-|p|) * (Real.exp |p| * s) :=
          mul_le_mul_of_nonneg_left hhi (Real.exp_pos _).le
      _ = s := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hRle : s / s' ≤ Real.exp |p| := by
    rw [div_le_iff₀ hs']
    calc s = Real.exp |p| * (Real.exp (-|p|) * s) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp |p| * s' := mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le
  -- the logarithm of the ratio is bounded by `|p| ≤ ε`
  have hlog : |Real.log (s / s')| ≤ |p| := by
    rw [abs_le]
    exact ⟨by
        have h := Real.log_le_log (Real.exp_pos (-|p|)) hRge
        rwa [Real.log_exp] at h,
      by
        have h := Real.log_le_log hRpos hRle
        rwa [Real.log_exp] at h⟩
  have hmain : (s / s') ^ e ≤ Real.exp (ε * |e|) := by
    rw [Real.rpow_def_of_pos hRpos]
    refine Real.exp_le_exp.mpr ?_
    calc Real.log (s / s') * e ≤ |Real.log (s / s') * e| := le_abs_self _
      _ = |Real.log (s / s')| * |e| := abs_mul _ _
      _ ≤ |p| * |e| := mul_le_mul_of_nonneg_right hlog (abs_nonneg e)
      _ ≤ ε * |e| := mul_le_mul_of_nonneg_right hp (abs_nonneg e)
  have hspow : s ^ e = (s / s') ^ e * s' ^ e := by
    conv_lhs => rw [show s = (s / s') * s' from (div_mul_cancel₀ s hs'.ne').symm]
    rw [Real.mul_rpow hRpos.le hs'.le]
  rw [hspow]
  exact mul_le_mul_of_nonneg_right hmain (Real.rpow_pos_of_pos hs' e).le

end Work.FTS.StrongEps.Traces
end
-- ===== merged: Submission.Work.FTS.StrongEps.smoothOpen_linPart =====
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

open Work.FTS.Galerkin (Fn)

/-! ## The finite-order `D`-calculus on an open set

`∂_z`, `∂_θ` lower the differentiability order by one, and `D_z`, `D_θ` are the products of
those with the smooth factors `z` and `sin(2θ)`.  These are the *finite-order* forms of the
calculus of `Work.FTS.LocData.SmoothChain`; they are repeated here (in the `StrongEps`
namespace, `private`) so that this module does not have to import the `LocData` chapter.
-/

/-- `∂_z` lowers the differentiability order by one on an open set. -/
private theorem pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-- `D_z` lowers the differentiability order by one on an open set. -/
private theorem Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := pz_fin hV h
  have hfun : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) V :=
    contDiff_fst.contDiffOn.mul hpz
  refine hfun.congr (fun p hp => ?_)
  rfl

/-- `∂_θ` lowers the differentiability order by one on an open set. -/
private theorem pth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-- `D_θ` lowers the differentiability order by one on an open set. -/
private theorem Dth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hpth := pth_fin hV h
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p) V :=
    hsin.mul hpth
  refine hfun.congr (fun p hp => ?_)
  rfl

/-! ## The angular factor `Γ` -/

/-- `Γ(θ) = (sin θ·cos²θ)^{α/3}` is `C^n` on the open quadrant, for every `n` and every `α`:
the base is positive and smooth there and we take an arbitrary real power of it. -/
private theorem gam_smooth (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Quad := by
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2) Quad :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Quad, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Quad.mp hp
    have hs : 0 < Real.sin p.2 :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    positivity
  simpa only [Work.Spaces.Gam] using
    hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

/-! ## The main theorem -/

theorem smoothOpen_linPart {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (hL12 : ∀ n : ℕ, ContDiffOn ℝ n (Work.Coercivity.L12f f) (Set.Ioi 0)) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Coercivity.LGammaT α f))
      Work.FTS.StrongEps.Quad := by
  intro n
  -- the open quadrant and the standing non-vanishing factor `1 + z`
  have hQ : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioo
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 : ℝ) + p.1) Quad :=
    contDiffOn_const.add contDiffOn_fst
  have h1z : ∀ p ∈ Quad, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp; have := (mem_Quad.mp hp).1; linarith
  -- the profile and its two first derivatives
  have hf0 : ContDiffOn ℝ n (Function.uncurry f) Quad := hf n
  have hDz : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz f)) Quad :=
    Dz_fin hQ (hf (n + 1))
  have hDth : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth f)) Quad :=
    Dth_fin hQ (hf (n + 1))
  have hGam : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Quad := gam_smooth α n
  have hL12f : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1) Quad :=
    (hL12 n).comp contDiffOn_fst (fun p hp => (mem_Quad.mp hp).1)
  have hinv : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((1 : ℝ) + p.1)⁻¹) Quad := hden.inv h1z
  -- the two rational coefficients, in the form in which `ContDiffOn` composition is easy
  have hcoef1 : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        2 * p.1 * Work.Spaces.Gam α p.2 * (Work.Spaces.c α)⁻¹ * ((1 + p.1)⁻¹) ^ 2) Quad :=
    (((contDiffOn_const.mul contDiffOn_fst).mul hGam).mul contDiffOn_const).mul (hinv.pow 2)
  have hcoef : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)) Quad := by
    refine hcoef1.congr (fun p hp => ?_)
    have hz : (1 : ℝ) + p.1 ≠ 0 := h1z p hp
    field_simp
  have hproj1 : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        Work.Spaces.Gam α p.2 * (Work.Spaces.c α)⁻¹
          * (2 * p.1 ^ 2 * ((1 + p.1)⁻¹) ^ 3)
          * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) Quad :=
    ((hGam.mul contDiffOn_const).mul
      ((contDiffOn_const.mul (contDiffOn_fst.pow 2)).mul (hinv.pow 3))).mul contDiffOn_const
  have hproj : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
          * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) Quad := by
    refine hproj1.congr (fun p hp => ?_)
    have hz : (1 : ℝ) + p.1 ≠ 0 := h1z p hp
    field_simp
  -- the six summands of the full expression
  have hC : ContDiffOn ℝ n (fun p : ℝ × ℝ => 2 * Function.uncurry f p / (1 + p.1)) Quad :=
    (contDiffOn_const.mul hf0).div hden h1z
  have hD : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)
          * Work.Coercivity.L12f f p.1) Quad :=
    hcoef.mul hL12f
  have hE : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => 3 * Function.uncurry (Work.Spaces.Dth f) p / (1 + p.1)) Quad :=
    (contDiffOn_const.mul hDth).div hden h1z
  -- the definitional unfolding of `𝓛_Γ^T` as a function of the point `(z,θ)`
  have hG : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      ((Function.uncurry f p + Function.uncurry (Work.Spaces.Dz f) p)
        - 2 * Function.uncurry f p / (1 + p.1)
        - (2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)
            * Work.Coercivity.L12f f p.1))
      - (3 * Function.uncurry (Work.Spaces.Dth f) p / (1 + p.1)
        - ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0))) Quad :=
    (((hf0.add hDz).sub hC).sub hD).sub (hE.sub hproj)
  refine hG.congr (fun p hp => ?_)
  rfl

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.wtE_shift_le =====
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

/-! ## The elementary trigonometric identity `sin (2 arctan u) = 2u/(1+u²)` -/

/-! ## The `z`-half: `w (zShift z p) ≤ e^{2|p|} w z`, hence `wtZ (zShift) ≤ e^{4|p|} wtZ` -/

/-- `w` is nonnegative. -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- The radial weight is shifted by at most `e^{2|p|}`:  for `z > 0` and any `p`,
`((1 + z e^{-p})/(z e^{-p}))² ≤ e^{2|p|} ((1+z)/z)²`. -/
theorem w_zShift_le (z p : ℝ) (hz : 0 < z) :
    Work.Spaces.w (zShift z p) ≤ Real.exp (2 * |p|) * Work.Spaces.w z := by
  have hone : 1 ≤ Real.exp |p| := Real.one_le_exp (abs_nonneg p)
  have hexp : Real.exp p ≤ Real.exp |p| := Real.exp_le_exp.2 (le_abs_self p)
  have h2 : z + Real.exp p ≤ Real.exp |p| * (1 + z) := by
    have h3 : z ≤ Real.exp |p| * z := by nlinarith [hz, hone]
    have h4 : z + Real.exp p ≤ Real.exp |p| * z + Real.exp |p| := add_le_add h3 hexp
    linarith [h4]
  have hsq : (z + Real.exp p) ^ 2 ≤ Real.exp (2 * |p|) * (1 + z) ^ 2 := by
    have h5 : (z + Real.exp p) ^ 2 ≤ (Real.exp |p| * (1 + z)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h6 : (Real.exp |p| * (1 + z)) ^ 2 = Real.exp (2 * |p|) * (1 + z) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [show (2 : ℝ) * |p| = |p| + |p| by ring, Real.exp_add, sq]
    linarith [h5, h6.le, h6.ge]
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  have hw1 : Work.Spaces.w (zShift z p) = (z + Real.exp p) ^ 2 / z ^ 2 := by
    rw [Work.Spaces.w, zShift]
    have hze : z * Real.exp (-p) = z / Real.exp p := by
      rw [Real.exp_neg]; ring
    rw [hze, div_pow]
    field_simp
    ring
  have hw2 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  rw [hw1, hw2]
  calc (z + Real.exp p) ^ 2 / z ^ 2
      ≤ (Real.exp (2 * |p|) * (1 + z) ^ 2) / z ^ 2 := div_le_div_of_nonneg_right hsq hz2.le
    _ = Real.exp (2 * |p|) * ((1 + z) ^ 2 / z ^ 2) := by rw [mul_div_assoc]

theorem wtZ_zShift_le (z p : ℝ) (hz : 0 < z) :
    wtZ (zShift z p) ≤ Real.exp (4 * |p|) * wtZ z := by
  have h := w_zShift_le z p hz
  have h2 : (Real.exp (2 * |p|) * Work.Spaces.w z) ^ 2
      = Real.exp (4 * |p|) * wtZ z := by
    rw [mul_pow, wtZ]
    rw [show (4 : ℝ) * |p| = 2 * |p| + 2 * |p| by ring, Real.exp_add, sq]
  calc wtZ (zShift z p) = Work.Spaces.w (zShift z p) ^ 2 := rfl
    _ ≤ (Real.exp (2 * |p|) * Work.Spaces.w z) ^ 2 := pow_le_pow_left₀ (w_nonneg _) h 2
    _ = Real.exp (4 * |p|) * wtZ z := h2

/-! ## The `θ`-half: `sEtaW (thShift θ p) ≤ e^{|p|} sEtaW θ` -/

theorem sEtaW_thShift_le {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    sEtaW (thShift θ p) ≤ Real.exp |p| * sEtaW θ := by
  have hcosp : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hsin2pos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hEE : Real.exp p * Real.exp (-p) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hEE' : Real.exp (-p) * Real.exp p = 1 := by rw [mul_comm, hEE]
  have hsin2 : Real.sin (2 * θ) = 2 * Real.tan θ * Real.cos θ ^ 2 := by
    rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]; field_simp
  set Dd : ℝ := Real.exp p * Real.cos θ ^ 2 + Real.exp (-p) * Real.sin θ ^ 2 with hDd
  have hDpos : 0 < Dd := by
    rw [hDd]
    have h1 : 0 < Real.exp p * Real.cos θ ^ 2 := mul_pos (Real.exp_pos p) (pow_pos hcosp 2)
    have h2 : 0 ≤ Real.exp (-p) * Real.sin θ ^ 2 :=
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    linarith
  have hDle : Dd ≤ Real.exp |p| := by
    rw [hDd]
    have h1 : Real.exp p ≤ Real.exp |p| := Real.exp_le_exp.2 (le_abs_self p)
    have h2 : Real.exp (-p) ≤ Real.exp |p| := Real.exp_le_exp.2 (neg_le_abs p)
    have hs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    calc Real.exp p * Real.cos θ ^ 2 + Real.exp (-p) * Real.sin θ ^ 2
        ≤ Real.exp |p| * Real.cos θ ^ 2 + Real.exp |p| * Real.sin θ ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
            (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
      _ = Real.exp |p| := by rw [← mul_add, hs, mul_one]
  have hsinid : Real.sin (2 * thShift θ p) = Real.sin (2 * θ) / Dd := by
    rw [hDd]
    have hE : Real.exp p ≠ 0 := Real.exp_ne_zero p
    have hE' : Real.exp (-p) ≠ 0 := Real.exp_ne_zero (-p)
    have hc : Real.cos θ ≠ 0 := hcosp.ne'
    rw [thShift]
    rw [show Real.sin (2 * Real.arctan (Real.tan θ * Real.exp (-p)))
        = 2 * (Real.tan θ * Real.exp (-p)) / (1 + (Real.tan θ * Real.exp (-p)) ^ 2) from
      sin_two_mul_arctan _]
    rw [hsin2, Real.tan_eq_sin_div_cos]
    field_simp
    ring_nf
    have hkey : Real.sin θ * Real.exp (-p) * Real.cos θ ^ 2 * Real.exp p
        = Real.sin θ * Real.cos θ ^ 2 := by
      rw [show Real.sin θ * Real.exp (-p) * Real.cos θ ^ 2 * Real.exp p
          = Real.sin θ * Real.cos θ ^ 2 * (Real.exp (-p) * Real.exp p) by ring, hEE', mul_one]
    linarith [hkey]
  rw [sEtaW, sEtaW, hsinid]
  have heta0 : 0 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have heta1 : Work.Spaces.eta ≤ 1 := by rw [Work.Spaces.eta]; norm_num
  have hrw : (Real.sin (2 * θ) / Dd) ^ (-(Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * Dd ^ Work.Spaces.eta := by
    rw [Real.div_rpow hsin2pos.le hDpos.le, Real.rpow_neg hDpos.le, div_inv_eq_mul]
  rw [hrw]
  have hDpow : Dd ^ Work.Spaces.eta ≤ Real.exp |p| := by
    calc Dd ^ Work.Spaces.eta ≤ (Real.exp |p|) ^ Work.Spaces.eta :=
          Real.rpow_le_rpow hDpos.le hDle heta0
      _ = Real.exp (|p| * Work.Spaces.eta) := (Real.exp_mul |p| _).symm
      _ ≤ Real.exp |p| := Real.exp_le_exp.2 (by nlinarith [abs_nonneg p, heta1])
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg hsin2pos.le _
  calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * Dd ^ Work.Spaces.eta
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * Real.exp |p| :=
        mul_le_mul_of_nonneg_left hDpow hnn
    _ = Real.exp |p| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring

/-! ## The shift bound for `wtE` -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.wtG_shift_le =====
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

/-! ## The `rpow` step

A one-sided multiplicative bound on a positive number turns into a bound on any negative power
of it, with the reciprocal constant in the exponent: this is the generic form of the passage
`sin(2·thShift θ p) ≥ e^{-|p|} sin 2θ ⟹ sin(2·thShift θ p)^{-γ} ≤ e^{γ|p|} sin(2θ)^{-γ}`. -/

/-- **Powers with negative exponent invert multiplicative bounds.**  If `0 < s` and
`Real.exp (-c) * s ≤ s'` with `γ ≥ 0`, then `s' ^ (-γ) ≤ Real.exp (γ * c) * s ^ (-γ)`.
(The bound is sharp: for `s' = Real.exp (-c) * s` it is an equality.) -/
theorem rpow_shift_le {s s' c γ : ℝ} (hs : 0 < s) (hγ : 0 ≤ γ)
    (hlo : Real.exp (-c) * s ≤ s') :
    s' ^ (-γ) ≤ Real.exp (γ * c) * s ^ (-γ) := by
  have hpos : 0 < Real.exp (-c) * s := mul_pos (Real.exp_pos _) hs
  have h1 : s' ^ (-γ) ≤ (Real.exp (-c) * s) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos hpos hlo (by linarith)
  rw [Real.mul_rpow (Real.exp_pos (-c)).le hs.le] at h1
  have h2 : (Real.exp (-c)) ^ (-γ) = Real.exp (γ * c) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos (-c)), Real.log_exp]
    congr 1
    ring
  rwa [h2] at h1

/-! ## The angular factor of `wtG` -/


/-! ## The shift bound for the full mixed weight -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.ZopSlotMul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

/-!
# The slot-product estimate for the radial multiplier `D_z = z ∂_z`

For two functions `φ, u : ℝ → ℝ` that are `C⁶` on `(0,∞)`, with the `DzdIter`-iterates of `φ`
up to order `6` bounded by `K`, and every `z > 0`, the weighted slot sum of the product
`φ·u` is bounded by a universal constant times `(1+K)²` times the weighted slot sum of `u`:

    `∑_{q ≤ 6} (D_z^q (φu)(z))² w(z)² ≤ C (1+K)² ∑_{q ≤ 6} (D_z^q u(z))² w(z)²`.

The proof is the one-variable Leibniz rule `dzdIter_mul_leibniz` for `DzdIter = (z∂_z)^q`
(which needs only the differentiability of the iterates, available from `C⁶`), followed by the
Cauchy–Schwarz binomial estimate `binom_sum_sq_le` and a triangle inequality over the seven
slots.  No weight is ever estimated: the factor `w(z)²` is common to all slots and is only
carried along.
-/

set_option autoImplicit false

/-! ## Smoothness of the `DzdIter`s of a `C^n` function of `z` alone -/

/-- `Dzd = z ∂_z` lowers the smoothness order by one on the open half-line. -/
private lemma contDiffOn_dzd_of_succ {u : ℝ → ℝ} {m : ℕ}
    (hu : ContDiffOn ℝ (m + 1) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ m (Work.Elliptic.Dzd u) (Set.Ioi (0 : ℝ)) := by
  have hd : ContDiffOn ℝ m (deriv u) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_deriv_of_succ hu
  show ContDiffOn ℝ m (fun z => z * deriv u z) (Set.Ioi (0 : ℝ))
  simpa only [id_eq] using
    (contDiffOn_id (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) (s := Set.Ioi (0 : ℝ))).mul hd

/-- The iterates of `Dzd = z ∂_z` lose one smoothness order each: a `C^n` function has
`C^{n-b}` `Dzd`-iterates of order `b` on `(0,∞)`. -/
private lemma contDiffOn_dzdIter_of_contDiffOn {u : ℝ → ℝ} {n : ℕ}
    (hu : ContDiffOn ℝ n u (Set.Ioi (0 : ℝ))) :
    ∀ b : ℕ, b ≤ n →
      ContDiffOn ℝ (((n - b : ℕ) : WithTop ℕ∞)) (Work.Elliptic.DzdIter b u)
        (Set.Ioi (0 : ℝ)) := by
  intro b
  induction b with
  | zero => intro _; simpa using hu
  | succ b ih =>
      intro hb
      have hb' : b ≤ n := by omega
      have hle : 1 ≤ n - b := by omega
      have hprev : ContDiffOn ℝ (((n - b : ℕ) : WithTop ℕ∞)) (Work.Elliptic.DzdIter b u)
          (Set.Ioi (0 : ℝ)) := ih hb'
      have hprev' : ContDiffOn ℝ (((n - b - 1 + 1 : ℕ) : WithTop ℕ∞))
          (Work.Elliptic.DzdIter b u) (Set.Ioi (0 : ℝ)) := by
        rwa [Nat.sub_add_cancel hle]
      have hstep : ContDiffOn ℝ (((n - b - 1 : ℕ) : WithTop ℕ∞))
          (Work.Elliptic.Dzd (Work.Elliptic.DzdIter b u)) (Set.Ioi (0 : ℝ)) :=
        contDiffOn_dzd_of_succ (u := Work.Elliptic.DzdIter b u) (m := n - b - 1) hprev'
      rw [Work.Elliptic.DzdIter_succ, Nat.sub_succ]
      exact hstep

/-- Differentiability of the `Dzd`-iterates of a `C^n` function of `z` alone. -/
private lemma differentiableAt_dzdIter_of_contDiffOn {u : ℝ → ℝ} {n : ℕ}
    (hu : ContDiffOn ℝ n u (Set.Ioi (0 : ℝ))) {b : ℕ} (hb : b + 1 ≤ n) {z : ℝ}
    (hz : 0 < z) : DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z := by
  have h := contDiffOn_dzdIter_of_contDiffOn hu b (by omega)
  have hne : (((n - b : ℕ)) : WithTop ℕ∞) ≠ 0 := by
    have hb0 : (n - b : ℕ) ≠ 0 := by omega
    exact_mod_cast hb0
  exact (h.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- The binomial coefficients `C(i,b)` for `i ≤ 6` are bounded by `2⁶ = 64`. -/
private lemma choose_cast_abs_le (i b : ℕ) (hi : i ≤ 6) :
    |((i.choose b : ℕ) : ℝ)| ≤ 64 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : i.choose b ≤ 64 := by
    have h26 : (2 : ℕ) ^ 6 = 64 := by norm_num
    have := Nat.choose_le_two_pow i b
    have := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hi
    omega
  exact_mod_cast h1

/-! ## The estimate -/

theorem ZopSlotMul_le : ∃ C : ℝ, 0 < C ∧ ∀ (φ u : ℝ → ℝ) (K : ℝ), 0 ≤ K →
    (∀ j ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j φ z| ≤ K) →
    ContDiffOn ℝ 6 φ (Set.Ioi (0 : ℝ)) → ContDiffOn ℝ 6 u (Set.Ioi (0 : ℝ)) →
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C * (1 + K) ^ 2 * (∑ q ∈ Finset.range 7,
            (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  refine ⟨2000000, by norm_num, ?_⟩
  intro φ u K hK hφb hφ hu z hz
  set W : ℝ := (Work.Spaces.w z) ^ 2 with hWdef
  set S : ℝ := ∑ k ∈ Finset.range 7, (Work.Elliptic.DzdIter k u z) ^ 2 * W with hS
  have hW : 0 ≤ W := by rw [hWdef]; exact sq_nonneg _
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) hW)
  -- the per-slot bound
  have hterm : ∀ q ≤ 6,
      (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * W ≤ 200704 * K ^ 2 * S := by
    intro q hq
    -- Leibniz
    have hleib := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz q φ u
      (fun b hb z' hz' =>
        differentiableAt_dzdIter_of_contDiffOn (n := 6) hφ (b := b) (by omega) hz')
      (fun b hb z' hz' =>
        differentiableAt_dzdIter_of_contDiffOn (n := 6) hu (b := b) (by omega) hz') z hz
    -- Cauchy–Schwarz on the binomial sum
    have hcs := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := q) (D := 64) (K := K) hK
      (x := fun b => Work.Elliptic.DzdIter b φ z)
      (y := fun m => Work.Elliptic.DzdIter m u z)
      (fun b hb => hφb b (by omega) z hz)
      (fun b hb => choose_cast_abs_le q b hq)
    -- shrink the two factors of `hcs`
    have hq7 : ((q : ℝ) + 1) ≤ 7 := by
      have : q ≤ 6 := hq
      exact_mod_cast (by omega : q + 1 ≤ 7)
    have hfac : ((q : ℝ) + 1) * 64 * K ≤ 448 * K := by
      have h64 : ((q : ℝ) + 1) * 64 ≤ 448 := by
        nlinarith [hq7]
      nlinarith [h64, hK]
    have hfac2 : (((q : ℝ) + 1) * 64 * K) ^ 2 ≤ (448 * K) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hfac 2
    have hsum_le : ∑ m ∈ Finset.range (q + 1), (Work.Elliptic.DzdIter m u z) ^ 2
        ≤ ∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun m hm => Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hm
          omega))
        (fun m _ _ => sq_nonneg _)
    have hstep : (∑ b ∈ Finset.range (q + 1),
          ((q.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b φ z
            * Work.Elliptic.DzdIter (q - b) u z)) ^ 2
        ≤ (448 * K) ^ 2 * (∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2) := by
      refine hcs.trans ?_
      refine mul_le_mul hfac2 hsum_le (Finset.sum_nonneg fun m _ => sq_nonneg _)
        (sq_nonneg (448 * K))
    -- multiply by the weight
    have hSW : (∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2) * W = S := by
      rw [hS, Finset.sum_mul]
    calc (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * W
        = (∑ b ∈ Finset.range (q + 1),
            ((q.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b φ z
              * Work.Elliptic.DzdIter (q - b) u z)) ^ 2 * W := by rw [hleib]
      _ ≤ ((448 * K) ^ 2 * (∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2)) * W :=
          mul_le_mul_of_nonneg_right hstep hW
      _ = (448 * K) ^ 2 * ((∑ m ∈ Finset.range 7, (Work.Elliptic.DzdIter m u z) ^ 2) * W) := by
          ring
      _ = (448 * K) ^ 2 * S := by rw [hSW]
      _ = 200704 * K ^ 2 * S := by ring
  -- sum the seven slots
  calc ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ ∑ _q ∈ Finset.range 7, 200704 * K ^ 2 * S :=
        Finset.sum_le_sum (fun q hq => hterm q (by
          have := Finset.mem_range.mp hq
          omega))
    _ = 7 * (200704 * K ^ 2 * S) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1404928 * K ^ 2 * S := by ring
    _ ≤ 2000000 * (1 + K) ^ 2 * S := by
        have hKsq : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith [hK]
        have h2 : 1404928 * K ^ 2 ≤ 2000000 * (1 + K) ^ 2 :=
          mul_le_mul (by norm_num) hKsq (sq_nonneg K) (by norm_num)
        exact mul_le_mul_of_nonneg_right h2 hSnn

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Analyticity of the profile on `(-1,∞)` -/

/-- `F_*` is a rational function whose only pole is at `z = -1`, hence analytic (order `⊤`)
on the half-line `(-1,∞)`. -/
theorem contDiffOn_FM_Fstar_analytic :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden
    (fun z hz => pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
  change ContDiffOn ℝ (⊤ : WithTop ℕ∞) ((fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2))
    (Set.Ioi (-1))
  exact h

/-! ## The closed form of the iterated derivatives -/

/-- **The one-step derivative of the closed form**: with
`φ_j(w) = 2·(-1)^j·j!·(w-j)/(1+w)^(j+2)`, one has `φ_j' = φ_{j+1}`. -/
theorem hasDerivAt_FM_Fstar_formula (j : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (w - (j : ℝ))
        / (1 + w) ^ (j + 2))
      (2 * (-1 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) * (z - ((j + 1 : ℕ) : ℝ))
        / (1 + z) ^ (j + 1 + 2)) z := by
  have hz' : (1 : ℝ) + z ≠ 0 := by simp only [Set.mem_Ioi] at hz; linarith
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (w - (j : ℝ)))
      (2 * (-1 : ℝ) ^ j * (j.factorial : ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - ((j : ℕ) : ℝ)) 1 z :=
      (hasDerivAt_id z).sub_const ((j : ℕ) : ℝ)
    have h2 := h.const_mul (2 * (-1 : ℝ) ^ j * (j.factorial : ℝ))
    simpa [mul_assoc] using h2
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (j + 2))
      (((j + 2 : ℕ) : ℝ) * (1 + z) ^ (j + 1)) z := by
    have h : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h.pow (j + 2)
    rw [show (fun w : ℝ => (1 + w) ^ (j + 2)) = (fun w : ℝ => 1 + w) ^ (j + 2) from by
      funext w; simp [Pi.pow_apply]]
    simpa using h2
  have hdiv := hnum.div hden (pow_ne_zero _ hz')
  convert hdiv using 1
  · have h1 : (1 + z) ^ (j + 1 + 2) = (1 + z) ^ (j + 1) * (1 + z) ^ 2 := by
      rw [show j + 1 + 2 = (j + 1) + 2 by omega, pow_add]
    have h2 : ((1 + z) ^ (j + 2)) ^ 2 = (1 + z) ^ (j + 2) * (1 + z) ^ (j + 2) := pow_two _
    have h3 : (1 + z) ^ (j + 2) = (1 + z) ^ (j + 1) * (1 + z) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    rw [h1, h2, h3]
    have hu : (1 + z) ^ (j + 1) ≠ 0 := pow_ne_zero _ hz'
    field_simp
    rw [show (-1 : ℝ) ^ (j + 1) = -(-1) ^ j by rw [pow_succ]; ring]
    rw [show ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) by
      rw [Nat.factorial_succ]; push_cast; ring]
    push_cast
    ring

/-- **The closed form of the iterated derivatives of the plain profile**:
`∂^j F_* z = 2·(-1)^j·j!·(z-j)/(1+z)^(j+2)` on `(-1,∞)`. -/
theorem deriv_iter_FM_Fstar_eq (j : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    deriv^[j] (fun z => Work.FM.Fstar z) z
      = 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (z - (j : ℝ)) / (1 + z) ^ (j + 2) := by
  induction j generalizing z with
  | zero =>
      rw [Function.iterate_zero_apply]
      simp only [Work.FM.Fstar]
      norm_num
  | succ n ih =>
      have hEqOn : Set.EqOn (deriv^[n] (fun z => Work.FM.Fstar z))
          (fun w : ℝ => 2 * (-1 : ℝ) ^ n * (n.factorial : ℝ) * (w - (n : ℝ))
            / (1 + w) ^ (n + 2)) (Set.Ioi (-1)) := fun w hw => ih hw
      rw [Function.iterate_succ_apply', hEqOn.deriv isOpen_Ioi hz]
      exact (hasDerivAt_FM_Fstar_formula n hz).deriv

/-! ## The slices of the iterated `z`-derivatives -/

/-- The iterated plain derivative of a function of `z` alone, as a `pzIter`. -/
theorem pzIter_zonly_eq_FM_deriv_iter (Φ : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Φ z) z θ = deriv^[k] Φ z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      congr 1
      funext z'
      exact ih z'

/-! ## The global bound `|z^k ∂_z^k F_* z| ≤ 2·k!·(k+1)` for `z ≥ 0` -/

/-- **The weighted plain derivatives of the profile are uniformly bounded on `[0,∞)`**:
`|z^k ∂_z^k F_* z| ≤ 2·k!·(k+1)` for every `z ≥ 0`.  (For `z ≥ 1` the sharper `O(1/z)`
bound is available in `Work.FTS.LocData6.FM_Fstar_jet_le6`; here we need the whole
half-line, including the endpoint `z = 0`.) -/
theorem zpow_deriv_FM_Fstar_le (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z| ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) := by
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos h1z _
  rw [deriv_iter_FM_Fstar_eq k hzI]
  have hrw : z ^ k * (2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - (k : ℝ)) / (1 + z) ^ (k + 2))
      = (-1 : ℝ) ^ k
          * (2 * (k.factorial : ℝ) * (z ^ k * (z - (k : ℝ))) / (1 + z) ^ (k + 2)) := by
    ring
  rw [hrw, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_div, abs_of_pos hden]
  have hnum : |2 * (k.factorial : ℝ) * (z ^ k * (z - (k : ℝ)))|
      = 2 * (k.factorial : ℝ) * (z ^ k * |z - (k : ℝ)|) := by
    rw [abs_mul, abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)),
      abs_of_nonneg (pow_nonneg hz k)]
  rw [hnum]
  rw [div_le_iff₀ hden]
  have h1 : z ^ k ≤ (1 + z) ^ k := pow_le_pow_left₀ hz (by linarith) k
  have h2 : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * (1 + z) ^ 2 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z, hz, hk0]
  have h3 : z ^ k * |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * (1 + z) ^ (k + 2) := by
    calc z ^ k * |z - (k : ℝ)| ≤ (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z) ^ 2) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = ((k : ℝ) + 1) * (1 + z) ^ (k + 2) := by rw [pow_add]; ring
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * (k.factorial : ℝ))
  linarith [h4]

/-! ## The Bell number of row `7` -/

/-- The Bell numbers of the rows `j ≤ 7` are at most `877` (`B₇ = 877`). -/
theorem bell_le_seven (j : ℕ) (hj : j ≤ 7) : Work.Spaces.bell j ≤ 877 := by
  interval_cases j <;> decide

/-! ## The jet bound -/

/-- **The first eight `D_z`-jets of `F_*` are uniformly bounded on `[0,∞)`.** -/
theorem FstarJet7 : ∃ M : ℝ, 0 < M ∧ ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter j Work.FM.Fstar z| ≤ M := by
  refine ⟨877 * (2 * ((Nat.factorial 7) : ℝ) * ((7 : ℝ) + 1)), ?_, ?_⟩
  · have h : (0 : ℝ) < ((Nat.factorial 7) : ℝ) := by exact_mod_cast Nat.factorial_pos 7
    positivity
  · intro j hj z hz
    have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
    have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by positivity⟩
    have hsmooth : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
      fun _ _ => contDiffOn_FM_Fstar_analytic
    rw [show Work.Elliptic.DzdIter j Work.FM.Fstar z
        = Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z 0 from
      (Work.Elliptic.DzIter_rad (fun z => Work.FM.Fstar z) j z 0).symm]
    rw [Work.Spaces.DzIter_eq_sum_scoef (h := fun z _ => Work.FM.Fstar z) hsmooth j z hzI 0 h0I]
    have hx : ∀ k ≤ j, |z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0|
        ≤ 2 * ((Nat.factorial 7) : ℝ) * ((7 : ℝ) + 1) := by
      intro k hk
      rw [pzIter_zonly_eq_FM_deriv_iter]
      refine (zpow_deriv_FM_Fstar_le k hz).trans ?_
      have hk7 : k ≤ 7 := le_trans hk hj
      have hfac : (k.factorial : ℝ) ≤ ((Nat.factorial 7) : ℝ) := by
        exact_mod_cast Nat.factorial_le hk7
      have hk1 : (k : ℝ) + 1 ≤ (7 : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk7
      have h2k : 2 * (k.factorial : ℝ) ≤ 2 * ((Nat.factorial 7) : ℝ) := by linarith
      exact mul_le_mul h2k hk1 (by linarith) (by positivity)
    have hsum := Work.Spaces.abs_sum_scoef_mul_le j
      (2 * ((Nat.factorial 7) : ℝ) * ((7 : ℝ) + 1))
      (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0) hx
    refine hsum.trans ?_
    have hbell : (Work.Spaces.bell j : ℝ) ≤ 877 := by
      exact_mod_cast bell_le_seven j hj
    have hM : (0 : ℝ) ≤ 2 * ((Nat.factorial 7) : ℝ) * ((7 : ℝ) + 1) := by
      have h : (0 : ℝ) ≤ ((Nat.factorial 7) : ℝ) := by
        exact_mod_cast (Nat.factorial_pos 7).le
      positivity
    exact mul_le_mul_of_nonneg_right hbell hM

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.mulExpansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

set_option quotPrecheck false in
/-- The product of the two restricted Lebesgue measures, as it appears throughout the flat
pairing estimates. -/
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

theorem mulExpansion {f g : ℝ → ℝ → ℝ} (a b : ℕ) (ρ : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hXY : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hterm : ∀ a₁ ≤ a, ∀ b₁ ≤ b, MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ f p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * g z θ) g
      = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
                * Work.Spaces.mixed b a g p.1 p.2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  -- Step 1: the slot pairing is the product-measure integral of the uncurried integrand.
  have hprod : Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * g z θ) g
      = ∫ p, ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2 ∂IPM := by
    rw [Work.FTS.TransportS.slotPairing]
    exact (MeasureTheory.integral_prod _ hXY).symm
  rw [hprod]
  -- Step 2: the Leibniz expansion of `D_z^bD_θ^a (f · g)`, a.e. on the open quadrant.
  have hpt : (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
      =ᵐ[IPM] (fun p : ℝ × ℝ =>
          ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                  * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
                  * Work.Spaces.mixed b a g p.1 p.2)) := by
    filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a f g hf hg p.1 p.2 hz hθ0 hθ1]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
    ring
  rw [MeasureTheory.integral_congr_ae hpt]
  -- Step 3: exchange the integral with the (finite) double sum.
  have key : ∀ a₁ ≤ a, ∀ b₁ ≤ b,
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2)) IPM :=
    fun a₁ ha₁ b₁ hb₁ => (hterm a₁ ha₁ b₁ hb₁).const_mul _
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun a₁ ha₁ => ?_
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun b₁ hb₁ => ?_
      exact MeasureTheory.integral_const_mul _ _
    · intro b₁ hb₁
      exact key a₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)) b₁
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))
  · intro a₁ ha₁
    exact MeasureTheory.integrable_finsetSum _ fun b₁ hb₁ =>
      key a₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)) b₁
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.divz_conj2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

theorem divz_conj2 (CΦ : ℝ) (hCΦpos : 0 < CΦ)
    (hCΦ : ∀ b : ℕ, b ≤ 6 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ CΦ * (z / (1 + z)))
    (hleib : ∀ (j i : ℕ) (G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen G →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
                * Work.Spaces.mixed (j - b) i G z θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (G : ℝ → ℝ → ℝ) (K : ℝ),
        Work.FTS.EllipticEst.SmoothOpen G →
        Work.Spaces.WlInfMem α 6 G → Work.Spaces.WlInf α 6 G ≤ K →
        ∀ j i : ℕ, 1 ≤ i → j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ|
            ≤ C * K * (z / (1 + z)) * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  -- The constant: `Σ_{b≤j} C(j,b) = 2^j ≤ 2^6 = 64` and the mixed-derivative bound carries
  -- `1000`, so `C = 100000·CΦ` suffices.
  refine ⟨100000 * CΦ, by positivity, ?_⟩
  intro α hα G K hG hGmem hGK j i hi hji z θ hz hθ0 hθpit
  have hαpos : 0 < α := hα.1
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθpit⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθpit⟩
  -- expand the Leibniz rule for the radial factor `z/(1+z)`
  rw [hleib j i G hG z θ hz hθ0 hθpit]
  set w : ℝ := z / (1 + z) with hw
  set Y : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) with hY
  have hz1 : (0:ℝ) < 1 + z := by linarith
  have hwpos : 0 < w := by rw [hw]; positivity
  have hwnn : 0 ≤ w := le_of_lt hwpos
  have hCΦnn : 0 ≤ CΦ := le_of_lt hCΦpos
  have hYnn : 0 ≤ Y := by
    rw [hY]
    exact mul_nonneg (by linarith [Work.Spaces.sin_two_nonneg' hθI])
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg' hθI) _)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 G :=
    Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hGmem
  have hKnn : 0 ≤ K := le_trans hWnn hGK
  -- each summand: the radial factor by `hCΦ`, the mixed derivative by `mixed_le_WlInf6`
  have hterm : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
          * Work.Spaces.mixed (j - b) i G z θ)|
        ≤ (j.choose b : ℝ) * ((CΦ * w) * (1000 * (K * Y))) := by
    intro b hb
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb6 : b ≤ 6 := by omega
    have h1 : |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ CΦ * w := by
      rw [hw]; exact hCΦ b hb6 z θ hz
    have h2 : |Work.Spaces.mixed (j - b) i G z θ| ≤ 1000 * (K * Y) := by
      have h2' := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 (α := α) hαpos hG hGmem
        (a := i) hi (b := j - b) (by omega) hz hθIoo
      refine le_trans h2' ?_
      have : Work.Spaces.WlInf α 6 G * Y ≤ K * Y := mul_le_mul_of_nonneg_right hGK hYnn
      exact mul_le_mul_of_nonneg_left this (by norm_num)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (j.choose b))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCΦnn hwnn)) (Nat.cast_nonneg _)
  have hsum1 : (∑ b ∈ Finset.range (j + 1),
        |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
          * Work.Spaces.mixed (j - b) i G z θ)|)
      ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * ((CΦ * w) * (1000 * (K * Y))) :=
    Finset.sum_le_sum hterm
  have hchoose : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) = (2:ℝ)^j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have h2j : (2:ℝ)^j ≤ 100 := by
    have hj6 : j ≤ 6 := by omega
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj6
    norm_num at h
    linarith
  have hprod : 0 ≤ (CΦ * w) * (K * Y) :=
    mul_nonneg (mul_nonneg hCΦnn hwnn) (mul_nonneg hKnn hYnn)
  refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) hsum1) ?_
  rw [← Finset.sum_mul, hchoose]
  calc (2:ℝ)^j * ((CΦ * w) * (1000 * (K * Y)))
      = 1000 * (2:ℝ)^j * ((CΦ * w) * (K * Y)) := by ring
    _ ≤ 1000 * 100 * ((CΦ * w) * (K * Y)) := by
        apply mul_le_mul_of_nonneg_right _ hprod
        exact mul_le_mul_of_nonneg_left h2j (by norm_num)
    _ = 100000 * CΦ * K * w * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
        rw [hY]; ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.WlInf_theta_only_level6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

/-!
# The `𝒲^{6,∞}`-bound for a function of `θ` alone

This is the level-`6` analogue of `Work.FTS.PhiStar.Psi0Est.WlInf_theta_only_six` (which is
the level-`5` statement).  For `F = fun _ θ => g θ` (a function of the angular variable
alone) all the radial derivatives `pzIter k F` vanish for `k ≥ 1`
(`pzIter_theta_only_succ`) and `DthIter j F = fun _ θ => dthU^[j] g θ` (`DthIter_theta_only`),
so in `WlInf α 6 F` only the slots with `k = 0` survive:

* the radial slot `k = 0` contributes `supAbs (fun _ θ => g θ) ≤ C`;
* the six angular slots `k = 0`, `1 ≤ j ≤ 6` contribute
  `supAbs (fun _ θ => dthU^[j] g θ · sin(2θ)^{-α/5}/(α + sin(2θ))) ≤ C` each;
* every slot with `k ≥ 1` is the supremum of the zero function.

Total `C + 6C = 7C`.
-/

/-- `∂_z^k` of a function of `θ` alone vanishes for `k ≥ 1`. -/
private lemma pzIter_theta_eq_zero (g : ℝ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Work.Spaces.pzIter k (fun _ θ => g θ) = fun _ _ => (0 : ℝ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact Work.FTS.PhiStar.Psi0Est.pzIter_theta_only_succ g k'

/-- `∂_z^k D_θ^j` of a function of `θ` alone vanishes for `k ≥ 1`. -/
private lemma pzIter_DthIter_theta_eq_zero (g : ℝ → ℝ) (j : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) = fun _ _ => (0 : ℝ) := by
  rw [Work.FTS.PhiStar.Psi0Est.DthIter_theta_only]
  exact pzIter_theta_eq_zero (Work.Spaces.dthU^[j] g) hk

/-- `|a·s/d| = |a|·s/d` for `s, d ≥ 0`. -/
private lemma abs_mul_div_of_nonneg {a s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) :
    |a * s / d| = |a| * s / d := by
  rw [abs_div, abs_mul, abs_of_nonneg hs, abs_of_nonneg hd]

/-- The angular slot with `k = 0` and order `1 ≤ j ≤ 6` is bounded by `C`. -/
private lemma angSlot_zero_le (α C : ℝ) (hα : 0 < α) (g : ℝ → ℝ)
    (hw : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] g θ| * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) ≤ C)
    {j : ℕ} (hj1 : 1 ≤ j) (hj6 : j ≤ 6) :
    Work.Spaces.supAbs (fun z θ => (z + 1) ^ 0
        * Work.Spaces.pzIter 0 (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ C := by
  refine Work.Spaces.supAbs_le (fun z _ θ hθ => ?_)
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hd : 0 ≤ α + Real.sin (2 * θ) := by linarith
  rw [Work.Spaces.pzIter_zero, Work.FTS.PhiStar.Psi0Est.DthIter_theta_only]
  simp only [pow_zero, one_mul]
  rw [abs_mul_div_of_nonneg (Real.rpow_nonneg hs _) hd]
  exact hw j hj1 hj6 θ hθ

private lemma sum7_ite_eq (C : ℝ) :
    (∑ k ∈ Finset.range 7, (if k = 0 then C else (0 : ℝ))) = C := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hbne
    rw [ite_eq_right hbne]
  · intro h
    exact absurd (Finset.mem_range.mpr (by norm_num : 0 < 7)) h

private lemma sum77_ite_eq (C : ℝ) :
    (∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
      (if k = 0 ∧ 1 ≤ j ∧ j ≤ 6 then C else (0 : ℝ))) = 6 * C := by
  have hinner : ∀ j : ℕ, (∑ k ∈ Finset.range 7,
      (if k = 0 ∧ 1 ≤ j ∧ j ≤ 6 then C else (0 : ℝ)))
      = (if 1 ≤ j ∧ j ≤ 6 then C else (0 : ℝ)) := by
    intro j
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hbne
      rw [ite_eq_right (fun h => hbne h.1)]
    · intro h
      exact absurd (Finset.mem_range.mpr (by norm_num : 0 < 7)) h
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  rw [Finset.sum_range_succ' (fun j => if 1 ≤ j ∧ j ≤ 6 then C else (0 : ℝ)) 6]
  have h0 : (if 1 ≤ (0 : ℕ) ∧ (0 : ℕ) ≤ 6 then C else (0 : ℝ)) = 0 := by norm_num
  rw [h0, add_zero]
  have hone : ∀ j ∈ Finset.range 6,
      (if 1 ≤ j + 1 ∧ j + 1 ≤ 6 then C else (0 : ℝ)) = C := by
    intro j hj
    have hj6 : j < 6 := Finset.mem_range.mp hj
    rw [ite_eq_left (by omega : 1 ≤ j + 1 ∧ j + 1 ≤ 6)]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num

/-- Sharp `𝒲^{6,∞}`-reduction for a function of `θ` alone. -/
theorem WlInf_theta_only_level6 (α C : ℝ) (hα : 0 < α) (hC : 0 < C) (g : ℝ → ℝ)
    (hg : ∀ θ ∈ Work.Spaces.Iθ, |g θ| ≤ C)
    (hw : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] g θ| * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) ≤ C) :
    Work.Spaces.WlInfMem α 6 (fun _ θ => g θ) ∧
      Work.Spaces.WlInf α 6 (fun _ θ => g θ) ≤ 7 * C := by
  have hC0 : 0 ≤ C := le_of_lt hC
  have hs2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  constructor
  · constructor
    · intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ hθ => ?_)
        simpa using hg θ hθ
      · have hk1 : 1 ≤ k := by omega
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (fun _ θ => g θ) z θ = 0 := by
          rw [pzIter_theta_eq_zero g hk1]
        rw [hz]
        simp only [mul_zero, abs_zero]
        exact hC0
    · intro j _ k _ hj1 hjk
      by_cases hk0 : k = 0
      · subst hk0
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ hθ => ?_)
        have hd : 0 ≤ α + Real.sin (2 * θ) := by linarith [hs2 θ hθ]
        rw [Work.Spaces.pzIter_zero, Work.FTS.PhiStar.Psi0Est.DthIter_theta_only]
        simp only [pow_zero, one_mul]
        rw [abs_mul_div_of_nonneg (Real.rpow_nonneg (hs2 θ hθ) _) hd]
        exact hw j hj1 (by omega) θ hθ
      · have hk1 : 1 ≤ k := by omega
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ = 0 := by
          rw [pzIter_DthIter_theta_eq_zero g j hk1]
        rw [hz]
        simp only [mul_zero, zero_mul, zero_div, abs_zero]
        exact hC0
  · rw [Work.Spaces.WlInf]
    have hS1 : (∑ k ∈ Finset.range (6 + 1), Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (fun _ θ => g θ) z θ)) ≤ C := by
      refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) (le_of_eq (sum7_ite_eq C))
      by_cases hk0 : k = 0
      · subst hk0
        rw [ite_eq_left rfl]
        refine Work.Spaces.supAbs_le (fun z _ θ hθ => ?_)
        simpa using hg θ hθ
      · have hk1 : 1 ≤ k := by omega
        rw [ite_eq_right hk0]
        refine Work.Spaces.supAbs_le (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (fun _ θ => g θ) z θ = 0 := by
          rw [pzIter_theta_eq_zero g hk1]
        rw [hz]
        simp
    have hS2 : (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
        if 1 ≤ j ∧ k + j ≤ 6 then Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ 6 * C := by
      refine le_trans (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_)))
        (le_of_eq (sum77_ite_eq C))
      by_cases h : 1 ≤ j ∧ k + j ≤ 6
      · rw [ite_eq_left h]
        have hj1 : 1 ≤ j := h.1
        have hj6 : j ≤ 6 := by omega
        by_cases hk0 : k = 0
        · subst hk0
          rw [ite_eq_left ⟨rfl, hj1, hj6⟩]
          exact angSlot_zero_le α C hα g hw hj1 hj6
        · have hk1 : 1 ≤ k := by omega
          rw [ite_eq_right (fun hh => hk0 hh.1)]
          refine Work.Spaces.supAbs_le (fun z _ θ _ => ?_)
          have hz : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ = 0 := by
            rw [pzIter_DthIter_theta_eq_zero g j hk1]
          rw [hz]
          simp
      · rw [ite_eq_right h]
        split_ifs with hh
        · exact hC0
        · exact le_refl 0
    linarith

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux.sliceIntSup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux


end Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.delicateBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.TransportS.T2Sup

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary real tools

These three tools are stated so that they require *no* measurability of the functions
involved; this is what keeps the final assembly free of side conditions. -/

/-- Young's inequality: `a b ≤ (t a² + b²/t)/2` for every `t > 0` (no sign hypothesis). -/
theorem delicate_amgm {a b t : ℝ} (ht : 0 < t) :
    a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
  have hsq : 0 ≤ (t * a - b) ^ 2 := sq_nonneg _
  have heq : (t * a ^ 2 + b ^ 2 / t) / 2 = (t ^ 2 * a ^ 2 + b ^ 2) / (2 * t) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  nlinarith [hsq]

/-- If `C ≤ (t A + B/t)/2` for every `t > 0` with `A, B ≥ 0`, then `C ≤ √(A B)`. -/
theorem delicate_le_sqrt_mul {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → C ≤ (t * A + B / t) / 2) : C ≤ Real.sqrt (A * B) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · rw [← hA0, zero_mul, Real.sqrt_zero]
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hspos : 0 < B / (2 * ε) + 1 := by positivity
    have h1 := h (B / (2 * ε) + 1) hspos
    rw [← hA0] at h1
    have hkey : B / (B / (2 * ε) + 1) ≤ 2 * ε := by
      have hden : 0 < B / (2 * ε) + 1 := by positivity
      rw [div_le_iff₀ hden]
      have hmul : (2 * ε) * (B / (2 * ε)) = B := by field_simp
      nlinarith [hmul]
    have h2 : (0 * 0 + B / (B / (2 * ε) + 1)) / 2 ≤ 0 + ε := by linarith
    linarith
  · rcases eq_or_lt_of_le hB with hB0 | hBpos
    · rw [← hB0, mul_zero, Real.sqrt_zero]
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have hspos : 0 < ε / A := by positivity
      have h1 := h (ε / A) hspos
      rw [← hB0, zero_div, add_zero] at h1
      have hkey : ε / A * A = ε := by field_simp
      have h2 : (ε / A * A + 0) / 2 ≤ ε + 0 := by rw [hkey]; linarith
      linarith
    · have hAsqrt : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
      have hBsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
      have hspos : 0 < Real.sqrt B / Real.sqrt A := div_pos hBsqrt hAsqrt
      have h1 := h (Real.sqrt B / Real.sqrt A) hspos
      have e1 : Real.sqrt B / Real.sqrt A * A = Real.sqrt A * Real.sqrt B := by
        field_simp
        rw [Real.sq_sqrt hA]
      have e2 : B / (Real.sqrt B / Real.sqrt A) = Real.sqrt A * Real.sqrt B := by
        field_simp
        rw [Real.sq_sqrt hB]
      have key : (Real.sqrt B / Real.sqrt A * A + B / (Real.sqrt B / Real.sqrt A)) / 2
          = Real.sqrt (A * B) := by
        rw [e1, e2, Real.sqrt_mul hA]
        ring
      linarith [h1, key]


/-- `σ^{-q} ≤ σ^{-γ}` for `0 < σ ≤ 1` and `q ≤ γ`. -/
theorem delicate_rpow_neg_le {σ q γ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (h : q ≤ γ) :
    σ ^ (-q) ≤ σ ^ (-γ) :=
  Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by linarith)

/-- `1 ≤ σ^{-γ}` for `0 < σ ≤ 1` and `0 ≤ γ`. -/
theorem delicate_one_le_rpow_neg {σ γ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hγ : 0 ≤ γ) :
    1 ≤ σ ^ (-γ) := by
  have h := Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (show -γ ≤ 0 by linarith)
  rwa [Real.rpow_zero] at h

/-- A.e. strong measurability of `θ ↦ σ(θ)^{-γ} v(θ)` on `Iθ` for `v` continuous on the open
interval. -/
theorem delicate_aesm_weight_mul {α : ℝ} {v : ℝ → ℝ}
    (hv : ContinuousOn v (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * v θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * v θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (((Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn).rpow_const ?_).mul hv
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by show (0 : ℝ) < 2 * θ; linarith [hθ.1])
      (by show 2 * θ < Real.pi; linarith [hθ.2, Real.pi_pos])))
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
  exact hcont.aestronglyMeasurable measurableSet_Ioo

/-- `x^{-β/2}` squared is `x^{-β}` (for `x ≥ 0`). -/
theorem delicate_sq_half_rpow {x β : ℝ} (hx : 0 ≤ x) : (x ^ (-(β) / 2)) ^ 2 = x ^ (-β) := by
  rw [sq]
  rcases eq_or_lt_of_le hx with h0 | h0
  · subst h0
    rcases eq_or_ne β 0 with hb | hb
    · subst hb
      norm_num
    · have h1 : -(β) / 2 ≠ 0 := by intro h; exact hb (by linarith)
      have h2 : -β ≠ 0 := by intro h; exact hb (by linarith)
      rw [Real.zero_rpow h1, Real.zero_rpow h2, mul_zero]
  · rw [← Real.rpow_add h0]
    ring_nf

/-- A four-factor product bound, all factors nonnegative. -/
theorem delicate_mul_four_le {a a' b b' c c' d d' : ℝ} (ha : a ≤ a') (hb : b ≤ b')
    (hc : c ≤ c') (hd : d ≤ d') (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') (hc'0 : 0 ≤ c') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0 ha'0
  have h2 : a * b * c ≤ a' * b' * c' := mul_le_mul h1 hc hc0 (mul_nonneg ha'0 hb'0)
  exact mul_le_mul h2 hd hd0 (mul_nonneg (mul_nonneg ha'0 hb'0) hc'0)

/-! ## The angular marginal `Ψ` -/

/-- The `θ`-marginal `Ψ(θ) = ∫_s w(s)² (D_z²D_θ g(s,θ))² ds` is a.e. strongly measurable
(it is the marginal of a function continuous on the open quadrant). -/
theorem delicate_psiTheta_aesm {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ => ∫ s in Work.Spaces.Iz,
        (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.mixed 2 1 g p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      simp only [Work.Spaces.w]
      exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2
    exact h1.mul ((hg.mixed 2 1).continuousOn.pow 2)
  have haesm := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.mixed 2 1 g p.1 p.2) ^ 2) hcont
  have h2 := haesm.prod_swap.integral_prod_right'
  simpa only [Function.uncurry, Prod.swap_prod_mk, Work.Spaces.Iz, Work.Spaces.Iθ] using h2

/-! ## The radial Hardy inequality on the slice `θ ↦ D_zD_θ g(·,θ)` -/



/-! ## The two `ℋ⁴`-slot bounds for the `g`-factors -/




end Work.FTS.TransportS.T2Sup
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.delicateMargInt =====
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

/-! ## Elementary angular facts -/

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem dmi_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
theorem dmi_sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The (nonnegative) target integrand. -/
theorem dmi_Fnonneg (α q : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
      * |Work.Spaces.mixed 3 1 g z θ| :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _)) (abs_nonneg _))
    (abs_nonneg _)) (abs_nonneg _)

/-- Almost every angle of `Iθ` is interior. -/
theorem dmi_ae_mem_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- Almost every radius of `Iz` is strictly positive. -/
theorem dmi_ae_pos_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iz]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The angular weight algebra -/

/-- `x ^ 2` as a real power. -/
theorem dmi_natpow_two (x : ℝ) : x ^ (2 : ℕ) = x ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
  exact (Real.rpow_natCast x 2).symm

/-- `σ^{-γ/2}·σ^{-γ/2} = σ^{-γ}`. -/
theorem dmi_rpow_half_mul {γ σ : ℝ} (hσ : 0 < σ) :
    σ ^ (-(γ / 2)) * σ ^ (-(γ / 2)) = σ ^ (-γ) := by
  rw [← Real.rpow_add hσ]
  congr 1
  ring

/-- `(σ^{-γ/2})² = σ^{-γ}`. -/
theorem dmi_rpow_half_sq {γ σ : ℝ} (hσ : 0 < σ) : (σ ^ (-(γ / 2))) ^ 2 = σ ^ (-γ) := by
  rw [dmi_natpow_two (σ ^ (-(γ / 2)))]
  rw [← Real.rpow_mul (le_of_lt hσ)]
  congr 1
  ring

/-- `σ^{-γ}(σX)² = X²σ^{2-γ}` for `σ > 0`. -/
theorem dmi_mul_sq {γ σ X : ℝ} (hσ : 0 < σ) :
    σ ^ (-γ) * (σ * X) ^ 2 = X ^ 2 * σ ^ (2 - γ) := by
  have h1 : (σ * X) ^ 2 = σ ^ (2 : ℝ) * X ^ 2 := by
    rw [mul_pow, dmi_natpow_two σ]
  rw [h1]
  rw [show (2 - γ : ℝ) = (-γ) + 2 from by ring, Real.rpow_add hσ]
  ring

/-- For `σ ∈ (0,1]` and `0 ≤ q ≤ γ` the weights compare: `σ^{-q} ≤ σ^{-γ}`. -/
theorem dmi_rpow_le {q γ σ : ℝ} (hq0 : 0 ≤ q) (hqγ : q ≤ γ) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) : σ ^ (-q) ≤ σ ^ (-γ) := by
  have hγ : 0 ≤ γ := le_trans hq0 hqγ
  rcases eq_or_lt_of_le hq0 with h | h
  · rw [← h, neg_zero, Real.rpow_zero]
    have hstep : σ ^ (0 : ℝ) ≤ σ ^ (-γ) :=
      Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by linarith)
    rwa [Real.rpow_zero] at hstep
  · exact Work.FTS.TransportS.SlotT2.rpow_neg_mono (le_of_lt hσ0) hσ1 h hqγ

/-- The `L²`–`L²` Cauchy–Schwarz inequality in its square-root form for the angular interval. -/
theorem dmi_cs_Iθ {u v : ℝ → ℝ}
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hv : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hu0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ u θ) (hv0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ v θ) :
    (∫ θ in Work.Spaces.Iθ, u θ * v θ)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, u θ ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, v θ ^ 2) := by
  have hsq := Work.Spaces.cs_integral hu hv
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, u θ ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ (fun θ _ => sq_nonneg _)
  have hL : 0 ≤ ∫ θ in Work.Spaces.Iθ, u θ * v θ :=
    MeasureTheory.setIntegral_nonneg hIθ (fun θ hθ => mul_nonneg (hu0 θ hθ) (hv0 θ hθ))
  calc (∫ θ in Work.Spaces.Iθ, u θ * v θ)
      = Real.sqrt ((∫ θ in Work.Spaces.Iθ, u θ * v θ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hL]
    _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, u θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, v θ ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, u θ ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, v θ ^ 2) := Real.sqrt_mul hA _

/-! ## Continuity of the auxiliary multipliers on the open quadrant -/

/-- `(z,θ) ↦ z^…`-free radial weight `w z` is continuous on the open quadrant. -/
theorem dmi_continuousOn_w :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  simp only [Work.Spaces.w]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

/-- `(z,θ) ↦ sin(2θ)^c` is continuous on the open quadrant. -/
theorem dmi_continuousOn_sin_pow (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
  intro p hp
  exact Or.inl (ne_of_gt (dmi_sin_two_pos hp.2))

/-! ## The main statement -/


end Work.FTS.TransportS.T2Sup
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.integrableOnSliceDelicate =====
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

theorem integrableOnSliceDelicate {α : ℝ} {f g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmf : Work.Spaces.HkMem α 4 f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
        * |Work.Spaces.mixed 3 1 g z θ|) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  -- the bound `K` for the `f`-factor, constant in `θ`
  set K : ℝ := Real.sqrt (Work.FTS.TransportS.SlotT2.supOpenBfun α f 3 z) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; exact Real.sqrt_nonneg _
  -- (1) the `f`-factor is dominated by `K` for almost every (indeed every interior) `θ`
  have hAbnd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.DzIter 3 f z θ| ≤ K := by
    rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have h := Work.FTS.TransportS.SlotT2.supOpen_slice_bound (b := 3) hf hmf hα hα1
      (by norm_num) hz θ hθ
    rw [hKdef, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  -- (2) the two `g`-slots are integrable against the full weight `canonW γ`
  have hB : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 1 1 g z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.TransportS.SlotT2.mslot_slice_integrable (Work.Spaces.gam_pos hα) le_rfl hg hmg 1 1
      le_rfl (by norm_num) hzIz
  have hC : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.TransportS.SlotT2.mslot_slice_integrable (Work.Spaces.gam_pos hα) le_rfl hg hmg 3 1
      le_rfl (by norm_num) hzIz
  -- (3) the majorant is integrable
  have hmajint : MeasureTheory.IntegrableOn (fun θ => (K / 2) *
      (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 1 1 g z θ) ^ 2
      + Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2)) Work.Spaces.Iθ :=
    (hB.add hC).const_mul (K / 2)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
        * |Work.Spaces.mixed 3 1 g z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) p.1 p.2
        * |Work.Spaces.DzIter 3 f p.1 p.2| * |Work.Spaces.mixed 1 1 g p.1 p.2|
        * |Work.Spaces.mixed 3 1 g p.1 p.2|) ?_ hz
    exact (((Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)).mul
      ((hf.DzIter 3).continuousOn.abs)).mul
      ((hg.mixed 1 1).continuousOn.abs)).mul
      ((hg.mixed 3 1).continuousOn.abs)
  refine MeasureTheory.Integrable.mono' hmajint haesm ?_
  filter_upwards [hAbnd, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθA hθI
  have hcw : 0 ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ :=
    Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
  have hnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
      * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
      * |Work.Spaces.mixed 3 1 g z θ| :=
    mul_nonneg (mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  -- the AM–GM step in `θ`
  have hamgm : |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|
      ≤ ((Work.Spaces.mixed 1 1 g z θ) ^ 2 + (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2 := by
    have h := two_mul_le_add_sq |Work.Spaces.mixed 1 1 g z θ| |Work.Spaces.mixed 3 1 g z θ|
    rw [sq_abs, sq_abs] at h
    linarith
  calc Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
        * |Work.Spaces.mixed 3 1 g z θ|
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (|Work.Spaces.DzIter 3 f z θ|
          * (|Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|)) := by ring
    _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (K * (((Work.Spaces.mixed 1 1 g z θ) ^ 2
          + (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcw
        exact mul_le_mul hθA hamgm (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hKnn
    _ = (K / 2) * (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 1 1 g z θ) ^ 2
      + Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2) := by ring

end Work.FTS.TransportS.T2Sup
end
end
-- ===== merged: Submission.Work.FTS.TransportS.t2Slice =====
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
set_option maxHeartbeats 1600000

/-! ## `SmoothQuad` implies `SmoothOpen` (`Work.FTS.TransportS.smoothOpen_of_smoothQuad`) -/

/-! ## A.e. strong measurability of the slice of `Heasy` -/


/-! ## Integrability of the `ℋ⁴`-integrand of `g` on the slice -/


/-! ## Integrability of the easy energy `EasyU` on the slice -/


/-! ## The main theorem -/


end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.HkMem_fatou =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Fatou for the `ℋ^k`-membership along a pointwise-convergent sequence

`Work.FTS_EllLimOK.HkMem_fatou` complements `Work.FTS_EllLimOK.HkSq_le_of_JConv` (which is the
`HkSq`-half of the same argument): from

* `HkMem α k (un n)` for every `n`,
* `HkSq α k (un n) ≤ C` for every `n`,
* a uniform bound `∫_θ HkIntegrand α k (un n) z θ ≤ C` on every angular slice `z ∈ Iz`,
* a.e. measurability of the uncurried limit integrand, and
* pointwise convergence of all mixed slots `D_z^j D_θ^i (un n) → D_z^j D_θ^i u` on the open
  quadrant,

it concludes both `HkMem α k u` *and* `HkSq α k u ≤ C`.

The proof is Fatou's lemma in the angular variable (which, together with `hTheta`, gives the
finiteness of every angular slice, hence the first half of `HkMem`) followed by Fatou's lemma in
the radial variable (giving the bound on the iterated integral).  At the two boundary lines
`z = 0` and `sin (2θ) = 0` the integrand vanishes identically, so the convergence hypothesis is
needed only on the open quadrant `Q0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! ## Auxiliary facts about the angular interval -/

/-- Almost every `θ ∈ Iθ = [0, π/2]` lies in the open interval `(0, π/2)`: only the two
endpoints are exceptional, and they form a null set. -/
theorem HkMem_fatou_ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hnull : MeasureTheory.volume (Work.Spaces.Iθ \ Set.Ioo (0 : ℝ) (π / 2)) = 0 := by
    have hsub : Work.Spaces.Iθ \ Set.Ioo (0 : ℝ) (π / 2) ⊆ ({0, π / 2} : Set ℝ) := by
      intro θ hθ
      rw [Set.mem_sdiff] at hθ
      obtain ⟨⟨h0, h2⟩, hnot⟩ := hθ
      rw [Set.mem_Ioo, not_and_or] at hnot
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hnot with h | h
      · left; exact le_antisymm (le_of_not_gt h) h0
      · right; exact le_antisymm h2 (le_of_not_gt h)
    refine MeasureTheory.measure_mono_null hsub ?_
    rw [show ({0, π / 2} : Set ℝ) = {0} ∪ {π / 2} from by
      ext θ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    exact MeasureTheory.measure_union_null (Real.volume_singleton (a := 0))
      (Real.volume_singleton (a := π / 2))
  rw [MeasureTheory.ae_restrict_iff' hIθ, MeasureTheory.ae_iff]
  rw [show {θ : ℝ | ¬(θ ∈ Work.Spaces.Iθ → θ ∈ Set.Ioo (0 : ℝ) (π / 2))}
      = Work.Spaces.Iθ \ Set.Ioo (0 : ℝ) (π / 2) from by
    ext θ; simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_imp]]
  exact hnull

/-- The `ℋ^k`-integrand of the sequence converges a.e. in `θ`, for every `z ∈ Iz`, as soon as all
mixed slots converge pointwise on the open quadrant.  At `z = 0` (where `w 0 = 0`) and at
`sin (2θ) = 0` both integrands vanish identically, which is why the convergence hypothesis is
only needed on `Q0`. -/
theorem HkMem_fatou_ae_tendsto {α : ℝ} {k : ℕ} {un : ℕ → ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hconv : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (un n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i u z θ)))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (un n) z θ) Filter.atTop
        (nhds (Work.Spaces.HkIntegrand α k u z θ)) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    refine Filter.Eventually.of_forall fun θ => ?_
    have h1 : (fun n => Work.Spaces.HkIntegrand α k (un n) 0 θ) = fun _ => (0 : ℝ) := by
      funext n; exact HkIntegrand_fst_zero α k (un n) θ
    rw [h1, HkIntegrand_fst_zero α k u θ]
    exact tendsto_const_nhds
  · refine (HkMem_fatou_ae_mem_Ioo_Iθ).mono fun θ hθ => ?_
    exact tendsto_HkIntegrand_of_tendsto_mixed (p := (z, θ))
      (fun j i hji => hconv j i hji z θ (by
        rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hzpos, hθ.1, hθ.2⟩))

/-! ## The main theorem -/


end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.JConvAux.ae_tendsto_HkIntegrand_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JConvAux.ae_tendsto_HkIntegrand_slice` — the integrand converges

The `ℋ^k`-integrand `HkIntegrand α k f z θ` is a finite sum of squares of terms
`slot · weight(z,θ)`, where `slot` runs over the mixed derivatives `D_z^j D_θ^i f` with
`j + i ≤ k` (and `mixed i 0 = DzIter i` supplies the first sum).  Hence, at a fixed `(z,θ)`,
convergence of the slots gives convergence of the integrand.  Off the open quadrant the weights
degenerate (`w 0 = 0`, so both sums vanish at `z = 0`; `sin(2θ) = 0` kills the denominators and
every mixed slot with `i ≥ 1`, which is why no positivity of `α` is needed), so the statement
holds at *every* point of `Iz × Iθ`, in particular a.e.

The elementary ingredients (`tendsto_HkIntegrand_of_tendsto_mixed` and the two degeneracy lemmas
`HkIntegrand_fst_zero`, `HkIntegrand_eq_zero_of_sin_eq_zero`) are the helpers of
`FTS_EllLimOK.HkSq_le_of_JConv`, whose proof uses this statement in turn.
-/
open scoped Real Topology
open MeasureTheory Filter

namespace Work.FTS_EllLimOK.JConvAux


end Work.FTS_EllLimOK.JConvAux
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.hB_locR8 =====
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

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The order-`8` jet bound of the profile `F_*(z) = 2z/(1+z)²`

The `k`-th derivative of the profile has the closed form
`∂_z^k F_* = 2(-1)^k k! (z-k)/(1+z)^(k+2)` (`GkerT`); the Stirling expansion of `D_z^b`
(`Work.Spaces.DzIter_eq_sum_scoef`) then bounds every `D_z`-jet by `bell b` times the
`z^j ∂_z^j`-bound, which decays like `1/z`. -/

/-- **The closed form of the `k`-th derivative of the profile** `F_*(z) = 2z/(1+z)²`:
`GkerT k z = 2·(-1)^k·k!·(z-k)/(1+z)^(k+2)`.  This is a local copy of
`Work.FTS.LocData.Gker` (whose module declares a `T1` clashing with the one of
`DzIter_bumpZ_bound`), proved independently here. -/
noncomputable def GkerT (k : ℕ) (z : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2)

@[simp] theorem GkerT_apply (k : ℕ) (z : ℝ) :
    GkerT k z = 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2) := rfl

/-- `GkerT 0` is the profile itself. -/
theorem GkerT_zero (z : ℝ) : GkerT 0 z = Work.FM.Fstar z := by
  simp only [GkerT_apply, Work.FM.Fstar]
  norm_num

/-- The unfolded form of the one-step recursion: `∂_z (2(-1)^k k!(z-k)/(1+z)^(k+2)) =
2(-1)^(k+1)(k+1)!(z-k-1)/(1+z)^(k+3)` off the pole `z = -1`. -/
theorem hasDerivAt_GkerT_aux (k : ℕ) {z : ℝ} (hz : 1 + z ≠ 0) :
    HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (w - (k : ℝ))
        / (1 + w) ^ (k + 2))
      (2 * (-1 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (z - ((k : ℝ) + 1))
        / (1 + z) ^ (k + 3)) z := by
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (w - (k : ℝ)))
      (2 * (-1 : ℝ) ^ k * (k.factorial : ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - (k : ℝ)) 1 z := (hasDerivAt_id z).sub_const _
    simpa [smul_eq_mul, mul_assoc] using h.const_mul (2 * (-1) ^ k * (k.factorial : ℝ))
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (k + 2))
      (((k : ℝ) + 2) * (1 + z) ^ (k + 1)) z := by
    have hsub : k + 2 - 1 = k + 1 := by omega
    have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ (k + 2))
        (((k : ℝ) + 2) * (1 + z) ^ (k + 1)) z := by
      have h1 := (((hasDerivAt_id (x := z)).const_add (1 : ℝ)).pow (k + 2))
      refine h1.congr_deriv ?_
      rw [hsub]
      simp only [id_eq, Nat.cast_add, mul_one]
      ring
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w; simp
    · ring
  have hp : (1 + z) ^ (k + 2) ≠ 0 := pow_ne_zero _ hz
  refine (hnum.fun_div hden hp).congr_deriv ?_
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- **The one-step recursion of the closed forms**: `∂_z (GkerT k) = GkerT (k+1)` off the pole
`z = -1`. -/
theorem hasDerivAt_GkerT (k : ℕ) {z : ℝ} (hz : 1 + z ≠ 0) :
    HasDerivAt (GkerT k) (GkerT (k + 1) z) z := by
  have hfun : GkerT k
      = fun w : ℝ => 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (w - (k : ℝ)) / (1 + w) ^ (k + 2) :=
    rfl
  rw [hfun]
  refine (hasDerivAt_GkerT_aux k hz).congr_deriv ?_
  simp only [GkerT_apply, Nat.cast_add, Nat.cast_one]

/-- **The `pzIter`s of the profile are the closed forms `GkerT`.** -/
theorem pzIter_Fstar_eq_GkerT (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) (θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z θ = GkerT k z := by
  induction k generalizing z with
  | zero => exact (GkerT_zero z).symm
  | succ k ih =>
      have hzlt : (-1 : ℝ) < z := hz
      have hne : (1 : ℝ) + z ≠ 0 := by linarith
      have hev : (fun w : ℝ => Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) w θ)
          =ᶠ[𝓝 z] GkerT k := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih hw
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz, Filter.EventuallyEq.deriv_eq hev]
      exact (hasDerivAt_GkerT k hne).deriv

/-- **The far-field decay of `z^k·GkerT k z`**, for `z ≥ 1` and every order `k`:
`|z^k·GkerT k z| ≤ 2·k!·(k+1)/z`. -/
theorem abs_zpow_mul_GkerT_le (k : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |z ^ k * GkerT k z| ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / z := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hzpow : (0 : ℝ) ≤ z ^ k := pow_nonneg hz0.le k
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos hz1 _
  have hkR : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * z := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    constructor <;> nlinarith [hz]
  have hsign : z ^ k * GkerT k z =
      (-1 : ℝ) ^ k * (2 * (k.factorial : ℝ) * z ^ k * (z - (k : ℝ)) / (1 + z) ^ (k + 2)) := by
    rw [GkerT_apply]
    ring
  rw [hsign, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_of_nonneg hfac,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hzpow]
  have step1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) / (1 + z) ^ (k + 2) := by
    gcongr
  have step2 : 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / z := by
    rw [div_le_div_iff₀ hden hz0]
    have h1 : 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) * z
        = 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) * z ^ (k + 2) := by
      rw [pow_add]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0.le (by linarith) (k + 2))
      (by positivity)
  linarith

/-- The `z`-slices of the profile are smooth on `(-1,∞)` (the only pole of `2z/(1+z)²` is
`z = -1`). -/
theorem contDiffOn_Fstar_self : ContDiffOn ℝ ⊤ (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hne : ∀ z : ℝ, z ∈ Set.Ioi (-1) → (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have hlt : (-1 : ℝ) < z := hz
    exact pow_ne_zero 2 (by linarith)
  refine (hnum.div hden hne).congr ?_
  intro z _
  simp only [Pi.div_apply, Work.FM.Fstar]

/-- For a function of `z` alone, every `D_z`-iterate is independent of `θ`. -/
theorem DzIter_zonly_theta_indep_self (Φ : ℝ → ℝ) (b : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter b (fun z _ => Φ z) z θ = Work.Spaces.DzIter b (fun z _ => Φ z) z θ' := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Spaces.DzIter b (fun z _ => Φ z) z' θ)
          = (fun z' => Work.Spaces.DzIter b (fun z _ => Φ z) z' θ') from
        funext fun z' => ih z']

/-- The iterated plain derivative of a function of `z` alone, as a `pzIter`. -/
theorem pzIter_zonly_eq_deriv_iter_self (Φ : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Φ z) z θ = deriv^[k] Φ z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      congr 1
      funext z'
      exact ih z'

/-- **The far-field bound for every `D_z`-iterate of the profile**: for `z ≥ 1` and every order
`b`, `|D_z^b F_*(z)| ≤ bell b · 2·b!·(b+1)/z`. -/
theorem DzIter_Fstar_le_general_self (b : ℕ) {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ|
      ≤ (Work.Spaces.bell b : ℝ) * (2 * (b.factorial : ℝ) * ((b : ℝ) + 1) / z) := by
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hsm : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ ⊤
      (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
    fun θ _ => contDiffOn_Fstar_self
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_rfl, by positivity⟩
  rw [DzIter_zonly_theta_indep_self (fun z => Work.FM.Fstar z) b z θ 0]
  rw [Work.Spaces.DzIter_eq_sum_scoef hsm b z hzmem 0 h0I]
  refine Work.Spaces.abs_sum_scoef_mul_le b (2 * (b.factorial : ℝ) * ((b : ℝ) + 1) / z)
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0) ?_
  intro k hk
  rw [pzIter_zonly_eq_deriv_iter_self (fun z => Work.FM.Fstar z) k z 0]
  have hker : deriv^[k] (fun z : ℝ => Work.FM.Fstar z) z = GkerT k z := by
    rw [← pzIter_zonly_eq_deriv_iter_self (fun z => Work.FM.Fstar z) k z 0]
    exact pzIter_Fstar_eq_GkerT k hzmem 0
  rw [hker]
  refine (abs_zpow_mul_GkerT_le k hz).trans ?_
  have hkfac : (k.factorial : ℝ) ≤ (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hk
  have hk1 : (k : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk
  gcongr

/-- The Bell numbers of the rows `j ≤ 8` are at most `9000` (`B_8 = 4140`). -/
theorem bell_le_9000_of_le_eight (j : ℕ) (hj : j ≤ 8) : Work.Spaces.bell j ≤ 9000 := by
  interval_cases j <;> decide

/-- **The `D_z`-jets of the profile decay like `1/z`, up to order `8`.** -/
theorem FM_Fstar_jet_le8_self :
    ∃ CF : ℝ, 0 < CF ∧ ∀ j ≤ 8, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z := by
  refine ⟨6531840000, by norm_num, fun j hj z hz θ => ?_⟩
  have hzpos : (0 : ℝ) < z := by linarith
  refine (DzIter_Fstar_le_general_self j hz θ).trans ?_
  have hbell : (Work.Spaces.bell j : ℝ) ≤ 9000 := by
    exact_mod_cast bell_le_9000_of_le_eight j hj
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ 40320 := by
    have h := Nat.factorial_le hj
    have h8 : (Nat.factorial 8 : ℕ) = 40320 := by decide
    rw [h8] at h
    exact_mod_cast h
  have hj1 : (j : ℝ) + 1 ≤ 9 := by
    have h : j + 1 ≤ 8 + 1 := Nat.succ_le_succ hj
    have hR : ((j + 1 : ℕ) : ℝ) ≤ ((8 + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    linarith
  have hfac0 : (0 : ℝ) ≤ ((j.factorial : ℕ) : ℝ) := by positivity
  have hj10 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hnum : 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ 725760 := by
    have h1 : ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ 40320 * 9 :=
      mul_le_mul hfac hj1 hj10 (by norm_num)
    nlinarith [h1]
  have hB : 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z ≤ 725760 / z :=
    div_le_div_of_nonneg_right hnum hzpos.le
  have hBnn : 0 ≤ 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z := by positivity
  calc (Work.Spaces.bell j : ℝ) * (2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z)
      ≤ 9000 * (725760 / z) := mul_le_mul hbell hB hBnn (by norm_num)
    _ = 6531840000 / z := by ring

/-! ## 2. Smoothness of a function of `z` alone on the strip `(-1,∞) × ℝ` -/

/-- A function of `z` alone, viewed as a function of `(z,θ)`, is jointly `C^n` on `(-1,∞) × ℝ`
as soon as its `z`-slice is `C^n` on `(-1,∞)` (the `θ`-variable is a dummy, so no restriction
on `θ` is needed). -/
theorem contDiffOn_uncurry_zOnly {n : ℕ} {φ : ℝ → ℝ}
    (h : ContDiffOn ℝ n φ (Set.Ioi (-1))) :
    ContDiffOn ℝ n (Function.uncurry (fun z (_ : ℝ) => φ z)) (Set.Ioi (-1) ×ˢ Set.univ) := by
  have hfun : Function.uncurry (fun z (_ : ℝ) => φ z) = fun p : ℝ × ℝ => φ p.1 := by
    funext p; rfl
  rw [hfun]
  exact h.comp contDiffOn_fst (fun p hp => hp.1)

/-! ## 3. The `D_z`-jets of `zfarR L` on `[L,∞)`, at order `8` -/

/-- **The `D_z`-jets of the far factor decay like `1/z` on `[L,∞)`.**  On `[L,2L]` the Leibniz
bound `zfarR_jet_le8_of_jets` applies; beyond `2L` the cut-off factor is `1`, so `zfarR L`
agrees with `FM.Fstar` on a neighbourhood of `z` and the profile bound transfers by
`DzIter_z_congr_of_eventuallyEq`. -/
theorem zfarR_jet_le8_Ici {Cu Cv : ℝ} (hCu1 : 1 ≤ Cu) (hCv : 0 < Cv)
    (hCu : ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 8 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu)
    (hCvM : ∀ a : ℕ, a ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ| ≤ Cv / z) :
    ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 8 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ|
        ≤ max (256 * Cu * Cv) Cv / z := by
  intro L hL j hj z hz θ
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpos : 0 < z := lt_of_lt_of_le hLpos hz
  by_cases h : z ≤ 2 * L
  · have h1 := zfarR_jet_le8_of_jets hCu1 hCv hCu hCvM L hL j hj z ⟨hz, h⟩ θ
    exact h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt hzpos))
  · push_neg at h
    have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = Work.FM.Fstar z' := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds h] with z' hz'
      exact Work.FTS.LocDataExt.zfarR_eq_FM_Fstar_of_ge hLpos (le_of_lt hz')
    rw [Work.FTS.LocDataExt.DzIter_z_congr_of_eventuallyEq hev j θ]
    have h1 := hCvM j hj z (by linarith) θ
    exact h1.trans (div_le_div_of_nonneg_right (le_max_right _ _) (le_of_lt hzpos))

/-- **The unconditional order-`8` jet bound of the far factor on `[L,∞)`**: there is `A > 0`
such that `|D_z^j (zfarR L) z| ≤ A/z` for every `L ≥ 1`, `j ≤ 8`, `z ≥ L` and `θ`. -/
theorem zfarR_jet_le8_clean_Ici :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 8 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z := by
  obtain ⟨Cu, hCu1, hCu⟩ := oneSubChi_jet_le8
  obtain ⟨Cv, hCvpos, hCvle⟩ := FM_Fstar_jet_le8_self
  exact ⟨max (256 * Cu * Cv) Cv, lt_of_lt_of_le hCvpos (le_max_right _ _),
    zfarR_jet_le8_Ici hCu1 hCvpos hCu hCvle⟩

/-- **The radial bound of the far summand** `-(α/c)·zfarR L` at order `8`: from the jet bound
`|D_z^j (zfarR L) z| ≤ A/z` on `z ≥ L` (below `L` the cut-off kills the whole expression). -/
theorem hB_zfar8 (α L : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hAz : ∀ j ≤ 8, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z) :
    ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
          z θ * Work.Spaces.w z) ^ 2
        ≤ ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  rw [Work.FTS.LocDataExt.DzIter_const_mul]
  have hsplit : ((-(α / Work.Spaces.c α)
        * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2
      = (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 := by
    ring
  rw [hsplit]
  have hmain : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2 ≤ A ^ 2 * 64 / (1 + z) ^ 2 := by
    by_cases hzL : z < L
    · -- the cut-off vanishes near `z`
      have hzabs : |z| < L := by rw [abs_of_nonneg hz]; exact hzL
      have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = 0 := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hzabs] with z' hz'
        rw [Work.FTS.LocDataExt.zfarR_apply, Work.Stability.chi_eq_one (by
          rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
          exact le_of_lt hz')]
        ring
      have hzero : Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ = 0 :=
        Work.FTS.LocData.ZFBase.DzIter_eq_zero_of_eventually_zero
          (hev.mono (fun z' hz' => fun _ => hz')) j
      rw [hzero]
      have : 0 ≤ A ^ 2 * 64 / (1 + z) ^ 2 :=
        div_nonneg (mul_nonneg (sq_nonneg A) (by norm_num)) (sq_nonneg _)
      simpa using this
    · push_neg at hzL
      have hzpos : 0 < z := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hL) hzL
      have h1 := hAz j hj z hzL θ
      have h2 : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 ≤ (A / z * Work.Spaces.w z) ^ 2 := by
        rw [mul_pow, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h3 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at h3
      refine h2.trans ?_
      have hnum : (1 + z) ^ 4 / z ^ 6 ≤ 64 / (1 + z) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 6)
          (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
        have h : (1 + z) ^ 6 ≤ 64 * z ^ 6 := by
          have h1 : 1 + z ≤ 2 * z := by linarith
          calc (1 + z) ^ 6 ≤ (2 * z) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
            _ = 64 * z ^ 6 := by ring
        nlinarith [h]
      calc (A / z * Work.Spaces.w z) ^ 2 = A ^ 2 * ((1 + z) ^ 4 / z ^ 6) := by
            rw [Work.Spaces.w]
            field_simp <;> ring
        _ ≤ A ^ 2 * (64 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hnum (sq_nonneg A)
        _ = A ^ 2 * 64 / (1 + z) ^ 2 := by ring
  calc (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 / (1 + z) ^ 2 := by ring

/-! ## 4. The bump `bumpZ` at order `8` -/

/-- The `D_z`-jets of the bump `bumpZ = χ(4·-5)` up to order `8` are bounded. -/
theorem DzIter_bumpZ_bound8 :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 8 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => Work.FTS.LocData.bumpZ z) z θ| ≤ C := by
  classical
  refine ⟨∑ c ∈ Finset.range 9,
    Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c), ?_⟩
  intro c hc z _ θ
  have hM : ∀ d : ℕ, 0 ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) ∧
      ∀ w : ℝ, |(Work.FTS.LocData.T1^[d]) Work.FTS.LocData.bumpZ w|
        ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    fun d => Classical.choose_spec (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d)
  rw [Work.FTS.LocData.DzIter_bumpZ_eq c θ z]
  have h1 : |(Work.FTS.LocData.T1^[c]) Work.FTS.LocData.bumpZ z|
      ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c) := (hM c).2 z
  have h2 : Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c)
      ≤ ∑ d ∈ Finset.range 9,
          Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    Finset.single_le_sum (fun d _ => (hM d).1) (Finset.mem_range.mpr (by omega))
  linarith

/-- The radial bound needed by the assembly for the bump `bumpZ`, at order `8`. -/
theorem hB_bumpZ8 :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 := by
  obtain ⟨D, hD⟩ := DzIter_bumpZ_bound8
  have hD0 : 0 ≤ D := by
    have h := hD 0 (by norm_num) 0 (by simp [Work.Spaces.Iz]) 0
    have h1 : |Work.Spaces.DzIter 0 (fun z _ => Work.FTS.LocData.bumpZ z) 0 0| = 0 := by
      rw [Work.FTS.LocData.DzIter_bumpZ_eq 0 0 0, Function.iterate_zero_apply,
        Work.FTS.LocData.bumpZ_zero, abs_zero]
    linarith [h1 ▸ h]
  refine ⟨D ^ 2 * (1771561 / 1296 : ℝ), by positivity, fun j hj z hz θ => ?_⟩
  by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · have hw := Work.FTS.LocData.w_sq_le_on_support hsupp
    have h1 : (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2 ≤ D ^ 2 := by
      have h := hD j hj z hz θ
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at h2
    rw [mul_pow]
    calc (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ D ^ 2 * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) :=
          mul_le_mul h1 hw (sq_nonneg _) (by positivity)
      _ = D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by ring
  · rw [Work.FTS.LocData.DzIter_bumpZ_eq j θ z,
      Work.FTS.LocData.T1_iterate_bumpZ_eq_zero hsupp j]
    have hD2 : 0 ≤ D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg D) (by norm_num)) (sq_nonneg _)
    simpa using hD2

/-! ## 5. The target -/

theorem hB_locR8 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
          * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
  classical
  obtain ⟨A, hApos, hAz⟩ := zfarR_jet_le8_clean_Ici
  obtain ⟨R₂, hR₂0, hR₂⟩ := hB_bumpZ8
  have hzfar := hB_zfar8 α L (le_of_lt hApos) hL (hAz L hL)
  refine ⟨2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) + β ^ 2 * R₂) + 1, by positivity,
    fun j hj z hz θ => ?_⟩
  -- the two summands of `locR`
  have hsub : (fun z (_ : ℝ) => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
      + (fun z (_ : ℝ) => β * Work.FTS.LocData.bumpZ z)
      = fun z (_ : ℝ) => Work.FTS.LocDataExt.locR α L β z := by
    funext z θ
    simp only [Pi.add_apply, Work.FTS.LocDataExt.locR_apply]
  -- joint smoothness of the two summands on a strip containing `(z,θ)`
  have hφ1 : ContDiffOn ℝ 8
      (fun z : ℝ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
      (Set.Ioi (-1)) :=
    ((ContDiffOn.const_smul (-(α / Work.Spaces.c α))
      (Work.FTS.LocDataExt.contDiffOn_zfarR L)).congr
        (fun z _ => by simp [smul_eq_mul])).of_le (by simp)
  have hφ2 : ContDiffOn ℝ 8 (fun z : ℝ => β * Work.FTS.LocData.bumpZ z) (Set.Ioi (-1)) :=
    ((ContDiffOn.const_smul β (Work.FTS.LocData.BumpZ_contDiff.contDiffOn)).congr
      (fun z _ => by simp [smul_eq_mul])).of_le (by simp)
  have hz0 : (0 : ℝ) ≤ z := hz
  have hmem : (z, θ) ∈ Set.Ioi (-1) ×ˢ Set.univ := by
    refine ⟨?_, trivial⟩
    show (-1 : ℝ) < z
    linarith
  have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.DzIter_add_of_contDiffOn
    (f₁ := fun z (_ : ℝ) => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
    (f₂ := fun z (_ : ℝ) => β * Work.FTS.LocData.bumpZ z)
    (V := Set.Ioi (-1) ×ˢ Set.univ) (n := 8) (isOpen_Ioi.prod isOpen_univ)
    (contDiffOn_uncurry_zOnly hφ1) (contDiffOn_uncurry_zOnly hφ2) j hj (z, θ) hmem
  have hloc : Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
      = Work.Spaces.DzIter j
          (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z) z θ
        + Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ := by
    rw [← hsub]
    exact hadd
  -- the two bounds
  have hzfb := hzfar j hj z hz θ
  have hbmp : (Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ
      * Work.Spaces.w z) ^ 2 ≤ β ^ 2 * R₂ / (1 + z) ^ 2 := by
    rw [Work.FTS.LocDataExt.DzIter_const_mul]
    rw [show (β * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
          * Work.Spaces.w z) ^ 2
        = β ^ 2 * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
            * Work.Spaces.w z) ^ 2) from by ring]
    calc β ^ 2 * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
            * Work.Spaces.w z) ^ 2)
        ≤ β ^ 2 * (R₂ / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left (hR₂ j hj z hz θ) (sq_nonneg β)
      _ = β ^ 2 * R₂ / (1 + z) ^ 2 := by ring
  -- put the two together
  rw [hloc]
  set X := Work.Spaces.DzIter j
    (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z) z θ with hX
  set Y := Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ with hY
  have hden : (0 : ℝ) < (1 + z) ^ 2 := pow_pos (by linarith) 2
  have hsq : ((X + Y) * Work.Spaces.w z) ^ 2
      ≤ 2 * (X * Work.Spaces.w z) ^ 2 + 2 * (Y * Work.Spaces.w z) ^ 2 := by
    nlinarith [sq_nonneg (X * Work.Spaces.w z - Y * Work.Spaces.w z)]
  calc ((X + Y) * Work.Spaces.w z) ^ 2
      ≤ 2 * (X * Work.Spaces.w z) ^ 2 + 2 * (Y * Work.Spaces.w z) ^ 2 := hsq
    _ ≤ 2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2)
        + 2 * (β ^ 2 * R₂ / (1 + z) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hzfb (by norm_num))
          (mul_le_mul_of_nonneg_left hbmp (by norm_num))
    _ = (2 * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 + β ^ 2 * R₂)) / (1 + z) ^ 2 := by ring
    _ ≤ (2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) + β ^ 2 * R₂) + 1) / (1 + z) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hden)

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.hB_locR8_of_FMjet =====
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

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Aiding lemmas -/

/-- A function of `z` alone, viewed as a function of `(z,θ)`, is jointly `C^n` on the strip
`(-1,∞) × ℝ` as soon as its `z`-slice is `C^n` on `(-1,∞)` (the `θ`-variable is a dummy, so no
restriction on `θ` is needed). -/
theorem contDiffOn_uncurry_zOnly_FMjet {n : ℕ} {φ : ℝ → ℝ}
    (h : ContDiffOn ℝ n φ (Set.Ioi (-1))) :
    ContDiffOn ℝ n (Function.uncurry (fun z (_ : ℝ) => φ z)) (Set.Ioi (-1) ×ˢ Set.univ) := by
  have hfun : Function.uncurry (fun z (_ : ℝ) => φ z) = fun p : ℝ × ℝ => φ p.1 := by
    funext p; rfl
  rw [hfun]
  exact h.comp contDiffOn_fst (fun p hp => hp.1)

/-! ## The `D_z`-jets of `zfarR L` on `[L,∞)`, at order `8` -/

/-- **The `D_z`-jets of the far factor decay like `1/z` on `[L,∞)`.**  On `[L,2L]` the Leibniz
bound `zfarR_jet_le8_of_jets` applies; beyond `2L` the cut-off factor is `1`, so `zfarR L`
agrees with `FM.Fstar` on a neighbourhood of `z` and the profile bound `hCvM` transfers by
`DzIter_z_congr_of_eventuallyEq`. -/
theorem zfarR_jet_le8_Ici_FMjet {Cu Cv : ℝ} (hCu1 : 1 ≤ Cu) (hCv : 0 < Cv)
    (hCu : ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 8 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu)
    (hCvM : ∀ a : ℕ, a ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ| ≤ Cv / z) :
    ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 8 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ|
        ≤ max (256 * Cu * Cv) Cv / z := by
  intro L hL j hj z hz θ
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpos : 0 < z := lt_of_lt_of_le hLpos hz
  by_cases h : z ≤ 2 * L
  · have h1 := zfarR_jet_le8_of_jets hCu1 hCv hCu hCvM L hL j hj z ⟨hz, h⟩ θ
    exact h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt hzpos))
  · push_neg at h
    have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = Work.FM.Fstar z' := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds h] with z' hz'
      exact Work.FTS.LocDataExt.zfarR_eq_FM_Fstar_of_ge hLpos (le_of_lt hz')
    rw [Work.FTS.LocDataExt.DzIter_z_congr_of_eventuallyEq hev j θ]
    have h1 := hCvM j hj z (by linarith) θ
    exact h1.trans (div_le_div_of_nonneg_right (le_max_right _ _) (le_of_lt hzpos))

/-- **The unconditional order-`8` jet bound of the far factor on `[L,∞)`**: there is `A > 0`
such that `|D_z^j (zfarR L) z| ≤ A/z` for every `L ≥ 1`, `j ≤ 8`, `z ≥ L` and `θ`, assuming the
profile jet bound. -/
theorem zfarR_jet_le8_clean_Ici_FMjet {CF : ℝ} (hCF : 0 < CF)
    (hF : ∀ j : ℕ, j ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 8 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z := by
  obtain ⟨Cu, hCu1, hCu⟩ := oneSubChi_jet_le8
  exact ⟨max (256 * Cu * CF) CF, lt_of_lt_of_le hCF (le_max_right _ _),
    zfarR_jet_le8_Ici_FMjet hCu1 hCF hCu hF⟩

/-- **The radial bound of the far summand** `-(α/c)·zfarR L` at order `8`: from the jet bound
`|D_z^j (zfarR L) z| ≤ A/z` on `z ≥ L` (below `L` the cut-off kills the whole expression). -/
theorem hB_zfar8_FMjet (α L : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hAz : ∀ j ≤ 8, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z) :
    ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
          z θ * Work.Spaces.w z) ^ 2
        ≤ ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  rw [Work.FTS.LocDataExt.DzIter_const_mul]
  have hsplit : ((-(α / Work.Spaces.c α)
        * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2
      = (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 := by
    ring
  rw [hsplit]
  have hmain : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2 ≤ A ^ 2 * 64 / (1 + z) ^ 2 := by
    by_cases hzL : z < L
    · -- the cut-off vanishes near `z`
      have hzabs : |z| < L := by rw [abs_of_nonneg hz]; exact hzL
      have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = 0 := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hzabs] with z' hz'
        rw [Work.FTS.LocDataExt.zfarR_apply, Work.Stability.chi_eq_one (by
          rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
          exact le_of_lt hz')]
        ring
      have hzero : Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ = 0 :=
        Work.FTS.LocData.ZFBase.DzIter_eq_zero_of_eventually_zero
          (hev.mono (fun z' hz' => fun _ => hz')) j
      rw [hzero]
      have : 0 ≤ A ^ 2 * 64 / (1 + z) ^ 2 :=
        div_nonneg (mul_nonneg (sq_nonneg A) (by norm_num)) (sq_nonneg _)
      simpa using this
    · push_neg at hzL
      have hzpos : 0 < z := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hL) hzL
      have h1 := hAz j hj z hzL θ
      have h2 : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 ≤ (A / z * Work.Spaces.w z) ^ 2 := by
        rw [mul_pow, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h3 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at h3
      refine h2.trans ?_
      have hnum : (1 + z) ^ 4 / z ^ 6 ≤ 64 / (1 + z) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 6)
          (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
        have h : (1 + z) ^ 6 ≤ 64 * z ^ 6 := by
          have h1 : 1 + z ≤ 2 * z := by linarith
          calc (1 + z) ^ 6 ≤ (2 * z) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
            _ = 64 * z ^ 6 := by ring
        nlinarith [h]
      calc (A / z * Work.Spaces.w z) ^ 2 = A ^ 2 * ((1 + z) ^ 4 / z ^ 6) := by
            rw [Work.Spaces.w]
            field_simp <;> ring
        _ ≤ A ^ 2 * (64 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hnum (sq_nonneg A)
        _ = A ^ 2 * 64 / (1 + z) ^ 2 := by ring
  calc (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 / (1 + z) ^ 2 := by ring

/-! ## The bump `bumpZ` at order `8` -/

/-- The `D_z`-jets of the bump `bumpZ = χ(4·-5)` up to order `8` are bounded. -/
theorem DzIter_bumpZ_bound8_FMjet :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 8 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => Work.FTS.LocData.bumpZ z) z θ| ≤ C := by
  classical
  refine ⟨∑ c ∈ Finset.range 9,
    Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c), ?_⟩
  intro c hc z _ θ
  have hM : ∀ d : ℕ, 0 ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) ∧
      ∀ w : ℝ, |(Work.FTS.LocData.T1^[d]) Work.FTS.LocData.bumpZ w|
        ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    fun d => Classical.choose_spec (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d)
  rw [Work.FTS.LocData.DzIter_bumpZ_eq c θ z]
  have h1 : |(Work.FTS.LocData.T1^[c]) Work.FTS.LocData.bumpZ z|
      ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c) := (hM c).2 z
  have h2 : Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c)
      ≤ ∑ d ∈ Finset.range 9,
          Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    Finset.single_le_sum (fun d _ => (hM d).1) (Finset.mem_range.mpr (by omega))
  linarith

/-- The radial bound needed by the assembly for the bump `bumpZ`, at order `8`. -/
theorem hB_bumpZ8_FMjet :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 := by
  obtain ⟨D, hD⟩ := DzIter_bumpZ_bound8_FMjet
  have hD0 : 0 ≤ D := by
    have h := hD 0 (by norm_num) 0 (by simp [Work.Spaces.Iz]) 0
    have h1 : |Work.Spaces.DzIter 0 (fun z _ => Work.FTS.LocData.bumpZ z) 0 0| = 0 := by
      rw [Work.FTS.LocData.DzIter_bumpZ_eq 0 0 0, Function.iterate_zero_apply,
        Work.FTS.LocData.bumpZ_zero, abs_zero]
    linarith [h1 ▸ h]
  refine ⟨D ^ 2 * (1771561 / 1296 : ℝ), by positivity, fun j hj z hz θ => ?_⟩
  by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · have hw := Work.FTS.LocData.w_sq_le_on_support hsupp
    have h1 : (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2 ≤ D ^ 2 := by
      have h := hD j hj z hz θ
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at h2
    rw [mul_pow]
    calc (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ D ^ 2 * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) :=
          mul_le_mul h1 hw (sq_nonneg _) (by positivity)
      _ = D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by ring
  · rw [Work.FTS.LocData.DzIter_bumpZ_eq j θ z,
      Work.FTS.LocData.T1_iterate_bumpZ_eq_zero hsupp j]
    have hD2 : 0 ≤ D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg D) (by norm_num)) (sq_nonneg _)
    simpa using hD2

/-! ## The target -/

theorem hB_locR8_of_FMjet (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    {CF : ℝ} (hCF : 0 < CF)
    (hF : ∀ j : ℕ, j ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
          * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
  classical
  obtain ⟨A, hApos, hAz⟩ := zfarR_jet_le8_clean_Ici_FMjet hCF hF
  obtain ⟨R₂, hR₂0, hR₂⟩ := hB_bumpZ8_FMjet
  have hzfar := hB_zfar8_FMjet α L (le_of_lt hApos) hL (hAz L hL)
  have hRnn : 0 ≤ 2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) + β ^ 2 * R₂) + 1 := by
    have h1 : 0 ≤ (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 := by positivity
    have h2 : 0 ≤ β ^ 2 * R₂ := mul_nonneg (sq_nonneg β) hR₂0
    linarith
  refine ⟨_, hRnn, fun j hj z hz θ => ?_⟩
  -- the two summands of `locR`
  have hsub : (fun z (_ : ℝ) => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
      + (fun z (_ : ℝ) => β * Work.FTS.LocData.bumpZ z)
      = fun z (_ : ℝ) => Work.FTS.LocDataExt.locR α L β z := by
    funext z θ
    simp only [Pi.add_apply, Work.FTS.LocDataExt.locR_apply]
  -- joint smoothness of the two summands on a strip containing `(z,θ)`
  have hφ1 : ContDiffOn ℝ 8
      (fun z : ℝ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
      (Set.Ioi (-1)) :=
    ((ContDiffOn.const_smul (-(α / Work.Spaces.c α))
      (Work.FTS.LocDataExt.contDiffOn_zfarR L)).congr
        (fun z _ => by simp [smul_eq_mul])).of_le (WithTop.coe_le_coe.mpr le_top)
  have hφ2 : ContDiffOn ℝ 8 (fun z : ℝ => β * Work.FTS.LocData.bumpZ z) (Set.Ioi (-1)) :=
    ((ContDiffOn.const_smul β (Work.FTS.LocData.BumpZ_contDiff.contDiffOn)).congr
      (fun z _ => by simp [smul_eq_mul])).of_le (WithTop.coe_le_coe.mpr le_top)
  have hmem : (z, θ) ∈ Set.Ioi (-1) ×ˢ Set.univ :=
    ⟨show -1 < z by have hz0 : (0 : ℝ) ≤ z := hz; linarith, trivial⟩
  have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.DzIter_add_of_contDiffOn
    (f₁ := fun z (_ : ℝ) => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
    (f₂ := fun z (_ : ℝ) => β * Work.FTS.LocData.bumpZ z)
    (V := Set.Ioi (-1) ×ˢ Set.univ) (n := 8) (isOpen_Ioi.prod isOpen_univ)
    (contDiffOn_uncurry_zOnly_FMjet hφ1) (contDiffOn_uncurry_zOnly_FMjet hφ2) j hj (z, θ) hmem
  have hloc : Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
      = Work.Spaces.DzIter j
          (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z) z θ
        + Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ := by
    rw [← hsub]
    exact hadd
  -- the two bounds
  have hzfb := hzfar j hj z hz θ
  have hbmp : (Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ
      * Work.Spaces.w z) ^ 2 ≤ β ^ 2 * R₂ / (1 + z) ^ 2 := by
    rw [Work.FTS.LocDataExt.DzIter_const_mul]
    rw [show (β * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
          * Work.Spaces.w z) ^ 2
        = β ^ 2 * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
            * Work.Spaces.w z) ^ 2) from by ring]
    calc β ^ 2 * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
            * Work.Spaces.w z) ^ 2)
        ≤ β ^ 2 * (R₂ / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left (hR₂ j hj z hz θ) (sq_nonneg β)
      _ = β ^ 2 * R₂ / (1 + z) ^ 2 := by ring
  -- put the two together
  rw [hloc]
  set X := Work.Spaces.DzIter j
    (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z) z θ with hX
  set Y := Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ with hY
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by
    have hz0 : (0 : ℝ) ≤ z := hz
    positivity
  have hsq : ((X + Y) * Work.Spaces.w z) ^ 2
      ≤ 2 * (X * Work.Spaces.w z) ^ 2 + 2 * (Y * Work.Spaces.w z) ^ 2 := by
    nlinarith [sq_nonneg (X * Work.Spaces.w z - Y * Work.Spaces.w z)]
  calc ((X + Y) * Work.Spaces.w z) ^ 2
      ≤ 2 * (X * Work.Spaces.w z) ^ 2 + 2 * (Y * Work.Spaces.w z) ^ 2 := hsq
    _ ≤ 2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2)
        + 2 * (β ^ 2 * R₂ / (1 + z) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hzfb (by norm_num))
          (mul_le_mul_of_nonneg_left hbmp (by norm_num))
    _ = (2 * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 + β ^ 2 * R₂)) / (1 + z) ^ 2 := by ring
    _ ≤ (2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) + β ^ 2 * R₂) + 1) / (1 + z) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hden)

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.dthIter_coef_mul_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- **The finite-order Leibniz rule for `D_θ` against an angular coefficient.**

`D_θ = sin(2θ) ∂_θ` is a derivation on `θ`-slices, so its `i`-th iterate of a product
`(z,θ) ↦ c θ · X z θ` (coefficient depending on `θ` alone) expands binomially:

`D_θ^i (c·X) = ∑_{k≤i} C(i,k) · (D_θ^k c) · (D_θ^{i-k} X)` on the open quadrant `Q0`,

as soon as the two factors are `C^i` on `Q0`.  (The hypothesis is deliberately finite-order:
the analytic-order Leibniz rule `Work.Spaces.DthIter_mul` requires `C^ω` and is not applicable
to merely `C^i` data.)

This is the `j = 0` instance of the mixed Leibniz rule `mixed_mul_fin`
(`Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin`): `mixed 0 i` is `D_θ^i` by definition, and
a coefficient which does not depend on `z` has vanishing `D_z`-jets. -/
theorem dthIter_coef_mul_eqOn {i : ℕ} {c : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ i (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hc : ContDiffOn ℝ i (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => c θ * X z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ * Work.Spaces.DthIter (i - k) X z θ)))
      Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  -- The coefficient `(z,θ) ↦ c θ` and `X` are `C^i` on `Q0`; `mixed_mul_fin` with `j = 0`
  -- asks for `C^{0+i}`, which is the same regularity (`0 + i = i`).
  have hf : ContDiffOn ℝ (↑(0 : ℕ) + ↑i) (Function.uncurry (fun z θ : ℝ => c θ))
      Work.FTS.EllipticEst.Q0 := by
    rw [Nat.cast_zero, zero_add]
    change ContDiffOn ℝ (↑i) (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0
    exact hc
  have hg : ContDiffOn ℝ (↑(0 : ℕ) + ↑i) (Function.uncurry X) Work.FTS.EllipticEst.Q0 := by
    rw [Nat.cast_zero, zero_add]
    exact hX
  have h := Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin (j := 0) (i := i)
      (f := fun z θ => c θ) (g := X) (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 hf hg z θ hp
  -- `mixed 0 i` is `D_θ^i`, so the two sides now have the same shape.
  change Work.Spaces.mixed 0 i (fun z θ => c θ * X z θ) z θ
      = ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ * Work.Spaces.DthIter (i - k) X z θ)
  rw [h]
  -- Collapse the inner `range (0+1)`-sum (only `b = 0` survives) and clear the
  -- binomial coefficient `(0 choose 0) = 1`.
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_range_one]
  simp only [Work.Spaces.mixed_zero_left, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one]
  ring

end Work.FTS_RegExport.RXT.Slots.JetCalc
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

noncomputable section

open MeasureTheory Set Filter

/-- **The `Θ`-slots of the profile `F`.**  Given the uniform bounds and the differentiability of
the `D_z`-jets of `L₁₂ F` (order `≤ 2`) and of `𝔽K F` (`≤ 1`), together with the level-one
identity `z ∂_z(L₁₂ F) = -𝔽K F` on `(0,∞)`, the three `Θ`-slots

* `Uop α (Theta α F)/sin(2θ)`,
* `L₁₂ F · c2m`,
* `Vop (Theta α F)`

have uniformly bounded mixed jets of order `≤ 2` on the open quadrant. -/
theorem theta_part_theta {α CL : ℝ} (hαG : 0 < α) (hCL0 : 0 < CL) {F : ℝ → ℝ → ℝ}
    (hL12jet : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 F z) z| ≤ CL)
    (hFKjet : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.FK F z) z| ≤ CL)
    (hL12diff : ∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Construction.L12 F z)) z)
    (hFKdiff : ∀ b : ℕ, b ≤ 1 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK F z)) z)
    (hL12d : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 F z') z = -Work.Construction.FK F z) :
    ∃ C : ℝ, 0 < C ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop α (Work.Construction.Theta α F)
          z θ / Real.sin (2 * θ)) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 F z
          * Work.Construction.c2m θ) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop (Work.Construction.Theta α F)) z θ| ≤ C) := by
  set C2 : ℝ := (3 / (4 * α)) * CL + (1 / 4) * CL with hC2
  set C3 : ℝ := 1000 * CL with hC3
  set C4 : ℝ := 1000 * ((1 / (2 * α)) * CL) with hC4
  have hC2pos : 0 < C2 := by
    rw [hC2]
    have := mul_pos (by positivity : (0:ℝ) < 3 / (4 * α)) hCL0
    linarith
  have hC4pos : 0 < C4 := by rw [hC4]; positivity
  have hConj3 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 F z
        * Work.Construction.c2m θ) z θ| ≤ C3 := by
    intro j i hji z θ hz hθ0 hθ1
    have hcomm : (fun z θ => Work.Construction.L12 F z * Work.Construction.c2m θ)
        = fun z θ => Work.Construction.c2m θ * Work.Construction.L12 F z := by
      funext z θ; ring
    rw [hcomm, Work.FTS.Nonlinear.Pieces.mixed_ang_rad (fun θ => Work.Construction.c2m θ)
      (fun z => Work.Construction.L12 F z) j i z θ]
    rw [abs_mul]
    have hang : |Work.Spaces.DthIter i (fun x θ' => Work.Construction.c2m θ') 0 θ| ≤ 1000 := by
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        rw [Work.Spaces.DthIter_zero, Work.Construction.c2m]
        have h1 : |Real.cos (2 * θ)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
        have h2 : Real.sin θ ^ 2 ≤ 1 := by
          have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
          nlinarith [sq_abs (Real.sin θ), abs_nonneg (Real.sin θ)]
        calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
            ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
              rw [sub_eq_add_neg]
              exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))
          _ = |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by
              rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
          _ ≤ 1 + 1 := add_le_add h1 h2
          _ = 2 := by norm_num
          _ ≤ 1000 := by norm_num
      · have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi (by omega) θ
        have hsin2 : Real.sin (2 * θ) ^ (2 : ℝ) ≤ 1 :=
          Real.rpow_le_one (Real.sin_pos_of_pos_of_lt_pi (by linarith)
            (by linarith [Real.pi_pos])).le (Real.sin_le_one _) (by norm_num)
        linarith [h, mul_le_mul_of_nonneg_left hsin2 (by norm_num : (0:ℝ) ≤ 1000)]
    rw [hC3]
    linarith [abs_nonneg (Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z),
      hL12jet j (by omega) z hz,
      mul_le_mul hang (hL12jet j (by omega) z hz) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1000)]
  have hConj4 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Vop (Work.Construction.Theta α F)) z θ| ≤ C4 := by
    intro j i hji z θ hz hθ0 hθ1
    have hEqOn : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Vop
          (Work.Construction.Theta α F) z θ))
        (Function.uncurry (fun z θ => Work.Construction.c2m θ
          * ((1 / (2 * α)) * Work.Construction.L12 F z)))
        Work.Construction.Qd := by
      intro p hp
      obtain ⟨hz', hθ0', hθ1'⟩ := hp
      have hOp := Work.FTS_RegExport.RXT.SysAux.Theta_ops hαG (F := F) hL12d p.1 p.2 hz' hθ0' hθ1'
      show Work.Construction.Vop (Work.Construction.Theta α F) p.1 p.2
        = Work.Construction.c2m p.2 * ((1 / (2 * α)) * Work.Construction.L12 F p.1)
      have h2α : (2 : ℝ) * α ≠ 0 := by positivity
      have hU' : Work.Construction.Vop (Work.Construction.Theta α F) p.1 p.2 * (2 * α)
          = Work.Construction.c2m p.2 * Work.Construction.L12 F p.1 := by
        linarith [hOp.1]
      rw [show Work.Construction.c2m p.2 * ((1 / (2 * α)) * Work.Construction.L12 F p.1)
          = Work.Construction.c2m p.2 * Work.Construction.L12 F p.1 / (2 * α) from by ring,
        eq_div_iff h2α]
      linarith [hU']
    have hmix := Work.FTS_RegExport.RXT.SysAux.mixed_congr_of_isOpen isOpen_Qd hEqOn j i z θ
      ⟨hz, hθ0, hθ1⟩
    rw [hmix, Work.FTS.Nonlinear.Pieces.mixed_ang_rad (fun θ => Work.Construction.c2m θ)
      (fun z => (1 / (2 * α)) * Work.Construction.L12 F z) j i z θ]
    rw [abs_mul]
    have hval' : Work.Elliptic.DzdIter j (fun z => (1 / (2 * α)) * Work.Construction.L12 F z) z
        = (1 / (2 * α)) * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z :=
      congrFun (DzdIter_const_mul j (1 / (2 * α)) (fun z => Work.Construction.L12 F z)) z
    rw [hval', abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * α))]
    have hang : |Work.Spaces.DthIter i (fun x θ' => Work.Construction.c2m θ') 0 θ| ≤ 1000 := by
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        rw [Work.Spaces.DthIter_zero, Work.Construction.c2m]
        have h1 : |Real.cos (2 * θ)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
        have h2 : Real.sin θ ^ 2 ≤ 1 := by
          have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
          nlinarith [sq_abs (Real.sin θ), abs_nonneg (Real.sin θ)]
        calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
            ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
              rw [sub_eq_add_neg]
              exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))
          _ = |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by
              rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
          _ ≤ 1 + 1 := add_le_add h1 h2
          _ = 2 := by norm_num
          _ ≤ 1000 := by norm_num
      · have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi (by omega) θ
        have hsin2 : Real.sin (2 * θ) ^ (2 : ℝ) ≤ 1 :=
          Real.rpow_le_one (Real.sin_pos_of_pos_of_lt_pi (by linarith)
            (by linarith [Real.pi_pos])).le (Real.sin_le_one _) (by norm_num)
        linarith [h, mul_le_mul_of_nonneg_left hsin2 (by norm_num : (0:ℝ) ≤ 1000)]
    rw [hC4]
    calc |Work.Spaces.DthIter i (fun x θ' => Work.Construction.c2m θ') 0 θ|
          * ((1 / (2 * α)) * |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z|)
        = (1 / (2 * α)) * (|Work.Spaces.DthIter i (fun x θ' => Work.Construction.c2m θ') 0 θ|
            * |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z|) := by ring
      _ ≤ (1 / (2 * α)) * (1000 * CL) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hang (hL12jet j (by omega) z hz) (abs_nonneg _)
            (by norm_num : (0:ℝ) ≤ 1000)) (by positivity)
      _ = 1000 * ((1 / (2 * α)) * CL) := by ring
  have hConj2 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop α (Work.Construction.Theta α F)
        z θ / Real.sin (2 * θ)) z θ| ≤ C2 := by
    intro j i hji z θ hz hθ0 hθ1
    have hEqOn : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Uop α
          (Work.Construction.Theta α F) z θ / Real.sin (2 * θ)))
        (Function.uncurry (fun z _ => -(3 / (4 * α)) * Work.Construction.L12 F z
          + (1 / 4) * Work.Construction.FK F z)) Work.Construction.Qd := by
      intro p hp
      obtain ⟨hz', hθ0', hθ1'⟩ := hp
      have hsin : Real.sin (2 * p.2) ≠ 0 := ne_of_gt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
      have hOp := Work.FTS_RegExport.RXT.SysAux.Theta_ops hαG (F := F) hL12d p.1 p.2 hz' hθ0' hθ1'
      show Work.Construction.Uop α (Work.Construction.Theta α F) p.1 p.2 / Real.sin (2 * p.2)
        = -(3 / (4 * α)) * Work.Construction.L12 F p.1 + (1 / 4) * Work.Construction.FK F p.1
      have h2α : (2 : ℝ) * α ≠ 0 := by positivity
      have hU : Work.Construction.Uop α (Work.Construction.Theta α F) p.1 p.2
          = (1 / 2) * (-(3 / (2 * α)) * Real.sin (2 * p.2) * Work.Construction.L12 F p.1
            + (1 / 2) * Real.sin (2 * p.2) * Work.Construction.FK F p.1) := by
        have hU' : Work.Construction.Uop α (Work.Construction.Theta α F) p.1 p.2 * 2
            = -(3 / (2 * α)) * Real.sin (2 * p.2) * Work.Construction.L12 F p.1
              + (1 / 2) * Real.sin (2 * p.2) * Work.Construction.FK F p.1 := by
          linarith [hOp.2.1]
        rw [show (1 / 2) * (-(3 / (2 * α)) * Real.sin (2 * p.2)
              * Work.Construction.L12 F p.1
            + (1 / 2) * Real.sin (2 * p.2) * Work.Construction.FK F p.1)
            = (-(3 / (2 * α)) * Real.sin (2 * p.2) * Work.Construction.L12 F p.1
              + (1 / 2) * Real.sin (2 * p.2) * Work.Construction.FK F p.1) / 2 from by ring,
          eq_div_iff (by norm_num : (2:ℝ) ≠ 0)]
        linarith [hU']
      rw [hU, div_eq_iff hsin]
      have hαne : α ≠ 0 := ne_of_gt hαG
      field_simp
      ring
    have hmix := Work.FTS_RegExport.RXT.SysAux.mixed_congr_of_isOpen isOpen_Qd hEqOn j i z θ
      ⟨hz, hθ0, hθ1⟩
    rw [hmix]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      rw [Work.Spaces.mixed_zero_right]
      show |Work.Spaces.DzIter j (fun z _ => -(3 / (4 * α)) * Work.Construction.L12 F z
        + (1 / 4) * Work.Construction.FK F z) z θ| ≤ C2
      rw [show Work.Spaces.DzIter j (fun z _ => -(3 / (4 * α)) * Work.Construction.L12 F z
          + (1 / 4) * Work.Construction.FK F z) z θ
          = Work.Elliptic.DzdIter j (fun z => -(3 / (4 * α)) * Work.Construction.L12 F z
            + (1 / 4) * Work.Construction.FK F z) z from
        Work.Elliptic.DzIter_rad _ j z θ]
      have hDr := DzdIter_const_mul_add (c := -(3 / (4 * α))) (d := (1 / 4))
        (u := fun z => Work.Construction.L12 F z)
        (v := fun z => Work.Construction.FK F z) (j := j)
        (fun b hb z' hz' => hL12diff b (by omega) z' hz')
        (fun b hb z' hz' => hFKdiff b (by omega) z' hz') hz
      rw [hDr]
      rw [hC2]
      calc |-(3 / (4 * α)) * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z
            + (1 / 4) * Work.Elliptic.DzdIter j (fun z => Work.Construction.FK F z) z|
          ≤ |-(3 / (4 * α)) * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z|
            + |(1 / 4) * Work.Elliptic.DzdIter j (fun z => Work.Construction.FK F z) z| :=
            abs_add_le _ _
        _ = (3 / (4 * α)) * |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 F z) z|
            + (1 / 4) * |Work.Elliptic.DzdIter j (fun z => Work.Construction.FK F z) z| := by
            rw [abs_mul, abs_mul, abs_neg,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 / (4 * α)),
              abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]
        _ ≤ (3 / (4 * α)) * CL + (1 / 4) * CL :=
            add_le_add (mul_le_mul_of_nonneg_left (hL12jet j (by omega) z hz) (by positivity))
              (mul_le_mul_of_nonneg_left (hFKjet j (by omega) z hz) (by norm_num))
    · have hz0 : Work.Spaces.DthIter i (fun z _ => -(3 / (4 * α)) * Work.Construction.L12 F z
          + (1 / 4) * Work.Construction.FK F z) = 0 :=
        DthIter_radial_eq_zero (fun z => -(3 / (4 * α)) * Work.Construction.L12 F z
          + (1 / 4) * Work.Construction.FK F z) i hi
      rw [Work.Spaces.mixed, hz0, DzIter_zero_fun]
      simpa using le_of_lt hC2pos
  refine ⟨max (max C3 C4) C2 + 1, ?_, ?_, ?_, ?_⟩
  · have h2 : 0 < C2 := hC2pos
    have h4 : 0 < C4 := hC4pos
    have h3 : 0 < C3 := by rw [hC3]; linarith
    nlinarith [le_max_left C3 C4, le_max_right C3 C4, le_max_left (max C3 C4) C2,
      le_max_right (max C3 C4) C2, h2, h3, h4]
  · intro j i hji z θ hz hθ0 hθ1
    have hle : C2 ≤ max (max C3 C4) C2 + 1 := by
      have h : C2 ≤ max (max C3 C4) C2 := le_max_right _ _
      linarith
    exact le_trans (hConj2 j i hji z θ hz hθ0 hθ1) hle
  · intro j i hji z θ hz hθ0 hθ1
    have hle : C3 ≤ max (max C3 C4) C2 + 1 := by
      have h : C3 ≤ max (max C3 C4) C2 := le_trans (le_max_left C3 C4) (le_max_left _ _)
      linarith
    exact le_trans (hConj3 j i hji z θ hz hθ0 hθ1) hle
  · intro j i hji z θ hz hθ0 hθ1
    have hle : C4 ≤ max (max C3 C4) C2 + 1 := by
      have h : C4 ≤ max (max C3 C4) C2 := le_trans (le_max_right C3 C4) (le_max_left _ _)
      linarith
    exact le_trans (hConj4 j i hji z θ hz hθ0 hθ1) hle

end

end Work.FTS_StreamBdry.Inputs
end
