import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.ZTBound
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
import Submission.Work.FTS.PhiStar.Psi0Est.exists_ZClass
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotBoundQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.sliceStep4Uniform
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.CoerDataT =====
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
open Work.FTS.Nonlin (RegQ CoerAdm)

set_option autoImplicit false

/-- **The level-`n` data of the transfer induction**: the Cauchy–Schwarz bound of `IP` at
level `n` (on `RegQ α n`), together with the coercivity of the paper's operator `𝓛_Γ^T`
at level `n` on the thin class `CoerAdm`. -/
structure CoerDataT (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity constant is positive -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz constant is positive -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ`-norm, on the level-`n` class -/
  cs : ∀ f g : Fn, RegQ α n f → RegQ α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- coercivity of `𝓛_Γ^T` at level `n`, on the one-condition class `CoerAdm` -/
  coer : ∀ f : Fn, CoerAdm α f →
    cc * Work.Spaces.HkSq α n f ≤ IP (Work.Coercivity.LGammaT α f) f


end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.HkIntegrand_ang_rad_le_n =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

set_option maxHeartbeats 800000

/-- **Pointwise separation of an angular profile and a radial function in the `ℋⁿ`-integrand,
`n ≤ 4`.**

This is the level-`n` (`n ≤ 4`) version of `Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le`.
The proof is the same pointwise computation: the two separation identities
`dzIter_ang_rad`/`mixed_ang_rad` split every iterate of `z ↦ a θ * r z` into the angular factor
`D_θ^i a` times the radial factor `D_z^j r`, the two squared-weight identities
`light_sq_nn`/`heavy_sq_nn` (valid on all of `Iθ`, including the endpoints where `sin(2θ) = 0`)
convert the weights, and the angular factor is bounded termwise using `ha0` and `ha1`.

The only difference from the `n = 4` statement is that the sums now run over `range (n+1)`
rather than `range 5`; the coefficient `4` is the number of angular orders `i ∈ {1,2,3,4}`, and
the sum over the genuinely occurring orders `1 ≤ i ≤ n` is extended to all four of them
(`(range (n+1)).filter (1 ≤ ·) ⊆ (range 5).filter (1 ≤ ·)`) using the nonnegativity of the
summands. -/
theorem HkIntegrand_ang_rad_le_n {n : ℕ} (hn : n ≤ 4) {α : ℝ} {a : ℝ → ℝ} {r : ℝ → ℝ} {G : ℝ → ℝ}
    {B0 B1 : ℝ}
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α n (fun z θ => a θ * r z) z θ
      ≤ (∑ i ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ
  have hsmGnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
    Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ
  -- ## The angular factor, bounded with the (at most) four available orders
  have hsum_ang : (∑ i ∈ Finset.range (n + 1),
        (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
      ≤ 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
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
      _ ≤ ∑ _i ∈ (Finset.range 5).filter (fun i => 1 ≤ i),
            B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hcnn)
          intro i hi
          rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact ⟨by omega, hi.2⟩
      _ = 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
          rw [show (Finset.range 5).filter (fun i => 1 ≤ i) = Finset.Icc 1 4 from by decide,
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
        + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
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
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) :=
        mul_le_mul_of_nonneg_left hM hRnn

end Work.FTS.CoercivityFix.Transfer.E2norm
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.Pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

set_option autoImplicit false

open Work.FTS.Galerkin (Fn)

/-! ## The `α`-uniform bound on the multiplier `ampA` -/

/-- **The multiplier `ampA α = 2z/(c(α)(1+z)²)` has uniformly bounded `(z∂_z)`-iterates.**
There is a single `K`, valid for every `α ∈ (0,1]`, such that `|D_z^j (ampA α) z| ≤ K` for
`j ≤ 4` and `z > 0`.

This is `E2pkg.ampA_dzdIter_bound` with the constant made explicit (`20·K₀`, where `K₀` is the
chart bound of `E2Bound.zop_phi_bound`): the only `α`-dependence of the estimate is the factor
`2/c(α) ≤ 20`, from `1/10 ≤ c(α)` (`Spaces.c_bounds`). -/
theorem ampA_dzdIter_bound_uniform :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K := by
  obtain ⟨K₀, hK₀, hbd⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 4
  refine ⟨20 * K₀, by positivity, ?_⟩
  intro α hα hα1 j hj z hz
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have h2c : 2 / Work.Spaces.c α ≤ 20 := by
    rw [div_le_iff₀ hcpos]
    linarith
  have hb : |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K₀ := hbd j hj z hz
  calc |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z|
      = |Work.Spaces.Zop^[j] (Work.FTS.CoercivityFix.Transfer.ampA α) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    _ = |Work.Spaces.Zop^[j]
          (fun z => (2 / Work.Spaces.c α) * (z / (1 + z) ^ 2)) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_eq_const_mul_fA]
    _ = |(2 / Work.Spaces.c α) * Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
    _ = |2 / Work.Spaces.c α|
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := abs_mul _ _
    _ = (2 / Work.Spaces.c α)
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [abs_of_nonneg (by positivity)]
    _ ≤ (2 / Work.Spaces.c α) * K₀ := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 20 * K₀ := mul_le_mul_of_nonneg_right h2c hK₀

/-! ## The angular-moment bound at level `n` -/

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm


/-! ## The `(z∂_z)`-iterates of `L₁₂ f` -/


/-! ## Two-term additivity of `HkSq` -/

/-- **`HkSq` is two-term subadditive** for a pair whose blocks add up pointwise and whose
`HkIntegrand` is pointwise dominated by twice the sum of the two integrands. -/
theorem HkSq_add_le (α : ℝ) (n : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α n f) (hg : Work.Spaces.HkMem α n g)
    (hfg : Work.Spaces.HkMem α n (f + g))
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n (f + g) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α n f z θ
          + 2 * Work.Spaces.HkIntegrand α n g z θ) :
    Work.Spaces.HkSq α n (f + g) ≤ 2 * Work.Spaces.HkSq α n f + 2 * Work.Spaces.HkSq α n g := by
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (f + g) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
    intro z hz
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α n (f + g) z θ
          ≤ 2 * Work.Spaces.HkIntegrand α n f z θ
            + 2 * Work.Spaces.HkIntegrand α n g z θ :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α n (f + g) z θ)
      (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2)) hae
    have hEq : (∫ a in Work.Spaces.Iθ,
          ((fun x => 2 * Work.Spaces.HkIntegrand α n f z x)
            + fun x => 2 * Work.Spaces.HkIntegrand α n g z x) a)
        = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
      simp only [Pi.add_apply]
      rw [MeasureTheory.integral_add ((hf.1 z hz).const_mul 2) ((hg.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact le_trans hmono (le_of_eq hEq)
  have hmain : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (f + g) z θ)
      ≤ ∫ z in Work.Spaces.Iz, (2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ)) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n (f + g) z θ)
      ((hf.2.const_mul 2).add (hg.2.const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hslice)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (f + g) z θ)
      ≤ ∫ z in Work.Spaces.Iz, (2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ)) := hmain
    _ = 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
        + 2 * (∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
        rw [MeasureTheory.integral_add (hf.2.const_mul 2) (hg.2.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end Work.FTS.CoercivityFix.Transfer.E2norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSBnd =====
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

/-! ## The three blocks of the expansion -/

/-- The first binomial block of `D_z^j (radS α f)`: `D_z^c (D_z a)` against `D_z^{j-c} L₁₂ f`. -/
noncomputable def W1 (α : ℝ) (f : Fn) (j : ℕ) : ℝ → ℝ := fun z =>
  ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)
    * (Work.Elliptic.DzdIter (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) z)
    * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z)

/-- The second binomial block: `D_z^c a` against `D_z^{j-c} (Qang f 0) = Qang f (j-c)`. -/
noncomputable def W2 (α : ℝ) (f : Fn) (j : ℕ) : ℝ → ℝ := fun z =>
  ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)
    * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
    * (Work.Elliptic.Qang f (j - b) z)

/-- The third (constant) block of `D_z^j (radS α f)`. -/
noncomputable def W3 (α : ℝ) (f : Fn) (j : ℕ) : ℝ → ℝ := fun z =>
  (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
    * (Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z)


/-! ## The majorant -/

/-- The explicit majorant of the squared and weighted `j`-th iterate of `radS`. -/
noncomputable def SmajA (α : ℝ) (f : Fn) (j : ℕ) (K : ℝ) (z : ℝ) : ℝ :=
  3 * ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
      + (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
        * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2))


end Work.FTS.CoercivityFix.Transfer.E2pkg
end
end
-- ===== merged: Submission.Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

set_option autoImplicit false

/-- **The quantitative `NiceFlat` bound for the heavy mixed slot.**

For data of class `Work.FTS.EllSol.FlatFT.NiceFlat` (jointly `C²` on the open strip, vanishing
at the two angles as *values*, and uniformly compactly supported in `t`) whose three
`σ_η`-weighted shifted slots are integrable, the `σ_η`-weighted mixed slot
`∂_θ(∂_t - b)u` is bounded by `C·(V + √(Z·Q))`.

This is the `hNice` input of `Work.FTS.EllSol.Shift2Flat.mixedSlotOfNice`: the quantitative
per-`θ` Plancherel data are supplied by `niceRangePlanch` and the `ℂ`-valued sharp angular
Agmon estimate by `Work.FTS.EllSol.Trunc.curlAgmon` (whose weight `thEta` is `sEta`), so that
`niceSlotBoundHE` applies verbatim. -/
theorem niceBoundQuantFts :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ) (u : ℝ → ℝ → ℝ), Work.FTS.EllSol.FlatFT.NiceFlat u →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
          + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) →
      (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2))
        ≤ ENNReal.ofReal (C * ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
              (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
                * Work.FTS.EllipticEst.sEta p.2)
            + Real.sqrt ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                  (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
                    + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                    (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2
                      * Work.FTS.EllipticEst.sEta p.2)))) := by
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.FTS.EllSol.Trunc.curlAgmon
  refine ⟨Cc, hCcpos, ?_⟩
  intro b u hg hSp hSpp hQ
  obtain ⟨h1, h2, h3⟩ := niceRangePlanch (b := b) hg
  have hmain := niceSlotBoundHE (Cc := Cc) hCcpos hCc (b := b) (u := u) hg
    h1 h2 h3
    (by simpa only [Work.FTS.EllSol.FlatFT.wE_eq_sEta] using hSp)
    (by simpa only [Work.FTS.EllSol.FlatFT.wE_eq_sEta] using hSpp)
    (by simpa only [Work.FTS.EllSol.FlatFT.wE_eq_sEta] using hQ)
  simpa only [Work.FTS.EllSol.FlatFT.wE_eq_sEta] using hmain

/-- `∫∫ (∂_θ(pz u - b·u))² σ_η < ⊤` from the three weighted slots of `u`.

A complete, hand-verified route is written up in
`Submission/Work/FTS/EllSol/Shift2Flat/NOTES_mixedSlot_route.md` (truncate `u` in `t` by
`Work.FTS.EllSol.Trunc.chi`, apply the complex Agmon inequality `Work.FTS.EllSol.Trunc.curlAgmon`
to the `θ`-slices of the truncated `t`-Fourier transform for each frequency, Plancherel per
slice, `μ(ξ) = (2πξ)² + b²` and Cauchy–Schwarz in `ξ`, then Fatou in the truncation scale).
The statement is TRUE — do not declare false. -/
theorem mixedSlotFiniteness {b : ℝ} (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hV : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hZ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) < ⊤ := by
  exact mixedSlotOfNice niceBoundQuantFts b u hu h0 hπ hV hZ hQ

end Work.FTS.EllSol.Shift2Flat
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.topB_sliceStep5_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `topB_sliceStep5_uniform`: Elgindi Step 5 for the slice, with a constant uniform in `γ`

The statement is that of `Work.FTS.EllipticEst.H2W.sliceStep5Weak` with the constant hoisted
out of the `γ`-quantifier: for `1 ≤ γ ≤ 3/2` and a `C⁴` function `u` on `(0, π/2)`
(continuous on the closed interval, vanishing at both ends) with `Lzero1 u = g` on `(0,π/2)`,

  `∫ (u⁗)² sin(2θ)^{4-γ} ≤ C (∫ (g'')² sin(2θ)^{4-γ} + ∫ (u''')² sin(2θ)^{2-γ}`
  `  + ∫ (u'')² sEta + ∫ (u')² + ∫ u²)`,

with a single `C` working for every `γ ∈ [1, 3/2]` (this is what the two-dimensional
Step-5 estimate needs, since it is instantiated at `γ = gam α` which varies with `α`).

The proof is the assembly of `sliceStep5Weak`; the point is that *its* proof already produces a
`γ`-independent constant, because the three leaves it invokes
(`sliceStep5Vv0`, `sliceStep5Vv1`, `g1BoundAlt vTwoW4WeakAlt`) are themselves stated with the
constant outside the `γ`-quantifier.  So the same integral bookkeeping, run with `γ` introduced
after the constant, yields the uniform estimate.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

open Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem topB_sliceStep5_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u g : ℝ → ℝ),
      ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
                Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := sliceStep5Vv0
  obtain ⟨C1, hC1pos, hC1⟩ := sliceStep5Vv1
  obtain ⟨C3, hC3pos, hC3⟩ := g1BoundAlt VTwoAlt.vTwoW4WeakAlt
  refine ⟨3 * (4 * (16 * (16 + 225 + C0 + 9 * C3) + 27 * (2 + 4 * C1) + 9 * C1 + 1) + 37),
    by linarith, ?_⟩
  intro γ hγ1 hγ2 u g hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  have hIθm : MeasurableSet Work.Spaces.Iθ := Iθ_measurableSet
  obtain ⟨hIntV0, hIntV1, _hIntG0, hIntG1⟩ :=
    sliceStep5Integrable γ hγ1 hγ2 u g hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  have hC0b := hC0 γ u g hγ1 hγ2 hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  have hC1b := hC1 γ u g hγ1 hγ2 hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  have hC3b := hC3 γ u g hγ1 hγ2 hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  -- ==== abbreviations ====
  set B2 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hB2
  set A3 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 - γ)) with hA3
  set A2 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Work.FTS.EllipticEst.sEta θ) with hA2
  set A1 := (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) with hA1
  set A0 := (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) with hA0
  set R := B2 + A3 + A2 + A1 + A0 with hR
  set A4 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hA4
  set AA := (∫ θ in Work.Spaces.Iθ,
    (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hAA
  set J2 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hJ2
  set J1 := (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 - γ)) with hJ1
  set J0 := (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hJ0
  set Q := (∫ θ in Work.Spaces.Iθ,
    (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hQ
  set X2 := (∫ θ in Work.Spaces.Iθ,
    (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hX2
  set X1 := (∫ θ in Work.Spaces.Iθ,
    (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hX1
  set X0 := (∫ θ in Work.Spaces.Iθ,
    (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hX0
  set V0 := (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 - γ)) with hV0
  set Bv1 := (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hBv1
  set G1 := (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 - γ)) with hG1
  -- ==== basic integrability ====
  have hIntJ2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' h2
      (((measurable_deriv (deriv u)).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))]
        exact mul_le_mul_of_nonneg_left (rpow4_le_sEta_rp γ hγ1 hγ2 hθ) (sq_nonneg _))
  have hIntJ1 : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' h1
      (((measurable_deriv u).pow_const 2).mul
        (measurable_rpow_sin_two γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (rpow2_nonneg_rp γ hθ))]
        simpa using mul_le_mul_of_nonneg_left (rpow2_le_one_rp γ hγ1 hγ2 hθ) (sq_nonneg _))
  have hIntJ0 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' h0
      (((huc.aestronglyMeasurable hIθm).pow 2).mul
        (measurable_rpow_sin_four γ hγ2).aestronglyMeasurable)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))]
        simpa using mul_le_mul_of_nonneg_left (rpow4_le_one_rp γ hγ1 hγ2 hθ) (sq_nonneg _))
  have hIntSv1 : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hIntV1
      (((Real.continuous_sin.measurable.mul
        (measurable_deriv (fun t => u t / Real.cos t))).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))]
        exact mul_le_mul_of_nonneg_right
          (sin_mul_sq_le_sq θ (deriv (fun t => u t / Real.cos t) θ))
          (rpow4_nonneg_rp γ hθ))
  have hIntCv0 : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun_ae hIntJ0 (by
      filter_upwards [cos_mul_ae (u := u)] with θ h
      rw [h])
  -- the same facts in `Integrable` form (this is what `integral_add` wants)
  have hIJ2 : MeasureTheory.Integrable
      (fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntJ2
  have hIJ1 : MeasureTheory.Integrable
      (fun θ => (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntJ1
  have hIJ0 : MeasureTheory.Integrable
      (fun θ => (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntJ0
  have hISv1 : MeasureTheory.Integrable
      (fun θ => (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntSv1
  have hICv0i : MeasureTheory.Integrable
      (fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntCv0
  have hI3i : MeasureTheory.Integrable
      (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict Work.Spaces.Iθ) := h3
  have hIG1i : MeasureTheory.Integrable
      (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntG1
  have hIV0i : MeasureTheory.Integrable
      (fun θ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntV0
  have hIBi : MeasureTheory.Integrable
      (fun θ => (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hB
  -- ==== X2 ====
  set D2 : ℝ → ℝ := fun θ => 3 *
      ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 4 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))) with hD2
  have hD2int : MeasureTheory.IntegrableOn D2 Work.Spaces.Iθ := by
    rw [hD2]
    exact ((hIntJ2.add hIntJ0).add (hIntSv1.const_mul 4)).const_mul 3
  have hae_nnX2 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      0 ≤ (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
    exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ)
  have haeX2 : (fun θ => (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] D2 := by
    filter_upwards [ae_mem_Ioo_Iθ, CV2_ae hu hode] with θ hθ hCV2
    have hw : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := rpow4_nonneg_rp γ (Iθ_of_Ioo hθ)
    have hsq : (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        ≤ 3 * ((deriv (deriv u) θ) ^ 2 + (u θ) ^ 2
            + 4 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2) := by
      rw [hCV2]
      nlinarith [sq_add_le_three (deriv (deriv u) θ) (u θ)
        (2 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ))]
    rw [hD2]
    calc (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ (3 * ((deriv (deriv u) θ) ^ 2 + (u θ) ^ 2
            + 4 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2)) *
          Real.rpow (Real.sin (2 * θ)) (4 - γ) := mul_le_mul_of_nonneg_right hsq hw
      _ = 3 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 4 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) := by ring
  have hIntCv2 : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hD2int
      ((((Real.continuous_cos.measurable).mul
        (measurable_deriv (deriv (fun t => u t / Real.cos t)))).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [hae_nnX2, haeX2] with θ h1 h2
        rwa [Real.norm_eq_abs, abs_of_nonneg h1])
  have hD2val : (∫ θ in Work.Spaces.Iθ, D2 θ) = 3 * (J2 + J0 + 4 * X1) := by
    have hA : MeasureTheory.Integrable
        (fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
          + (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIJ2.add hIJ0
    have hB' : MeasureTheory.Integrable
        (fun θ => 4 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hISv1.const_mul 4
    rw [hD2, MeasureTheory.integral_const_mul 3]
    rw [MeasureTheory.integral_add
      (f := fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (g := fun θ => 4 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))) hA hB']
    rw [MeasureTheory.integral_add
      (f := fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (g := fun θ => (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      hIJ2 hIJ0]
    rw [MeasureTheory.integral_const_mul 4, hJ2, hJ0, hX1]
  have hX2cmp : X2 ≤ 3 * (J2 + J0 + 4 * X1) := by
    rw [hX2]
    calc (∫ θ in Work.Spaces.Iθ,
          (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, D2 θ := integral_le_of_ae hae_nnX2 hD2int haeX2
      _ = 3 * (J2 + J0 + 4 * X1) := hD2val
  -- ==== Q ====
  set DQ : ℝ → ℝ := fun θ => 16 *
      (16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + 9 * ((deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))) with hDQ
  have hDQint : MeasureTheory.IntegrableOn DQ Work.Spaces.Iθ := by
    rw [hDQ]
    exact ((((h3.const_mul 16).add (hIntJ1.const_mul 225)).add hIntV0).add
      (hIntG1.const_mul 9)).const_mul 16
  have hae_nnQ : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      0 ≤ (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
    exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ)
  have haeQ : (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] DQ := by
    filter_upwards [ae_mem_Ioo_Iθ, CV3_ae hu hode] with θ hθ hCV3
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hcos : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).ne'
    have htan : Real.tan θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ 4 * Real.rpow (Real.sin (2 * θ)) (2 - γ) := tan_sq_mul_rpow4_le_rp γ hθ
    have hsqeq : (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
        = Real.tan θ ^ 2 *
          (Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 :=
      sin_mul_sq_eq_tan hcos _
    have hcv : (Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
        ≤ 4 * ((4 * deriv (deriv (deriv u)) θ) ^ 2 + (15 * deriv u θ) ^ 2
            + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 + (3 * deriv g θ) ^ 2) := by
      rw [hCV3]
      nlinarith [sq_add_le_four (4 * deriv (deriv (deriv u)) θ) (15 * deriv u θ)
        (-(Real.sin θ * (u θ / Real.cos θ))) (3 * deriv g θ)]
    have hsv : (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_le_mul_of_nonneg_right (sin_mul_sq_le_sq θ _) (rpow2_nonneg_rp γ (Iθ_of_Ioo hθ))
    rw [hsqeq, hDQ]
    have hw2 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := rpow2_nonneg_rp γ (Iθ_of_Ioo hθ)
    calc Real.tan θ ^ 2 *
          (Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        = (Real.tan θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) *
          (Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 := by ring
      _ ≤ (4 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) *
          (4 * ((4 * deriv (deriv (deriv u)) θ) ^ 2 + (15 * deriv u θ) ^ 2
            + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 + (3 * deriv g θ) ^ 2)) :=
          mul_le_mul htan hcv (sq_nonneg _) (by positivity)
      _ = 16 * Real.rpow (Real.sin (2 * θ)) (2 - γ) *
          (16 * (deriv (deriv (deriv u)) θ) ^ 2 + 225 * (deriv u θ) ^ 2
            + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 + 9 * (deriv g θ) ^ 2) := by ring
      _ ≤ 16 * Real.rpow (Real.sin (2 * θ)) (2 - γ) *
          (16 * (deriv (deriv (deriv u)) θ) ^ 2 + 225 * (deriv u θ) ^ 2
            + (u θ / Real.cos θ) ^ 2 + 9 * (deriv g θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (by linarith [sin_mul_sq_le_sq θ (u θ / Real.cos θ)])
            (by positivity)
      _ = 16 * (16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + 9 * ((deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))) := by ring
  have hIntQint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hDQint
      ((((Real.continuous_sin.measurable).mul
        (measurable_deriv (deriv (deriv (fun t => u t / Real.cos t))))).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [hae_nnQ, haeQ] with θ h1 h2
        rwa [Real.norm_eq_abs, abs_of_nonneg h1])
  have hDQval : (∫ θ in Work.Spaces.Iθ, DQ θ) = 16 * (16 * A3 + 225 * J1 + V0 + 9 * G1) := by
    have hA : MeasureTheory.Integrable
        (fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hI3i.const_mul 16).add (hIJ1.const_mul 225)).add hIV0i
    have hA' : MeasureTheory.Integrable
        (fun θ => 9 * ((deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hIG1i.const_mul 9
    have hB : MeasureTheory.Integrable
        (fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        (volume.restrict Work.Spaces.Iθ) :=
      (hI3i.const_mul 16).add (hIJ1.const_mul 225)
    have hB' : MeasureTheory.Integrable
        (fun θ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIV0i
    have hC : MeasureTheory.Integrable
        (fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hI3i.const_mul 16
    have hC' : MeasureTheory.Integrable
        (fun θ => 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hIJ1.const_mul 225
    rw [hDQ, MeasureTheory.integral_const_mul 16]
    rw [MeasureTheory.integral_add
      (f := fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (g := fun θ => 9 * ((deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))) hA hA']
    rw [MeasureTheory.integral_add
      (f := fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
      (g := fun θ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      hB hB']
    rw [MeasureTheory.integral_add
      (f := fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
      (g := fun θ => 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
      hC hC']
    rw [MeasureTheory.integral_const_mul 16, MeasureTheory.integral_const_mul 225,
      MeasureTheory.integral_const_mul 9, hA3, hJ1, hV0, hG1]
  have hQcmp : Q ≤ 16 * (16 * A3 + 225 * J1 + V0 + 9 * G1) := by
    rw [hQ]
    calc (∫ θ in Work.Spaces.Iθ,
          (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, DQ θ := integral_le_of_ae hae_nnQ hDQint haeQ
      _ = 16 * (16 * A3 + 225 * J1 + V0 + 9 * G1) := hDQval
  -- ==== AA ====
  set DAA : ℝ → ℝ := fun θ => 4 *
      ((Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hDAA
  have hDAAint : MeasureTheory.IntegrableOn DAA Work.Spaces.Iθ := by
    rw [hDAA]
    exact (((hIntQint.add (hIntCv2.const_mul 9)).add (hIntSv1.const_mul 9)).add
      hIntCv0).const_mul 4
  have hae_nnAA : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      0 ≤ (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
    exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ)
  have haeAA : (fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] DAA := by
    filter_upwards [ae_mem_Ioo_Iθ, tanu3_ae hu] with θ hθ htan3
    have hw : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := rpow4_nonneg_rp γ (Iθ_of_Ioo hθ)
    have hsq : (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
        ≤ 4 * ((Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
            + 9 * (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
            + 9 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2
            + (Real.cos θ * (u θ / Real.cos θ)) ^ 2) := by
      rw [htan3]
      nlinarith [sq_add_le_four
        (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ)
        (3 * (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ))
        (-(3 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ)))
        (-(Real.cos θ * (u θ / Real.cos θ)))]
    rw [hDAA]
    calc (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ (4 * ((Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
            + 9 * (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
            + 9 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2
            + (Real.cos θ * (u θ / Real.cos θ)) ^ 2)) *
          Real.rpow (Real.sin (2 * θ)) (4 - γ) := mul_le_mul_of_nonneg_right hsq hw
      _ = 4 * ((Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by ring
  have hIntAAint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hDAAint
      (((measurable_deriv (deriv (deriv (fun t => Real.tan t * u t)))).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [hae_nnAA, haeAA] with θ h1 h2
        rwa [Real.norm_eq_abs, abs_of_nonneg h1])
  have hDAAval : (∫ θ in Work.Spaces.Iθ, DAA θ) = 4 * (Q + 9 * X2 + 9 * X1 + X0) := by
    have hIQi : MeasureTheory.Integrable
        (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIntQint
    have hICv2i : MeasureTheory.Integrable
        (fun θ => (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIntCv2
    have hA : MeasureTheory.Integrable
        (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) :=
      (hIQi.add (hICv2i.const_mul 9)).add (hISv1.const_mul 9)
    have hA' : MeasureTheory.Integrable
        (fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hICv0i
    have hB : MeasureTheory.Integrable
        (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hIQi.add (hICv2i.const_mul 9)
    have hB' : MeasureTheory.Integrable
        (fun θ => 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hISv1.const_mul 9
    have hC : MeasureTheory.Integrable
        (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIQi
    have hC' : MeasureTheory.Integrable
        (fun θ => 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hICv2i.const_mul 9
    rw [hDAA, MeasureTheory.integral_const_mul 4]
    rw [MeasureTheory.integral_add
      (f := fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
      (g := fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)) hA hA']
    rw [MeasureTheory.integral_add
      (f := fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
      (g := fun θ => 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) hB hB']
    rw [MeasureTheory.integral_add
      (f := fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (g := fun θ => 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) hC hC']
    rw [MeasureTheory.integral_const_mul 9, MeasureTheory.integral_const_mul 9,
      hQ, hX2, hX1, hX0]
  have hAAcmp : AA ≤ 4 * (Q + 9 * X2 + 9 * X1 + X0) := by
    rw [hAA]
    calc (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, DAA θ := integral_le_of_ae hae_nnAA hDAAint haeAA
      _ = 4 * (Q + 9 * X2 + 9 * X1 + X0) := hDAAval
  -- ==== A4 ====
  set DA4 : ℝ → ℝ := fun θ => 3 *
      ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hDA4
  have hDA4int : MeasureTheory.IntegrableOn DA4 Work.Spaces.Iθ := by
    rw [hDA4]
    exact (((hIntAAint.add (hIntJ2.const_mul 36))).add hB).const_mul 3
  have hae_nnA4 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      0 ≤ (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
    exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ)
  have haeA4 : (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] DA4 := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm, eqn_deriv2_ae hu hode] with θ hθ heqn
    have hw : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := rpow4_nonneg_rp γ hθ
    have hsq : (deriv (deriv (deriv (deriv u))) θ) ^ 2
        ≤ 3 * ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
            + 36 * (deriv (deriv u) θ) ^ 2 + (deriv (deriv g) θ) ^ 2) := by
      rw [heqn]
      nlinarith [sq_sub_sub_le_three (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ)
        (6 * deriv (deriv u) θ) (deriv (deriv g) θ)]
    rw [hDA4]
    calc (deriv (deriv (deriv (deriv u))) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ (3 * ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
            + 36 * (deriv (deriv u) θ) ^ 2 + (deriv (deriv g) θ) ^ 2)) *
          Real.rpow (Real.sin (2 * θ)) (4 - γ) := mul_le_mul_of_nonneg_right hsq hw
      _ = 3 * ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by ring
  have hA4cmp : A4 ≤ 3 * (AA + 36 * J2 + B2) := by
    rw [hA4]
    calc (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (deriv (deriv u))) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, DA4 θ := integral_le_of_ae hae_nnA4 hDA4int haeA4
      _ = 3 * (AA + 36 * J2 + B2) := by
        have hIAA : MeasureTheory.Integrable
            (fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (4 - γ))
            (volume.restrict Work.Spaces.Iθ) := hIntAAint
        have hE : MeasureTheory.Integrable
            (fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
                  Real.rpow (Real.sin (2 * θ)) (4 - γ)
                + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
            (volume.restrict Work.Spaces.Iθ) := hIAA.add (hIJ2.const_mul 36)
        have hE' : MeasureTheory.Integrable
            (fun θ => (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
            (volume.restrict Work.Spaces.Iθ) := hIBi
        have hF : MeasureTheory.Integrable
            (fun θ => 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
            (volume.restrict Work.Spaces.Iθ) := hIJ2.const_mul 36
        rw [hDA4, MeasureTheory.integral_const_mul 3]
        rw [MeasureTheory.integral_add
          (f := fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (4 - γ)
              + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
          (g := fun θ => (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
          hE hE']
        rw [MeasureTheory.integral_add
          (f := fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (4 - γ))
          (g := fun θ => 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
          hIAA hF]
        rw [MeasureTheory.integral_const_mul 36, hAA, hJ2, hB2]
  -- ==== the simple comparisons ====
  have hX1cmp : X1 ≤ Bv1 := by
    rw [hX1]
    calc (∫ θ in Work.Spaces.Iθ,
          (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
          integral_le_of_ae
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))
            hIntV1
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_le_mul_of_nonneg_right
                (sin_mul_sq_le_sq θ (deriv (fun t => u t / Real.cos t) θ))
                (rpow4_nonneg_rp γ hθ))
      _ = Bv1 := hBv1.symm
  have hX0eq : X0 = J0 := by
    rw [hX0, hJ0]
    exact MeasureTheory.integral_congr_ae (by
      filter_upwards [cos_mul_ae (u := u)] with θ h
      rw [h])
  have hJ0le : J0 ≤ A0 := by
    rw [hJ0]
    calc (∫ θ in Work.Spaces.Iθ,
          (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
          integral_le_of_ae
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))
            h0
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              simpa using mul_le_mul_of_nonneg_left (rpow4_le_one_rp γ hγ1 hγ2 hθ)
                (sq_nonneg (u θ)))
      _ = A0 := hA0.symm
  have hJ1le : J1 ≤ A1 := by
    rw [hJ1]
    calc (∫ θ in Work.Spaces.Iθ,
          (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
          integral_le_of_ae
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_nonneg (sq_nonneg _) (rpow2_nonneg_rp γ hθ))
            h1
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              simpa using mul_le_mul_of_nonneg_left (rpow2_le_one_rp γ hγ1 hγ2 hθ)
                (sq_nonneg (deriv u θ)))
      _ = A1 := hA1.symm
  have hJ2le : J2 ≤ A2 := by
    rw [hJ2]
    calc (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
          integral_le_of_ae
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))
            h2
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_le_mul_of_nonneg_left (rpow4_le_sEta_rp γ hγ1 hγ2 hθ)
                (sq_nonneg (deriv (deriv u) θ)))
      _ = A2 := hA2.symm
  -- ==== nonnegativity and elementary bounds ====
  have hA0nn : 0 ≤ A0 := by
    rw [hA0]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ _ => sq_nonneg _)
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ _ => sq_nonneg _)
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (by
        rw [Work.FTS.EllipticEst.sEta]
        exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have hA3nn : 0 ≤ A3 := by
    rw [hA3]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (rpow2_nonneg_rp γ hθ))
  have hB2nn : 0 ≤ B2 := by
    rw [hB2]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))
  have hA0le : A0 ≤ R := by rw [hR]; linarith [hA1nn, hA2nn, hA3nn, hB2nn]
  have hA1le : A1 ≤ R := by rw [hR]; linarith [hA0nn, hA2nn, hA3nn, hB2nn]
  have hA2le : A2 ≤ R := by rw [hR]; linarith [hA0nn, hA1nn, hA3nn, hB2nn]
  have hA3le : A3 ≤ R := by rw [hR]; linarith [hA0nn, hA1nn, hA2nn, hB2nn]
  have hB2le : B2 ≤ R := by rw [hR]; linarith [hA0nn, hA1nn, hA2nn, hA3nn]
  -- ==== the final arithmetic ====
  have hV0b : V0 ≤ C0 * R := hC0b
  have hBv1b : Bv1 ≤ C1 * R := hC1b
  have hG1b : G1 ≤ C3 * R := hC3b
  have hQb : Q ≤ 16 * (16 + 225 + C0 + 9 * C3) * R := by
    linarith [hQcmp, hA3le, hJ1le, hA1le, hV0b, hG1b]
  have hAAb : AA ≤ 4 * (16 * (16 + 225 + C0 + 9 * C3) + 27 * (2 + 4 * C1) + 9 * C1 + 1) * R := by
    linarith [hAAcmp, hQb, hX2cmp, hX1cmp, hBv1b, hX0eq, hJ2le, hJ0le, hA0le, hA1le, hA2le]
  have hA4b : A4 ≤ 3 * (4 * (16 * (16 + 225 + C0 + 9 * C3) + 27 * (2 + 4 * C1) + 9 * C1 + 1) + 37) * R := by
    linarith [hA4cmp, hAAb, hJ2le, hA2le, hB2le]
  exact hA4b

end Work.FTS.EllipticEst.Cores
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.Cores.topB_step5_integrable =====
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

/-!
# `Cores/topB_step5_integrable`: the honesty of the five Step-5 slots at level `2`

The lemma proves that the five `z`-integrals appearing in the right-hand side of the level-`2`
Step-5 estimate (the `B`-half of the top angular slot of `∂_θθΨ`) are honest for every datum of
the weak class `TT.EllWeakPos α 2 F Ψ`:

* the source slot  `∫_z w² ∫_θ (∂_θ²Gsrc)² sin(2θ)^{4-γ}`,
* the Step-4 slot  `∫_z w² ∫_θ (∂_θ³Ψ)² sin(2θ)^{2-γ}`,
* the three lower-order slots `∫_z w² ∫_θ (∂_θ²Ψ)² sin(2θ)^{-η}`, `∫_z w² ∫_θ (∂_θΨ)²`,
  `∫_z w² ∫_θ Ψ²`.

The route is pointwise domination by the level-`2` `ℋ`-integrand of `∂_θθΨ` (components
`memB` of the weak class, and `memF` / `memA` for the source), together with the weighted slice
Poincaré inequality `SliceSqBoundsOpen` for the two unweighted lower-order slots (whose slices
are continuous on the closed angular interval by `remov.weakSliceRegular`, whence the
`θ`-endpoint conditions needed by the Poincaré inequality are available).

Pre-existing ingredients consumed here: `s20src_integrableOn_slotZ_sigma4_DzIter`,
`s20src_integrableOn_slotZ_sigma4_Az`, `s20src_integrableOn_slotZ_sEta_DzIter`,
`s20src_slotZ_Gsrc_le`, the pointwise slot bounds `Mine.sig4_slot_pointwise` and
`s20_honesty`, and `Cores.Pieces.TL2.smoothOpen_Gsrc` for the smoothness of the source.
-/

/-! ## The weighted slice Poincaré constant -/

/-- The constant of the weighted slice Poincaré inequality `SliceSqBoundsOpen`. -/
private noncomputable def topB_poincC : ℝ :=
  Classical.choose Work.FTS.EllipticEst.WeakMoment.SliceSqBoundsOpen


private theorem topB_poincC_spec {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (hp : u (Real.pi / 2) = 0)
    (h5 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ topB_poincC * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) ∧
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ topB_poincC * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) :=
  (Classical.choose_spec Work.FTS.EllipticEst.WeakMoment.SliceSqBoundsOpen).2 u
    hsm hcont h0 hp h5

/-! ## The two lower-order slices of `Ψ` -/

/-- **The weighted slice Poincaré bounds for the slice `Ψ z ·`.**  Both `∫ (Ψ z ·)²` and
`∫ (∂_θΨ z ·)²` are dominated by `topB_poincC · ∫ (∂_θ²Ψ z ·)² sin(2θ)^{-η}` for `z > 0`: the
weighted Poincaré inequality gives the weighted versions, and `sin(2θ)^{-η} ≥ 1` on the open
interval turns them into the unweighted ones. -/
private theorem topB_slicePoincare_psi {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    {z : ℝ} (hz : 0 < z) :
    ((∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ topB_poincC * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) ∧
      ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        ≤ topB_poincC * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have hp : ContDiffOn ℝ n (fun θ' : ℝ => (z, θ')) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h2 := (h.smooth n).comp hp (fun θ' hθ' => ⟨hz, hθ'⟩)
    simpa [Function.comp_def, Function.uncurry] using h2
  obtain ⟨hcont, -, -, -, -, -, h7⟩ :=
    Work.FTS.EllipticEst.remov.weakSliceRegular 2 (by norm_num) α F Ψ hα hα4 h z hz
  have hcont' : ContinuousOn (fun θ : ℝ => Ψ z θ) Work.Spaces.Iθ := by
    simpa only [Work.Spaces.Iθ] using hcont
  obtain ⟨h1i, h1l, h2i, h2l⟩ :=
    topB_poincC_spec hsm hcont' (h.zero z) (h.pi_half z) h7
  have hone : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.H2W.Step5.s20src_one_le_sEta_ae
  have hle1 : (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) h1i
      (by
        filter_upwards [hone] with θ hθ
        nlinarith [sq_nonneg (Ψ z θ)])
  have hle2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) h2i
      (by
        filter_upwards [hone] with θ hθ
        nlinarith [sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)])
  refine ⟨hle1.trans h1l, hle2.trans h2l⟩

/-! ## The outer transfer for the two unweighted lower-order slots -/

/-- **Outer integrability of the `∂_θΨ`- and `Ψ`-slots from the `η`-slot.**  Since the slicewise
Poincaré bounds hold for every `z > 0` and the `η`-slot is outer-integrable by hypothesis, the
two unweighted slots are outer-integrable as well. -/
private theorem topB_low_slots_outer {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hA2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) Work.Spaces.Iz := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmaj : MeasureTheory.IntegrableOn (fun z => topB_poincC * ((Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iz := by
    simpa only [MeasureTheory.IntegrableOn, smul_eq_mul] using hA2.const_mul topB_poincC
  have haesmΨ : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hH : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Ψ p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_w_sq).mul (hΨ.continuousOn.pow 2)
    have hstr := Work.FTS.EllipticEst.H2W.Step5.s20src_aesm_integral_Qd
      (H := fun z θ => (Work.Spaces.w z) ^ 2 * (Ψ z θ) ^ 2) hH
    simpa only [MeasureTheory.integral_const_mul] using hstr
  have haesmD : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hH : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pthIter 1 Ψ p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_w_sq).mul (hΨ.pth.continuousOn.pow 2)
    have hstr := Work.FTS.EllipticEst.H2W.Step5.s20src_aesm_integral_Qd
      (H := fun z θ => (Work.Spaces.w z) ^ 2 * (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) hH
    simpa only [MeasureTheory.integral_const_mul] using hstr
  constructor
  · refine MeasureTheory.Integrable.mono' hmaj haesmD ?_
    filter_upwards [Work.FTS.EllipticEst.H2W.Step5.s20src_ae_pos_mem_Iz] with z hz
    have hpo := topB_slicePoincare_psi hα hα4 h hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (integral_nonneg fun θ => sq_nonneg _))]
    calc (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (topB_poincC * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hpo.2 (sq_nonneg _)
      _ = topB_poincC * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring
  · refine MeasureTheory.Integrable.mono' hmaj haesmΨ ?_
    filter_upwards [Work.FTS.EllipticEst.H2W.Step5.s20src_ae_pos_mem_Iz] with z hz
    have hpo := topB_slicePoincare_psi hα hα4 h hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (integral_nonneg fun θ => sq_nonneg _))]
    calc (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (topB_poincC * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hpo.1 (sq_nonneg _)
      _ = topB_poincC * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

/-! ## The `σ₄`-slot of `∂_θ²F` -/

/-- **Outer integrability of the `σ₄`-slot of `∂_θ²F`.**  The pointwise slot bound
`Mine.sig4_slot_pointwise` dominates `w²(∂_θ²F)²σ₄` by `10·HkIntegrand α 2 F`. -/
private theorem topB_slotZ_F_sigma4_outer {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hFmem : Work.Spaces.HkMem α 2 F) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
      (Work.Spaces.pthIter 2 F)
      (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz := by
  have hgam2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 F) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hF 2
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
        (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.H2W.Step5.s20src_aesm_integral_Qd
      (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_slotFun hX
        (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_sigma4 α))
  have hmaj : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      10 * Work.Spaces.HkIntegrand α 2 F z θ) Work.Spaces.Iz := by
    have h := hFmem.2.const_mul 10
    refine h.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    simp only [MeasureTheory.integral_const_mul]
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  rw [Real.norm_of_nonneg (Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ_nonneg
    (fun θ hθ => Work.FTS.EllipticEst.H2W.Step5.s20src_sigma4_nonneg α hθ) z)]
  refine MeasureTheory.integral_mono_of_nonneg ?_ ((hFmem.1 z hz).const_mul 10) ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun_nonneg
      (fun θ' hθ' => Work.FTS.EllipticEst.H2W.Step5.s20src_sigma4_nonneg α hθ') z θ hθ
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hpt := Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α)
      hgam2 le_rfl F z θ hθ
    simpa only [Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hpt

/-! ## The `σ₄`-slot of the source `∂_θ²Gsrc` -/

/-- **Outer integrability of the `σ₄`-slot of `∂_θ²Gsrc`.**  `s20src_slotZ_Gsrc_le` bounds the
source slot by the three pieces `∂_θ²F`, `∂_θ²(Az Ψ)` and `∂_θ²(D_zΨ)`, each of which is
outer-integrable against `σ₄`. -/
private theorem topB_slotZ_Gsrc_sigma4_outer {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
      (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
      (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hGs : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl
      (Work.FTS.EllipticEst.Cores.Pieces.TL2.smoothOpen_Gsrc h) 2
  have hmaj : MeasureTheory.IntegrableOn (fun z => 3 *
      (Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ (Work.Spaces.pthIter 2 F)
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        + α ^ 4 * Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        + (α * (5 + α)) ^ 2 * Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)) Work.Spaces.Iz := by
    have h1 := topB_slotZ_F_sigma4_outer hα hα4 hF h.memF
    have h2 := (Work.FTS.EllipticEst.H2W.Step5.s20src_integrableOn_slotZ_sigma4_Az
      hΨ h.memB hα4).const_mul (α ^ 4)
    have h3 := (Work.FTS.EllipticEst.H2W.Step5.s20src_integrableOn_slotZ_sigma4_DzIter
      hΨ h.memB hα4 1 (by norm_num)).const_mul ((α * (5 + α)) ^ 2)
    have h4 := ((h1.add h2).add h3).const_mul 3
    simpa only [MeasureTheory.IntegrableOn, smul_eq_mul, Pi.add_apply] using h4
  have haesm := Work.FTS.EllipticEst.H2W.Step5.s20src_aesm_integral_Qd
    (H := fun z θ => Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun
      (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
      (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
    (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_slotFun hGs
      (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_sigma4 α))
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  rw [Real.norm_of_nonneg (Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ_nonneg
    (fun θ hθ => Work.FTS.EllipticEst.H2W.Step5.s20src_sigma4_nonneg α hθ) z)]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
  · subst h0
    simp only [Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ_zero_left, mul_zero, add_zero]
    norm_num
  · exact Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ_Gsrc_le hα hα4 hF h.memF hΨ h.memB hpos

/-! ## The Step-4 slot of `∂_θ³Ψ` -/

/-- **Outer integrability of the `σ₂`-slot of `∂_θ³Ψ`.**  This is `s20_honesty`'s second
conjunct (`s20F3 = 8 w²(∂_θ³Ψ)²σ₂`) rescaled by `1/8`. -/
private theorem topB_slot3_Psi_sigma2_outer {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iz := by
  obtain ⟨-, -, -, h3z⟩ := Work.FTS.EllipticEst.H2W.Step5.s20_honesty α F Ψ hα hα4 h
  have h := h3z.const_mul (1 / 8)
  have h' : MeasureTheory.IntegrableOn (fun z => (1 / 8) *
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)) Work.Spaces.Iz := by
    simpa only [MeasureTheory.IntegrableOn, smul_eq_mul] using h
  refine h'.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  show (1 / 8) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
      = (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
  rw [show (fun θ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ) = fun θ =>
      (8 * (Work.Spaces.w z) ^ 2) * ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) from rfl]
  rw [MeasureTheory.integral_const_mul]
  ring

/-! ## The target -/

theorem topB_step5_integrable (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the `η`-slot of `∂_θθΨ` (the third conjunct), directly from `HkMem α 2 (∂_θθΨ)`
  have hA2 : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h0 := Work.FTS.EllipticEst.H2W.Step5.s20src_integrableOn_slotZ_sEta_DzIter
      hΨ h.memB 0 (by norm_num)
    refine h0.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    simp only [Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ,
      Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun, Work.Spaces.DzIter_zero]
    rw [MeasureTheory.integral_const_mul]
  -- the two unweighted lower-order slots (the fourth and fifth conjuncts)
  obtain ⟨hA1, hA0⟩ := topB_low_slots_outer hα hα4 h hA2
  -- the source slot (the first conjunct)
  have hJ2 : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h0 := topB_slotZ_Gsrc_sigma4_outer hα hα4 h
    refine h0.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    simp only [Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ,
      Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun]
    rw [MeasureTheory.integral_const_mul]
    simp only [Work.FTS.EllipticEst.Mine.sig4]
  -- the Step-4 slot (the second conjunct)
  have hM3 := topB_slot3_Psi_sigma2_outer hα hα4 h
  exact ⟨hJ2, hM3, hA2, hA1, hA0⟩

end

end Work.FTS.EllipticEst.Cores
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.slot01Weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false


/-! ## Elementary `rpow` algebra on the angular weights -/

/-- `s ^ 2 * s ^ (-c) = s ^ (2 - c)` for `s ≥ 0` and `c < 2`. -/
theorem slot01_rpow_two_mul_neg {s : ℝ} (hs : 0 ≤ s) {c : ℝ} (hc : c < 2) :
    s ^ 2 * s ^ (-c) = s ^ (2 - c) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    have h2 : (0 : ℝ) < 2 - c := by linarith
    by_cases hc0 : c = 0
    · subst hc0; norm_num
    · rw [Real.zero_rpow (neg_ne_zero.mpr hc0), Real.zero_rpow (ne_of_gt h2), mul_zero]
  · rw [← Real.rpow_natCast s 2, ← Real.rpow_add h]; ring_nf

/-- `(s ^ (-c / 2)) ^ 2 = s ^ (-c)` for `s ≥ 0` and `c > 0`. -/
theorem slot01_sq_rpow_neg_half {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (s ^ (-(c / 2))) ^ 2 = s ^ (-c) := by
  rw [← Real.rpow_natCast (s ^ (-(c / 2))) 2, ← Real.rpow_mul hs]
  ring_nf

/-! ## The `(1,0)` mixed slot: weight identities -/

/-- `D_θ f = sin(2θ)·∂_θ f`. -/
theorem slot01_mixed_zero_one_eq (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed 0 1 f = fun z θ => Real.sin (2 * θ) * Work.Spaces.pth f z θ := by
  funext z θ
  rfl

/-- The squared weight identity for the `(1,0)` slot:
`(D_θ f · Wt α)² = (∂_θ f)² w² sin(2θ)^{2-γ}` on the angular interval. -/
theorem slot01_wt_sq_identity (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) (z : ℝ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_nonneg hθ
  have hγ : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : Work.Spaces.gam α < 2 := by
    rw [Work.Spaces.gam]; linarith
  rw [slot01_mixed_zero_one_eq]
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  have h1 : (Real.sin (2 * θ) * Work.Spaces.pth f z θ
        * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by ring
  rw [h1, slot01_sq_rpow_neg_half hs (Work.Spaces.gam α),
    ← slot01_rpow_two_mul_neg hs hγ2]
  ring

/-- The `(1,0)` slot of any function, as an iterated integral with the angular weight
`σ_γ = sin(2θ)^{2-γ}`. -/
theorem slot01_L2Sq_mixed01_eq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  rw [Work.Spaces.L2Sq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [show (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) from
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => slot01_wt_sq_identity α hα hα4 f z hθ)]
  rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        from setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- The left-hand side, rewritten as an iterated integral with the angular weight `σ_γ`. -/
theorem slot01_LHS_eq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  rw [slot01_L2Sq_mixed01_eq α hα hα4 (Work.Spaces.pthIter 2 Ψ)]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine congrArg (fun t => (Work.Spaces.w z) ^ 2 * t) ?_
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  simp only [Work.Spaces.pthIter_succ]


/-- The weight algebra for a slot: `(A · (w / s^{η/2}))² = A² · s^{-η} · w²`. -/
theorem slot01_slot_sq_eq {η A wv s : ℝ} (hs : 0 ≤ s) :
    (A * (wv / s ^ (η / 2))) ^ 2 = A ^ 2 * s ^ (-η) * wv ^ 2 := by
  rw [div_eq_mul_inv, ← Real.rpow_neg hs (η / 2)]
  rw [show (A * (wv * s ^ (-(η / 2)))) ^ 2 = A ^ 2 * wv ^ 2 * (s ^ (-(η / 2))) ^ 2 from by ring]
  rw [slot01_sq_rpow_neg_half hs η]
  ring

/-! ## The target -/

theorem slot01Weak : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ C * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨K0, hK0pos, hK0⟩ := Work.H2W.slot01SliceBound
  obtain ⟨C1, hC1pos, hC1⟩ := Work.H2W.slot01ZTBound
  have hC1nn : 0 ≤ C1 := hC1pos.le
  have hK0nn : 0 ≤ K0 := hK0pos.le
  refine ⟨K0 * (1 + 3 * C1) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hsmΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ### the pieces of the estimate, as functions of the radius `z`
  set JintF : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 2 F z θ with hJintF
  set Q : ℕ → ℝ → ℝ := fun j z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hQ
  set Ps : ℕ → ℝ → ℝ := fun j z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ with hPs
  set I : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hI
  set Fs : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hFs
  set Zt : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hZt
  set Dt : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hDt
  -- ### elementary nonnegativity
  have hJnn : ∀ z, 0 ≤ JintF z := fun z => by
    rw [hJintF]; beta_reduce
    exact MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 2 F z θ
  have hQnn : ∀ j z, 0 ≤ Q j z := fun j z => by
    rw [hQ]; beta_reduce
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  -- ### the weight identity `w² · Ps j = Q j`
  have hQeq : ∀ j z, (Work.Spaces.w z) ^ 2 * Ps j z = Q j z := by
    intro j z
    rw [hPs, hQ, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall ?_))
    intro θ hθ
    beta_reduce
    have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_nonneg hθ
    rw [slot01_slot_sq_eq (η := Work.Spaces.eta) hs, Work.FTS.EllipticEst.sEta]
    ring
  -- ### the source slot of `F` is dominated by the `ℋ²`-integrand of `F`
  have hFsQ : ∀ z ∈ Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Fs z ≤ JintF z := by
    intro z hz
    rw [hFs, hJintF, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (h.memF.1 z hz) ?_
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun θ hθ => ?_)
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _))
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun θ hθ => ?_)
      beta_reduce
      have h1 := slot01_wt_sq_identity α hα hα4 F z hθ
      rw [show (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          = (Work.Spaces.pth F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) from by ring]
      rw [← h1]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 1 0 le_rfl (by norm_num)
  -- ### the a.e.-in-`z` domination `w² · I ≤ K0 · JintF + K0(1+3C1)(Q 0 + Q 1 + Q 2)`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.w z) ^ 2 * I z
        ≤ K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici,
      Filter.Eventually.of_forall (hK0 α F Ψ hα hα4 h), hC1 α F Ψ hα hα4 h]
      with z hz h1 h2
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- at `z = 0` the weight `w` vanishes, and the right-hand side is nonnegative
      subst hz0
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      have hMJ : 0 ≤ K0 * JintF 0 := mul_nonneg hK0nn (hJnn 0)
      have hK1 : 0 ≤ K0 * (1 + 3 * C1) := mul_nonneg hK0nn (by linarith)
      have hsum0 : 0 ≤ Q 0 0 + Q 1 0 + Q 2 0 := by
        have := hQnn 0 0; have := hQnn 1 0; have := hQnn 2 0; linarith
      have hMQ : 0 ≤ K0 * (1 + 3 * C1) * (Q 0 0 + Q 1 0 + Q 2 0) := mul_nonneg hK1 hsum0
      rw [hw0]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      linarith [hMJ, hMQ]
    · -- the honest case `z > 0`
      have h1z : I z ≤ K0 * (Fs z + Ps 0 z + Zt z + Dt z) := by
        simp only [hI, hFs, hPs, hZt, hDt]
        exact h1 hzpos
      have h2z := h2 hzpos
      have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hZ := h2z.1
      have hD := h2z.2
      have hZ' : (Work.Spaces.w z) ^ 2 * Zt z ≤ C1 * (Q 1 z + Q 2 z) := by
        calc (Work.Spaces.w z) ^ 2 * Zt z
            ≤ (Work.Spaces.w z) ^ 2 * (C1 * (Ps 1 z + Ps 2 z)) :=
              mul_le_mul_of_nonneg_left hZ hw
          _ = C1 * (Q 1 z + Q 2 z) := by rw [← hQeq 1 z, ← hQeq 2 z]; ring
      have hD' : (Work.Spaces.w z) ^ 2 * Dt z ≤ C1 * Q 1 z := by
        calc (Work.Spaces.w z) ^ 2 * Dt z
            ≤ (Work.Spaces.w z) ^ 2 * (C1 * Ps 1 z) := mul_le_mul_of_nonneg_left hD hw
          _ = C1 * Q 1 z := by rw [← hQeq 1 z]; ring
      calc (Work.Spaces.w z) ^ 2 * I z
          ≤ (Work.Spaces.w z) ^ 2 * (K0 * (Fs z + Ps 0 z + Zt z + Dt z)) :=
            mul_le_mul_of_nonneg_left h1z hw
        _ = K0 * ((Work.Spaces.w z) ^ 2 * Fs z + (Work.Spaces.w z) ^ 2 * Ps 0 z
              + (Work.Spaces.w z) ^ 2 * Zt z + (Work.Spaces.w z) ^ 2 * Dt z) := by ring
        _ ≤ K0 * (JintF z + Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z) := by
            refine mul_le_mul_of_nonneg_left ?_ hK0nn
            linarith [hFsQ z hz, hQeq 0 z, hZ', hD']
        _ ≤ K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
            have hinner : Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z
                ≤ (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
              have h3 : 0 ≤ C1 * (3 * Q 0 z + Q 1 z + 2 * Q 2 z) :=
                mul_nonneg hC1nn (by linarith [hQnn 0 z, hQnn 1 z, hQnn 2 z])
              nlinarith [h3, hQnn 0 z, hQnn 1 z, hQnn 2 z]
            calc K0 * (JintF z + Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z)
                = K0 * JintF z + K0 * (Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z) := by ring
              _ ≤ K0 * JintF z + K0 * ((1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z)) :=
                  add_le_add le_rfl (mul_le_mul_of_nonneg_left hinner hK0nn)
              _ = K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by ring
  -- ### integrability of the dominating function
  have hIntJ : MeasureTheory.Integrable JintF
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := h.memF.2
  have hIntQ : ∀ j, j ≤ 2 → MeasureTheory.Integrable (Q j)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro j hj
    have hbase := Work.FTS.EllipticEst.integrableOn_slice_Iz α 2 ((hsmΨ.pth).pth) h.memB j hj
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
    rw [hQ]
    beta_reduce
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp [Work.Spaces.w]
    · refine MeasureTheory.integral_congr_ae
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_))
      beta_reduce
      have hp : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨hzpos, hθ⟩
      have hcomm : Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ) z θ :=
        Work.EllipticEst.H2W.pthIter2_DzIter_comm hsmΨ j hp
      rw [hcomm]
      rfl
  -- ### the integrated comparison
  have hIntQsum : MeasureTheory.Integrable (fun z => Q 0 z + Q 1 z + Q 2 z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hIntQ 0 (by norm_num)).add (hIntQ 1 (by norm_num))).add (hIntQ 2 (by norm_num))
  have hMint : MeasureTheory.Integrable
      (fun z => K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hIntJ.const_mul K0).add (hIntQsum.const_mul (K0 * (1 + 3 * C1)))
  have hmain : ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * I z
      ≤ ∫ z in Work.Spaces.Iz,
          K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (by
        rw [hI]; beta_reduce
        refine MeasureTheory.integral_nonneg_of_ae
          ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
            (Filter.Eventually.of_forall fun θ hθ => ?_))
        exact mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _)))
      hMint hslice
  -- ### the right-hand side
  set L : ℕ → ℝ := fun j => Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) with hLdef
  have hLnn : ∀ j, 0 ≤ L j := fun j => by
    rw [hLdef]; beta_reduce
    rw [Work.Spaces.L2Sq]
    exact MeasureTheory.integral_nonneg fun z =>
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hQint : ∀ j, ∫ z in Work.Spaces.Iz, Q j z = L j := fun j => by
    rw [hQ, hLdef]
    beta_reduce
    rw [Work.Spaces.L2Sq]
  have hJint : ∫ z in Work.Spaces.Iz, JintF z = Work.Spaces.HkSq α 2 F := rfl
  have hsum : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      = L 0 + L 1 + L 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hLdef]
  -- ### the value of the dominating integral
  have hE : ∫ z in Work.Spaces.Iz,
        (K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      = K0 * Work.Spaces.HkSq α 2 F + K0 * (1 + 3 * C1) * (L 0 + L 1 + L 2) := by
    rw [MeasureTheory.integral_add (f := fun z => K0 * JintF z)
      (g := fun z => K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      (hIntJ.const_mul K0) (hIntQsum.const_mul (K0 * (1 + 3 * C1)))]
    rw [MeasureTheory.integral_const_mul K0 JintF,
      MeasureTheory.integral_const_mul (K0 * (1 + 3 * C1))
        (fun z => Q 0 z + Q 1 z + Q 2 z)]
    rw [MeasureTheory.integral_add (f := fun z => Q 0 z + Q 1 z) (g := fun z => Q 2 z)
      ((hIntQ 0 (by norm_num)).add (hIntQ 1 (by norm_num))) (hIntQ 2 (by norm_num))]
    rw [MeasureTheory.integral_add (f := fun z => Q 0 z) (g := fun z => Q 1 z)
      (hIntQ 0 (by norm_num)) (hIntQ 1 (by norm_num))]
    rw [hJint, hQint 0, hQint 1, hQint 2]
  -- ### assembly
  have hLHS : Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * I z := by
    rw [slot01_LHS_eq α hα hα4 Ψ]
  rw [hLHS, hsum]
  refine le_trans (le_trans hmain (le_of_eq hE)) ?_
  have hH0 : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hS0 : 0 ≤ L 0 + L 1 + L 2 := by
    have := hLnn 0; have := hLnn 1; have := hLnn 2; linarith
  have hKC : 0 ≤ K0 * C1 := mul_nonneg hK0nn hC1nn
  -- `K0 ≤ K0 · (1 + 3 C1)`
  have hXK : K0 ≤ K0 * (1 + 3 * C1) := by nlinarith [hKC]
  have hA : K0 * Work.Spaces.HkSq α 2 F
      ≤ (K0 * (1 + 3 * C1)) * Work.Spaces.HkSq α 2 F :=
    mul_le_mul_of_nonneg_right hXK hH0
  nlinarith [hA, hS0, hH0]

end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.IPGen.OpenBasic =====
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

/-! ## Block continuity and block additivity from `SmoothOpen` -/


/-- **Block additivity from interior smoothness**: for `SmoothOpen f₁`, `SmoothOpen f₂` every
mixed derivative of `f₁ + f₂` splits on the open quadrant (`SmoothOpen.mixed_add`). -/
theorem BlocksAdd_of_smoothOpen {k : ℕ} {f₁ f₂ : Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen f₁) (h₂ : Work.FTS.EllipticEst.SmoothOpen f₂) :
    Work.FTS.CoercivityFix.Assembly.BlocksAdd k f₁ f₂ := by
  intro a b _ z θ hzθ
  exact h₁.mixed_add h₂ b a z θ hzθ.1 hzθ.2.1 hzθ.2.2

/-! ## Descent of `HkMem` along the recursion slots -/

/-- **`HkMem` descends one level along `D_θ`** (for `α` in the sharp range `-(1/10) ≤ α`
where `η ≤ γ`, which is precisely the range in which the pure `D_z`-slots of `D_θf` are
dominated by the mixed `(1,·)`-slots of `f`).

The pointwise domination with constant `1` is
`CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge`; `HkMem_of_majorant` turns it into membership,
the continuity input being `SmoothOpen.continuousOn_HkIntegrand` of `SmoothOpen.Dth`. -/
theorem HkMem_Dth_le {α : ℝ} {k : ℕ} {f : Fn} (hα : -(1 / 10 : ℝ) ≤ α)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α (k + 1) f) :
    Work.Spaces.HkMem α k (Work.Spaces.Dth f) :=
  Work.FTS.LocData.HkMem_of_majorant α k (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (k + 1) f z θ)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hf).continuousOn_HkIntegrand α k)
    hm.1 hm.2
    (fun z hz θ hθ => Work.FTS.CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge α hα k f z θ hz hθ)

/-- **`HkMem` descends one level along `D_z`** (no restriction on `α`).  This is the
`SmoothOpen`-hypothesis version of `EllipticEst.remov.EllWeakPos.HkMem_Dz_shift` (which spends
the intermediate level `k`), via the pointwise domination
`EllipticEst.UopHk.HkIntegrand_Dz_le_succ`. -/
theorem HkMem_Dz_le {α : ℝ} {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α (k + 1) f) : Work.Spaces.HkMem α k (Work.Spaces.Dz f) :=
  Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α k hf hm

/-- **`HkMem` descends any number of levels** in the open class: this is
`OpenPkg.HkMem_mono_open`, restated in this chapter's namespace for convenience. -/
theorem HkMem_mono_le {α : ℝ} {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ l : ℕ, l ≤ k → Work.Spaces.HkMem α k f → Work.Spaces.HkMem α l f :=
  Work.FTS.OpenPkg.HkMem_mono_open hf

/-- The descent triple consumed by the `HkIPStep`-lift of the `add` clause: from the
level-`(k+1)` honesty of `f` (and its interior smoothness) one gets the level-`k` honesty of
`f`, `D_θf` and `D_zf`. -/
theorem HkMem_descent {α : ℝ} {k : ℕ} {f : Fn} (hα : -(1 / 10 : ℝ) ≤ α)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α (k + 1) f) :
    Work.Spaces.HkMem α k f ∧ Work.Spaces.HkMem α k (Work.Spaces.Dth f)
      ∧ Work.Spaces.HkMem α k (Work.Spaces.Dz f) :=
  ⟨Work.FTS.OpenPkg.HkMem_mono_open hf k (Nat.le_succ k) hm,
    HkMem_Dth_le hα hf hm, HkMem_Dz_le hf hm⟩

end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.AngRadHkMem =====
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

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `ℋ⁴`-integrand of an angular `×` radial product is dominated by the product of the
radial density with the separated angular majorant.**

This is a local restatement of `Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le` in the
form (with the weight factor of the `B1`-term grouped as `G(θ)²·smG α θ`) used by the majorant
criterion below. -/
private theorem hkIntegrand_ang_rad_le {α : ℝ} {a r G : ℝ → ℝ} {B0 B1 : ℝ}
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
      ≤ Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by
  have h := Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le (α := α) (a := a) (r := r)
    (G := G) (B0 := B0) (B1 := B1) (z := z) ha0 ha1 hθ
  calc Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
      ≤ Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) := h
    _ = Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by
        ring

/-- **Integrability of the separated angular majorant and of its `z`-slice-integral.**

Local restatement of `Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable`, with the
weight factor of the `B1`-term grouped as `G(θ)²·smG α θ`. -/
private theorem majorant_integrable {α : ℝ} {r G : ℝ → ℝ} {B0 B1 : ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)))
        Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.Nonlinear.RadialProd.Rint r z
            * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
                + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)))
        Work.Spaces.Iz := by
  have hAng : MeasureTheory.IntegrableOn
      (fun θ : ℝ => B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
      Work.Spaces.Iθ :=
    (Work.FTS.NonlinRows.AuxAngRad.integrableOn_smE.const_mul _).add (hGint.const_mul _)
  refine ⟨fun z _ => hAng.const_mul _, ?_⟩
  have hRint := Work.FTS.NonlinRows.AuxAngRad.integrableOn_Rint_of_HkMem hrmem
  have hK : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.Nonlinear.RadialProd.Rint r z
        * (∫ θ in Work.Spaces.Iθ, (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))))
      Work.Spaces.Iz := hRint.mul_const _
  refine MeasureTheory.IntegrableOn.congr_fun hK (fun z _ => ?_) measurableSet_Ici
  rw [MeasureTheory.integral_const_mul]

theorem AngRadHkMem {α : ℝ} {a r G : ℝ → ℝ} {B0 B1 : ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z))
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) := by
  -- The product datum is `C^∞` on the open quadrant, hence its `ℋ⁴`-integrand is continuous
  -- there.
  have hsmooth : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * r z) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad ha hr
  obtain ⟨hMslice, hMz⟩ := majorant_integrable (α := α) (r := r) (G := G)
    (B0 := B0) (B1 := B1) hGint hrmem
  -- The majorant criterion, with the majorant written out explicitly so that the final goal
  -- is the pointwise domination.
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := fun z θ => a θ * r z)
    (M := fun z θ => Work.FTS.Nonlinear.RadialProd.Rint r z
      * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))) ?_ ?_ ?_ ?_
  · exact hsmooth.continuousOn_HkIntegrand α 4
  · exact hMslice
  · exact hMz
  · intro z _ θ hθ
    exact hkIntegrand_ang_rad_le (α := α) (a := a) (r := r) (G := G) (B0 := B0) (B1 := B1)
      ha0 ha1 hθ

end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Gs_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Row19GsAux

open Work.FTS.Nonlinear.Pieces.RNP (Gs)

/-! ## Plumbing: `pzIter` as an iterated derivative, congruence, and the constant rule -/

/-- The iterated plain `z`-derivative is the `k`-fold derivative of the `θ`-slice. -/
theorem pzIter_eq_iter_deriv_aux (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter k f z θ = deriv^[k] (fun t => f t θ) z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    rw [show (fun z' : ℝ => Work.Spaces.pzIter k f z' θ) = deriv^[k] (fun t => f t θ) from
      funext (fun z' => ih z')]
    exact congrFun (Function.iterate_succ_apply' deriv k (fun t => f t θ)).symm z

/-- Iterated `deriv` respects eventual equality. -/
theorem iterDeriv_eventuallyEq {f g : ℝ → ℝ} {z : ℝ} (h : f =ᶠ[𝓝 z] g) (k : ℕ) :
    deriv^[k] f =ᶠ[𝓝 z] deriv^[k] g := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have h1 : deriv^[k + 1] f = deriv (deriv^[k] f) := by
      funext x; rw [Function.iterate_succ_apply']
    have h2 : deriv^[k + 1] g = deriv (deriv^[k] g) := by
      funext x; rw [Function.iterate_succ_apply']
    rw [h1, h2]
    exact ih.deriv

/-- Iterated `deriv` is a local operation. -/
theorem iterDeriv_congr_of_eventuallyEq {f g : ℝ → ℝ} {z : ℝ}
    (h : f =ᶠ[𝓝 z] g) (k : ℕ) : deriv^[k] f z = deriv^[k] g z :=
  (iterDeriv_eventuallyEq h k).eq_of_nhds

/-- The constant rule for the iterated derivative. -/
theorem iterDeriv_const_mul {c z : ℝ} (k : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ ((k : ℕ∞) : WithTop ℕ∞) f z) :
    deriv^[k] (fun t => c * f t) z = c * deriv^[k] f z := by
  rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
  exact iteratedDeriv_const_mul c hf

/-- `Hz` is `C^k` near every `z > -1`, for every finite `k`. -/
theorem contDiffAt_Hz_finite (k : ℕ) {z : ℝ} (hz : -1 < z) :
    ContDiffAt ℝ ((k : ℕ∞) : WithTop ℕ∞) Work.FTS.Nonlinear.FstarPkg.Hz z :=
by
  have hle : ((k : ℕ∞) : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [show Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  exact (contDiffOn_Hz.of_le (m := ((k : ℕ∞) : WithTop ℕ∞)) hle).contDiffAt
    (isOpen_Ioi.mem_nhds hz)

/-! ## The separated form of the profile -/

/-- For `z > -1` the profile `D_zF_*` is the product of the angular factor `α·Γ(θ)/c` and the
radial factor `Hz`. -/
theorem Gs_eq_factor {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : -1 < z) :
    Gs α z θ = (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
      * Work.FTS.Nonlinear.FstarPkg.Hz z := by
  change Work.Spaces.Dz (Work.Construction.Fstar α) z θ = _
  rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα hz]
  ring

/-- The `z`-slices of `Gs α` are `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_slice_Gs {α : ℝ} (hα : 0 < α) (θ : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => Gs α z θ) (Set.Ioi (-1)) :=
  ((contDiffOn_const (c := α * Work.Spaces.Gam α θ / Work.Spaces.c α)).mul
      contDiffOn_Hz).congr
    (fun t ht => Gs_eq_factor hα ht)

/-- The iterated plain `z`-derivative of `Gs α` factors as the angular factor times the
`k`-th derivative of `Hz`. -/
theorem pzIter_Gs_factor {α : ℝ} (hα : 0 < α) (k : ℕ) {z θ : ℝ} (hz : -1 < z) :
    Work.Spaces.pzIter k (Gs α) z θ
      = (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z := by
  have hF : (fun t : ℝ => Gs α t θ)
      =ᶠ[𝓝 z] (fun t : ℝ => (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * Work.FTS.Nonlinear.FstarPkg.Hz t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    exact Gs_eq_factor hα ht
  rw [pzIter_eq_iter_deriv_aux,
    iterDeriv_congr_of_eventuallyEq (f := fun t : ℝ => Gs α t θ)
      (g := fun t : ℝ => (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * Work.FTS.Nonlinear.FstarPkg.Hz t) hF k]
  exact iterDeriv_const_mul k Work.FTS.Nonlinear.FstarPkg.Hz (contDiffAt_Hz_finite k hz)

/-- **The `D_z`-factorisation of the profile.**  The angular factor is a constant for the
radial operator `D_z`. -/
theorem DzIter_Gs_factor {α : ℝ} (hα : 0 < α) (m : ℕ) {z θ : ℝ} (hz : -1 < z) :
    Work.Spaces.DzIter m (Gs α) z θ
      = (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ := by
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (h := Gs α) (θ := θ)
    (contDiffOn_slice_Gs hα θ) m z hz]
  rw [DzIter_Hz_eq_sum m z θ hz, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pzIter_Gs_factor hα k hz]
  ring

/-! ## The angular factorisation of the `D_θ`-iterates -/

/-- `D_θ^i` vanishes on the profile whenever `sin 2θ = 0`, for `i ≥ 1`. -/
theorem DthIter_succ_eq_zero_of_sin {f : ℝ → ℝ → ℝ} {θ : ℝ} (h : Real.sin (2 * θ) = 0)
    (j : ℕ) (z : ℝ) : Work.Spaces.DthIter (j + 1) f z θ = 0 := by
  rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, h, zero_mul]

/-- A `D_z`-iterate of a function whose `θ`-slice is identically zero vanishes. -/
theorem DzIter_eq_zero_of_slice_zero {g : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, g z θ = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DzIter m g z θ = 0 := by
  induction m generalizing z with
  | zero => exact h z
  | succ m ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    have hfun : (fun z' : ℝ => Work.Spaces.DzIter m g z' θ) = fun _ : ℝ => (0 : ℝ) :=
      funext (fun z' => ih z')
    rw [hfun]; simp

/-- **The `D_θ`-factorisation of the profile.**  On the open angular interval the angular
operator only sees the angular factor `α·Γ(θ)/c`; the radial factor `Hz` is a constant for
`D_θ`. -/
theorem DthIter_Gs_factor {α : ℝ} (hα : 0 < α) (i : ℕ) {z θ : ℝ} (hz : -1 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DthIter i (Gs α) z θ
      = (α / Work.Spaces.c α)
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
        * Work.FTS.Nonlinear.FstarPkg.Hz z := by
  have hmain : ∀ i : ℕ, ∀ z θ : ℝ, -1 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DthIter i (Gs α) z θ
        = Work.Spaces.dthU^[i] (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α) θ
          * Work.FTS.Nonlinear.FstarPkg.Hz z := by
    intro i
    induction i with
    | zero =>
      intro z θ hz hθ
      rw [Work.Spaces.DthIter_zero, Function.iterate_zero, id_eq]
      exact Gs_eq_factor hα hz
    | succ i ih =>
      intro z θ hz hθ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hev : (fun θ' : ℝ => Work.Spaces.DthIter i (Gs α) z θ')
          =ᶠ[𝓝 θ] (fun θ' : ℝ =>
            Work.Spaces.dthU^[i] (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α) θ'
              * Work.FTS.Nonlinear.FstarPkg.Hz z) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'
      rw [Filter.EventuallyEq.deriv_eq hev,
        Work.Spaces.deriv_mul_const' (Work.FTS.Nonlinear.FstarPkg.Hz z) θ
          (Work.Spaces.dthU^[i] (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α))]
      have hd : Work.Spaces.dthU^[i + 1]
            (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α) θ
          = Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[i]
              (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α)) θ := by
        rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply]
      rw [hd]
      ring
  rw [hmain i z θ hz hθ]
  rw [show (fun t : ℝ => α * Work.Spaces.Gam α t / Work.Spaces.c α)
      = (fun t : ℝ => (α / Work.Spaces.c α) * Work.Spaces.Gam α t) from by
    funext t; ring]
  rw [Work.Spaces.dthU_iter_const_mul,
    Work.FTS.LocData.DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]

/-- The `z`-slices of the `D_θ`-iterates of the profile are `C^∞` on `(-1,∞)` (in the open
angular class). -/
theorem contDiffOn_slice_DthIter_Gs {α : ℝ} (hα : 0 < α) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Spaces.DthIter i (Gs α) z θ) (Set.Ioi (-1)) :=
  ((contDiffOn_const (c := (α / Work.Spaces.c α)
      * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)).mul
    contDiffOn_Hz).congr
    (fun t ht => DthIter_Gs_factor hα i ht hθ)

/-- **The `D_z`-factorisation of the angular iterates of the profile.** -/
theorem DzIter_DthIter_Gs_factor {α : ℝ} (hα : 0 < α) (i m : ℕ) {z θ : ℝ}
    (hz : -1 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter m (Work.Spaces.DthIter i (Gs α)) z θ
      = ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
        * Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ := by
  have hpk : ∀ k : ℕ, Work.Spaces.pzIter k (Work.Spaces.DthIter i (Gs α)) z θ
      = ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
        * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z := by
    intro k
    have hF : (fun t : ℝ => Work.Spaces.DthIter i (Gs α) t θ)
        =ᶠ[𝓝 z] (fun t : ℝ => ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
          * Work.FTS.Nonlinear.FstarPkg.Hz t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
      exact DthIter_Gs_factor hα i ht hθ
    rw [pzIter_eq_iter_deriv_aux,
      iterDeriv_congr_of_eventuallyEq (f := fun t : ℝ => Work.Spaces.DthIter i (Gs α) t θ)
        (g := fun t : ℝ => ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
          * Work.FTS.Nonlinear.FstarPkg.Hz t) hF k]
    exact iterDeriv_const_mul k Work.FTS.Nonlinear.FstarPkg.Hz (contDiffAt_Hz_finite k hz)
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth
      (h := Work.Spaces.DthIter i (Gs α)) (θ := θ)
      (contDiffOn_slice_DthIter_Gs hα i hθ) m z hz,
    DzIter_Hz_eq_sum m z θ hz, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hpk k]
  ring

end Row19GsAux

open Row19GsAux

theorem Gs_bounds : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    (∀ m : ℕ, m ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter m (Work.FTS.Nonlinear.Pieces.RNP.Gs α) z θ|
        ≤ C * α * (z / (1 + z) ^ 2)) ∧
    (∀ i m : ℕ, 1 ≤ i → i ≤ 4 → m ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.FTS.Nonlinear.Pieces.RNP.Gs α))
          z θ|
        ≤ C * α * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
            * (z / (1 + z) ^ 2)) := by
  obtain ⟨CH, hCHpos, hCH⟩ := abs_DzIter_Hz_le
  refine ⟨10 * CH + 1, by linarith, fun α hα hα1 => ⟨?_, ?_⟩⟩
  · intro m hm z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hw : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz0 (by positivity)
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hcoef : |α * Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 * α := by
      rw [abs_div, abs_of_pos hcpos, abs_mul, abs_of_pos hα, abs_of_nonneg hG0]
      rw [div_le_iff₀ hcpos]
      nlinarith
    have hHz := hCH m hm z hz0 θ
    rw [DzIter_Gs_factor hα m hz1, abs_mul]
    calc |α * Work.Spaces.Gam α θ / Work.Spaces.c α|
            * |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
        ≤ (10 * α) * (CH * (z / (1 + z) ^ 2)) :=
          mul_le_mul hcoef hHz (abs_nonneg _) (mul_nonneg (by norm_num) hα.le)
      _ ≤ (10 * CH + 1) * α * (z / (1 + z) ^ 2) := by nlinarith [hw, hCHpos]
  · intro i m hi1 hi4 hm z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hw : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz0 (by positivity)
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · -- the origin angle: both the profile and its angular factor vanish
      subst h0
      have hzero : ∀ z' : ℝ, Work.Spaces.DthIter i
          (Work.FTS.Nonlinear.Pieces.RNP.Gs α) z' 0 = 0 := by
        intro z'
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact DthIter_succ_eq_zero_of_sin (by simp) j z'
      rw [DzIter_eq_zero_of_slice_zero hzero m z, abs_zero]
      have hR : 0 ≤ (10 * CH + 1) * α
          * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 0|
          * (z / (1 + z) ^ 2) := by positivity
      linarith
    rcases eq_or_lt_of_le hθ.2 with hpi | hpi
    · -- the right endpoint of the angular interval
      subst hpi
      have hzero : ∀ z' : ℝ, Work.Spaces.DthIter i
          (Work.FTS.Nonlinear.Pieces.RNP.Gs α) z' (Real.pi / 2) = 0 := by
        intro z'
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact DthIter_succ_eq_zero_of_sin
          (by rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]) j z'
      rw [DzIter_eq_zero_of_slice_zero hzero m z, abs_zero]
      have hR : 0 ≤ (10 * CH + 1) * α
          * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 (Real.pi / 2)|
          * (z / (1 + z) ^ 2) := by positivity
      linarith
    · -- the interior of the angular interval
      rw [DzIter_DthIter_Gs_factor hα i m hz1 ⟨h0, hpi⟩, abs_mul]
      have hcoef : |(α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ 10 * α
          * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| := by
        rw [abs_mul, abs_div, abs_of_pos hcpos, abs_of_pos hα]
        rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]
        have hC0 : (0 : ℝ) ≤ |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| :=
          abs_nonneg _
        nlinarith [mul_nonneg hα.le hC0]
      have hHz := hCH m hm z hz0 θ
      calc |(α / Work.Spaces.c α)
              * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
            * |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
          ≤ (10 * α * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|)
              * (CH * (z / (1 + z) ^ 2)) :=
            mul_le_mul hcoef hHz (abs_nonneg _) (by positivity)
        _ ≤ (10 * CH + 1) * α
              * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
              * (z / (1 + z) ^ 2) := by
            have hC0 : (0 : ℝ) ≤ |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| :=
              abs_nonneg _
            nlinarith [mul_nonneg (mul_nonneg hα.le hC0) hw, hCHpos]

end

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs_lipschitz =====
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

/-- The half strip `(-1,∞) × (0,π/2)`: the set on which `Φ_s` is smooth (`SmoothQuad`), and
on which the coefficient `V(Φ̃_*)` is smooth as well.  (Contrary to the *weighted* coefficient
`((z+1)/z)·ℛ(Φ̃_*)` of row 11 there is no `1/z`-factor here, so the smoothness survives down
to `z = 0`.) -/
abbrev HalfStrip : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Positivity of `c(α)` and the profile identity `L₁₂(F_*) = 2α/(1+z)` for every `α > 0` -/

/-- `c(α) = ∫₀^{π/2} Γ(θ)K(θ) dθ` is positive for every `α > 0` — the integrand
`Γ K = 3 (sinθ cos²θ)^{1+α/3}` is strictly positive on the open interval `(0,π/2)`.
(This is the general-`α` strengthening of `Work.Coercivity.c_pos`, which assumes `α ≤ 1`.) -/
theorem c_pos_of_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.c α := by
  have hint : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ :=
    Work.Spaces.CAux.integrableOn_GamK α hα
  have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with θ hθ
    exact (Work.Spaces.gamK_bounds α θ hα hθ).1
  have hmem : ∀ θ ∈ Set.Ioo (Real.pi / 6) (Real.pi / 3),
      θ ∈ Function.support (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    intro θ hθ
    have h1 : 0 < θ := by linarith [hθ.1, Real.pi_pos]
    have h2 : θ < Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
    have hu : 0 < Real.sin θ * Real.cos θ ^ 2 := mul_pos hsin (pow_pos hcos 2)
    have hGam : 0 < Work.Spaces.Gam α θ := by
      rw [Work.Spaces.Gam]
      exact Real.rpow_pos_of_pos hu _
    have hK : 0 < Work.Spaces.K θ := by rw [Work.Spaces.K]; positivity
    simp only [Function.mem_support]
    exact ne_of_gt (mul_pos hGam hK)
  have hmeas : 0 < volume (Function.support
      (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ) ∩ Work.Spaces.Iθ) := by
    have hsub : Set.Ioo (Real.pi / 6) (Real.pi / 3) ⊆
        Function.support (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
          ∩ Work.Spaces.Iθ := by
      intro θ hθ
      exact ⟨hmem θ hθ, ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩⟩
    have hvol : 0 < volume (Set.Ioo (Real.pi / 6) (Real.pi / 3)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
    exact lt_of_lt_of_le hvol (measure_mono hsub)
  have hpos := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint).mpr hmeas
  simpa [Work.Spaces.c] using hpos

/-- The angular density of `L₁₂` at the profile `F_*` is `α · F_*(s)/s`, for **every**
`α > 0` (the general-`α` version of `Work.Construction.L12dens_Fstar`). -/
theorem L12dens_Fstar_pos {α : ℝ} (hα : 0 < α) (s : ℝ) :
    Work.Construction.L12dens (Work.Construction.Fstar α) s
      = α * (Work.FM.Fstar s / s) := by
  have hc : Work.Spaces.c α ≠ 0 := ne_of_gt (c_pos_of_pos hα)
  rw [Work.Construction.L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [setIntegral_congr_fun (s := Set.Icc 0 (Real.pi / 2)) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [integral_mul_const]
  have hcint : (∫ θ in Set.Icc 0 (Real.pi / 2),
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α) = α := by
    rw [integral_div, integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval, mul_div_assoc, div_self hc, mul_one]
  rw [hcint]

/-- **The profile identity `L₁₂(F_*)(z) = 2α/(1+z)` for every `α > 0` and every `z > -1`** —
the general-`α` version of `Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one`. -/
theorem L12Fstar_eq_pos {α z : ℝ} (hα : 0 < α) (hz : -1 < z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun (s := Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
            = α * (Work.FM.Fstar s / s) from L12dens_Fstar_pos hα s)]
  rw [MeasureTheory.integral_const_mul,
    Work.FTS.Nonlinear.FstarPkg.integral_Ioi_Fstar_div_of_gt_neg_one z hz]
  ring

/-! ## Smoothness of the coefficient `V(Φ̃_*)` on the half strip -/

/-- `Θ_* = (1/(4α)) sin(2θ) L₁₂(F_*)` is `C^∞` on the half strip `(-1,∞) × (0,π/2)`: the
profile identity turns it into the elementary `sin(2θ)/(2(1+z))`. -/
theorem ThetaFstar_contDiffOn_neg_one {α : ℝ} (hα : 0 < α) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Theta α (Work.Construction.Fstar α)))
      HalfStrip := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) HalfStrip := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) HalfStrip :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) HalfStrip :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ HalfStrip, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have h1 : -1 < p.1 := Set.mem_Ioi.mp hp.1
      have : (0 : ℝ) < 1 + p.1 := by linarith
      positivity
    exact hnum.div hden hne
  refine hsmooth.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : -1 < z := Set.mem_Ioi.mp hp.1
  simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  rw [L12Fstar_eq_pos hα hz]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hzne : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp
  ring

/-- **`V(Φ̃_*)` is `C^∞` on the half strip `(-1,∞) × (0,π/2)`** — in particular it is
continuous in `z` down to `z = 0`, which is what the Lipschitz bound needs.  (This is the
improvement of `Rv_smooth`, which only gives smoothness on the *open* quadrant `z > 0` for
the `1/z`-weighted row-11 coefficient.) -/
theorem Vs_smoothQuad {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) := by
  have hVopen : IsOpen HalfStrip := isOpen_Ioi.prod isOpen_Ioo
  have hΦ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Φs) HalfStrip :=
    hs.smooth
  have hΘ : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Theta α (Work.Construction.Fstar α))) HalfStrip :=
    ThetaFstar_contDiffOn_neg_one (α := α) hα
  have hΨ : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))
      HalfStrip := by
    refine (hΦ.sub hΘ).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    rfl
  have hpth := Work.FTS.LocData.contDiffOn_pth hVopen hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) HalfStrip :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) HalfStrip :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hcosne : ∀ p ∈ HalfStrip, Real.cos p.2 ≠ 0 := by
    intro p hp
    have hθ := Set.mem_Ioo.mp hp.2
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ.2⟩)
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) HalfStrip := hsin.div hcos hcosne
  show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) HalfStrip
  have hfun : Function.uncurry (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))
      = fun p : ℝ × ℝ =>
          Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) p.1 p.2
            - (Real.sin p.2 / Real.cos p.2)
              * Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs p.1 p.2 := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.Vop, Real.tan_eq_sin_div_cos]
  rw [hfun]
  exact hpth.sub (htan.mul hΨ)

/-! ## The Lipschitz bound -/

theorem Vs_lipschitz {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          - Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs 0 θ|
        ≤ max Cs 0 * α * z := by
  intro z hz θ hθ
  have hz0 : 0 ≤ z := hz
  have hsq := Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun ζ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs ζ θ) (Set.Ioi (-1)) :=
    hsq.curry_z hθ
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) z,
      DifferentiableAt ℝ (fun ζ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs ζ θ) x := by
    intro x hx
    have hx1 : x ∈ Set.Ioi (-1) := by
      rw [Set.mem_Ioi]; linarith [hx.1]
    exact (hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hx1)
  have hbdd : ∀ x ∈ Set.Icc (0 : ℝ) z,
      ‖deriv (fun ζ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs ζ θ) x‖
        ≤ max Cs 0 * α := by
    intro x hx
    have hxI : x ∈ Work.Spaces.Iz := hx.1
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hb := Work.FTS.Nonlinear.Pieces.RNP.abs_dVs_le (α := α) (Cs := Cs) (Φs := Φs)
      hα hs x hxI θ hθI
    rw [Real.norm_eq_abs]
    have hder : deriv (fun ζ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs ζ θ) x
        = Work.Spaces.pz (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) x θ := rfl
    rw [hder]
    refine le_trans ?_ hb
    rw [abs_mul, abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x + 1)]
    nlinarith [abs_nonneg (Work.Spaces.pz (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) x θ),
      hx.1]
  have hmain := (convex_Icc (0 : ℝ) z).norm_image_sub_le_of_norm_deriv_le hdiff hbdd
    (left_mem_Icc.mpr hz0) (right_mem_Icc.mpr hz0)
  simpa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hz0] using hmain

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.dthIter_Vs_le_WlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

theorem dthIter_Vs_le_WlInf {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) z θ|
        ≤ Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  -- `Vs α Φs` is by definition `Vop (PhiTil α F_* Φs)`, whose `𝒲^{4,∞}`-membership is the
  -- field `StarPkg.V`.  For `i ≥ 1` the angular derivative `D_θ^i` occupies exactly the mixed
  -- slot `(j, k) = (i, 0)` of the `𝒲^{4,∞}`-norm, and the slot bound
  -- `Spaces.pz_Dth_sup_bound` is precisely the stated inequality (with `(z+1)^0 = 1`).
  intro i hi hi4 z hz θ hθ
  have hmem : Work.Spaces.WlInfMem α 4 (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) := by
    simpa only [Work.FTS.Nonlinear.Pieces.RNP.Vs, Work.FTS.Nonlin.PhiTs] using hs.V.1
  have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) hmem
    i 0 hi (by omega) z θ hz hθ
  simpa using h

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
-- ===== merged: Submission.Work.FTS.OpenPkg.l12zero_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

variable {f : ℝ → ℝ → ℝ}

/-- **Joint continuity of `(z,θ) ↦ (f z θ)²` on the open quadrant**, from `SmoothOpen f`.  This is
`l12q_quad_continuous` of `Work.FTS.H2.L12ZeroQ` with `SmoothQuad` weakened to `SmoothOpen` (the
two sets are literally the same open quadrant, so no restriction step is needed). -/
theorem l12zero_quad_continuous (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hsm.continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
  simpa only [Function.uncurry] using h2

/-- **A.e. strong measurability of the Hardy-weighted angular energy in the interior class**, from
mere continuity of the datum on the open quadrant: `r ↦ (∫_θ f(r,θ)²)·((1+r)/r)²` on `(0,∞)`.
By Fubini from the joint a.e. strong measurability of `(r,θ) ↦ (f r θ)²` for the product of the
restrictions of Lebesgue measure to `Iz` and `Iθ` (`Work.Spaces.aesm_of_continuousOn_Qd`); the
Hardy weight `r ↦ ((1+r)/r)²` is continuous on `(0,∞)`. -/
theorem l12zero_energy_aesm
    (hc : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hsq : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    change ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) _
    exact hc.pow 2
  have hquad : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hsq
  have hslice : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hquad
  have hmono : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      ≤ MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hslice.mono_measure hmono
  have hw : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((ContinuousOn.div (continuousOn_const.add continuousOn_id) continuousOn_id
      (fun r hr => ne_of_gt (Set.mem_Ioi.mp hr))).pow 2).aestronglyMeasurable measurableSet_Ioi
  exact h1.mul hw

/-- **Integrability of the squared angular slice in the interior class.**  For `SmoothOpen f` and
`HkMem α 4 f`, every radial slice `θ ↦ (f z θ)²` with `z > 0` is integrable on `Iθ`.

This is `Work.FTS.H2.l12q_slice_sq_integrableOn` with `SmoothQuad` replaced by `SmoothOpen`: for
a.e. `θ ∈ Iθ` (all `θ ∈ Ioo 0 (π/2)`) one has `0 < sin(2θ) ≤ 1` and `w z ≥ 1`, so
`(f z θ)² ≤ (f z θ·(w z/sin(2θ)^{η/2}))² ≤ HkIntegrand α 4 f z θ`
(`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`); the majorant is integrable on `Iθ` by `hmem.1`, and
the dominated function is a.e. strongly measurable there by
`Work.Spaces.aesm_slice_of_continuousOn_Qd` (continuity on the open quadrant from `SmoothOpen`). -/
theorem l12zero_slice_sq_integrableOn (α : ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (l12zero_quad_continuous hsm) hz
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := (π / 2))).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hz]
  have hkey : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f z θ) ^ 2 ≤ (f z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f z θ) ^ 2 = (f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f z θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f z θ) ^ 2‖ = (f z θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)

/-- **The `L₁₂(0)` bound from a pointwise weight bound.**  If the angular slices are integrable
for a.e. `r > 0`, the Hardy-weighted angular energy is a.e. strongly measurable there, and it is
dominated a.e. by an integrable `Φ`, then `|L₁₂(f)(0)| ≤ 3 √(∫_{r>0} Φ)`.

This is `Work.FTS.Nonlinear.Pieces.L12_zero_le_of_weight_bound` (the assembly used by the rows),
whose `L²`-Cauchy–Schwarz core is the unconditional `Work.FTS.Nonlinear.Pieces.L12_zero_le_weak`.
It is `Work.FTS.H2.L12ZeroQ`'s assembly with the slicewise regularity inputs replaced by their
hypotheses. -/
theorem l12zero_of_weight_bound {Φ : ℝ → ℝ}
    (hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => f r θ ^ 2) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦ : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ r) :
    |Work.Construction.L12 f 0| ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Φ r) := by
  have hnn : ∀ r : ℝ, 0 ≤ (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2 :=
    fun r => mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _)
  have hfin : MeasureTheory.IntegrableOn
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine hΦ.mono' hmeas ?_
    filter_upwards [hbd] with r hr
    rw [Real.norm_of_nonneg (hnn r)]
    exact hr
  have hle := Work.FTS.Nonlinear.Pieces.L12_zero_le_weak 0 f hsl hfin
  have hmono : (∫ r in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      ≤ ∫ r in Set.Ioi (0 : ℝ), Φ r :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r _ => hnn r)) hΦ hbd
  calc |Work.Construction.L12 f 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2) := hle
    _ ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Φ r) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)

/-- **The zero mode of `L₁₂` in the open-quadrant class** (the field `N4Norm'.l12zero`):
for `HQo α 4 f` (interior `C^∞` plus honest `ℋ⁴`-membership), `|L₁₂(f)(0)| ≤ 3|f|_{ℋ⁴}`, with the
constant `3` independent of `α` and `f`.  The paper's form is `|L₁₂(f)(0)| ≤ C‖((z+1)/z)f‖_{L²}`
together with `‖((1+z)/z)f‖²_{L²} = ∫∫ f²w ≤ ∫∫ f²w²/sin(2θ)^η = |f|²_{ℋ⁴}`, the second step
being `Work.FTS.H2.L12Q.phiWeight_slice_le` (no smoothness).

The estimate never uses `α ≤ 1` (the constant is universal), so the version below is stated for
every `α > 0`; the field `N4Norm'.l12zero` of `N4Norm'_of_fields` quantifies over
`α ∈ Set.Ioc 0 α₂`, for which this is exactly the right shape. -/
theorem l12zero_field_all :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 4 f →
      |Work.Construction.L12 f 0| ≤ C * Work.FTS.Nonlin.Xn α f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α _hα f hf
  obtain ⟨hopen, hmem⟩ := hf
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hopen.continuousOn
  -- the three slicewise/radial regularity inputs
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f r θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact l12zero_slice_sq_integrableOn α hopen hmem (Set.mem_Ioi.mp hr)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    l12zero_energy_aesm hcont
  -- the Hardy-weighted angular energy is dominated by `r ↦ ∫_θ HkIntegrand α 4 f r θ`
  have hΦ : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact Work.FTS.H2.L12Q.phiWeight_slice_le α f hmem r (Set.mem_Ioi.mp hr)
  have hmain := l12zero_of_weight_bound hsl hmeas hΦ hbd
  -- the radial integral of `∫_θ HkIntegrand` over `(0,∞)` is `HkSq α 4 f`
  have hHkSq : (∫ r in Set.Ioi (0 : ℝ),
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      = Work.Spaces.HkSq α 4 f := by
    rw [Work.Spaces.HkSq, Work.Spaces.Iz]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  calc |Work.Construction.L12 f 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) := hmain
    _ = 3 * Work.FTS.Nonlin.Xn α f := by
        rw [hHkSq, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]

/-- **The zero mode of `L₁₂` in the open-quadrant class** (`Work.FTS.VocabO.HQo α 4 f`, i.e.
interior `C^∞` plus honest `ℋ⁴`-membership): `|L₁₂(f)(0)| ≤ C|f|_{ℋ⁴}` with `C = 3` universal.
This is the requested field `N4Norm'.l12zero` in the form of its consumers, which take
`α ∈ (0,1]`; the slightly stronger `l12zero_field_all` above covers every `α > 0`. -/
theorem l12zero_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 4 f →
      |Work.Construction.L12 f 0| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hC, h⟩ := l12zero_field_all
  exact ⟨C, hC, fun α hα _hα1 f hf => h α hα f hf⟩

end

end Work.FTS.OpenPkg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0_exists =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Psi0_exists : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∃ ψ : ℝ → ℝ,
    ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioo 0 (π / 2)) ∧
    ContinuousOn ψ (Set.Icc 0 (π / 2)) ∧ ψ 0 = 0 ∧ ψ (π / 2) = 0 ∧
    (∀ θ ∈ Set.Ioo 0 (π / 2), Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ) ∧
    (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0 ∧
    Work.Spaces.WlInfMem α 5 (fun _ θ => iteratedDeriv 2 ψ θ) ∧
    Work.Spaces.WlInf α 5 (fun _ θ => iteratedDeriv 2 ψ θ) ≤ C ∧
    (∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.DthIter j (fun _ θ' => ψ θ') 0 θ| ≤ C * Real.sin (2 * θ)) := by
  -- the three auxiliary classes
  have hI : ∃ K : ℝ, IClass K := by
    obtain ⟨K, hKpos, hK1, hK2⟩ := Psi0Aux.cos_sq_Gam_div_sin_bounds
    exact ⟨K, hKpos, hK1, hK2⟩
  have hb : ∃ b : ℕ → ℝ, ElemClass b := by
    obtain ⟨b, hb0, hb1, hb2, hb3, hb4⟩ := Psi0Aux.dthU_iter_elementary_bounds_repaired
    exact ⟨b, hb0, hb2, hb3, hb4⟩
  have hH : ∃ cc dd : ℕ → ℝ, HClass cc dd := by
    obtain ⟨_, hHL⟩ := Psi0Aux.GamBar_dthU_le
    obtain ⟨cc, dd, hcc0, hdd0, hccdd⟩ := hHL
    exact ⟨cc, dd, hcc0, hdd0, hccdd⟩
  obtain ⟨κ, ell, hZ⟩ := Psi0Est.exists_ZClass hI hb hH
  obtain ⟨ν, hA⟩ := Psi0Est.exists_AClass ⟨κ, ell, hZ⟩
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Psi0Est.exists_WBound
    (fun α hα hα1 θ hθ => psiSol_sndDeriv α hα hα1 hθ) ⟨κ, ell, hZ⟩ ⟨ν, hA⟩ hH
  have hνnn : ∀ j, 0 ≤ ν j := hA.1
  refine ⟨max (6 * C₁) (max 1 ((∑ j ∈ Finset.range 7, ν j) + 1)), ?_, fun α hα hα1 => ?_⟩
  · refine lt_of_lt_of_le (by norm_num :
      (0:ℝ) < max 1 ((∑ j ∈ Finset.range 7, ν j) + 1)) (le_max_right _ _)
  · obtain ⟨hWmem, hWle⟩ := Psi0Est.WlInf_psiSol C₁ hC₁pos α hα hα1
      (fun θ hθ => (hC₁ α hα hα1 θ hθ).1)
      (fun j hj1 hj5 θ hθ => (hC₁ α hα hα1 θ hθ).2 j hj1 hj5)
    refine ⟨psiSol α, contDiffOn_psiSol α hα hα1, continuousOn_psiSol α hα hα1,
      psiSol_zero α, psiSol_pi_div_two α,
      (fun θ hθ => psiSol_ode α hα hα1 hθ), psiSol_moment α hα hα1, hWmem, ?_, ?_⟩
    · refine le_trans hWle (le_trans (le_max_left _ _) le_rfl)
    · intro j hj6 θ hθ
      have hAj := hA.2 α hα hα1 j hj6 θ hθ
      have hDth : Work.Spaces.DthIter j (fun _ θ' => psiSol α θ') 0 θ
          = Work.Spaces.dthU^[j] (psiSol α) θ := by
        have h := Work.Spaces.DthIter_decomp j (psiSol α) (fun _ : ℝ => (1:ℝ)) 0 θ
        simpa using h
      rw [hDth]
      have hmem : j ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
      have hνle : ν j ≤ (∑ i ∈ Finset.range 7, ν i) + 1 := by
        have := Finset.single_le_sum (fun i _ => hνnn i) hmem
        linarith
      have hmain : ν j ≤ max (6 * C₁) (max 1 ((∑ i ∈ Finset.range 7, ν i) + 1)) :=
        le_trans (le_trans hνle (le_max_right 1 _)) (le_max_right (6 * C₁) _)
      exact le_trans hAj (mul_le_mul_of_nonneg_right hmain
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open =====
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

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary properties of the weight `w` -/

/-- **The weight `w` is decreasing on `(0,∞)`**: `w(s) = (1 + 1/s)²` and `s ↦ 1/s` is
antitone. -/
theorem w_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Work.Spaces.w b ≤ Work.Spaces.w a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : Work.Spaces.w b = (1 + b⁻¹) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow, add_div, div_self (ne_of_gt hb)]
    ring
  have h2 : Work.Spaces.w a = (1 + a⁻¹) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow, add_div, div_self (ne_of_gt ha)]
    ring
  rw [h1, h2]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have h := inv_anti₀ ha hab
  linarith

/-- The elementary arithmetic inequality behind the constant of the window device:
`64 z³ ≤ (1 + 2z)⁴` for `z ≥ 0` (equivalently `2·(2/z)·w(2z)^{-2} ≤ 1`). -/
theorem sixtyfour_mul_cube_le {z : ℝ} (hz : 0 ≤ z) : 64 * z ^ 3 ≤ (1 + 2 * z) ^ 4 := by
  have hfac : (1 + 2 * z) ^ 4 - 64 * z ^ 3
      = 1 + 8 * z * (2 * z * (z - 1) ^ 2 + (z + 1)) := by ring
  have hpos : (0 : ℝ) ≤ 2 * z * (z - 1) ^ 2 + (z + 1) := by nlinarith [sq_nonneg (z - 1), hz]
  nlinarith [hfac, hpos, hz]

/-- **The coefficient of the window device is at most `1/2`**:
`2·(2/z)·w(2z)^{-2} ≤ 1` for `z > 0`. -/
theorem two_mul_coef_le_one {z : ℝ} (hz : 0 < z) :
    2 * ((2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) ≤ 1 := by
  have hw : (Work.Spaces.w (2 * z)) ^ 2 = (1 + 2 * z) ^ 4 / (16 * z ^ 4) := by
    rw [Work.Spaces.w, div_pow]; field_simp; ring
  rw [hw, inv_div]
  have h64 : 64 * z ^ 3 ≤ (1 + 2 * z) ^ 4 := sixtyfour_mul_cube_le hz.le
  have hden : 0 < (1 + 2 * z) ^ 4 := by positivity
  rw [show (2 : ℝ) * (2 / z * (16 * z ^ 4 / (1 + 2 * z) ^ 4))
      = 64 * z ^ 3 / (1 + 2 * z) ^ 4 by field_simp; ring]
  rw [div_le_one hden]
  exact h64

/-! ## Pointwise domination of a pure `D_z`-slot by the `ℋ⁴`-integrand -/

/-- On the open quadrant, a pure `D_z`-slot of order `k ≤ 4` is dominated by `HkIntegrand`:
the `k`-th summand of the pure sum is `(D_z^k g · w / sin(2θ)^{η/2})²` and
`sin(2θ)^{η/2} ≤ 1`. -/
theorem dzSlot_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {k : ℕ} (hk : k ≤ 4)
    {z θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.DzIter k f z θ * Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
  have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ k hk
  have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have heq : (Work.Spaces.DzIter k f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter k f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  calc (Work.Spaces.DzIter k f z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.DzIter k f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ (Work.Spaces.DzIter k f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hone
    _ = (Work.Spaces.DzIter k f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hkey

/-! ## The relative-window Agmon bound -/

/-- **The window bound for the radial iterates.**  For `z > 0`, `θ ∈ (0,π/2)` and every `i`,

  `(D_z^i g z θ)² ≤ (2/z)·w(2z)^{-2}·(∫_z^{2z}(D_z^i g s θ)²w(s)²ds
      + ∫_z^{2z}(D_z^{i+1} g s θ)²w(s)²ds)`.

Route: `tvAverageLe` on `[z,2z]` for `U(s) = (D_z^i g s θ)²` gives
`U z ≤ (1/z)∫_{z}^{2z}U + ∫_{z}^{2z}|U'|`; `∂_z(D_z^i g)(s,θ) = D_z^{i+1}g s θ / s`, AM–GM
`2|XY|/s ≤ (X²+Y²)/z` (as `s ≥ z > 0`), and the monotonicity of `w` on the window. -/
private theorem windowBoundDzIter_local {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (i : ℕ) :
    (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ *
        ((∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
          + (∫ s in z..(2 * z), (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
              * (Work.Spaces.w s) ^ 2)) := by
  have hz2 : z < 2 * z := by linarith
  have hz2' : z ≤ 2 * z := hz2.le
  have hsub : Set.Icc z (2 * z) ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le hz hs.1
  have hcontD : ContinuousOn (fun s => Work.Spaces.DzIter i g s θ) (Set.Icc z (2 * z)) :=
    ((hO.DzIter i).curry_z hθ).continuousOn.mono hsub
  have hcontD1 : ContinuousOn (fun s => Work.Spaces.DzIter (i + 1) g s θ) (Set.Icc z (2 * z)) :=
    ((hO.DzIter (i + 1)).curry_z hθ).continuousOn.mono hsub
  have hcontW : ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Icc z (2 * z)) := by
    have h1 : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Icc z (2 * z)) := by
      simp only [Work.Spaces.w]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun s hs => ?_)
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hs.1))
    exact h1.pow 2
  have hUderiv : ∀ x ∈ Set.Icc z (2 * z),
      HasDerivAt (fun s => (Work.Spaces.DzIter i g s θ) ^ 2)
        (2 * Work.Spaces.DzIter i g x θ * Work.Spaces.pz (Work.Spaces.DzIter i g) x θ) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
    have hd : HasDerivAt (fun s => Work.Spaces.DzIter i g s θ)
        (Work.Spaces.pz (Work.Spaces.DzIter i g) x θ) x :=
      Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice_DzIter hO i hθ hxpos
    have h2 := hd.pow 2
    have hval : (↑(2 : ℕ) : ℝ) * Work.Spaces.DzIter i g x θ ^ (2 - 1)
        * Work.Spaces.pz (Work.Spaces.DzIter i g) x θ
        = 2 * Work.Spaces.DzIter i g x θ * Work.Spaces.pz (Work.Spaces.DzIter i g) x θ := by
      norm_num
    rw [hval] at h2
    exact h2
  have hcontU : ContinuousOn (fun s => (Work.Spaces.DzIter i g s θ) ^ 2) (Set.Icc z (2 * z)) :=
    hcontD.pow 2
  have hcontU' : ContinuousOn
      (fun s => 2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ)
      (Set.Icc z (2 * z)) := by
    have hP : ContinuousOn (fun s => Work.Spaces.pz (Work.Spaces.DzIter i g) s θ)
        (Set.Icc z (2 * z)) :=
      (((hO.DzIter i).pz).curry_z hθ).continuousOn.mono hsub
    exact (continuousOn_const.mul hcontD).mul hP
  have hIntU : IntervalIntegrable (fun s => (Work.Spaces.DzIter i g s θ) ^ 2) volume z (2 * z) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hz2']; exact hcontU)
  have hIntU' : IntervalIntegrable
      (fun s => 2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ)
      volume z (2 * z) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hz2']; exact hcontU')
  have htv := Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.tvAverageLe hz2 le_rfl hz2'
    hUderiv hIntU' hIntU
  rw [show (2 : ℝ) * z - z = z by ring] at htv
  have hW : 0 < Work.Spaces.w (2 * z) := Work.FTS.TransportS.w_pos_of_pos (by linarith)
  have hW2 : 0 < (Work.Spaces.w (2 * z)) ^ 2 := by positivity
  set A : ℝ := ∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
    with hAdef
  set B : ℝ := ∫ s in z..(2 * z), (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
    with hBdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact intervalIntegral.integral_nonneg hz2' fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact intervalIntegral.integral_nonneg hz2' fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- the mean-value term
  have hA : (∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2)
      ≤ ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * A := by
    rw [hAdef, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hz2' hIntU ?_ ?_
    · exact ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le hz2']; exact continuousOn_const.mul (hcontU.mul hcontW))
    · intro s hs
      have hspos : 0 < s := lt_of_lt_of_le hz hs.1
      have hle : Work.Spaces.w (2 * z) ≤ Work.Spaces.w s := w_antitone hspos (by linarith [hs.2])
      have hsq : (Work.Spaces.w (2 * z)) ^ 2 ≤ (Work.Spaces.w s) ^ 2 :=
        pow_le_pow_left₀ hW.le hle 2
      rw [inv_mul_eq_div, le_div_iff₀ hW2]
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  -- the total-variation term
  have hfint : IntervalIntegrable
      (fun s => (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2) volume z (2 * z) :=
    ContinuousOn.intervalIntegrable (by
      rw [Set.uIcc_of_le hz2']; exact hcontU.mul hcontW)
  have hgint : IntervalIntegrable
      (fun s => (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
      volume z (2 * z) :=
    ContinuousOn.intervalIntegrable (by
      rw [Set.uIcc_of_le hz2']; exact hcontD1.pow 2 |>.mul hcontW)
  have hB' : (∫ s in z..(2 * z),
        |2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ|)
      ≤ ∫ s in z..(2 * z), ((1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹)
          * ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            + (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
    refine intervalIntegral.integral_mono_on hz2' hIntU'.abs ?_ ?_
    · exact ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le hz2']
        exact continuousOn_const.mul ((hcontU.mul hcontW).add (hcontD1.pow 2 |>.mul hcontW)))
    · intro s hs
      have hspos : 0 < s := lt_of_lt_of_le hz hs.1
      have hle : Work.Spaces.w (2 * z) ≤ Work.Spaces.w s := w_antitone hspos (by linarith [hs.2])
      have hsq : (Work.Spaces.w (2 * z)) ^ 2 ≤ (Work.Spaces.w s) ^ 2 :=
        pow_le_pow_left₀ hW.le hle 2
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter i g) s θ
          = Work.Spaces.DzIter (i + 1) g s θ / s := by
        have h1 : Work.Spaces.DzIter (i + 1) g s θ
            = s * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ := rfl
        rw [h1, mul_comm s, mul_div_cancel_right₀ _ (ne_of_gt hspos)]
      have hkey : |2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ|
          ≤ (|Work.Spaces.DzIter i g s θ| ^ 2
            + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2) / z := by
        rw [le_div_iff₀ hz, hpz]
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hspos,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have h2 : 2 * (|Work.Spaces.DzIter i g s θ| * |Work.Spaces.DzIter (i + 1) g s θ|)
            ≤ |Work.Spaces.DzIter i g s θ| ^ 2 + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2 := by
          nlinarith [sq_nonneg (|Work.Spaces.DzIter i g s θ|
            - |Work.Spaces.DzIter (i + 1) g s θ|)]
        have hzs : z / s ≤ 1 := (div_le_one hspos).mpr hs.1
        calc 2 * |Work.Spaces.DzIter i g s θ|
              * (|Work.Spaces.DzIter (i + 1) g s θ| / s) * z
            = 2 * (|Work.Spaces.DzIter i g s θ| * |Work.Spaces.DzIter (i + 1) g s θ|)
              * (z / s) := by ring
          _ ≤ (|Work.Spaces.DzIter i g s θ| ^ 2
                + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2) * 1 :=
              mul_le_mul h2 hzs (by positivity) (by positivity)
          _ = |Work.Spaces.DzIter i g s θ| ^ 2
                + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2 := by ring
      have hinv : 1 ≤ (Work.Spaces.w s) ^ 2 * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hW2, one_mul]
        exact hsq
      have hX : (Work.Spaces.DzIter i g s θ) ^ 2
          ≤ (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
        calc (Work.Spaces.DzIter i g s θ) ^ 2 = (Work.Spaces.DzIter i g s θ) ^ 2 * 1 := by ring
          _ ≤ (Work.Spaces.DzIter i g s θ) ^ 2
              * ((Work.Spaces.w s) ^ 2 * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
          _ = (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
              * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by ring
      have hY : (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
          ≤ (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
        calc (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
            = (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * 1 := by ring
          _ ≤ (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
              * ((Work.Spaces.w s) ^ 2 * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
          _ = (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
              * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by ring
      have hfin : |Work.Spaces.DzIter i g s θ| ^ 2 + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2
          ≤ ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
              + (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
            * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
        rw [sq_abs, sq_abs, add_mul]
        linarith [hX, hY]
      calc |2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ|
          ≤ (|Work.Spaces.DzIter i g s θ| ^ 2
              + |Work.Spaces.DzIter (i + 1) g s θ| ^ 2) / z := hkey
        _ ≤ (((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                + (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
              * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) / z :=
            div_le_div_of_nonneg_right hfin hz.le
        _ = (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹
              * ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                + (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
            ring
  have hB : (∫ s in z..(2 * z),
        |2 * Work.Spaces.DzIter i g s θ * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ|)
      ≤ (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (A + B) := by
    refine hB'.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hfint hgint,
      ← hAdef, ← hBdef]
  have hcnn : (0 : ℝ) ≤ (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by positivity
  have hmain : (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (A + B) := by
    calc (Work.Spaces.DzIter i g z θ) ^ 2
        ≤ (1 / z) * (∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2)
            + ∫ s in z..(2 * z),
                |2 * Work.Spaces.DzIter i g s θ
                  * Work.Spaces.pz (Work.Spaces.DzIter i g) s θ| := htv
      _ ≤ (1 / z) * (((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * A)
            + (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (A + B) :=
          add_le_add (mul_le_mul_of_nonneg_left hA (by positivity)) hB
      _ = (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (2 * A + B) := by ring
      _ ≤ (1 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (2 * A + 2 * B) :=
          mul_le_mul_of_nonneg_left (by linarith) hcnn
      _ = (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ * (A + B) := by ring
  rw [hAdef, hBdef] at hmain
  exact hmain

/-! ## The a.e. pointwise slice bound -/

/-- **The a.e. slice bound.**  For a.e. angle (namely whenever the angular slice of
`HkIntegrand α 4 g` is integrable in `z`) the square of the pure slot `D_z^i g z θ` is
dominated by the *slice* `∫_s HkIntegrand α 4 g s θ ds`, for `i ≤ 3`. -/
private theorem ae_dzIter_sq_le_sliceIntegral {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hInt : MeasureTheory.IntegrableOn
      (fun s => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iz)
    (i : ℕ) (hi : i ≤ 3) :
    (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := by
  have hz2' : z ≤ 2 * z := by linarith
  have hwin := windowBoundDzIter_local hO hz hθ i
  have hCnn : 0 ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ := by
    have := Work.FTS.TransportS.w_pos_of_pos (by linarith : (0 : ℝ) < 2 * z)
    positivity
  have hChalf : 2 * ((2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹) ≤ 1 := two_mul_coef_le_one hz
  have hJnn : 0 ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ :=
    integral_nonneg fun s => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hinterval : ∀ k ≤ 4,
      (∫ s in z..(2 * z), (Work.Spaces.DzIter k g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := by
    intro k hk
    rw [intervalIntegral.integral_of_le hz2']
    calc (∫ s in Set.Ioc z (2 * z), (Work.Spaces.DzIter k g s θ) ^ 2
            * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Set.Ioc z (2 * z), Work.Spaces.HkIntegrand α 4 g s θ := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_ ?_
          · exact hInt.mono_set (fun s hs => le_of_lt (lt_trans hz hs.1))
          · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
            have h := dzSlot_sq_le_HkIntegrand (α := α) (f := g) hk hθ.1 hθ.2 (z := s)
            rwa [mul_pow] at h
      _ ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ :=
          setIntegral_mono_set hInt
            (Eventually.of_forall fun s => Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
            (Eventually.of_forall fun s hs => le_of_lt (lt_trans hz hs.1))
  have h1 := hinterval i (by omega)
  have h2 := hinterval (i + 1) (by omega)
  calc (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹ *
          ((∫ s in z..(2 * z), (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
            + (∫ s in z..(2 * z), (Work.Spaces.DzIter (i + 1) g s θ) ^ 2
                * (Work.Spaces.w s) ^ 2)) := hwin
    _ ≤ (2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹
          * (2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        linarith
    _ = (2 * ((2 / z) * ((Work.Spaces.w (2 * z)) ^ 2)⁻¹))
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ) := by ring
    _ ≤ 1 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ) :=
        mul_le_mul_of_nonneg_right hChalf hJnn
    _ = ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := one_mul _

/-! ## The target -/

theorem Qang_sq_le_const_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 3) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g i z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  have hCS := Work.FTS.OpenPkg.QangOpen.Qang_sq_leQ_open α g hO hmem i (by omega) hz
  obtain ⟨hswap, hIntHkθ, hAeIntHk⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 (hO.forall 4) hmem
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ⟨h0, h1⟩)
  have hkey : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.DzIter i g z θ) ^ 2
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := by
    filter_upwards [hAeIntHk, haeθ] with θ hInt hθ
    exact ae_dzIter_sq_le_sliceIntegral hO hz hθ hInt i hi
  have hθint : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 4 g := by
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ :=
          integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hIntHkθ hkey
      _ = Work.Spaces.HkSq α 4 g := hswap
  calc (Work.Elliptic.Qang g i z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2) := hCS
    _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g :=
        mul_le_mul_of_nonneg_left hθint (integral_nonneg fun θ => sq_nonneg _)

end Work.FTS.StrongEps.E4R3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.L12f_slot_le_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E1Open

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The level-`n` weighted slot bound for `L₁₂ f`**, given the level-`n` angular-moment bound
`hQ` as a hypothesis (so that this lemma is independent of the angular port). -/
theorem L12f_slot_le_O_of {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem β m g → ∀ i : ℕ, i ≤ m →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ CQ * Work.Spaces.HkSq β m g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α n f := by
  refine ⟨4 * (107 * CQ) + 1, by positivity, ?_⟩
  intro α hαIoc f hsm hmem4 h0 n hn
  have hαpos : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm n (by omega) hmem4
  -- the two definitions of `L₁₂` agree
  have h0e : Work.Elliptic.L12 f 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h0
  obtain ⟨hgen, hInt0, hBnd0⟩ :=
    Work.FTS.OpenPkg.l12_open_bundle α f hαpos hα1 hsm hmem4 h0e
  set u : ℝ → ℝ := fun z => Work.Elliptic.L12 f z with hudef
  -- ## the a.e. transfer `D_z^i u = -Qang f (i-1)` on `Iz`, `1 ≤ i ≤ 3`
  have htrans : ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      (fun z : ℝ => (Work.Elliptic.Qang f (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z : ℝ => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro i hi hi3
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang f (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hsub : i - 1 ≤ 3 := by omega
    have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang f (i - 1) z := by
      have h := hgen (i - 1) hsub z hzpos
      rwa [show i - 1 + 1 = i by omega] at h
    rw [key, neg_sq]
  -- ## integrability of every slot
  have hInt : ∀ i : ℕ, i ≤ n → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hInt0
    · exact ((hQ α n f hαpos hα1 hsm hmemn (i - 1) (by omega)).1).congr
        (htrans i h (by omega))
  -- ## the bounds of the individual slots
  have hb0 : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (CQ * Work.Spaces.HkSq α n f) := by
    have hb : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang f 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hBnd0
    exact le_trans hb (mul_le_mul_of_nonneg_left
      (hQ α n f hαpos hα1 hsm hmemn 0 (Nat.zero_le n)).2 (by norm_num))
  have hbI : ∀ i : ℕ, 1 ≤ i → i ≤ n → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ CQ * Work.Spaces.HkSq α n f := by
    intro i hi hin
    rw [← MeasureTheory.integral_congr_ae (htrans i hi (by omega))]
    exact (hQ α n f hαpos hα1 hsm hmemn (i - 1) (by omega)).2
  -- ## the sum of the slots
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 4 * (107 * (CQ * Work.Spaces.HkSq α n f)) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range (n + 1))
      (fun i hi => hInt i (by have := Finset.mem_range.mp hi; omega))]
    have hnd : 0 ≤ CQ * Work.Spaces.HkSq α n f :=
      mul_nonneg hCQ (Work.Spaces.HkSq_nonneg α n f)
    have hterm : ∀ i ∈ Finset.range (n + 1), (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (CQ * Work.Spaces.HkSq α n f) := by
      intro i hi
      have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact hb0
      · exact le_trans (hbI i h hin) (by linarith)
    have h1 : (∑ i ∈ Finset.range (n + 1), (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _i ∈ Finset.range (n + 1), 107 * (CQ * Work.Spaces.HkSq α n f) :=
      Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    have hcard : (((n + 1 : ℕ)) : ℝ) ≤ 4 := by
      have : ((n : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hn
      push_cast
      linarith
    refine le_trans h1 ?_
    have hnn : 0 ≤ 107 * (CQ * Work.Spaces.HkSq α n f) := by linarith
    exact mul_le_mul_of_nonneg_right hcard hnn
  -- ## integrability of the whole `z`-sum
  have hsumInt : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum (Finset.range (n + 1))
      (fun i hi => hInt i (by have := Finset.mem_range.mp hi; omega))
  -- ## back to `Work.Coercivity.L12f`
  have hfun : Work.Coercivity.L12f f = u := by
    funext z
    have h1 : Work.Coercivity.L12f f = Work.Construction.L12 f := rfl
    rw [hudef, h1]
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z
  have hcongr : (fun z : ℝ => ∑ c ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (fun z : ℝ => ∑ c ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter c u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    funext z
    rw [hfun]
  constructor
  · rw [hcongr]
    exact hsumInt
  · rw [hcongr]
    refine le_trans hsum_le ?_
    have hk : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
    calc 4 * (107 * (CQ * Work.Spaces.HkSq α n f))
        = (4 * (107 * CQ)) * Work.Spaces.HkSq α n f := by ring
      _ ≤ (4 * (107 * CQ) + 1) * Work.Spaces.HkSq α n f :=
          mul_le_mul_of_nonneg_right (by linarith) hk

end Work.FTS.StrongEps.EpsE4Thr.E1Open
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass =====
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

/-! ## The open classes -/

/-- **The open-quadrant version of `RegQ`**: `C^∞` on the open quadrant `(0,∞) × (0,π/2)` (instead
of the strip `(-1,∞) × (0,π/2)`), honesty of the `ℋ^k`-integrand, and the vanishing of the
integration-by-parts boundary terms up to order `k`.

`RegQo` is exactly what the interior integration by parts of the coercivity needs, and — unlike
`RegQ` — it *is* a consequence of the class-`C` clause carried by the route's data. -/
def RegQo (α : ℝ) (k : ℕ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α k f ∧
    Work.FTS.Nonlin.BdryTraces α k f

/-- **The open-quadrant version of `CoerAdm`**: the four clauses (regularity, angular vanishing,
the two axis values and the vanishing `L₁₂`-zero-mode), with `RegQo` in place of `RegQ`. -/
def CoerAdmO (α : ℝ) (f : Fn) : Prop :=
  RegQo α 5 f ∧ Work.Spaces.VanishTheta f ∧
    (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) ∧
    Work.Construction.L12 f 0 = 0

/-! ## Elementary API -/

/-- `RegQo` is monotone in the order. -/
theorem regQo_mono {α : ℝ} {f : Fn} {k l : ℕ} (hkl : k ≤ l) (h : RegQo α l f) :
    RegQo α k f :=
  ⟨h.1, Work.FTS.OpenPkg.HkMem_mono_open h.1 k hkl h.2.1,
    fun a b hab => h.2.2 a b (le_trans hab hkl)⟩



/-- `RegQo α 5 f` gives the `RegQo α 4` instance (used by the algebraic clauses). -/
theorem CoerAdmO.regQoFour {α : ℝ} {f : Fn} (h : CoerAdmO α f) : RegQo α 4 f :=
  regQo_mono (by norm_num) h.1


/-! ## The open-class analogue of `UnifIP` -/

/-- **The open-class analogue of `Work.FTS.Nonlin.UnifIP`**: the same clause list, with the frozen
classes `RegQ α 4` / `CoerAdm α` replaced by `RegQo α 4` / `CoerAdmO α`.

This is the interface the level-four barrier can actually be run against: `UnifIPO` implies the
frozen `UnifIP` (`UnifIPO.toUnifIP`), and — unlike `UnifIP` — it is *satisfiable at the projected
slices of the route* (`OpenBarrier.coerAdmO_slice_JfamP`). -/
structure UnifIPO (IP : ℝ → Fn → Fn → ℝ) (α₂ cc clo Cup Ccs : ℝ) : Prop where
  pos : 0 < α₂ ∧ 0 < cc ∧ 0 < clo ∧ 0 < Cup ∧ 0 < Ccs
  symm : ∀ α f g, IP α f g = IP α g f
  add_fst : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g, RegQo α 4 f₁ → RegQo α 4 f₂ → RegQo α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  smul_fst : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) f g, RegQo α 4 f → RegQo α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  congr_qd : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g, RegQo α 4 f → RegQo α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  nonneg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, RegQo α 4 f → 0 ≤ IP α f f
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g, RegQo α 4 f → RegQo α 4 g →
    |IP α f g| ≤ Ccs * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g
  lo : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdmO α f → clo * Work.Spaces.HkSq α 4 f ≤ IP α f f
  up : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdmO α f → IP α f f ≤ Cup * Work.Spaces.HkSq α 4 f
  coer : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdmO α f →
    cc * Work.Spaces.HkSq α 4 f ≤ IP α (Work.Coercivity.LGammaT α f) f
  Dz_self : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdmO α f →
    |IP α (Work.Spaces.Dz f) f| ≤ Ccs * Work.FTS.Nonlin.Xn α f ^ 2


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L12F_mul_HkSq_le =====
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

open Work.FTS.CoercivityFix.E2Bound (gpoly Tmul)

/-! ## The chart polynomial for `z ↦ 1/(1+z)` -/

/-- The chart polynomial whose `gpoly`-evaluation is `z ↦ 1/(1+z)`, namely `½(1 - X)`:
`½(1 - (z-1)/(z+1)) = 1/(z+1)`. -/
private def Pone : Polynomial ℝ := Polynomial.C (1 / 2) * (1 - Polynomial.X)

/-- `gpoly Pone z = 1/(1+z)` away from the pole `z = -1`. -/
private lemma gpoly_Pone {z : ℝ} (hz : z ≠ -1) : gpoly Pone z = 1 / (1 + z) := by
  have hz1 : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  rw [Work.FTS.CoercivityFix.E2Bound.gpoly_apply, Pone,
    Work.FTS.CoercivityFix.E2Bound.zchart_apply]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [show (z - 1) / (z + 1) = (1 + z - 2) / (1 + z) by ring]
  rw [show (1 : ℝ) = (1 + z) / (1 + z) by field_simp]
  field_simp
  ring

/-- `Szop b` bounds `|Zop^b (z ↦ 1/(1+z))|` on `(0,∞)`: it is the sum of the absolute values
of the coefficients of the `b`-th `Tmul`-iterate of the chart polynomial `Pone`. -/
private def Szop (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range ((Tmul^[b] Pone).natDegree + 1), |(Tmul^[b] Pone).coeff k|

private lemma Szop_nonneg (b : ℕ) : 0 ≤ Szop b :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The **`α`-independent** bound for the `Zop`-iterates of `L₁₂(F_*(α))` of order `≤ 3`. -/
private def Kzop : ℝ := 2 * ∑ b ∈ Finset.range 4, Szop b

private lemma Kzop_nonneg : 0 ≤ Kzop := by
  show (0 : ℝ) ≤ 2 * ∑ b ∈ Finset.range 4, Szop b
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun b _ => Szop_nonneg b))

/-! ## The `Zop`-bound on the profile -/

private lemma zop_L12F_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (b : ℕ) (hb : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    |(Work.Spaces.Zop^[b]
        (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)) z| ≤ Kzop := by
  have hz' : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  -- the profile identity, in the shape `2α · (1/(1+z))`
  have hEq : Set.EqOn (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)
      (fun w : ℝ => (2 * α) * (1 / (1 + w))) (Set.Ioi (-1 : ℝ)) := by
    intro w hw
    show Work.Construction.L12 (Work.Construction.Fstar α) w = (2 * α) * (1 / (1 + w))
    rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hw]
    ring
  have h1 : (Work.Spaces.Zop^[b]
        (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)) z
      = (Work.Spaces.Zop^[b] (fun w : ℝ => (2 * α) * (1 / (1 + w)))) z :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi hEq hz'
  have h2 : (Work.Spaces.Zop^[b] (fun w : ℝ => (2 * α) * (1 / (1 + w)))) z
      = (2 * α) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z :=
    congrFun (Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul b (2 * α)
      (fun w : ℝ => 1 / (1 + w))) z
  -- the explicit function is a chart polynomial
  have h3 : (Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z
      = gpoly (Tmul^[b] Pone) z := by
    have hb2 : Set.EqOn (fun w : ℝ => 1 / (1 + w)) (gpoly Pone) (Set.Ioi (0 : ℝ)) :=
      fun w hw => (gpoly_Pone (by have hw' : (0 : ℝ) < w := hw; linarith)).symm
    rw [Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi hb2 hz,
      Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate Pone b z hz]
  -- the chart variable lies in `(-1,1)`
  have h4 : |gpoly (Tmul^[b] Pone) z| ≤ Szop b := by
    rw [Work.FTS.CoercivityFix.E2Bound.gpoly_apply]
    exact Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff _
      (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hz)
  have hb4 : b ∈ Finset.range 4 := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hb)
  have hle : Szop b ≤ ∑ b' ∈ Finset.range 4, Szop b' :=
    Finset.single_le_sum (fun i _ => Szop_nonneg i) hb4
  have hα2 : (0 : ℝ) < 2 * α := by linarith
  calc |(Work.Spaces.Zop^[b]
          (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)) z|
      = |(2 * α) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z| := by rw [h1, h2]
    _ = |2 * α| * |(Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z| := abs_mul _ _
    _ = (2 * α) * |(Work.Spaces.Zop^[b] (fun w : ℝ => 1 / (1 + w))) z| := by
        rw [abs_of_nonneg hα2.le]
    _ = (2 * α) * |gpoly (Tmul^[b] Pone) z| := by rw [h3]
    _ ≤ (2 * α) * Szop b := mul_le_mul_of_nonneg_left h4 hα2.le
    _ ≤ 2 * Szop b := by
        refine mul_le_mul_of_nonneg_right ?_ (Szop_nonneg b)
        have h2α : 2 * α ≤ 2 * 1 := by linarith
        simpa using h2α
    _ ≤ 2 * ∑ b' ∈ Finset.range 4, Szop b' := mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = Kzop := rfl

/-! ## The profile is `C^∞` on `(-1,∞)` -/

private lemma contDiffOn_L12F (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi (-1)) := by
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi (-1)) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 : ℝ) + z)
        (Set.Ioi (-1)) := contDiffOn_const.add contDiffOn_id
    have h2 := (contDiffOn_const (c := 2 * α) :
        ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ => 2 * α) (Set.Ioi (-1))).div h1
      (fun z hz => ne_of_gt (by have hz' : (-1 : ℝ) < z := hz; linarith))
    exact h2
  refine ContDiffOn.congr hbase ?_
  intro z hz
  exact Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz

/-! ## The theorem -/

theorem L12F_mul_HkSq_le : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkMem α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * g z θ) ∧
      Work.Spaces.HkSq α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * g z θ)
        ≤ C * Work.Spaces.HkSq α 3 g := by
  obtain ⟨C₀, hC₀, hmain⟩ := Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le 3
  refine ⟨C₀ * (1 + Kzop) ^ 2, mul_pos hC₀ (pow_pos (by linarith [Kzop_nonneg]) 2), ?_⟩
  intro α hα g hg hm
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi (-1)) := contDiffOn_L12F α hα0 hα1
  have hbnd : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |(Work.Spaces.Zop^[b]
        (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w)) z| ≤ Kzop :=
    fun b hb z hz => zop_L12F_le α hα0 hα1 b hb hz
  exact (hmain α (fun w : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) w) Kzop
    Kzop_nonneg hbnd hsm g hg).2 hm

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.BcoefMem6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The radial block of the order-`6` separation bound -/

/-- The sum of the squares of the weighted `D_z`-iterates of the radial profile, up to order `6`:
the radial factor produced by the separation bound `HkIntegrandSepLeGen` at `k = 6`. -/
def radSnorm6 (z : ℝ) : ℝ :=
  ∑ q ∈ Finset.range 7,
    ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z) ^ 2

lemma radSnorm6_ge_zero (z : ℝ) : 0 ≤ radSnorm6 z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The radial block in the exact shape produced by `HkIntegrandSepLeGen`: there the weight is
squared inside each summand, whereas `radSnorm6` uses `(X·w)²`. -/
lemma radSnorm6_eq_hkSep (z : ℝ) :
    radSnorm6 z = ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z' _ => Work.FTS.StrongPersist.L3Aux.bcoefRad z') z 0) ^ 2
        * (Work.Spaces.w z) ^ 2 := by
  rw [radSnorm6]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_pow]
  congr 1
  rw [show Work.Spaces.DzIter q (fun z' _ => Work.FTS.StrongPersist.L3Aux.bcoefRad z') z 0
      = (fun z => Work.Spaces.DzIter q (fun z' _ => Work.FTS.StrongPersist.L3Aux.bcoefRad z') z 0) z
      from rfl]
  rw [Work.Spaces.sliceZ_DzIter q (fun z' _ => Work.FTS.StrongPersist.L3Aux.bcoefRad z') 0]
  rw [show Work.Spaces.OpZ = Work.Spaces.Zop from rfl]

/-! ## The target -/

theorem BcoefMem6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
    Work.Spaces.HkMem α 6
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
    Work.Spaces.HkSq α 6
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ≤ C := by
  obtain ⟨K, hKpos, hrb⟩ := bcoefRad_zop_bound6
  obtain ⟨K3, hK3pos, hangblk⟩ := gamCoef_angBlk6
  obtain ⟨M, hMpos, hang⟩ := Work.FTS.StrongPersist.L3Aux.radAngInt_bound
  have hK : 0 ≤ K := le_of_lt hKpos
  have hCnn : 0 ≤ 14 * K ^ 2 * (K3 * M) := by positivity
  refine ⟨14 * K ^ 2 * (K3 * M) + 1, by linarith, fun α hα hα1 => ?_⟩
  obtain ⟨hangint, hangbd⟩ := hang α hα hα1
  have hA0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => Work.FTS.StrongPersist.L3Aux.radAngInt_nonneg
        (Work.FTS.StrongPersist.L3Aux.sin_two_nonneg_of_mem_Iθ hθ)))
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) := by
    simpa only [Work.FTS.StrongPersist.L3Aux.bcoefRad,
      Work.FTS.StrongPersist.L3Aux.gamCoefAng] using
      Work.FTS.StrongPersist.L3Aux.smoothOpen_prod α
  have hmajint : ∀ z : ℝ, MeasureTheory.Integrable
      (fun θ : ℝ => radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
      (volume.restrict Work.Spaces.Iθ) := by
    intro z
    exact (hangint.const_mul K3).const_mul (radSnorm6 z)
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) z θ
        ≤ radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ) := by
    intro z hz θ hθ
    have h1 := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
      (C := Work.FTS.StrongPersist.L3Aux.gamCoefAng α)
      (B := Work.FTS.StrongPersist.L3Aux.bcoefRad) (z := z) (θ := θ) hθ
    have h2 := hangblk α hα hα1 θ hθ
    refine h1.trans ?_
    rw [← radSnorm6_eq_hkSep z]
    refine (mul_le_mul_of_nonneg_right h2 (radSnorm6_ge_zero z)).trans ?_
    exact le_of_eq (by ring)
  refine ⟨hsm, ?_, ?_⟩
  · refine Work.FTS.LocData.HkMem_of_majorant α 6
      (M := fun z θ => radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
      ?_ ?_ ?_ hpt
    · simpa only [Work.FTS.EllipticEst.Q0] using hsm.continuousOn_HkIntegrand α 6
    · intro z hz
      exact hmajint z
    · have hS : MeasureTheory.IntegrableOn radSnorm6 Work.Spaces.Iz :=
        (radSnorm6_int_le hK hrb).1
      have he : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
          = fun z : ℝ => radSnorm6 z
              * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ)) := by
        funext z
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [he]
      exact hS.mul_const _
  · rw [Work.Spaces.HkSq]
    have hSint : MeasureTheory.IntegrableOn radSnorm6 Work.Spaces.Iz :=
      (radSnorm6_int_le hK hrb).1
    have hSbd : (∫ z in Work.Spaces.Iz, radSnorm6 z) ≤ 14 * K ^ 2 :=
      (radSnorm6_int_le hK hrb).2
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) z θ)
          ≤ radSnorm6 z
              * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ)) := by
      intro z hz
      have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          Work.Spaces.HkIntegrand α 6
            (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) z θ
            ≤ radSnorm6 z * (K3 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ) :=
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
        (hmajint z) hae
      refine hmono.trans (le_of_eq ?_)
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have houter := MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      (hSint.mul_const _)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
    rw [MeasureTheory.integral_mul_const] at houter
    refine houter.trans ?_
    have h1 : (∫ z in Work.Spaces.Iz, radSnorm6 z)
          * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
        ≤ 14 * K ^ 2
            * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ)) :=
      mul_le_mul_of_nonneg_right hSbd (mul_nonneg (le_of_lt hK3pos) hA0)
    refine h1.trans ?_
    have h2 : 14 * K ^ 2
          * (K3 * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ))
        ≤ 14 * K ^ 2 * (K3 * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hangbd (le_of_lt hK3pos))
        (by positivity)
    linarith [h2]

end Work.FTS.StrongPersist.L6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateMargIntHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.TransportS
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

/-- **Integrability of the delicate radial marginal in the honest class.** -/
theorem delicateMargInt_hon :
    ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → 0 ≤ q → q ≤ Work.Spaces.gam α →
      HonF α f → Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
              * |Work.Spaces.mixed 3 1 g z θ|)
        Work.Spaces.Iz := by
  intro α q f g hα hα1 hq0 hqγ hsf hSmoG hHk4g
  have hSmoF : Work.FTS.EllipticEst.SmoothOpen f := hsf.1
  have hHk4f : Work.Spaces.HkMem α 4 f := hsf.2.1
  have hgam_pos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hgam_nn : 0 ≤ Work.Spaces.gam α := le_of_lt hgam_pos
  change MeasureTheory.Integrable
    (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
    (MeasureTheory.volume.restrict Work.Spaces.Iz)
  -- notation
  set S : ℝ → ℝ :=
    fun z => sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2), y = |Work.Spaces.DzIter 3 f z θ|}
    with hS
  set mg : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hmg
  set cg : ℝ := Work.Spaces.HkSq α 4 g with hcg
  have hcgnn : 0 ≤ cg := by rw [hcg]; exact Work.Spaces.HkSq_nonneg α 4 g
  -- (1) the sup-bound of `supThetaIntOpen`
  obtain ⟨C0, _hC0pos, hC0⟩ := Work.FTS.TransportS.SlotT2.supThetaIntOpen
  obtain ⟨hSint_raw, hSle_raw⟩ := hC0 α f 3 hα hα1 (by norm_num) hSmoF hHk4f
  have hSint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * S z ^ 2)
      Work.Spaces.Iz := by
    refine hSint_raw.congr ?_
    filter_upwards with z
    have hz : S z
        = sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2), y = |Work.Spaces.DzIter 3 f z θ|} := by
      rw [hS]
    rw [hz]
    ring
  have hSle : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * S z ^ 2)
      ≤ C0 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
    have h := hSle_raw
    rw [show (fun z => sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          y = |Work.Spaces.DzIter 3 f z θ|} ^ 2 * (Work.Spaces.w z) ^ 2)
        = fun z => (Work.Spaces.w z) ^ 2 * S z ^ 2 from by
      funext z; rw [hS]; ring] at h
    exact h
  have hSbd : ∀ z : ℝ, 0 < z → BddAbove
      {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2), y = |Work.Spaces.DzIter 3 f z θ|} :=
    fun z hz => Work.FTS.TransportS.SlotT2.supOpen_slice_bddAbove (α := α) (f := f) (b := 3)
      hSmoF hHk4f hα hα1 (by norm_num) hz
  have hAle : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.mixed 3 0 f z θ| ≤ S z := by
    intro z hz θ hθ
    have h1 : |Work.Spaces.DzIter 3 f z θ|
        ≤ sSup {y : ℝ | ∃ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
            y = |Work.Spaces.DzIter 3 f z θ'|} := le_csSup (hSbd z hz) ⟨θ, hθ, rfl⟩
    have hz' : S z
        = sSup {y : ℝ | ∃ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
            y = |Work.Spaces.DzIter 3 f z θ'|} := by rw [hS]
    rw [Work.Spaces.mixed_zero_right, hz']
    exact h1
  -- (2) the uniform-in-`z` angular bound for the `(1,1)`-slot of `g`
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
  have hBbound : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn
          (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2) ≤ Cang * cg := by
    intro z hz
    have hae : (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 1 1 g z θ) ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
      filter_upwards [dmi_ae_mem_Iθ] with θ hθ
      rw [Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth hSmoG 1 hz hθ]
      exact dmi_mul_sq (γ := Work.Spaces.gam α)
        (X := Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ) (dmi_sin_two_pos hθ)
    refine ⟨?_, ?_⟩
    · refine MeasureTheory.Integrable.mono' (hHk4g.1 z (le_of_lt hz)) ?_ ?_
      · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g p.1 p.2) ^ 2) ?_ hz
        have h1 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
          refine ((Real.continuous_sin.comp
            (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
          intro p hp
          exact Or.inl (ne_of_gt (dmi_sin_two_pos hp.2))
        exact h1.mul ((hSmoG.mixed 1 1).continuousOn.pow 2)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _)
          (sq_nonneg _))]
        have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (one_le_w hz)
        have hXn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2 :=
          mul_nonneg (Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _) (sq_nonneg _)
        have hstep : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 1 1 g z θ) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 1 1 g z θ) ^ 2 := by
          have h := mul_le_mul_of_nonneg_right hw2 hXn
          simpa [one_mul, mul_assoc] using h
        refine hstep.trans ?_
        exact Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g hgam_pos le_rfl hz hθ 1 1
          (by norm_num) (by norm_num)
    · rw [MeasureTheory.integral_congr_ae hae]
      have h := hCang α g 1 hα hα1 hSmoG hHk4g (by norm_num) z hz
      rw [hcg]
      exact h
  -- (3) the angular bound for the `(3,1)`-slot of `g`, in terms of the marginals
  have hCbound : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g z θ) ^ 2) ≤ mg z := by
    intro z hz
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      fun θ hθ => Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g hgam_pos le_rfl hz hθ 3 1
        (by norm_num) (by norm_num)
    have hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2 := fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _)) (sq_nonneg _)
    have hint : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hHk4g.1 z (le_of_lt hz)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g p.1 p.2) ^ 2)
          (((dmi_continuousOn_w.pow 2).mul
            (dmi_continuousOn_sin_pow (-(Work.Spaces.gam α)))).mul
            ((hSmoG.mixed 3 1).continuousOn.pow 2)) hz
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (hnn θ hθ)]
        exact hpt θ hθ
    refine ⟨hint, ?_⟩
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hnn)
      (hHk4g.1 z (le_of_lt hz))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    rw [hmg]
    exact h
  -- (4) the pointwise-in-`z` bound on the marginal
  have hmarg : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z) := by
    intro z hz
    obtain ⟨hBint, hBle⟩ := hBbound z hz
    obtain ⟨hCint, hCle⟩ := hCbound z hz
    have hSnn : 0 ≤ S z := by
      refine le_trans (abs_nonneg _) (hAle z hz (π / 4) ?_)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hwnn : 0 ≤ Work.Spaces.w z := le_of_lt (w_pos_of_pos hz)
    have hmgnn : 0 ≤ mg z :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
    -- the two `L²`-functions of the Cauchy–Schwarz step
    set u : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
      * |Work.Spaces.mixed 1 1 g z θ| with hu
    set v : ℝ → ℝ := fun θ => Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
      * |Work.Spaces.mixed 3 1 g z θ| with hv
    have hsinnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
      fun θ hθ => Real.rpow_nonneg (dmi_sin_two_nonneg_of_mem hθ) _
    have hu0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ u θ := by
      intro θ hθ; rw [hu]; exact mul_nonneg (hsinnn θ hθ) (abs_nonneg _)
    have hv0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ v θ := by
      intro θ hθ; rw [hv]
      exact mul_nonneg (mul_nonneg hwnn (hsinnn θ hθ)) (abs_nonneg _)
    -- the a.e. shape of `u²` and `v²`
    have hu2ae : (fun θ => u θ ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2) := by
      filter_upwards [dmi_ae_mem_Iθ] with θ hθ
      simp only [hu]
      rw [mul_pow, sq_abs, dmi_rpow_half_sq (dmi_sin_two_pos hθ)]
    have hu2 : (∫ θ in Work.Spaces.Iθ, u θ ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 g z θ) ^ 2 :=
      MeasureTheory.integral_congr_ae hu2ae
    have hv2ae : (fun θ => v θ ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 3 1 g z θ) ^ 2) := by
      filter_upwards [dmi_ae_mem_Iθ] with θ hθ
      simp only [hv]
      rw [mul_pow, mul_pow, sq_abs, dmi_rpow_half_sq (dmi_sin_two_pos hθ)]
    have hv2 : (∫ θ in Work.Spaces.Iθ, v θ ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 3 1 g z θ) ^ 2 :=
      MeasureTheory.integral_congr_ae hv2ae
    -- the `L²`-memberships
    have hu_mem : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
      · rw [hu]
        exact Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))
            * |Work.Spaces.mixed 1 1 g p.1 p.2|)
          ((dmi_continuousOn_sin_pow (-(Work.Spaces.gam α / 2))).mul
            ((hSmoG.mixed 1 1).continuousOn.abs)) hz
      · exact hBint.congr hu2ae.symm
    have hv_mem : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
      · rw [hv]
        exact Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))
            * |Work.Spaces.mixed 3 1 g p.1 p.2|)
          ((dmi_continuousOn_w.mul (dmi_continuousOn_sin_pow (-(Work.Spaces.gam α / 2)))).mul
            ((hSmoG.mixed 3 1).continuousOn.abs)) hz
      · exact hCint.congr hv2ae.symm
    -- the pointwise bound for interior angles
    have hptF : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|
          ≤ (Work.Spaces.w z * S z) * (u θ * v θ) := by
      intro θ hθ
      have hσ := dmi_sin_two_pos hθ
      have hq1 := dmi_rpow_le hq0 hqγ hσ (Real.sin_le_one _)
      have hhalf := dmi_rpow_half_mul (γ := Work.Spaces.gam α) hσ
      have hA := hAle z hz θ hθ
      have h1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|
          ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * S z * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ| := by
        have h2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left hq1 (sq_nonneg _)
        have h3 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * |Work.Spaces.mixed 3 0 f z θ|
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * S z := by
          have := mul_le_mul h2 hA (abs_nonneg _)
            (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hσ) _))
          simpa [mul_assoc] using this
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (abs_nonneg _))
          (abs_nonneg _)
      have h2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * S z * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|
          = (Work.Spaces.w z * S z) * (u θ * v θ) := by
        simp only [hu, hv]
        rw [← hhalf]
        ring
      rw [h2] at h1
      exact h1
    have hptae : (fun θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z * S z) * (u θ * v θ)) := by
      filter_upwards [dmi_ae_mem_Iθ] with θ hθ
      exact hptF θ hθ
    have hFnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
        * |Work.Spaces.mixed 3 1 g z θ| := fun θ hθ => dmi_Fnonneg α q f g z θ hθ
    -- the Cauchy–Schwarz step in `θ`
    have hCS := dmi_cs_Iθ hu_mem hv_mem hu0 hv0
    have huv_int : MeasureTheory.IntegrableOn (fun θ => u θ * v θ) Work.Spaces.Iθ :=
      MeasureTheory.memLp_one_iff_integrable.mp (hu_mem.mul hv_mem)
    have hwS : 0 ≤ Work.Spaces.w z * S z := mul_nonneg hwnn hSnn
    have hsqrt_nn : 0 ≤ Real.sqrt (Cang * cg) := Real.sqrt_nonneg _
    have hFaesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f p.1 p.2| * |Work.Spaces.mixed 1 1 g p.1 p.2|
          * |Work.Spaces.mixed 3 1 g p.1 p.2|)
        ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          ((hSmoF.mixed 3 0).continuousOn.abs)).mul
          ((hSmoG.mixed 1 1).continuousOn.abs)).mul
          ((hSmoG.mixed 3 1).continuousOn.abs)) hz
    have hstep1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z * S z) * (u θ * v θ) :=
      MeasureTheory.integral_mono_of_nonneg
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hFnn)
        (huv_int.const_mul (Work.Spaces.w z * S z)) hptae
    have hstep2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z * S z) * (u θ * v θ))
        = (Work.Spaces.w z * S z) * (∫ θ in Work.Spaces.Iθ, u θ * v θ) :=
      MeasureTheory.integral_const_mul _ _
    have hCS' : (∫ θ in Work.Spaces.Iθ, u θ * v θ)
        ≤ Real.sqrt (Cang * cg) * Real.sqrt (mg z) := by
      refine hCS.trans ?_
      refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · rw [hu2]; exact hBle
      · rw [hv2]; exact hCle
    have hstep3 : (Work.Spaces.w z * S z) * (Real.sqrt (Cang * cg) * Real.sqrt (mg z))
        ≤ (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z) := by
      have hkey : 2 * (Work.Spaces.w z * S z) * Real.sqrt (mg z)
          ≤ (Work.Spaces.w z * S z) ^ 2 + mg z := by
        have h := two_mul_le_add_sq (Real.sqrt ((Work.Spaces.w z * S z) ^ 2)) (Real.sqrt (mg z))
        rw [Real.sq_sqrt (sq_nonneg _), Real.sq_sqrt hmgnn, Real.sqrt_sq_eq_abs,
          abs_of_nonneg hwS] at h
        exact h
      calc (Work.Spaces.w z * S z) * (Real.sqrt (Cang * cg) * Real.sqrt (mg z))
          = Real.sqrt (Cang * cg) * ((Work.Spaces.w z * S z) * Real.sqrt (mg z)) := by ring
        _ ≤ Real.sqrt (Cang * cg)
            * ((1 / 2) * ((Work.Spaces.w z * S z) ^ 2 + mg z)) := by
            refine mul_le_mul_of_nonneg_left ?_ hsqrt_nn
            linarith [hkey]
        _ = (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z) := by
            ring
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ (Work.Spaces.w z * S z) * (∫ θ in Work.Spaces.Iθ, u θ * v θ) := by
          rw [← hstep2]
          exact hstep1
      _ ≤ (Work.Spaces.w z * S z) * (Real.sqrt (Cang * cg) * Real.sqrt (mg z)) :=
          mul_le_mul_of_nonneg_left hCS' hwS
      _ ≤ (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z) := hstep3
  -- (5) integrability of the majorant and measurability of the marginal
  have hMint : MeasureTheory.Integrable
      (fun z => (1 / 2) * Real.sqrt (Cang * cg) * ((Work.Spaces.w z) ^ 2 * S z ^ 2 + mg z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hmgint : MeasureTheory.IntegrableOn mg Work.Spaces.Iz := by
      rw [hmg]
      exact hHk4g.2
    exact ((hSint.add hmgint).const_mul ((1 / 2) * Real.sqrt (Cang * cg)))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q) * |Work.Spaces.mixed 3 0 f p.1 p.2|
        * |Work.Spaces.mixed 1 1 g p.1 p.2| * |Work.Spaces.mixed 3 1 g p.1 p.2|)
        ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          ((hSmoF.mixed 3 0).continuousOn.abs)).mul
          ((hSmoG.mixed 1 1).continuousOn.abs)).mul
          ((hSmoG.mixed 3 1).continuousOn.abs)))
  refine MeasureTheory.Integrable.mono' hMint haesm ?_
  filter_upwards [dmi_ae_pos_Iz] with z hz
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
      * |Work.Spaces.mixed 3 1 g z θ| :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => dmi_Fnonneg α q f g z θ hθ)
  rw [Real.norm_of_nonneg hnn]
  exact hmarg z hz

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotWeightHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Continuity of the angular `rpow` weight on the open quadrant -/

/-- The uncurried angular weight `θ ↦ sin(2θ)^p` (applied to the second coordinate) is
continuous on the open quadrant, where `sin(2θ) > 0`. -/
theorem continuousOn_sin_two_rpow_snd (p : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => (Real.sin (2 * q.2)) ^ p)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2),
      0 < Real.sin (2 * q.2) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hq
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [h2.1])
      (by linarith [h2.2, Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun q hq => Or.inl (ne_of_gt (hsinpos q hq)))

/-! ## The `θ`-integrability of a single weighted slot -/


/-! ## The pointwise domination in `θ` -/

/-- **Pointwise domination of a weighted `ℋ⁴`-slot by the `ℋ⁴`-integrand.**  For every slot
`(a,b)` with `a + b ≤ 4` and every exponent `q` admissible for that slot (`q ∈ {0, η}` when
`a = 0`, `q ∈ {0, η, γ}` when `a ≥ 1`), and every angle `θ` in the open interval `(0, π/2)`,
`w(z)²·((D_z^bD_θ^a g)(z,θ))²·sin(2θ)^{-q} ≤ HkIntegrand α 4 g z θ`. -/
theorem slotWeight_pointwise_le (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α) (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- ## `a = 0`: the pure `D_z`-slot, with `q ≤ η`
    have hb4 : b ≤ 4 := by omega
    have hqle : q ≤ Work.Spaces.eta := by
      rcases hq0 ha0 with hq | hq
      · rw [hq]; exact le_of_lt Work.Spaces.eta_pos
      · rw [hq]
    have hsq : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le hqle hθ
    rw [ha0, Work.Spaces.mixed_zero_right]
    have hrhs : (Work.Spaces.DzIter b g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [mul_pow, Work.H2.T1Q.slotQ_whz_sq z hθI]
      ring
    rw [show (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DzIter b g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q) from by ring]
    refine le_trans (mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))) ?_
    rw [← hrhs]
    exact Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ b hb4
  · -- ## `a ≥ 1`: the mixed slot, with `q ≤ γ`
    have hqle : q ≤ Work.Spaces.gam α := by
      obtain hq | hq | hq := hqa hapos
      · rw [hq]; exact le_of_lt (Work.Spaces.gam_pos hα)
      · rw [hq]
        exact le_trans (le_of_lt Work.Spaces.eta_lt_one) (le_of_lt (Work.Spaces.one_lt_gam hα))
      · rw [hq]
    have hsq : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le hqle hθ
    have hrhs : (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2
        = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [mul_pow, Work.H2.T1Q.slotQ_wt_sq α z hθI]
      ring
    rw [show (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q) from by ring]
    refine le_trans (mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))) ?_
    rw [← hrhs]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ a b hapos hab

/-- The pointwise domination, in the almost-everywhere form needed for the `θ`-integration:
it holds at every `θ ∈ Iθ` except the two endpoints, which are null. -/
theorem ae_slotWeight_pointwise_le (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α) (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rw [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => slotWeight_pointwise_le α g a b q hα hab hq0 hqa hθ)

/-! ## The per-`z` bound -/

/-- **The per-`z` bound of the weighted slot energy.**  For every `z ∈ Iz`,
`w(z)²·∫_θ (D_z^bD_θ^a g)(z,θ)²·sin(2θ)^{-q} ≤ ∫_θ HkIntegrand α 4 g z θ`. -/
theorem slotWeight_z_le (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ))
  · rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z (le_of_lt hzpos)) ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)))
    · exact ae_slotWeight_pointwise_le α g a b q hα hab hq0 hqa z

/-! ## Almost-everywhere strong measurability of the `z`-marginal -/

/-- The `z`-marginal of the weighted slot energy is a.e. strongly measurable on `Iz`: the
uncurried slot is continuous on the open quadrant, hence a.e. strongly measurable for the
product measure, and integration in `θ` preserves a.e. strong measurability
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`). -/
theorem aesm_slotWeight (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed b a g p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-q))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hg.mixed b a).continuousOn.pow 2).mul (continuousOn_sin_two_rpow_snd (-q))
  have hX : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed b a g p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-q))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hinner := hX.integral_prod_right' (ν := volume.restrict Work.Spaces.Iθ)
  have hw2 : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    simp only [Work.Spaces.w]
    fun_prop
  exact hw2.aestronglyMeasurable.mul hinner

/-- The `z`-marginal of the weighted slot energy is nonnegative everywhere. -/
theorem slotWeight_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ) (z : ℝ) :
    0 ≤ (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) :=
  mul_nonneg (sq_nonneg _) (integral_nonneg_of_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _))))

/-! ## The main theorem -/

/-- The `z`-integrability and the `ℋ⁴`-bound of the weighted angular slot energy.
For `g` honestly in `ℋ⁴` (`SmoothOpen` plus `HkMem α 4 g`) and every slot `(a,b)` with
`a + b ≤ 4` and exponent `q` admissible for that slot (`q ∈ {0, eta}` for `a = 0`,
`q ∈ {0, eta, gam α}` for `a ≥ 1`), the function
`z ↦ w(z)²·∫_θ (mixed b a g z θ)²·sin(2θ)^{-q}` is integrable on `Iz = [0,∞)` with integral at
most `HkSq α 4 g`.

Route: `w(z)²·∫_θ ... ≤ ∫_θ w(z)²(...)²` (as `w² ≥ 0`), and the a.e. pointwise domination
`w(z)²σ^{-q}(mixed b a g z θ)² ≤ HkIntegrand α 4 g z θ` (for `a = 0`: `V = DzIter b g` and
`σ^{-q} ≤ σ^{-eta}`, giving the `i`-th `D_z`-summand of `HkIntegrand`; for `a ≥ 1`: the mixed
summand with weight `Wt α` and `q ≤ gam α`), first in `θ` for each `z ∈ Iz` (the `θ`-slice of
`HkIntegrand` is integrable by `HkMem`) and then in `z` (the `HkMem`-integrability of
`z ↦ ∫_θ HkIntegrand α 4 g z θ`, plus a.e. strong measurability of `z ↦ ∫_θ ...` from continuity
on the open quadrant, `Work.FTS.H2.aesm_of_Qd` /
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`).  Both conjuncts are needed: the second
by the per-slot assembly, the first to be able to `integral_const_mul`.

**Two traps.**  (1) The pointwise domination is *false* at `θ = 0` and `θ = π/2` when `q = 0`
(Lean has `0 ^ 0 = 1` but `0 ^ (-q) = 0` for `q > 0`, and the `HkIntegrand` summand vanishes
there), so it must be used a.e. (`setIntegral_mono_ae` / `integral_mono_ae`), not pointwise.
(2) For the first conjunct, the a.e. strong measurability of `z ↦ ∫_θ ...` on `Iz` has to cover
`z = 0`; there `w 0 = 0` and the whole function is `0`, so a `z = 0` case split (or an a.e.
argument on `Ioi 0`) settles it. -/
theorem SlotWeightHkSq (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        ≤ Work.Spaces.HkSq α 4 g := by
  set F : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) with hF
  set H : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hH
  have hle : ∀ z ∈ Work.Spaces.Iz, F z ≤ H z :=
    fun z hz => slotWeight_z_le α g a b q hα hα1 hg hmem hab hq0 hqa hz
  have hFint : MeasureTheory.IntegrableOn F Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hmem.2 (aesm_slotWeight α g a b q hg) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => by
      rw [Real.norm_of_nonneg (by rw [hF]; exact slotWeight_nonneg α g a b q z)]
      exact hle z hz)
  refine ⟨hFint, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hFint hmem.2
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hle z hz))
  simpa only [hH, Work.Spaces.HkSq] using hmono

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
end
-- ===== merged: Submission.Work.FTS.StrongPersist.QangDiff6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

/-- The angular moment at level `k + 2` for `g` is the angular moment at level `k` for the
`D_z²`-shift `D_z²g`: `Qang g (k+2) = Qang (D_z²g) k`.  This is the identity which lets the
whole level-4 `z`-calculus of the angular moments be applied to `D_z²g` instead of `g`,
producing the level-6 statements about `g`. -/
theorem Qang_DzIter_two_shift (g : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Elliptic.Qang g (k + 2) = Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) k := by
  funext z
  show (∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (k + 2) g z θ)
    = ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Work.Spaces.DzIter 2 g) z θ
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.Spaces.DzIter_add_right k 2 g]

theorem QangDiff6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    (∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        HasDerivAt (fun w => Work.Elliptic.Qang g j w)
          (Work.Elliptic.Qang g (j + 1) z / z) z) ∧
      (∀ j : ℕ, j ≤ 5 → ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0)) := by
  -- The two levels of honesty that the level-4 `z`-calculus of the angular moments consumes:
  -- `HkMem α 4 g` (for the moments of `g` itself) and `HkMem α 4 (D_z²g)` (for the moments of
  -- the shift, i.e. the moments of `g` at the two levels `4`, `5`).
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem
  have hmem5₁ : Work.Spaces.HkMem α 5 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 5 hO hmem
  have hmem4₂ : Work.Spaces.HkMem α 4 (Work.Spaces.DzIter 2 g) := by
    have h : Work.Spaces.HkMem α 4 (Work.Spaces.Dz (Work.Spaces.Dz g)) :=
      Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hO.Dz hmem5₁
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h
  have hO₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 2 g) := hO.DzIter 2
  -- the level-4 chain for `g`
  have hcont1 : ∀ j : ℕ, j ≤ 3 →
      ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) :=
    fun j hj => Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α g hO hmem4 hj
  have hder1 : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w) (Work.Elliptic.Qang g (j + 1) z / z) z :=
    fun j hj z hz =>
      Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α g hO hmem4 hj hz
        (hcont1 (j + 1) (by omega))
  -- the level-4 chain for the shift `D_z²g`
  have hcont2 : ∀ j : ℕ, j ≤ 3 →
      ContinuousOn (fun z => Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) j z) (Set.Ioi 0) :=
    fun j hj => Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α _ hO₂ hmem4₂ hj
  have hder2 : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) j w)
        (Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) (j + 1) z / z) z :=
    fun j hj z hz =>
      Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α _ hO₂ hmem4₂ hj hz
        (hcont2 (j + 1) (by omega))
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    rcases Nat.lt_or_ge j 3 with hlt | hge
    · exact hder1 j (by omega) z hz
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      have hk : k ≤ 2 := by omega
      have hfun : (fun w => Work.Elliptic.Qang g (k + 2) w)
          =ᶠ[nhds z] (fun w => Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) k w) :=
        Filter.Eventually.of_forall (fun w => congrFun (Qang_DzIter_two_shift g k) w)
      have hval : Work.Elliptic.Qang g (k + 2 + 1) z / z
          = Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) (k + 1) z / z := by
        rw [show k + 2 + 1 = (k + 1) + 2 from by omega,
          congrFun (Qang_DzIter_two_shift g (k + 1)) z]
      exact (hder2 k hk z hz).congr_of_eventuallyEq hfun |>.congr_deriv hval.symm
  · intro j hj
    rcases Nat.lt_or_ge j 4 with hlt | hge
    · exact hcont1 j (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      have hk : k ≤ 3 := by omega
      refine (hcont2 k hk).congr (fun z _ => ?_)
      exact congrFun (Qang_DzIter_two_shift g k) z

end Work.FTS.StrongPersist
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.Main =====
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
set_option maxHeartbeats 4000000

open Work.FTS.TransportS.SlotT2

/-! ## Elementary monotonicity of the canonical weight -/

theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `σ^{-η} ≤ σ^{-η'}` for `η ≤ η'` and `σ ∈ (0,1]`. -/
theorem rpow_neg_le_neg {σ a b : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hab : a ≤ b) :
    σ ^ (-a) ≤ σ ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by linarith)

/-- For `0 ≤ q ≤ 1 + η`, `σ^{1-q} ≤ σ^{-η}` on `σ ∈ (0,1]`. -/
theorem rpow_one_sub_le {σ q : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hq : q ≤ 1 + Work.Spaces.eta) : σ ^ (1 - q) ≤ σ ^ (-Work.Spaces.eta) :=
  Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by linarith)

theorem sqrt_mul_sqrt_le_half (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
  have h := two_mul_le_add_sq (Real.sqrt x) (Real.sqrt y)
  rw [Real.sq_sqrt hx, Real.sq_sqrt hy] at h
  linarith

/-! ## Almost everywhere versions of the two standard facts -/

/-- A pointwise statement for interior angles upgrades to an a.e. statement on `Iθ`. -/
theorem ae_of_forall_Ioo {P : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), P θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), P θ := by
  have hmeas : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-- A pointwise statement for positive radii upgrades to an a.e. statement on `Iz`. -/
theorem ae_of_forall_Ioi {P : ℝ → Prop} (h : ∀ z, 0 < z → P z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), P z := by
  have hmeas : (MeasureTheory.volume.restrict Work.Spaces.Iz : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume))).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h

/-! ## A slot predicate on the open quadrant

The Mathlib-side predicate `SlotW` demands the domination at *all* angles of `Iθ`, including the
endpoints `θ ∈ {0, π/2}`, where the weight `canonW 0 = w²` does not vanish.  For the exponent
`q = 0` (the leaf weight `w²`) the domination therefore fails there, while all the arguments
only ever use interior angles.  The predicate below only asks for the interior bound. -/

/-- The interior version of `SlotW`: `canonW q · X²` is dominated by the `ℋ⁴`-integrand of `f`
on the *open* quadrant. -/
def SlotWo (α q : ℝ) (X : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ

theorem SlotWo.of_slotW {α q : ℝ} {X f : ℝ → ℝ → ℝ} (h : SlotW α q X f) :
    SlotWo α q X f :=
  fun z θ hz hθ hθ2 => h.le z hz.le θ ⟨hθ.le, hθ2.le⟩

theorem slotWo_z {α : ℝ} {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    (f : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 4) : SlotWo α q (Work.Spaces.DzIter j f) f :=
  SlotWo.of_slotW (slotW_z α hq0 hq f j hj)

theorem slotWo_mixed {α : ℝ} {q : ℝ} (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    SlotWo α q (Work.Spaces.mixed j i f) f :=
  SlotWo.of_slotW (slotW_mixed α hq0 hqγ f j i hi hij)

/-- The pure `D_z`-slots at exponent `0` are slots for the `ℋ⁴`-integrand. -/
theorem slotWo_zero_z {α : ℝ} (f : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 4) :
    SlotWo α 0 (Work.Spaces.DzIter j f) f := by
  intro z θ hz hθ hθ2
  have hη := (slotWo_z (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl f j hj)
    z θ hz hθ hθ2
  have hle : canonW 0 z θ ≤ canonW Work.Spaces.eta z θ := by
    have h1 : canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
      simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
    rw [h1, canonW]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (one_le_rpow_neg Work.Spaces.eta_nonneg ⟨hθ, hθ2⟩)
  exact le_trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) hη

/-- The mixed slots at exponent `0` are slots for the `ℋ⁴`-integrand. -/
theorem slotWo_zero_mixed {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) : SlotWo α 0 (Work.Spaces.mixed j i f) f := by
  intro z θ hz hθ hθ2
  have hγ0 : 0 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.gam_pos hα)
  have hγ := (slotWo_mixed (α := α) (q := Work.Spaces.gam α) (Work.Spaces.gam_pos hα)
    le_rfl f j i hi hij) z θ hz hθ hθ2
  have hle : canonW 0 z θ ≤ canonW (Work.Spaces.gam α) z θ := by
    have h1 : canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
      simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
    rw [h1, canonW]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (one_le_rpow_neg hγ0 ⟨hθ, hθ2⟩)
  exact le_trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) hγ

/-! ## The pointwise splitting of a product of two canonical slots -/

/-- On the interval `Iθ`, `canonW q z θ · |G| · |Y|` is the product of the square roots of the
two `q`-weighted squares. -/
theorem canonW_mul_abs_eq {q z θ : ℝ} {G Y : ℝ → ℝ → ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW q z θ * |G z θ| * |Y z θ|
      = Real.sqrt (canonW q z θ * (G z θ) ^ 2)
        * Real.sqrt (canonW q z θ * (Y z θ) ^ 2) := by
  have hc : 0 ≤ canonW q z θ := canonW_nonneg hθ
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [show (Real.sqrt (canonW q z θ) * |G z θ|) * (Real.sqrt (canonW q z θ) * |Y z θ|)
      = (Real.sqrt (canonW q z θ) * Real.sqrt (canonW q z θ)) * (|G z θ| * |Y z θ|) from by
    ring]
  rw [Real.mul_self_sqrt hc]
  ring


/-- The product `√A · √B` of two `θ`-slice integrable densities is integrable (dominated by
the arithmetic mean). -/
theorem integrable_sqrt_mul_sqrt_slice {A B : ℝ → ℝ} {s : Set ℝ}
    (hA : MeasureTheory.IntegrableOn A s)
    (hB : MeasureTheory.IntegrableOn B s)
    (hAnn : ∀ x, 0 ≤ A x) (hBnn : ∀ x, 0 ≤ B x) :
    MeasureTheory.IntegrableOn (fun x => Real.sqrt (A x) * Real.sqrt (B x)) s := by
  refine MeasureTheory.Integrable.mono' ((hA.add hB).const_mul (1/2)) ?_ ?_
  · exact (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    show Real.sqrt (A x) * Real.sqrt (B x) ≤ (1/2) * (A x + B x)
    rw [show (1/2 : ℝ) * (A x + B x) = (A x + B x) / 2 from by ring]
    exact sqrt_mul_sqrt_le_half (A x) (B x) (hAnn x) (hBnn x)

/-! ## The three generic Leibniz-term bounds -/





/-! ## The top-slot bound (the radial integration by parts) -/

/-- Multiplication of a `SmoothOpen` function by a power of `sin(2θ)` keeps it `SmoothOpen`
(on the open quadrant the base is positive). -/
theorem smoothOpen_mul_rpow_sin {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (d : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin (2 * θ) ^ d * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => Real.sin (2 * θ) ^ d * f z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => Real.sin (2 * θ) ^ d * f z θ)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) ^ d * f p.1 p.2 from rfl]
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) ^ d) Work.FTS.EllipticEst.Q0 := by
    have htwo : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (2:ℝ) * p.2)
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2:ℝ))).mul
        (contDiffOn_snd (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0))
    refine (htwo.sin).rpow_const_of_ne ?_
    intro p hp
    have hp2 : 0 < p.2 := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by have := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2; linarith [Real.pi_pos]))
  exact h1.mul hf

/-- `D_z` of a product with a `θ`-only factor. -/
theorem Dz_mul_sin {f : ℝ → ℝ → ℝ} (d : ℝ) (z θ : ℝ) :
    Work.Spaces.Dz (fun z θ => Real.sin (2 * θ) ^ d * f z θ) z θ
      = Real.sin (2 * θ) ^ d * Work.Spaces.Dz f z θ := by
  simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_const_mul_field]
  ring


end Work.FTS.TransportS.T2Sup
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T3SlotAux.Remainder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3SlotAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary rearrangement -/

/-- The AM–GM rearrangement used for every Leibniz term: from a bound on the coefficient
factor and a bound on the product of the weight with the two `g`-factors, one gets the bound
on the full product. -/
theorem abs_term_le {ρ F G Y A X : ℝ} (h1 : ρ * |F| ≤ A) (h2 : A * (|G| * |Y|) ≤ X) :
    ρ * |F * G| * |Y| ≤ X := by
  rw [abs_mul]
  calc ρ * (|F| * |G|) * |Y| = (ρ * |F|) * (|G| * |Y|) := by ring
    _ ≤ A * (|G| * |Y|) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ X := h2

/-! ## The σ-gain of the leaf weights -/

theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-- `sin(2θ) · sin(2θ)^{-q} = sin(2θ)^{1-q}` on the open quadrant. -/
theorem sin_mul_sin_rpow_neg {θ q : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-q) = (Real.sin (2 * θ)) ^ (1 + -q) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [Real.rpow_add hs, Real.rpow_one]

/-- **The σ-gain of the leaf weights.**  For every leaf weight `ρ` of the slot `a`, the
product `sin(2θ)·ρ` is dominated by the canonical weight `canonW (γ-1)`. -/
theorem IsLeafW.sigma_mul_le_canonW {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : IsLeafW α a ρ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * ρ z θ
      ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hkey : ∀ {q : ℝ}, q ≤ Work.Spaces.gam α →
      (Real.sin (2 * θ)) ^ (1 + -q) ≤ (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
    intro q hq
    refine Real.rpow_le_rpow_of_exponent_ge
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
      hs1 ?_
    linarith
  have hcanon : (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α))
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
    rw [Work.FTS.TransportS.SlotT2.canonW,
      show -(Work.Spaces.gam α - 1) = 1 + -(Work.Spaces.gam α) by ring]
  rcases h with h | h | ⟨_, h⟩
  · subst h
    calc Real.sin (2 * θ) * leafEta z θ
        = (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          rw [leafEta]; ring
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.eta)) := by
          rw [sin_mul_sin_rpow_neg hθ]
      _ ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left (hkey (eta_le_gam hα)) (sq_nonneg _)
      _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := le_of_eq hcanon
  · subst h
    have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
      have h1 := one_le_rpow_neg (q := Work.Spaces.gam α - 1) (by linarith) hθ
      rwa [show -(Work.Spaces.gam α - 1) = 1 + -(Work.Spaces.gam α) by ring] at h1
    calc Real.sin (2 * θ) * leafOne z θ = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) := by
          rw [leafOne]; ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left (le_trans hs1 hone) (sq_nonneg _)
      _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := le_of_eq hcanon
  · subst h
    calc Real.sin (2 * θ) * leafGam α z θ
        = (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          rw [leafGam]; ring
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
          rw [sin_mul_sin_rpow_neg hθ]
      _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := le_of_eq hcanon


/-! ## The pointwise bound on a single Leibniz term -/

/-- **One non-exceptional Leibniz term.**  For `(a1,b1) ≠ (0,0)` the summand
`(D_z^{b1}D_θ^{a1}f)·(D_z^{b-b1+1}D_θ^{a-a1}g)` of the Leibniz expansion of
`D_z^bD_θ^a(f D_z g)` is bounded, against the leaf weight `ρ`, by `Mf · HkIntegrand α 4 g`.

* for `a1 = 0` (hence `b1 ≥ 1`) the coefficient factor is a pure `D_z`-derivative, bounded by
  `Mf`, and the two `g`-factors are `ℋ⁴`-slots of the weight class of the slot `a`;
* for `a1 ≥ 1` the coefficient factor carries the σ-gain of `CoefTh 3`, and the extra factor
  `sin(2θ)` moves the weight to `canonW (γ-1)`, which still dominates the weight classes of the
  two `g`-factors (whose angular indices are `a - a1` and `a`). -/
theorem term_le {α Mf C_f : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hMf : 0 ≤ Mf)
    (hleaf : IsLeafW α a ρ) (hab : a + b ≤ 4) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b)
    (hne : ¬ (a1 = 0 ∧ b1 = 0))
    (hDzb : ∀ b1 : ℕ, 1 ≤ b1 → b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter b1 f z θ| ≤ Mf)
    (hFmix : ∀ a1 b1 : ℕ, 1 ≤ a1 → a1 + b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b1 a1 f z θ| ≤ C_f * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f)
    (hMfC : C_f * Work.FTS.VocabO.CoefTh 3 f ≤ Mf)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ρ z θ * |Work.Spaces.mixed b1 a1 f z θ
        * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
      ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hρnn : 0 ≤ ρ z θ := IsLeafW.nonneg hleaf z hθI
  rcases eq_or_ne a1 0 with ha1zero | ha1ne
  · -- the coefficient factor is a pure `D_z`-derivative
    subst ha1zero
    have hb1pos : 1 ≤ b1 := by
      rcases Nat.eq_zero_or_pos b1 with h | h
      · exact absurd ⟨rfl, h⟩ hne
      · exact h
    have hb1le : b1 ≤ 4 := by omega
    have hidx : (a - 0) + (b - b1 + 1) ≤ 4 := by
      have h := Nat.sub_add_cancel hb1
      omega
    have h1 : ρ z θ * |Work.Spaces.mixed b1 0 f z θ| ≤ Mf * ρ z θ := by
      rw [Work.Spaces.mixed_zero_right]
      calc ρ z θ * |Work.Spaces.DzIter b1 f z θ| ≤ ρ z θ * Mf :=
            mul_le_mul_of_nonneg_left (hDzb b1 hb1pos hb1le z θ hz hθ0 hθ1) hρnn
        _ = Mf * ρ z θ := by ring
    have h2 : (Mf * ρ z θ) * (|Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
        * |Work.Spaces.mixed b a g z θ|) ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
      have hle : ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (qOf α a) z θ :=
        IsLeafW.le_canonW hα hleaf hz hθ
      have hq0 : 0 < qOf α a := qOf_pos α hα a
      have hqγ : qOf α a ≤ Work.Spaces.gam α := qOf_le_gam α hα a
      have hhi : (a - 0) = 0 → qOf α a ≤ Work.Spaces.eta := by
        intro h
        have ha0 : a = 0 := by omega
        rw [ha0]
        exact le_of_eq (qOf_zero α)
      have hha : a = 0 → qOf α a ≤ Work.Spaces.eta :=
        fun h => by rw [h]; exact le_of_eq (qOf_zero α)
      have hpair := canonW_pair_le (α := α) (g := g) (q := qOf α a) hq0 hqγ
        (j := b - b1 + 1) (i := a - 0) (b := b) (a := a) hhi hha hidx hab hzI hθI
      calc (Mf * ρ z θ) * (|Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
            * |Work.Spaces.mixed b a g z θ|)
          = Mf * ((ρ z θ * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|)
            * |Work.Spaces.mixed b a g z θ|) := by ring
        _ ≤ Mf * ((Work.FTS.TransportS.SlotT2.canonW (qOf α a) z θ
              * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|)
            * |Work.Spaces.mixed b a g z θ|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) (abs_nonneg _)) hMf
        _ ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := mul_le_mul_of_nonneg_left hpair hMf
    exact abs_term_le h1 h2
  · -- the coefficient factor carries the σ-gain of `CoefTh 3`
    have ha1pos : 1 ≤ a1 := Nat.one_le_iff_ne_zero.mpr ha1ne
    have hb1le : b1 ≤ 4 := by omega
    have hidx : (a - a1) + (b - b1 + 1) ≤ 4 := by
      have h1 := Nat.sub_add_cancel ha1
      have h2 := Nat.sub_add_cancel hb1
      omega
    have hsnn : 0 ≤ Real.sin (2 * θ) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ0]) (by linarith [hθ1, Real.pi_pos]))
    have h1 : ρ z θ * |Work.Spaces.mixed b1 a1 f z θ|
        ≤ Mf * (Real.sin (2 * θ) * ρ z θ) := by
      have hF := hFmix a1 b1 ha1pos (by omega) z θ hz hθ0 hθ1
      have hFM : |Work.Spaces.mixed b1 a1 f z θ| ≤ Real.sin (2 * θ) * Mf := by
        calc |Work.Spaces.mixed b1 a1 f z θ|
            ≤ C_f * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f := hF
          _ = Real.sin (2 * θ) * (C_f * Work.FTS.VocabO.CoefTh 3 f) := by ring
          _ ≤ Real.sin (2 * θ) * Mf := mul_le_mul_of_nonneg_left hMfC hsnn
      calc ρ z θ * |Work.Spaces.mixed b1 a1 f z θ| ≤ ρ z θ * (Real.sin (2 * θ) * Mf) :=
            mul_le_mul_of_nonneg_left hFM hρnn
        _ = Mf * (Real.sin (2 * θ) * ρ z θ) := by ring
    have h2 : (Mf * (Real.sin (2 * θ) * ρ z θ))
        * (|Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
          * |Work.Spaces.mixed b a g z θ|) ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
      have hsig : Real.sin (2 * θ) * ρ z θ
          ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ :=
        IsLeafW.sigma_mul_le_canonW hα hleaf hθ
      have hq0 : 0 < Work.Spaces.gam α - 1 := by
        rw [Work.Spaces.gam]; linarith
      have hqγ : Work.Spaces.gam α - 1 ≤ Work.Spaces.gam α := by linarith
      have hqη : Work.Spaces.gam α - 1 ≤ Work.Spaces.eta := by
        rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
      have hpair := canonW_pair_le (α := α) (g := g) (q := Work.Spaces.gam α - 1) hq0 hqγ
        (j := b - b1 + 1) (i := a - a1) (b := b) (a := a)
        (fun _ => hqη) (fun h => absurd h (by omega)) hidx hab hzI hθI
      calc (Mf * (Real.sin (2 * θ) * ρ z θ))
            * (|Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)
          = Mf * ((Real.sin (2 * θ) * ρ z θ)
            * (|Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)) := by ring
        _ ≤ Mf * ((Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|)
            * |Work.Spaces.mixed b a g z θ|) := by
            refine mul_le_mul_of_nonneg_left ?_ hMf
            calc Real.sin (2 * θ) * ρ z θ
                  * (|Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
                    * |Work.Spaces.mixed b a g z θ|)
                = ((Real.sin (2 * θ) * ρ z θ)
                    * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|)
                  * |Work.Spaces.mixed b a g z θ| := by ring
              _ ≤ ((Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ
                    * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|)
                  * |Work.Spaces.mixed b a g z θ|) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hsig (abs_nonneg _)) (abs_nonneg _)
        _ ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := mul_le_mul_of_nonneg_left hpair hMf
    exact abs_term_le h1 h2

/-! ## The pointwise bound on the whole exceptional-free remainder -/

/-- **The Leibniz expansion and the pointwise bound on the remainder.**  On the open quadrant,

`D_z^bD_θ^a(f D_z g) - f · D_z(D_z^bD_θ^a g)`
  `= ∑_{(a1,b1) ≠ (0,0)} c(a1,b1)·(D_z^{b1}D_θ^{a1}f)·(D_z^{b-b1+1}D_θ^{a-a1}g)`,

and each summand is bounded by `Mf · HkIntegrand α 4 g` (`term_le`), so the whole remainder,
weighted by the leaf weight `ρ` and paired with `D_z^bD_θ^a g`, is bounded by
`6400 Mf HkIntegrand α 4 g`. -/
theorem remainder_pointwise {α Mf C_f : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hleaf : IsLeafW α a ρ) (hab : a + b ≤ 4)
    (hDzb : ∀ b1 : ℕ, 1 ≤ b1 → b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter b1 f z θ| ≤ Mf)
    (hFmix : ∀ a1 b1 : ℕ, 1 ≤ a1 → a1 + b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b1 a1 f z θ| ≤ C_f * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f)
    (hMfC : C_f * Work.FTS.VocabO.CoefTh 3 f ≤ Mf) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρ z θ * (Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
          - f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ)
        * Work.Spaces.mixed b a g z θ|
        ≤ 6400 * Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hρnn : 0 ≤ ρ z θ := IsLeafW.nonneg hleaf z hθI
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hleib := Work.FTS.TransportS.mixed_mul_Dz_open b a f g hsf hsg z θ hz hθ0 hθ1
  set s : Finset (ℕ × ℕ) := Finset.range (a + 1) ×ˢ Finset.range (b + 1) with hs
  set F : ℕ × ℕ → ℝ := fun p => (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ)
      * (Work.Spaces.mixed p.2 p.1 f z θ
        * Work.Spaces.mixed (b - p.2 + 1) (a - p.1) g z θ) with hF
  have hsumprod : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (a.choose a1 : ℝ) * (b.choose b1 : ℝ)
        * (Work.Spaces.mixed b1 a1 f z θ
          * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ))
      = ∑ p ∈ s, F p := by
    rw [hs]
    exact (Finset.sum_product (Finset.range (a + 1)) (Finset.range (b + 1)) F).symm
  have h00mem : ((0, 0) : ℕ × ℕ) ∈ s := by
    rw [hs]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hDz : Work.Spaces.mixed (b + 1) a g z θ
      = Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ := rfl
  have h00F : F (0, 0) = f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ := by
    rw [hF]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul,
      Nat.sub_zero, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero, hDz]
  have hR : Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        - f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
      = ∑ p ∈ s.erase (0, 0), F p := by
    rw [hleib, hsumprod, ← h00F]
    exact (Finset.sum_erase_eq_sub (s := s) (f := F) (a := (0,0)) h00mem).symm
  have hterm : ∀ p ∈ s.erase (0, 0),
      |ρ z θ * F p * Work.Spaces.mixed b a g z θ|
        ≤ ((a.choose p.1 : ℝ) * (b.choose p.2 : ℝ))
          * (Mf * Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro p hp
    have hp' : p ∈ s := Finset.mem_of_mem_erase hp
    have hpne : p ≠ (0, 0) := Finset.ne_of_mem_erase hp
    rw [hs] at hp'
    have ha1 : p.1 ≤ a :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hp').1)
    have hb1 : p.2 ≤ b :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hp').2)
    have hne : ¬ (p.1 = 0 ∧ p.2 = 0) := by
      rintro ⟨h1, h2⟩
      exact hpne (by ext <;> simp [h1, h2])
    have hcore := term_le (α := α) (Mf := Mf) (C_f := C_f) (f := f) (g := g) (a := a) (b := b)
      (a1 := p.1) (b1 := p.2) (ρ := ρ) hα hα1 hMf hleaf hab ha1 hb1 hne hDzb hFmix hMfC
      hz hθ0 hθ1
    have hc : 0 ≤ (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ) := by positivity
    calc |ρ z θ * F p * Work.Spaces.mixed b a g z θ|
        = ((a.choose p.1 : ℝ) * (b.choose p.2 : ℝ))
          * (ρ z θ * |Work.Spaces.mixed p.2 p.1 f z θ
              * Work.Spaces.mixed (b - p.2 + 1) (a - p.1) g z θ|
            * |Work.Spaces.mixed b a g z θ|) := by
          rw [hF]
          simp only [abs_mul, abs_of_nonneg hρnn, abs_of_nonneg hc,
            abs_of_nonneg (show (0 : ℝ) ≤ ((a.choose p.1 : ℕ) : ℝ) by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ ((b.choose p.2 : ℕ) : ℝ) by positivity)]
          ring
      _ ≤ ((a.choose p.1 : ℝ) * (b.choose p.2 : ℝ))
          * (Mf * Work.Spaces.HkIntegrand α 4 g z θ) := mul_le_mul_of_nonneg_left hcore hc
  have hcoef : ∀ p : ℕ × ℕ, (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ) ≤ 256 := by
    intro p
    have ha4 : a ≤ 4 := by omega
    have hb4 : b ≤ 4 := by omega
    have h1 : (a.choose p.1 : ℝ) ≤ 16 := by
      have h : a.choose p.1 ≤ 2 ^ 4 :=
        le_trans (Nat.choose_le_two_pow a p.1) (Nat.pow_le_pow_right (by norm_num) ha4)
      exact_mod_cast h
    have h2 : (b.choose p.2 : ℝ) ≤ 16 := by
      have h : b.choose p.2 ≤ 2 ^ 4 :=
        le_trans (Nat.choose_le_two_pow b p.2) (Nat.pow_le_pow_right (by norm_num) hb4)
      exact_mod_cast h
    calc (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ) ≤ 16 * 16 :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by norm_num)
      _ = 256 := by norm_num
  have hsumc : ∑ p ∈ s.erase (0, 0),
      (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ) ≤ 6400 := by
    have hcard : (s.erase (0, 0)).card ≤ 25 := by
      have h1 : s.card = (a + 1) * (b + 1) := by
        rw [hs, Finset.card_product]
        simp
      have h2 : (s.erase (0, 0)).card ≤ s.card := Finset.card_erase_le
      have ha4 : a ≤ 4 := by omega
      have hb4 : b ≤ 4 := by omega
      have hmul : (a + 1) * (b + 1) ≤ 25 := by
        have h3 : a + 1 ≤ 5 := by omega
        have h4 : b + 1 ≤ 5 := by omega
        exact le_trans (Nat.mul_le_mul h3 h4) (by norm_num)
      omega
    calc ∑ p ∈ s.erase (0, 0), (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ)
        ≤ ∑ _p ∈ s.erase (0, 0), (256 : ℝ) :=
          Finset.sum_le_sum fun p _ => hcoef p
      _ = ((s.erase (0, 0)).card : ℝ) * 256 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 25 * 256 := by
          have : ((s.erase (0, 0)).card : ℝ) ≤ 25 := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right this (by norm_num)
      _ = 6400 := by norm_num
  have hmain : |ρ z θ * (∑ p ∈ s.erase (0, 0), F p) * Work.Spaces.mixed b a g z θ|
      ≤ 6400 * Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
    have h1 : ρ z θ * (∑ p ∈ s.erase (0, 0), F p) * Work.Spaces.mixed b a g z θ
        = ∑ p ∈ s.erase (0, 0), (ρ z θ * F p * Work.Spaces.mixed b a g z θ) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [h1]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    calc (∑ p ∈ s.erase (0, 0), (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ))
          * (Mf * Work.Spaces.HkIntegrand α 4 g z θ)
        ≤ 6400 * (Mf * Work.Spaces.HkIntegrand α 4 g z θ) :=
          mul_le_mul_of_nonneg_right hsumc (mul_nonneg hMf hHknn)
      _ = 6400 * Mf * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  rwa [← hR] at hmain

end Work.FTS.TransportS.T3SlotAux
end
end
