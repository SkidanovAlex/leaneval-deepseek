import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.hkMemOfJConv
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.BSlotTop.SliceAngGenFts =====
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
set_option maxHeartbeats 1600000

/-- **The one-dimensional angular estimate** (the `OneD`-shaped statement of `TT.ESW`). -/
theorem sliceAngGenFts (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (iteratedDeriv j u θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨Co, hCopos, hvout⟩ := Work.FTS.EllipticEst.remov.slice_ang_v_outer k hk
  -- the top-order slot in the reflected divided variable, fed through
  -- `farTopXAuxLive_of_top` into the reflected `shiftV` form expected by
  -- `slice_ang_v_far_live_of_top`
  obtain ⟨Cf, hCfpos, hvfar⟩ :=
    Work.FTS.EllipticEst.remov.slice_ang_v_far_live_of_top k hk
      (Work.FTS.EllipticEst.remov.farTopXAuxLive_of_top k hk
        (Work.FTS.EllipticEst.remov.EllFarTopDiv.sinWeight_xDivX_top_le' k hk))
  -- the `v`-slot bounds on the whole angular interval
  have hV : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.SliceHyp k γ u g → ∀ m : ℕ, m ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
        ∧ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
    refine ⟨Co + Cf, by linarith, ?_⟩
    intro γ u g h m hm
    obtain ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hH1, hH2, hH3, hH4, hH5, hH6⟩ := h
    obtain ⟨ho1, ho2⟩ :=
      hvout γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 m hm
    obtain ⟨hf1, hf2⟩ :=
      hvfar γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 m hm
    have hU : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ∪ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)
        = Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ, Set.Icc_union_Icc_eq_Icc (by positivity)
        (by linarith [Real.pi_pos])]
    constructor
    · have hunion := ho1.union hf1
      rwa [hU] at hunion
    · rw [Work.FTS.EllipticEst.remov.integral_split_Iθ
        (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) ho1 hf1]
      linarith
  obtain ⟨C, hC, hfin⟩ := sliceAngGenFinalFts k hk hV
  exact ⟨C, hC, fun γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 =>
    hfin γ u g ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hH1, hH2, hH3, hH4, hH5, hH6⟩⟩

end Work.FTS.EllipticEst.Prop.BSlotTop
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeODE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem SlotsZeroModeODE {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0)
    (h0 : ∀ z, Φ z 0 = 0)
    (hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ)) :
    ∀ m : ℕ,
      MeasureTheory.LocallyIntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) ∧
      (∀ ρ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ρ) → HasCompactSupport ρ →
        tsupport ρ ⊆ Set.Ioi 0 →
        (∫ z in Set.Ioi 0, z ^ ((5 - α) / α) * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
          - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
          * (∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ)) = 0) ∧
      MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 * z ^ (-4 : ℝ))
        (Set.Ioi 0) := by
  intro m
  have hL2 : L2Facts α Φ := SlotsZeroModeL2 (α := α) (Φ := Φ) hsm hHk
  have hcut : CutFacts m := SlotsZeroCutoff m
  obtain ⟨C, hCpos, hCpt⟩ := hL2.2.2.2.1
  refine ⟨(hL2.1 m).1, ?_, (hL2.1 m).2⟩
  intro ρ hρ hρc hρs
  obtain ⟨a, b, ha, hab, hsub⟩ := exists_Icc_of_tsupport_subset hρc hρs
  have hk := key_iter (α := α) (Φ := Φ) (ρ := ρ) (m := m) (C := C) (a := a) (b := b)
    hsm hsol hρ hρc hρs hcut hL2.2.1 hCpt hCpos.le
    (hL2.2.2.2.2.2.2 a b ha hab) (hL2.2.2.2.2.1 a b ha hab) ha hsub
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Φ z θ
          * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
          * (z ^ ((5 - α) / α) * Real.cos θ))
        = z ^ ((5 - α) / α) * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
            - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
          * (∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ) := by
    intro z
    have hpt : (∫ θ in Work.Spaces.Iθ, Φ z θ
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
        * (z ^ ((5 - α) / α) * Real.cos θ))
        = ∫ θ in Work.Spaces.Iθ, (z ^ ((5 - α) / α)
            * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
              - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
            * (Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
      rw [← restrict_Ioo_eq_Iθ]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
      have hcos : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
      rw [bslOp_sepMode (α := α) (ρ := ρ) (m := m) hcos, radOp]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
  have hcongr : (∫ z in Set.Ioi 0, z ^ ((5 - α) / α) * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
        * (∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Real.cos θ))
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Φ z θ
          * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
          * (z ^ ((5 - α) / α) * Real.cos θ) := by
    refine MeasureTheory.setIntegral_congr_ae (μ := volume) (s := Set.Ioi 0)
      (f := fun z => z ^ ((5 - α) / α) * (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
        * (∫ θ in Work.Spaces.Iθ, Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ))
      (g := fun z => ∫ θ in Work.Spaces.Iθ, Φ z θ
          * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
          * (z ^ ((5 - α) / α) * Real.cos θ))
      measurableSet_Ioi (Eventually.of_forall fun z _ => (hinner z).symm)
  rw [hcongr, hk]

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkg_O =====
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

theorem IntPkg_O {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f) :
    Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f := by
  obtain ⟨hs, hm, hb⟩ := hf
  -- the five squared-block integrability fields
  obtain ⟨hsqE, hsqME, hsqMG, hsqO, hsqMO⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.IntPkgSq_O α hα hs hm
  -- the `𝓛`-pairings
  have hLf_eta := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqE 0 (by norm_num)) (hsqE 1 (by norm_num))
  have hLDz_eta := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs.Dz
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqE 1 (by norm_num)) (hsqE 2 (by norm_num))
  have hLDth_gam := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs.Dth
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqMG 1 0 (by norm_num) (by norm_num)) (hsqMG 1 1 (by norm_num) (by norm_num))
  have hLf_one := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs
    Work.FTS.CoercivityFix.Coer1.continuousOn_w2
    Work.FTS.CoercivityFix.Coer1.w2_nonneg
    (hsqO 0 (by norm_num)) (hsqO 1 (by norm_num))
  have hLDz_one := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs.Dz
    Work.FTS.CoercivityFix.Coer1.continuousOn_w2
    Work.FTS.CoercivityFix.Coer1.w2_nonneg
    (hsqO 1 (by norm_num)) (hsqO 2 (by norm_num))
  have hLDth_one := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O hs.Dth
    Work.FTS.CoercivityFix.Coer1.continuousOn_w2
    Work.FTS.CoercivityFix.Coer1.w2_nonneg
    (hsqMO 1 0 (by norm_num) (by norm_num)) (hsqMO 1 1 (by norm_num) (by norm_num))
  -- the transport pairings
  have hintf_eta := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O hs
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqE 0 (by norm_num)) (hsqME 1 0 (by norm_num) (by norm_num))
  have hthDz : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth (Work.Spaces.Dz f) z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hae : (Function.uncurry (fun z θ =>
          (Work.Spaces.mixed 1 1 f z θ) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
        =ᵐ[MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
        (Function.uncurry (fun z θ => (Work.Spaces.Dth (Work.Spaces.Dz f) z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)) := by
      have h := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.ae_Dz_Dth_comm_O hs
      rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict] at h
      filter_upwards [h] with p hp
      show (Work.Spaces.Dz (Work.Spaces.Dth f) p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2
        = (Work.Spaces.Dth (Work.Spaces.Dz f) p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2
      rw [hp]
    exact (hsqME 1 1 (by norm_num) (by norm_num)).congr hae
  have hintDz_eta := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O hs.Dz
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqE 1 (by norm_num)) hthDz
  have hintDth_gam := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O hs.Dth
    (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)
    (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
    (hsqMG 1 0 (by norm_num) (by norm_num)) (hsqMG 2 0 (by norm_num) (by norm_num))
  have hintf_one := Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O hs
    Work.FTS.CoercivityFix.Coer1.continuousOn_w2
    Work.FTS.CoercivityFix.Coer1.w2_nonneg
    (hsqO 0 (by norm_num)) (hsqMO 1 0 (by norm_num) (by norm_num))
  -- the `Lhat`- and `E2hat`-pairings of the `D_z`-commutator split
  have hLhat := Work.FTS.CoercivityFix.Coer1.intLhat_of hLDz_eta
    (Work.FTS.CoercivityFix.Coer1.intTransport_of hintDz_eta)
  have hE2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
        * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.intE2hat_of
      (Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.continuousOn_E2hat_O hs
        (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _))
      (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _)
      (hsqE 0 (by norm_num)) (hsqE 1 (by norm_num)) (hsqME 1 0 (by norm_num) (by norm_num))
  -- the boundary traces of the three `z`-integrations by parts
  have hasm0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 0 0 (by norm_num)).1 θ hθ).1
  have hasmT0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 0 0 (by norm_num)).1 θ hθ).2
  have hasm1 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 0 1 (by norm_num)).1 θ hθ).1
  have hasmT1 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 0 1 (by norm_num)).1 θ hθ).2
  have hasm2 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dth f z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 1 0 (by norm_num)).1 θ hθ).1
  have hasmT2 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dth f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 1 0 (by norm_num)).1 θ hθ).2
  refine ⟨hsqE, hsqME, hsqMG, hsqO, hsqMO, hLf_eta, hLDz_eta, hLDth_gam, hLf_one,
    hLhat, hE2, hintf_eta, hintDz_eta, hintDth_gam, hintf_one, ?_, ?_, ?_⟩
  · -- `ZIBPO f`
    refine Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs hasm0 hasmT0 ?_ hLf_one
    refine (hsqO 0 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
    ring
  · -- `ZIBPO (D_z f)`
    refine Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs.Dz hasm1 hasmT1 ?_ hLDz_one
    refine (hsqO 1 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    ring
  · -- `ZIBPO (D_θ f)`
    refine Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs.Dth hasm2 hasmT2 ?_ hLDth_one
    refine (hsqMO 1 0 (by norm_num) (by norm_num)).congr
      (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    ring

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalZero_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem JepsMarginalZero_zero {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f)
    (hlamm : Measurable lam)
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    (htr : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (lam z)))
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
        (f z θ - lam z)^2
          ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * (∫ σ in Work.Spaces.Iθ,
                (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2))
    (hjtr : ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε f z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ z ∈ Set.Ioi (0:ℝ),
      (∫ s : ℝ, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))) = 0 := by
  intro z hz
  -- the two constants of the estimate
  have hgam : (1 : ℝ) < Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith [hα.1]
  set A : ℝ := 100 / (Work.Spaces.gam α - 1) with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  set Kb : ℝ := max 1 A with hKbdef
  have hKb1 : 1 ≤ Kb := by rw [hKbdef]; exact le_max_left _ _
  have hKbA : A ≤ Kb := by rw [hKbdef]; exact le_max_right _ _
  have hKb0 : 0 ≤ Kb := le_trans zero_le_one hKb1
  -- the linear pointwise bound of `hbd`, valid a.e. in `z`
  have hbdlin : ∀ᵐ w ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ∀ θ ∈ Set.Ioo 0 (Real.pi/4), |f w θ - lam w| ≤ (A * Ibd α f w + 1) / 2 := by
    have h := HbdPointwiseLe hα hbd
    filter_upwards [h] with w hw
    intro θ hθ
    have h2 := hw θ hθ
    rw [hAdef]
    exact h2
  -- transport the a.e. statements to the `p`-variable
  have hbdp : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
      |f (z * Real.exp (-p.1)) θ - lam (z * Real.exp (-p.1))|
        ≤ (A * Ibd α f (z * Real.exp (-p.1)) + 1) / 2 :=
    AEShiftPreimage hz hbdlin
  have htrp : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
      Filter.Tendsto (fun θ => f (z * Real.exp (-p.1)) θ) (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (lam (z * Real.exp (-p.1)))) :=
    AEShiftPreimage hz htr
  -- the `θ`-shift converges to `0⁺`
  have hshift : ∀ p₂ : ℝ, Filter.Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
    intro p₂
    have hcont : ContinuousAt (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂))) 0 :=
      Real.continuous_arctan.continuousAt.comp
        ((Real.continuousAt_tan.mpr (by rw [Real.cos_zero]; norm_num)).mul_const _)
    have htend : Filter.Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂)))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂)))
          (nhds (0 : ℝ)) (nhds (Real.arctan (Real.tan 0 * Real.exp (-p₂)))) := hcont.tendsto
      have h2 : Real.arctan (Real.tan 0 * Real.exp (-p₂)) = 0 := by simp
      rw [h2] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_iff.mpr ⟨htend, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi/2 by positivity)] with θ hθ
    exact (Real.arctan_pos).2
      (mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _))
  -- the integrability of the dominating density
  have hIbdint : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun w : ℝ => Ibd α f w) (Set.Icc a b) :=
    fun a b ha hab => IbdLocalIntegrable hso hm ha hab
  have hdom : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1))))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    JkerDomDensityIntegrable hρ hε hz hlamm hint hIbdint
  have hJ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖)
      (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    (Work.FTS.StrongEps.Jker_integrable hρ.moll hε).norm
  have hbdd : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Kb * (‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))
        + ‖Work.FTS.StrongEps.Jker ρ ε p‖))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    (hdom.add hJ).const_mul Kb
  -- the three inputs of the dominated convergence theorem
  have hmeas : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0), MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi/2 by positivity)] with θ hθ
    exact (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).aestronglyMeasurable.mul
      (AEShiftProfile hso hz hθ)
  obtain ⟨θ₀, hθ₀pos, hθ₀mem⟩ := ThShiftSmall hε
  have hbound : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
      ‖Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))‖
      ≤ Kb * (‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))
        + ‖Work.FTS.StrongEps.Jker ρ ε p‖) := by
    filter_upwards [Ioo_mem_nhdsGT hθ₀pos] with θ hθ
    filter_upwards [hbdp] with p hp
    by_cases hJ0 : Work.FTS.StrongEps.Jker ρ ε p = 0
    · rw [hJ0, zero_mul, norm_zero]
      simp
    · have hp2 : |p.2| ≤ ε := by
        have hsup := Work.FTS.StrongEps.Jker_ne_zero_support hρ.moll hε hJ0
        have hsq : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
        have h2 := (sq_le_sq.mp hsq : |p.2| ≤ |ε|)
        rwa [abs_of_pos hε] at h2
      have hΘ : Real.arctan (Real.tan θ * Real.exp (-p.2)) ∈ Set.Ioo 0 (Real.pi/4) :=
        hθ₀mem θ hθ p.2 hp2
      have hfl := hp _ hΘ
      have hJnn : 0 ≤ ‖Work.FTS.StrongEps.Jker ρ ε p‖ := norm_nonneg _
      have hLnn : 0 ≤ |lam (z * Real.exp (-p.1))| := abs_nonneg _
      have hInn : 0 ≤ Ibd α f (z * Real.exp (-p.1)) := Ibd_nonneg α f _
      have hf : |f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))|
          ≤ |lam (z * Real.exp (-p.1))|
            + (A * Ibd α f (z * Real.exp (-p.1)) + 1) / 2 := by
        have h1 := abs_add_le
          (f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))
            - lam (z * Real.exp (-p.1))) (lam (z * Real.exp (-p.1)))
        simp only [sub_add_cancel] at h1
        linarith
      calc ‖Work.FTS.StrongEps.Jker ρ ε p *
            f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))‖
          = ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            |f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))| := by
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            (|lam (z * Real.exp (-p.1))|
              + (A * Ibd α f (z * Real.exp (-p.1)) + 1) / 2) :=
              mul_le_mul_of_nonneg_left hf hJnn
        _ ≤ ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            (Kb * (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)) + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ hJnn
              have hexp : Kb * (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)) + 1)
                  = Kb * |lam (z * Real.exp (-p.1))| + Kb * Ibd α f (z * Real.exp (-p.1))
                    + Kb := by ring
              have h3 : A * Ibd α f (z * Real.exp (-p.1)) / 2
                  ≤ Kb * Ibd α f (z * Real.exp (-p.1)) := by
                have h4 := mul_le_mul_of_nonneg_right (by linarith : A / 2 ≤ Kb) hInn
                linarith
              have h4 : |lam (z * Real.exp (-p.1))| ≤ Kb * |lam (z * Real.exp (-p.1))| := by
                have h5 := mul_le_mul_of_nonneg_right hKb1 hLnn
                simpa using h5
              have h5 : (1 : ℝ) / 2 ≤ Kb := by linarith
              linarith
        _ = Kb * (‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))
            + ‖Work.FTS.StrongEps.Jker ρ ε p‖) := by ring
  have hlimae : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)), Filter.Tendsto
      (fun θ => Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))) := by
    filter_upwards [htrp] with p hp
    exact Tendsto.const_mul _ (hp.comp (hshift p.2))
  -- dominated convergence
  have hdct : Filter.Tendsto
      (fun θ => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (MeasureTheory.volume : Measure (ℝ × ℝ)))
      (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
      (F := fun θ p => Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (f := fun p => Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
      (fun p : ℝ × ℝ => Kb * (‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))
        + ‖Work.FTS.StrongEps.Jker ρ ε p‖))
      hmeas hbound hbdd hlimae
  -- rewrite `Jeps` into the `p`-integral form and the limit into the marginal integral
  have hcoe : ∀ θ ∈ Set.Ioo 0 (Real.pi/2), Work.FTS.StrongEps.Jeps ρ ε f z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p *
          f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))) := by
    intro θ hθ
    rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε f hz hθ]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]
  have hjeps : Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε f z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))) :=
    hdct.congr' (by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi/2 by positivity)] with θ hθ
      exact (hcoe θ hθ).symm)
  rw [MarginalTransferIntegrable hρ.moll hε hz hlamm hint] at hjeps
  -- uniqueness of the limit: the trace hypothesis says the same limit is `0`
  exact (tendsto_nhds_unique (hjtr z hz) hjeps).symm

end Work.FTS.StrongEps.EpsLocalPStar
end
