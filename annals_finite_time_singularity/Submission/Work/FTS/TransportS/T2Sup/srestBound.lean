import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityStep.Step.Coercive
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.FluxOpen
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotData
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.slotDz_LGammaT_O =====
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
set_option maxHeartbeats 1600000

theorem slotDz_LGammaT_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Work.FTS.Galerkin.Fn} (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hHH : Work.Coercivity.HardyHyp f) :
    (1 / 5) * Work.Coercivity.EDz f - 100 * Work.Coercivity.EfEta f
        - 100 * Work.Coercivity.EDth α f - 10 ^ 12 * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) := by
  have hα1' : α ≤ 1 := by linarith
  have hα4 : α ≤ 1 / 4 := by linarith
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hf2 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f :=
    Work.FTS.StrongEps.EpsE4Thr.regQo_mono (by norm_num) hf.1
  -- ## the two estimates
  have hC0 := OClass.C0_sq_le_Ef_O α hα hα1' hso hf2 hIP
  obtain ⟨hS2_int, hS_bound, hpair_int, hpair_lb⟩ :=
    OClass.Zrest_pairing_ge_O α hα hα1 hso hf2 hIP hHH hC0
  have hA' : (47 / 100) * Work.Coercivity.EDz f
      - (Work.Coercivity.EfEta f + 4 * Work.Coercivity.EDth α f
        + (1 / 8) * Work.Coercivity.EDz f)
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f) := by
    have h := OClass.est_A_O α hα hα4 hf2 hIP
    rwa [← Work.FTS.CoercivityFix.Coer1.EDz_eq_En,
      ← Work.FTS.CoercivityFix.Coer1.EfEta_eq_En,
      ← Work.FTS.CoercivityFix.Coer1.EDth_eq_En α f] at h
  -- ## integrability of the `𝓛̂`-pairing
  have hDzLhat_int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hsum := hIP.intLhat_Dz_eta.add hIP.intE2hat_Dz_eta
    refine hsum.congr ?_
    have hμ : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.CoercivityFix.Coer1.iz_prod_restrict.symm
    rw [hμ]
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    obtain ⟨z, θ⟩ := p
    have hkey : Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
          + Work.FTS.CoercivityFix.E2hat f z θ :=
      Work.FTS.StrongPersist.H6Aux.Dz_Lhat_of_open
        (V := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) (isOpen_Ioi.prod isOpen_Ioo)
        (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) from hso)
        ⟨hp1, hp2⟩ hp1
    simp only [Pi.add_apply, Function.uncurry_apply_pair]
    rw [hkey]
    ring
  -- ## the a.e. pointwise decomposition and the splitting of the pairing
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
          + (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ) := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    have h := OClass.Dz_LGammaT_eq_Lhat_add_Zrest_O α hα hα1 hso hHH z θ hz hθ
    rw [h]
    ring
  have hsplit : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f) := by
    rw [Work.Coercivity.wip_congr_ae hae]
    exact Work.Coercivity.wip_add_left (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      hDzLhat_int hpair_int
  -- ## nonnegativity of the energies
  have e1 : 0 ≤ Work.Coercivity.EDz f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDz_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e2 : 0 ≤ Work.Coercivity.EfEta f := by
    rw [Work.FTS.CoercivityFix.Coer1.EfEta_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e3 : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e4 : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  have hsplit' : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f) := hsplit
  rw [hsplit']
  nlinarith [hA', hpair_lb, e1, e2, e3, e4]

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.WipLhatGe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `⟨𝓛̂u, u⟩_{w²σ} ≥ -(5/2)⟨u, u⟩_{w²σ}` for the angular exponent `q ∈ [0,2]`

This file proves

  `-(5/2)·∫∫ u² w² sin(2θ)^{-q} ≤ wip (Rhoq q) (Lhat u) u`

for `u` smooth on the open quadrant and `0 ≤ q ≤ 2`, from the three joint-integrability
hypotheses `u²ρ_q`, `(D_z u)·u·ρ_q`, `(D_θ u)·u·ρ_q` (`ρ_q = Rhoq q = w²sin(2θ)^{-q}`).

## Route

Write `𝓛̂ = 𝓛 - Transport` (`Lhat_eq`).  Then

* `wip ρ_q (𝓛u) u = ½∫∫ u²ρ_q` — the self-adjointness `WipLSelf` (the `z`-integration by
  parts `wip_Dz_ibp` with `∂_z(z w²) = ((z-3)/(1+z))w²`, valid under the same three
  integrability hypotheses, the third of which is *derived* here from `u²w²σ`
  (`zw2_deriv_integrable`));
* `wip ρ_q (Transport u) u = 3·wip (Φ₁σ) (D_θu) u` with `Φ₁ = w²/(1+z)` (pointwise algebra
  plus scalar homogeneity of `wip`);
* `wip (Φ₁σ) (D_θu) u ≤ ∫∫ u²ρ_q` — the `θ`-integration by parts `wip_Dth_ibp` gives
  `(q-1)∫_z Φ₁∫_θ cos(2θ)σu²`, and `|q-1| ≤ 1`, `|cos 2θ| ≤ 1`, `Φ₁ ≤ w²` give the bound
  (`dth_Phi1_wip_le`).

Adding up: `wip ρ_q (𝓛̂u) u ≥ ½A - 3A = -(5/2)A`.

## Note on the scratch file

`_probe_wl.lean` in this directory is a scratch copy used while `R.Slots` was being
refactored; nothing imports it.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular weight `sin(2θ)^{-q}` (an abbreviation of `Coer1.sig`). -/
private abbrev sigQ (q : ℝ) : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-q)

/-- The `z`-only weight `Φ₁ = w²/(1+z)`. -/
private abbrev phiOne : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 / (1 + z)

/-- `wip` depends only on the pointwise product of its three arguments. -/
private theorem wip_int_congr {ρ₁ ρ₂ A₁ A₂ B₁ B₂ : ℝ → ℝ → ℝ}
    (h : ∀ z θ, A₁ z θ * B₁ z θ * ρ₁ z θ = A₂ z θ * B₂ z θ * ρ₂ z θ) :
    Work.Coercivity.wip ρ₁ A₁ B₁ = Work.Coercivity.wip ρ₂ A₂ B₂ := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => h z θ)

/-- `wip ρ u u` is the iterated integral of `u²ρ` (local copy of `SlotsBasic.wip_self_eq`). -/
private theorem wip_self_eq_local (ρ u : ℝ → ℝ → ℝ) :
    Work.Coercivity.wip ρ u u = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      u z θ ^ 2 * ρ z θ := by
  rw [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  ring

/-- `sin(2θ)^{-q} ≥ 0` on the closed angular interval. -/
private theorem sigQ_nonneg {q θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigQ q θ := by
  have h2 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h3 : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h2 h3) _

/-- **The core estimate** in the normalisation `ρ_q = w²·sin(2θ)^{-q}`: the pairing of
`𝓛̂u` with `u` against `ρ_q` is bounded below by `-(5/2)` times the weighted `L²` mass. -/
private theorem wip_Lhat_ge_aux {u : ℝ → ℝ → ℝ} {q : ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen u) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hZ : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    -(5 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ))
      ≤ Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (Work.FTS.CoercivityFix.Lhat u) u := by
  -- ## 0. integrability normalisations
  have hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ sigQ q θ := fun θ hθ => sigQ_nonneg hθ
  have hUsq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  have hZsq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hZ.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  have hTsq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hT.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  have hUu : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  -- ## 1. the derived `z`-weight integrability `u²·∂_z(z w²)·σ`
  have h3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2
        * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * sigQ q θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    zw2_deriv_integrable (σ := sigQ q) hσnn hUsq
  -- ## 2. integrability of the `𝓛`- and `Transport`-pairings
  have hdiv : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * sigQ q θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hUsq
  have hL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hsum : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * sigQ q θ
          + (Work.Spaces.Dz u z θ * u z θ * (Work.Spaces.w z) ^ 2 * sigQ q θ)
          - 2 * (u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * sigQ q θ / (1 + z))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (hUsq.add hZsq).sub (hdiv.const_mul 2)
    refine hsum.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Coercivity.L, Work.Spaces.Dz]
    ring
  have hTr : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hdivT : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
          * (Work.Spaces.w z) ^ 2 * sigQ q θ / (1 + z)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hTsq
    have h3m : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => 3 * (Work.Spaces.Dth u z θ * u z θ
          * (Work.Spaces.w z) ^ 2 * sigQ q θ / (1 + z))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hdivT.const_mul 3
    refine h3m.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Coercivity.Transport]
    ring
  -- ## 3. the algebraic split `𝓛̂ = 𝓛 - Transport`
  have hsplit : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
        (Work.FTS.CoercivityFix.Lhat u) u
      = Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (Work.Coercivity.L u) u
        - Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (Work.Coercivity.Transport u) u := by
    have h := Work.FTS.CoercivityFix.Coer1.wip_sub_left
      (ρ := fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
      (A := Work.Coercivity.L u) (B := Work.Coercivity.Transport u) (C := u) hL hTr
    rw [show Work.FTS.CoercivityFix.Lhat u
      = fun z θ => Work.Coercivity.L u z θ - Work.Coercivity.Transport u z θ from rfl]
    exact h
  -- ## 4. the `𝓛`-self pairing (`WipLSelf`)
  have hW : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
        (Work.Coercivity.L u) u
      = (1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ)) :=
    WipLSelf (u := u) (σ := sigQ q) hs hUsq hZsq h3
  -- ## 5. the transport term is `3` times the `Φ₁`-weighted `D_θ`-pairing
  have hTr3 : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
        (Work.Coercivity.Transport u) u
      = 3 * Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ)
          (Work.Spaces.Dth u) u := by
    have h1 : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (Work.Coercivity.Transport u) u
        = Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
            (fun z θ => 3 * (Work.Spaces.Dth u z θ / (1 + z))) u := by
      refine wip_int_congr (fun z θ => ?_)
      simp only [Work.Coercivity.Transport]
      ring
    have h2 : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (fun z θ => 3 * (Work.Spaces.Dth u z θ / (1 + z))) u
        = 3 * Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
            (fun z θ => Work.Spaces.Dth u z θ / (1 + z)) u :=
      Work.Coercivity.wip_smul_left
    have h3' : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
          (fun z θ => Work.Spaces.Dth u z θ / (1 + z)) u
        = Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ)
            (Work.Spaces.Dth u) u := by
      refine wip_int_congr (fun z θ => ?_)
      simp only [phiOne]
      ring
    rw [h1, h2, h3']
  -- ## 6. the `D_θ`-pairing bound
  have hDth : Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ)
        (Work.Spaces.Dth u) u
      ≤ Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ) u u :=
    dth_Phi1_wip_le (q := q) hs hq0 hq2 hTsq hUu
  -- ## 7. assembly
  have hkey : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
        (Work.FTS.CoercivityFix.Lhat u) u
      = (1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ))
        - 3 * Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ)
            (Work.Spaces.Dth u) u := by
    rw [hsplit, hW, hTr3]
  have hself : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * sigQ q θ) u u
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ)) :=
    wip_self_eq_local _ _
  have hle : Work.Coercivity.wip (fun z θ => phiOne z * sigQ q θ) (Work.Spaces.Dth u) u
      ≤ (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ)) := by
    rw [← hself]
    exact hDth
  rw [hkey]
  linarith [hle]

theorem WipLhatGe {u : ℝ → ℝ → ℝ} {q : ℝ} (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hZ : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    -(5 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ)
      ≤ Work.Coercivity.wip (Work.FTS.StrongPersist.H6Aux.R.Rhoq q)
          (Work.FTS.CoercivityFix.Lhat u) u := by
  have hZw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hZ.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig, sigQ]
  have hTw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hT.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig, sigQ]
  have hUw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * sigQ q θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig, sigQ]
  have hρeq : (fun z θ : ℝ => (Work.Spaces.w z) ^ 2 * sigQ q θ)
      = Work.FTS.StrongPersist.H6Aux.R.Rhoq q := by
    funext z θ
    simp only [sigQ, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
  have hAeq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * Work.FTS.StrongPersist.H6Aux.R.Rhoq q z θ)
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * sigQ q θ)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [sigQ, Work.FTS.StrongPersist.H6Aux.R.Rhoq,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
  rw [hAeq, ← hρeq]
  exact wip_Lhat_ge_aux hs hq0 hq2 hZw hTw hUw

end Work.FTS.StrongPersist.H6Aux.R
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.t3SlotHonest =====
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

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- From the a.e. trace predicate `TraceAe g`, the a.e. traces of a *single* slot `k`: this is
the form in which the per-slot estimate consumes the boundary conditions. -/
theorem traceAe_single {g : ℝ → ℝ → ℝ} (h : TraceAe g) (k : Fin 5) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) :=
  h.mono fun _ hθ => hθ k

/-
# The honest per-slot `D_z`-transport bound

This is the *honest* (open-quadrant) form of the per-slot transport bound
`Work.FTS.TransportS.T3Slot C` (proved for a positive `C` as
`Work.FTS.TransportS.t3SlotGuarded`).  It differs from `T3Slot` only in the `g`-side
hypothesis bundle: instead of the frozen

  `T3SG α g = RegQ α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`
            `= (SmoothQuad g ∧ HkMem α 4 g ∧ BdryTraces α 4 g) ∧ HkMem α 5 g ∧ DecayAll 4 g`

it asks the honest

  `SmoothOpen g ∧ HkMem α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g ∧ TraceAe g`,

where `TraceAe g` (`Submission/Work/FTS/StrongPersist/N6Trans/Hon/TraceDefs.lean`) is the
*almost-everywhere* form of the radial part of `BdryTraces α 4 g`:
`∀ᵐ θ ∂(volume.restrict Iθ), ∀ k : Fin 5, z (Thard g k z θ w z)² → 0` at `0⁺` and at `+∞`.

## Why it is provable

The proof of `t3SlotGuarded` uses `SmoothQuad g` only to obtain facts on the *open* quadrant
(`SmoothOpen g` suffices), and uses `BdryTraces α 4 g` only through exactly the hypothesis
`TraceAe` above (the `htr` argument of `slot_prod_le`).  The whole agent chain
(`TransportS.slotPairing`, `TransportS.SlotT2.canonW`, `TransportS.T3SlotAux.*`,
`TransportS.T3BadAux.slot_prod_le`) is reusable; only the `SmoothQuad`-typed lemmas need
open (`SmoothOpen`) twins: `integrable_HkIntegrand_prod`, `integrable_Xz_sq`,
`integrable_gK`, `continuousOn_Xz_Qd`, `continuousOn_Yz_Qd`, `continuousOn_gK_Qd`,
`continuousOn_gK'_Qd`, `continuousOn_mixed_Qd`, and `slot_slice_le_ae` / `slot_prod_le`
with the a.e. trace hypothesis `∀ᵐ θ, …,` in place of `∀ θ ∈ Ioo 0 (π/2), …`
(in `slot_slice_le_ae` the a.e. hypothesis is simply added to the `filter_upwards` list
that already contains `ae_mem_Ioo_Iθ`, `h4`, `h5`, `hX2`).

## Consumers

`Work.FTS.StrongPersist.N6Trans.IP4T3Honest` (the node this serves) combines this per-slot
bound with `Work.FTS.TransportS.ip4SlotDomFixed` (the slot domination of the concrete
`IP4`) exactly as `Work.FTS.TransportS.T3Clause_of_slot` does, to get the honest `t3`
clause for `Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1`.
-/
theorem t3SlotHonest : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.TransportS.T3SF α f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
      Work.FTS.StrongPersist.N6Trans.Hon.TraceAe g →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 4 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
          ≤ C * α ^ (-(1 / 2 : ℝ))
              * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
              * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  obtain ⟨C_f, hC_f_pos, hC_f⟩ := Work.FTS.H2.OpenPort.coefTh3_mixed_gain
  refine ⟨6402 * (101 + C_f), by positivity, ?_⟩
  intro α f g hα hα1 hF hsg hm4 hm5 hdec htrAe a b ρ hab hleaf
  obtain ⟨hsf, hwf, hcf⟩ := hF
  -- ## the constant `Mf = 100|f|_{𝒲^{4,∞}} + C_f CoefTh 3 f`
  set Mf : ℝ := 100 * Work.Spaces.WlInf α 4 f + C_f * Work.FTS.VocabO.CoefTh 3 f with hMfdef
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hwf
  have hCnn : 0 ≤ Work.FTS.VocabO.CoefTh 3 f := Work.FTS.TransportS.coefTh_nonneg 3 f
  have hMf : 0 ≤ Mf := by rw [hMfdef]; positivity
  have hMfC : C_f * Work.FTS.VocabO.CoefTh 3 f ≤ Mf := by rw [hMfdef]; linarith
  have hMfW : 100 * Work.Spaces.WlInf α 4 f ≤ Mf := by
    rw [hMfdef]; linarith [mul_nonneg hC_f_pos.le hCnn]
  have hMfW' : Work.Spaces.WlInf α 4 f ≤ Mf := by linarith [hMfW, hWnn]
  -- ## the pointwise bounds on the coefficient `f`
  have hDzb : ∀ b1 : ℕ, 1 ≤ b1 → b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter b1 f z θ| ≤ Mf := by
    intro b1 _ hb4 z θ hz hθ0 hθ1
    exact (Work.FTS.TransportS.T3SlotAux.dzIter_le_WlInf_open hsf hwf hb4 hz
      ⟨hθ0, hθ1⟩).trans hMfW
  have hFmix : ∀ a1 b1 : ℕ, 1 ≤ a1 → a1 + b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |Work.Spaces.mixed b1 a1 f z θ| ≤ C_f * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f :=
    fun a1 b1 ha1 hab' z θ hz hθ0 hθ1 => hC_f f hsf hcf a1 b1 ha1 hab' z θ hz hθ0 hθ1
  have hfbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf := by
    intro z hz θ hθ
    have h := Work.Spaces.zpz_le_WlInf (α := α) hwf (j := 0) (by norm_num) hz hθ
    simpa using h.trans hMfW'
  have hDzbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf := by
    intro z hz θ hθ
    have h := Work.Spaces.zpz_le_WlInf (α := α) hwf (j := 1) (by norm_num) hz hθ
    simpa [Work.Spaces.Dz] using h.trans hMfW'
  -- ## the leaf weight data: the exponent `q`, its domination, and continuity
  have hdata : ∃ q : ℝ, 0 ≤ q ∧ q ≤ Work.FTS.TransportS.T3SlotAux.qOf α a ∧
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        ρ z θ = Work.FTS.TransportS.SlotT2.canonW q z θ) ∧
      ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.LocData.Qd := by
    rcases hleaf with h | h | ⟨ha1, h⟩
    · subst h
      refine ⟨Work.Spaces.eta, le_of_lt Work.Spaces.eta_pos, ?_, ?_, ?_⟩
      · rcases eq_or_ne a 0 with ha0 | ha
        · rw [ha0, Work.FTS.TransportS.T3SlotAux.qOf_zero]
        · rw [Work.FTS.TransportS.T3SlotAux.qOf_of_ne ha, Work.Spaces.gam, Work.Spaces.eta]
          linarith
      · intro z θ _ _ _
        rfl
      · refine (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul
          (Work.FTS.TransportS.continuousOn_sinpow_Qd (-(Work.Spaces.eta)))).congr ?_
        intro p _
        simp only [Pi.mul_apply, Work.FTS.TransportS.leafEta]
    · subst h
      refine ⟨0, le_refl 0, le_of_lt (Work.FTS.TransportS.T3SlotAux.qOf_pos α hα a), ?_, ?_⟩
      · intro z θ _ _ _
        rw [Work.FTS.TransportS.SlotT2.canonW, neg_zero, Real.rpow_zero, mul_one]
        rfl
      · simpa [Work.FTS.TransportS.leafOne] using Work.FTS.TransportS.continuousOn_w_sq_Qd
    · subst h
      refine ⟨Work.Spaces.gam α, le_of_lt (Work.Spaces.gam_pos hα), ?_, ?_, ?_⟩
      · rw [Work.FTS.TransportS.T3SlotAux.qOf_of_ne (by omega : a ≠ 0)]
      · intro z θ _ _ _
        rfl
      · refine (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul
          (Work.FTS.TransportS.continuousOn_sinpow_Qd (-(Work.Spaces.gam α)))).congr ?_
        intro p _
        simp only [Pi.mul_apply, Work.FTS.TransportS.leafGam]
  obtain ⟨q, hq0, hqle, hρeq, hρcont⟩ := hdata
  have hρle : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ := by
    intro z θ hz hθ0 hθ1
    rw [hρeq z θ hz hθ0 hθ1]
    exact Work.FTS.TransportS.T3SlotAux.canonW_le_of_le hqle ⟨hθ0, hθ1⟩
  have hρnonneg : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ :=
    fun z θ hθ => Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z hθ
  -- ## the boundary traces of each top slot
  have htr : ∀ k : Fin 5, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) :=
    fun k => traceAe_single htrAe k
  -- ## the abbreviation `X = f · D_z g`
  set X : ℝ → ℝ → ℝ := fun z θ => f z θ * Work.Spaces.Dz g z θ with hX
  -- ## the pointwise bound on the exceptional-free remainder
  have hrempt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρ z θ * (Work.Spaces.mixed b a X z θ
          - f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ)
        * Work.Spaces.mixed b a g z θ|
        ≤ 6400 * Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z θ hz hθ0 hθ1
    rw [hX]
    exact Work.FTS.TransportS.T3SlotAux.remainder_pointwise (α := α) (Mf := Mf) (C_f := C_f)
      (f := f) (g := g) (a := a) (b := b) (ρ := ρ) hα hα1 hMf hsf hsg hleaf hab hDzb hFmix
      hMfC z θ hz hθ0 hθ1
  -- ## the exceptional term: integrability and bound
  have hflux : Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
        ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
    by_cases h4 : a + b = 4
    · -- the exceptional (order-five) slot: radial integration by parts
      let k : Fin 5 := ⟨a, by omega⟩
      have hk : k.val = a := rfl
      refine ⟨?_, ?_⟩
      · refine flux_integrable_open (α := α) (Mf := Mf) (q := q)
          (r := Work.FTS.TransportS.T3SlotAux.qOf α a - q) (f := f) (g := g) (a := a) (b := b)
          (ρ := ρ) (k := k) hMf hsf hsg hm5 hk h4 rfl hqle hρeq ?_
        intro z θ hz hθ0 hθ1
        exact (hfbound z (le_of_lt hz) θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩)
      · exact flux_bound_open (α := α) (Mf := Mf) (q := q) (f := f)
          (g := g) (a := a) (b := b) (ρ := ρ) (k := k) hMf hsf hsg hm4 hm5 hk h4 hqle hρeq
          hfbound hDzbound (htr k)
    · -- the slot has order `≤ 3`: the exceptional term is an ordinary `ℋ⁴`-slot
      have hab3 : a + b ≤ 3 := by omega
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |ρ z θ * f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
              * Work.Spaces.mixed b a g z θ| ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
        intro z θ hz hθ0 hθ1
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
        have hρz : ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ :=
          hρle z θ hz hθ0 hθ1
        have hDz : Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
            = Work.Spaces.mixed (b + 1) a g z θ := rfl
        have hpair := Work.FTS.TransportS.T3SlotAux.canonW_pair_le (α := α) (g := g)
          (q := Work.FTS.TransportS.T3SlotAux.qOf α a)
          (Work.FTS.TransportS.T3SlotAux.qOf_pos α hα a)
          (Work.FTS.TransportS.T3SlotAux.qOf_le_gam α hα a)
          (j := b + 1) (i := a) (b := b) (a := a)
          (fun h => by rw [h, Work.FTS.TransportS.T3SlotAux.qOf_zero])
          (fun h => by rw [h, Work.FTS.TransportS.T3SlotAux.qOf_zero])
          (by omega) hab (le_of_lt hz) hθI
        have hXnn : 0 ≤ |Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ| :=
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have hρf : ρ z θ * |f z θ| ≤ Mf
            * Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ := by
          calc ρ z θ * |f z θ|
              ≤ Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ * Mf :=
                mul_le_mul hρz (hfbound z (le_of_lt hz) θ hθI) (abs_nonneg _)
                  (Work.FTS.TransportS.SlotT2.canonW_nonneg hθI)
            _ = Mf * Work.FTS.TransportS.SlotT2.canonW
                  (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ := by ring
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hρnonneg z θ hθI), hDz]
        calc (ρ z θ * |f z θ|) * |Work.Spaces.mixed (b + 1) a g z θ|
              * |Work.Spaces.mixed b a g z θ|
            = (ρ z θ * |f z θ|) * (|Work.Spaces.mixed (b + 1) a g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by ring
          _ ≤ (Mf * Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ)
                * (|Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|) :=
              mul_le_mul_of_nonneg_right hρf hXnn
          _ = Mf * (Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
                * (|Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|)) := by ring
          _ ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
              refine mul_le_mul_of_nonneg_left ?_ hMf
              rw [← mul_assoc]
              exact hpair
      have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
        refine ((hρcont.mul hsf.continuousOn).mul
          ((hsg.mixed b a).Dz.continuousOn)).mul ((hsg.mixed b a).continuousOn)
      have hint : Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        refine Integrable.mono'
          (((integrable_HkIntegrand_prod_open hsg hm4).1).const_mul Mf) haesm ?_
        filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
          |ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2| ≤ Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2)
          (fun z θ hz hθ hθ' => hpt z θ hz hθ hθ')] with p hp
        simpa [Real.norm_eq_abs] using hp
      refine ⟨hint, ?_⟩
      calc |∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
          ≤ ∫ p, |ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2|
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
            abs_integral_le_integral_abs
        _ ≤ ∫ p, Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
            integral_mono_ae hint.abs
              (((integrable_HkIntegrand_prod_open hsg hm4).1).const_mul Mf)
              (Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ hθ' => hpt z θ hz hθ hθ')
        _ = Mf * Work.Spaces.HkSq α 4 g := by
            rw [MeasureTheory.integral_const_mul,
              (integrable_HkIntegrand_prod_open hsg hm4).2]
        _ ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
            have := Work.Spaces.HkSq_nonneg α 4 g
            nlinarith [hMf]
  -- ## integrability of the remainder
  have hremaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
      * (Work.Spaces.mixed b a X p.1 p.2
        - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
      * Work.Spaces.mixed b a g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hmul : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
      hsf.mul hsg.Dz
    rw [hX]
    refine (hρcont.mul ((hmul.mixed b a).continuousOn.sub
      (hsf.continuousOn.mul ((hsg.mixed b a).Dz.continuousOn)))).mul
      ((hsg.mixed b a).continuousOn)
  have hremint : Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * (Work.Spaces.mixed b a X p.1 p.2
        - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
      * Work.Spaces.mixed b a g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine Integrable.mono'
      (((integrable_HkIntegrand_prod_open hsg hm4).1).const_mul (6400 * Mf))
      hremaesm ?_
    filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
      |ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
          - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
        * Work.Spaces.mixed b a g p.1 p.2| ≤ 6400 * Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      (fun z θ hz hθ hθ' => hrempt z θ hz hθ hθ')] with p hp
    simpa [Real.norm_eq_abs] using hp
  have hrembound : |∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
        - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
        * Work.Spaces.mixed b a g p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
      ≤ 6400 * Mf * Work.Spaces.HkSq α 4 g := by
    calc |∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
            - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
            * Work.Spaces.mixed b a g p.1 p.2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
        ≤ ∫ p, |ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
              - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
            * Work.Spaces.mixed b a g p.1 p.2|
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ p, 6400 * Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          integral_mono_ae hremint.abs
            (((integrable_HkIntegrand_prod_open hsg hm4).1).const_mul (6400 * Mf))
            (Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ hθ' => hrempt z θ hz hθ hθ')
      _ = 6400 * Mf * Work.Spaces.HkSq α 4 g := by
          rw [MeasureTheory.integral_const_mul,
            (integrable_HkIntegrand_prod_open hsg hm4).2]
  -- ## the product-measure form of the pairing
  have hsplit_ae : (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b a X p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
      =ᵐ[(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)]
        ((fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2)
          + fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
            - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
            * Work.Spaces.mixed b a g p.1 p.2) :=
    Filter.Eventually.of_forall fun p => by
      simp only [Pi.add_apply]
      ring
  have hXYint : Integrable (Function.uncurry (fun z θ : ℝ => ρ z θ
        * Work.Spaces.mixed b a X z θ * Work.Spaces.mixed b a g z θ))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hflux.1.add hremint).congr hsplit_ae.symm
  have hident : Work.FTS.TransportS.slotPairing ρ a b X g
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a X p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.TransportS.slotPairing]
    exact MeasureTheory.integral_integral
      (f := fun z θ : ℝ => ρ z θ * Work.Spaces.mixed b a X z θ
        * Work.Spaces.mixed b a g z θ) hXYint
  have hsplit : (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a X p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = (∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        + (∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
              - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
            * Work.Spaces.mixed b a g p.1 p.2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
    (MeasureTheory.integral_congr_ae hsplit_ae).trans
      (MeasureTheory.integral_add hflux.1 hremint)
  have hfin : |Work.FTS.TransportS.slotPairing ρ a b X g| ≤ 6402 * Mf * Work.Spaces.HkSq α 4 g := by
    rw [hident, hsplit]
    calc |(∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
          + (∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
                - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))|
        ≤ |(∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))|
          + |(∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
                - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))| := abs_add_le _ _
      _ ≤ 2 * Mf * Work.Spaces.HkSq α 4 g + 6400 * Mf * Work.Spaces.HkSq α 4 g :=
          add_le_add hflux.2 hrembound
      _ = 6402 * Mf * Work.Spaces.HkSq α 4 g := by ring
  -- ## the arithmetic
  have hMfle : Mf ≤ (101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f) := by
    rw [hMfdef]; nlinarith [hWnn, hCnn, hC_f_pos.le]
  have hαpow : 1 ≤ α ^ (-(1 / 2 : ℝ)) := by
    have hpos : 0 < α ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hα _
    have hle : α ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    have hneg : α ^ (-(1 / 2 : ℝ)) = (α ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hα.le (1 / 2)
    rw [hneg]
    exact (one_le_inv₀ hpos).mpr hle
  rw [hX]
  refine hfin.trans ?_
  have hHk : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Work.FTS.H2.HkNorm_sq α g).symm
  rw [hHk]
  calc 6402 * Mf * (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMfle (by norm_num))
          (sq_nonneg _)
    _ ≤ 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
          * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
        have h0 : 0 ≤ 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f
            + Work.FTS.VocabO.CoefTh 3 f)) := by positivity
        calc 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
              * (Work.FTS.Nonlin.Xn α g) ^ 2
            = (6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f
                + Work.FTS.VocabO.CoefTh 3 f)) * 1)
              * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
          _ ≤ (6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
                * α ^ (-(1 / 2 : ℝ))) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαpow h0) (sq_nonneg _)
          _ = 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
                * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    _ = 6402 * (101 + C_f) * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Cont =====
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
set_option maxHeartbeats 4000000

/-! ## Continuity of the slot data on the open quadrant -/

theorem continuousOn_t1W (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => t1W q p.1 p.2) Work.FTS.H2.Qd := by
  show ContinuousOn (fun p : ℝ × ℝ =>
    (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)) Work.FTS.H2.Qd
  exact (Work.FTS.H2.continuousOn_w_Qd.pow 2).mul
    (Work.FTS.H2.continuousOn_sin_rpow_Qd (-q))

theorem continuousOn_t1Leib {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => t1Leib f g a b p.1 p.2) Work.FTS.H2.Qd := by
  show ContinuousOn (fun p : ℝ × ℝ => ∑ a1 ∈ Finset.range (a + 1),
      ∑ b1 ∈ Finset.range (b + 1), (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * (Work.Spaces.mixed b1 a1 f p.1 p.2
             * Work.Spaces.mixed (b - b1) (a - a1 + 1) g p.1 p.2))) Work.FTS.H2.Qd
  refine continuousOn_finset_sum (Finset.range (a + 1))
    (fun a1 _ => continuousOn_finset_sum (Finset.range (b + 1)) (fun b1 _ => ?_))
  by_cases h : a1 = 0 ∧ b1 = 0
  · simpa only [if_pos h] using continuousOn_const (c := (0 : ℝ)) (s := Work.FTS.H2.Qd)
  · simp only [if_neg h]
    exact continuousOn_const.mul (((hf.mixed b1 a1).continuousOn).mul
      ((hg.mixed (b - b1) (a - a1 + 1)).continuousOn))

theorem continuousOn_t1Easy {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => t1Easy q f g a b p.1 p.2) Work.FTS.H2.Qd := by
  show ContinuousOn (fun p : ℝ × ℝ => t1W q p.1 p.2 * t1Leib f g a b p.1 p.2
    * Work.Spaces.mixed b a g p.1 p.2) Work.FTS.H2.Qd
  exact ((continuousOn_t1W q).mul (continuousOn_t1Leib hf hg a b)).mul
    ((hg.mixed b a).continuousOn)

theorem continuousOn_t1EasyAbs {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => t1EasyAbs q f g a b p.1 p.2) Work.FTS.H2.Qd := by
  show ContinuousOn (fun p : ℝ × ℝ => |t1W q p.1 p.2| * (∑ a1 ∈ Finset.range (a + 1),
      ∑ b1 ∈ Finset.range (b + 1), (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * (Work.Spaces.mixed b1 a1 f p.1 p.2
             * Work.Spaces.mixed (b - b1) (a - a1 + 1) g p.1 p.2)|))
      * |Work.Spaces.mixed b a g p.1 p.2|) Work.FTS.H2.Qd
  refine (((continuousOn_t1W q).abs).mul ?_).mul ((hg.mixed b a).continuousOn).abs
  refine continuousOn_finset_sum (Finset.range (a + 1))
    (fun a1 _ => continuousOn_finset_sum (Finset.range (b + 1)) (fun b1 _ => ?_))
  by_cases h : a1 = 0 ∧ b1 = 0
  · simpa only [if_pos h] using continuousOn_const (c := (0 : ℝ)) (s := Work.FTS.H2.Qd)
  · simp only [if_neg h]
    exact (continuousOn_const.mul (((hf.mixed b1 a1).continuousOn).mul
      ((hg.mixed (b - b1) (a - a1 + 1)).continuousOn))).abs

/-- Almost every point of the product measure `pm` lies in the open quadrant. -/
theorem ae_pm_mem_Qd_T1Hon : ∀ᵐ p ∂Work.FTS.H2.pm, p ∈ Work.FTS.H2.Qd := by
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) =ᵐ[volume.prod volume] Work.FTS.H2.Qd :=
    MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have h1 : Work.FTS.H2.pm
      = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [Work.FTS.H2.pm, MeasureTheory.Measure.prod_restrict]
  rw [h1, MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_mem Work.FTS.H2.isOpen_Qd.measurableSet


/-- The slot easy majorant `slotEasySum` is continuous on the open quadrant. -/
theorem continuousOn_slotEasySum (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => slotEasySum α f g a b p.1 p.2) Work.FTS.H2.Qd := by
  have hW : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.slotW α a p.1 p.2)
      Work.FTS.H2.Qd := by
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      have hfun : (fun p : ℝ × ℝ => Work.FTS.TransportS.slotW α 0 p.1 p.2)
          = fun p : ℝ × ℝ => (Work.FTS.H2.Whz p.1 p.2) ^ 2 := by
        funext p
        simp only [Work.FTS.TransportS.slotW_zero]
      have hfun2 : ((fun p : ℝ × ℝ => Work.FTS.H2.Whz p.1 p.2) ^ 2)
          = fun p : ℝ × ℝ => (Work.FTS.H2.Whz p.1 p.2) ^ 2 := by
        funext p; simp only [Pi.pow_apply]
      rw [hfun, ← hfun2]
      exact Work.FTS.H2.continuousOn_Whz_Qd.pow 2
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
      have hfun : (fun p : ℝ × ℝ => Work.FTS.TransportS.slotW α a p.1 p.2)
          = fun p : ℝ × ℝ => (Work.FTS.H2.Wm α p.1 p.2) ^ 2 := by
        funext p
        simp only [Work.FTS.TransportS.slotW_of_pos' α ha1]
      have hfun2 : ((fun p : ℝ × ℝ => Work.FTS.H2.Wm α p.1 p.2) ^ 2)
          = fun p : ℝ × ℝ => (Work.FTS.H2.Wm α p.1 p.2) ^ 2 := by
        funext p; simp only [Pi.pow_apply]
      rw [hfun, ← hfun2]
      exact (Work.FTS.H2.continuousOn_Wm_Qd α).pow 2
  show ContinuousOn (fun p : ℝ × ℝ => ∑ a1 ∈ Finset.range (a + 1),
      ∑ b1 ∈ Finset.range (b + 1), (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        Work.FTS.TransportS.slotW α a p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g p.1 p.2|
          * |Work.Spaces.mixed b a g p.1 p.2|)) Work.FTS.H2.Qd
  refine continuousOn_finset_sum (Finset.range (a + 1))
    (fun a1 _ => continuousOn_finset_sum (Finset.range (b + 1)) (fun b1 _ => ?_))
  by_cases h : a1 = 0 ∧ b1 = 0
  · simpa only [if_pos h] using continuousOn_const (c := (0 : ℝ)) (s := Work.FTS.H2.Qd)
  · simp only [if_neg h]
    exact (((hW.mul ((hf.mixed b1 a1).continuousOn).abs).mul
      ((hg.mixed (b - b1) (a - a1 + 1)).continuousOn).abs).mul
      ((hg.mixed b a).continuousOn).abs)

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.srestBound =====
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
set_option maxHeartbeats 2000000

open Work.FTS.TransportS.SlotT2

/-! ## Continuity of the remainder on the open quadrant -/

/-- Each summand of `Srest` (a product of two mixed derivatives of `f` resp. `g` with a
binomial coefficient) is continuous on the open quadrant when `f` and `g` are. -/
theorem continuousOn_uncurry_Srest {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) :
    ContinuousOn (Function.uncurry (Srest f g a b))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hmain : ContinuousOn (fun p : ℝ × ℝ => Srest f g a b p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    simp only [Srest]
    refine continuousOn_finsetSum _ (fun a1 _ => continuousOn_finsetSum _ (fun b1 _ => ?_))
    split_ifs with h
    · exact continuousOn_const
    · exact continuousOn_const.mul
        (((hf.mixed b1 a1).continuousOn).mul
          ((hg.mixed (b + 1 - b1) (a - a1)).continuousOn))
  exact hmain

/-! ## The abstract domination argument -/

/-- **The `Srest` estimate.**  Given a pointwise majorant of the shape `6400 · Maj1` for the
`Srest`-pairing on the open quadrant, the a.e. strong measurability of the pairing (supplied
here by continuity on the open quadrant), and the `ℋ⁴`-membership of `f` and `g`, the angular
marginal is integrable and its iterated integral is at most

  `6400 · ((Mf + MK) · HkSq α 4 g + Mg · (HkNorm α 4 f · HkNorm α 4 g))`.

The bound is `∫_z (∫_θ |…|) ≤ ∫_z 6400 · ((Mf + MK) · ∫_θ HkIntegrand g + Mg · √Ff · √Gg)`,
with the angular Cauchy–Schwarz `∫_θ √(HkIntegrand f) √(HkIntegrand g) ≤ √Ff · √Gg` and the
radial Cauchy–Schwarz `∫_z √Ff · √Gg ≤ |f|_{ℋ⁴} |g|_{ℋ⁴}`. -/
theorem srest_aux {α : ℝ}
    {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g)
    (hcont : ContinuousOn (Function.uncurry (fun z θ =>
      Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ| ≤ 6400 * Maj1 α f g Mf MK Mg z θ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ 6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
            + Mg * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the two slot energies and their integrability
  have hFf_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      Work.Spaces.Iz := hmf.2
  have hGg_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      Work.Spaces.Iz := hmg.2
  have hFf_nn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
  have hGg_nn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  have hCS_int : MeasureTheory.IntegrableOn
      (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      Work.Spaces.Iz :=
    integrable_sqrt_mul_sqrt_slice hFf_int hGg_int hFf_nn hGg_nn
  have hLim_int : MeasureTheory.IntegrableOn
      (fun z => 6400 * ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))))
      Work.Spaces.Iz :=
    ((hGg_int.const_mul (Mf + MK)).add (hCS_int.const_mul Mg)).const_mul 6400
  -- the angular slice of the majorant is integrable, for every `z ∈ Iz`
  have hMaj_slice_int : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.Integrable (fun θ => Maj1 α f g Mf MK Mg z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have h1 : MeasureTheory.Integrable
        (fun θ => (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (hmg.1 z hz).const_mul _
    have h2 : MeasureTheory.Integrable
        (fun θ => Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (integrable_sqrt_mul_sqrt_slice (A := fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        (B := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (hmf.1 z hz) (hmg.1 z hz)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).const_mul Mg
    refine (h1.add h2).congr ?_
    filter_upwards with θ
    simp only [Pi.add_apply, Maj1]
  -- the angular slice bound `∫ |·| ≤ 6400 ∫ Maj1`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|)
        ≤ 6400 * ∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have hzero : (fun θ : ℝ =>
          |Work.FTS.TransportS.SlotT2.canonW q 0 θ * Srest f g a b 0 θ
            * Work.Spaces.mixed b a g 0 θ|) = fun _ => (0 : ℝ) := by
        funext θ
        rw [Work.FTS.TransportS.SlotT2.canonW_zero_z, zero_mul, zero_mul, abs_zero]
      rw [hzero, MeasureTheory.integral_zero]
      exact mul_nonneg (by norm_num)
        (MeasureTheory.setIntegral_nonneg hIθm
          (fun θ _ => Maj1_nonneg (by linarith [hMf, hMK]) hMg 0 θ))
    · rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|)
        (g := fun θ => 6400 * Maj1 α f g Mf MK Mg z θ) ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun θ => abs_nonneg _)
      · exact (hMaj_slice_int z hz).const_mul 6400
      · exact ae_of_forall_Ioo (fun θ hθ => hpt z θ hz0 hθ.1 hθ.2)
  -- the angular slice of `Maj1` is bounded by the explicit radial majorant
  have hMaj_le : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
        ≤ (Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    intro z hz
    have h1 : MeasureTheory.Integrable
        (fun θ => (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (hmg.1 z hz).const_mul _
    have h2 : MeasureTheory.Integrable
        (fun θ => Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (integrable_sqrt_mul_sqrt_slice (A := fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        (B := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (hmf.1 z hz) (hmg.1 z hz)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).const_mul Mg
    have hsplit : (∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
        = (Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
      simp only [Maj1]
      rw [MeasureTheory.integral_add h1 h2, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    have hcs := cs_sqrt_le (s := Work.Spaces.Iθ)
      (A := fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
      (B := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      (hmf.1 z hz) (hmg.1 z hz)
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
    rw [hsplit]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hcs hMg)
      ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
  -- the slice bound in the form used by the radial domination
  have hslice2 : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|)
        ≤ 6400 * ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := by
    intro z hz
    exact le_trans (hslice z hz)
      (mul_le_mul_of_nonneg_left (hMaj_le z hz) (by norm_num))
  -- the marginal bound
  have hmarg : ∀ z ∈ Work.Spaces.Iz,
      ‖∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ‖
        ≤ 6400 * ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := by
    intro z hz
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ)) ?_
    simpa only [Real.norm_eq_abs] using hslice2 z hz
  -- a.e. strong measurability of the marginal
  have hInner_aesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * Srest f g a b z θ * Work.Spaces.mixed b a g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * Srest f g a b p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) hcont).integral_prod_right'
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa [Function.uncurry] using h
  -- the integrability of the marginal
  have hInner_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * Srest f g a b z θ * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz :=
    MeasureTheory.Integrable.mono' hLim_int hInner_aesm
      (MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => hmarg z hz))
  refine ⟨hInner_int, ?_⟩
  -- the two exact identities for the majorant integral
  have hGgEq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ) = Work.Spaces.HkSq α 4 g := rfl
  have hCSeq : (∫ z in Work.Spaces.Iz,
        Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
    have h := cs_sqrt_le (s := Work.Spaces.Iz)
      (A := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (B := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      hFf_int hGg_int hFf_nn hGg_nn
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    simpa only [Work.Spaces.HkSq] using h
  have hCompute : (∫ z in Work.Spaces.Iz,
        6400 * ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))))
      ≤ 6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
          + Mg * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)) := by
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add (hGg_int.const_mul (Mf + MK)) (hCS_int.const_mul Mg)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (le_of_eq (by rw [hGgEq])) (mul_le_mul_of_nonneg_left hCSeq hMg))
      (by norm_num)
  have hstep1 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ| ≤
      ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * Srest f g a b z θ * Work.Spaces.mixed b a g z θ)
    simpa only [Real.norm_eq_abs] using h
  have hstep2 : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ|) ≤
      ∫ z in Work.Spaces.Iz, 6400 * ((Mf + MK) *
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => abs_nonneg _)) hLim_int
      (MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => by
        simpa only [Real.norm_eq_abs] using hmarg z hz))
  exact le_trans hstep1 (le_trans hstep2 hCompute)

/-! ## The requested statement -/

theorem srestBound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg) (hqnn : 0 ≤ q)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f) (hGsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hqcase : q ≤ Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    (hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf)
    (hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ))
    (hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Work.FTS.TransportS.T2Sup.Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * Work.FTS.TransportS.T2Sup.Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ 6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
            + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)) := by
  have hcont : ContinuousOn (Function.uncurry (fun z θ =>
      Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    ((continuousOn_canonW q).mul (continuousOn_uncurry_Srest hFsm hGsm a b)).mul
      ((hGsm.mixed b a).continuousOn)
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ| ≤ 6400 * Maj1 α f g Mf MK Mg z θ := by
    intro z θ hz hθ hθ2
    have h := canonW_mul_Srest_le (α := α) hα hα1 (f := f) (g := g) (a := a) (b := b)
      (q := q) (Mf := Mf) (MK := MK) (Mg := Mg) hMf hMK hMg hqnn hab hq0 hqγ hqcase
      hFsup hFσ hGsup z θ hz hθ hθ2
    calc |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ|
        = Work.FTS.TransportS.SlotT2.canonW q z θ * |Srest f g a b z θ|
            * |Work.Spaces.mixed b a g z θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)]
      _ ≤ 6400 * Maj1 α f g Mf MK Mg z θ := h
  exact srest_aux hMf hMK hMg hmf hmg hcont hpt

end Work.FTS.TransportS.T2Sup
end
end
