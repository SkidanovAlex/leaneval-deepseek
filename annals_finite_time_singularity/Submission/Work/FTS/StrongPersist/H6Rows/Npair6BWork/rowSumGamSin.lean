import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssembly
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gRad
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharp_LGammaT_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `𝓛_Γ^T g − 𝓛_Γ^T g' = 𝓛_Γ^T (g − g')`, sharply

The linear part `𝓛_Γ^T` of the dynamic right-hand side of the Galerkin chapter is a **linear**
operator in the profile: on the open quadrant `(0,∞) × (0,π/2)`,

  `𝓛_Γ^T g − 𝓛_Γ^T g' = 𝓛_Γ^T (g − g')`      (`sharp_LGammaT_diff_eqOn`).

Everything in `𝓛_Γ^T` is transparently additive — the `𝓛`-part (`deriv`-linear on the open
quadrant, `SmoothOpen.DzIter_sub_open`) and the transport part — except the two *nonlocal*
`L₁₂`-terms, whose additivity needs the integrability of the angular slices **and** of the
`L₁₂`-densities of both summands (they are integrals over the unbounded region `(z,∞)`):

* the `z`-slot `L₁₂(f)(z)` is additive by `L12f_eq_sub_add`, with the integrability supplied by
  `SmoothOpen` + `HkMem α 4` (`GalBasis.cc.integrableOn_{slice,L12dens}_of_SmoothOpen_HkMem`);
* the projector slot `L₁₂(Transport f)(0)` — `Transport f = 3 sin(2θ)∂_θf/(1+z)` — needs the
  same integrability facts for the *transport* profile, which is `Transport_L12_integrable`;
  the pointwise comparison of `Transport f − Transport f'` with `Transport (f − f')` on the open
  quadrant then finishes with `L12f_congr_of_agreeOnQ`.

With the identity in hand, the sharp difference estimate reduces to the single profile bound
`Norm.Xn_LGammaT_le` applied to the difference `h`: the `SmoothOpen` and `HkMem` clauses
transport along the open-quadrant identity (`NonlinRows.smoothOpen_sub`, `HkMem_congr_Q0`), and
the norm clause through `HkSq_congr_open`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.GalFields.RHS

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The `L₁₂`-slot of the transport term -/

/-- **Additivity of the projector slot** `L₁₂(Transport ·)(0)`: for two `SmoothOpen` profiles
with `HkMem α 4`, the transport-`L₁₂`-difference is the transport-`L₁₂` of the difference. -/
theorem sharp_L12f_Transport_eq_sub_add {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f f' : Fn}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) (hSf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f') :
    Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport (fun z θ => f z θ - f' z θ)) 0
        + Work.Coercivity.L12f (Work.Coercivity.Transport f') 0 := by
  obtain ⟨hs1, hd1⟩ := Transport_L12_integrable hα hα1 hSf hmf
  obtain ⟨hs2, hd2⟩ := Transport_L12_integrable hα hα1 hSf' hmf'
  have h1 := L12f_eq_sub_add (a := Work.Coercivity.Transport f)
    (b := Work.Coercivity.Transport f') hs1 hs2 hd1 hd2
  have hcg : Work.Coercivity.L12f
        (fun z θ => Work.Coercivity.Transport f z θ - Work.Coercivity.Transport f' z θ) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport (fun z θ => f z θ - f' z θ)) 0 := by
    refine L12f_congr_of_agreeOnQ (le_refl 0) ?_
    intro z θ hz hθ0 hθ1
    have h := Work.FTS.EllipticEst.TTSlot11Aux.DthIter_sub_open hSf hSf' 1 z θ hz hθ0 hθ1
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] at h
    simp only [Work.Coercivity.Transport]
    rw [h]
    ring
  rw [hcg] at h1
  exact h1

/-! ## The identity on the open quadrant -/

/-- **`𝓛_Γ^T` is linear on the open quadrant**: for `SmoothOpen` profiles in `ℋ⁴_α`,
`𝓛_Γ^T f − 𝓛_Γ^T f'` agrees with `𝓛_Γ^T(f − f')` at every interior point of the quadrant.

The three components are additive there: `𝓛` and `Transport` through the `deriv`-linearity of
the iterated operators (`SmoothOpen.DzIter_sub_open`, `SmoothOpen.DthIter_sub_open`), and the
two `L₁₂`-slots through `L12f_eq_sub_add` (integrability from `SmoothOpen` + `HkMem α 4`) and
`sharp_L12f_Transport_eq_sub_add`. -/
theorem sharp_LGammaT_diff_eqOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f f' : Fn}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) (hSf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f') :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Coercivity.LGammaT α f z θ - Work.Coercivity.LGammaT α f' z θ
        = Work.Coercivity.LGammaT α (fun z θ => f z θ - f' z θ) z θ := by
  intro z θ hz hθ0 hθ1
  -- the two `D`-operators are subtractive on the open quadrant
  have hDz : Work.Spaces.Dz f z θ
      = Work.Spaces.Dz (fun z θ => f z θ - f' z θ) z θ + Work.Spaces.Dz f' z θ := by
    have h := Work.FTS.EllipticEst.TTSlot11Aux.DzIter_sub_open hSf hSf' 1 z θ hz hθ0 hθ1
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] at h
    linarith
  have hDth : Work.Spaces.Dth f z θ
      = Work.Spaces.Dth (fun z θ => f z θ - f' z θ) z θ + Work.Spaces.Dth f' z θ := by
    have h := Work.FTS.EllipticEst.TTSlot11Aux.DthIter_sub_open hSf hSf' 1 z θ hz hθ0 hθ1
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] at h
    linarith
  -- hence for the transport term as well
  have hT : Work.Coercivity.Transport f z θ
      = Work.Coercivity.Transport (fun z θ => f z θ - f' z θ) z θ
        + Work.Coercivity.Transport f' z θ := by
    simp only [Work.Coercivity.Transport]
    rw [hDth]
    ring
  -- the integrability inputs of the `z`-slot at the base point `z`
  have hDa : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ := by
    intro s hs
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hSf hmf
      (lt_trans hz (Set.mem_Ioi.mp hs))
  have hDb : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f' s θ / s) Work.Spaces.Iθ := by
    intro s hs
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hSf' hmf'
      (lt_trans hz (Set.mem_Ioi.mp hs))
  have hDca : MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hSf hmf).mono_set
      (Set.Ioi_subset_Ioi hz.le)
  have hDcb : MeasureTheory.IntegrableOn (Work.Construction.L12dens f') (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hSf' hmf').mono_set
      (Set.Ioi_subset_Ioi hz.le)
  have hL12 : Work.Coercivity.L12f f z
      = Work.Coercivity.L12f (fun z θ => f z θ - f' z θ) z + Work.Coercivity.L12f f' z :=
    L12f_eq_sub_add hDa hDb hDca hDcb
  have hLT : Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport (fun z θ => f z θ - f' z θ)) 0
        + Work.Coercivity.L12f (Work.Coercivity.Transport f') 0 :=
    sharp_L12f_Transport_eq_sub_add hα hα1 hSf hSf' hmf hmf'
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.Proj,
    Work.Coercivity.L]
  rw [hDz, hT, hL12, hLT]
  ring

/-! ## Smoothness of `𝓛_Γ^T g` for `GalClass` data -/


/-! ## The target -/


end Work.FTS.GalFields.RHS
end
-- ===== merged: Submission.Work.FTS.PhiStar.RouteB.exists_uniform_HkSq_psiSeries_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RouteB

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "psiSeries" => Work.FTS.PhiStar.Series.psiSeries
local notation "psiTrunc" => Work.FTS.PhiStar.Series.psiTrunc
local notation "acoeff" => Work.FTS.PhiStar.Series.acoeff
local notation "cmode" => Work.FTS.PhiStar.Series.cmode
local notation "eNorm" => Work.EllipticEst.ModalSolution.eNorm

/-- `sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private theorem sEta_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sEta θ :=
  Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _

/-- **The energy bound `HkSq α 0 (psiSeries α F) ≤ C · HkSq α 0 F` with the explicit,
source-independent constant `C = 72 * ∫ θ in Iθ, sEta θ + 1`.**

This is the analytic content of the second conjunct of `ClassCHon.hkMem_zero_psiSeries_aux`, with
the constant written out so that it can be hoisted outside `∀ F`; the `HkMem` conjunct of the
sibling is not needed for the energy estimate and is therefore dropped. -/
theorem HkSq_psiSeries_le_const {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F)
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ)
    (hint_a : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun z => (acoeff α m F z) ^ 2 * (w z) ^ 2) Iz)
    (hper : ∀ m : ℕ, Work.FTS.ClassC.muSeq α m *
        Real.sqrt (∫ z in Iz, (acoeff α m F z) ^ 2 * (w z) ^ 2)
      ≤ Real.sqrt (∫ z in Iz,
          (Real.sqrt (eNorm m) * cmode m F z) ^ 2 * (w z) ^ 2))
    (hmeasT : ∀ N : ℕ, AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal ((psiTrunc α F N z θ) ^ 2 * (w z) ^ 2 * sEta θ))
      (MeasureTheory.volume.restrict Iz))
    (hslmeas : ∀ z ∈ Iz, AEMeasurable (fun θ : ℝ =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      (MeasureTheory.volume.restrict Iθ))
    (hmeasS : AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hcoef : ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |acoeff α m F z|)) :
    Work.Spaces.HkSq α 0 (psiSeries α F)
      ≤ (72 * (∫ θ in Iθ, sEta θ) + 1) * Work.Spaces.HkSq α 0 F := by
  have hα1 : α ≤ 1 := by linarith
  -- ## the pointwise convergence of the truncations
  have hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.PhiStar.integrableOn_sq_Q0_of_HkMem hF0 hsm
  have hconv : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => psiTrunc α F N z θ) Filter.atTop
        (nhds (psiSeries α F z θ)) := fun z hz θ hθ =>
    Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries hα hα1 hmom hsm hL2 hz hθ
  -- ## nonnegativity of the source energy and of the angular mass
  have hHkSqF : 0 ≤ Work.Spaces.HkSq α 0 F := by
    rw [Work.Spaces.HkSq]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 F z θ
  have hσnn : 0 ≤ ∫ θ in Iθ, sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => sEta_nonneg_Iθ' hθ)
  set e : ℝ := 72 * (∫ θ in Iθ, sEta θ) with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  set C₀ : ℝ := e * Work.Spaces.HkSq α 0 F with hC₀
  have hC₀nn : 0 ≤ C₀ := by rw [hC₀]; exact mul_nonneg he0 hHkSqF
  -- ## the truncated `lintegral` bound, uniformly in `N`
  have hbd : ∀ N : ℕ, (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal ((psiTrunc α F N z θ) ^ 2 * (w z) ^ 2 * sEta θ))
        ≤ ENNReal.ofReal C₀ := by
    intro N
    have h1 := Work.FTS.ClassC.lintegral_psiTrunc_le α F N hsm hF0 hint hintσ
      (fun m _ => hint_a m) (μ := fun m => Work.FTS.ClassC.muSeq α m)
      (fun m => Work.FTS.ClassC.muSeq_pos hα hα4 m) (fun m _ => hper m)
    have h2 := Work.FTS.ClassC.modeSum_muSeq_sum_le α hα hα4 N
    have hK0 : 0 ≤ 9 * (∫ θ in Iθ, sEta θ) := by linarith
    have hS0 : 0 ≤ ∑ m ∈ Finset.range (N + 1),
        (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    have h3 : 9 * (∫ θ in Iθ, sEta θ) *
          (∑ m ∈ Finset.range (N + 1),
            (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2)
          * Work.Spaces.HkSq α 0 F ≤ C₀ := by
      rw [hC₀, he]
      have h8 : (∑ m ∈ Finset.range (N + 1),
            (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2) ≤ 8 := h2
      nlinarith [hHkSqF, hσnn, hK0, hS0, h8]
    exact h1.trans (ENNReal.ofReal_le_ofReal h3)
  -- ## Fatou in the truncation parameter
  have hfinExpl : (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal ((psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ))
        ≤ ENNReal.ofReal C₀ :=
    Work.FTS.ClassCHon.CmpSupp.lintegral_psiSeries_le_Iz hC₀nn hconv hmeasT hbd
  -- ## transfer to the `HkIntegrand` form used by the capstone
  have hz_eq : ∀ z : ℝ, (∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      = (∫⁻ θ in Iθ,
        ENNReal.ofReal ((psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ)) := by
    intro z
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq' hθ]
    rw [show w z ^ 2 * ((psiSeries α F z θ) ^ 2 * sEta θ)
        = (psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ from by ring]
  have hfinIz : (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal C₀ := by
    rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hz_eq)]
    exact hfinExpl
  have hfin : (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal C₀ := by
    rw [MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact hfinIz
  -- ## the honesty of the series, and the energy bound
  have hmemΨ : Work.Spaces.HkMem α 0 (psiSeries α F) :=
    Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone hC₀nn hslmeas hfin hmeasS hcoef
  have hC₁ : 0 ≤ (e + 1) * Work.Spaces.HkSq α 0 F :=
    mul_nonneg (by linarith) hHkSqF
  have hfin₁ : (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal ((e + 1) * Work.Spaces.HkSq α 0 F) := by
    refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hHkSqF]
  exact Work.FTS.ClassCHon.CmpSupp.hkSq_le_of_lintegral hC₁ hmemΨ hfin₁

/-- The level-`0` `psiSeries` estimate with a constant *uniform in the source*: a
strengthening of (the second conjunct of) `Work.FTS.ClassCHon.hkMem_zero_psiSeries_of_source`,
where `∃ C` is hoisted outside `∀ F`.  The proof of the sibling produces the explicit constant
`C = 72 * ∫ θ in Iθ, (sin (2θ)) ^ (-(Work.Spaces.eta)) + 1`, which involves `α` only: replay the
argument of `Work.FTS.ClassCHon.hkMem_zero_psiSeries_of_source` (or of
`ClassCHon.hkMem_zero_psiSeries_aux` in the same file, via `ClassCHon.perMode_data_of_source`,
`ClassCHon.aemeasurable_acoeff_of_source`, `ClassCHon.meas_bundle_open`,
`ClassCHon.hcoef_source_general`, `ClassC.lintegral_psiTrunc_le`,
`ClassC.modeSum_muSeq_sum_le`, `CmpSupp.lintegral_psiSeries_le_Iz`,
`CmpSupp.hkSq_le_of_lintegral`) with `C` defined before `F` is introduced. -/
theorem exists_uniform_HkSq_psiSeries_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen F →
      Work.Spaces.HkMem α 1 F → (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) →
      Work.Spaces.HkSq α 0 (Work.FTS.PhiStar.Series.psiSeries α F)
        ≤ C * Work.Spaces.HkSq α 0 F := by
  refine ⟨72 * (∫ θ in Iθ, sEta θ) + 1, ?_, ?_⟩
  · have hσnn : 0 ≤ ∫ θ in Iθ, sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => sEta_nonneg_Iθ' hθ)
    linarith
  · intro F hsm hF hmom
    -- ## descent in the order, and the extraction of the `z ∂_z F` slot
    have hsmForall : ∀ n : ℕ,
        ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hsm
    have hF0 : Work.Spaces.HkMem α 0 F :=
      Work.FTS.EllipticEst.TT.HkMem_descend_open (k := 0) (l := 1) (by norm_num) hsmForall hF
    have hF1 : Work.Spaces.HkMem α 1 F := hF
    have hDz : Work.Spaces.HkMem α 0 (Work.Spaces.Dz F) :=
      Work.FTS.EllipticEst.Cores.HkMem_zero_of_DzIter_slot (k := 1) (i := 1) le_rfl hsm hF1
    -- ## the angular slice integrabilities of the source
    have hint : ∀ z ∈ Set.Ioi (0 : ℝ),
        MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
      fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem hF0 hz
    have hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
        MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ :=
      fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem hF0 hz
    -- ## the two per-mode facts and the three measurabilities
    obtain ⟨hint_a, hper⟩ :=
      Work.FTS.ClassCHon.perMode_data_of_source hα hα4 hsm hF0 hF1 hmom
    obtain ⟨hmeasT, hslmeas, hmeasS⟩ :=
      Work.FTS.ClassCHon.meas_bundle_open
        (Work.FTS.ClassCHon.aemeasurable_acoeff_of_source hα hα4 hsm hF0 hF1)
    -- ## the weighted `ℓ¹`-summability of the radial coefficients, and the energy bound
    exact HkSq_psiSeries_le_const hα hα4 hsm hF0 hmom hint hintσ hint_a hper hmeasT hslmeas
      hmeasS (Work.FTS.ClassCHon.hcoef_source_general hα hα4 hsm hF0 hF1 hDz hmom)

end Work.FTS.PhiStar.RouteB
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.slotMaj_of_offquadrant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Vanishing of the slots off the open quadrant

`D_θ = sin(2θ)∂_θ` and `D_z = z∂_z` are derivative operators, so if a profile `g` vanishes at
*every* angle outside `(0, π/2)` then every slot `D_z^jD_θ^i g` vanishes there too: the vanishing
is preserved by `D_z` (the slice in `z` at a fixed angle is identically zero), and `D_θ` either
sees a whole neighbourhood on which the function is zero (angles strictly below `0` or strictly
above `π/2`) or multiplies by `sin(2θ) = 0` (the angles `0` and `π/2`). -/

private theorem DthIter_eq_zero_of_offquadrant {g : Fn}
    (hoff : ∀ z θ : ℝ, θ ∉ Set.Ioo 0 (π / 2) → g z θ = 0) :
    ∀ (i : ℕ) (z θ : ℝ), θ ∉ Set.Ioo 0 (π / 2) → Work.Spaces.DthIter i g z θ = 0 := by
  intro i
  induction i with
  | zero => intro z θ hθ; exact hoff z θ hθ
  | succ i ih =>
    intro z θ hθ
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i g z θ') θ = 0
    rcases eq_or_ne (Real.sin (2 * θ)) 0 with hs | hs
    · rw [hs, zero_mul]
    · -- `sin(2θ) ≠ 0` forces `θ ∉ [0, π/2]`, so a whole neighbourhood of `θ` is off the quadrant
      have hnotcl : θ ∉ closure (Set.Ioo (0 : ℝ) (π / 2)) := by
        intro hcl
        have hmem : θ ∈ Set.Icc (0 : ℝ) (π / 2) := by
          rwa [closure_Ioo (ne_of_lt (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2))] at hcl
        exact hs (by
          rcases eq_or_lt_of_le hmem.1 with h | h
          · rw [← h]; simp
          · rcases eq_or_lt_of_le hmem.2 with h2 | h2
            · rw [h2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
            · exact absurd ⟨h, h2⟩ hθ)
      have hderiv : deriv (fun θ' => Work.Spaces.DthIter i g z θ') θ = 0 := by
        have hev : (fun θ' => Work.Spaces.DthIter i g z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hnotcl] with θ' hθ'
          exact ih z θ' (fun hmem => hθ' (subset_closure hmem))
        rw [hev.deriv_eq, deriv_const]
      rw [hderiv, mul_zero]

private theorem mixed_eq_zero_of_offquadrant {g : Fn}
    (hoff : ∀ z θ : ℝ, θ ∉ Set.Ioo 0 (π / 2) → g z θ = 0) (j i : ℕ) (z θ : ℝ)
    (hθ : θ ∉ Set.Ioo 0 (π / 2)) : Work.Spaces.mixed j i g z θ = 0 := by
  have hD : ∀ z' : ℝ, Work.Spaces.DthIter i g z' θ = 0 :=
    fun z' => DthIter_eq_zero_of_offquadrant hoff i z' θ hθ
  have hdz : ∀ j : ℕ, ∀ z : ℝ, Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ = 0 := by
    intro j
    induction j with
    | zero => intro z; exact hD z
    | succ j ih =>
      intro z
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z' θ) = fun _ => (0 : ℝ)
            from funext ih, deriv_const, mul_zero]
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ = 0
  exact hdz j z

/-- **The `SlotMaj` clause from a quadrant bound plus off-quadrant vanishing.**  `SlotMaj k Maj g`
quantifies over *all* real angles, while every pointwise estimate on the route is a statement
about the open quadrant; for a profile which vanishes off the open quadrant the two agree, because
`D_θ` and `D_z` are derivative operators and both carry the vanishing (`D_θ = sin(2θ)∂_θ` kills
the boundary angles, and on the complementary open regions the slice is locally zero). -/
theorem slotMaj_of_offquadrant {k : ℕ} {Maj : ℝ → ℝ} {g : Fn}
    (h0 : ∀ z, 0 ≤ Maj z)
    (hoff : ∀ z θ : ℝ, θ ∉ Set.Ioo 0 (π / 2) → g z θ = 0)
    (hbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, j + i ≤ k →
      |Work.Spaces.mixed j i g z θ| ≤ Maj z) :
    SlotMaj k Maj g := by
  intro z hz θ j i hji
  by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
  · exact hbd z hz θ hθ.1 hθ.2 j i hji
  · rw [mixed_eq_zero_of_offquadrant hoff j i z θ hθ, abs_zero]
    exact h0 z

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.RadBound.slot5_radA_pointwise_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RadBound/slot5_radA_pointwise_le` — the pointwise slot-`5` bound for `radA α f`

The radial profile of the transfer defect is

  `radA α f z = −ampA α z · L₁₂ f(z) + (ampB α z / c α) · L₁₂(Transport f)(0)`

(`Transfer.radA`), a sum of a product of the two `z`-profiles `ampA α`, `L₁₂ f` and a *constant*
multiple of the profile `ampB α`.  This file proves the pointwise estimate

  `Σ_{q<5} (D_z^q (radA α f)(z))² w(z)²
    ≤ 2·(6400·K²)·Σ_{q<5} (D_z^q (L₁₂ f)(z))² w(z)²
      + 2·(L₁₂(Transport f)(0)/c α)²·Σ_{q<5} (D_z^q (ampB α)(z))² w(z)²`

for every `z > 0`, under the sole hypothesis that the `(z∂_z)`-iterates of `ampA α` up to order
`4` are bounded by `K`; the two differentiability hypotheses are exactly what the Leibniz rule
for `D_z = z∂_z` needs at level `≤ 4`.

The three steps are:

* `radA_split_open` / `radA_expansion_open` — the pointwise expansion of `D_z^q (radA α f)`,
  `q ≤ 4`, obtained from the additivity of the `D_z`-iterates (`E1Parts.DzdIter_add_of_diff`,
  the differentiability of the `ampA α·L₁₂ f` iterates being the hypothesis `hAdiff` and that of
  the `ampB α` iterates coming from the smoothness `contDiffOn_ampB_five`) and the Leibniz rule
  (`Nonlinear.Pieces.dzdIter_mul_leibniz`);
* `radA_iter_sq_le` — the per-slot bound, from `(a+b)² ≤ 2a²+2b²`, `|D_z^b (ampA α)| ≤ K`,
  `Σ_b C(q,b) = 2^q` and the Cauchy–Schwarz estimate `(Σ|y_i|)² ≤ #s·Σy_i²`
  (`sq_sum_le_card_mul_sum_sq`);
* the assembly, where the numerical bound `2·4^q·(q+1) ≤ 2560` for `q ≤ 4` gives exactly the
  constant `2·6400 = 12800` when summed over the five slots.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
noncomputable section

open scoped Real Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.FTS.StrongEps.EpsRLX.RadBound

/-! ## The two summands of `radA α f` -/

/-- First summand of `radA α f`: `−ampA α · L₁₂ f`.  (The `(−1)·`-form is what
`E2pkg.dzdIter_const_mul` rewrites.) -/
abbrev radAU1 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : ℝ → ℝ :=
  fun z => -1 * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)

/-- Second summand of `radA α f`: the constant multiple of `ampB α`. -/
abbrev radAU2 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : ℝ → ℝ :=
  fun z => (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
    * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0

/-- **The decomposition of `radA` on `(0,∞)`** into its two summands. -/
theorem radA_split_open (α : ℝ) (f : Work.FTS.Galerkin.Fn) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.FTS.CoercivityFix.Transfer.radA α f z
        = (radAU1 α f + radAU2 α f) z := by
  intro z hz
  simp only [radAU1, radAU2, Pi.add_apply, Work.FTS.CoercivityFix.Transfer.radA]
  ring

/-! ## The pointwise expansion of the `D_z`-iterates of `radA` -/

/-- **The pointwise expansion of `D_z^q (radA α f)`**, `q ≤ 4`, on `(0,∞)`: the Leibniz sum of
the product `ampA α · L₁₂ f` plus the constant multiple of `D_z^q (ampB α)`. -/
theorem radA_expansion_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z)
    (hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z) :
    ∀ q : ℕ, q ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = -(∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
              * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
          + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
              * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
  intro q hq z hz
  have hU1diff : ∀ b < q, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (radAU1 α f)) z' := by
    intro b hb z' hz'
    rw [show radAU1 α f = fun z => -1 * (Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z) from rfl,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
    exact (hAdiff b (by omega) z' hz').const_mul (-1)
  have hU2diff : ∀ b < q, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (radAU2 α f)) z' := by
    intro b hb z' hz'
    have hU2 : radAU2 α f = fun z => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        / Work.Spaces.c α) * Work.FTS.CoercivityFix.Transfer.ampB α z := by
      funext w; simp only [radAU2]; ring
    rw [hU2, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
    exact (Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_five
      (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampB_five α) (by omega) hz').const_mul _
  have hLeib : Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
        * Work.Coercivity.L12f f z') z
      = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Work.Elliptic.DzdIter b
          (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) :=
    Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz q
      (Work.FTS.CoercivityFix.Transfer.ampA α) (Work.Coercivity.L12f f)
      (fun b hb z' hz' =>
        Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_five
          (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α) (by omega) hz')
      (fun b hb z' hz' => hL12diff b (by omega) z' hz') z hz
  have hU1val : Work.Elliptic.DzdIter q (radAU1 α f) z = -1 * (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z' * Work.Coercivity.L12f f z') z) := by
    rw [show radAU1 α f = fun z => -1 * (Work.FTS.CoercivityFix.Transfer.ampA α z
        * Work.Coercivity.L12f f z) from rfl,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
  have hU2val : Work.Elliptic.DzdIter q (radAU2 α f) z
      = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
    have hU2 : radAU2 α f = fun z => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        / Work.Spaces.c α) * Work.FTS.CoercivityFix.Transfer.ampB α z := by
      funext w; simp only [radAU2]; ring
    rw [hU2, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
  have hsumcongr : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Work.Elliptic.DzdIter b
        (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z))
      = (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) :=
    Finset.sum_congr rfl (fun b hb => by ring)
  calc Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
      = Work.Elliptic.DzdIter q (radAU1 α f + radAU2 α f) z :=
        Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _
          (radA_split_open α f) q z hz
    _ = Work.Elliptic.DzdIter q (radAU1 α f) z + Work.Elliptic.DzdIter q (radAU2 α f) z :=
        Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff q _ _ hU1diff hU2diff z hz
    _ = _ := by rw [hU1val, hU2val, hLeib, hsumcongr]; ring

/-! ## The per-slot bound -/

/-- **The pointwise bound for one `z∂_z`-slot of `radA α f`**, `q ≤ 4`: the squared iterate
weighted by `w²` is dominated by the full Leibniz slot sum of `L₁₂ f` (with the constant
`2·(K·2^q)²·(q+1)`) plus the constant-multiple slot of `ampB α`. -/
theorem radA_iter_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z)
    (hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z)
    {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b : ℕ, b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) :
    ∀ q : ℕ, q ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
            * (∑ c ∈ Finset.range (q + 1),
                (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
  intro q hq z hz
  have hexp := radA_expansion_open α hα hα1 f hL12diff hAdiff q hq z hz
  have hw2nn : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hchoose : (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℕ) : ℝ)) = (2 : ℝ) ^ q := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  have hSbound : |∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z|
      ≤ K * 2 ^ q * ∑ c ∈ Finset.range (q + 1),
          |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
    have hterm : ∀ b ∈ Finset.range (q + 1),
        |(q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z|
        ≤ K * ((q.choose b : ℝ) * ∑ c ∈ Finset.range (q + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) := by
      intro b hb
      have hC : 0 ≤ (q.choose b : ℝ) := Nat.cast_nonneg _
      have hb4 : b ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hAb : |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd b hb4 z hz
      have hXb : |Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z|
          ≤ ∑ c ∈ Finset.range (q + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| :=
        Finset.single_le_sum (f := fun c => |Work.Elliptic.DzdIter c
            (Work.Coercivity.L12f f) z|) (fun c _ => abs_nonneg _) (Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hb
          omega))
      calc |(q.choose b : ℝ)
            * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z|
          = (q.choose b : ℝ) * |Work.Elliptic.DzdIter b
              (Work.FTS.CoercivityFix.Transfer.ampA α) z|
            * |Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hC]
        _ ≤ (q.choose b : ℝ) * K * ∑ c ∈ Finset.range (q + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hAb hC) hXb (abs_nonneg _) ?_
            exact mul_nonneg hC hKnn
        _ = K * ((q.choose b : ℝ) * ∑ c ∈ Finset.range (q + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) := by ring
    have h3 : ∑ b ∈ Finset.range (q + 1), K * ((q.choose b : ℝ)
          * ∑ c ∈ Finset.range (q + 1), |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)
        = K * 2 ^ q * ∑ c ∈ Finset.range (q + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
      rw [← Finset.mul_sum, ← Finset.sum_mul, hchoose]
      ring
    have h2 := Finset.sum_le_sum hterm
    have h1 := Finset.abs_sum_le_sum_abs (s := Finset.range (q + 1))
      (f := fun b => (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
    linarith [h1, h2, h3.le, h3.ge]
  have hcs : (∑ c ∈ Finset.range (q + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) ^ 2
      ≤ ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (q + 1))
      (f := fun c => |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)
    rw [Finset.card_range] at h
    simpa only [nsmul_eq_mul, sq_abs, Nat.cast_add, Nat.cast_one] using h
  have hAmaj : (K * 2 ^ q * (∑ c ∈ Finset.range (q + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
      ≤ (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by
    calc (K * 2 ^ q * (∑ c ∈ Finset.range (q + 1),
          |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
        = (K * 2 ^ q) ^ 2 * (∑ c ∈ Finset.range (q + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) ^ 2 := by ring
      _ ≤ (K * 2 ^ q) ^ 2 * (((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by ring
  have hSsq : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
      ≤ (K * 2 ^ q * (∑ c ∈ Finset.range (q + 1),
          |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)) hSbound 2
    rwa [sq_abs] at h
  have hmaj : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
      ≤ (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := le_trans hSsq hAmaj
  have hmain : (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
      ≤ 2 * (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
            * (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z)) ^ 2 := by
    rw [hexp]
    nlinarith [sq_nonneg ((∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
        + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
          * (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z))]
  calc (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
      ≤ (2 * (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
            * (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z)) ^ 2)
          * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hmain hw2nn
    _ = 2 * ((∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by ring
    _ ≤ 2 * (((K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
              * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmaj hw2nn) (by norm_num)
    _ = 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
            * (∑ c ∈ Finset.range (q + 1),
                (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
        rw [← Finset.sum_mul]; ring

/-- The numerical bound behind the constant `6400`: for `q ≤ 4`,
`2·(K·2^q)²·(q+1) ≤ 2560·K²`, and `5·2560 = 12800 = 2·6400`. -/
theorem radA_slot_coeff_le {K : ℝ} (hKnn : 0 ≤ K) {q : ℕ} (hq : q ≤ 4) :
    2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1) ≤ 2560 * K ^ 2 := by
  have h2q : (2 : ℝ) ^ q ≤ 16 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq
    norm_num at h
    exact h
  have h2qnn : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
  have hsq : ((2 : ℝ) ^ q) ^ 2 ≤ 256 := by
    nlinarith [h2q, h2qnn, sq_nonneg ((2 : ℝ) ^ q - 16)]
  have hq5 : ((q : ℝ) + 1) ≤ 5 := by
    have h : (q : ℝ) ≤ 4 := by exact_mod_cast hq
    linarith
  have hmul : ((2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1) ≤ 256 * 5 :=
    mul_le_mul hsq hq5 (by positivity) (by norm_num)
  calc 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
      = 2 * K ^ 2 * (((2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)) := by ring
    _ ≤ 2 * K ^ 2 * (256 * 5) := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = 2560 * K ^ 2 := by ring

/-! ## The target -/

theorem slot5_radA_pointwise_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z)
    (hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z)
    {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b : ℕ, b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K)
    {z : ℝ} (hz : 0 < z) :
    Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z
      ≤ 2 * (6400 * K ^ 2) * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
  have hw2nn : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hslotnn : (0 : ℝ) ≤ Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z :=
    Work.FTS.GalFields.Norm.slot5_nonneg _ _
  -- the per-slot bounds
  have hper : ∀ q ∈ Finset.range 5,
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
            * (∑ c ∈ Finset.range (q + 1),
                (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) :=
    fun q hq => radA_iter_sq_le α hα hα1 f hL12diff hAdiff hKnn hKbd q
      (Nat.le_of_lt_succ (Finset.mem_range.mp hq)) z hz
  -- the tail of the `L₁₂ f`-slot sum is dominated by the full slot sum
  have hslot : ∀ q : ℕ, q ≤ 4 →
      (∑ c ∈ Finset.range (q + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z := by
    intro q hq
    simp only [Work.FTS.GalFields.Norm.slot5]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro c hc
      simp only [Finset.mem_range] at hc ⊢
      omega
    · intro c hc _
      exact mul_nonneg (sq_nonneg _) hw2nn
  calc Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z
      = ∑ q ∈ Finset.range 5,
          (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
        simp only [Work.FTS.GalFields.Norm.slot5]
    _ ≤ ∑ q ∈ Finset.range 5,
          (2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
              * (∑ c ∈ Finset.range (q + 1),
                  (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2)
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                * (Work.Spaces.w z) ^ 2)) := Finset.sum_le_sum hper
    _ = (∑ q ∈ Finset.range 5,
          (2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
              * (∑ c ∈ Finset.range (q + 1),
                  (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2)))
        + (∑ q ∈ Finset.range 5,
            2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                * (Work.Spaces.w z) ^ 2)) := Finset.sum_add_distrib
    _ ≤ (∑ _q ∈ Finset.range 5,
          2560 * K ^ 2 * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z)
        + (∑ q ∈ Finset.range 5,
            2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                * (Work.Spaces.w z) ^ 2)) := by
        refine add_le_add (Finset.sum_le_sum ?_) le_rfl
        intro q hq
        have hq4 : q ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
        have hcoefnn : (0 : ℝ) ≤ 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1) := by positivity
        calc 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
              * (∑ c ∈ Finset.range (q + 1),
                  (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2)
            ≤ 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
                * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z :=
              mul_le_mul_of_nonneg_left (hslot q hq4) hcoefnn
          _ ≤ 2560 * K ^ 2 * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z :=
              mul_le_mul_of_nonneg_right (radA_slot_coeff_le hKnn hq4) hslotnn
    _ = (∑ _q ∈ Finset.range 5,
          2560 * K ^ 2 * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z)
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
        have hsumB : (∑ q ∈ Finset.range 5,
              2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
                * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2))
            = 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
                * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
          rw [← Finset.mul_sum]
          rfl
        rw [hsumB]
    _ = 2 * (6400 * K ^ 2) * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num
        ring

end Work.FTS.StrongEps.EpsRLX.RadBound
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.HkMemXnN05 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

open MeasureTheory Set Filter
open scoped Real Topology
open Work.Spaces
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The level-`5` additivity of `HkMem`/`HkNorm` -/

/-- **Binary additivity of the level-`5` membership and norm** (the level-`5` analogue of
`ClassCRHS.add2`). -/
theorem add2_5 {α : ℝ} (hα : 0 < α) {u v : ℝ → ℝ → ℝ} {Bu Bv : ℝ}
    (husm : Work.FTS.EllipticEst.SmoothOpen u) (hvsm : Work.FTS.EllipticEst.SmoothOpen v)
    (hu : Work.Spaces.HkMem α 5 u) (hv : Work.Spaces.HkMem α 5 v)
    (bu : Work.Spaces.HkNorm α 5 u ≤ Bu) (bv : Work.Spaces.HkNorm α 5 v ≤ Bv)
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) :
    Work.Spaces.HkMem α 5 (fun z θ => u z θ + v z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => u z θ + v z θ) ≤ 2 * (Bu + Bv) := by
  have hmem : Work.Spaces.HkMem α 5 (fun z θ => u z θ + v z θ) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 5 husm hvsm hu hv
  refine ⟨hmem, ?_⟩
  have hb := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 5 hα husm hvsm hu hv
  have h1 := Work.Spaces.HkNorm_nonneg α 5 u
  have h2 := Work.Spaces.HkNorm_nonneg α 5 v
  linarith

/-! ## The assembly from the atomic data

The atomic sources are the lemmas `L5W_atoms_w`, `L5_L12w`, `L5_c2mL12w`, `W5_DthFstar`,
`W5_DzFstar`, `W5_c2m_L12Fstar`, `HkMem5_N0fix` (modules `H5/Atoms*.lean`). -/

/-- **The level-`5` `N₀`-block from the atomic data.** -/
theorem HkMemXnN05_of_atoms
    (hWat : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ a : ℝ, 0 < a ∧ ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w →
        Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ B →
        L5 α w a ∧ L5 α (Work.Spaces.Dz w) a ∧ L5 α (Work.Spaces.Dth w) a)
    (hL12 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ a : ℝ, 0 < a ∧ ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w →
        Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ B →
        L5 α (fun z θ => Work.Construction.L12 w z) a)
    (hc2mL12 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ a : ℝ, 0 < a ∧ ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w →
        Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → Work.Spaces.HkNorm α 6 w ≤ B →
        L5 α (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) a)
    (hDthF : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
        W5 α (Work.Spaces.Dth (Work.Construction.Fstar α)) a)
    (hDzF : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
        W5 α (Work.Spaces.Dz (Work.Construction.Fstar α)) a)
    (hc2mL12F : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
        W5 α (fun z θ => Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z) a)
    (hN0fix : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
        Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N0fix α) ∧
        Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α) ≤ a) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ K : ℝ, 0 < K ∧ ∀ {w : Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.Spaces.HkMem α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ K := by
  intro α hαI C₀ B
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- ## the universal constants
  obtain ⟨Cp, hCp, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  -- ## the atomic data
  obtain ⟨aw, haw, hwdata⟩ := hWat hαI (C₀ := C₀) (B := B)
  obtain ⟨aL, haL, hLdata⟩ := hL12 hαI (C₀ := C₀) (B := B)
  obtain ⟨aN, haN, hNdata⟩ := hc2mL12 hαI (C₀ := C₀) (B := B)
  obtain ⟨aDF, haDF, hDFdata⟩ := hDthF hαI
  obtain ⟨aDz, haDz, hDzdata⟩ := hDzF hαI
  obtain ⟨aF2, haF2, hF2data⟩ := hc2mL12F hαI
  obtain ⟨a0, ha0, h0mem, h0bd⟩ := hN0fix hαI
  have hrpow : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- ## the level-`5` bounds of the seven pieces
  set b0 : ℝ := a0 with hb0
  set b1 : ℝ := |1 / α| * (3 * (Cp * α ^ (-(1 / 2 : ℝ)) * aL * aw)) with hb1
  set b2 : ℝ := |3 / (2 * α)| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * aDF * aL)) with hb2
  set b3 : ℝ := |3 / (2 * α)| * (3 * (Cp * α ^ (-(1 / 2 : ℝ)) * aw * aL)) with hb3
  set b4 : ℝ := |(-1 : ℝ)| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * aDz * aN)) with hb4
  set b5 : ℝ := |(-1 : ℝ)| * (3 * (Cp * α ^ (-(1 / 2 : ℝ)) * aN * aw)) with hb5
  set b6 : ℝ := |(-1 : ℝ)| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * aF2 * aw)) with hb6
  have hb0nn : 0 ≤ b0 := by rw [hb0]; exact ha0.le
  have hb1nn : 0 ≤ b1 := by
    rw [hb1]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCp.le hrpow) haL.le) haw.le))
  have hb2nn : 0 ≤ b2 := by
    rw [hb2]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCw.le hrpow) haDF.le) haL.le))
  have hb3nn : 0 ≤ b3 := by
    rw [hb3]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCp.le hrpow) haw.le) haL.le))
  have hb4nn : 0 ≤ b4 := by
    rw [hb4]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCw.le hrpow) haDz.le) haN.le))
  have hb5nn : 0 ≤ b5 := by
    rw [hb5]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCp.le hrpow) haN.le) haw.le))
  have hb6nn : 0 ≤ b6 := by
    rw [hb6]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCw.le hrpow) haF2.le) haw.le))
  -- ## the cumulative bounds
  set c6 : ℝ := 2 * (b5 + b6) with hc6
  set c5 : ℝ := 2 * (b4 + c6) with hc5
  set c4 : ℝ := 2 * (b3 + c5) with hc4
  set c3 : ℝ := 2 * (b2 + c4) with hc3
  set c2 : ℝ := 2 * (b1 + c3) with hc2
  set c1 : ℝ := 2 * (b0 + c2) with hc1
  have hc6nn : 0 ≤ c6 := by rw [hc6]; linarith
  have hc5nn : 0 ≤ c5 := by rw [hc5]; linarith
  have hc4nn : 0 ≤ c4 := by rw [hc4]; linarith
  have hc3nn : 0 ≤ c3 := by rw [hc3]; linarith
  have hc2nn : 0 ≤ c2 := by rw [hc2]; linarith
  have hc1nn : 0 ≤ c1 := by rw [hc1]; linarith
  refine ⟨c1 + 1, by linarith, ?_⟩
  -- ## the data
  intro w hw hXnw hX6
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hw
  have hc2msm : Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α
  have hnegsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12sm
  -- ## the atomic facts
  have hatoms := hwdata hw hXnw hX6
  have hL5w : L5 α w aw := hatoms.1
  have hL5Dzw : L5 α (Work.Spaces.Dz w) aw := hatoms.2.1
  have hL5Dthw : L5 α (Work.Spaces.Dth w) aw := hatoms.2.2
  have hL5L12 : L5 α (fun z θ => Work.Construction.L12 w z) aL := hLdata hw hXnw hX6
  have hL5N : L5 α (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) aN :=
    hNdata hw hXnw hX6
  have hDF5 : W5 α (Work.Spaces.Dth (Work.Construction.Fstar α)) aDF := hDFdata
  have hDz5 : W5 α (Work.Spaces.Dz (Work.Construction.Fstar α)) aDz := hDzdata
  have hF25 : W5 α (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) aF2 := hF2data
  -- ## the six product rows
  have row1 := L5_mul (α := α) (Cprod := Cp) (C := fun z θ => Work.Construction.L12 w z)
    (G := w) (c := 1 / α) (a := aL) (b := aw) hα hα1 hCp (hprod α hα hα1)
    haL.le haw.le hL5L12 hL5w
  have row2 := W5_mul (α := α) (Cw := Cw) (F := Work.Spaces.Dth (Work.Construction.Fstar α))
    (G := fun z θ => Work.Construction.L12 w z) (c := 3 / (2 * α)) (a := aDF) (b := aL)
    hα hα1 hCw (hwprod α hα hα1) haDF.le haL.le hDF5 hL5L12
  have row3 := L5_mul (α := α) (Cprod := Cp) (C := Work.Spaces.Dth w)
    (G := fun z θ => Work.Construction.L12 w z) (c := 3 / (2 * α)) (a := aw) (b := aL)
    hα hα1 hCp (hprod α hα hα1) haw.le haL.le hL5Dthw hL5L12
  have row4 := W5_mul (α := α) (Cw := Cw) (F := Work.Spaces.Dz (Work.Construction.Fstar α))
    (G := fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) (c := -1)
    (a := aDz) (b := aN) hα hα1 hCw (hwprod α hα hα1) haDz.le haN.le hDz5 hL5N
  have row5 := L5_mul (α := α) (Cprod := Cp) (C := fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 w z) (G := Work.Spaces.Dz w) (c := -1) (a := aN) (b := aw)
    hα hα1 hCp (hprod α hα hα1) haN.le haw.le hL5N hL5Dzw
  have row6 := W5_mul (α := α) (Cw := Cw) (F := fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) (G := Work.Spaces.Dz w)
    (c := -1) (a := aF2) (b := aw) hα hα1 hCw (hwprod α hα hα1) haF2.le haw.le hF25 hL5Dzw
  -- ## the equalities with the named pieces
  have h1eq : Work.FTS.Nonlin.N03g α w = fun z θ => (1 / α)
      * ((fun z θ => Work.Construction.L12 w z) z θ * w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  have h2eq : Work.FTS.Nonlin.N04aF α w = fun z θ => (3 / (2 * α))
      * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * (fun z θ => Work.Construction.L12 w z) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth, Work.Spaces.pth]
    ring
  have h3eq : Work.FTS.Nonlin.N04bF α w = fun z θ => (3 / (2 * α))
      * (Work.Spaces.Dth w z θ * (fun z θ => Work.Construction.L12 w z) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth, Work.Spaces.pth]
    ring
  have h4eq : Work.FTS.Nonlin.N05aF α w = fun z θ => -1
      * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * (Work.Construction.c2m θ * Work.Construction.L12 w z)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    ring
  have h5eq : Work.FTS.Nonlin.N05bF α w = fun z θ => -1
      * ((Work.Construction.c2m θ * Work.Construction.L12 w z) * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have h6eq : Work.FTS.Nonlin.N06F α w = fun z θ => -1
      * ((Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  -- ## the seven pieces: membership, smoothness, norm bound
  have h0m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N0fix α) := h0mem
  have h1m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N03g α w) := by
    rw [h1eq]; exact row1.1
  have h2m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N04aF α w) := by
    rw [h2eq]; exact row2.1
  have h3m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N04bF α w) := by
    rw [h3eq]; exact row3.1
  have h4m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N05aF α w) := by
    rw [h4eq]; exact row4.1
  have h5m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N05bF α w) := by
    rw [h5eq]; exact row5.1
  have h6m : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N06F α w) := by
    rw [h6eq]; exact row6.1
  have h0bd' : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α) ≤ b0 := by
    rw [hb0]; exact h0bd
  have h1bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N03g α w) ≤ b1 := by
    rw [h1eq, hb1]; exact row1.2
  have h2bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N04aF α w) ≤ b2 := by
    rw [h2eq, hb2]; exact row2.2
  have h3bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N04bF α w) ≤ b3 := by
    rw [h3eq, hb3]; exact row3.2
  have h4bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N05aF α w) ≤ b4 := by
    rw [h4eq, hb4]; exact row4.2
  have h5bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N05bF α w) ≤ b5 := by
    rw [h5eq, hb5]; exact row5.2
  have h6bd : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N06F α w) ≤ b6 := by
    rw [h6eq, hb6]; exact row6.2
  have h0sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix α hα hα1
  have h1sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α w) := by
    rw [h1eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hL12sm hsmw)
  have h2sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α w) := by
    rw [h2eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hFsm.Dth hL12sm)
  have h3sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α w) := by
    rw [h3eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hsmw.Dth hL12sm)
  have h4sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α w) := by
    rw [h4eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul hFsm.Dz hnegsm)
  have h5sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α w) := by
    rw [h5eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul hnegsm hsmw.Dz)
  have h6sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α w) := by
    rw [h6eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12Fsm) hsmw.Dz)
  -- ## the nested assembly
  have ht6 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N05bF α w)
    (v := Work.FTS.Nonlin.N06F α w) h5sm h6sm h5m h6m h5bd h6bd hb5nn hb6nn
  have ht6' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ) ≤ c6 := by
    rw [hc6]; exact ht6.2
  have hsm6' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add h5sm h6sm
  have ht5 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N05aF α w)
    (v := fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)
    h4sm hsm6' h4m ht6.1 h4bd ht6' hb4nn hc6nn
  have ht5' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) ≤ c5 := by
    rw [hc5]; exact ht5.2
  have hsm5' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) :=
    Work.FTS.NonlinRows.smoothOpen_add h4sm hsm6'
  have ht4 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N04bF α w)
    (v := fun z θ => Work.FTS.Nonlin.N05aF α w z θ
      + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))
    h3sm hsm5' h3m ht5.1 h3bd ht5' hb3nn hc5nn
  have ht4' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) ≤ c4 := by
    rw [hc4]; exact ht4.2
  have hsm4' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_add h3sm hsm5'
  have ht3 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N04aF α w)
    (v := fun z θ => Work.FTS.Nonlin.N04bF α w z θ
      + (Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))
    h2sm hsm4' h2m ht4.1 h2bd ht4' hb2nn hc4nn
  have ht3' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) ≤ c3 := by
    rw [hc3]; exact ht3.2
  have hsm3' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) :=
    Work.FTS.NonlinRows.smoothOpen_add h2sm hsm4'
  have ht2 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N03g α w)
    (v := fun z θ => Work.FTS.Nonlin.N04aF α w z θ
      + (Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))
    h1sm hsm3' h1m ht3.1 h1bd ht3' hb1nn hc3nn
  have ht2' : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) ≤ c2 := by
    rw [hc2]; exact ht2.2
  have hsm2' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) :=
    Work.FTS.NonlinRows.smoothOpen_add h1sm hsm3'
  have ht1 := add2_5 (α := α) hα (u := Work.FTS.Nonlin.N0fix α)
    (v := fun z θ => Work.FTS.Nonlin.N03g α w z θ
      + (Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))))
    h0sm hsm2' h0m ht2.1 h0bd' ht2' hb0nn hc2nn
  have hSum_le : Work.Spaces.HkNorm α 5
      (fun z θ => Work.FTS.Nonlin.N0fix α z θ
        + (Work.FTS.Nonlin.N03g α w z θ
          + (Work.FTS.Nonlin.N04aF α w z θ
            + (Work.FTS.Nonlin.N04bF α w z θ
              + (Work.FTS.Nonlin.N05aF α w z θ
                + (Work.FTS.Nonlin.N05bF α w z θ
                  + Work.FTS.Nonlin.N06F α w z θ)))))) ≤ c1 := by
    rw [hc1]; exact ht1.2
  -- ## the transfer to `N₀`
  have hsplit := fun z θ (h : (z, θ) ∈ Work.Construction.Qd) =>
    Work.FTS.StrongEps.ClassCRHS.N0_split_open_aux hα hsmw z θ h
  have hmem : Work.Spaces.HkMem α 5
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 ht1.1
      (fun z hz θ hθ => (hsplit z θ ⟨hz, hθ.1, hθ.2⟩).symm)
  have hksq : Work.Spaces.HkSq α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      = Work.Spaces.HkSq α 5
        (fun z θ => Work.FTS.Nonlin.N0fix α z θ
          + (Work.FTS.Nonlin.N03g α w z θ
            + (Work.FTS.Nonlin.N04aF α w z θ
              + (Work.FTS.Nonlin.N04bF α w z θ
                + (Work.FTS.Nonlin.N05aF α w z θ
                  + (Work.FTS.Nonlin.N05bF α w z θ
                    + Work.FTS.Nonlin.N06F α w z θ)))))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 5
      (fun z θ hz hθ0 hθ1 => hsplit z θ ⟨hz, hθ0, hθ1⟩)
  have hXn : Work.Spaces.HkNorm α 5
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ c1 := by
    have h : Work.Spaces.HkNorm α 5
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
        = Work.Spaces.HkNorm α 5
          (fun z θ => Work.FTS.Nonlin.N0fix α z θ
            + (Work.FTS.Nonlin.N03g α w z θ
              + (Work.FTS.Nonlin.N04aF α w z θ
                + (Work.FTS.Nonlin.N04bF α w z θ
                  + (Work.FTS.Nonlin.N05aF α w z θ
                    + (Work.FTS.Nonlin.N05bF α w z θ
                      + Work.FTS.Nonlin.N06F α w z θ)))))) := by
      simp only [Work.Spaces.HkNorm, hksq]
    rw [h]
    exact hSum_le
  exact ⟨hmem, le_trans hXn (by linarith)⟩

/-- **The `N₀`-block at level 5** (the level-`5` analogue of `HkMemXnN0`,
`Submission/Work/FTS/StrongEps/ClassCRHS/HkMemXnN0.lean`).

Same route as `HkMemXnN5`: the level shift `H5.HkSq_succ_le` plus the Leibniz identities
`H5.Dz_mul_eqOn_Q0` / `H5.Dth_mul_eqOn_Q0` plus the level-four product rules
(`OpenPkg.prod_field`, `OpenPkg.wprod_field_winf`, `OpenPkg.angmul_field`), applied to the seven
monomials of `N0 α (F_*+w) w` (see `Work.Construction.N0`: the terms
`(3/(2α))s2·L12(F_*)·pth(F_*)`, `-c2m·L12(F_*)·Dz(F_*)`, `(1/α)·L12 g·g`,
`(3/(2α))s2·L12 g·pth F`, `-c2m·L12 g·Dz F`, `-c2m·L12(F_*)·Dz g`, where `F = F_* + w`).
There is no star and no elliptic data here: the atoms are `w`, `Dth w`, `Dz w`, the radial
functions `L12 w z`, `FK w`, and the fixed profiles `F_*`, `DthF_*`, `DzF_*`, `s2`, `c2m`, `hKer`,
`L12(F_*)`, together with the `(z/(1+z))`-weighted versions where the level-4 proof uses them.
`K` may depend on `α, C₀, B` but not on `w`.  The level-4 proof is
`HkMemXnN0` + `ClassCRHS/HkMemXnN0Rows.lean` + `HkMemXnN0Aux.lean`. -/
theorem HkMemXnN05 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ K : ℝ, 0 < K ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.Spaces.HkMem α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ∧
      Work.Spaces.HkNorm α 5 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ K :=
  HkMemXnN05_of_atoms Atoms.L5AtomsW Atoms.L5L12W (Atoms.L5C2mL12W Atoms.L5L12W)
    Atoms.W5DthFstar Atoms.W5DzFstar Atoms.W5C2mL12Fstar Atoms.HkMem5N0fix

end Work.FTS.StrongEps.H5
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open Work.FTS.StrongPersist.H6Rows.Npair6BWork (PM aesm_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- `T₀ f z = ∫_θ (D_z^6 f z θ)²`, the *unweighted* angular energy of the sixth `D_z`-iterate. -/
def T0 (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 6 f z θ) ^ 2

/-- `TT f z = w(z)² T₀ f z`, the `ρ = w²` (i.e. `leafOne`-)weighted angular energy. -/
def TT (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * T0 f z





end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumB1Five =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem npSinTwoNonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- **The remaining `a₁ = 0` summand: `(a,b,b₁) = (1,5,5)` (the highest pure-radial coefficient slot).**

The pairing is `∫∫ ρ · D_z⁵A · mixed 1 1 f · mixed 5 1 f`; it is the only configuration of the row with
`a₁ = 0` for which the coefficient slot has no pointwise price (`supSix` covers orders `≤ 4` only), while the
two `f`-slots have orders `2` and `6`.

Route (three-factor split; no pair of the three factors can carry the `γ`-weight alone, since the pure
`D_z⁵A`-slot only has the `η`-slot and `canonW (gam α) ≤ √(canonW q₁ · canonW q₂)` needs `q₁ + q₂ ≥ 2γ`
while the available slots give at most `η + γ < 2γ`):

1. `ρ ≤ canonW (gam α)` and `σ^{-(γ-η/2)} ≤ w²σ^{-γ}` (as `σ^{η/2} ≤ w²`), so on the open quadrant
   `ρ|X||F||G| ≤ (wσ^{-η/2}|X|)·w·(σ^{-(γ-η/2)}|F||G|)`;
2. Cauchy–Schwarz in `θ` for the two `f`-slots:
   `∫_θσ^{-(γ-η/2)}|F||G| ≤ √(∫_θσ^{-γ}F²)·√(∫_θσ^{-γ}G²) =: √(P(z)Q(z))` (split `γ-η/2 = q₁+q₂` with
   `2q₁, 2q₂ ≤ γ`);
3. Cauchy–Schwarz in `θ` for the first factor: `∫_θσ^{-η/2}|X| ≤ √(∫_θσ^{-η})·√(∫_θX²) ≤ C√(∫_θX²)`
   (`∫_θσ^{-η} < ∞` as `η < 1`);
4. Cauchy–Schwarz in `z` with `A(z) := √(∫_θX²)·√(P(z))`, `B(z) := √(Q(z))`:
   `∫_zw²AB ≤ √(∫_zw²A²)·√(∫_zw²B²)`, where
   `∫_zw²A² ≤ (sup_zP)·∫_zw²∫_θX² ≤ (C·HkSq α 4 f)·(HkSq α 6 A) ≤ C·M²·K6²` and
   `∫_zw²B² = ∫_zw²∫_θσ^{-γ}(mixed 5 1 f)² ≤ HkSq α 6 f` (`T6Coef/zProdIntLe` for the slot `(5,1)`).
   Hence `|∫| ≤ C α^{-1/2}M·K6·HkNorm α 6 f`.

The one new ingredient is the `z`-for-`θ` slice-sup `sup_z ∫_θσ^{-γ}(mixed 1 1 f z ·)² ≤ C·HkSq α 4 f`: the
`(i,j) = (1,1)` generalisation of the proved `T6Coef/vSliceSupLe` (the `(1,0)` case), by the same route
(`TransportS/SupDzAux/sda_HkSqSwap_open` + the `z`-Agmon for the pair of slots `(1,1)`/`(2,1)`, of order
`≤ 4`, e.g. `SixAux.zslice6_hardy`), together with `∫∫w²(D_z⁵A)² ≤ HkSq α 6 A` (`σ^{-η} ≥ 1`).

**Implementation note.**  The three factors are separated with the *same* `σ^{-γ}` weight as follows:
the leaf weight is compared with `leafGam α` (`ρ ≤ canonW (gam α) = leafGam α`), the pure slot `D_z⁵A` is
bounded by the `θ`-Agmon majorant `√(b1fiveMX α A z)` (`xSliceAgmon5`), the two `f`-slots by the angular
Cauchy–Schwarz `gamSliceCS11` together with the slice-sup `gamSliceSup11` (constant `3`), and the remaining
radial pair by the Cauchy–Schwarz `b1gRadCS`; the radial integrals are `xProdIntLe`, `zProdIntLe` and the
bookkeeping is `rowSumB1FiveArith`.  All the `mixed 1 1 f`-slice machinery is the already-proved
`H6Row6Gam`/`H6Row6` chain (`b1gSliceInt`, `b1gInner`, `b1gOuter`, `b1gRadCS`, `b1gMajInt`). -/
theorem rowSumB1Five : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.FTS.TransportS.IsLeafW α 1 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.DzIter 5 A p.1 p.2
          * Work.Spaces.mixed 1 1 f p.1 p.2
          * Work.Spaces.mixed 5 1 f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter 5 A p.1 p.2
            * Work.Spaces.mixed 1 1 f p.1 p.2
            * Work.Spaces.mixed 5 1 f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f := by
  refine ⟨100, by norm_num, ?_⟩
  intro α hα A f K0 K4 K6 K1 M ρ hCoef hThMem hThLe hDat hρ
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  -- ## basic nonnegativities
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hDat.bdd
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hCoef.n6
  have hNnn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  -- ## the integrand
  set F : ℝ × ℝ → ℝ := fun p => ρ p.1 p.2 * Work.Spaces.DzIter 5 A p.1 p.2
      * Work.Spaces.mixed 1 1 f p.1 p.2 * Work.Spaces.mixed 5 1 f p.1 p.2 with hF
  -- ## `ρ` is dominated by the leaf `γ`-weight on the open quadrant
  have hρle : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ ≤ Work.FTS.TransportS.leafGam α z θ := by
    intro z θ hz hθ hθ2
    have h := leafW_le_canonW_gam (α := α) hα0 hρ z θ hz hθ hθ2
    rwa [leafGam_eq_canonW]
  have hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ :=
    fun z θ => leafW_nonneg hρ z θ
  -- ## the pointwise domination `|F| ≤ |b1gF|` on the open quadrant
  have hptQ0 : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      |F p| ≤ |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have h1 : |F p| = ρ p.1 p.2 * |Work.Spaces.DzIter 5 A p.1 p.2|
        * |Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2| := by
      simp only [hF]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hρnn p.1 p.2 hz hθ0 hθ1)]
    have h2 : |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| =
        Work.FTS.TransportS.leafGam α p.1 p.2 * |Work.Spaces.DzIter 5 A p.1 p.2|
        * |Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2| := by
      rw [Work.FTS.StrongPersist.H6Row6.b1gF_apply, Work.Spaces.mixed_zero_right]
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (Work.FTS.TransportS.leafGam_nonneg α (npSinTwoNonneg hθ))]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hρle p.1 p.2 hz hθ0 hθ1) (abs_nonneg _)) (abs_nonneg _))
      (abs_nonneg _)
  -- ## the slicewise core for `b1gF` (the `mixed 1 1 f` middle slot)
  have hSliceInt := Work.FTS.StrongPersist.H6Row6.b1gSliceInt α A f hα0 hα1
    hCoef.sm hDat.sm hCoef.h6 hDat.h6
  have hinner := Work.FTS.StrongPersist.H6Row6.b1gInner α A f M hαI
    hCoef.sm hDat.sm hCoef.h6 hDat.h6 hDat.bdd
  have hIouter := Work.FTS.StrongPersist.H6Row6.b1gOuter α A f M hαI
    hCoef.sm hDat.sm hCoef.h6 hDat.h6 hDat.bdd
  have hIslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ => |Work.FTS.StrongPersist.H6Row6.b1gF α A f (0, θ)|)
          = fun _ => (0 : ℝ) := by
        funext θ
        rw [Work.FTS.StrongPersist.H6Row6.b1gF_apply, Work.Spaces.mixed_zero_right]
        simp only [Work.FTS.TransportS.leafGam, Work.Spaces.w]
        norm_num
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · exact hSliceInt z hpos
  have hcontF0 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.StrongPersist.H6Row6.b1gF α A f p)
      Work.FTS.EllipticEst.Q0 := by
    simp only [Work.FTS.StrongPersist.H6Row6.b1gF_apply]
    exact (((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hCoef.sm.mixed 5 0))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hDat.sm.mixed 1 1))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hDat.sm.mixed 5 1))
  have hI0aesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Work.FTS.StrongPersist.H6Row6.b1gF α A f p|) PM :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF0.abs
  obtain ⟨hF0abs_int, hF0abs_val⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|)
    (fun z θ => abs_nonneg _) hI0aesm hIslice hIouter
  -- ## the two radial integrals
  have hMXval := (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe α A hα0 hα1
    hCoef.sm hCoef.h6).2
  have hQval := (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe α f hα0 hα1
    hDat.sm hDat.h6).2
  have hcsz := Work.FTS.StrongPersist.H6Row6.b1gRadCS α A f hα0 hα1
    hCoef.sm hDat.sm hCoef.h6 hDat.h6
  have hMajInt := Work.FTS.StrongPersist.H6Row6.b1gMajInt α A f M hα0 hα1
    hCoef.sm hDat.sm hCoef.h6 hDat.h6 hMnn
  -- ## the arithmetic inputs
  have hSqA : Work.Spaces.HkSq α 6 A = (Work.Spaces.HkNorm α 6 A) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 A)]
  have hSqf : Work.Spaces.HkSq α 6 f = (Work.Spaces.HkNorm α 6 f) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
  have hcoefnn : 0 ≤ 4 / Real.pi + 200 / (Work.Spaces.gam α - 1) := by
    refine add_nonneg (by positivity) ?_
    refine div_nonneg (by norm_num) ?_
    rw [Work.Spaces.gam_sub_one]; positivity
  have hMXle : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * K6 ^ 2 := by
    refine le_trans (by
      simpa only [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply] using hMXval) ?_
    rw [hSqA]
    refine mul_le_mul_of_nonneg_left ?_ hcoefnn
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 A) hCoef.n6 2
  have hQle : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)
      ≤ (Work.Spaces.HkNorm α 6 f) ^ 2 := by
    refine le_trans (by
      simpa only [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply] using hQval) ?_
    rw [hSqf]
  -- ## the value bound on the `b1gF`-side
  have hval0 : (∫ z, (∫ θ, |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f := by
    have hstep1 : (∫ z, (∫ θ, |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        ≤ ∫ z, Real.sqrt 3 * M * ((Work.Spaces.w z
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
            * (Work.Spaces.w z
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.integral_mono_ae hIouter hMajInt hinner
    have hstep2 : (∫ z, Real.sqrt 3 * M * ((Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
          * (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = Real.sqrt 3 * M * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
          * (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))) :=
      MeasureTheory.integral_const_mul _ _
    have hstep3 : Real.sqrt 3 * M * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
          * (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)))
        ≤ Real.sqrt 3 * M * (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
            * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) :=
      mul_le_mul_of_nonneg_left hcsz (mul_nonneg (Real.sqrt_nonneg 3) hMnn)
    have hstep4 : Real.sqrt 3 * M * (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
            * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))
        ≤ 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f :=
      rowSumB1FiveArith hα0 hα1 hMnn hK6nn hNnn hMXle hQle
    exact hstep1.trans (hstep2.le.trans (hstep3.trans hstep4))
  -- ## a.e. strong measurability and integrability of `F`
  have hFaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p) PM := by
    simp only [hF]
    exact (((aesm_leafW hρ).mul (aesm_mixed hCoef.sm 5 0)).mul
      (aesm_mixed hDat.sm 1 1)).mul (aesm_mixed hDat.sm 5 1)
  have hptae : ∀ᵐ p ∂PM,
      |F p| ≤ |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| :=
    ae_of_forall_Qd (fun z θ hz hθ hθ2 =>
      hptQ0 (z, θ) (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩))
  have hFabs_aesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |F p|) PM :=
    continuous_abs.comp_aestronglyMeasurable hFaesm
  have hFabs_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => |F p|) PM := by
    refine hF0abs_int.mono' hFabs_aesm ?_
    filter_upwards [hptae] with p hp
    rw [Real.norm_eq_abs, abs_abs]
    exact hp
  have hF_int : MeasureTheory.Integrable F PM := by
    refine hFabs_int.mono' hFaesm ?_
    filter_upwards with p
    exact le_of_eq (by rw [Real.norm_eq_abs])
  have hle_abs : (∫ p, |F p| ∂PM)
      ≤ ∫ p, |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| ∂PM :=
    MeasureTheory.integral_mono_ae hFabs_int hF0abs_int hptae
  -- ## assembly
  refine ⟨hF_int, ?_⟩
  calc |∫ p, F p ∂PM|
      ≤ ∫ p, ‖F p‖ ∂PM := by
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm (μ := PM) F
    _ = ∫ p, |F p| ∂PM := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ p, |Work.FTS.StrongPersist.H6Row6.b1gF α A f p| ∂PM := hle_abs
    _ = ∫ z, (∫ θ, |Work.FTS.StrongPersist.H6Row6.b1gF α A f (z, θ)|
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := hF0abs_val
    _ ≤ 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * Work.Spaces.HkNorm α 6 f := hval0

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumFlux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-- **The flux (top self-pairing) Leibniz summand: `a₁ = b₁ = 0`, `a + b = 6`.**

The summand is `∫∫ ρ · A · mixed (b+1) a f · mixed b a f` (the `(0,0)` Leibniz term of
`D_z^bD_θ^a (A·D_z f)` at the top slot, where `mixed (b+1) a f = D_z(mixed b a f)`).

Route: `Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay` (proved) applied with `h := A`, `g := f`,
`q := γ` if `1 ≤ a` resp. `q := η` if `a = 0`, and `M := max K0 (C/√(γ-1)·K4)` (bounds for `|A|` and `|D_zA|`
from `CoefData.val` and `TransportS.sup_dz_le_hk` with `Xn α A = HkNorm α 4 A`) gives
`|∫_z∫_θ canonW q · A · D_z(mixed b a f) · mixed b a f| ≤ 2·M·HkSq α 6 f`.  Choose `q` to be the exponent of
the leaf weight `ρ` itself when that is convenient (`IsLeafW` makes `ρ` one of `canonW η`, `canonW 0`,
`canonW (gam α)`), so that the left-hand side *is* the `fluxSix_noDecay` integral; otherwise use
`ρ ≤ canonW q` on the open quadrant and absorb `ρ/canonW q` (a `θ`-only factor bounded by `1`) into `h`.
Convert the iterated integral into the `PM`-integral by Fubini (`MeasureTheory.integral_prod`; integrability
comes from the pointwise domination by `canonW q·|A|·|D_z(mixed b a f)|·|mixed b a f|` and `HkMem α 6 f`,
`HkMem α 7 f`).  Since `C/√(γ-1) = C√10·α^{-1/2}`, the conclusion is `C α^{-1/2}(K0+K4)·HkSq α 6 f`. -/
theorem rowSumFlux : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b = 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * A p.1 p.2
            * Work.Spaces.mixed (b + 1) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Cfl, hCflpos, hflux⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay
  obtain ⟨Cd, hCdpos, hsd⟩ := Work.FTS.TransportS.sup_dz_le_hk
  refine ⟨Cfl * max 1 (Cd * Real.sqrt 10), by positivity, ?_⟩
  intro α hαIoc A f K0 K4 K6 K1 M a b ρ hcoef hctmem hctle hdat hab hleaf
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hCd0 : 0 ≤ Cd := le_of_lt hCdpos
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK0 : 0 ≤ K0 := by
    have h := hcoef.val 1 (Real.pi / 4) (by norm_num) (by positivity)
      (by linarith [Real.pi_pos])
    exact le_trans (abs_nonneg _) h
  -- ## the pointwise price of the coefficient slot `D_z A`
  have hph : 0 < α ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hα0 _
  have hple : α ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα0.le hα1 (by norm_num)
  have hpow1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hα0.le]
    exact (one_le_inv₀ hph).mpr hple
  have hsqrt_gam : Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt α / Real.sqrt 10 := by
    rw [Work.Spaces.gam_sub_one, Real.sqrt_div hα0.le]
  have hpow_alpha : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hα0.le (1 / 2 : ℝ)]
  have hdiv : (Real.sqrt (Work.Spaces.gam α - 1))⁻¹
      = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
    rw [hsqrt_gam, inv_div, div_eq_mul_inv, hpow_alpha]
  have hDzA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dz A z θ| ≤ Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4 := by
    intro z θ hz hθ0 hθ2
    have h1 := hsd α A hα0 hα1 hcoef.sm hcoef.h4 1 (by norm_num) z θ hz hθ0 hθ2
    have h2 : |Work.Spaces.Dz A z θ| ≤ Cd / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.Nonlin.Xn α A := by
      simpa only [Work.Spaces.DzIter, Work.Spaces.Dz] using h1
    have hmain : Cd / Real.sqrt (Work.Spaces.gam α - 1)
        = Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, hdiv]
      ring
    calc |Work.Spaces.Dz A z θ|
        ≤ Cd / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A := h2
      _ ≤ Cd / Real.sqrt (Work.Spaces.gam α - 1) * K4 :=
          mul_le_mul_of_nonneg_left hcoef.n4 (div_nonneg hCd0 (Real.sqrt_nonneg _))
      _ = Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4 := by rw [hmain]
  set MA : ℝ := max K0 (Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4) with hMAdef
  have hMA0 : 0 ≤ MA := le_trans hK0 (le_max_left _ _)
  have hC0_1 : (1 : ℝ) ≤ max 1 (Cd * Real.sqrt 10) := le_max_left _ _
  have hpow_nn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hα0 _)
  have hA_le : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA :=
    fun z θ hz hθ0 hθ2 => le_trans (hcoef.val z θ hz hθ0 hθ2) (le_max_left _ _)
  have hDzA_le : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dz A z θ| ≤ MA :=
    fun z θ hz hθ0 hθ2 => le_trans (hDzA z θ hz hθ0 hθ2) (le_max_right _ _)
  have hMA_le : MA ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
    rw [hMAdef]
    refine max_le ?_ ?_
    · have h1 : K0 ≤ α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
        le_trans (le_add_of_nonneg_right hK4) (le_mul_of_one_le_left (by linarith) hpow1)
      calc K0 ≤ α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := h1
        _ ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
            have h2 : α ^ (-(1 / 2 : ℝ))
                ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) := by
              calc α ^ (-(1 / 2 : ℝ)) = 1 * α ^ (-(1 / 2 : ℝ)) := by ring
                _ ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) :=
                    mul_le_mul_of_nonneg_right hC0_1 hpow_nn
            exact mul_le_mul_of_nonneg_right h2 (by linarith)
    · have h2 : Cd * Real.sqrt 10 ≤ max 1 (Cd * Real.sqrt 10) := le_max_right _ _
      have hnn : 0 ≤ max 1 (Cd * Real.sqrt 10) := le_trans zero_le_one hC0_1
      have h3 : Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4
          ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * K4 := by
        refine mul_le_mul_of_nonneg_right ?_ hK4
        exact mul_le_mul_of_nonneg_right h2 hpow_nn
      calc Cd * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4
          ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * K4 := h3
        _ ≤ max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hnn hpow_nn)
  -- ## the canonical-weight form of the slot, for an admissible exponent `q`
  have key : ∀ (q : ℝ), 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      MeasureTheory.Integrable
          (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
            * Work.Spaces.mixed (b + 1) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
            * Work.Spaces.mixed (b + 1) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ Cfl * max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4)
            * Work.Spaces.HkSq α 6 f := by
    intro q hq0 hqγ hqη
    -- the iterated-integral flux bound
    have hflux_it : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ Cfl * MA * Work.Spaces.HkSq α 6 f :=
      hflux α A f a b q MA hα0 hα1 hq0 hqγ hqη (by omega) hcoef.sm hdat.sm hdat.h6 hdat.h7
        hA_le hDzA_le
    -- the two pointwise slot dominations
    have hdom6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ _ hθ hθ2
      rcases Nat.eq_zero_or_pos a with ha | ha
      · rw [ha, Work.Spaces.mixed_zero_right]
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le 6 (hqη ha) hθ hθ2 (by omega)
      · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le 6 hqγ hθ hθ2 ha (by omega)
    have hdom7 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
      intro z θ _ hθ hθ2
      rcases Nat.eq_zero_or_pos a with ha | ha
      · rw [ha, Work.Spaces.mixed_zero_right]
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le 7 (hqη ha) hθ hθ2 (by omega)
      · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le 7 hqγ hθ hθ2 ha (by omega)
    -- the pointwise bound on the integrand
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
            * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ|
          ≤ (MA / 2) * (Work.Spaces.HkIntegrand α 7 f z θ
              + Work.Spaces.HkIntegrand α 6 f z θ) := by
      intro z θ hz hθ0 hθ2
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ2.le⟩
      have hcw : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
        Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
      have hX := hdom7 z θ hz hθ0 hθ2
      have hY := hdom6 z θ hz hθ0 hθ2
      have hrew : Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
            * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ
          = A z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ) := by ring
      rw [hrew]
      refine le_trans (Work.FTS.StrongPersist.N6Trans.SixAux.abs_mul_canonW_mul_le
        (q := q) (M := MA) (X := Work.Spaces.mixed (b + 1) a f z θ)
        (Y := Work.Spaces.mixed b a f z θ) (hh := A z θ) hcw hMA0
        (hA_le z θ hz hθ0 hθ2)) ?_
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith : 0 ≤ MA / 2)
    -- continuity on the open quadrant
    have hcontF : ContinuousOn (fun p : ℝ × ℝ =>
        Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ =>
          Work.FTS.TransportS.SlotT2.canonW q p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        Work.FTS.TransportS.SlotT2.continuousOn_canonW q
      have h2 : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hcoef.sm.continuousOn
      have h3 : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.mixed (b + 1) a f p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hdat.sm.mixed (b + 1) a).continuousOn
      have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hdat.sm.mixed b a).continuousOn
      exact (((h1.mul h2).mul h3).mul h4).congr (fun p _ => rfl)
    -- integrability of the integrand
    have hdomint : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (MA / 2) * (Work.Spaces.HkIntegrand α 7 f p.1 p.2
          + Work.Spaces.HkIntegrand α 6 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      (((Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hdat.sm hdat.h7).1.add
        (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hdat.sm hdat.h6).1).const_mul
          (MA / 2))
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcontF
    have hae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        ‖Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2‖
          ≤ (MA / 2) * (Work.Spaces.HkIntegrand α 7 f p.1 p.2
              + Work.Spaces.HkIntegrand α 6 f p.1 p.2) :=
      ae_of_forall_Qd
        (fun z θ hz hθ0 hθ2 => by rw [Real.norm_eq_abs]; exact hpt z θ hz hθ0 hθ2)
    have hFint : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      hdomint.mono' haesm hae
    -- Fubini
    have hFub : (∫ p, Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * A p.1 p.2
            * Work.Spaces.mixed (b + 1) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ :=
      (MeasureTheory.integral_integral
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun z θ => Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ)
        hFint).symm
    have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
              * Work.Spaces.Dz (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      rfl
    -- the price
    have hprice : Cfl * MA * Work.Spaces.HkSq α 6 f
        ≤ Cfl * max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4)
            * Work.Spaces.HkSq α 6 f := by
      calc Cfl * MA * Work.Spaces.HkSq α 6 f
          ≤ Cfl * (max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
              * Work.Spaces.HkSq α 6 f :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMA_le hCflpos.le) hS0
        _ = Cfl * max 1 (Cd * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4)
              * Work.Spaces.HkSq α 6 f := by ring
    exact ⟨hFint, by rw [hFub, hcongr]; exact le_trans hflux_it hprice⟩
  -- ## the three leaf weights
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · subst hρ
    exact key Work.Spaces.eta Work.Spaces.eta_nonneg
      (Work.FTS.TransportS.T2Sup.eta_le_gam hα0) (fun _ => le_rfl)
  · subst hρ
    have hfun : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafOne p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
        = (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW 0 p.1 p.2 * A p.1 p.2
          * Work.Spaces.mixed (b + 1) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2) := by
      funext p
      simp only [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW, neg_zero,
        Real.rpow_zero, mul_one]
    rw [hfun]
    exact key 0 le_rfl (le_of_lt (Work.Spaces.gam_pos hα0))
      (fun _ => Work.Spaces.eta_nonneg)
  · subst hρ
    exact key (Work.Spaces.gam α) (le_of_lt (Work.Spaces.gam_pos hα0)) le_rfl
      (fun ha0 => absurd ha0 (Nat.one_le_iff_ne_zero.mp ha1))

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-! ## Two elementary helpers -/

/-- `CoefTh` is nonnegative (each summand is a supremum of absolute values). -/
theorem coefTh_nonneg (l : ℕ) (A : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.VocabO.CoefTh l A := by
  rw [Work.FTS.VocabO.CoefTh]
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs with h
  · exact supAbsO_nonneg _
  · exact le_rfl

/-- **The integral engine.**  A pointwise domination of `|F|` by `M · HkIntegrand α 6 g` on the
open quadrant gives integrability of `F` against the product measure `PM` and the bound
`|∫ F| ≤ M · HkSq α 6 g`. -/
theorem abs_integral_le_pointwise {α M : ℝ} {F g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 6 g) (hM : 0 ≤ M)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) PM)
    (hpt : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ M * Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) PM ∧
      |∫ p, F p.1 p.2 ∂PM| ≤ M * Work.Spaces.HkSq α 6 g := by
  obtain ⟨hint, hle⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise hg hmemg hM haesm hpt
  obtain ⟨-, hle2⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise hg hmemg hM haesm.neg
      (fun z θ hz hθ hθ2 => by rw [abs_neg]; exact hpt z θ hz hθ hθ2)
  rw [MeasureTheory.integral_neg] at hle2
  exact ⟨hint, abs_le.mpr ⟨by linarith, hle⟩⟩

/-- **Leibniz summand, the `σ`-gain (mismatch) case: `a₁ = a ≥ 1`, `ρ = leafGam α`, `a + b₁ ≤ 2`.**

Route (all on the open quadrant, which is conull for `PM`).  `Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat`
gives `|mixed b₁ a A| ≤ 4 · Kf · sin(2θ)` whenever `Kf` bounds `|mixed b i (pth A)|` for `b+i ≤ 1`; by
`Npair6BWork.coefTh_pointwise` (from `CoefThMem 1 A` and `CoefTh 1 A ≤ K1`) one may take `Kf = K1`.
Hence `leafGam α · |mixed b₁ a A| · |D_z^{b-b₁+1} f| · |mixed b a f|
  ≤ (4K1) · (w²σ^{1-γ}) · |D_z^{b-b₁+1} f| · |mixed b a f|`
and `w²σ^{1-γ} ≤ √(canonW η · (D_z^{b-b₁+1} f)²) · √(canonW (gam α) · (mixed b a f)²)` because
`σ^{1-γ} ≤ σ^{-η/2}·σ^{-γ/2}` (`2 - γ + η ≥ 0`, true for `α ≤ 1`); both slots lie in
`HkIntegrand α 6 f` (`b-b₁+1 ≤ 6` because `a ≥ 1`; `1 ≤ a`, `a+b ≤ 6` for the mixed slot).
Conclude `≤ 4K1·HkSq α 6 f` by `cs_sqrt`/`rowSummand_core`. -/
theorem rowSumGamSin : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b b₁ : ℕ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → 1 ≤ a → b₁ ≤ b → a + b₁ ≤ 2 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a A p.1 p.2
          * Work.Spaces.DzIter (b - b₁ + 1) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a A p.1 p.2
            * Work.Spaces.DzIter (b - b₁ + 1) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * K1 * Work.Spaces.HkSq α 6 f := by
  -- the flat `∂_θ`-price is converted into the `sin(2θ)`-gain
  obtain ⟨Csin, hCsin, hgain⟩ := Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
  refine ⟨Csin, hCsin, ?_⟩
  intro α hα A f K0 K4 K6 K1 M a b b₁ hcoef hctmem hctle hdat hab ha hb1 hab1
  obtain ⟨hα0, hα1⟩ := hα
  -- `K1` is nonnegative, because it dominates `CoefTh 1 A ≥ 0`
  have hK1 : 0 ≤ K1 := le_trans (coefTh_nonneg 1 A) hctle
  have hKX0 : 0 ≤ Csin * K1 := mul_nonneg hCsin.le hK1
  -- the index facts
  have hq0 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  have hqγ : Work.Spaces.gam α - 1 ≤ Work.Spaces.gam α := by linarith
  have hqη : Work.Spaces.gam α - 1 ≤ Work.Spaces.eta := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  -- the `sin(2θ)`-gain
  have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ a A z θ| ≤ Csin * K1 * Real.sin (2 * θ) :=
    hgain A K1 hK1 hcoef.sm (coefTh_pointwise hctmem hctle) a b₁ ha hab1
  -- a.e. strong measurability of the summand
  have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed b₁ a A p.1 p.2
        * Work.Spaces.DzIter (b - b₁ + 1) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) PM :=
    (((aesm_leafW (α := α) (a := a) (Or.inr (Or.inr ⟨ha, rfl⟩))).mul
      (aesm_mixed hcoef.sm b₁ a)).mul
      (aesm_of_smoothOpen (hdat.sm.DzIter (b - b₁ + 1)))).mul
      (aesm_mixed hdat.sm b a)
  refine abs_integral_le_pointwise (M := Csin * K1)
    (F := fun z θ => Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b₁ a A z θ
        * Work.Spaces.DzIter (b - b₁ + 1) f z θ * Work.Spaces.mixed b a f z θ)
    hdat.sm hdat.h6 hKX0 haesm ?_
  intro z θ hz hθ hθ2
  have hs : 0 ≤ Real.sin (2 * θ) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
  -- the pair of `f`-slots, with the exponent `γ - 1` (which `σ` supplies)
  have hpair := Work.FTS.StrongPersist.N6Trans.canonW_pair_le6 (α := α) (g := f)
    (q := Work.Spaces.gam α - 1) (j := b - b₁ + 1) (i := 0) (b := b) (a := a)
    hq0 hqγ (fun _ => hqη) (fun h => absurd h (by omega))
    (by omega : 0 + (b - b₁ + 1) ≤ 6) hab hz.le hθI
  simp only [Work.Spaces.mixed_zero_right] at hpair
  -- the `σ`-shift `leafGam α · sin(2θ) = canonW (gam α - 1)`
  have hshift : Work.FTS.TransportS.leafGam α z θ * Real.sin (2 * θ)
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
    have hsp : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hpow : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sin (2 * θ)
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by
      calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sin (2 * θ)
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Real.sin (2 * θ)) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
        _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) + 1) :=
            (Real.rpow_add hsp (-(Work.Spaces.gam α)) 1).symm
        _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by congr 1; ring
    rw [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.leafGam, mul_assoc, hpow]
  have hlnn : 0 ≤ Work.FTS.TransportS.leafGam α z θ :=
    Work.FTS.TransportS.leafGam_nonneg α hs
  have hYnn : 0 ≤ |Work.Spaces.DzIter (b - b₁ + 1) f z θ| := abs_nonneg _
  have hZnn : 0 ≤ |Work.Spaces.mixed b a f z θ| := abs_nonneg _
  calc |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b₁ a A z θ
        * Work.Spaces.DzIter (b - b₁ + 1) f z θ * Work.Spaces.mixed b a f z θ|
      = Work.FTS.TransportS.leafGam α z θ * |Work.Spaces.mixed b₁ a A z θ|
          * |Work.Spaces.DzIter (b - b₁ + 1) f z θ| * |Work.Spaces.mixed b a f z θ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hlnn]
    _ ≤ Work.FTS.TransportS.leafGam α z θ * (Csin * K1 * Real.sin (2 * θ))
          * |Work.Spaces.DzIter (b - b₁ + 1) f z θ| * |Work.Spaces.mixed b a f z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hX z θ hz hθ hθ2) hlnn) hYnn) hZnn
    _ = Csin * K1 * (Work.FTS.TransportS.leafGam α z θ * Real.sin (2 * θ)
          * |Work.Spaces.DzIter (b - b₁ + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) := by
        ring
    _ = Csin * K1 * (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ
          * |Work.Spaces.DzIter (b - b₁ + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) := by
        rw [hshift]
    _ ≤ Csin * K1 * Work.Spaces.HkIntegrand α 6 f z θ :=
        mul_le_mul_of_nonneg_left hpair hKX0

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
