import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.hardyAngL2Integrable
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.sliceThetaHardy
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyA
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The pure `D_z`-slot estimate at the critical angular weight

`SixRoute.thetaHardyA` is the sharp angular Hardy inequality which trades the critical
weight `sin(2θ)^{-(1-α/10)}` against the *derivative* slot `sin(2θ)^{-γ}` plus the trace at
`θ = π/4`.  Here we integrate it against the radial weight `w(z)²` over `Iz`: the angular
derivative slot of the `j`-th `D_z`-slice is read through the mixed slot
`mixed j 1 f = sin(2θ) · ∂_θ(D_z^j f)`, and the trace at `θ = π/4` is controlled by
`T6Gen.tracePi4Five`.  The result is the product-measure statement consumed by the level-six
pairing (`H6Pair6Aux.T6Gen.summand_le_mismatch_gen`). -/

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_of_mem_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `(Wt α z θ)² = w(z)² · sin(2θ)^{-γ}` on `Iθ`. -/
private lemma wt_sq_eq (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ' hθ
  have hgam : Work.Spaces.gam α ≠ 0 := by
    have hg : Work.Spaces.gam α = 1 + α / 10 := rfl
    rw [hg]; intro h; linarith
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The weight identity converting the `sin(2θ)^{-γ}`-weighted mixed slot into the
`Wt`-weighted one. -/
private lemma wt_mul (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (a : ℝ) :
    (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * a ^ 2)
      = (a * Work.Spaces.Wt α z θ) ^ 2 := by
  have hW := wt_sq_eq α hα z θ hθ
  rw [mul_pow, hW]; ring

/-! ### The measure-theoretic packaging

Given a jointly a.e.-strongly-measurable `G`, the a.e. nonnegativity of its angular slices,
their a.e. integrability, and an integrable majorant `D` for the (norm of the) angular
integrals, the product integral of `G` is integrable and dominated by `∫ D`. -/

private theorem prodIterBound {G : ℝ → ℝ → ℝ} {D : ℝ → ℝ}
    (hAE : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 ≤ G z θ)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => G z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hN : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, ‖G z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) ≤ D z)
    (hDint : Integrable D (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    Integrable (fun p : ℝ × ℝ => G p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, G p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ ∫ z, D z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hnorm_int : Integrable
      (fun z => ∫ θ, ‖G z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Integrable.mono' hDint hAE.norm.integral_prod_right' (hN.mono fun z hz => by
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
      exact hz)
  have hint : Integrable (fun p : ℝ × ℝ => G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff hAE).mpr ⟨hslice, hnorm_int⟩
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.integral_prod _ hint]
  have hΦint : Integrable
      (fun z => ∫ θ, G z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Integrable.mono' hDint hAE.integral_prod_right' (hN.mono fun z hz =>
      le_trans (MeasureTheory.norm_integral_le_integral_norm (fun θ => G z θ)) hz)
  refine MeasureTheory.integral_mono_ae hΦint hDint ?_
  filter_upwards [hnn, hslice, hN] with z hz0 hz1 hz2
  exact le_trans (MeasureTheory.integral_mono_ae hz1 hz1.norm
    (hz0.mono fun θ hθ => le_of_eq (Real.norm_of_nonneg hθ).symm)) hz2

/-! ### The main estimate -/

theorem qDzLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (j : ℕ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → j ≤ 5 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
          * (Work.Spaces.DzIter j f p.1 p.2) ^ 2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
        (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
              * (Work.Spaces.DzIter j f p.1 p.2) ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          ≤ C * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₁, hC₁pos, hHardy⟩ := sliceThetaHardy
  obtain ⟨C₂, hC₂pos, hTrace⟩ := tracePi4Five
  refine ⟨12 * C₁ + C₁ * C₂ + 1, by positivity, ?_⟩
  intro α hα f j hf hmem hj
  obtain ⟨hα0, hα1⟩ := hα
  have hIθms : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzms : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hcoefnn : 0 ≤ C₁ / α ^ 2 := div_nonneg hC₁pos.le (sq_nonneg _)
  have hαinvnn : 0 ≤ α ^ (-(2 : ℝ)) := Real.rpow_nonneg hα0.le _
  -- ## the pointwise identity for the `θ`-weighted mixed slot
  have hΨid : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j 1 f z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    intro z _
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem hIθms
      (fun θ hθ => wt_mul α hα0 z θ hθ (Work.Spaces.mixed j 1 f z θ)))
  -- ## the pointwise (in `z`) bound on the angular integral
  have hΦbound : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
          * (Work.Spaces.DzIter j f z θ) ^ 2)
        ≤ C₁ / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
            + C₂ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes
      subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      have hzero : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w 0) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter j f 0 θ) ^ 2) = 0 := by
        have hfun : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter j f 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
          funext θ; rw [hw0]; ring
        rw [hfun, MeasureTheory.integral_zero]
      rw [hzero]
      exact mul_nonneg hcoefnn (add_nonneg (integral_nonneg fun θ => sq_nonneg _)
        (mul_nonneg hC₂pos.le
          (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f 0 θ)))
    · -- `z > 0`: the angular Hardy inequality applied to the slice `θ ↦ D_z^j f z θ`
      have hSH := hHardy α ⟨hα0, hα1⟩ f j hf hj hzpos
        (thetaAngIntegrable α ⟨hα0, hα1⟩ f hf hmem j hj hzpos)
      have hLHS : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter j f z θ) ^ 2)
          = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(1 - α / 10))
                * (Work.Spaces.DzIter j f z θ) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.setIntegral_congr_fun hIθms (fun θ _ => by ring)
      have hTr := hTrace α ⟨hα0, hα1⟩ f j hf hmem hj z hz
      rw [hLHS]
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter j f z θ) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * (C₁ / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed j 1 f z θ) ^ 2)
              + (Work.Spaces.DzIter j f z (Real.pi / 4)) ^ 2)) :=
            mul_le_mul_of_nonneg_left hSH (sq_nonneg _)
        _ = C₁ / α ^ 2 * ((Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed j 1 f z θ) ^ 2)
              + (Work.Spaces.DzIter j f z (Real.pi / 4)) ^ 2)) := by ring
        _ = C₁ / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
              + (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j f z (Real.pi / 4)) ^ 2) := by
            rw [mul_add, hΨid z hz]
        _ ≤ C₁ / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
              + C₂ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hcoefnn
            linarith [hTr]
  -- ## a.e. nonnegativity of the integrand on the angular slices
  have hGnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
          * (Work.Spaces.DzIter j f z θ) ^ 2 :=
    Filter.Eventually.of_forall fun _ => MeasureTheory.ae_restrict_of_forall_mem hIθms
      (fun θ hθ => mul_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _))
        (sq_nonneg _))
  -- ## a.e. integrability of the angular slices
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Integrable (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter j f z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem hIzms (fun z hz => ?_)
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      have hfun : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
          * (Work.Spaces.DzIter j f 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ; rw [hw0]; ring
      rw [hfun]
      exact integrableOn_zero
    · have hgc1 : ContDiffOn ℝ 1 (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        ((hf.DzIter j).curry_θ hzpos).of_le (by norm_num [Work.Stability.smoothOrder])
      have hInt2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)
              * deriv (fun θ' : ℝ => Work.Spaces.DzIter j f z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
        simpa only [Work.Spaces.pth] using
          thetaAngIntegrable α ⟨hα0, hα1⟩ f hf hmem j hj hzpos
      have hA := hardyAngL2Integrable α ⟨hα0, hα1⟩
        (fun θ : ℝ => Work.Spaces.DzIter j f z θ) hgc1 hInt2
      refine (hA.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      exact MeasureTheory.ae_restrict_of_forall_mem hIθms (fun θ _ => by ring)
  -- ## the majorant is integrable
  have hΨparts := mixedSlotL2 α ⟨hα0, hα1⟩ f j hf hmem hj
  have hΨint : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hΨparts.1
  have hΨle : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f := hΨparts.2
  have hIIint : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2
  have hDint : Integrable (fun z : ℝ => C₁ / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      + C₂ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hΨint.add (hIIint.const_mul C₂)).const_mul (C₁ / α ^ 2)
  -- ## joint a.e. strong measurability
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
      * (Work.Spaces.DzIter j f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
      rw [hfun]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt hp.1)
    have hsinbase : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(1 - α / 10)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      refine hsinbase.rpow_const (fun p hp => Or.inl ?_)
      have h1 : (0 : ℝ) < 2 * p.2 := by linarith [hp.2.1]
      have h2 : 2 * p.2 < Real.pi := by linarith [hp.2.2, Real.pi_pos]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
    exact ((hw.pow 2).mul hsin).mul (((hf.DzIter j).continuousOn).pow 2)
  have hAE : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
      * (Work.Spaces.DzIter j f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- ## the norm-majorant
  have hN : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, ‖(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
          * (Work.Spaces.DzIter j f z θ) ^ 2‖
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ C₁ / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
            + C₂ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem hIzms (fun z hz => ?_)
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem hIθms
      (fun θ hθ => Real.norm_of_nonneg (mul_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _))
        (sq_nonneg _))))]
    exact hΦbound z hz
  -- ## the product-measure statement
  obtain ⟨hGint, hGle⟩ := prodIterBound (G := fun z θ => (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter j f z θ) ^ 2)
    (D := fun z => C₁ / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        + C₂ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)))
    hAE hGnn hslice hN hDint
  refine ⟨hGint, ?_⟩
  refine hGle.trans ?_
  -- ## the final arithmetic
  have hIIval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ) = Work.Spaces.HkSq α 6 f := rfl
  have hDval : (∫ z in Work.Spaces.Iz, C₁ / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      + C₂ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)))
      = C₁ / α ^ 2 * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
          + C₂ * Work.Spaces.HkSq α 6 f) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hΨint (hIIint.const_mul C₂),
      MeasureTheory.integral_const_mul, hIIval]
  rw [hDval]
  calc C₁ / α ^ 2 * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        + C₂ * Work.Spaces.HkSq α 6 f)
      ≤ C₁ / α ^ 2 * (Work.Spaces.HkSq α 6 f + C₂ * Work.Spaces.HkSq α 6 f) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoefnn
        linarith [hΨle]
    _ = C₁ * (1 + C₂) * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
        rw [div_eq_mul_inv, Real.rpow_neg hα0.le (2 : ℝ), Real.rpow_two]
        ring
    _ ≤ (12 * C₁ + C₁ * C₂ + 1) * α ^ (-(2 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f) := by
        have h1 : C₁ * (1 + C₂) ≤ 12 * C₁ + C₁ * C₂ + 1 := by
          nlinarith [hC₁pos, hC₂pos]
        have h3 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
        calc C₁ * (1 + C₂) * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f
            ≤ (12 * C₁ + C₁ * C₂ + 1) * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hαinvnn) hHknn
          _ ≤ (12 * C₁ + C₁ * C₂ + 1) * α ^ (-(2 : ℝ))
                * (1 + Work.Spaces.HkSq α 6 f) :=
              mul_le_mul_of_nonneg_left h3
                (mul_nonneg (by nlinarith [hC₁pos, hC₂pos]) hαinvnn)

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
