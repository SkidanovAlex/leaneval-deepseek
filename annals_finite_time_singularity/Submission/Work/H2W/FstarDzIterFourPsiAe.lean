import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllSol.PkgK5.mixedSlotGen
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.FstarDzIterFourAe
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgJets.pinHardy
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2W.momentChainAe
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.ClassCHon.meas_bundle_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon

open MeasureTheory Set

/-- **The three measurabilities of the level-`0` energy of the mode series**, for a general
source: the a.e.-measurability of the truncated angular energy `z ↦ ∫⁻_θ ofReal (Ψ_N² w² σ)`,
of the angular density at each `z ∈ Iz`, and of the outer `lintegral`.  The only input is the
a.e.-measurability of the radial coefficients `acoeff α m F`; no regularity of `F` itself is
needed (the angular factor of each summand is the fixed continuous `eFam m`).

This is `Work.FTS.ClassCHon.CmpSupp.meas_bundle` with its unused hypotheses (`hα`, `hα1`,
`horth`, `hsm`, `hL2`) dropped; its proof (which mentions none of them) applies verbatim. -/
theorem meas_bundle_open {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hacm : ∀ m : ℕ, AEMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (∀ N : ℕ, AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    ∧ (∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  -- The proof is that of `Work.FTS.ClassCHon.CmpSupp.meas_bundle`, which mentions none of the
  -- hypotheses dropped here; we reuse its building blocks (`hkIntegrand_zero`, `measurable_w`,
  -- `measurable_sin_rpow_half`, `measurable_sEta`, `aemeasurable_psiSeries_uncurry`).
  have hzero : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0
        (Work.FTS.PhiStar.Series.psiSeries α F) z θ
      = (Work.FTS.PhiStar.Series.psiSeries α F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun z θ => CmpSupp.hkIntegrand_zero α F z θ
  -- the truncated series is jointly measurable on `Iz × Iθ`
  have hTrunc : ∀ N : ℕ, AEMeasurable
      (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    intro N
    unfold Work.FTS.PhiStar.Series.psiTrunc
    refine Finset.aemeasurable_fun_sum _ (fun m _ => ?_)
    exact ((hacm m).comp_fst).mul
      (((Work.FTS.PhiStar.Series.continuous_eFam m).measurable.comp measurable_snd).aemeasurable)
  refine ⟨?_, ?_, ?_⟩
  · -- 1. the truncated angular energy, as a function of `z`
    intro N
    have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2) ^ 2
          * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.sEta p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      refine ((hTrunc N).pow_const 2 |>.mul ?_ |>.mul ?_).ennreal_ofReal
      · exact ((CmpSupp.measurable_w.comp measurable_fst).aemeasurable).pow_const 2
      · exact (CmpSupp.measurable_sEta.comp measurable_snd).aemeasurable
    exact h1.lintegral_prod_right
  · -- 2. the angular level-`0` density, for fixed `z ∈ Iz`
    intro z _
    have hz' : AEMeasurable (fun θ : ℝ => Work.FTS.PhiStar.Series.psiSeries α F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h : AEMeasurable (fun θ : ℝ => ∑' m : ℕ,
          Work.FTS.PhiStar.Series.acoeff α m F z
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine AEMeasurable.tsum (fun m => ?_)
        exact ((continuous_const.mul
          (Work.FTS.PhiStar.Series.continuous_eFam m)).measurable).aemeasurable
      exact h
    have heq : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
        = (fun θ : ℝ => ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)) := by
      funext θ; rw [hzero]
    rw [heq]
    exact ((hz'.mul ((measurable_const.div
      (CmpSupp.measurable_sin_rpow_half.comp measurable_id)).aemeasurable)).pow_const 2).ennreal_ofReal
  · -- 3. the `z`-integral of the level-`0` density, on `(0,∞)`
    have hacm' : ∀ m : ℕ, AEMeasurable
        (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      intro m
      refine (hacm m).mono_measure ?_
      refine MeasureTheory.Measure.restrict_mono_set volume ?_
      intro z hz
      exact le_of_lt (show (0 : ℝ) < z from hz)
    have hfac : AEMeasurable (fun p : ℝ × ℝ =>
        Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      ((CmpSupp.measurable_w.comp measurable_fst).aemeasurable).div
        ((CmpSupp.measurable_sin_rpow_half.comp measurable_snd).aemeasurable)
    have hJ : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) p.1 p.2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have heq : (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
            (Work.FTS.PhiStar.Series.psiSeries α F) p.1 p.2))
          = (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F p.1 p.2
              * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)) := by
        funext p; rw [hzero]
      rw [heq]
      exact (((CmpSupp.aemeasurable_psiSeries_uncurry hacm').mul hfac).pow_const 2).ennreal_ofReal
    exact hJ.lintegral_prod_right

end Work.FTS.ClassCHon
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.CutBkAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine
namespace CutBk

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Local abbreviations -/

/-- The drift coefficient `(z-3)/(1+z)` of the radial weight identity `(z w²)' = w²·b`. -/
def cutB (z : ℝ) : ℝ := (z - 3) / (1 + z)

/-- `D_z²G + b·D_zG`, the radial factor produced by the integration by parts. -/
def cutXi (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.DzIter 2 G p.1 p.2
    + cutB p.1 * Work.Spaces.Dz G p.1 p.2

/-- `∂_θ²G`. -/
def cutD2 (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.pthIter 2 G p.1 p.2

/-- `D_zG`. -/
def cutPs (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.Dz G p.1 p.2

/-- The weight `ρ = w(z)²·thEta(θ)`. -/
def cutRho : ℝ × ℝ → ℝ :=
  fun p => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2

/-- The strip `Iz ×ˢ Iθ`. -/
def Izθ : Set (ℝ × ℝ) := Work.Spaces.Iz ×ˢ Work.Spaces.Iθ

/-- The (restricted Lebesgue) measure on the strip. -/
def Mu : Measure (ℝ × ℝ) := volume.restrict Izθ

/-! ## Elementary facts -/

lemma thEta_zero : Work.FTS.EllipticEst.thEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.thEta, mul_zero, Real.sin_zero]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

lemma thEta_piHalf : Work.FTS.EllipticEst.thEta (π / 2) = 0 := by
  have h2 : 2 * (π / 2) = π := by ring
  rw [Work.FTS.EllipticEst.thEta, h2, Real.sin_pi]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

lemma measurableSet_Izθ : MeasurableSet Izθ := by
  rw [Izθ, Work.Spaces.Iz, Work.Spaces.Iθ]
  exact measurableSet_Ici.prod measurableSet_Icc

lemma Mu_eq_prod :
    Mu = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [Mu, Izθ, Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- The set integral over the strip is the integral for the product of the two restricted
measures. -/
lemma setIntegral_Izθ_eq_prod {f : ℝ × ℝ → ℝ} :
    (∫ p in Izθ, f p)
      = ∫ p, f p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  show (∫ p, f p ∂Mu) = _
  rw [Mu_eq_prod]

/-- A pointwise statement on the strip is an almost-everywhere statement. -/
lemma ae_of_mem_Izθ {P : ℝ × ℝ → Prop} (h : ∀ p ∈ Izθ, P p) :
    ∀ᵐ p ∂Mu, P p := by
  rw [Mu, ae_restrict_iff' measurableSet_Izθ]
  exact Eventually.of_forall h

/-- A pointwise statement on `Iθ` is an almost-everywhere statement. -/
lemma ae_of_mem_Iθ {P : ℝ → Prop} (h : ∀ θ ∈ Work.Spaces.Iθ, P θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), P θ := by
  rw [ae_restrict_iff' measurableSet_Iθ]
  exact Eventually.of_forall h

/-- `cutRho` is nonnegative on the strip. -/
lemma cutRho_nonneg {p : ℝ × ℝ} (hp : p ∈ Izθ) : 0 ≤ cutRho p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hp.2)

/-- `cutRho (0,θ) = 0`: the radial weight vanishes at `z = 0`. -/
lemma cutRho_zero_fst (θ : ℝ) : cutRho (0, θ) = 0 := by
  simp [cutRho, Work.Spaces.w]

/-! ## Continuity on the open quadrant -/

lemma contOn_comp_fst {f : ℝ → ℝ} {s t : Set ℝ} (hf : ContinuousOn f s) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1) (s ×ˢ t) := by
  have hmap : Set.MapsTo (Prod.fst : ℝ × ℝ → ℝ) (s ×ˢ t) s := fun p hp => hp.1
  have h := hf.comp continuousOn_fst hmap
  simpa only [Function.comp_def] using h

lemma contOn_comp_snd {f : ℝ → ℝ} {s t : Set ℝ} (hf : ContinuousOn f s) :
    ContinuousOn (fun p : ℝ × ℝ => f p.2) (t ×ˢ s) := by
  have hmap : Set.MapsTo (Prod.snd : ℝ × ℝ → ℝ) (t ×ˢ s) s := fun p hp => hp.2
  have h := hf.comp continuousOn_snd hmap
  simpa only [Function.comp_def] using h

lemma continuousOn_cutB_comp :
    ContinuousOn (fun p : ℝ × ℝ => cutB p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h : ContinuousOn (fun z : ℝ => (z - 3) / (1 + z)) (Set.Ioi 0) := by
    refine ContinuousOn.div (continuousOn_id.sub continuousOn_const)
      (continuousOn_const.add continuousOn_id) ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    linarith
  have h2 := contOn_comp_fst (t := Set.Ioo (0 : ℝ) (π / 2)) h
  simpa only [cutB] using h2

lemma continuousOn_cutRho :
    ContinuousOn cutRho (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hmain : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.mul ?_ ?_
    · have h : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := by
        refine ContinuousOn.pow (ContinuousOn.div
          ((continuousOn_const.add continuousOn_id).pow 2) (continuousOn_id.pow 2) ?_) 2
        intro z hz
        exact pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < z from hz))
      have h2 := contOn_comp_fst (t := Set.Ioo (0 : ℝ) (π / 2)) h
      simpa only [Work.Spaces.w] using h2
    · have h : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          (Set.Ioo 0 (π / 2)) := by
        refine ContinuousOn.rpow_const
          ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
        intro θ hθ
        left
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))
      have h2 := contOn_comp_snd (t := Set.Ioi (0 : ℝ)) h
      simpa only [Work.FTS.EllipticEst.thEta] using h2
  exact hmain

lemma continuousOn_cutXi {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ContinuousOn (cutXi G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hmain : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 2 G p.1 p.2
      + cutB p.1 * Work.Spaces.Dz G p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.add (hG.DzIter 2).continuousOn ?_
    exact continuousOn_cutB_comp.mul (hG.Dz).continuousOn
  exact hmain

lemma continuousOn_cutD2 {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ContinuousOn (cutD2 G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (hG.pth.pth).continuousOn

lemma continuousOn_cutPs {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ContinuousOn (cutPs G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (hG.Dz).continuousOn

lemma continuousOn_cutChi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => χ k p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h1 : ContDiffOn ℝ 1 (χ k) (Set.Ioi 0) :=
    (hχ.sm k).of_le (by simp [Work.Stability.smoothOrder])
  exact contOn_comp_fst (t := Set.Ioo (0 : ℝ) (π / 2)) h1.continuousOn

lemma continuousOn_cutDchi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (χ k) p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h1 : ContDiffOn ℝ 1 (χ k) (Set.Ioi 0) :=
    (hχ.sm k).of_le (by simp [Work.Stability.smoothOrder])
  have hd : ContinuousOn (fun z : ℝ => deriv (χ k) z) (Set.Ioi 0) :=
    h1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  exact contOn_comp_fst (t := Set.Ioo (0 : ℝ) (π / 2)) hd

/-! ## A.e. strong measurability of the joint integrands -/

lemma aesm_of_Qd {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) : AEStronglyMeasurable g Mu := by
  rw [Mu_eq_prod]
  exact Work.Spaces.aesm_of_continuousOn_Qd g hg

lemma aesm_cutPsi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p) Mu :=
  aesm_of_Qd ((continuousOn_cutRho.mul (continuousOn_cutChi hχ k)).mul
    (continuousOn_cutXi hG) |>.mul (continuousOn_cutD2 hG))

lemma aesm_cutPsiB {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) Mu :=
  aesm_of_Qd ((((continuousOn_fst.mul (continuousOn_cutDchi hχ k)).mul continuousOn_cutRho).mul
    (continuousOn_cutPs hG)).mul (continuousOn_cutD2 hG))

/-! ## Cauchy–Schwarz in `L²` with an a.e.-nonnegative weight -/

lemma csSqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} {ρ Ξ Φ : α → ℝ}
    (hρ : 0 ≤ ρ) (hΞ : Integrable (fun x => ρ x * Ξ x ^ 2) μ)
    (hΦ : Integrable (fun x => ρ x * Φ x ^ 2) μ) :
    Integrable (fun x => ρ x * |Ξ x| * |Φ x|) μ
      ∧ (∫ x, ρ x * |Ξ x| * |Φ x| ∂μ)
        ≤ Real.sqrt (∫ x, ρ x * Ξ x ^ 2 ∂μ) * Real.sqrt (∫ x, ρ x * Φ x ^ 2 ∂μ) := by
  set f : α → ℝ := fun x => Real.sqrt (ρ x * Ξ x ^ 2) with hf
  set g : α → ℝ := fun x => Real.sqrt (ρ x * Φ x ^ 2) with hg
  have hfm : AEStronglyMeasurable f μ :=
    (hΞ.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g μ :=
    (hΦ.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hf2 : (fun x => f x ^ 2) = fun x => ρ x * Ξ x ^ 2 := by
    funext x; rw [hf]; exact Real.sq_sqrt (mul_nonneg (hρ x) (sq_nonneg _))
  have hg2 : (fun x => g x ^ 2) = fun x => ρ x * Φ x ^ 2 := by
    funext x; rw [hg]; exact Real.sq_sqrt (mul_nonneg (hρ x) (sq_nonneg _))
  have hfmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).mpr (by rw [hf2]; exact hΞ)
  have hgmem : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm).mpr (by rw [hg2]; exact hΦ)
  have hsq : ∀ x, f x * g x = ρ x * |Ξ x| * |Φ x| := by
    intro x
    have h1 : Real.sqrt (ρ x * Ξ x ^ 2) * Real.sqrt (ρ x * Φ x ^ 2)
        = Real.sqrt ((ρ x * Ξ x ^ 2) * (ρ x * Φ x ^ 2)) :=
      (Real.sqrt_mul (mul_nonneg (hρ x) (sq_nonneg _)) _).symm
    rw [hf, hg, h1]
    have h2 : (ρ x * Ξ x ^ 2) * (ρ x * Φ x ^ 2) = (ρ x * |Ξ x| * |Φ x|) ^ 2 := by
      rw [← sq_abs (Ξ x), ← sq_abs (Φ x)]
      ring
    rw [h2, Real.sqrt_sq]
    exact mul_nonneg (mul_nonneg (hρ x) (abs_nonneg _)) (abs_nonneg _)
  have hfun : (fun x => f x * g x) = fun x => ρ x * |Ξ x| * |Φ x| := funext hsq
  have hdom : Integrable (fun x => (1 / 2) * (ρ x * Ξ x ^ 2 + ρ x * Φ x ^ 2)) μ :=
    (hΞ.add hΦ).const_mul (1 / 2)
  have hInt : Integrable (fun x => f x * g x) μ := by
    refine Integrable.mono' hdom (hfm.mul hgm) (Eventually.of_forall fun x => ?_)
    have hnn : (0 : ℝ) ≤ f x * g x := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_of_nonneg hnn, hsq]
    have hxn : (0 : ℝ) ≤ ρ x := hρ x
    have hΞx : (0 : ℝ) ≤ |Ξ x| := abs_nonneg _
    have hΦx : (0 : ℝ) ≤ |Φ x| := abs_nonneg _
    have hsq1 : |Ξ x| ^ 2 = Ξ x ^ 2 := sq_abs (Ξ x)
    have hsq2 : |Φ x| ^ 2 = Φ x ^ 2 := sq_abs (Φ x)
    nlinarith [sq_nonneg (|Ξ x| - |Φ x|)]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (f := f) (g := g)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (by simpa using hfmem) (by simpa using hgmem)
  have hf2' : (∫ x, f x ^ (2 : ℝ) ∂μ) = ∫ x, ρ x * Ξ x ^ 2 ∂μ := by
    rw [show (fun x => f x ^ (2 : ℝ)) = fun x => ρ x * Ξ x ^ 2 from by
      funext x; rw [Real.rpow_two]; exact congrFun hf2 x]
  have hg2' : (∫ x, g x ^ (2 : ℝ) ∂μ) = ∫ x, ρ x * Φ x ^ 2 ∂μ := by
    rw [show (fun x => g x ^ (2 : ℝ)) = fun x => ρ x * Φ x ^ 2 from by
      funext x; rw [Real.rpow_two]; exact congrFun hg2 x]
  refine ⟨by rwa [hfun] at hInt, ?_⟩
  calc (∫ x, ρ x * |Ξ x| * |Φ x| ∂μ)
      = ∫ x, f x * g x ∂μ := by rw [hfun]
    _ ≤ (∫ x, f x ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)
          * (∫ x, g x ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := hholder
    _ = Real.sqrt (∫ x, ρ x * Ξ x ^ 2 ∂μ) * Real.sqrt (∫ x, ρ x * Φ x ^ 2 ∂μ) := by
        rw [hf2', hg2', Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-! ## Cauchy–Schwarz with an only-a.e.-nonnegative weight -/

lemma csSqrt_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {ρ Ξ Φ : α → ℝ}
    (hρ : 0 ≤ᵐ[μ] ρ) (hΞ : Integrable (fun x => ρ x * Ξ x ^ 2) μ)
    (hΦ : Integrable (fun x => ρ x * Φ x ^ 2) μ) :
    Integrable (fun x => ρ x * |Ξ x| * |Φ x|) μ
      ∧ (∫ x, ρ x * |Ξ x| * |Φ x| ∂μ)
        ≤ Real.sqrt (∫ x, ρ x * Ξ x ^ 2 ∂μ) * Real.sqrt (∫ x, ρ x * Φ x ^ 2 ∂μ) := by
  set ρ' : α → ℝ := fun x => max 0 (ρ x) with hρ'
  have hρ'nn : 0 ≤ ρ' := fun x => le_max_left _ _
  have hae : ρ' =ᵐ[μ] ρ := hρ.mono fun x hx => by
    simp only [hρ', Pi.zero_apply] at *
    exact max_eq_right hx
  have hΞ' : Integrable (fun x => ρ' x * Ξ x ^ 2) μ :=
    hΞ.congr (hae.symm.mul EventuallyEq.rfl)
  have hΦ' : Integrable (fun x => ρ' x * Φ x ^ 2) μ :=
    hΦ.congr (hae.symm.mul EventuallyEq.rfl)
  obtain ⟨hint, hle⟩ := csSqrt hρ'nn hΞ' hΦ'
  have hfun : (fun x => ρ' x * |Ξ x| * |Φ x|) =ᵐ[μ] (fun x => ρ x * |Ξ x| * |Φ x|) :=
    (hae.mul EventuallyEq.rfl).mul EventuallyEq.rfl
  have hfun2 : (fun x => ρ' x * Ξ x ^ 2) =ᵐ[μ] (fun x => ρ x * Ξ x ^ 2) := hae.mul EventuallyEq.rfl
  have hfun3 : (fun x => ρ' x * Φ x ^ 2) =ᵐ[μ] (fun x => ρ x * Φ x ^ 2) := hae.mul EventuallyEq.rfl
  refine ⟨hint.congr hfun, ?_⟩
  rw [integral_congr_ae hfun, integral_congr_ae hfun2, integral_congr_ae hfun3] at hle
  exact hle


/-! ## Pointwise bounds for the two joint integrands -/

lemma log_k_pos (k : ℕ) : 0 < Real.log ((k : ℝ) + 2) := by
  refine Real.log_pos ?_
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

lemma abs_cutPsi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    |cutRho p * χ k p.1 * cutXi G p * cutD2 G p|
      = cutRho p * |χ k p.1| * |cutXi G p| * |cutD2 G p| := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (cutRho_nonneg hp)]

lemma abs_cutPsi_le {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    |cutRho p * χ k p.1 * cutXi G p * cutD2 G p|
      ≤ cutRho p * |cutXi G p| * |cutD2 G p| := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ p.1 from hp.1) with h0 | hpos
  · have hp0 : p = (0, p.2) := Prod.ext h0.symm rfl
    rw [hp0, cutRho_zero_fst]
    simp
  · have hb := hχ.bnd k p.1 hpos
    have hρnn : (0 : ℝ) ≤ cutRho p := cutRho_nonneg hp
    have hχa : |χ k p.1| ≤ 1 := abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
    rw [abs_cutPsi hχ k hp]
    calc cutRho p * |χ k p.1| * |cutXi G p| * |cutD2 G p|
        = (cutRho p * |cutXi G p| * |cutD2 G p|) * |χ k p.1| := by ring
      _ ≤ (cutRho p * |cutXi G p| * |cutD2 G p|) * 1 :=
          mul_le_mul_of_nonneg_left hχa
            (mul_nonneg (mul_nonneg hρnn (abs_nonneg _)) (abs_nonneg _))
      _ = cutRho p * |cutXi G p| * |cutD2 G p| := by ring

lemma cutPsi_le_abs {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    cutRho p * χ k p.1 * cutXi G p * cutD2 G p
      ≤ cutRho p * |cutXi G p| * |cutD2 G p| :=
  le_trans (le_abs_self _) (abs_cutPsi_le hχ k hp)

lemma abs_cutPsiB {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    |(p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p|
      = |p.1 * deriv (χ k) p.1| * cutRho p * |cutPs G p| * |cutD2 G p| := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (cutRho_nonneg hp)]

lemma abs_cutPsiB_le {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    |(p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p|
      ≤ (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|) := by
  have hKL : 0 ≤ K / Real.log ((k : ℝ) + 2) := div_nonneg hχ.K0 (log_k_pos k).le
  have hle : |p.1 * deriv (χ k) p.1| ≤ K / Real.log ((k : ℝ) + 2) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ p.1 from hp.1) with h0 | hpos
    · rw [← h0, zero_mul, abs_zero]; exact hKL
    · exact hχ.d1 k p.1 hpos
  have hρnn : (0 : ℝ) ≤ cutRho p := cutRho_nonneg hp
  have hPx : (0 : ℝ) ≤ |cutPs G p| := abs_nonneg _
  have hDx : (0 : ℝ) ≤ |cutD2 G p| := abs_nonneg _
  rw [abs_cutPsiB hχ k hp]
  calc |p.1 * deriv (χ k) p.1| * cutRho p * |cutPs G p| * |cutD2 G p|
      = |p.1 * deriv (χ k) p.1| * (cutRho p * |cutPs G p| * |cutD2 G p|) := by ring
    _ ≤ (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|) :=
        mul_le_mul_of_nonneg_right hle (mul_nonneg (mul_nonneg hρnn hPx) hDx)

lemma cutPsiB_le {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p
      ≤ (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|) :=
  le_trans (le_abs_self _) (abs_cutPsiB_le hχ k hp)

lemma amgm_le {a b ρ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : 0 ≤ ρ) :
    ρ * a * b ≤ (1 / 2) * (ρ * a ^ 2 + ρ * b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-! ## Integrability of the two joint integrands -/

lemma integrable_cutPsi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hXi : Integrable (fun p : ℝ × ℝ => cutRho p * cutXi G p ^ 2) Mu)
    (hT : Integrable (fun p : ℝ × ℝ => cutRho p * cutD2 G p ^ 2) Mu) :
    Integrable (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p) Mu := by
  refine Integrable.mono' ((hXi.add hT).const_mul (1 / 2)) (aesm_cutPsi hχ k hG) ?_
  refine ae_of_mem_Izθ (fun p hp => ?_)
  show ‖cutRho p * χ k p.1 * cutXi G p * cutD2 G p‖
      ≤ 1 / 2 * (cutRho p * cutXi G p ^ 2 + cutRho p * cutD2 G p ^ 2)
  have h1 : ‖cutRho p * χ k p.1 * cutXi G p * cutD2 G p‖
      ≤ cutRho p * |cutXi G p| * |cutD2 G p| :=
    le_trans (le_of_eq (Real.norm_eq_abs _)) (abs_cutPsi_le hχ k hp)
  have hsq1 : |cutXi G p| ^ 2 = cutXi G p ^ 2 := sq_abs _
  have hsq2 : |cutD2 G p| ^ 2 = cutD2 G p ^ 2 := sq_abs _
  have h2 : cutRho p * |cutXi G p| * |cutD2 G p|
      ≤ (1 / 2) * (cutRho p * cutXi G p ^ 2 + cutRho p * cutD2 G p ^ 2) := by
    have h := amgm_le (a := |cutXi G p|) (b := |cutD2 G p|) (ρ := cutRho p)
      (abs_nonneg _) (abs_nonneg _) (cutRho_nonneg hp)
    rwa [hsq1, hsq2] at h
  linarith

lemma integrable_cutPsiB {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hD : Integrable (fun p : ℝ × ℝ => cutRho p * cutPs G p ^ 2) Mu)
    (hT : Integrable (fun p : ℝ × ℝ => cutRho p * cutD2 G p ^ 2) Mu) :
    Integrable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) Mu := by
  have hKL : 0 ≤ K / Real.log ((k : ℝ) + 2) := div_nonneg hχ.K0 (log_k_pos k).le
  refine Integrable.mono'
    (((hD.add hT).const_mul (1 / 2)).const_mul (K / Real.log ((k : ℝ) + 2)))
    (aesm_cutPsiB hχ k hG) ?_
  refine ae_of_mem_Izθ (fun p hp => ?_)
  show ‖(p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p‖
      ≤ K / Real.log ((k : ℝ) + 2)
        * (1 / 2 * (cutRho p * cutPs G p ^ 2 + cutRho p * cutD2 G p ^ 2))
  have h3 : ‖(p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p‖
      ≤ (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|) :=
    le_trans (le_of_eq (Real.norm_eq_abs _)) (abs_cutPsiB_le hχ k hp)
  have hsq1 : |cutPs G p| ^ 2 = cutPs G p ^ 2 := sq_abs _
  have hsq2 : |cutD2 G p| ^ 2 = cutD2 G p ^ 2 := sq_abs _
  have h2 : (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|)
      ≤ (K / Real.log ((k : ℝ) + 2))
        * (1 / 2 * (cutRho p * cutPs G p ^ 2 + cutRho p * cutD2 G p ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hKL
    have h := amgm_le (a := |cutPs G p|) (b := |cutD2 G p|) (ρ := cutRho p)
      (abs_nonneg _) (abs_nonneg _) (cutRho_nonneg hp)
    rwa [hsq1, hsq2] at h
  linarith

end CutBk
end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.massK_tendsto_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem massK_tendsto_zero {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    (htr0 : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => ψ z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htr1 : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hE : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ Work.Spaces.Iθ)) :
    Filter.Tendsto (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by

  have ha : 0 < Work.FTS.EllSol.PkgK5.cA k := Work.FTS.EllSol.PkgK5.cA_pos k
  have hab : Work.FTS.EllSol.PkgK5.cA k ≤ Work.FTS.EllSol.PkgK5.cB k :=
    Work.FTS.EllSol.PkgK5.cA_le_cB k
  -- the angular weight is nonnegative on `Iθ`
  have hthnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have h2 : (0 : ℝ) ≤ 2 * θ := by linarith [hθ.1]
    have hpi : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨h2, hpi⟩) _
  set M : ℝ := ∫ p in (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) ×ˢ
      Work.Spaces.Iθ),
      (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2
    with hM
  obtain ⟨hiter, -, hIntIθ, hIntLp, hIntRp⟩ := massK_iterated_eq (k := k) (ψ := ψ) hE
  -- the a.e. slice integrability on `Iθ` (this is the `prod_right_ae` of `hE`)
  have hzmem' : ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
      z ∈ Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k) :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  have haeIθ : ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
      MeasureTheory.Integrable (fun s : ℝ => (Work.Spaces.pth ψ z s) ^ 2 *
        Work.FTS.EllipticEst.thEta s) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 *
        (Work.Spaces.pth ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
        ((MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k)
            (Work.FTS.EllSol.PkgK5.cB k))).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      exact hE
    filter_upwards [h1.prod_right_ae, hzmem'] with z hz hzm
    have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
    have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      rw [Work.Spaces.w]
      exact pow_ne_zero 2 (div_ne_zero (by positivity) (pow_ne_zero 2 (ne_of_gt hzpos)))
    have h2 : MeasureTheory.Integrable (fun s : ℝ => (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hz.congr (Filter.Eventually.of_forall (fun s => by ring))
    have h3 := h2.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)
    refine h3.congr (Filter.Eventually.of_forall (fun s => ?_))
    exact inv_mul_cancel_left₀ hwne _
  have haeIoo : ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
      MeasureTheory.IntegrableOn (fun s : ℝ => (Work.Spaces.pth ψ z s) ^ 2 *
        Work.FTS.EllipticEst.thEta s) (Set.Ioo 0 (Real.pi / 2)) := by
    filter_upwards [haeIθ] with z hz
    exact MeasureTheory.IntegrableOn.mono_set hz
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  -- the key two-sided bound
  have key : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ θ * M ∧
      (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ (Real.pi / 2 - θ) * M ∧
      (0 ≤ ∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθpi : θ < Real.pi / 2 := hθ.2
    have hθnn : 0 ≤ θ := le_of_lt hθ0
    have hconv : (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2)
        = ∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
      rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
    -- the slice bounds, a.e. in `z`
    have hbdL : ∀ᵐ z ∂(MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
        ψ z θ ^ 2 ≤ θ * ∫ s in Set.Ioo 0 θ,
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s := by
      filter_upwards [haeIoo, hzmem'] with z hzint hzm
      have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
      have hf : ContDiffOn ℝ 1 (fun s => ψ z s) (Set.Ioo 0 (Real.pi / 2)) :=
        (hψ.curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
      exact (slice_rate_thEta (fun s => ψ z s) hf (htr0 z hzpos) (htr1 z hzpos) hzint).1 θ hθ
    have hbdR : ∀ᵐ z ∂(MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
        ψ z θ ^ 2 ≤ (Real.pi / 2 - θ) * ∫ s in Set.Ioo θ (Real.pi / 2),
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s := by
      filter_upwards [haeIoo, hzmem'] with z hzint hzm
      have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
      have hf : ContDiffOn ℝ 1 (fun s => ψ z s) (Set.Ioo 0 (Real.pi / 2)) :=
        (hψ.curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
      exact (slice_rate_thEta (fun s => ψ z s) hf (htr0 z hzpos) (htr1 z hzpos) hzint).2 θ hθ
    -- integrability of the two dominating functions
    have hIntL : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        (θ * ∫ s in Set.Ioo 0 θ, (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))) :=
      ((hIntLp θ hθ).const_mul θ).congr (Filter.Eventually.of_forall (fun z => by ring))
    have hIntR : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        ((Real.pi / 2 - θ) * ∫ s in Set.Ioo θ (Real.pi / 2),
          (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))) :=
      ((hIntRp θ hθ).const_mul (Real.pi / 2 - θ)).congr
        (Filter.Eventually.of_forall (fun z => by ring))
    -- nonnegativity of the mass integrand a.e.
    have hnn_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))]
        (fun z : ℝ => χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) := by
      filter_upwards [hzmem'] with z hzm
      have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
      exact mul_nonneg (mul_nonneg (hχ.bnd k z hzpos).1 (sq_nonneg _)) (sq_nonneg _)
    -- integrability of the dominating functions: only the `Iθ`-integral is used
    have hIntL : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        (θ * ∫ s in Work.Spaces.Iθ, (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))) :=
      (hIntIθ.const_mul θ).congr (Filter.Eventually.of_forall (fun z => by ring))
    have hIntR : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        ((Real.pi / 2 - θ) * ∫ s in Work.Spaces.Iθ, (Work.Spaces.pth ψ z s) ^ 2 *
          Work.FTS.EllipticEst.thEta s))
        (MeasureTheory.volume.restrict (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))) :=
      (hIntIθ.const_mul (Real.pi / 2 - θ)).congr (Filter.Eventually.of_forall (fun z => by ring))
    -- the inner-integral monotonicity: `Ioo 0 θ ⊆ Iθ` resp. `Ioo θ (π/2) ⊆ Iθ`
    have hinnerL : ∀ᵐ z ∂(MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
        (∫ s in Set.Ioo 0 θ, (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
          ≤ (∫ s in Work.Spaces.Iθ, (Work.Spaces.pth ψ z s) ^ 2 *
              Work.FTS.EllipticEst.thEta s) := by
      filter_upwards [haeIθ] with z hz
      refine MeasureTheory.setIntegral_mono_set hz ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
        exact mul_nonneg (sq_nonneg _) (hthnn s hs)
      · filter_upwards with s hs
        exact ⟨le_of_lt hs.1, le_of_lt (lt_trans hs.2 hθpi)⟩
    have hinnerR : ∀ᵐ z ∂(MeasureTheory.volume.restrict
        (Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k))),
        (∫ s in Set.Ioo θ (Real.pi / 2), (Work.Spaces.pth ψ z s) ^ 2 *
            Work.FTS.EllipticEst.thEta s)
          ≤ (∫ s in Work.Spaces.Iθ, (Work.Spaces.pth ψ z s) ^ 2 *
              Work.FTS.EllipticEst.thEta s) := by
      filter_upwards [haeIθ] with z hz
      refine MeasureTheory.setIntegral_mono_set hz ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
        exact mul_nonneg (sq_nonneg _) (hthnn s hs)
      · filter_upwards with s hs
        exact ⟨le_of_lt (lt_trans hθ0 hs.1), le_of_lt hs.2⟩
    -- the left bound
    have hboundL : (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ θ * M := by
      have hsym : (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
            (Work.Spaces.w z) ^ 2 * (θ * ∫ s in Work.Spaces.Iθ,
              (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
          = θ * ∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
              (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iθ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
      have hmono := MeasureTheory.integral_mono_of_nonneg hnn_ae hIntL ?_
      · rw [hsym] at hmono
        rw [hM, ← hiter]
        exact hmono
      · filter_upwards [hbdL, hzmem', hinnerL] with z hzbd hzm hzin
        have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
        have hχ1 : χ k z ≤ 1 := (hχ.bnd k z hzpos).2
        have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have hψ2 : 0 ≤ ψ z θ ^ 2 := sq_nonneg _
        calc χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
              have h := mul_le_mul_of_nonneg_right hχ1 (mul_nonneg hw hψ2)
              simpa only [one_mul, mul_assoc] using h
          _ ≤ (Work.Spaces.w z) ^ 2 * (θ * ∫ s in Set.Ioo 0 θ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
              mul_le_mul_of_nonneg_left hzbd hw
          _ ≤ (Work.Spaces.w z) ^ 2 * (θ * ∫ s in Work.Spaces.Iθ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzin hθnn) hw
    -- the right bound
    have hboundR : (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ (Real.pi / 2 - θ) * M := by
      have hsym : (∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k),
            (Work.Spaces.w z) ^ 2 * ((Real.pi / 2 - θ) * ∫ s in Work.Spaces.Iθ,
              (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s))
          = (Real.pi / 2 - θ) * ∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k)
              (Work.FTS.EllSol.PkgK5.cB k),
              (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iθ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
      have hmono := MeasureTheory.integral_mono_of_nonneg hnn_ae hIntR ?_
      · rw [hsym] at hmono
        rw [hM, ← hiter]
        exact hmono
      · filter_upwards [hbdR, hzmem', hinnerR] with z hzbd hzm hzin
        have hzpos : 0 < z := lt_of_lt_of_le ha hzm.1
        have hχ1 : χ k z ≤ 1 := (hχ.bnd k z hzpos).2
        have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have hψ2 : 0 ≤ ψ z θ ^ 2 := sq_nonneg _
        have hπ : 0 ≤ Real.pi / 2 - θ := by linarith [Real.pi_pos]
        calc χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
              have h := mul_le_mul_of_nonneg_right hχ1 (mul_nonneg hw hψ2)
              simpa only [one_mul, mul_assoc] using h
          _ ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2 - θ) * ∫ s in Set.Ioo θ (Real.pi / 2),
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
              mul_le_mul_of_nonneg_left hzbd hw
          _ ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2 - θ) * ∫ s in Work.Spaces.Iθ,
                (Work.Spaces.pth ψ z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzin hπ) hw

    have hmnn : 0 ≤ ∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun u hu => by
        have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
        exact mul_nonneg (mul_nonneg (hχ.bnd k u hu0).1 (sq_nonneg _)) (sq_nonneg _))
    refine ⟨?_, ?_, hmnn⟩
    · rw [hconv]; exact hboundL
    · rw [hconv]; exact hboundR
  -- the two filters
  have hIOl : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    have h1 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show (0:ℝ) < Real.pi / 2 by linarith [Real.pi_pos]))
    have h2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
    exact Filter.mem_of_superset (Filter.inter_mem h2 h1) (fun x hx => ⟨hx.1, hx.2⟩)
  have hIOr : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    have h1 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show (0:ℝ) < Real.pi / 2 by linarith [Real.pi_pos]))
    have h2 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      self_mem_nhdsWithin
    exact Filter.mem_of_superset (Filter.inter_mem h1 h2) (fun x hx => ⟨hx.1, hx.2⟩)
  have hnn_left : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ ∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
    filter_upwards [hIOl] with θ hθ
    exact (key θ hθ).2.2
  have hbnd_left : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ θ * M := by
    filter_upwards [hIOl] with θ hθ
    exact (key θ hθ).1
  have htend_left : Filter.Tendsto (fun θ : ℝ => θ * M)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h1.mul_const M
  have hnn_right : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      0 ≤ ∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2 := by
    filter_upwards [hIOr] with θ hθ
    exact (key θ hθ).2.2
  have hbnd_right : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      (∫ z in Work.FTS.EllSol.PkgK5.cA k..Work.FTS.EllSol.PkgK5.cB k,
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2) ≤ (Real.pi / 2 - θ) * M := by
    filter_upwards [hIOr] with θ hθ
    exact (key θ hθ).2.1
  have htend_right : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) * M)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2))
          (nhds (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
      simpa using h2.mono_left nhdsWithin_le_nhds
    simpa using h1.mul_const M
  exact ⟨squeeze_zero' hnn_left hbnd_left htend_left,
    squeeze_zero' hnn_right hbnd_right htend_right⟩

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.mixedSlotAll =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The bundled level-`i` bound holds for every `i ≥ 1`. -/
theorem levelBnd_all : ∀ i : ℕ, 1 ≤ i → LevelBnd i := by
  intro i
  refine Nat.strong_induction_on i ?_
  intro i ih hi
  rcases eq_or_lt_of_le hi with h1 | h2
  · subst h1
    exact levelBnd_one
  · have hi1 : 1 ≤ i - 1 := by omega
    exact levelBnd_step i (by omega) (ih (i - 1) (by omega) hi1)

/-- **The mixed angular slot bound at level `i`.** -/
theorem mixedSlotLevel (i : ℕ) (hi : 1 ≤ i) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)) →
      Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (etaInt h) Work.Spaces.Iθ →
      (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn (gamInt α m h) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ ∧
      pLhs α i h ≤ C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
  obtain ⟨C, hCpos, hC⟩ := levelBnd_all i hi
  exact ⟨C, hCpos, fun α h hα hα1 hsm h0 hπ hD hG =>
    hC α h hα hα1 hsm h0 hπ hD hG i hi le_rfl⟩

/-- **The general-`k` mixed slot bound** in the shape required by the per-slice division
estimate: a single constant `C` serves all levels `i ≤ k`. -/
theorem mixedSlotBoundGenK (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        Work.Spaces.Iθ →
      ∀ i : ℕ, 1 ≤ i → i ≤ k →
        (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  have hex : ∀ i : ℕ, 1 ≤ i → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
        ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)) →
        Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
        Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
        MeasureTheory.IntegrableOn (etaInt h) Work.Spaces.Iθ →
        (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn (gamInt α m h) Work.Spaces.Iθ) →
        MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ ∧
        pLhs α i h ≤ C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) :=
    fun i hi => mixedSlotLevel i hi
  let Kf : ℕ → ℝ := fun i => if hi : 1 ≤ i then (hex i hi).choose else 1
  have hKf : ∀ i (hi : 1 ≤ i), 0 < Kf i ∧
      ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
        ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)) →
        Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
        Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
        MeasureTheory.IntegrableOn (etaInt h) Work.Spaces.Iθ →
        (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn (gamInt α m h) Work.Spaces.Iθ) →
        MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ ∧
        pLhs α i h ≤ Kf i * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
    intro i hi
    have h1 : Kf i = (hex i hi).choose := by
      dsimp only [Kf]
      exact dif_pos hi
    rw [h1]
    exact (hex i hi).choose_spec
  have hnn : ∀ j ∈ Finset.Icc 1 k, 0 ≤ Kf j := fun j hj =>
    le_of_lt (hKf j (Finset.mem_Icc.mp hj).1).1
  have hSnn : 0 ≤ ∑ j ∈ Finset.Icc 1 k, Kf j := Finset.sum_nonneg hnn
  refine ⟨(∑ j ∈ Finset.Icc 1 k, Kf j) + 1, by linarith, ?_⟩
  intro α h hα hα1 hsm h0 hπ hD i hi1 hik hG
  obtain ⟨hpos, hb⟩ := hKf i hi1
  obtain ⟨hint, hbd⟩ := hb α h hα hα1 hsm h0 hπ hD hG
  have hle : Kf i ≤ (∑ j ∈ Finset.Icc 1 k, Kf j) + 1 := by
    have hsingle := Finset.single_le_sum hnn (Finset.mem_Icc.mpr ⟨hi1, hik⟩)
    linarith
  have hXnn : 0 ≤ pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h :=
    add_nonneg (pEta_nonneg h) (Finset.sum_nonneg (fun m _ => pGam_nonneg α m h))
  refine ⟨?_, ?_⟩
  · change MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ
    exact hint
  · change pLhs α i h ≤ ((∑ j ∈ Finset.Icc 1 k, Kf j) + 1)
        * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h)
    exact hbd.trans (mul_le_mul_of_nonneg_right hle hXnn)

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.PsiFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 3200000

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-! ## Elementary interval bookkeeping -/



/-! ## Continuity of the partial sums on the open quadrant -/

/-- The mode-`m` term of the partial sum is continuous on the open quadrant. -/
theorem continuousOn_acoeff_mul_eFam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.acoeff α m F p.1 *
      Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Work.FTS.EllipticEst.Q0 := by
  have hc : MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0) :=
    Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  have h1 : ContinuousOn (fun z => Work.FTS.PhiStar.Series.acoeff α m F z) (Set.Ioi 0) := by
    simp only [Work.FTS.PhiStar.Series.acoeff]
    exact radGreenContinuousOn hα hα1 m hc (Work.EllipticEst.ModalSolution.aesm_cmode hsm m)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.H2.ModalSol.ModeIdent.continuous_eFam m).comp_continuousOn
      continuous_snd.continuousOn
  exact (h1.comp continuous_fst.continuousOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)).mul h2

/-- The partial sums of the mode series are continuous on the open quadrant. -/
theorem continuousOn_uncurry_psiTrunc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0) (N : ℕ) :
    ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N))
      Work.FTS.EllipticEst.Q0 := by
  have hfun : Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N)
      = fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.acoeff α m F p.1 *
            Work.FTS.PhiStar.Gegenbauer.eFam m p.2 := by
    funext p
    simp only [Function.uncurry, Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_apply]
  rw [hfun]
  exact continuousOn_finsetSum (Finset.range (N + 1))
    (fun m _ => continuousOn_acoeff_mul_eFam α hα hα1 hsm hL2 m)

/-! ## The weak identity for the limit -/

/-- **The weak identity for the modal solution.**  For every smooth test function `φ` compactly
supported in the open quadrant, `Psi α F` solves `bslOp α Ψ = F` weakly against the weight
`z ^ ((5-α)/α) cos θ`. -/
theorem psi_weak_identity (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F φ : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0, Work.FTS.H2.ModalSol.Psi α F p.1 p.2
        * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  classical
  obtain ⟨a, b, c, d, ha, hab, hc0, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hqpos : 0 < (5 - α) / α := div_pos (by linarith) hα
  set K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d with hKdef
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet K := hKcomp.isClosed.measurableSet
  have hKfin : (volume : Measure (ℝ × ℝ)) K < ⊤ := hKcomp.measure_lt_top
  have hKne : K.Nonempty := ⟨((a + b) / 2, (c + d) / 2),
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hbsl0 : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ K,
      Work.Elliptic.bslOp α φ p.1 p.2 = 0 := fun p hp => bslOp_eq_zero_off_box hbox hp.2
  -- ## reduction of the integrals to the box
  have hvanL : ∀ N : ℕ, (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    fun N => setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by rw [hbsl0 p hp]; ring)
  have hvanLinf : (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.H2.ModalSol.Psi α F p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, Work.FTS.H2.ModalSol.Psi α F p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by rw [hbsl0 p hp]; ring)
  -- ## the two uniform bounds
  obtain ⟨M3, hM3⟩ := hKcomp.exists_bound_of_continuousOn ((continuousOn_bslOp hφsm).mono hKsub)
  have hM3nn : 0 ≤ M3 := le_trans (norm_nonneg _) (hM3 hKne.choose hKne.choose_spec)
  obtain ⟨C, hC0, hCbnd⟩ := psiTrunc_bound_on α hα hα1 horth hsm hL2
    (c := min c (π / 2 - d)) (d := d)
    (lt_of_le_of_lt (min_le_left c (π / 2 - d)) hcd)
    (lt_min hc0 (by linarith)) hd
  have hCann : 0 ≤ C * a ^ (-(1 / 2) : ℝ) := mul_nonneg hC0.le (Real.rpow_nonneg ha.le _)
  -- ## dominated convergence on the box
  have hDCT : Filter.Tendsto (fun N : ℕ => ∫ p in K,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop (nhds (∫ p in K, Work.FTS.H2.ModalSol.Psi α F p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : ℝ × ℝ => C * a ^ (-(1 / 2) : ℝ) * M3 * b ^ ((5 - α) / α)) ?_ ?_ ?_ ?_
    · intro N
      refine ContinuousOn.aestronglyMeasurable ?_ hKmeas
      refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
      · exact (continuousOn_uncurry_psiTrunc α hα hα1 hsm hL2 N).mono hKsub
      · exact (continuousOn_bslOp hφsm).mono hKsub
      · exact (continuousOn_fst.rpow_const
          (fun p hp => Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
          (Real.continuous_cos.comp_continuousOn continuousOn_snd)
    · exact MeasureTheory.integrableOn_const
        (C := C * a ^ (-(1 / 2) : ℝ) * M3 * b ^ ((5 - α) / α))
        (lt_top_iff_ne_top.mp hKfin)
    · intro N
      rw [ae_restrict_iff' hKmeas]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
      have hθd : p.2 ∈ Set.Icc (min c (π / 2 - d)) d :=
        ⟨le_trans (min_le_left _ _) hp.2.1, hp.2.2⟩
      have hψ : |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2|
          ≤ C * a ^ (-(1 / 2) : ℝ) := by
        refine le_trans (hCbnd N p.1 p.2 hp1 hθd) ?_
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos ha hp.1.1 (by norm_num)) hC0.le
      have hbsl : |Work.Elliptic.bslOp α φ p.1 p.2| ≤ M3 := by
        have h := hM3 p hp
        rwa [Real.norm_eq_abs] at h
      have hw : |p.1 ^ ((5 - α) / α) * Real.cos p.2| ≤ b ^ ((5 - α) / α) := by
        rw [abs_mul]
        refine le_trans (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p.2)
          (abs_nonneg _)) ?_
        rw [mul_one, abs_of_nonneg (Real.rpow_nonneg hp1.le _)]
        exact Real.rpow_le_rpow hp1.le hp.1.2 hqpos.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hψ hbsl (abs_nonneg _) hCann) hw (abs_nonneg _)
        (mul_nonneg hCann hM3nn)
    · rw [ae_restrict_iff' hKmeas]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      have hlim := psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2
        (lt_of_lt_of_le ha hp.1.1)
        ⟨lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
      exact ((hlim.mul tendsto_const_nhds).mul tendsto_const_nhds)
  -- ## assembly
  have hLHS : Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.H2.ModalSol.Psi α F p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
    rw [hvanLinf]
    exact hDCT.congr' (Filter.Eventually.of_forall (fun N => (hvanL N).symm))
  have hseq : ∀ N : ℕ, (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0, (∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    fun N => psiTrunc_weak_identity α hα hα1 horth hsm hL2 hφ hφc hφs N
  exact tendsto_nhds_unique hLHS
    (((sourceSideLimit (α := α) hsm hφ hφc hφs hL2)).congr'
      (Filter.Eventually.of_forall (fun N => (hseq N).symm)))

end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- The divided angular mode `Q_m = eFam m / sin 2θ` (Lean's `0/0 = 0` at the endpoints; only the
open interval is used). -/
def Qm (m : ℕ) : ℝ → ℝ := fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ / Work.Construction.s2 θ

/-- The resummed angular profile of the expansion: `Wt ψ 0 = ψ / sin 2θ` and, for `j ≥ 1`,
`Wt ψ j = Σ_m b_m λ_m^{-j} Q_m` with `b_m = bmode m ψ`. -/
def Wt (ψ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun θ => ψ θ / Work.Construction.s2 θ
  | (j + 1) => fun θ =>
      ∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j + 1)
          * Qm m θ

/-- `chia ψ j = sin 2θ · Wt ψ j`: the function whose `Linv` gives the derivative of the next
profile.  On `(0,π/2)`, `chia ψ 0 = ψ`. -/
def chia (ψ : ℝ → ℝ) (j : ℕ) : ℝ → ℝ := fun θ => Work.Construction.s2 θ * Wt ψ j θ

/-- Truncation order of the radial expansion (`J = 8`). -/
def J : ℕ := 8

/-- `Wt ψ 0` is `ψ / sin 2θ` (definitional). -/
theorem Wt_zero (ψ : ℝ → ℝ) : Wt ψ 0 = fun θ => ψ θ / Work.Construction.s2 θ := rfl

/-- `chia ψ j = sin 2θ · Wt ψ j` (definitional). -/
theorem chia_eq (ψ : ℝ → ℝ) (j : ℕ) :
    chia ψ j = fun θ => Work.Construction.s2 θ * Wt ψ j θ := rfl

/-- For `θ ≠ 0, π/2` the `sin 2θ`-multiple of `Q_m` is `eFam m`. -/
theorem s2_mul_Qm {m : ℕ} {θ : ℝ} (h : Work.Construction.s2 θ ≠ 0) :
    Work.Construction.s2 θ * Qm m θ = Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  simp only [Qm]
  field_simp

/-- On the open interval, `chia ψ 0 = ψ`. -/
theorem chia_zero {ψ : ℝ → ℝ} {θ : ℝ}
    (hs : Work.Construction.s2 θ ≠ 0) : chia ψ 0 θ = ψ θ := by
  simp only [chia, Wt_zero]
  field_simp

/-- The series form of `chia` on the open interval: for `j ≥ 1`,
`chia ψ j = Σ_m b_m λ_m^{-j} eFam m`. -/
theorem chia_eq_tsum (ψ : ℝ → ℝ) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    chia ψ (j + 1) θ
      = ∑' m : ℕ,
          Work.FTS.PhiStar.Series.bmode m ψ * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  have hs : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
        (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))
  show Work.Construction.s2 θ * Wt ψ (j + 1) θ = _
  simp only [Wt]
  rw [← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rw [← s2_mul_Qm (m := m) hs]
  ring

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.eFamSupBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

/-!
# `Work.FTS.PhiStar.FlatWAux.eFamSupBound` — linear sup bound for the Gegenbauer family

The Dirichlet eigenfunctions of `Lzero` are
`eFam m θ = cos θ · gC (2m+1) (sin θ) = cos θ · C^{(3/2)}_{2m+1}(sin θ)`
(`Work.FTS.PhiStar.Gegenbauer.eFam`).  This file proves that they grow at most *linearly* in
the mode number, uniformly on `Iθ = [0, π/2]`:

`∃ C, 0 < C ∧ ∀ m θ ∈ Iθ, |eFam m θ| ≤ C · (2m+1)`   (here `C = 3`).

**Route.**  The sharp bound on the open interval is the Sturm–Liouville energy estimate
`Work.FTS.PhiStar.Series.Deleg.psiAngBounds`: with `u(x) = (1-x²)·gC (2m+1)(x)` one has
`u'' = -N·gC (2m+1)` for `N = (2m+2)(2m+3)`, whence `u(x)² ≤ N(1-x²)` on `[0,1]` and, after
`x = sin θ`,

  `|eFam m θ| ≤ √((2m+2)(2m+3))`   for `θ ∈ (0, π/2)`.

The two endpoints are trivial (`eFam m 0 = 0` because `gC (2m+1)` is odd, and
`eFam m (π/2) = 0` because `cos (π/2) = 0`), and `(2m+2)(2m+3) ≤ (3(2m+1))²` for `m ≥ 0`
completes the proof with `C = 3`.  Note `√((2m+2)(2m+3)) ~ 2m`, so the linear shape is sharp.
-/

/-- The energy bound of `Work.FTS.PhiStar.Series.Deleg.psiAngBounds`, first conjunct: on the
open interval `(0, π/2)` the family grows at most like `√((2m+2)(2m+3))`. -/
private lemma eFam_abs_le_sqrt_open (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) :=
  (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).1 m θ hθ

theorem eFamSupBound : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1) := by
  refine ⟨3, by norm_num, fun m θ hθ => ?_⟩
  rw [Work.Spaces.Iθ] at hθ
  obtain ⟨h0, h1⟩ := hθ
  have hkey : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ 3 * (2 * (m : ℝ) + 1) := by
    rcases eq_or_lt_of_le h0 with h | h
    · -- `θ = 0`: the odd Gegenbauer polynomial vanishes
      rw [← h, Work.FTS.PhiStar.Series.eFam_zero_right m, abs_zero]
      positivity
    rcases eq_or_lt_of_le h1 with h' | h'
    · -- `θ = π/2`: the `cos θ` factor vanishes
      rw [h', Work.FTS.PhiStar.Series.eFam_zero_left m, abs_zero]
      positivity
    -- on the open interval, the Sturm–Liouville energy bound
    refine le_trans (eFam_abs_le_sqrt_open m ⟨h, h'⟩) ?_
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hsq : (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) ≤ (3 * (2 * (m : ℝ) + 1)) ^ 2 := by
      nlinarith [sq_nonneg (m : ℝ), hm]
    calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        ≤ Real.sqrt ((3 * (2 * (m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 3 * (2 * (m : ℝ) + 1) := Real.sqrt_sq (by positivity)
  exact hkey

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CapstoneMeasurability =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Honesty.CapstoneMeasurability`

The two **measurability inputs** of the modal-series honesty capstones

* `Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone`,
* `Work.FTS.ClassC.HonestCut.HkMem_zero_zpz_psiSeries_of_capstone`,
* `Work.FTS.ClassC.HonestCut.HkMem_zero_Q_psiSeries_of_capstone`,
* `Work.FTS.ClassC.HonestCut.HkMem_zero_pth2_psiSeries_of_capstone`,
* `Work.FTS.ClassC.HonestCut.HkMem_zero_zpz_pth2_psiSeries_of_capstone`,
* `Work.FTS.PhiStar.Honesty.HkMem_zsq_pzIter2_psiSeries_of_capstone`

are

```
hslmeas : ∀ z ∈ Iz, AEMeasurable (fun θ => ENNReal.ofReal (HkIntegrand α 0 G z θ))
                     (volume.restrict Iθ)
hmeas   : AEMeasurable (fun z => ∫⁻ θ in Iθ, ENNReal.ofReal (HkIntegrand α 0 G z θ))
                     (volume.restrict (Ioi 0))
```

where `G` is the slot under consideration (`Ψ`, `z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ`, …).  Both are
*unconditional* once the slot is `C^∞` on the open quadrant (`SmoothOpen G`), and this file
proves them in that generality:

* `aesm_ofReal_HkIntegrand_prod` — the uncurried integrand `(z,θ) ↦ ofReal (HkIntegrand …)` is
  a.e. strongly measurable for the product of the restricted measures (continuity on the open
  quadrant plus the null-set identification `Iz ↔ Ioi 0`, `Iθ ↔ Ioo 0 (π/2)`);
* `aemeasurable_lintegral_HkIntegrand` — Fubini's measurability theorem for the `θ`-lower
  integral, giving `hmeas`;
* `aemeasurable_slice_HkIntegrand` — the slice version, giving `hslmeas`
  (`z = 0` is the constant `0`; for `z > 0` the slice of a function continuous on the open
  quadrant is continuous on `(0,π/2)`, a conull subset of `Iθ`);
* `smoothOpen_z_mul` — the missing smoothness closure (multiplication by the `z`-coordinate),
  used to feed the `z∂_z∂_θ²Ψ` slot;
* `capstoneMeasurability` — the two inputs bundled in exactly the capstones' shape, for an
  arbitrary `SmoothOpen` slot;
* `capstoneMeasurability_zsqPz2`, `…_pthIter2`, `…_zpz_pthIter2` — the three slot instances
  (radial second derivative, angular second derivative, mixed diagonal second derivative) for a
  `SmoothOpen Ψ`.

Nothing here is analytic: the file is pure measurability bookkeeping and carries no `sorry`.
-/

noncomputable section
open scoped Real Topology ENNReal BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ

/-! ## Smoothness closure under multiplication by `z` -/

/-- `SmoothOpen` is closed under multiplication by the `z`-coordinate. -/
theorem smoothOpen_z_mul {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => z * G z θ)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun z θ : ℝ => z * G z θ)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry G p := rfl
  rw [h1]
  exact (contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder)).mul hG

/-! ## The uncurried integrand is a.e. strongly measurable -/

/-- The uncurried `ENNReal`-valued `ℋ^k`-integrand of a datum `C^∞` on the open quadrant is
a.e. strongly measurable for the product of the two restricted measures. -/
theorem aesm_ofReal_HkIntegrand_prod (α : ℝ) (k : ℕ) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      ((MeasureTheory.volume.restrict Iz).prod (MeasureTheory.volume.restrict Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hG.continuousOn_HkIntegrand α k
  have hcont' : ContinuousOn
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    hcont'.aestronglyMeasurable hUm
  have hz : Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Iz ×ˢ Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain.aemeasurable

/-! ## The `θ`-lower integral is a.e. measurable in `z` -/

/-- **`hmeas`**: for a slot `C^∞` on the open quadrant, the `θ`-lower integral of the `ENNReal`
`ℋ^k`-integrand is a.e. measurable on `(0,∞)`. -/
theorem aemeasurable_lintegral_HkIntegrand (α : ℝ) (k : ℕ) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
      (MeasureTheory.volume.restrict Iz) :=
    (aesm_ofReal_HkIntegrand_prod α k hG).lintegral_prod_right
  have hmeas : MeasureTheory.volume.restrict Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.restrict_Ioi_eq_restrict_Ici (μ := volume) (a := (0 : ℝ))).symm
  rwa [hmeas] at h1

/-! ## The `θ`-slices -/

/-- **`hslmeas`**: for a slot `C^∞` on the open quadrant, every `θ`-slice of the `ENNReal`
`ℋ^k`-integrand is a.e. measurable. -/
theorem aemeasurable_slice_ofReal_HkIntegrand (α : ℝ) (k : ℕ) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ∀ z ∈ Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
      (MeasureTheory.volume.restrict Iθ) := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · subst h0
    have hzero : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G 0 θ))
        = fun _ : ℝ => (0 : ℝ≥0∞) := by
      funext θ
      have : Work.Spaces.HkIntegrand α k G 0 θ = 0 := by
        simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
      rw [this, ENNReal.ofReal_zero]
    rw [hzero]
    exact aemeasurable_const
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hG.continuousOn_HkIntegrand α k
    have hs := Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2) hcont hpos
    exact hs.aemeasurable.ennreal_ofReal

/-! ## The two inputs in the capstones' shape -/


/-! ## The three second-order slots of a `SmoothOpen` datum -/




end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.HkSq_sub_le_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Subadditivity of the `ℋ^l`-energy for a *difference*

`Work.Spaces.HkSq α l` is the square of the paper's weighted norm `|·|_{ℋ^l}`, i.e. the iterated
integral of the *nonnegative* integrand `Work.Spaces.HkIntegrand α l`:

`HkSq α l f = ∫_{z ∈ Iz} ∫_{θ ∈ Iθ} HkIntegrand α l f z θ`.

The integrand is a sum of squares of *linear* slot expressions, so on the open quadrant
`Q0 = (0,∞) × (0,π/2)` the pointwise estimate `(a - b)² ≤ 2a² + 2b²` together with the additivity
of the iterated operators `D_z^i` and `D_z^j D_θ^i` for `SmoothOpen` data gives

`HkIntegrand α l (f - g) ≤ 2·HkIntegrand α l f + 2·HkIntegrand α l g`

at every point of the closed quadrant (that pointwise statement is
`Work.FTS.PhiStar.Honesty.EllWeakAux.HkIntegrand_sub_le_open`, from which the boundary lines
`z = 0` and `sin(2θ) = 0` are handled separately).

Integrating that monotone comparison over `θ` and then over `z` — the dominating function
`2·HkIntegrand α l f + 2·HkIntegrand α l g` being integrable precisely by the two membership
hypotheses `HkMem α l f`, `HkMem α l g` — yields the requested

`HkSq α l (f - g) ≤ 2·(HkSq α l f + HkSq α l g)`.

This is the difference-form companion of `Work.FTS.GalFields.RHS.HkSq_add_le_open`; both are
instances of the same "pointwise bound + monotonicity of the integral" pattern
(`MeasureTheory.integral_mono_of_nonneg`, which needs only the *upper* function to be
integrable).  No `α > 0` hypothesis is needed, because the pointwise integrand bound is
`α`-free.
-/

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Subadditivity of `HkSq` for a difference**, on the open smoothness class.

For `f`, `g` smooth on the open quadrant and with honest `ℋ^l`-integrability certificates,

`HkSq α l (f - g) ≤ 2·(HkSq α l f + HkSq α l g)`. -/
theorem HkSq_sub_le_open (α : ℝ) (l : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α l f) (hmg : Work.Spaces.HkMem α l g) :
    Work.Spaces.HkSq α l (fun z θ => f z θ - g z θ)
      ≤ 2 * (Work.Spaces.HkSq α l f + Work.Spaces.HkSq α l g) := by
  -- the pointwise bound on the closed quadrant, from the open-quadrant subadditivity
  have hpt := Work.FTS.PhiStar.Honesty.EllWeakAux.HkIntegrand_sub_le_open (α := α) (k := l) hf hg
  -- inner (angular) monotonicity of the integral
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ)
        ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l f z θ)
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ) := by
    intro z hz
    have hint : Integrable (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α l f z θ + Work.Spaces.HkIntegrand α l g z θ)
        (volume.restrict Work.Spaces.Iθ) := (hmf.1 z hz).add (hmg.1 z hz)
    -- regroup `2a + 2b` as `2(a + b)`
    have hptz : ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ
          ≤ 2 * (Work.Spaces.HkIntegrand α l f z θ + Work.Spaces.HkIntegrand α l g z θ) :=
      fun θ hθ => by
        have h := hpt z hz θ hθ
        linarith
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ)
      (g := fun θ => 2 * (Work.Spaces.HkIntegrand α l f z θ
        + Work.Spaces.HkIntegrand α l g z θ))
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α l (fun z θ => f z θ - g z θ) z θ)
      (hint.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Icc hptz)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)]
  -- outer (radial) monotonicity of the integral
  have hmain : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l f z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α l (fun z θ => f z θ - g z θ) z θ)
      (g := fun z => 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l f z θ)
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ))
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α l (fun z θ => f z θ - g z θ) z θ)
      ((hmf.2.add hmg.2).const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  -- evaluate the dominating iterated integral
  have hR : (∫ z in Work.Spaces.Iz, 2 * ((∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α l f z θ)
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ))
      = 2 * (Work.Spaces.HkSq α l f + Work.Spaces.HkSq α l g) := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmf.2 hmg.2]
  exact hmain.trans_eq hR

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.BmCutComm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

local notation "Iθ" => Work.Spaces.Iθ
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam

/-! # The commutator term of the cutoff argument

Let `χ δ` be a cutoff family (`1` on `[δ, π/2-δ]`, vanishing outside `(δ/2, π/2-δ/2)`, with
`|(χ δ)'| ≤ K₁/δ`, `|(χ δ)''| ≤ K₂/δ²` and `(χ δ)' = (χ δ)'' = 0` *outside the two layers*
`(δ/2,δ) ∪ (π/2-δ, π/2-δ/2)`).  For a function `ψ` that is small on a pair of boundary
layers, the commutator integral

`∫_{Iθ} ψ · (-(χ'' e) - 2 (χ' e') + tan θ · χ' · e) · cos θ`

tends to `0` along `δ = 1/(n+1)`.  This is the estimate that lets the cutoff be removed from
the weak identity `λ_m ∫ ψ χ e cos = ∫ Γ̄ χ e cos` (`BmodeCoeff.coeff_eq`).

The integrand vanishes outside the layers (so only an interval of total length `2δ` matters),
and on the layers each of the three terms gains a factor `δ` (from `e = eFam m` vanishing at
the endpoints and from `sin θ cos²θ ≤ δ` resp. `cos θ ≤ 1`), which cancels the `1/δ`,
`1/δ²` growth of the derivatives of the cutoff. -/

/-! ## The pointwise bound for the bracket -/

/-- Pointwise bound for `(χ'' e + 2 χ' e' - tan θ χ' e) · cos θ`.  The two summands coming
from `χ''` and `χ'` are estimated with `e · cos` and `e' · cos`; the `tan`-summand uses
`|tan θ cos θ| ≤ 1` together with `|e θ| ≤ A cos θ`. -/
theorem bracket_cos_bound {χ : ℝ → ℝ → ℝ} {e de : ℝ → ℝ} {K₁ K₂ A B δ θ : ℝ}
    (hd : |deriv (χ δ) θ| ≤ K₁ / δ) (hdd : |deriv (deriv (χ δ)) θ| ≤ K₂ / δ ^ 2)
    (he : |e θ| ≤ A * Real.cos θ)
    (he2 : |e θ * Real.cos θ| ≤ A * Real.sin θ * Real.cos θ ^ 2)
    (hde : |de θ * Real.cos θ| ≤ B + A) :
    |(-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * de θ)
        + Real.tan θ * deriv (χ δ) θ * e θ) * Real.cos θ|
      ≤ (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) + 2 * (K₁ / δ) * (B + A)
        + (K₁ / δ) * (A * Real.cos θ) := by
  have hdd0 : 0 ≤ K₂ / δ ^ 2 := le_trans (abs_nonneg _) hdd
  have hd0 : 0 ≤ K₁ / δ := le_trans (abs_nonneg _) hd
  have h1 : |deriv (deriv (χ δ)) θ * e θ * Real.cos θ|
      ≤ (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul hdd he2 (abs_nonneg _) hdd0
  have h2 : |deriv (χ δ) θ * de θ * Real.cos θ| ≤ (K₁ / δ) * (B + A) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul hd hde (abs_nonneg _) hd0
  have htan : |Real.tan θ * Real.cos θ| ≤ 1 := by
    have h := abs_tan_mul_cos_le (1 : ℝ) θ
    rwa [mul_one, abs_one] at h
  have h3 : |Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ|
      ≤ (K₁ / δ) * (A * Real.cos θ) := by
    have hstep : Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ
        = (Real.tan θ * Real.cos θ) * (deriv (χ δ) θ * e θ) := by ring
    rw [hstep, abs_mul]
    have hY : |deriv (χ δ) θ * e θ| ≤ (K₁ / δ) * (A * Real.cos θ) := by
      rw [abs_mul]
      exact mul_le_mul hd he (abs_nonneg _) hd0
    calc |Real.tan θ * Real.cos θ| * |deriv (χ δ) θ * e θ|
        ≤ 1 * ((K₁ / δ) * (A * Real.cos θ)) :=
          mul_le_mul htan hY (abs_nonneg _) (by norm_num)
      _ = (K₁ / δ) * (A * Real.cos θ) := one_mul _
  have hsplit : (-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * de θ)
        + Real.tan θ * deriv (χ δ) θ * e θ) * Real.cos θ
      = -(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)
        - 2 * (deriv (χ δ) θ * de θ * Real.cos θ)
        + Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ := by ring
  rw [hsplit]
  have ha : |-(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)|
      + |2 * (deriv (χ δ) θ * de θ * Real.cos θ)|
      ≤ (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) + 2 * ((K₁ / δ) * (B + A)) := by
    have hb : |2 * (deriv (χ δ) θ * de θ * Real.cos θ)| ≤ 2 * ((K₁ / δ) * (B + A)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    exact add_le_add (by rwa [abs_neg]) hb
  calc |-(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)
        - 2 * (deriv (χ δ) θ * de θ * Real.cos θ)
        + Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ|
      ≤ |-(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)
          - 2 * (deriv (χ δ) θ * de θ * Real.cos θ)|
        + |Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ| := abs_add_le _ _
    _ ≤ (|-(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)|
          + |2 * (deriv (χ δ) θ * de θ * Real.cos θ)|)
        + |Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ| :=
        add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) + 2 * ((K₁ / δ) * (B + A)))
        + (K₁ / δ) * (A * Real.cos θ) := add_le_add ha h3
    _ = (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) + 2 * (K₁ / δ) * (B + A)
        + (K₁ / δ) * (A * Real.cos θ) := by ring

/-! ## The derivative of `eFam m` against `cos` -/

/-- `|(eFam m)' θ · cos θ| ≤ B + A` on `Iθ`, from the bound `B` on the derivative of the
product `eFam m · cos` and the bound `A` on `eFam m`. -/
theorem efam_deriv_cos_le (m : ℕ) {A B : ℝ} (hA : 0 < A)
    (hAe : ∀ θ ∈ Iθ, |eF m θ| ≤ A * Real.cos θ)
    (hBe : ∀ θ : ℝ, |deriv (fun t : ℝ => eF m t * Real.cos t) θ| ≤ B) :
    ∀ θ ∈ Iθ, |deriv (eF m) θ * Real.cos θ| ≤ B + A := by
  intro θ hθ
  have hd : HasDerivAt (eF m) (deriv (eF m) θ) θ :=
    (((contDiff_eF m).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hcos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have h1 : deriv (fun t : ℝ => eF m t * Real.cos t) θ
      = deriv (eF m) θ * Real.cos θ - eF m θ * Real.sin θ := by
    rw [show (fun t : ℝ => eF m t * Real.cos t) = eF m * Real.cos from rfl,
      deriv_mul hd.differentiableAt hcos.differentiableAt, hd.deriv, hcos.deriv]
    ring
  have h2 : deriv (eF m) θ * Real.cos θ
      = deriv (fun t : ℝ => eF m t * Real.cos t) θ + eF m θ * Real.sin θ := by
    linarith [h1]
  rw [h2]
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hs1 : |Real.sin θ| ≤ 1 := abs_le.mpr (Real.sin_mem_Icc θ)
  have hA0 : 0 ≤ A * Real.cos θ := le_trans (abs_nonneg _) (hAe θ hθ)
  have h3 : |eF m θ * Real.sin θ| ≤ A := by
    rw [abs_mul]
    calc |eF m θ| * |Real.sin θ| ≤ (A * Real.cos θ) * 1 :=
          mul_le_mul (hAe θ hθ) hs1 (abs_nonneg _) hA0
      _ = A * Real.cos θ := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hcos1 hA.le
      _ = A := mul_one A
  calc |deriv (fun t : ℝ => eF m t * Real.cos t) θ + eF m θ * Real.sin θ|
      ≤ |deriv (fun t : ℝ => eF m t * Real.cos t) θ| + |eF m θ * Real.sin θ| :=
        abs_add_le _ _
    _ ≤ B + A := add_le_add (hBe θ) h3

/-! ## The layers -/

private lemma layer_sin_cos_sq_le_left {δ θ : ℝ} (hδ4 : δ ≤ 1 / 4) (h1 : δ / 2 < θ)
    (h2 : θ < δ) : Real.sin θ * Real.cos θ ^ 2 ≤ δ := by
  have hθ0 : 0 < θ := by linarith
  have hs : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hsnn : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ0.le, by linarith [h2, hδ4, Real.pi_gt_three]⟩
  have hc2 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  nlinarith [hs, hsnn, hc2, h2]

private lemma layer_sin_cos_sq_le_right {δ θ : ℝ} (hδ4 : δ ≤ 1 / 4)
    (h1 : Real.pi / 2 - δ < θ) (h2 : θ < Real.pi / 2 - δ / 2) :
    Real.sin θ * Real.cos θ ^ 2 ≤ δ := by
  have hδpos : 0 < δ := by linarith [h1, h2]
  have hθ0 : 0 < θ := by linarith [h1, hδ4, Real.pi_gt_three]
  have hθpi : θ < Real.pi / 2 := by linarith [h2, hδ4]
  have hc0 : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩)
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcle : Real.cos θ ≤ Real.pi / 2 - θ := by
    have h := Real.sin_le (show (0 : ℝ) ≤ Real.pi / 2 - θ by linarith)
    rwa [Real.sin_pi_div_two_sub] at h
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsq : Real.sin θ * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith [hs1, hc0]
  have hsq2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, hc1]
  linarith

/-! ## The limit -/

theorem bmcut_commutator_tendsto (χ : ℝ → ℝ → ℝ) (K₁ K₂ A B : ℝ)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hA : 0 < A) (hB : 0 < B)
    (hχd : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, |deriv (χ δ) θ| ≤ K₁ / δ)
    (hχdd : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, |deriv (deriv (χ δ)) θ| ≤ K₂ / δ ^ 2)
    (hχsupp : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ,
        (θ ∉ Set.Ioo (δ / 2) δ ∧ θ ∉ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2)) →
        deriv (χ δ) θ = 0 ∧ deriv (deriv (χ δ)) θ = 0)
    (m : ℕ)
    (hAe : ∀ θ ∈ Iθ, |eF m θ| ≤ A * Real.cos θ)
    (hAe2 : ∀ θ ∈ Iθ, |eF m θ * Real.cos θ| ≤ A * Real.sin θ * Real.cos θ ^ 2)
    (hBe : ∀ θ : ℝ, |deriv (fun t : ℝ => eF m t * Real.cos t) θ| ≤ B)
    (ψ : ℝ → ℝ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : ℝ,
        (θ ∈ Set.Icc 0 ρ ∨ θ ∈ Set.Icc (Real.pi / 2 - ρ) (Real.pi / 2)) → |ψ θ| < ε) :
    Filter.Tendsto (fun n : ℕ => ∫ θ in Iθ, ψ θ *
        (-(deriv (deriv (χ (1 / ((n : ℝ) + 1)))) θ * eF m θ)
          - 2 * (deriv (χ (1 / ((n : ℝ) + 1))) θ * deriv (eF m) θ)
          + Real.tan θ * deriv (χ (1 / ((n : ℝ) + 1))) θ * eF m θ) * Real.cos θ)
      Filter.atTop (nhds 0) := by
  set Cp : ℝ := K₂ * A + 2 * K₁ * (B + A) + K₁ * A with hCpdef
  have hCp0 : 0 ≤ Cp := by rw [hCpdef]; positivity
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  set P : ℝ := ε / (2 * (Cp + 1)) with hPdef
  have hPpos : 0 < P := by rw [hPdef]; positivity
  obtain ⟨ρ, hρpos, hρ⟩ := hsmall P hPpos
  have hρmin : 0 < min ρ (1 / 4 : ℝ) := lt_min hρpos (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_le_nhds hρmin))
  refine ⟨N, fun n hn => ?_⟩
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle : δ ≤ min ρ (1 / 4 : ℝ) := hN n hn
  have hδρ : δ ≤ ρ := le_trans hδle (min_le_left _ _)
  have hδ4 : δ ≤ 1 / 4 := le_trans hδle (min_le_right _ _)
  set L : Set ℝ := Set.Ioo (δ / 2) δ ∪ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2)
    with hLdef
  set F : ℝ → ℝ := fun θ => ψ θ *
    (-(deriv (deriv (χ δ)) θ * eF m θ)
      - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
      + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ with hFdef
  have hde : ∀ θ ∈ Iθ, |deriv (eF m) θ * Real.cos θ| ≤ B + A :=
    efam_deriv_cos_le m hA hAe hBe
  have hlayer : ∀ θ ∈ L, |F θ| ≤ P * Cp / δ := by
    intro θ hθL
    have hθL' := hθL
    rw [hLdef] at hθL
    have hθI : θ ∈ Iθ := by
      rcases hθL with h | h
      · exact ⟨by linarith [h.1], by linarith [h.2, hδ4, Real.pi_gt_three]⟩
      · exact ⟨by linarith [h.1, hδ4, Real.pi_gt_three], by linarith [h.2, hδ4]⟩
    have hψb : |ψ θ| < P := by
      refine hρ θ ?_
      rcases hθL with h | h
      · exact Or.inl ⟨by linarith [h.1], le_trans h.2.le hδρ⟩
      · exact Or.inr ⟨by linarith [h.1, hδρ], by linarith [h.2, hδ4]⟩
    have hsc_le : Real.sin θ * Real.cos θ ^ 2 ≤ δ := by
      rcases hθL with h | h
      · exact layer_sin_cos_sq_le_left hδ4 h.1 h.2
      · exact layer_sin_cos_sq_le_right hδ4 h.1 h.2
    have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hbr := bracket_cos_bound (χ := χ) (e := eF m) (de := deriv (eF m))
      (θ := θ) (hχd δ hδpos θ) (hχdd δ hδpos θ) (hAe θ hθI) (hAe2 θ hθI) (hde θ hθI)
    have hbr' : |(-(deriv (deriv (χ δ)) θ * eF m θ)
        - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
        + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ| ≤ Cp / δ := by
      refine le_trans hbr ?_
      have hK10 : (0 : ℝ) ≤ K₁ / δ := by positivity
      have hK20 : (0 : ℝ) ≤ K₂ / δ ^ 2 := by positivity
      have e1 : (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) ≤ (K₂ / δ ^ 2) * (A * δ) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hsc_le, hA]) hK20
      have e2 : (K₁ / δ) * (A * Real.cos θ) ≤ (K₁ / δ) * A :=
        mul_le_mul_of_nonneg_left (by nlinarith [hc1, hA]) hK10
      have e3 : (K₂ / δ ^ 2) * (A * δ) + 2 * (K₁ / δ) * (B + A) + (K₁ / δ) * A
          = Cp / δ := by
        rw [hCpdef]
        field_simp
      linarith [e1, e2, e3]
    show |ψ θ * (-(deriv (deriv (χ δ)) θ * eF m θ)
        - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
        + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ| ≤ P * Cp / δ
    rw [show ψ θ * (-(deriv (deriv (χ δ)) θ * eF m θ)
        - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
        + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ
      = ψ θ * ((-(deriv (deriv (χ δ)) θ * eF m θ)
        - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
        + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ) from by ring]
    rw [abs_mul]
    calc |ψ θ| * |(-(deriv (deriv (χ δ)) θ * eF m θ)
          - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
          + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ|
        ≤ P * (Cp / δ) := mul_le_mul hψb.le hbr' (abs_nonneg _) hPpos.le
      _ = P * Cp / δ := by ring
  have hzero : ∀ θ ∈ Iθ \ L, F θ = 0 := by
    intro θ hθ
    obtain ⟨hθI, hθnotL⟩ := hθ
    have h1 : θ ∉ Set.Ioo (δ / 2) δ := fun hm => hθnotL (by rw [hLdef]; exact Or.inl hm)
    have h2 : θ ∉ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2) :=
      fun hm => hθnotL (by rw [hLdef]; exact Or.inr hm)
    obtain ⟨hd0, hdd0⟩ := hχsupp δ hδpos θ ⟨h1, h2⟩
    show ψ θ * (-(deriv (deriv (χ δ)) θ * eF m θ)
      - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
      + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ = 0
    rw [hd0, hdd0]
    ring
  have hsub : L ⊆ Iθ := by
    intro θ hθ
    rw [hLdef] at hθ
    rcases hθ with h | h
    · exact ⟨by linarith [h.1], by linarith [h.2, hδ4, Real.pi_gt_three]⟩
    · exact ⟨by linarith [h.1, hδ4, Real.pi_gt_three], by linarith [h.2, hδ4]⟩
  have hfin : volume L < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hmeasL : volume.real L ≤ δ := by
    rw [hLdef]
    have h1 : volume.real (Set.Ioo (δ / 2) δ) ≤ δ / 2 := by
      rw [Real.volume_real_Ioo_of_le (by linarith : δ / 2 ≤ δ)]
      linarith
    have h2 : volume.real (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2)) ≤ δ / 2 := by
      rw [Real.volume_real_Ioo_of_le (by linarith : Real.pi / 2 - δ ≤ Real.pi / 2 - δ / 2)]
      linarith
    have hun := MeasureTheory.measureReal_union_le (μ := (volume : Measure ℝ))
      (Set.Ioo (δ / 2) δ) (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2))
    linarith
  rw [Real.dist_eq, sub_zero]
  have hsplit : (∫ θ in Iθ, F θ) = ∫ θ in L, F θ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iθ hsub hzero
  rw [hsplit]
  have hboundL : ∀ θ ∈ L, ‖F θ‖ ≤ P * Cp / δ := fun θ hθ => hlayer θ hθ
  calc |∫ θ in L, F θ|
      ≤ P * Cp / δ * volume.real L :=
        norm_setIntegral_le_of_norm_le_const hfin hboundL
    _ ≤ P * Cp / δ * δ := by
        refine mul_le_mul_of_nonneg_left hmeasL ?_
        rw [hCpdef]
        positivity
    _ = P * Cp := by
        rw [div_mul_cancel₀ (P * Cp) (ne_of_gt hδpos)]
    _ = ε * Cp / (2 * (Cp + 1)) := by rw [hPdef]; ring
    _ < ε := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (Cp + 1))]
        nlinarith [hCp0, hε]

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.mode_series_summable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

local notation "bm" => Work.FTS.PhiStar.Series.bmode
local notation "lamF" => Work.FTS.PhiStar.Gegenbauer.lam
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam

/-- The eigenvalue `lam m = 2m(2m+5)` is positive for `m ≥ 1`. -/
lemma lamF_pos {m : ℕ} (hm : 1 ≤ m) : 0 < lamF m := by
  have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  show 0 < 2 * (m : ℝ) * (2 * (m : ℝ) + 5)
  nlinarith

/-- `4 (m:ℝ)² ≤ lam m` for `m ≥ 1`. -/
lemma four_sq_le_lamF {m : ℕ} (hm : 1 ≤ m) : 4 * (m : ℝ) ^ 2 ≤ lamF m := by
  have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  show 4 * (m : ℝ) ^ 2 ≤ 2 * (m : ℝ) * (2 * (m : ℝ) + 5)
  nlinarith

/-- The pointwise decay of the mode series: the hypothesis `hdec` on the coefficients together
with the growth hypothesis `hgr` on the eigenvectors gives the summable majorant
`max (Cd*Cg) 1 · m^{-5/2}`. -/
lemma mode_bound (ψ : ℝ → ℝ) {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |bm m ψ| ≤ Cd / (lamF m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |eF m θ| ≤ Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) :
    ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |(bm m ψ / lamF m) * eF m θ| ≤ max (Cd * Cg) 1 * (m : ℝ) ^ (-(5 / 2 : ℝ)) := by
  intro m θ hθ
  by_cases hm : m = 0
  · subst hm
    have hz : ((0 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) = 0 := by
      rw [show ((0 : ℕ) : ℝ) = 0 by norm_num, Real.zero_rpow (by norm_num)]
    have hlz : lamF 0 = 0 := by simp [Work.FTS.PhiStar.Gegenbauer.lam]
    rw [hlz, div_zero, zero_mul, abs_zero, hz, mul_zero]
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hx1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hxpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hx1
    have hlam_pos : 0 < lamF m := lamF_pos hm1
    have hlam_ge : 4 * (m : ℝ) ^ 2 ≤ lamF m := four_sq_le_lamF hm1
    have hsqrt_pos : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have hden : 0 < (lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos (pow_pos hlam_pos 2) hsqrt_pos
    -- step 1: `|bm m ψ| / lam m ≤ Cd / ((lam m)² √(2m+1))`
    have hstep : |bm m ψ| / lamF m ≤ Cd / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
      calc |bm m ψ| / lamF m
          ≤ (Cd / (lamF m * Real.sqrt (2 * (m : ℝ) + 1))) / lamF m :=
            div_le_div_of_nonneg_right (hdec m hm1) (le_of_lt hlam_pos)
        _ = Cd / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
            rw [div_div]
            congr 1
            ring
    -- step 2: `((m+1)^{3/2} ≤ 16 m^{3/2}`
    have hY : ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) ≤ 16 * (m : ℝ) ^ ((3 / 2 : ℝ)) := by
      have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
      have h1 : ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) ≤ (2 * (m : ℝ)) ^ ((3 / 2 : ℝ)) :=
        Real.rpow_le_rpow (by linarith) hle (by norm_num)
      have h2 : (2 * (m : ℝ)) ^ ((3 / 2 : ℝ))
          = (2 : ℝ) ^ ((3 / 2 : ℝ)) * (m : ℝ) ^ ((3 / 2 : ℝ)) :=
        Real.mul_rpow (by norm_num) (le_of_lt hxpos)
      have h3 : (2 : ℝ) ^ ((3 / 2 : ℝ)) ≤ 16 := by
        have hh : (2 : ℝ) ^ ((3 / 2 : ℝ)) ≤ (2 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        have h4 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
        linarith
      calc ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) ≤ (2 * (m : ℝ)) ^ ((3 / 2 : ℝ)) := h1
        _ = (2 : ℝ) ^ ((3 / 2 : ℝ)) * (m : ℝ) ^ ((3 / 2 : ℝ)) := h2
        _ ≤ 16 * (m : ℝ) ^ ((3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (le_of_lt hxpos) _)
    -- step 3: the denominator dominates `16 m⁴ √1`
    have hD16 : 16 * (m : ℝ) ^ (4 : ℝ) ≤ (lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by
      have h4 : (m : ℝ) ^ (4 : ℝ) = (m : ℝ) ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hsq : 16 * (m : ℝ) ^ (4 : ℝ) ≤ (lamF m) ^ 2 := by
        rw [h4]
        nlinarith [sq_nonneg (lamF m - 4 * (m : ℝ) ^ 2), hlam_ge]
      have hs1 : 1 ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
        Real.one_le_sqrt.mpr (by linarith)
      calc 16 * (m : ℝ) ^ (4 : ℝ) = 16 * (m : ℝ) ^ (4 : ℝ) * 1 := by ring
        _ ≤ (lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
            mul_le_mul hsq hs1 (by norm_num) (le_of_lt (pow_pos hlam_pos 2))
    -- step 4: the exponent bookkeeping `m^{-5/2} · m⁴ = m^{3/2}`
    have hbr : (m : ℝ) ^ (-(5 / 2 : ℝ)) * (16 * (m : ℝ) ^ (4 : ℝ))
        = 16 * (m : ℝ) ^ ((3 / 2 : ℝ)) := by
      have hrr : (m : ℝ) ^ (-(5 / 2 : ℝ)) * (m : ℝ) ^ (4 : ℝ)
          = (m : ℝ) ^ ((3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hxpos]
        norm_num
      calc (m : ℝ) ^ (-(5 / 2 : ℝ)) * (16 * (m : ℝ) ^ (4 : ℝ))
          = 16 * ((m : ℝ) ^ (-(5 / 2 : ℝ)) * (m : ℝ) ^ (4 : ℝ)) := by ring
        _ = 16 * (m : ℝ) ^ ((3 / 2 : ℝ)) := by rw [hrr]
    -- the key inequality
    have hkey : ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))
          / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
        ≤ (m : ℝ) ^ (-(5 / 2 : ℝ)) := by
      rw [div_le_iff₀ hden]
      have h := mul_le_mul_of_nonneg_left hD16
        (Real.rpow_nonneg (le_of_lt hxpos) (-(5 / 2 : ℝ)))
      rw [hbr] at h
      linarith
    -- assemble
    have hprod : |bm m ψ| / lamF m * |eF m θ|
        ≤ (Cd / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
            * (Cg * (((m : ℝ) + 1) ^ ((3 / 2 : ℝ)))) :=
      mul_le_mul hstep (hgr m θ hθ) (abs_nonneg _)
        (div_nonneg (le_of_lt hCd) (le_of_lt hden))
    calc |(bm m ψ / lamF m) * eF m θ|
        = |bm m ψ| / lamF m * |eF m θ| := by
          rw [abs_mul, abs_div, abs_of_pos hlam_pos]
      _ ≤ (Cd / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
            * (Cg * (((m : ℝ) + 1) ^ ((3 / 2 : ℝ)))) := hprod
      _ = Cd * Cg * (((m : ℝ) + 1) ^ ((3 / 2 : ℝ))
            / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) := by
          field_simp
      _ ≤ max (Cd * Cg) 1 * (m : ℝ) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul (le_max_left _ _) hkey
            (div_nonneg
              (le_of_lt (Real.rpow_pos_of_pos (by linarith : 0 < (m : ℝ) + 1) _))
              (le_of_lt hden))
            (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))

theorem mode_series_summable (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) :
    (∃ M : ℕ → ℝ, (∀ m : ℕ, 0 ≤ M m) ∧ Summable M ∧
        ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
          |(Work.FTS.PhiStar.Series.bmode m ψ / Work.FTS.PhiStar.Gegenbauer.lam m)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M m)
      ∧ ContinuousOn
          (fun θ => ∑' m : ℕ,
            (Work.FTS.PhiStar.Series.bmode m ψ / Work.FTS.PhiStar.Gegenbauer.lam m)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  set A : ℝ := max (Cd * Cg) 1 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKle : Cd * Cg ≤ A := by
    rw [hAdef]
    exact le_max_left _ _
  have hbase : Summable (fun m : ℕ => (m : ℝ) ^ (-(5 / 2 : ℝ))) :=
    (Real.summable_nat_rpow (p := (-(5 / 2 : ℝ)))).mpr (by norm_num)
  have hMsum : Summable (fun m : ℕ => A * (m : ℝ) ^ (-(5 / 2 : ℝ))) := hbase.mul_left A
  have hbd : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |(Work.FTS.PhiStar.Series.bmode m ψ / Work.FTS.PhiStar.Gegenbauer.lam m)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ A * (m : ℝ) ^ (-(5 / 2 : ℝ)) := by
    intro m θ hθ
    have h := mode_bound ψ hCd hCg hdec hgr m θ hθ
    rwa [hAdef]
  refine ⟨?_, ?_⟩
  · exact ⟨fun m => A * (m : ℝ) ^ (-(5 / 2 : ℝ)),
      fun m => mul_nonneg (le_of_lt hApos) (Real.rpow_nonneg (Nat.cast_nonneg m) _),
      hMsum, hbd⟩
  · refine continuousOn_tsum (u := fun m : ℕ => A * (m : ℝ) ^ (-(5 / 2 : ℝ))) ?_ hMsum ?_
    · intro m
      have hcont : Continuous (fun θ : ℝ =>
          (Work.FTS.PhiStar.Series.bmode m ψ / Work.FTS.PhiStar.Gegenbauer.lam m)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
        rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
            = (fun θ : ℝ => Real.cos θ
                * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) from rfl]
        exact (Real.continuous_cos.mul
          ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
            Real.continuous_sin)).const_mul _
      exact hcont.continuousOn
    · intro m θ hθ
      rw [Real.norm_eq_abs]
      exact hbd m θ hθ

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Weil.tendstoIntegralPsiTrunc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Measurability of `𝒜φ = phiA α` -/

/-- `𝒜φ = phiA α = αz²φ'' + (5+α)zφ'` is measurable: it is a combination of `deriv` and
`iteratedDeriv 2`, and `deriv` is universally measurable (`measurable_deriv`). -/
theorem measurable_phiA (α : ℝ) : Measurable (Work.FTS.VocabO.phiA α) := by
  have h2 : Measurable (iteratedDeriv 2 Work.FTS.VocabO.phiR) := by
    have h : iteratedDeriv 2 Work.FTS.VocabO.phiR = deriv (deriv Work.FTS.VocabO.phiR) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h]
    exact measurable_deriv _
  have h1 : Measurable (deriv Work.FTS.VocabO.phiR) := measurable_deriv _
  have hA : Measurable (fun z : ℝ => α * z ^ 2) :=
    measurable_const.mul (measurable_id.pow_const 2)
  have hB : Measurable (fun z : ℝ => (5 + α) * z) := measurable_const.mul measurable_id
  change Measurable (fun z : ℝ => α * z ^ 2 * iteratedDeriv 2 Work.FTS.VocabO.phiR z
    + (5 + α) * z * deriv Work.FTS.VocabO.phiR z)
  exact (hA.mul h2).add (hB.mul h1)

/-! ## Measurability of parameter-dependent integrals -/

/-- The joint integrand of the interval integral `z ↦ ∫_0^z F` on a *variable* interval:
`(z,t) ↦ 1_{(0,z]}(t)·F t·t^s`. -/
def jointIoc (F : ℝ → ℝ) (s : ℝ) : ℝ × ℝ → ℝ :=
  fun p => if p.2 ∈ Set.Ioc (0 : ℝ) p.1 then F p.2 * p.2 ^ s else 0

/-- The joint integrand of the tail integral `z ↦ ∫_{Ioi z} F`:
`(z,t) ↦ 1_{(z,∞)}(t)·F t·t^s`. -/
def jointIoi (F : ℝ → ℝ) (s : ℝ) : ℝ × ℝ → ℝ :=
  fun p => if p.2 ∈ Set.Ioi p.1 then F p.2 * p.2 ^ s else 0

theorem jointIoc_measurable {F : ℝ → ℝ} (hF : Measurable F) (s : ℝ) :
    Measurable (jointIoc F s) := by
  change Measurable (fun p : ℝ × ℝ =>
    if p.2 ∈ Set.Ioc (0 : ℝ) p.1 then F p.2 * p.2 ^ s else 0)
  refine Measurable.ite ?_ ((hF.comp measurable_snd).mul (measurable_snd.pow_const s))
    measurable_const
  exact (measurableSet_lt (measurable_const : Measurable fun _ : ℝ × ℝ => (0 : ℝ))
      measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)

theorem jointIoi_measurable {F : ℝ → ℝ} (hF : Measurable F) (s : ℝ) :
    Measurable (jointIoi F s) := by
  change Measurable (fun p : ℝ × ℝ =>
    if p.2 ∈ Set.Ioi p.1 then F p.2 * p.2 ^ s else 0)
  refine Measurable.ite ?_ ((hF.comp measurable_snd).mul (measurable_snd.pow_const s))
    measurable_const
  exact measurableSet_lt measurable_fst measurable_snd

/-- **The primitive of a measurable function is a.e. strongly measurable.**  For `z > 0`,
`z ↦ ∫_0^z F(t)t^s dt` is the partial integral of the jointly measurable function
`jointIoc F s`, whence the a.e. strong measurability by
`AEStronglyMeasurable.integral_prod_right'`. -/
theorem aesm_intervalIntegral_mul_rpow (F : ℝ → ℝ) (hF : Measurable F) (s : ℝ) :
    AEStronglyMeasurable (fun z : ℝ => ∫ t in (0 : ℝ)..z, F t * t ^ s)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have h1 : AEStronglyMeasurable (fun z : ℝ => ∫ t, jointIoc F s (z, t) ∂(volume : Measure ℝ))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    (jointIoc_measurable hF s).aestronglyMeasurable
      (μ := ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (volume : Measure ℝ))
      |>.integral_prod_right'
  refine h1.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  rw [intervalIntegral.integral_of_le hz.le,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
    by_cases h : t ∈ Set.Ioc (0 : ℝ) z <;> simp [h, jointIoc, Set.indicator_apply])

/-- **The tail integral of a measurable function is a.e. strongly measurable.** -/
theorem aesm_IoiIntegral_mul_rpow (F : ℝ → ℝ) (hF : Measurable F) (s : ℝ) :
    AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, F t * t ^ s)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have h1 : AEStronglyMeasurable (fun z : ℝ => ∫ t, jointIoi F s (z, t) ∂(volume : Measure ℝ))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    (jointIoi_measurable hF s).aestronglyMeasurable
      (μ := ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (volume : Measure ℝ))
      |>.integral_prod_right'
  refine h1.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _hz
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
    by_cases h : t ∈ Set.Ioi z <;> simp [h, jointIoi, Set.indicator_apply])

/-- **The modal radial Green function of a measurable source is a.e. strongly measurable.**
`radGreen α m c` is a sum of the two parameter-dependent integrals above, multiplied by the
measurable powers `z^{-(2m+5)/α}` and `z^{2m/α}`. -/
theorem aesm_radGreen (α : ℝ) (m : ℕ) {c : ℝ → ℝ} (hc : Measurable c) :
    AEStronglyMeasurable (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have h1 : AEStronglyMeasurable
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    aesm_intervalIntegral_mul_rpow c hc ((2 * (m : ℝ) + 5) / α - 1)
  have h2 : AEStronglyMeasurable
      (fun z : ℝ => ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    aesm_IoiIntegral_mul_rpow c hc (-(2 * (m : ℝ) / α) - 1)
  have hz1 : AEStronglyMeasurable (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α)) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hz2 : AEStronglyMeasurable (fun z : ℝ => z ^ (2 * (m : ℝ) / α))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hmain : AEStronglyMeasurable (fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5)) *
      (z ^ (-(2 * (m : ℝ) + 5) / α)
          * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        + z ^ (2 * (m : ℝ) / α)
          * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    ((hz1.mul h1).add (hz2.mul h2)).const_mul _
  exact hmain.congr (Filter.Eventually.of_forall fun z => rfl)

/-- The modal radial Green function for the specific source `𝒜φ` of the `Φ_*` construction. -/
theorem aesm_radGreen_phiA (α : ℝ) (m : ℕ) :
    AEStronglyMeasurable
      (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
  aesm_radGreen α m (measurable_phiA α)

/-! ## The limit theorem -/

theorem tendstoIntegralPsiTrunc {α : ℝ} {ψ : ℝ → ℝ}
    (hbox : ∀ (a b c d : ℝ), 0 < a → a ≤ b → 0 < c → c ≤ d → d < π / 2 →
      (∃ B : ℝ, ∀ (N : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.PhiStar.Series.Weil.box a b c d →
        |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2| ≤ B) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ × ℝ,
        p ∈ Work.FTS.PhiStar.Series.Weil.box a b c d →
        |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) n p.1 p.2
          - Work.FTS.PhiStar.Series.Weil.R α ψ p.1 p.2| ≤ ε))
    {φ : ℝ → ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.Weil.R α ψ p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
  classical
  -- ## Step 1: the compact box containing the support of the test function
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hboxopen⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  obtain ⟨hbdd, hconv⟩ := hbox a b c d ha hab.le hc hcd.le hd
  obtain ⟨B, hB⟩ := hbdd
  let K : Set (ℝ × ℝ) := Work.FTS.PhiStar.Series.Weil.box a b c d
  have hKdef : K = Set.Icc a b ×ˢ Set.Icc c d := rfl
  have hKmeas : MeasurableSet K := by
    rw [hKdef]
    exact measurableSet_Icc.prod measurableSet_Icc
  have hKcomp : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod isCompact_Icc
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.PhiStar.Series.Weil.box_subset_Q0 ha hab.le hc hcd.le hd
  have hφ0 : ∀ p : ℝ × ℝ, p ∉ K → φ p.1 p.2 = 0 := by
    intro p hp
    refine hboxopen p (fun hmem => hp ?_)
    exact ⟨⟨hmem.1.1.le, hmem.1.2.le⟩, ⟨hmem.2.1.le, hmem.2.2.le⟩⟩
  have hbsl0 : ∀ p : ℝ × ℝ, p ∉ K → Work.Elliptic.bslOp α φ p.1 p.2 = 0 := by
    intro p hp
    refine Work.FTS.H2.ModalSolR.bslOp_eq_zero_off_box hboxopen ?_
    simpa only [hKdef] using hp
  -- ## Step 2: the weight against which we integrate
  set g : ℝ × ℝ → ℝ :=
    fun p => Work.Elliptic.bslOp α φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) with hg
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hgc : ContinuousOn g K := by
    rw [hg, hKdef]
    refine ContinuousOn.mul
      ((Work.FTS.H2.ModalSolR.continuousOn_bslOp hφsm).mono hKsub) ?_
    exact (continuousOn_fst.rpow_const (fun p hp => Or.inl (ne_of_gt (hKsub hp).1))).mul
      ((Real.continuous_cos.comp continuous_snd).continuousOn)
  have hgint : Integrable (fun p : ℝ × ℝ => ‖g p‖)
      ((volume : Measure (ℝ × ℝ)).restrict K) :=
    hgc.norm.integrableOn_compact hKcomp
  -- ## Step 3: measurability of the partial sums and of the limit
  have hQ0prod : (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
    rw [Work.FTS.EllipticEst.Q0, MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact (MeasureTheory.Measure.prod_restrict (Set.Ioi 0) (Set.Ioo 0 (π / 2))).symm
  have haesm_psiTrunc (N : ℕ) : AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) := by
    have hterm : ∀ m ∈ Finset.range (N + 1), AEStronglyMeasurable
        (fun p : ℝ × ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
          * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) := by
      intro m _
      have h1 : AEStronglyMeasurable
          (fun p : ℝ × ℝ =>
            Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) p.1)
          ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) := by
        rw [hQ0prod]
        exact (aesm_radGreen_phiA α m).comp_quasiMeasurePreserving
          MeasureTheory.Measure.quasiMeasurePreserving_fst
      have h2 : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) :=
        (((Work.FTS.ClassC.contDiff_eFam_nat m 1).continuous.measurable).comp
          measurable_snd).aestronglyMeasurable
      exact (h1.const_mul _).mul h2
    have hsum := Finset.aestronglyMeasurable_sum (Finset.range (N + 1)) hterm
    refine hsum.congr ?_
    filter_upwards with p
    simp only [Finset.sum_apply, Work.FTS.PhiStar.Series.psiTrunc]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Work.FTS.PhiStar.Series.acoeff_RemSource]
  have hpsiK (N : ℕ) : AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict K) :=
    (haesm_psiTrunc N).mono_set hKsub
  have haesm_R : AEStronglyMeasurable (fun p : ℝ × ℝ => R α ψ p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict K) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun N => hpsiK N) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε / 2) (by linarith)
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]
      linarith [hN n hn p hp]⟩
  -- ## Step 4: integrability of the two integrands on the box
  obtain ⟨N₁, hN₁⟩ := hconv 1 one_pos
  have hRb : ∀ p : ℝ × ℝ, p ∈ K → |R α ψ p.1 p.2| ≤ B + 1 := by
    intro p hp
    have h1 : |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2
        - R α ψ p.1 p.2| ≤ 1 := hN₁ N₁ le_rfl p hp
    have h2 : |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2|
        ≤ B := hB N₁ p hp
    calc |R α ψ p.1 p.2|
        = |R α ψ p.1 p.2
            - Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2
            + Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2| :=
          by ring_nf
      _ ≤ |R α ψ p.1 p.2
            - Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2|
          + |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2| :=
          abs_add_le _ _
      _ ≤ 1 + B := by
          rw [abs_sub_comm]
          exact add_le_add h1 h2
      _ = B + 1 := by ring
  have hAint (N : ℕ) : Integrable
      (fun p : ℝ × ℝ =>
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2 * g p)
      ((volume : Measure (ℝ × ℝ)).restrict K) := by
    refine Integrable.mono' (hgint.const_mul B)
      ((hpsiK N).mul (hgc.aestronglyMeasurable hKmeas)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hB N p hp) (abs_nonneg _)
  have hBint : Integrable (fun p : ℝ × ℝ => R α ψ p.1 p.2 * g p)
      ((volume : Measure (ℝ × ℝ)).restrict K) := by
    refine Integrable.mono' (hgint.const_mul (B + 1))
      (haesm_R.mul (hgc.aestronglyMeasurable hKmeas)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hRb p hp) (abs_nonneg _)
  -- ## Step 5: the ε-argument on the box
  have hmain : Filter.Tendsto (fun N : ℕ => ∫ p in K,
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2 * g p)
      Filter.atTop (nhds (∫ p in K, R α ψ p.1 p.2 * g p)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hDnn : 0 ≤ ∫ p in K, ‖g p‖ :=
      integral_nonneg fun p => norm_nonneg _
    have hden : (0 : ℝ) < (∫ p in K, ‖g p‖) + 1 := by linarith
    have hpos : 0 < ε / 2 / ((∫ p in K, ‖g p‖) + 1) :=
      div_pos (by linarith) hden
    obtain ⟨N, hN⟩ := hconv (ε / 2 / ((∫ p in K, ‖g p‖) + 1)) hpos
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, ← Real.norm_eq_abs, ← MeasureTheory.integral_sub (hAint n) hBint]
    calc ‖∫ p in K, (Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ)
            n p.1 p.2 * g p - R α ψ p.1 p.2 * g p)‖
        ≤ ∫ p in K, ‖Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ)
            n p.1 p.2 * g p - R α ψ p.1 p.2 * g p‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ p in K, ε / 2 / ((∫ p in K, ‖g p‖) + 1) * ‖g p‖ := by
          refine MeasureTheory.integral_mono_ae ((hAint n).sub hBint).norm
            (hgint.const_mul _) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
          have hsub : Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ)
                n p.1 p.2 * g p - R α ψ p.1 p.2 * g p
              = (Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ)
                n p.1 p.2 - R α ψ p.1 p.2) * g p := by ring
          rw [hsub, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hN n hn p hp) (abs_nonneg _)
      _ = ε / 2 / ((∫ p in K, ‖g p‖) + 1) * (∫ p in K, ‖g p‖) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hden]
          nlinarith [hDnn]
      _ < ε := by linarith
  -- ## Step 6: transfer the statement back to the quadrant
  have hvanA : ∀ N : ℕ, (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K,
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2 * g p := by
    intro N
    rw [Work.FTS.H2.ModalSolR.setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by
      rw [hbsl0 p hp.2]
      ring)]
    refine MeasureTheory.setIntegral_congr_fun hKmeas (fun p _ => ?_)
    simp only [hg]
    ring
  have hvanB : (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.Weil.R α ψ p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, R α ψ p.1 p.2 * g p := by
    rw [Work.FTS.H2.ModalSolR.setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by
      rw [hbsl0 p hp.2]
      ring)]
    refine MeasureTheory.setIntegral_congr_fun hKmeas (fun p _ => ?_)
    simp only [hg]
    ring
  rw [funext hvanA, hvanB]
  exact hmain

end Work.FTS.PhiStar.Series.Weil
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.PtBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2hatOAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `ℋⁿ`-slot bound for the `D_z`-commutator defect, on the open class.**  For `α > 0`,
`f` of class `SmoothOpen` and `(z,θ)` in the open quadrant,

`HkIntegrand α n (Ê₂ f) z θ ≤ Cn·(HkIntegrand α n f z θ + HkIntegrand α n (D_θ f) z θ)`

with `Cn` depending only on `n`. -/
theorem E2hat_HkIntegrand_le_uniform_pt (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α →
      Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
          ≤ Cn * (Work.Spaces.HkIntegrand α n f z θ
              + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ) := by
  obtain ⟨K, hK0, hKb⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound n
  refine ⟨18 * zmulC n * (1 + K) ^ 2 + 1, ?_, ?_⟩
  · have h : 0 ≤ zmulC n * (1 + K) ^ 2 := mul_nonneg (zmulC_pos n).le (sq_nonneg _)
    linarith
  · intro α f hα hf z hz θ hθ
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hDth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f) := by
      simpa using hf.DthIter 1
    have hphi : ∀ m : ℕ, ContDiffOn ℝ m (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) :=
      phiZ_contDiffOn
    have hA : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) :=
      smoothOpen_const_mul 2 (smoothOpen_mul (smoothOpen_zOnly hphi) hf)
    have hB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) :=
      smoothOpen_const_mul 3 (smoothOpen_mul (smoothOpen_zOnly hphi) hDth)
    rw [Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f]
    have h1 := Work.FTS.GalFields.RHS.HkIntegrand_add_le_open α n hα hA hB z hzIz θ hθI
    have h1' : Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)
            + 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
        ≤ 2 * (Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
          + Work.Spaces.HkIntegrand α n
              (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ) := by
      simpa only [Pi.add_apply] using h1
    have h2 := Work.FTS.LocData.HkIntegrand_const_mul α n 2
      (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
    have h3 := Work.FTS.LocData.HkIntegrand_const_mul α n 3
      (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ
    have h2' : Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
        = 4 * Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ := by
      rw [h2]; norm_num
    have h3' : Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
        = 9 * Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ := by
      rw [h3]; norm_num
    have h4 := HkIntegrand_zmul_SO α n (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb hphi f hf
      z hz θ hθ
    have h5 := HkIntegrand_zmul_SO α n (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb hphi
      (Work.Spaces.Dth f) hDth z hz θ hθ
    have hX : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
      Work.Spaces.HkIntegrand_nonneg α n f z θ
    have hY : 0 ≤ Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ
    have hK1 : (0 : ℝ) ≤ (1 + K) ^ 2 := by positivity
    have hC0 : 0 ≤ zmulC n * (1 + K) ^ 2 := mul_nonneg (zmulC_pos n).le hK1
    have hCX : 0 ≤ zmulC n * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ :=
      mul_nonneg hC0 hX
    have hCY : 0 ≤ zmulC n * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
      mul_nonneg hC0 hY
    nlinarith [h1', h2', h3', h4, h5, hX, hY, hCX, hCY]

end Work.FTS.StrongEps.EpsE4Thr.E2hatOAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_bd0_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.HardyOpen

open Work.FTS.CoercivityFix.Coer1T

/-! ## Private open-class helpers

The `L¹`/`L²` bookkeeping of `Work.FTS.CoercivityFix.Coer1T.L12f_bd0`
(`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`) is re-proved here in the *open*
smoothness class `Work.FTS.EllipticEst.SmoothOpen f` (`C^∞` on the open quadrant
`(0,∞) × (0,π/2)`), for use in the boundary estimate below:

* `bd0_sliceSq` — the squared angular slice `θ ↦ (f s θ)²` is `L¹` on `Iθ` for `s > 0`;
* `bd0_B4_aesm`, `bd0_B4_sqrt_aesm_mono` — a.e. strong measurability of `s ↦ √(B4 α f s)`;
* `bd0_dens_abs_le` — the density bound `|L₁₂dens(K,f,s)| ≤ √3·s/(1+s)²·√(B4 α f s)`;
* `bd0_L12f_abs_le_prim` — `|L₁₂ f z| ≤ √3 ∫_{(0,z]} s√(B4 α f s)` for `0 < z ≤ 1`;
* `bd0_L12f_sq_le_small` — `(L₁₂ f z)² ≤ 3 z³ ∫_{(0,z]} B4 α f` for `0 < z ≤ 1`.

The only `SmoothQuad` inputs of the original chain are the joint continuity of the
`ℋ⁴`-integrand (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`) and the angular
slice integrability of `f²`; everything else already needs no smoothness hypothesis.  The
helpers are `private` because the open-class analogues are also being produced by the sibling
tasks of this directory. -/

/-- The squared angular slice `θ ↦ (f s θ)²` is integrable on `Iθ` for `s > 0`, for a datum
that is continuous on the *open* quadrant and lies in `ℋ⁴`.

For a.e. `θ ∈ Iθ` (all `θ ∈ Ioo 0 (π/2)`) one has `0 < sin(2θ) ≤ 1` and `w s ≥ 1`, so
`(f s θ)² ≤ (f s θ·(w s/sin(2θ)^{η/2}))² ≤ HkIntegrand α 4 f s θ`
(`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`); the majorant is integrable on `Iθ` by `hmem.1`,
and the dominated function is a.e. strongly measurable there by
`Work.Spaces.aesm_slice_of_continuousOn_Qd`. -/
private theorem bd0_sliceSq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ := by
  have hquad : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := hC
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
    simpa only [Function.uncurry] using h2
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f s θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) hquad hs
  refine MeasureTheory.Integrable.mono' (hmem.1 s (le_of_lt hs)) haesm ?_
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
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hs]
  have hkey : 1 ≤ Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f s θ) ^ 2 ≤ (f s θ * (Work.Spaces.w s
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f s θ) ^ 2 = (f s θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f s θ) ^ 2
            * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f s θ * (Work.Spaces.w s
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f s θ) ^ 2‖ = (f s θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f s θ * (Work.Spaces.w s
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f s θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 0 (by norm_num)

/-- A.e. strong measurability of `s ↦ B4 α f s = ∫_θ HkIntegrand α 4 f s θ` on `Iz`, from
`C^∞` on the open quadrant: the joint integrand is continuous there
(`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`) hence a.e. strongly measurable
(`Work.Spaces.aesm_of_continuousOn_Qd`), and Fubini gives the measurability of the partial
integral. -/
private theorem bd0_B4_aesm (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (B4 α f) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
    (hsm.continuousOn_HkIntegrand α 4)).integral_prod_right'

/-- The restriction of `bd0_B4_aesm` to subsets of `Iz` (the open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.B4_sqrt_aesm_mono`). -/
private theorem bd0_B4_sqrt_aesm_mono (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun s => Real.sqrt (B4 α f s)) (MeasureTheory.volume.restrict u) :=
  (Real.continuous_sqrt.comp_aestronglyMeasurable (bd0_B4_aesm α hsm)).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

/-- The `L₁₂`-density bound in the open class: for `s > 0`,
`|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)`
(the open-class analogue of `Work.FTS.CoercivityFix.Coer1T.dens_abs_le`). -/
private theorem bd0_dens_abs_le (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ}
    (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ :=
    bd0_sliceSq hsm.continuousOn hmem hs
  have h1 : |Work.Elliptic.L12dens f s| ≤ Real.sqrt 3 * Real.sqrt
      (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s :=
    Work.FTS.H2.l12q_l12dens_slice f hs hsl
  rw [Work.FTS.H2.L12dens_eq_FM_K f s] at h1
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  -- the a.e. pointwise domination `(f s θ)^2 ≤ HkIntegrand α 4 f s θ / (w s)^2`
  have hpt : (fun θ => (f s θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
  have hint : ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2 ≤ B4 α f s / (Work.Spaces.w s) ^ 2 := by
    have hg : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
    rwa [MeasureTheory.integral_div] at h
  have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
      ≤ Real.sqrt (B4 α f s) / Work.Spaces.w s := by
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
        ≤ Real.sqrt (B4 α f s / (Work.Spaces.w s) ^ 2) := Real.sqrt_le_sqrt hint
      _ = Real.sqrt (B4 α f s) / Real.sqrt ((Work.Spaces.w s) ^ 2) :=
          Real.sqrt_div (B4_nonneg α f s) _
      _ = Real.sqrt (B4 α f s) / Work.Spaces.w s := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
  have h5 : Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
    calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
        ≤ Real.sqrt 3 * (Real.sqrt (B4 α f s) / Work.Spaces.w s) / s := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs)
          exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
          rw [Work.Spaces.w]
          field_simp
  exact le_trans h1 h5

/-- `|L₁₂ f z| ≤ √3 ∫_{(0,z]} s √(B4 α f s)` for `0 < z ≤ 1`, in the open class
(the analogue of `Work.FTS.CoercivityFix.Coer1T.L12f_abs_le_prim`). -/
private theorem bd0_L12f_abs_le_prim (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, s * Real.sqrt (B4 α f s) := by
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hrepr : Work.Coercivity.L12f f z = -(∫ s in Set.Ioc 0 z, G s) := by
    rw [L12f_eq_neg_prim hint hl12 hz, intervalIntegral.integral_of_le hz.le]
  rw [hrepr, abs_neg]
  -- the majorant `maj s = √3 * (s * √(B4 s))`
  have hu : Set.Ioc (0 : ℝ) z ⊆ Work.Spaces.Iz := fun t ht => le_of_lt ht.1
  have hmaj_aesm : AEStronglyMeasurable
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (B4 α f s)))
      (volume.restrict (Set.Ioc 0 z)) :=
    ((continuous_id.aestronglyMeasurable.mul (bd0_B4_sqrt_aesm_mono α hsm hu)).const_mul
      (Real.sqrt 3))
  -- the majorant is integrable
  have hBint : MeasureTheory.IntegrableOn (B4 α f) (Set.Ioc 0 z) :=
    (B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 z) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hmaj_bound : ∀ s ∈ Set.Ioc 0 z,
      Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) ≤ (Real.sqrt 3 / 2) * (1 + B4 α f s) := by
    intro s hs
    have hBs : 0 ≤ B4 α f s := B4_nonneg α f s
    have hle1 : s ≤ 1 := le_trans hs.2 hz1
    have hs0 : 0 < s := hs.1
    have hsqrt_le : Real.sqrt (B4 α f s) ≤ (1 + B4 α f s) / 2 := by
      nlinarith [Real.sq_sqrt hBs, sq_nonneg (Real.sqrt (B4 α f s) - 1)]
    have hsle : s * Real.sqrt (B4 α f s) ≤ Real.sqrt (B4 α f s) := by
      nlinarith [hle1, hs0, Real.sqrt_nonneg (B4 α f s)]
    nlinarith [hsqrt_le, hsle, Real.sqrt_nonneg 3]
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (B4 α f s))) (Set.Ioc 0 z) :=
    ((hconst.add hBint).const_mul (Real.sqrt 3 / 2)).mono' hmaj_aesm
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => by
        rw [Real.norm_of_nonneg (by
          have hx0 : 0 < x := hx.1
          positivity)]
        exact hmaj_bound x hx))
  -- the pointwise domination of `G`
  have hG_bd : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 z)), ‖G s‖
      ≤ Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have h1 := bd0_dens_abs_le α hsm hmem hs0
    have h2 : s / (1 + s) ^ 2 ≤ s := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg s, le_of_lt hs0]
    rw [Real.norm_eq_abs]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := h1
      _ ≤ Real.sqrt 3 * s * Real.sqrt (B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := by ring
  have hbd := MeasureTheory.norm_integral_le_of_norm_le hmaj_int hG_bd
  rw [Real.norm_eq_abs] at hbd
  calc |∫ s in Set.Ioc 0 z, G s|
      ≤ ∫ s in Set.Ioc 0 z, Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := hbd
    _ = Real.sqrt 3 * ∫ s in Set.Ioc 0 z, s * Real.sqrt (B4 α f s) := by
        rw [MeasureTheory.integral_const_mul]

/-- Near the origin the tail of the density grows at most like `z^{3/2}`:
`(L₁₂ f z)² ≤ 3 z³ ∫_{(0,z]} B4 α f` for `0 < z ≤ 1`, in the open class
(the analogue of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_le_small`). -/
private theorem bd0_L12f_sq_le_small (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s := by
  set Ψ : ℝ → ℝ := fun s => s * Real.sqrt (B4 α f s) with hΨdef
  have hu : Set.Ioc (0 : ℝ) z ⊆ Work.Spaces.Iz := fun t ht => le_of_lt ht.1
  have hBint : MeasureTheory.IntegrableOn (B4 α f) (Set.Ioc 0 z) :=
    (B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have hΨ_aesm : AEStronglyMeasurable Ψ (volume.restrict (Set.Ioc 0 z)) :=
    continuous_id.aestronglyMeasurable.mul (bd0_B4_sqrt_aesm_mono α hsm hu)
  have hΨ2_eq : ∀ s, (Ψ s) ^ 2 = s ^ 2 * B4 α f s := by
    intro s
    rw [hΨdef]
    simp only
    rw [mul_pow, Real.sq_sqrt (B4_nonneg α f s)]
  have hΨ2_int : MeasureTheory.IntegrableOn (fun s => (Ψ s) ^ 2) (Set.Ioc 0 z) := by
    refine (hBint.const_mul (z ^ 2)).mono' (hΨ_aesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hΨ2_eq s]
    have hs2 : s ^ 2 ≤ z ^ 2 := by nlinarith [hs.1, hs.2, le_of_lt hz]
    exact mul_le_mul_of_nonneg_right hs2 (B4_nonneg α f s)
  have hΨmem : MemLp Ψ 2 (volume.restrict (Set.Ioc 0 z)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hΨ_aesm).mpr hΨ2_int
  have hcs := cs_one hz hΨmem
  have hΨ2_le : ∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 ≤ z ^ 2 * ∫ s in Set.Ioc 0 z, B4 α f s := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => sq_nonneg _)
      (hBint.const_mul (z ^ 2)) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    show Ψ s ^ 2 ≤ z ^ 2 * B4 α f s
    rw [hΨ2_eq s]
    have hs2 : s ^ 2 ≤ z ^ 2 := by nlinarith [hs.1, hs.2, le_of_lt hz]
    exact mul_le_mul_of_nonneg_right hs2 (B4_nonneg α f s)
  have hAnn : 0 ≤ ∫ s in Set.Ioc 0 z, Ψ s :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun s hs => mul_nonneg (le_of_lt hs.1) (Real.sqrt_nonneg _))
  have h1 := bd0_L12f_abs_le_prim α hsm hmem hint hl12 hz hz1
  have habs := abs_le.mp h1
  have key : (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := by
    have h3A : 0 ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s :=
      mul_nonneg (Real.sqrt_nonneg 3) hAnn
    have h1' : (Work.Coercivity.L12f f z) ^ 2
        ≤ (Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s) ^ 2 :=
      sq_le_sq' (by linarith [habs.1]) habs.2
    rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at h1'
    linarith
  calc (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := key
    _ ≤ 3 * (z * ∫ s in Set.Ioc 0 z, (Ψ s) ^ 2) := by linarith [hcs]
    _ ≤ 3 * (z * (z ^ 2 * ∫ s in Set.Ioc 0 z, B4 α f s)) := by
        have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
        have := mul_le_mul_of_nonneg_left hΨ2_le hz0
        linarith
    _ = 3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s := by ring

/-- `bd0` of `HardyHyp` in the *open* class: the two boundary terms `(L₁₂ f)²/z^{2j-1}` and `w z·(L₁₂ f)²` vanish as `z → 0⁺` (`j ≤ 2`), from `SmoothOpen f` (in place of `SmoothQuad f`).  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_bd0` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`), which squeezes both terms against `3·∫_{(0,z]} B4 α f` (resp. `12·`) using the small-`z` estimate `(L₁₂ f z)² ≤ 3 z³ ∫_{(0,z]} B4 α f` for `0 < z ≤ 1` and `Ioc_B4_tendsto_zero` (both hypothesis-free apart from `HkMem`).  The small-`z` estimate is the open-class adaptation of `L12f_sq_le_small`/`L12f_abs_le_prim` (helper lemmas may be proved inside the same file), whose only `SmoothQuad` use is the a.e. strong measurability of `s ↦ √(B4 α f s)` (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` + `Work.Spaces.aesm_of_continuousOn_Qd`) and the density bound `dens_abs_le` (open version from `Work.Spaces.sq_le_HkIntegrand_z`). -/
theorem L12f_bd0_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) (j : ℕ) (hj : j ≤ 2) :
    Filter.Tendsto (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => Work.Spaces.w z * (Work.Coercivity.L12f f z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hmem1 : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      (fun z hz => ⟨hz.1, le_of_lt hz.2⟩)
  have hβ : Filter.Tendsto (fun z => ∫ s in Set.Ioc 0 z, B4 α f s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Ioc_B4_tendsto_zero α hmem
  have h2j : (2 * (j : ℝ)) ≤ 4 := by
    have h2 : 2 * j ≤ 4 := by omega
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring]
    exact_mod_cast h2
  constructor
  · refine squeeze_zero' (g := fun z => 3 * ∫ s in Set.Ioc 0 z, B4 α f s) ?_ ?_
      (by simpa using hβ.const_mul 3)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact div_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hz _))
    · filter_upwards [self_mem_nhdsWithin, hmem1] with z hz hz1
      have hX := bd0_L12f_sq_le_small α hsm hmem hint hl12 hz hz1.2
      have hzpow : z ^ (3 : ℕ) ≤ z ^ (2 * (j : ℝ) - 1) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hz hz1.2
          (show (2 * (j : ℝ) - 1) ≤ 3 by linarith)
        simpa using h
      have hstep : (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)
          ≤ (Work.Coercivity.L12f f z) ^ 2 / z ^ 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hz 3) hzpow
      have hstep2 : (Work.Coercivity.L12f f z) ^ 2 / z ^ 3
          ≤ 3 * (∫ s in Set.Ioc 0 z, B4 α f s) := by
        rw [div_le_iff₀ (pow_pos hz 3)]
        nlinarith [hX]
      exact le_trans hstep hstep2
  · refine squeeze_zero' (g := fun z => 12 * ∫ s in Set.Ioc 0 z, B4 α f s) ?_ ?_
      (by simpa using hβ.const_mul 12)
    · filter_upwards with z
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      exact mul_nonneg hw (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, hmem1] with z hz hz1
      have hX := bd0_L12f_sq_le_small α hsm hmem hint hl12 hz hz1.2
      have hβnn : 0 ≤ ∫ s in Set.Ioc 0 z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun s _ => B4_nonneg α f s)
      have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      have h4 : (1 + z) ^ 2 ≤ 4 := by
        have h5 : 1 + z ≤ 2 := by linarith [hz1.2]
        have hz0 : (0 : ℝ) < z := hz
        have h6 : (0 : ℝ) ≤ 1 + z := by linarith
        calc (1 + z) ^ 2 = (1 + z) * (1 + z) := by ring
          _ ≤ 2 * 2 := mul_le_mul h5 h5 h6 (by linarith)
          _ = 4 := by norm_num
      rw [hw]
      have hz0 : (0 : ℝ) < z := hz
      rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hz0 2)]
      have h1 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
          ≤ 4 * (3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s) :=
        mul_le_mul h4 hX (sq_nonneg _) (by norm_num)
      have h2 : 4 * (3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s)
          ≤ 12 * (∫ s in Set.Ioc 0 z, B4 α f s) * z ^ 2 := by
        nlinarith [hβnn, hz0, hz1.2, sq_nonneg z, pow_pos hz0 2,
          mul_le_mul_of_nonneg_left hz1.2 (mul_nonneg (show (0:ℝ) ≤ 12 by norm_num) hβnn)]
      linarith [h1, h2]

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_bdTop_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.HardyOpen

open Work.FTS.CoercivityFix.Coer1T (B4 B4_nonneg B4_integrableOn B4_tail_tendsto)

set_option maxHeartbeats 800000

/-! ## The open-class prerequisites of the large-`z` estimate for `L₁₂`

`Work.FTS.CoercivityFix.Coer1T.L12f_bdTop` is proved from the large-`z` bound
`L12f_abs_le_large`, whose proof uses `SmoothQuad` only through

* the a.e. strong measurability of `s ↦ √(B4 α f s)` on `(z,∞)` (via `B4_sqrt_aesm_mono`),
  which in the open class comes from `SmoothOpen.continuousOn_HkIntegrand` +
  `Work.Spaces.aesm_of_continuousOn_Qd`;
* the density bound `dens_abs_le`, whose proof uses `SmoothQuad` only through the
  slice-square integrability `l12q_slice_sq_integrableOn`, i.e. through joint continuity of
  `(z,θ) ↦ (f z θ)²` on the open quadrant.

Both uses are replaced below by their `SmoothOpen` analogues.  Everything else in the chain
(`B4_integrableOn`, `dens`-domination by `HkIntegrand`, Cauchy–Schwarz, `B4_tail_tendsto`,
`integral_Ioi_inv_sq`, `inv_memLp_Ioi`) is hypothesis-free apart from `HkMem α 4 f`, so those
lemmas are re-used as they are. -/

/-- Joint continuity of `(z,θ) ↦ (f z θ)²` on the open quadrant, from `SmoothOpen f`. -/
theorem bdTop_continuousOn_quad_sq {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 := by
  rw [show (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      = (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) from by funext p; rfl]
  exact ((hF.forall 0).continuousOn).pow 2

/-- The squared angular slice is integrable on `Iθ` for `z > 0`, from `SmoothOpen f` and
`HkMem α 4 f` (the open-class analogue of `Work.FTS.H2.l12q_slice_sq_integrableOn`). -/
theorem bdTop_slice_sq_integrableOn (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (bdTop_continuousOn_quad_sq hF) hz
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

/-- A.e. strong measurability of `B4 α f = ∫_θ HkIntegrand α 4 f` on `Iz`, from `SmoothOpen f`
(open analogue of `B4_aesm`). -/
theorem bdTop_B4_aesm (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (B4 α f) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (hF.continuousOn_HkIntegrand α 4)).integral_prod_right'

/-- A.e. strong measurability of `s ↦ √(B4 α f s)` on `Iz`, from `SmoothOpen f`. -/
theorem bdTop_B4_sqrt_aesm (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun s => Real.sqrt (B4 α f s))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (bdTop_B4_aesm α hF)

theorem bdTop_B4_sqrt_aesm_mono (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    MeasureTheory.AEStronglyMeasurable (fun s => Real.sqrt (B4 α f s))
      (MeasureTheory.volume.restrict u) :=
  (bdTop_B4_sqrt_aesm α hF).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

theorem bdTop_sqrt_B4_memLp_Ioi (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MemLp (fun s : ℝ => Real.sqrt (B4 α f s)) 2 (volume.restrict (Set.Ioi z)) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    (bdTop_B4_sqrt_aesm_mono α hF (fun t ht => le_of_lt (lt_trans hz ht)))).mpr ?_
  refine ((B4_integrableOn α f hmem).mono_set
    (fun t ht => lt_trans hz ht)).congr_fun (fun s _ => ?_) measurableSet_Ioi
  exact (Real.sq_sqrt (B4_nonneg α f s)).symm

/-- The majorant `s ↦ s⁻¹ √(B4 α f s)` is integrable on `(z,∞)` for `z > 0`. -/
theorem bdTop_inv_mul_sqrt_B4_integrableOn (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun s => s⁻¹ * Real.sqrt (B4 α f s)) (Set.Ioi z) :=
  (Work.FTS.CoercivityFix.Coer1T.inv_memLp_Ioi hz).integrable_mul
    (bdTop_sqrt_B4_memLp_Ioi α hF hmem hz)

/-- The `L₁₂`-density obeys `|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)` for `s > 0`;
open-class version of `Work.FTS.CoercivityFix.Coer1T.dens_abs_le`. -/
theorem bdTop_dens_abs_le (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {s : ℝ} (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ :=
    bdTop_slice_sq_integrableOn α hF hmem hs
  have h1 : |Work.Elliptic.L12dens f s| ≤ Real.sqrt 3 * Real.sqrt
      (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s :=
    Work.FTS.H2.l12q_l12dens_slice f hs hsl
  rw [Work.FTS.H2.L12dens_eq_FM_K f s] at h1
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  -- the a.e. pointwise domination `(f s θ)^2 ≤ HkIntegrand α 4 f s θ / (w s)^2`
  have hpt : (fun θ => (f s θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ =>
        Work.FTS.CoercivityFix.Coer1T.slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
  have hint : ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2
      ≤ B4 α f s / (Work.Spaces.w s) ^ 2 := by
    have hg : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
    rwa [MeasureTheory.integral_div] at h
  have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
      ≤ Real.sqrt (B4 α f s) / Work.Spaces.w s := by
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
        ≤ Real.sqrt (B4 α f s / (Work.Spaces.w s) ^ 2) := Real.sqrt_le_sqrt hint
      _ = Real.sqrt (B4 α f s) / Real.sqrt ((Work.Spaces.w s) ^ 2) :=
          Real.sqrt_div (B4_nonneg α f s) _
      _ = Real.sqrt (B4 α f s) / Work.Spaces.w s := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
  have h5 : Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
    calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
        ≤ Real.sqrt 3 * (Real.sqrt (B4 α f s) / Work.Spaces.w s) / s := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs)
          exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
          rw [Work.Spaces.w]
          field_simp
  exact le_trans h1 h5

/-- `|L12f f z| ≤ √3 · √(1/z) · √(∫_{s>z} B4 α f s)` for `z ≥ 1`; open-class version of
`Work.FTS.CoercivityFix.Coer1T.L12f_abs_le_large`. -/
theorem bdTop_L12f_abs_le_large (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz1 : 1 ≤ z) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) := by
  have hz : 0 < z := lt_of_lt_of_le one_pos hz1
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s => s⁻¹ * Real.sqrt (B4 α f s)) (Set.Ioi z) :=
    bdTop_inv_mul_sqrt_B4_integrableOn α hF hmem hz
  have h1 : |Work.Coercivity.L12f f z| ≤ ∫ s in Set.Ioi z, |G s| := by
    have h := MeasureTheory.norm_integral_le_integral_norm (f := G)
      (μ := volume.restrict (Set.Ioi z))
    rw [Work.Coercivity.L12f, Work.FM.L12]
    simpa [G, Real.norm_eq_abs] using h
  have h2 : ∫ s in Set.Ioi z, |G s|
      ≤ Real.sqrt 3 * ∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (hmaj_int.const_mul (Real.sqrt 3)) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := lt_trans hz hs
    have hb := bdTop_dens_abs_le α hF hmem hs0
    have hle : s / (1 + s) ^ 2 ≤ s⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [le_of_lt hs0]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := hb
      _ ≤ Real.sqrt 3 * s⁻¹ * Real.sqrt (B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s⁻¹ * Real.sqrt (B4 α f s)) := by ring
  have hcs := Work.Spaces.cs_integral (u := fun s : ℝ => s⁻¹)
    (v := fun s : ℝ => Real.sqrt (B4 α f s)) (s := Set.Ioi z)
    (Work.FTS.CoercivityFix.Coer1T.inv_memLp_Ioi hz)
    (bdTop_sqrt_B4_memLp_Ioi α hF hmem hz)
  have hv2 : ∫ s in Set.Ioi z, (Real.sqrt (B4 α f s)) ^ 2 = ∫ s in Set.Ioi z, B4 α f s := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    exact Real.sq_sqrt (B4_nonneg α f s)
  rw [Work.FTS.CoercivityFix.Coer1T.integral_Ioi_inv_sq hz, hv2] at hcs
  have hC : 0 ≤ (1 / z) * ∫ s in Set.Ioi z, B4 α f s := by
    have : (0 : ℝ) ≤ ∫ s in Set.Ioi z, B4 α f s :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
    positivity
  have hsqrt : ∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s)
      ≤ Real.sqrt ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
    have hsq : (∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s)) ^ 2
        ≤ (Real.sqrt ((1 / z) * ∫ s in Set.Ioi z, B4 α f s)) ^ 2 := by
      rw [Real.sq_sqrt hC]
      exact hcs
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _))
  have hfinal : Real.sqrt 3 * (∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s))
      ≤ Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 3)
    refine le_trans hsqrt (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity)]
  linarith [h1, h2, hfinal]

/-- `bdTop` of `HardyHyp` in the *open* class: the two boundary terms `(L₁₂ f)²/z^{2j-1}` and `w z·(L₁₂ f)²` vanish as `z → ∞` (any `j`), from `SmoothOpen f` (in place of `SmoothQuad f`).  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_bdTop` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`), which squeezes both terms against `3·∫_{(z,∞)} B4 α f` (resp. `12·`) using the large-`z` estimate `|L₁₂ f z| ≤ √3·√(1/z)·√(∫_{(z,∞)} B4 α f)` for `1 ≤ z` and `B4_tail_tendsto` (both hypothesis-free apart from `HkMem`).  The large-`z` estimate is the open-class adaptation of `L12f_abs_le_large`/`inv_mul_sqrt_B4_integrableOn`/`sqrt_B4_memLp_Ioi` (helper lemmas may be proved inside the same file), whose only `SmoothQuad` use is the a.e. strong measurability of `s ↦ √(B4 α f s)` (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` + `Work.Spaces.aesm_of_continuousOn_Qd`) and the density bound `dens_abs_le` (open version from `Work.Spaces.sq_le_HkIntegrand_z`). -/
theorem L12f_bdTop_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) (j : ℕ) :
    Filter.Tendsto (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun z => Work.Spaces.w z * (Work.Coercivity.L12f f z) ^ 2)
        Filter.atTop (nhds 0) := by
  have hT : Filter.Tendsto (fun z => ∫ s in Set.Ioi z, B4 α f s) Filter.atTop (𝓝 0) :=
    B4_tail_tendsto α f
  have hmem1 : Set.Ici (1 : ℝ) ∈ Filter.atTop := Filter.Ici_mem_atTop 1
  constructor
  · refine squeeze_zero' (g := fun z => 3 * ∫ s in Set.Ioi z, B4 α f s) ?_ ?_
      (by simpa using hT.const_mul 3)
    · filter_upwards [hmem1] with z hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
      exact div_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hz0 _))
    · filter_upwards [hmem1] with z hz
      have hz1 : 1 ≤ z := hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
      have hX := bdTop_L12f_abs_le_large α hsm hmem hz1
      have hTnn : 0 ≤ ∫ s in Set.Ioi z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
      have hsq' : (Work.Coercivity.L12f f z) ^ 2
          ≤ 3 * ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
        have h1 : (Real.sqrt (1 / z)) ^ 2 = 1 / z := Real.sq_sqrt (by positivity)
        have h2 : (Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) ^ 2
            = ∫ s in Set.Ioi z, B4 α f s := Real.sq_sqrt hTnn
        have habs := abs_le.mp hX
        have h3 : (Work.Coercivity.L12f f z) ^ 2
            ≤ (Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s))) ^ 2 :=
          sq_le_sq' (by linarith [habs.1]) habs.2
        rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pow, h1, h2] at h3
        linarith [h3]
      have hzj : (1 : ℝ) ≤ z ^ (2 * (j : ℝ) - 1) * z := by
        have h2j : (-1 : ℝ) ≤ 2 * (j : ℝ) - 1 := by
          have : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
          linarith
        have h3 : z ^ (-1 : ℝ) ≤ z ^ (2 * (j : ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_le hz1 h2j
        rw [Real.rpow_neg_one] at h3
        have := mul_le_mul_of_nonneg_right h3 hz0.le
        rw [inv_mul_cancel₀ (ne_of_gt hz0)] at this
        linarith
      have hstep : (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)
          ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) := by
        have hz_inv : 1 / z ≤ z ^ (2 * (j : ℝ) - 1) := (div_le_iff₀ hz0).mpr hzj
        have hstep2 : 3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s)
            ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) * z ^ (2 * (j : ℝ) - 1) := by
          have h3T : (0 : ℝ) ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) := by linarith
          have := mul_le_mul_of_nonneg_right hz_inv h3T
          nlinarith [this]
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hz0 (2 * (j : ℝ) - 1))]
        linarith [hsq', hstep2]
      exact hstep
  · refine squeeze_zero' (g := fun z => 12 * ∫ s in Set.Ioi z, B4 α f s) ?_ ?_
      (by simpa using hT.const_mul 12)
    · filter_upwards with z
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      exact mul_nonneg hw (sq_nonneg _)
    · filter_upwards [hmem1] with z hz
      have hz1 : 1 ≤ z := hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
      have hX := bdTop_L12f_abs_le_large α hsm hmem hz1
      have hTnn : 0 ≤ ∫ s in Set.Ioi z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
      have habs := abs_le.mp hX
      have hsq' : (Work.Coercivity.L12f f z) ^ 2
          ≤ 3 * ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
        have h1 : (Real.sqrt (1 / z)) ^ 2 = 1 / z := Real.sq_sqrt (by positivity)
        have h2 : (Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) ^ 2
            = ∫ s in Set.Ioi z, B4 α f s := Real.sq_sqrt hTnn
        have h3 : (Work.Coercivity.L12f f z) ^ 2
            ≤ (Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s))) ^ 2 :=
          sq_le_sq' (by linarith [habs.1]) habs.2
        rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pow, h1, h2] at h3
        linarith [h3]
      have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      have h4 : (1 + z) ^ 2 ≤ 4 * z ^ 2 := by nlinarith [hz1, sq_nonneg z, sq_nonneg (z - 1)]
      have hz2 : (0 : ℝ) < z ^ 2 := by positivity
      have hstep2 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
          ≤ 12 * (∫ s in Set.Ioi z, B4 α f s) * z ^ 2 := by
        have h5 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
            ≤ 4 * z ^ 2 * (3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s)) :=
          mul_le_mul h4 hsq' (sq_nonneg _) (by positivity)
        have h6 : 4 * z ^ 2 * (3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s))
            = 12 * (∫ s in Set.Ioi z, B4 α f s) * z := by
          field_simp
          ring
        rw [h6] at h5
        have h7 : 12 * (∫ s in Set.Ioi z, B4 α f s) * z
            ≤ 12 * (∫ s in Set.Ioi z, B4 α f s) * z ^ 2 := by
          have := mul_le_mul_of_nonneg_left hz1
            (by linarith : (0:ℝ) ≤ 12 * (∫ s in Set.Ioi z, B4 α f s))
          nlinarith [this]
        linarith [h5, h7]
      rw [hw, div_mul_eq_mul_div, div_le_iff₀ hz2]
      linarith [hstep2]

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_sq_div_large_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.HardyOpen

namespace LargeAux

/-! ## The angular slice and the density bound -/

/-- The squared angular slice `θ ↦ (f z θ)²` is integrable on `Iθ` for `z > 0`, for a datum
which is `C^∞` on the open quadrant and in `ℋ⁴`.  This is
`Work.FTS.H2.l12q_slice_sq_integrableOn` with its smoothness hypothesis weakened from
`SmoothQuad f` to `SmoothOpen f` (the only use of `SmoothQuad` there is the a.e. strong
measurability of the slice). -/
theorem slice_sq_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := Work.Spaces.aesm_slice_of_continuousOn_Qd ((Function.uncurry f) ^ 2)
      (hsm.continuousOn.pow 2) hz
    simpa only [Function.uncurry, Pi.pow_apply] using h
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

/-- The `L₁₂`-density obeys `|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)` for `s > 0`:
the open-class version of `Work.FTS.CoercivityFix.Coer1T.dens_abs_le`. -/
theorem L12dens_abs_le_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ}
    (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2)
        * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_integrableOn_open α hsm hmem hs
  have h1 : |Work.Elliptic.L12dens f s| ≤ Real.sqrt 3 * Real.sqrt
      (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s :=
    Work.FTS.H2.l12q_l12dens_slice f hs hsl
  rw [Work.FTS.H2.L12dens_eq_FM_K f s] at h1
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  -- the a.e. pointwise domination `(f s θ)^2 ≤ HkIntegrand α 4 f s θ / (w s)^2`
  have hpt : (fun θ => (f s θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => Work.FTS.CoercivityFix.Coer1T.slice_sq_le_HkIntegrand_div_w_sq
        α hs hθ.1 hθ.2)
  have hint : ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2
      ≤ Work.FTS.CoercivityFix.Coer1T.B4 α f s / (Work.Spaces.w s) ^ 2 := by
    have hg : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
    rwa [MeasureTheory.integral_div] at h
  have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
      ≤ Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s := by
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
        ≤ Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s / (Work.Spaces.w s) ^ 2) :=
          Real.sqrt_le_sqrt hint
      _ = Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)
            / Real.sqrt ((Work.Spaces.w s) ^ 2) :=
          Real.sqrt_div (Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s) _
      _ = Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
  have h5 : Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2)
        * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
    calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
        ≤ Real.sqrt 3
            * (Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) / Work.Spaces.w s) / s := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs)
          exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s / (1 + s) ^ 2)
            * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s) := by
          rw [Work.Spaces.w]
          field_simp
  exact le_trans h1 h5

/-! ## The radial density `B4` and its square root -/

/-- A.e. strong measurability of `B4 α f` on `Iz`, from the joint continuity of the
`ℋ⁴`-integrand on the open quadrant. -/
theorem B4_aesm_open (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Work.FTS.CoercivityFix.Coer1T.B4 α f)
      (volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.continuousOn_HkIntegrand α 4
  exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

/-- A.e. strong measurability of `s ↦ √(B4 α f s)` on `Iz`. -/
theorem B4_sqrt_aesm_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun s => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      (volume.restrict Work.Spaces.Iz) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (B4_aesm_open α hsm)

/-- The a.e. strong measurability of `s ↦ √(B4 α f s)` restricted to any `u ⊆ Iz`. -/
theorem B4_sqrt_aesm_mono_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun s => Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s))
      (volume.restrict u) :=
  (B4_sqrt_aesm_open α hsm).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)




/-! ## The `L¹`-integrability of the density tail -/

/-- `s ↦ (L12dens K f s)² · s²` is integrable on `(1,∞)`. -/
theorem G_sq_mul_sq_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn
      (fun s => (Work.FM.L12dens Work.Spaces.K f s) ^ 2 * s ^ 2) (Set.Ioi 1) := by
  have hG : AEStronglyMeasurable (Work.FM.L12dens Work.Spaces.K f)
      (volume.restrict (Set.Ioi 1)) :=
    Work.FTS.CoercivityFix.Coer1T.L12dens_aesm_Ioi hcont
  have hmaj : MeasureTheory.IntegrableOn
      (fun s => 3 * Work.FTS.CoercivityFix.Coer1T.B4 α f s) (Set.Ioi 1) :=
    ((Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono_set
      (Set.Ioi_subset_Ioi zero_le_one)).const_mul 3
  refine hmaj.mono' ((hG.pow 2).mul (continuous_pow 2).aestronglyMeasurable) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hb := L12dens_abs_le_open α hsm hmem hs0
  have hB : 0 ≤ Work.FTS.CoercivityFix.Coer1T.B4 α f s :=
    Work.FTS.CoercivityFix.Coer1T.B4_nonneg α f s
  have habs := abs_le.mp hb
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hsq : (Work.FM.L12dens Work.Spaces.K f s) ^ 2
      ≤ (Real.sqrt 3 * (s / (1 + s) ^ 2)
          * Real.sqrt (Work.FTS.CoercivityFix.Coer1T.B4 α f s)) ^ 2 := by
    nlinarith [habs.1, habs.2]
  refine le_trans (mul_le_mul_of_nonneg_right hsq (sq_nonneg s)) ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt hB]
  rw [div_pow]
  have h4 : s ^ 4 ≤ (1 + s) ^ 4 := by
    have h2 : s ≤ (1 + s) ^ 2 := by nlinarith [sq_nonneg s]
    nlinarith [h2, sq_nonneg s, sq_nonneg (s ^ 2)]
  rw [show ((1 + s) ^ 2) ^ 2 = (1 + s) ^ 4 by ring]
  rw [show 3 * (s ^ 2 / (1 + s) ^ 4) * Work.FTS.CoercivityFix.Coer1T.B4 α f s * s ^ 2
      = 3 * ((s ^ 2 * s ^ 2) / (1 + s) ^ 4) * Work.FTS.CoercivityFix.Coer1T.B4 α f s by ring]
  rw [show s ^ 2 * s ^ 2 = s ^ 4 by ring]
  have h1 : s ^ 4 / (1 + s) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h4
  nlinarith [h1, hB]

/-- `(L12f f z)²` is integrable on `(1,∞)`, in the open class. -/
theorem L12f_sq_integrableOn_Ioi_one_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn (fun z => (Work.Coercivity.L12f f z) ^ 2) (Set.Ioi 1) := by
  have hG_int := G_sq_mul_sq_integrableOn_open α hsm hmem hcont
  have hGmem : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 1) :=
    hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have h := (Work.FTS.CoercivityFix.Coer1T.Hardy.Ioi_tail_sq_integrable
    (Work.FM.L12dens Work.Spaces.K f) hG_int hGmem).1
  simpa [Work.Coercivity.L12f, Work.FM.L12] using h

end LargeAux

/-- `intA` of `HardyHyp` on `(1,∞)` in the *open* class: `(L₁₂ f)²/z^{2j} ∈ L¹((1,∞))` for any `j`, from `SmoothOpen f` (in place of `SmoothQuad f`).  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_large` (`Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`) together with its helpers `L12f_sq_integrableOn_Ioi_one`, `G_sq_mul_sq_integrableOn`, `L12f_abs_le_large`, `inv_mul_sqrt_B4_integrableOn`, `sqrt_B4_memLp_Ioi` re-proved in the open class (put them in the same file); the only uses of `SmoothQuad` in that chain are the a.e. strong measurability of `s ↦ √(B4 α f s)` (from `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` + `Work.Spaces.aesm_of_continuousOn_Qd`) and the density bound `dens_abs_le` (whose open version follows from `Work.Spaces.sq_le_HkIntegrand_z` plus continuity of the angular slice, `Work.Spaces.aesm_slice_of_continuousOn_Qd`).  The inputs `L12f_eq_neg_prim`, `L12f_continuousOn`, `L12f_aesm_mono`, `B4_integrableOn`, `B4_tail_tendsto`, `integral_Ioi_inv_sq`, `inv_memLp_Ioi` and `Hardy.Ioi_tail_sq_integrable` need no smoothness at all. -/
theorem L12f_sq_div_large_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z)
    (j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))) (Set.Ioi 1) := by
  have h1 := LargeAux.L12f_sq_integrableOn_Ioi_one_open α hsm hmem hint hcont
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioi 1)) :=
    Work.FTS.CoercivityFix.Coer1T.L12f_aesm_mono hint hcont (Set.Ioi_subset_Ioi zero_le_one)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹)
      (volume.restrict (Set.Ioi 1)) := by
    have hEq : (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹) = fun z => (z ^ (2 * j))⁻¹ := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact (((continuous_pow (2 * j)).measurable.inv).aestronglyMeasurable).mono_measure
      (MeasureTheory.Measure.restrict_mono_set volume (Set.Ioi_subset_Ioi zero_le_one))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  refine h1.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hz1 : 1 ≤ z := le_of_lt hz
  have hzj : (1 : ℝ) ≤ z ^ (2 * (j : ℝ)) := by
    have h2j : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact one_le_pow₀ hz1
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))
      ≤ (Work.Coercivity.L12f f z) ^ 2 / 1 :=
        div_le_div_of_nonneg_left (sq_nonneg _) one_pos hzj
    _ = _ := by ring

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.intB_integrableOn_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.HardyOpen

/-- The angular slice `z ↦ ∫_θ (f z θ)²` is a.e. strongly measurable on `(0,∞)` for a datum
which is merely continuous on the open quadrant. -/
theorem phi_aesm_of_continuousOn {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((show ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) from hcont)).pow 2
  have haesmJoint : AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hc
  have hnumIz : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
  exact hnumIz.mono_measure (MeasureTheory.Measure.restrict_mono_set volume
    (show Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz from Set.Ioi_subset_Ici_self))

/-- `intB` of `HardyHyp` in the *open* class: `z ↦ (∫_θ f z θ²)/z^{2j}` is integrable on `(0,∞)` for `j ≤ 2`, from `SmoothOpen f` (in place of `SmoothQuad f`) and `HkMem α 4 f`.  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.intB_integrableOn` (in `Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`), whose only use of `SmoothQuad` is the a.e. strong measurability of `z ↦ ∫_θ (f z θ)²`, which in the open class follows from `ContinuousOn (Function.uncurry f) Q0` via `Work.Spaces.aesm_of_continuousOn_Qd` (using `Work.FTS.EllipticEst.SmoothOpen.forall 0`); the domination step is `phi_div_rpow_le_B4` and `B4_integrableOn`, both of which need only `hmem`. -/
theorem intB_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) (j : ℕ)
    (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ)))
      (Set.Ioi 0) := by
  have hnum : AEMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (phi_aesm_of_continuousOn
      ((Work.FTS.EllipticEst.SmoothOpen.forall hsm 0).continuousOn)).aemeasurable
  have hden : AEMeasurable (fun z : ℝ => z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 0)) := by
    have hEq : (fun z : ℝ => z ^ (2 * (j : ℝ))) = fun z => z ^ (2 * j) := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact ((continuous_pow (2 * j)).measurable).aemeasurable
  have haesm : AEStronglyMeasurable
      (fun z => (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 0)) := (hnum.div hden).aestronglyMeasurable
  refine (Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono' haesm ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
  rw [Real.norm_of_nonneg (div_nonneg (integral_nonneg fun θ => sq_nonneg _)
    (le_of_lt (Real.rpow_pos_of_pos hz _)))]
  exact Work.FTS.CoercivityFix.Coer1T.phi_div_rpow_le_B4 α hmem hz j hj

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO =====
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

/-- **The open-class integrability bundle**: `CoercivityFix.Coer1.IntPkg` with the three
`z`-integration-by-parts fields taken in the open class `CoercivityFix.Coer1SO.ZIBPO`. -/
structure IntPkgO (α : ℝ) (f : Fn) : Prop where
  /-- the squared `D_z`-blocks with the `η`-weight -/
  sqDzEta : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the `η`-weight -/
  sqMixedEta : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the `γ`-weight -/
  sqMixedGam : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      (Work.Spaces.mixed j i f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared `D_z`-blocks with the plain radial weight -/
  sqDzOne : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the plain radial weight -/
  sqMixedOne : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the `η`-weight -/
  intL_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L f z θ * f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_z f` with the `η`-weight -/
  intL_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_θ f` with the `γ`-weight -/
  intL_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the plain radial weight -/
  intL_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `Lhat`-pairing of `D_z f` with the `η`-weight -/
  intLhat_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `D_z`-commutator defect against `D_z f` with the `η`-weight -/
  intE2hat_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
      * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `f` with the `η`-weight -/
  hint_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * f z θ
      * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `D_z f` with the `η`-weight -/
  hint_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
      * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `D_θ f` with the `γ`-weight -/
  hint_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `f` with the plain radial weight -/
  hint_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * f z θ
      * Work.Spaces.w z ^ 2 / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `z`-integration-by-parts hypotheses for `f` -/
  zibp_f : Work.FTS.CoercivityFix.Coer1SO.ZIBPO f
  /-- the `z`-integration-by-parts hypotheses for `D_z f` -/
  zibp_Dz : Work.FTS.CoercivityFix.Coer1SO.ZIBPO (Work.Spaces.Dz f)
  /-- the `z`-integration-by-parts hypotheses for `D_θ f` -/
  zibp_Dth : Work.FTS.CoercivityFix.Coer1SO.ZIBPO (Work.Spaces.Dth f)

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.ampA_dzdIter_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

/-! ## The chart-side remainders `R_b`

Abbreviate `Tmul P = ½(1 - X²)·P'` and `Pphi = ¼(1 - X²)` (the chart-side pictures of
`Zop = z∂_z` and of `φ(z) = z/(1+z)²`, `E2Bound/ZopPhiDefs.lean`).  Since

  `Tmul ((1 - X²)·R) = ½(1 - X²)·((1 - X²)·R' - 2X·R) = (1 - X²)·(½((1 - X²)·R' - 2X·R))`,

the factor `(1 - X²)` is preserved by the iteration, and `Tmul^[b] Pphi = (1 - X²)·Rseq b`
with the recursion below. -/

/-- The chart-side remainder polynomials `R_b` of the iterates of `Pphi`: defined by
`Tmul^[b] Pphi = (1 - X²)·Rseq b`. -/
noncomputable def Rseq : ℕ → Polynomial ℝ
  | 0 => Polynomial.C (1 / 4)
  | k + 1 => Polynomial.C (1 / 2) *
      ((1 - Polynomial.X ^ 2) * Polynomial.derivative (Rseq k)
        - Polynomial.C 2 * Polynomial.X * Rseq k)

@[simp] lemma Rseq_zero : Rseq 0 = Polynomial.C (1 / 4) := rfl

@[simp] lemma Rseq_succ (k : ℕ) : Rseq (k + 1) = Polynomial.C (1 / 2) *
      ((1 - Polynomial.X ^ 2) * Polynomial.derivative (Rseq k)
        - Polynomial.C 2 * Polynomial.X * Rseq k) := rfl

/-- **The factor `(1 - X²)` is preserved by the `Tmul`-iteration**: `Tmul^[b] Pphi` is
`(1 - X²)` times the polynomial `Rseq b`. -/
lemma Tmul_iter_Pphi (b : ℕ) :
    Work.FTS.CoercivityFix.E2Bound.Tmul^[b] Work.FTS.CoercivityFix.E2Bound.Pphi
      = (1 - Polynomial.X ^ 2) * Rseq b := by
  induction b with
  | zero =>
      show Work.FTS.CoercivityFix.E2Bound.Pphi = (1 - Polynomial.X ^ 2) * Rseq 0
      rw [Work.FTS.CoercivityFix.E2Bound.Pphi_eq, Rseq_zero]
      ring
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Work.FTS.CoercivityFix.E2Bound.Tmul_apply,
        Rseq_succ]
      rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
        Polynomial.derivative_X_pow]
      norm_num
      ring

/-- Evaluating `(1 - X²)·R` in the chart: `gpoly ((1 - X²)·R) z = (1 - y²)·R(y)`, `y = zchart z`. -/
lemma gpoly_one_sub_sq_mul (R : Polynomial ℝ) (z : ℝ) :
    Work.FTS.CoercivityFix.E2Bound.gpoly ((1 - Polynomial.X ^ 2) * R) z
      = (1 - (Work.FTS.CoercivityFix.E2Bound.zchart z) ^ 2)
        * R.eval (Work.FTS.CoercivityFix.E2Bound.zchart z) := by
  simp only [Work.FTS.CoercivityFix.E2Bound.gpoly, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]

/-- `1 - y² = 4·φ(z)` for the chart variable `y = zchart z = (z-1)/(z+1)` (`z ≠ -1`). -/
lemma one_sub_zchart_sq (z : ℝ) (hz : z ≠ -1) :
    1 - (Work.FTS.CoercivityFix.E2Bound.zchart z) ^ 2 = 4 * (z / (1 + z) ^ 2) := by
  have h := Work.FTS.CoercivityFix.E2Bound.gpoly_Pphi (z := z) hz
  simp only [Work.FTS.CoercivityFix.E2Bound.gpoly, Work.FTS.CoercivityFix.E2Bound.Pphi,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one] at h
  rw [← h]
  ring

/-- **The `D_z`-iterates of the transfer profile `ampA α z = 2z/(c(α)(1+z)²)` are dominated by
`z/(1+z)²`** — in particular they are `O(z)` at `z → 0⁺` and `O(1/z)` at `z → ∞`.  (The
existing `E2pkg.ampA_dzdIter_bound` gives only *boundedness* on `(0,∞)`, which is not enough
for the boundary traces of the nonlocal term `-Γ(θ)·ampA α z·L₁₂(x)(z)` of `𝓛_Γ^T`: those need
the `z`-decay at `0⁺`.)

Route: `ampA α = (2/c(α))·φ` with `φ(z) = z/(1+z)²` (`ampA_eq_const_mul_fA`,
`Zop_iter_const_mul`), and the `Zop`-iterates of `φ` keep the factor `φ`:

* `Zop^[b] φ = gpoly (Tmul^[b] Pphi)` (`E2Bound.Zop_gpoly` iterated), and
  `Tmul P = ½(1-X²)·P'`, `Pphi = ¼(1-X²)`, so by induction `Tmul^[b] Pphi = (1-X²)·R_b` for
  polynomials `R_b`;
* on `(0,∞)` the chart variable `y = zchart z = (z-1)/(z+1)` lies in `[-1,1]`
  (`abs_zchart_le_one`) and `¼(1-y²) = φ(z)` exactly, so
  `|Zop^[b] φ z| = φ(z)·|R_b(y)| ≤ (Σ|coeffs of R_b|)·φ(z)`. -/
theorem ampA_dzdIter_abs_le (α : ℝ) (b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        ≤ K * (z / (1 + z) ^ 2) := by
  refine ⟨|2 / Work.Spaces.c α| * 4 * (Rseq b).sum (fun _ a => |a|), ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (abs_nonneg _) (by norm_num)) ?_
    rw [Polynomial.sum_def]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  · intro z hz
    -- the `φ`-iterate is dominated by `4·φ·(Σ|coeffs of Rseq b|)`
    have hkey : ∀ w : ℝ, 0 < w →
        |Work.Spaces.Zop^[b] (fun w : ℝ => w / (1 + w) ^ 2) w|
          ≤ 4 * (w / (1 + w) ^ 2) * (Rseq b).sum (fun _ a => |a|) := by
      intro w hw
      have hwm1 : w ≠ -1 := Work.FTS.CoercivityFix.E2Bound.zchart_ne_neg_one hw
      rw [Work.FTS.CoercivityFix.E2Bound.Zop_iter_gpoly b w hw, Tmul_iter_Pphi,
        gpoly_one_sub_sq_mul]
      rw [abs_mul, abs_of_nonneg (by rw [one_sub_zchart_sq w hwm1]; positivity)]
      rw [one_sub_zchart_sq w hwm1]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.CoercivityFix.E2Bound.poly_eval_abs_le _
          (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hw)) (by positivity)
    calc |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        = |(2 / Work.Spaces.c α) * Work.Spaces.Zop^[b] (fun w : ℝ => w / (1 + w) ^ 2) z| := by
            rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
              Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_eq_const_mul_fA,
              Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
      _ = |2 / Work.Spaces.c α| * |Work.Spaces.Zop^[b] (fun w : ℝ => w / (1 + w) ^ 2) z| :=
            abs_mul _ _
      _ ≤ |2 / Work.Spaces.c α| * (4 * (z / (1 + z) ^ 2) * (Rseq b).sum (fun _ a => |a|)) :=
            mul_le_mul_of_nonneg_left (hkey z hz) (abs_nonneg _)
      _ = (|2 / Work.Spaces.c α| * 4 * (Rseq b).sum (fun _ a => |a|)) * (z / (1 + z) ^ 2) := by
            ring

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.HkSum5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-`5` finite-sum closure**: a function agreeing on the open quadrant with the sum
`∑_{k<n} F k` of `ℋ⁵`-honest, `SmoothOpen` summands is `ℋ⁵`-honest, with the norm bound
`Xn5 α g ≤ √(2^n) ∑_k Xn5 α (F k)`. -/
theorem HkSumOpenClosure5 {α : ℝ} (hα : 0 < α) {n : ℕ} {g : Fn}
    {F : ℕ → Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5 g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsm : ∀ k ∈ Finset.range n, Work.FTS.EllipticEst.SmoothOpen (F k))
    (hm : ∀ k ∈ Finset.range n, Work.Spaces.HkMem α 5 (F k))
    (hag : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      g z θ = ∑ k ∈ Finset.range n, F k z θ) :
    Work.Spaces.HkMem α 5 g ∧
      Work.Spaces.HkNorm α 5 g ≤ Real.sqrt ((2 : ℝ) ^ n) * ∑ k ∈ Finset.range n,
        Work.Spaces.HkNorm α 5 (F k) := by
  classical
  set M : ℝ → ℝ → ℝ := fun z θ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
      Work.Spaces.HkIntegrand α 5 (F k) z θ with hM
  have hMnn : ∀ z θ : ℝ, 0 ≤ M z θ := by
    intro z θ
    show 0 ≤ (2 : ℝ) ^ n * ∑ k ∈ Finset.range n, Work.Spaces.HkIntegrand α 5 (F k) z θ
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => Work.Spaces.HkIntegrand_nonneg α 5 (F k) z θ)
  -- ### membership
  have hmem : Work.Spaces.HkMem α 5 g := by
    refine Work.FTS.LocData.HkMem_of_majorant (f := g) (M := M) α 5 hcont ?_ ?_ ?_
    · intro z hz
      show IntegrableOn (fun θ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
        Work.Spaces.HkIntegrand α 5 (F k) z θ) Work.Spaces.Iθ
      have hsum : Integrable (fun θ : ℝ => ∑ k ∈ Finset.range n,
          Work.Spaces.HkIntegrand α 5 (F k) z θ) (volume.restrict Work.Spaces.Iθ) :=
        integrable_finsetSum (Finset.range n) (fun k hk => (hm k hk).1 z hz)
      exact hsum.const_mul _
    · show IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
        Work.Spaces.HkIntegrand α 5 (F k) z θ) Work.Spaces.Iz
      have hsum : Integrable (fun z : ℝ => ∑ k ∈ Finset.range n,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 (F k) z θ)
          (volume.restrict Work.Spaces.Iz) :=
        integrable_finsetSum (Finset.range n) (fun k hk => (hm k hk).2)
      have hbase : Integrable (fun z : ℝ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 (F k) z θ)
          (volume.restrict Work.Spaces.Iz) := hsum.const_mul _
      refine hbase.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
      intro k hk
      exact (hm k hk).1 z hz
    · intro z hz θ hθ
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
      · subst hz0
        rw [Work.FTS.LocData.HkIntegrand_zero_fst]
        exact hMnn 0 θ
      · by_cases hs : Real.sin (2 * θ) = 0
        · rw [Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α 5 g hα hs]
          exact hMnn z θ
        · have hθpos : 0 < θ := by
            rcases lt_or_eq_of_le (show (0 : ℝ) ≤ θ from hθ.1) with h | h
            · exact h
            · exact absurd (by rw [← h, mul_zero, Real.sin_zero]) hs
          have hθlt : θ < Real.pi / 2 := by
            rcases lt_or_eq_of_le hθ.2 with h | h
            · exact h
            · exact absurd (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hs
          have hgeq : Work.Spaces.HkIntegrand α 5 g z θ
              = Work.Spaces.HkIntegrand α 5
                  (fun z θ => ∑ k ∈ Finset.range n, F k z θ) z θ :=
            Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := 5)
              (fun z θ hz hθ hlt => hag z θ hz hθ hlt) z θ hzpos hθpos hθlt
          rw [hgeq]
          have hle := Work.FTS.GalFields.RHS.HkIntegrand_finset_sum_le α 5 hα
            (Finset.range n) hsm z hz θ hθ
          simp only [Finset.card_range] at hle
          exact hle
  refine ⟨hmem, ?_⟩
  -- ### the norm bound
  have hXn : Work.Spaces.HkNorm α 5 g
      = Work.Spaces.HkNorm α 5 (fun z θ => ∑ k ∈ Finset.range n, F k z θ) := by
    show Work.Spaces.HkNorm α 5 g = _
    rw [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 5 hag,
      Work.Spaces.HkNorm]
  rw [hXn]
  simpa only [Finset.card_range] using
    Work.FTS.GalFields.RHS.HkNorm_finset_sum_le α 5 hα (Finset.range n) hsm hm

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.mixed_morrey_step =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem mixed_morrey_step {χ : ℝ × ℝ → ℝ} {F : ℝ → ℝ → ℝ} {α C C₀ M Km : ℝ}
    {a b c d a' b' c' d' : ℝ}
    (hmor : ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q| ≤ Km * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
        + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * dist p q ^ (1 / 2 : ℝ))
    (hKmnn : 0 ≤ Km) (hα : 0 < α) (hC₀nn : 0 ≤ C₀) (hCpos : 0 < C)
    (hχC2 : ContDiff ℝ 2 χ) (hχcs : HasCompactSupport χ) (hχnn : ∀ x, 0 ≤ χ x)
    (hχle1 : ∀ x, χ x ≤ 1)
    (hχone : ∀ z, z ∈ Set.Icc a b → ∀ θ, θ ∈ Set.Icc c d → χ (z, θ) = 1)
    (hχzero : ∀ x, x ∉ Set.Icc a' b' ×ˢ Set.Icc c' d' → χ x = 0)
    (hMfd1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ M) (hMfd2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M)
    (hsub : Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F) (hFmem : Work.Spaces.HkMem α 6 F)
    (hFbd : Work.Spaces.HkNorm α 6 F ≤ C₀)
    (hrect : ∀ (j i : ℕ), j + i ≤ 4 →
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.mixed j i F z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)) :
    ∀ (j i : ℕ), j + i ≤ 4 → ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c d,
        |Work.Spaces.mixed j i F p.1 p.2 - Work.Spaces.mixed j i F q.1 q.2|
          ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)) * dist p q ^ (1 / 2 : ℝ) := by
  intro j i hji p hp q hq
  have hisOpen : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  -- the uncurried slot and the rectangle
  set G : ℝ × ℝ → ℝ := Function.uncurry (Work.Spaces.mixed j i F) with hGdef
  set s : Set (ℝ × ℝ) := Set.Icc a' b' ×ˢ Set.Icc c' d' with hsdef
  have hsc : IsClosed s := isClosed_Icc.prod isClosed_Icc
  have hscm : MeasurableSet s := hsc.measurableSet
  have hkomp : IsCompact s := isCompact_Icc.prod isCompact_Icc
  -- `G` is `C²` on the open quadrant
  have hG2 : ContDiffOn ℝ 2 G Work.FTS.EllipticEst.Q0 := by
    have h := (hFsm.mixed j i).of_le two_le_smoothOrder
    simpa only [hGdef] using h
  have hG1 : ContDiffOn ℝ 1 G Work.FTS.EllipticEst.Q0 := hG2.of_le (by norm_num)
  have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ G) Work.FTS.EllipticEst.Q0 :=
    hG2.fderiv_of_isOpen hisOpen (by norm_num)
  -- integrability on the rectangle, from continuity
  have hI0 : IntegrableOn (fun x : ℝ × ℝ => (G x) ^ 2) s :=
    ((hG2.continuousOn.mono hsub).pow 2).integrableOn_compact hkomp
  have hI1 : IntegrableOn (fun x : ℝ × ℝ => ‖fderiv ℝ G x‖ ^ 2) s := by
    have hcont := (hfd1.continuousOn.mono hsub).norm.pow 2
    exact hcont.integrableOn_compact hkomp
  -- the four basis entries of `D²G`, as functions of the point, and their sum `E`
  set A : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pzIter 2 (Work.Spaces.mixed j i F) x.1 x.2 with hAdef
  set B : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) x.1 x.2 with hBdef
  set Cc : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) x.1 x.2 with hCcdef
  set D : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pthIter 2 (Work.Spaces.mixed j i F) x.1 x.2 with hDdef
  set E : ℝ × ℝ → ℝ := fun x => ‖A x‖ + ‖B x‖ + ‖Cc x‖ + ‖D x‖ with hEdef
  have hI2 : IntegrableOn (fun x : ℝ × ℝ => E x ^ 2) s := by
    have hAc := (((hFsm.mixed j i).pz).pz).continuousOn
    have hBc := (((hFsm.mixed j i).pth).pz).continuousOn
    have hCc' := (((hFsm.mixed j i).pz).pth).continuousOn
    have hDc := (((hFsm.mixed j i).pth).pth).continuousOn
    have hE := ((((hAc.norm.add hBc.norm).add hCc'.norm).add hDc.norm)).mono hsub
    exact (hE.pow 2).integrableOn_compact hkomp
  have hIA : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pz).pz).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hIB : IntegrableOn (fun x : ℝ × ℝ => (B x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pth).pz).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hIC : IntegrableOn (fun x : ℝ × ℝ => (Cc x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pz).pth).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hID : IntegrableOn (fun x : ℝ × ℝ => (D x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pth).pth).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  -- `E` dominates the operator norm of the second derivative
  have hEbd : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ E x := by
    intro x hx
    have hxQ : x ∈ Work.FTS.EllipticEst.Q0 := hsub hx
    have h := norm_fderiv_fderiv_le_basis (G := Work.Spaces.mixed j i F) hisOpen hG2 hxQ
    simpa only [hEdef, hAdef, hBdef, hCcdef, hDdef, Real.norm_eq_abs,
      Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h
  -- the rectangle bounds of the hypothesis
  obtain ⟨hmix, hpz1, hpth1, hpz2, hpzpth, hpthpz, hpth2⟩ := hrect j i hji
  -- the `L²`-bound of the slot itself on the rectangle
  have hAg : ∫ x in s, (G x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have hr : ∫ x in s, (G x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.mixed j i F z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := G)
        (a := a') (b := b') (c := c') (d := d') hI0
      simpa only [hGdef, Function.uncurry] using h
    rw [hr]; exact hmix
  -- the `L²`-bound of the four second basis entries
  have hA2 : ∫ x in s, (A x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have heq : ∫ x in s, (A x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pzIter 2 (Work.Spaces.mixed j i F) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := A)
        (a := a') (b := b') (c := c') (d := d') hIA
      simpa only [hAdef] using h
    rw [heq]
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hpz2
  have hB2 : ∫ x in s, (B x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have heq : ∫ x in s, (B x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := B)
        (a := a') (b := b') (c := c') (d := d') hIB
      simpa only [hBdef] using h
    rw [heq]; exact hpzpth
  have hC2 : ∫ x in s, (Cc x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have heq : ∫ x in s, (Cc x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := Cc)
        (a := a') (b := b') (c := c') (d := d') hIC
      simpa only [hCcdef] using h
    rw [heq]; exact hpthpz
  have hD2 : ∫ x in s, (D x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have heq : ∫ x in s, (D x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pthIter 2 (Work.Spaces.mixed j i F) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := D)
        (a := a') (b := b') (c := c') (d := d') hID
      simpa only [hDdef] using h
    rw [heq]
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hpth2
  -- hence `∫_s E² ≤ 16 C |F|²`
  have hE2 : ∫ x in s, E x ^ 2 ≤ 16 * C * Work.Spaces.HkSq α 6 F := by
    have hpt : ∀ x ∈ s, E x ^ 2
        ≤ 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := by
      intro x hx
      have h := Work.FTS.StrongLWP.Sobolev.eqc_sq_add4_le ‖A x‖ ‖B x‖ ‖Cc x‖ ‖D x‖
      simpa only [hEdef, Real.norm_eq_abs, sq_abs] using h
    have h12 : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2 + (B x) ^ 2) s := hIA.add hIB
    have h123 : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2) s :=
      h12.add hIC
    have h1234 : IntegrableOn (fun x : ℝ × ℝ =>
        (A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) s := h123.add hID
    have hInt : IntegrableOn (fun x : ℝ × ℝ =>
        4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)) s := h1234.const_mul 4
    have hmono : ∫ x in s, E x ^ 2
        ≤ ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hInt
        (ae_restrict_of_forall_mem hscm hpt)
    have sA : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2) = (∫ x in s, (A x) ^ 2) + ∫ x in s, (B x) ^ 2 :=
      integral_add hIA hIB
    have sB : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2)
        = (∫ x in s, ((A x) ^ 2 + (B x) ^ 2)) + ∫ x in s, (Cc x) ^ 2 :=
      integral_add h12 hIC
    have sC : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        = (∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2)) + ∫ x in s, (D x) ^ 2 :=
      integral_add h123 hID
    have sD : ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        = 4 * ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) :=
      integral_const_mul 4 _
    have hsum4 : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        ≤ (((C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F)
            + C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F := by
      rw [sC, sB, sA]
      linarith [hA2, hB2, hC2, hD2]
    calc ∫ x in s, E x ^ 2
        ≤ ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := hmono
      _ = 4 * ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := sD
      _ ≤ 4 * ((((C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F)
            + C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F) :=
          mul_le_mul_of_nonneg_left hsum4 (by norm_num)
      _ = 16 * C * Work.Spaces.HkSq α 6 F := by ring
  -- the `L²`-bound of the first derivative
  have hD1 : ∫ x in s, ‖fderiv ℝ G x‖ ^ 2 ≤ 4 * C * Work.Spaces.HkSq α 6 F := by
    have hpt : ∀ x ∈ s, ‖fderiv ℝ G x‖ ^ 2
        ≤ 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := by
      intro x hx
      have hxQ : x ∈ Work.FTS.EllipticEst.Q0 := hsub hx
      have hdiff : DifferentiableAt ℝ G x :=
        (hG2.contDiffAt (hisOpen.mem_nhds hxQ)).differentiableAt (by norm_num)
      have e1 : (fderiv ℝ G x) (1, 0)
          = Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2 :=
        (Work.Spaces.pz_eq_fderiv (G := Work.Spaces.mixed j i F) hdiff).symm
      have e2 : (fderiv ℝ G x) (0, 1)
          = Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2 :=
        (Work.Spaces.pth_eq_fderiv (G := Work.Spaces.mixed j i F) hdiff).symm
      have hop := Work.FTS.StrongLWP.Sobolev.eqc_opNorm_le_basis_sum (fderiv ℝ G x)
      rw [e1, e2, Real.norm_eq_abs, Real.norm_eq_abs] at hop
      have h1 : ‖fderiv ℝ G x‖ ^ 2
          ≤ (|Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2|
              + |Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hop 2
      have h2 := Work.FTS.StrongLWP.Sobolev.eqc_sq_add2_le
        |Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2|
        |Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2|
      rw [sq_abs, sq_abs] at h2
      exact h1.trans h2
    have hIpz : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := by
      have hcont := ((hFsm.mixed j i).pz).continuousOn.mono hsub
      exact (hcont.pow 2).integrableOn_compact hkomp
    have hIpth : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := by
      have hcont := ((hFsm.mixed j i).pth).continuousOn.mono hsub
      exact (hcont.pow 2).integrableOn_compact hkomp
    have hInt : IntegrableOn (fun x : ℝ × ℝ =>
        2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)) s :=
      (hIpz.add hIpth).const_mul 2
    have hzp : ∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F := by
      have heq : ∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
              (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 :=
        Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq
          (f := Function.uncurry (Work.Spaces.pz (Work.Spaces.mixed j i F)))
          (a := a') (b := b') (c := c') (d := d') hIpz
      rw [heq]; exact hpz1
    have hthp : ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F := by
      have heq : ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
              (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 :=
        Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq
          (f := Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed j i F)))
          (a := a') (b := b') (c := c') (d := d') hIpth
      rw [heq]; exact hpth1
    have hIpzth : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := hIpz.add hIpth
    have sA : ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
        = (∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
          + ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2 :=
      integral_add hIpz hIpth
    have sB : ∫ x in s, 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
        = 2 * ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) :=
      integral_const_mul 2 _
    calc ∫ x in s, ‖fderiv ℝ G x‖ ^ 2
        ≤ ∫ x in s, 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hInt
            (ae_restrict_of_forall_mem hscm hpt)
      _ = 2 * ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := sB
      _ = 2 * ((∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
            + ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := by rw [sA]
      _ ≤ 2 * ((C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F) := by
          linarith [hzp, hthp]
      _ = 4 * C * Work.Spaces.HkSq α 6 F := by ring
  -- the cutoff product
  have hv2 : ContDiff ℝ 2 (fun x : ℝ × ℝ => χ x * G x) :=
    contDiff_two_mul_of_contDiffOn_two hsc hsub hisOpen hχC2 hχzero hG2
  have hvcs : HasCompactSupport (fun x : ℝ × ℝ => χ x * G x) :=
    Work.FTS.StrongLWP.Sobolev.eqc_hasCompactSupport_mul (χ := χ) (g := G) hχcs
  -- Morrey's inequality for `χ · G`
  have hm := hmor (fun x : ℝ × ℝ => χ x * G x) hv2 hvcs p q
  -- the two `L²`-norms appearing in Morrey's inequality
  have hA : ∫ x : ℝ × ℝ, (χ x * G x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F :=
    (Work.FTS.StrongLWP.Sobolev.eqc_integral_mul_sq_le hχzero hχle1 hχnn hscm hI0).trans hAg
  have hB : ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2
      ≤ 3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α 6 F := by
    have hM0 : ∀ x : ℝ × ℝ, ‖χ x‖ ≤ 1 := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχnn x)]; exact hχle1 x
    have hgd : ∀ y ∈ Work.FTS.EllipticEst.Q0, DifferentiableAt ℝ G y := fun y hy =>
      (hG2.contDiffAt (hisOpen.mem_nhds hy)).differentiableAt (by norm_num)
    have hgd2 : ∀ y ∈ Work.FTS.EllipticEst.Q0, DifferentiableAt ℝ (fderiv ℝ G) y := fun y hy =>
      (hfd1.contDiffAt (hisOpen.mem_nhds hy)).differentiableAt (by norm_num)
    have hbd := Work.FTS.StrongLWP.Sobolev.eqc_integral_fderiv_fderiv_mul_sq_le
      (χ := χ) (g := G) (s := s) (U := Work.FTS.EllipticEst.Q0)
      (M0 := 1) (M1 := M) (M2 := M) (E := E)
      hχC2 hsc hχzero hM0 hMfd1 hMfd2 hisOpen hsub hgd hgd2 hEbd hI0 hI1 hI2
    have hstep : 3 * (1 ^ 2 * (∫ x in s, E x ^ 2)
          + (2 * M) ^ 2 * (∫ x in s, ‖fderiv ℝ G x‖ ^ 2)
          + M ^ 2 * (∫ x in s, (G x) ^ 2))
        ≤ 3 * (1 ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F)
          + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F)
          + M ^ 2 * (C * Work.Spaces.HkSq α 6 F)) := by
      have a1 := mul_le_mul_of_nonneg_left hE2 (by norm_num : (0 : ℝ) ≤ 1 ^ 2)
      have a2 := mul_le_mul_of_nonneg_left hD1 (sq_nonneg (2 * M))
      have a3 := mul_le_mul_of_nonneg_left hAg (sq_nonneg M)
      linarith
    calc ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2
        ≤ 3 * (1 ^ 2 * (∫ x in s, E x ^ 2)
            + (2 * M) ^ 2 * (∫ x in s, ‖fderiv ℝ G x‖ ^ 2)
            + M ^ 2 * (∫ x in s, (G x) ^ 2)) := hbd
      _ ≤ 3 * (1 ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F)
            + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F)
            + M ^ 2 * (C * Work.Spaces.HkSq α 6 F)) := hstep
      _ = 3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α 6 F := by ring
  -- the square-root comparison
  have hCnn : 0 ≤ C := le_of_lt hCpos
  have hQnn : 0 ≤ 3 * C * (16 + 17 * M ^ 2) := by positivity
  have hsum : Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
        + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
      ≤ 2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
    have hs1 : Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
        ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
      calc Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
          ≤ Real.sqrt (C * Work.Spaces.HkSq α 6 F) := Real.sqrt_le_sqrt hA
        _ = Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α 6 F) := Real.sqrt_mul hCnn _
        _ ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ :=
            mul_le_mul (Real.sqrt_le_sqrt (by linarith [hQnn])) hFbd
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hs2 : Real.sqrt (∫ x : ℝ × ℝ,
          ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
        ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
      calc Real.sqrt (∫ x : ℝ × ℝ,
            ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
          ≤ Real.sqrt (3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α 6 F) :=
            Real.sqrt_le_sqrt hB
        _ = Real.sqrt (3 * C * (16 + 17 * M ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 6 F) :=
            Real.sqrt_mul hQnn _
        _ ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ :=
            mul_le_mul (Real.sqrt_le_sqrt (by linarith [hCnn])) hFbd
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  -- the values at `p` and `q` inside the inner rectangle
  have hGp : G p = Work.Spaces.mixed j i F p.1 p.2 := rfl
  have hGq : G q = Work.Spaces.mixed j i F q.1 q.2 := rfl
  have hχp : χ p = 1 := hχone p.1 hp.1 p.2 hp.2
  have hχq : χ q = 1 := hχone q.1 hq.1 q.2 hq.2
  have hvp : (fun x : ℝ × ℝ => χ x * G x) p = Work.Spaces.mixed j i F p.1 p.2 := by
    simp only [hχp, hGp, one_mul]
  have hvq : (fun x : ℝ × ℝ => χ x * G x) q = Work.Spaces.mixed j i F q.1 q.2 := by
    simp only [hχq, hGq, one_mul]
  -- assemble
  have hd0 : 0 ≤ dist p q ^ (1 / 2 : ℝ) := Real.rpow_nonneg dist_nonneg _
  have hfin : |(fun x : ℝ × ℝ => χ x * G x) p - (fun x : ℝ × ℝ => χ x * G x) q|
      ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)) * dist p q ^ (1 / 2 : ℝ) := by
    calc |(fun x : ℝ × ℝ => χ x * G x) p - (fun x : ℝ × ℝ => χ x * G x) q|
        ≤ Km * (Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ,
                ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2))
          * dist p q ^ (1 / 2 : ℝ) := hm
      _ ≤ Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)
            * dist p q ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hKmnn) hd0
  rw [hvp, hvq] at hfin
  exact hfin

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-! ## The vanishing of `D_z^j` on the zero function -/

/-- `D_z^j` of the identically zero function vanishes. -/
theorem DzIter_zero_fun (j : ℕ) :
    Work.Spaces.DzIter j (fun _ (_ : ℝ) => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const]
      ring

-- Import `Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux` (which defines
-- `KsFun α = fun z _ => α * (2 * z / (1 + z) ^ 2)` and
-- `KsTor α = fun z θ => Real.sin θ ^ 2 * KsFun α z θ`, and proves
-- `ks_Dz_bound : |D_z^j (KsFun α) z| ≤ 2*5040*203*α*(z/(1+z))` for `j ≤ 6`, `z ≥ 0`;
-- `DzIter_const_mul_apply`, `pzIter_DthIter_KsTor`, `DthIter_KsFun_eq_zero`,
-- `dthU_sinSq_weighted : |D_θ^i(sin²) θ| ≤ C*(α + sin 2θ)*sin(2θ)^{α/5}` for `1 ≤ i ≤ 6`,
-- `θ ∈ (0,π/2)`), plus `Submission.Work.Spaces.Defs`.
-- Route: `mixed j i A = DzIter j (DthIter i A)`; for `A = KsFun` use `DthIter_KsFun_eq_zero`
-- (`i ≥ 1`, both sides 0) and `ks_Dz_bound` (`i = 0`); for `A = KsTor` use
-- `DthIter_KsTor`/`DzIter_const_mul_apply` to factor the LHS as
-- `|D_θ^i(sin²) θ| * |D_z^j (KsFun α) z|` (`sin²θ ≤ 1` for `i = 0`) and multiply the two
-- bounds.  `θ ∈ Iθ` (needed by `ks_Dz_bound`) follows from `0 < θ < π/2`.
theorem ksMixed : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ A : ℝ → ℝ → ℝ,
    (A = (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) ∨
     A = (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2)))) →
    ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ C * α * (z / (1 + z)) *
        (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
  obtain ⟨C1, hC1pos, hC1⟩ := dthU_sinSq_weighted
  refine ⟨2 * 5040 * 203 * max C1 1, ?_, ?_⟩
  · have h : (1 : ℝ) ≤ max C1 1 := le_max_right _ _
    nlinarith
  · intro α hαI A hA j i hji z θ hz hθ0 hθ2
    obtain ⟨hαpos, hα1⟩ := hαI
    have hαnn : (0 : ℝ) ≤ α := le_of_lt hαpos
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have hzr : (0 : ℝ) ≤ z / (1 + z) := div_nonneg hz0 (le_of_lt hz1)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hsin0 : (0 : ℝ) ≤ Real.sin (2 * θ) := le_of_lt hsin
    have hX0 : (0 : ℝ) ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
    have hbr : 0 ≤ 2 * 5040 * 203 * α * (z / (1 + z)) :=
      mul_nonneg (mul_nonneg (by norm_num) hαnn) hzr
    -- the two functions named in the statement are `KsFun α` / `KsTor α`
    have hfun1 : (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) = KsFun α := rfl
    have hfun2 : (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2)))
        = KsTor α := rfl
    rcases hA with hA | hA
    · -- ## the radial function `KsFun α`
      have hAK : A = KsFun α := by rw [hA]; exact hfun1
      subst hAK
      by_cases hi : 1 ≤ i
      · -- `i ≥ 1`: `D_θ^i (KsFun α) = 0`
        have hi6 : i ≤ 6 := by omega
        have hzero : Work.Spaces.DthIter i (KsFun α) = fun _ _ => (0 : ℝ) :=
          DthIter_KsFun_eq_zero α hi
        have hm : Work.Spaces.mixed j i (KsFun α) z θ = 0 := by
          rw [Work.Spaces.mixed, hzero, DzIter_zero_fun j]
        rw [hm, abs_zero, ite_eq_left hi]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hαnn) hzr) hX0
      · -- `i = 0`
        have hi0 : i = 0 := by omega
        subst hi0
        have hb := ks_Dz_bound α hαnn j (by omega) z hz0 θ hθI
        have hb' : |Work.Spaces.mixed j 0 (KsFun α) z θ|
            ≤ 2 * 5040 * 203 * α * (z / (1 + z)) := by
          simpa only [Work.Spaces.mixed_zero_right] using hb
        rw [ite_eq_right (by norm_num : ¬ (1 ≤ 0)), mul_one]
        refine le_trans hb' ?_
        calc (2 * 5040 * 203 : ℝ) * α * (z / (1 + z))
            = (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) * 1 := by ring
          _ ≤ (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) * (max C1 1) :=
              mul_le_mul_of_nonneg_left (le_max_right C1 1) hbr
          _ = 2 * 5040 * 203 * max C1 1 * α * (z / (1 + z)) := by ring
    · -- ## the angular function `KsTor α`
      have hAK : A = KsTor α := by rw [hA]; exact hfun2
      subst hAK
      have hi6 : i ≤ 6 := by omega
      -- factor the mixed derivative
      have hfac : Work.Spaces.mixed j i (KsTor α) z θ
          = Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ
            * Work.Spaces.DzIter j (KsFun α) z θ := by
        rw [Work.Spaces.mixed]
        rw [show Work.Spaces.DthIter i (KsTor α)
              = fun z θ => Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ
                  * KsFun α z θ
            from funext fun z => funext fun θ => DthIter_KsTor α i z θ]
        rw [DzIter_const_mul_apply]
      rw [hfac, abs_mul]
      have hb := ks_Dz_bound α hαnn j (by omega) z hz0 θ hθI
      by_cases hi : 1 ≤ i
      · -- `i ≥ 1`: multiply the two bounds
        rw [ite_eq_left hi]
        have hd := hC1 α ⟨hαpos, hα1⟩ i hi hi6 θ ⟨hθ0, hθ2⟩
        have hXnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := hX0
        refine le_trans (mul_le_mul hd hb (abs_nonneg _)
          (mul_nonneg (le_of_lt hC1pos) hXnn)) ?_
        calc C1 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * (2 * 5040 * 203 * α * (z / (1 + z)))
            = C1 * ((2 * 5040 * 203) * α * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by ring
          _ ≤ max C1 1 * ((2 * 5040 * 203) * α * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
              mul_le_mul_of_nonneg_right (le_max_left C1 1)
                (mul_nonneg hbr hXnn)
          _ = 2 * 5040 * 203 * max C1 1 * α * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      · -- `i = 0`: `|sin²θ| ≤ 1`
        have hi0 : i = 0 := by omega
        subst hi0
        rw [ite_eq_right (by norm_num : ¬ (1 ≤ 0)), mul_one]
        simp only [Function.iterate_zero, id_eq]
        have hs2 : |Real.sin θ ^ 2| ≤ 1 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact Real.sin_sq_le_one θ
        refine le_trans (mul_le_mul hs2 hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)) ?_
        calc (1 : ℝ) * (2 * 5040 * 203 * α * (z / (1 + z)))
            = (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) := by ring
          _ ≤ 2 * 5040 * 203 * max C1 1 * α * (z / (1 + z)) := by
              calc (2 * 5040 * 203 : ℝ) * α * (z / (1 + z))
                  = (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) * 1 := by ring
                _ ≤ (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) * (max C1 1) :=
                    mul_le_mul_of_nonneg_left (le_max_right C1 1) hbr
                _ = 2 * 5040 * 203 * max C1 1 * α * (z / (1 + z)) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksTorWlInf =====
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

/-! ## Slot bounds for `KsTor α`

`KsTor α = fun z θ => sin²θ · Ks(z)` is a product of a function of `θ` alone and a
function of `z` alone, so every mixed derivative factors (`pzIter_KsTor`,
`pzIter_DthIter_KsTor` in `KsAux`):

* `∂_z^k KsTor α = sin²θ · ∂_z^k Ks`,
* `∂_z^k D_θ^j KsTor α = D_θ^j(sin²)(θ) · ∂_z^k Ks`.

Hence each `𝒲^{6,∞}`-slot is the product of a `θ`-factor and a `z`-factor.  The `z`-factor
is bounded by `2α·k!·(k+1) ≤ 2α·5040` (`ks_pz_bound` + `fact_mul_le_5040`), the `θ`-factor of
a radial slot by `1`, and the weighted `θ`-factor of an angular slot by the constant of
`dthU_sinSq_weight`. -/

/-- `sin θ ^ 2 ≤ 1`. -/
private theorem sin_sq_le_one (θ : ℝ) : Real.sin θ ^ 2 ≤ 1 := by
  nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ]

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

/-- The `z`-factor of a slot: `|(z+1)^k ∂_z^k Ks| ≤ 2α·k!·(k+1) ≤ 2α·5040` for `k ≤ 6`. -/
private theorem ks_zfactor_le {α : ℝ} (hα : 0 ≤ α) (k : ℕ) (hk : k ≤ 6) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (θ : ℝ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ| ≤ 2 * α * 5040 := by
  have h1 := ks_pz_bound α hα k z hz θ
  have h2 := fact_mul_le_5040 k hk
  calc |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ|
      ≤ 2 * α * ((k.factorial : ℝ) * (k + 1)) := h1
    _ ≤ 2 * α * 5040 := mul_le_mul_of_nonneg_left h2 (by linarith)

/-- **The radial slots.**  For `k ≤ 6` and `(z,θ)` in the closed quadrant,
`|(z+1)^k ∂_z^k KsTor α| ≤ 2α·5040`. -/
private theorem radial_slot_le {α : ℝ} (hα : 0 ≤ α) (k : ℕ) (hk : k ≤ 6) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (_hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (KsTor α) z θ| ≤ 2 * α * 5040 := by
  rw [pzIter_KsTor]
  have hsin : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hsin1 : Real.sin θ ^ 2 ≤ 1 := sin_sq_le_one θ
  have hres := ks_zfactor_le hα k hk hz θ
  calc |(z + 1) ^ k * (Real.sin θ ^ 2 * Work.Spaces.pzIter k (KsFun α) z θ)|
      = Real.sin θ ^ 2 * |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ| := by
        rw [show (z + 1) ^ k * (Real.sin θ ^ 2 * Work.Spaces.pzIter k (KsFun α) z θ)
              = Real.sin θ ^ 2 * ((z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ)
            from by ring,
          abs_mul, abs_of_nonneg hsin]
    _ ≤ 1 * (2 * α * 5040) := mul_le_mul hsin1 hres (abs_nonneg _) (by norm_num)
    _ = 2 * α * 5040 := by ring

/-- **The angular slots.**  The `θ`-factor carries the weighted endpoint bound (`hCw`,
the content of `dthU_sinSq_weight`), the `z`-factor the radial bound. -/
private theorem ang_slot_le {α Cw : ℝ} (hα : 0 < α) (_hα1 : α ≤ 1) (hCwpos : 0 < Cw)
    (hCw : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ Cw)
    (j k : ℕ) (hj1 : 1 ≤ j) (hjk : k + j ≤ 6) {z : ℝ} (hz : z ∈ Work.Spaces.Iz)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      ≤ Cw * (2 * α * 5040) := by
  rw [pzIter_DthIter_KsTor]
  have hj6 : j ≤ 6 := by omega
  have hk6 : k ≤ 6 := by omega
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg hs0 _) hden.le
  have hD := hCw j hj1 hj6 θ hθ
  have hD' : |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ Cw := by
    simpa only [div_eq_mul_inv, mul_assoc] using hD
  have hZ := ks_zfactor_le hα.le k hk6 hz θ
  calc |(z + 1) ^ k * (Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ
          * Work.Spaces.pzIter k (KsFun α) z θ)
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      = (|Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        * |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ| := by
        rw [show (z + 1) ^ k * (Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ
              * Work.Spaces.pzIter k (KsFun α) z θ)
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
            = (Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
              * ((z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ) from by ring,
          abs_mul, abs_mul, abs_of_nonneg hw0]
    _ ≤ Cw * (2 * α * 5040) := mul_le_mul hD' hZ (abs_nonneg _) hCwpos.le

/-! ## The main statement -/

-- Import `Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux` (which defines
-- `KsTor α = fun z θ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2))` — definitionally the
-- function below — and proves the helpers `KsTor_eq_FK`, `pzIter_KsTor`,
-- `pzIter_DthIter_KsTor`, `ks_pz_bound`, `pzIter_KsFun`), plus
-- `Submission.Work.Spaces.Defs` and the weighted endpoint bound
-- `Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight`:
-- `|D_θ^j (sin²) θ| · sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 1095801216` for `1 ≤ j ≤ 6`, `0 < α ≤ 1`,
-- `θ ∈ Iθ`.  Route: `pzIter_KsTor` + `ks_pz_bound` bound the radial slots by `2α·k!(k+1)`;
-- for the angular slots `pzIter_DthIter_KsTor` factors the slot as
-- `D_θ^j(sin²)(θ) · ∂_z^k Ks(z) · sin(2θ)^{-α/5}/(α+sin 2θ)`, and `dthU_sinSq_weight` bounds
-- the θ-part by `1095801216` while `ks_pz_bound` bounds the z-part by `2α·k!(k+1) ≤ 10080α`.
theorem ksTorWlInf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.WlInfMem α 6 (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2))) ∧
    Work.Spaces.WlInf α 6 (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2)))
      ≤ C * α := by
  obtain ⟨Cw, hCwpos, hCw⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight
  refine ⟨max 1 (70560 + 49 * Cw * 10080), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro α hαI
  obtain ⟨hα, hα1⟩ := hαI
  have hα0 : 0 ≤ α := le_of_lt hα
  change Work.Spaces.WlInfMem α 6 (KsTor α) ∧
      Work.Spaces.WlInf α 6 (KsTor α) ≤ max 1 (70560 + 49 * Cw * 10080) * α
  have hCwα : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ Cw := hCw α hα hα1
  have hmem : Work.Spaces.WlInfMem α 6 (KsTor α) := by
    refine ⟨fun k hk => ?_, fun j _ k _ hj1 hjk => ?_⟩
    · exact Work.Spaces.supFinite_of_pointwise
        (fun z hz θ hθ => radial_slot_le hα0 k hk hz hθ)
    · exact Work.Spaces.supFinite_of_pointwise
        (fun z hz θ hθ => ang_slot_le hα hα1 hCwpos hCwα j k hj1 hjk hz hθ)
  have hbound : Work.Spaces.WlInf α 6 (KsTor α)
      ≤ max 1 (70560 + 49 * Cw * 10080) * α := by
    rw [Work.Spaces.WlInf]
    have hZterm : ∀ k ∈ Finset.range (6 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsTor α) z θ)
          ≤ 2 * α * 5040 := by
      intro k hk
      have hk6 : k ≤ 6 := by have := Finset.mem_range.mp hk; omega
      exact Work.Spaces.supAbs_le (fun z hz θ hθ => radial_slot_le hα0 k hk6 hz hθ)
    have hZ : (∑ k ∈ Finset.range (6 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsTor α) z θ))
        ≤ 7 * (2 * α * 5040) := by
      calc (∑ k ∈ Finset.range (6 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsTor α) z θ))
          ≤ ∑ _k ∈ Finset.range (6 + 1), (2 * α * 5040) := Finset.sum_le_sum hZterm
        _ = 7 * (2 * α * 5040) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    have hTterm : ∀ j k : ℕ,
        (if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ Cw * (2 * α * 5040) := by
      intro j k
      by_cases hc : 1 ≤ j ∧ k + j ≤ 6
      · rw [ite_eq_left hc]
        exact Work.Spaces.supAbs_le
          (fun z hz θ hθ => ang_slot_le hα hα1 hCwpos hCwα j k hc.1 hc.2 hz hθ)
      · rw [ite_eq_right hc]
        have hnn : 0 ≤ Cw * (2 * α * 5040) := by positivity
        exact hnn
    have hT : (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
        if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ 49 * (Cw * (2 * α * 5040)) := by
      calc (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
            if 1 ≤ j ∧ k + j ≤ 6 then
              Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0)
          ≤ ∑ _j ∈ Finset.range (6 + 1), ∑ _k ∈ Finset.range (6 + 1),
              (Cw * (2 * α * 5040)) :=
            Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hTterm j k))
        _ = 49 * (Cw * (2 * α * 5040)) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
    have hfin : 7 * (2 * α * 5040) + 49 * (Cw * (2 * α * 5040))
        ≤ max 1 (70560 + 49 * Cw * 10080) * α := by
      have hEq : 7 * (2 * α * 5040) + 49 * (Cw * (2 * α * 5040))
          = (70560 + 49 * Cw * 10080) * α := by ring
      rw [hEq]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hα0
    linarith
  exact ⟨hmem, hbound⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksWlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option autoImplicit false

/-- Every `∂_z`-iterate of the identically zero function vanishes. -/
private lemma pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0:ℝ)) = fun _ _ => (0:ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]

-- Import `Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux` (which defines
-- `KsFun α = fun z _ => α * (2 * z / (1 + z) ^ 2)` — definitionally the function below — and
-- proves the helpers `KsFun_eq_FK`, `pzIter_KsFun`, `ks_pz_bound`,
-- `DthIter_KsFun_eq_zero`), plus `Submission.Work.Spaces.Defs` (`WlInf`, `WlInfMem`,
-- `supAbs_le`, `HkAux.supFinite_of_pointwise`).
-- Route: `pzIter_KsFun` + `ks_pz_bound` give `supAbs ((z+1)^k ∂_z^k Ks) ≤ 2α·k!(k+1)` for
-- `k ≤ 6` via `Work.Spaces.supAbs_le`, and `DthIter_KsFun_eq_zero` kills every `j ≥ 1`
-- angular slot (`supAbs` of the identically zero function is ≤ 0).  Summing,
-- `WlInf α 6 Ks ≤ 2α·Σ_{k≤6} k!(k+1) = 11826α`.
theorem ksWlInf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.WlInfMem α 6 (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) ∧
    Work.Spaces.WlInf α 6 (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) ≤ C * α := by
  refine ⟨11826, by norm_num, fun α hαI => ?_⟩
  obtain ⟨hαpos, hαle⟩ := hαI
  have hα0 : 0 ≤ α := le_of_lt hαpos
  have hKs : (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) = KsFun α := rfl
  refine ⟨?_, ?_⟩
  · rw [hKs]
    -- `WlInfMem α 6 (KsFun α)`: the radial slots are bounded by `ks_pz_bound`, the
    -- angular slots are identically zero.
    refine ⟨fun k hk => ?_, fun j hj k hk hj1 hkj => ?_⟩
    · refine ⟨2 * α * ((k.factorial : ℝ) * (k + 1)), fun y hy => ?_⟩
      obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
      exact ks_pz_bound α hα0 k z hz θ
    · refine ⟨0, fun y hy => ?_⟩
      obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
      have h1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsFun α)) = fun _ _ => (0:ℝ) := by
        rw [DthIter_KsFun_eq_zero α hj1, pzIter_zero_fun]
      rw [h1]
      simp
  · rw [hKs, Work.Spaces.WlInf]
    -- The angular sum vanishes identically: every surviving slot (`j ≥ 1`) is the
    -- supremum of the zero function.
    have hth : (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
        if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsFun α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ 0 := by
      refine Finset.sum_nonpos fun j hj => Finset.sum_nonpos fun k hk => ?_
      by_cases hc : 1 ≤ j ∧ k + j ≤ 6
      · rw [if_pos hc]
        refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
        have h1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsFun α)) = fun _ _ => (0:ℝ) := by
          rw [DthIter_KsFun_eq_zero α hc.1, pzIter_zero_fun]
        rw [h1]
        simp
      · rw [if_neg hc]
    -- The radial sum is bounded by `∑_{k ≤ 6} 2α·k!(k+1) = 11826α`.
    have hz_sum : (∑ k ∈ Finset.range (6 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ))
        ≤ 2 * α * 5913 :=
      calc (∑ k ∈ Finset.range (6 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ))
          ≤ ∑ k ∈ Finset.range (6 + 1), 2 * α * ((k.factorial : ℝ) * (k + 1)) :=
            Finset.sum_le_sum fun k hk => Work.Spaces.supAbs_le (fun z hz θ hθ =>
              ks_pz_bound α hα0 k z hz θ)
        _ = 2 * α * 5913 := by
            norm_num [Finset.sum_range_succ, Nat.factorial]
            ring
    calc (∑ k ∈ Finset.range (6 + 1),
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ))
        + (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
          if 1 ≤ j ∧ k + j ≤ 6 then
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsFun α)) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          else 0)
        ≤ 2 * α * 5913 + 0 := add_le_add hz_sum hth
      _ = 11826 * α := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IbpSliceBound` — the cutoff-free angular integration-by-parts bound

The angular integration by parts of `Work.H2.T1Q.IbpCutoff` is localised away from the two
ends `θ = 0`, `θ = π/2` of the quadrant by a cutoff `χ`; here we remove the cutoff, at the
price of weakening the *identity* to an *inequality*:

  `|∫_θ sin(2θ)^{-q}·F·(sin(2θ)·V')·V| ≤ (3/2)·Kf·∫_θ V²·sin(2θ)^{-q}`

with the exponent range `|1 - q| ≤ 1` (i.e. `q ∈ [0,2]`, the range of the slots `η`, `γ`).

The proof uses the cutoff family `χ ζ` of `Work.H2.T1Q.Cutoff` at the scale `ζ`: for every `ζ`
the localised bound `Work.H2.T1Q.slotBound_cutoff` gives

  `|∫_θ χ_ζ·F·D_θV·V·sin(2θ)^{-q}| ≤ (3/2)Kf·∫_θ V²sin(2θ)^{-q}
      + (Kf·B/2)·(∫_{(0,2ζ)}V²sin(2θ)^{-q} + ∫_{(π/2-2ζ,π/2)}V²sin(2θ)^{-q})`,

with a *uniform* constant `B` (the uniform weighted derivative bound `|sin(2θ)·χ_ζ'| ≤ B` of
`Cutoff`).  Along the sequence `ζ_n = 1/(2(n+4))` the error terms vanish by
`Work.H2.T1Q.ShrinkInt`, the cutoffs converge to `1` almost everywhere, and
`Work.H2.T1Q.SliceLimit` passes to the limit, provided `θ ↦ sin(2θ)^{-q}F(sin(2θ)V')V` is
integrable; when it is not, the integral is `0` by definition and the estimate is trivial.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.HardSlotAux

set_option maxHeartbeats 800000

theorem IbpSliceBound :
    ∃ B : ℝ, 0 < B ∧ ∀ (q Kf : ℝ) (F V : ℝ → ℝ),
      0 ≤ Kf → |1 - q| ≤ 1 →
      ContDiffOn ℝ 1 F (Set.Ioo 0 (π / 2)) →
      ContDiffOn ℝ 1 V (Set.Ioo 0 (π / 2)) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), |F θ| ≤ Kf) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv F θ| ≤ Kf) →
      MeasureTheory.IntegrableOn (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ →
      |∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-q) * F θ * (Real.sin (2 * θ) * deriv V θ) * V θ|
        ≤ (3 / 2 + B / 2) * Kf * ∫ θ in Work.Spaces.Iθ,
            (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
  obtain ⟨chi, B, hBpos, hchism, hchinn, hchile, hchione, hchiz0l, hchiz0r, hchid0l, hchid0r,
    hchibd, hchilim⟩ := Work.H2.T1Q.Cutoff
  refine ⟨B, hBpos, ?_⟩
  intro q Kf F V hKf0 hqabs hF1 hV1 hFb hFd hVint
  set g : ℝ → ℝ := fun θ =>
    (Real.sin (2 * θ)) ^ (-q) * F θ * (Real.sin (2 * θ) * deriv V θ) * V θ with hg
  set psi : ℝ → ℝ := fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) with hpsi
  -- nonnegativity of `psi`
  have hpsi_mem : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ psi θ := by
    intro θ hθ
    rw [hpsi]
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)
  have hpsi_nonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ, psi θ :=
    MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpsi_mem)
  have hpsi_int : MeasureTheory.IntegrableOn psi Work.Spaces.Iθ := by
    rw [hpsi]; exact hVint
  -- the pointwise bound on the `W`-factor of the localised integration by parts
  have hWb : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 / 2) * (Real.sin (2 * θ) * deriv F θ) + (1 - q) * Real.cos (2 * θ) * F θ|
        ≤ (3 / 2) * Kf :=
    fun θ hθ => Work.H2.T1Q.Wq_bound hKf0 (hFd θ hθ) (hFb θ hθ) hqabs
  -- the support-weighted derivative bound of the cutoff at scale `ζ`
  have hsd : ∀ ζ : ℝ, 0 < ζ → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Real.sin (2 * θ) * deriv (chi ζ) θ|
        ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
            + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) := by
    intro ζ hζ θ hθ
    have hindnn : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
        + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
      have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
        by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
      have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
      linarith
    -- the derivative vanishes on the middle interval, where the cutoff is `1`
    have hmid : ∀ θ' ∈ Set.Ioo ζ (π / 2 - ζ), deriv (chi ζ) θ' = 0 := by
      intro θ' hθ'
      have hev : chi ζ =ᶠ[𝓝 θ'] (fun _ => (1 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ'] with t ht
        exact hchione ζ t hζ (le_of_lt ht.1) (le_of_lt ht.2)
      exact Work.H2.T1Q.deriv_eq_zero_of_eventuallyEq_one hev
    by_cases h1 : θ < ζ / 2
    · rw [hchid0l ζ θ hζ h1, mul_zero, abs_zero]
      exact mul_nonneg hBpos.le hindnn
    by_cases h2 : π / 2 - ζ / 2 < θ
    · rw [hchid0r ζ θ hζ h2, mul_zero, abs_zero]
      exact mul_nonneg hBpos.le hindnn
    by_cases h3 : θ ≤ 2 * ζ
    · have hA : θ ∈ Set.Ioc 0 (2 * ζ) := ⟨by linarith [hθ.1], h3⟩
      have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        have ha : (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
          Set.indicator_of_mem hA _
        have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
          by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
          · simp [Set.indicator_of_mem hm]
          · simp [Set.indicator_of_notMem hm]
        rw [ha]; linarith
      calc |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B := hchibd ζ hζ θ
        _ = B * 1 := by ring
        _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
            mul_le_mul_of_nonneg_left hind hBpos.le
    · have h3' : 2 * ζ < θ := not_le.mp h3
      by_cases h4 : π / 2 - 2 * ζ < θ
      · have hB' : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2) :=
          ⟨h4, by linarith [not_lt.mp h2, Real.pi_pos]⟩
        have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
            + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
          have hb : (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
            Set.indicator_of_mem hB' _
          have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
            by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
            · simp [Set.indicator_of_mem hm]
            · simp [Set.indicator_of_notMem hm]
          rw [hb]; linarith
        calc |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B := hchibd ζ hζ θ
          _ = B * 1 := by ring
          _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
              mul_le_mul_of_nonneg_left hind hBpos.le
      · have hmidz : deriv (chi ζ) θ = 0 :=
          hmid θ ⟨by linarith, by linarith [not_lt.mp h4]⟩
        rw [hmidz, mul_zero, abs_zero]
        exact mul_nonneg hBpos.le hindnn
  -- the localised integration by parts, in `IbpG`/`IbpK` form
  have hibp : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 / 4 →
      MeasureTheory.IntegrableOn (Work.H2.T1Q.IbpG q (chi ζ) F V) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q (chi ζ) F V θ
        = -∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q (chi ζ) F V θ := by
    intro ζ hζ hζ4
    have hδ : 0 < ζ / 2 := by linarith
    have hδ4 : ζ / 2 ≤ π / 4 := by linarith [Real.pi_gt_three]
    exact IbpCutoffAnyQ (q := q) (χ := chi ζ) (hf := F) (hv := V) (hchism ζ) hδ hδ4
      (fun θ hθ => hchiz0l ζ θ hζ hθ) (fun θ hθ => hchiz0r ζ θ hζ hθ) hF1 hV1
  -- the cutoff scales tend to `0⁺`
  have hζseq : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 4))) Filter.atTop
      (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hshift : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 4)) Filter.atTop Filter.atTop := by
        have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 4)
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h2
      have hmul : Filter.Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 4)) Filter.atTop Filter.atTop :=
        hshift.const_mul_atTop (by norm_num)
      have hinv : Filter.Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 4))⁻¹) Filter.atTop (nhds 0) :=
        hmul.inv_tendsto_atTop
      simpa [one_div] using hinv
    · refine Filter.Eventually.of_forall (fun n => ?_)
      show (0 : ℝ) < 1 / (2 * ((n : ℝ) + 4))
      positivity
  -- the shrinking error term
  set err : ℕ → ℝ := fun n => (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)), psi θ)
      + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2), psi θ) with herrdef
  have herr : Filter.Tendsto err Filter.atTop (nhds 0) := by
    rw [herrdef]
    have h := (Work.H2.T1Q.ShrinkInt (h := psi) hpsi_int).const_mul (Kf * B / 2)
    simpa only [mul_zero] using h
  -- the localised bound at scale `ζ_n`
  have hbd : ∀ n : ℕ, |∫ θ in Work.Spaces.Iθ, chi (1 / (2 * ((n : ℝ) + 4))) θ * g θ|
      ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, psi θ) + err n := by
    intro n
    set ζ : ℝ := 1 / (2 * ((n : ℝ) + 4)) with hζdef
    have hn4 : (0 : ℝ) < (n : ℝ) + 4 := by
      have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hζ0 : 0 < ζ := by rw [hζdef]; positivity
    have hζ4 : ζ ≤ 1 / 4 := by
      rw [hζdef]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : (2 : ℝ) * 4 ≤ 2 * ((n : ℝ) + 4) := by linarith
      calc 1 / (2 * ((n : ℝ) + 4)) ≤ 1 / (2 * 4) := one_div_le_one_div_of_le (by norm_num) h1
        _ ≤ 1 / 4 := by norm_num
    have hζ2 : 2 * ζ ≤ π / 2 := by linarith [hζ4, Real.pi_gt_three]
    obtain ⟨hAint, hIBP⟩ := hibp ζ hζ0 hζ4
    have hb := Work.H2.T1Q.slotBound_cutoff (q := q) (Kf := Kf) (B := B) (ζ := ζ)
      (χ := chi ζ) (F := F) (V := V) hKf0 hBpos.le hζ0 hζ2 (fun θ => hchinn ζ θ)
      (fun θ => hchile ζ θ) (hsd ζ hζ0) hFb hWb hVint hAint hIBP
    have hLfun : (∫ θ in Work.Spaces.Iθ,
          chi ζ θ * (F θ * (Real.sin (2 * θ) * deriv V θ) * V θ * (Real.sin (2 * θ)) ^ (-q)))
        = ∫ θ in Work.Spaces.Iθ, chi ζ θ * g θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [hg]; ring
    rw [hLfun] at hb
    have h2ζ : 2 * ζ = 1 / ((n : ℝ) + 4) := by
      rw [hζdef]
      field_simp
    rw [h2ζ] at hb
    simpa only [herrdef, hζdef] using hb
  by_cases hLint : MeasureTheory.IntegrableOn g Work.Spaces.Iθ
  · -- the genuine case: pass to the limit in `ζ`
    have hlim : |∫ θ in Work.Spaces.Iθ, g θ| ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, psi θ) :=
      Work.H2.T1Q.SliceLimit (φ := g) (chi := fun n : ℕ => chi (1 / (2 * ((n : ℝ) + 4))))
        (M := (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, psi θ)) (err := err) herr hLint
        (fun n => ((hchism _).continuous).aestronglyMeasurable)
        (fun n θ => by rw [abs_of_nonneg (hchinn _ θ)]; exact hchile _ θ)
        (by
          filter_upwards [Work.H2.T1Q.ae_Iθ_mem_Ioo] with θ hθ
          exact (hchilim θ hθ.1 hθ.2).comp hζseq)
        hbd
    refine le_trans hlim ?_
    have h1 : 0 ≤ (B / 2) * Kf * (∫ θ in Work.Spaces.Iθ, psi θ) :=
      mul_nonneg (mul_nonneg (by linarith [hBpos]) hKf0) hpsi_nonneg
    nlinarith [h1]
  · -- the degenerate case: not integrable, so the integral is `0` by definition
    have hzero : (∫ θ in Work.Spaces.Iθ, g θ) = 0 := MeasureTheory.integral_undef hLint
    rw [hzero, abs_zero]
    exact mul_nonneg (mul_nonneg (by linarith [hBpos]) hKf0) hpsi_nonneg

end Work.FTS.StrongPersist.N6Trans.HardSlotAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Reduction of the slot exponent.**  On the open angular interval `(0,π/2)` the weight
`θ ↦ sin(2θ)^{-q}` is increasing in the exponent `q` (because `0 < sin(2θ) ≤ 1` there).  Hence
if the `p`-weighted square of a fixed function `V` — which is continuous on `(0,π/2)`, so that
every such slice is a.e. strongly measurable — is integrable, the same holds for the `q`-weighted
square for every `q ≤ p`. -/
theorem integrable_slot_rpow_le {V : ℝ → ℝ} {p q : ℝ} (hpq : q ≤ p)
    (hV : ContinuousOn V (Set.Ioo (0 : ℝ) (π / 2)))
    (hI : Integrable (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-p))
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))) :
    Integrable (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
  have hsin : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Work.Spaces.sin_two_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  refine Integrable.mono' hI ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable
      ((hV.pow 2).mul (Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_sin_two_rpow (-q)))
      measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) (-q)))]
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le hpq hθ) (sq_nonneg _)

/-- Angular integrability of a single `ℋ⁴`-slot, generalized from the proved
`Work.FTS.StrongPersist.N6Trans.HardSlotAux.SlotIntegrableHonest`
(`Submission/Work/FTS/StrongPersist/N6Trans/HardSlotAux/SlotIntegrableHonest.lean`), whose
statement is the special case `a + b = 4` with the extra hypothesis `a = 0 → q = eta`:

* the constraint on the *total* order is relaxed from `a + b = 4` to `a + b ≤ 4`;
* for `a = 0` the exponent `q = 0` is allowed as well (it is needed for the `w²` leaf weight of
  the slot `(a,b) = (0,4)`; the existing result only allows `q = eta` there).

Route: the slot is dominated by a summand of the integrable `ℋ⁴`-integrand:
`a = 0` gives `V = DzIter b g`, `b ≤ 4`, and `w²σ^{-q} V² ≤ w²σ^{-eta} V² = (DzIter b g · wσ^{-eta/2})²`
(since `σ ≤ 1` and `q ≤ eta`), the `i`-th summand of `HkIntegrand`; `a ≥ 1` gives
`w²σ^{-q}V² ≤ w²σ^{-gam α}V² = (mixed b a g · Wt)²`, a summand of `HkIntegrand` since `1 ≤ a` and
`a + b ≤ 4`.  Everything else (a.e. strong measurability of the slots, the reduction of `Iθ` to the
open interval) is already in `HardSlotAux.SlotIntegrableHonest`. -/
theorem SlotIntegrableGen (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ := by
  have hwne : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwne
  change Integrable (fun θ : ℝ =>
      (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
    (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo]
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- ## `a = 0`: the pure `D_z`-slot with exponent `q ∈ {0, η}`
    subst ha0
    have hb : b ≤ 4 := by omega
    rw [Work.Spaces.mixed_zero_right]
    have hslice : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter b g z θ)
        (Set.Ioo (0 : ℝ) (π / 2)) := ((hg.DzIter b).curry_θ hz).continuousOn
    -- the `η`-weighted slot is a summand of `HkIntegrand`
    have hZ : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have h : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hg hmem b hb (z := z) (le_of_lt hz)
      rwa [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo] at h
    have heta : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine (hZ.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_whz_sq z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.DzIter b g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter b g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    rcases hq0 rfl with hq | hq
    · rw [hq]
      simpa using integrable_slot_rpow_le (V := fun θ => Work.Spaces.DzIter b g z θ)
        (p := Work.Spaces.eta) (q := 0) Work.Spaces.eta_nonneg hslice heta
    · rw [hq]
      exact heta
  · -- ## `a ≥ 1`: every slot is a summand of the `ℋ⁴`-integrand with weight `σ^{-γ}`
    have hcontm : ContinuousOn (fun θ : ℝ => Work.Spaces.mixed b a g z θ)
        (Set.Ioo (0 : ℝ) (π / 2)) := ((hg.mixed b a).curry_θ hz).continuousOn
    have hM : Integrable (fun θ : ℝ =>
        (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have hHk : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
        have h : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
            (volume.restrict Work.Spaces.Iθ) := hmem.1 z (le_of_lt hz)
        rwa [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo] at h
      refine Integrable.mono' hHk ?_ ?_
      · exact ContinuousOn.aestronglyMeasurable
          ((hcontm.mul (Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_Wt_slice α z)).pow 2)
          measurableSet_Ioo
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ a b hapos hab
    have hgamma : Integrable (fun θ : ℝ => (Work.Spaces.mixed b a g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine (hM.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_wt_sq α z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.mixed b a g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed b a g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    rcases hqa hapos with hq | hq | hq
    · rw [hq]
      simpa using integrable_slot_rpow_le (V := fun θ => Work.Spaces.mixed b a g z θ)
        (p := Work.Spaces.gam α) (q := 0) (le_of_lt (Work.Spaces.gam_pos hα)) hcontm hgamma
    · rw [hq]
      exact integrable_slot_rpow_le (V := fun θ => Work.Spaces.mixed b a g z θ)
        (p := Work.Spaces.gam α) (q := Work.Spaces.eta)
        (le_trans (le_of_lt Work.Spaces.eta_lt_one) (le_of_lt (Work.Spaces.one_lt_gam hα)))
        hcontm hgamma
    · rw [hq]
      exact hgamma

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
end
-- ===== merged: Submission.Work.FTS_EllLimOK.VopTransfer.VopJetsAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.VopTransfer

set_option maxHeartbeats 800000

/-- `Vop Ψ = ∂_θΨ - tan θ·Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_vop {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Ψ) := hsm.pth
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) := by
    rw [Work.FTS.EllipticEst.SmoothOpen] at hsm ⊢
    have h : Function.uncurry (fun z θ => Real.tan θ * Ψ z θ)
        = (fun p : ℝ × ℝ => Real.tan p.2) * (Function.uncurry Ψ) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]
    refine ContDiffOn.mul ?_ hsm
    have heq : (fun p : ℝ × ℝ => Real.tan p.2)
        = (fun p : ℝ × ℝ => Real.sin p.2) / (fun p : ℝ × ℝ => Real.cos p.2) := by
      funext p; exact Real.tan_eq_sin_div_cos p.2
    rw [heq]
    refine ContDiffOn.div (contDiffOn_snd.sin) (contDiffOn_snd.cos) ?_
    intro p hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
  rw [Work.FTS.EllipticEst.SmoothOpen] at h1 h2 ⊢
  have h : Function.uncurry (Work.Construction.Vop Ψ)
      = Function.uncurry (Work.Spaces.pth Ψ)
        - Function.uncurry (fun z θ => Real.tan θ * Ψ z θ) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact h1.sub h2

/-- Multiplication by a `C^∞` angular factor preserves `SmoothOpen`. -/
theorem smoothOpen_angular_mul {c : ℝ → ℝ} (hc : ContDiff ℝ ⊤ c) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c θ * f z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hf ⊢
  have h : Function.uncurry (fun z θ => c θ * f z θ)
      = (fun p : ℝ × ℝ => c p.2) * (Function.uncurry f) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  refine ContDiffOn.mul ?_ hf
  exact ((hc.comp contDiff_snd).of_le le_top).contDiffOn

/-- `D_θ`-iterates only see the values on the open quadrant. -/
theorem DthIter_congr_Q0 {u v : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i u))
      (Function.uncurry (Work.Spaces.DthIter i v)) Work.FTS.EllipticEst.Q0 := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n u) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n v) p.1 p.2
      rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hp]

/-- Locality of `mixed` on the open quadrant. -/
theorem mixed_congr_Q0 {u v : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.mixed j i u z θ = Work.Spaces.mixed j i v z θ := by
  intro z θ hz hθ
  have hDth := DthIter_congr_Q0 h i
  exact Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i u) (G := Work.Spaces.DthIter i v)
    (fun z' θ' hz' h1 h2 => hDth (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', h1, h2⟩))
    j z θ hz hθ.1 hθ.2

/-- A `θ`-only factor passes through `D_z`-iterates. -/
theorem DzIter_theta_const_mul (c : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (j : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.DzIter j (fun z θ => c θ * H z θ) z θ
        = c θ * Work.Spaces.DzIter j H z θ := by
  induction j with
  | zero => intro z θ _ _; rfl
  | succ n ih =>
      intro z θ hz hθ
      have heq : Set.EqOn
          (Function.uncurry (Work.Spaces.DzIter n (fun z θ => c θ * H z θ)))
          (Function.uncurry (fun z θ => c θ * Work.Spaces.DzIter n H z θ))
          Work.FTS.EllipticEst.Q0 := by
        intro p hp
        rcases p with ⟨z', θ'⟩
        obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ih z' θ' hz' ⟨hθ'1, hθ'2⟩
      have hpz := Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 heq
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
      simp only [Work.Spaces.pz] at hpz
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hpz, deriv_const_mul_field]
      ring

/-- The recurrence `D_θΨ = sin(2θ)·VopΨ + 2 sin²θ·Ψ` on the open quadrant. -/
theorem Dth_eq_sfun_mul_add {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth Ψ z θ = Real.sin (2 * θ) * Work.Construction.Vop Ψ z θ
      + 2 * Real.sin θ ^ 2 * Ψ z θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have htan : Real.sin (2 * θ) * Real.tan θ = 2 * Real.sin θ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
  simp only [Work.Spaces.Dth, Work.Construction.Vop]
  rw [show Real.sin (2 * θ) * (Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ)
        + 2 * Real.sin θ ^ 2 * Ψ z θ
      = Real.sin (2 * θ) * Work.Spaces.pth Ψ z θ
        - (Real.sin (2 * θ) * Real.tan θ) * Ψ z θ + 2 * Real.sin θ ^ 2 * Ψ z θ from by ring]
  rw [htan]
  ring

/-- **Leibniz for `mixed` with an angular factor.**  For a `C^∞` angular factor `c` and `f`
smooth on the open quadrant, `D_z^j D_θ^i (c(θ)·f) = ∑_{m ≤ i} C(i,m)·(Lop^m c)(θ) ·
D_z^j D_θ^{i-m} f` at every point of the open quadrant. -/
theorem mixed_angular_mul {c : ℝ → ℝ} (hc : ∀ θ : ℝ, ContDiffAt ℝ ⊤ c θ)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (fun z θ => c θ * f z θ) z θ
      = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ
          * Work.Spaces.mixed j (i - m) f z θ := by
  have hck : ∀ k : ℕ, ContDiff ℝ k c := fun k => (contDiff_iff_contDiffAt.mpr hc).of_le le_top
  have hcd : ∀ (a : ℕ) (z₀ : ℝ), a ≤ i → DifferentiableOn ℝ
      (fun θ' => Work.Spaces.DthIter a (fun z θ => c θ) z₀ θ') (Set.Ioo 0 (π / 2)) := by
    intro a z₀ _
    have h1 : ContDiff ℝ 1 (Work.Spaces.Lop^[a] c) := contDiff_Lop_iterate c hck a 1
    have h2 : (fun θ' => Work.Spaces.DthIter a (fun z θ => c θ) z₀ θ') = Work.Spaces.Lop^[a] c := by
      funext θ'
      exact congrFun (Work.Spaces.DthIter_eq_iterate_Lop a (fun z θ => c θ) z₀) θ'
    rw [h2]
    exact (h1.differentiable (by norm_num)).differentiableOn
  have hfd : ∀ z' : ℝ, 0 < z' → ∀ a ≤ i, DifferentiableOn ℝ
      (fun θ' => Work.Spaces.DthIter a f z' θ') (Set.Ioo 0 (π / 2)) := by
    intro z' hz' a _
    have h1 : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.DthIter a f z' θ') (Set.Ioo 0 (π / 2)) :=
      contDiffOn_iff_forall_nat_le.mp ((hf.DthIter a).curry_θ hz') 1 le_top
    exact h1.differentiableOn (by norm_num)
  have hident : ∀ (m : ℕ) (z₀ θ₀ : ℝ), Work.Spaces.DthIter m (fun z θ => c θ) z₀ θ₀
      = Work.FTS.EllipticEst.LopIter m c θ₀ := by
    intro m z₀ θ₀
    rw [Work.Spaces.DthIter_eq_iterate_Lop]
    rfl
  have hEqOn : Set.EqOn
      (Function.uncurry (Work.Spaces.DthIter i (fun a b : ℝ => c b * f a b)))
      (Function.uncurry (fun z' θ' => ∑ m ∈ Finset.range (i + 1),
        ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ')
          * Work.Spaces.DthIter (i - m) f z' θ'))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp
    rcases p with ⟨z', θ'⟩
    obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hleib := Work.FTS.TransportS.DthIter_mul_eq_of_diffOn i (fun z θ => c θ) f
      (z := z') (θ := θ') ⟨hθ'1, hθ'2⟩ (fun a ha => hcd a z' ha) (fun a ha => hfd z' hz' a ha)
    show Work.Spaces.DthIter i (fun a b : ℝ => c b * f a b) z' θ'
      = ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ')
          * Work.Spaces.DthIter (i - m) f z' θ'
    rw [hleib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hident m z' θ']
    ring
  rw [show Work.Spaces.mixed j i (fun z θ => c θ * f z θ)
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun a b : ℝ => c b * f a b)) from rfl,
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter i (fun a b : ℝ => c b * f a b))
      (G := fun z' θ' => ∑ m ∈ Finset.range (i + 1),
        ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ')
          * Work.Spaces.DthIter (i - m) f z' θ')
      (fun z' θ' hz' h1 h2 => hEqOn (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', h1, h2⟩))
      j z θ hz hθ.1 hθ.2,
    Work.FTS.TransportS.DzIter_sum_const_mul (Finset.range (i + 1))
      (fun m θ' => (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ')
      (fun m => Work.Spaces.DthIter (i - m) f) (fun m _ => hf.DthIter (i - m)) j hz hθ.1 hθ.2]
  exact Finset.sum_congr rfl fun m _ => rfl

end Work.FTS_EllLimOK.VopTransfer
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.STC.L12_sub_C4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.STC

theorem L12_sub_C4 {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : ContDiffOn ℝ 4 (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hb : ContDiffOn ℝ 4 (Function.uncurry b) Work.FTS.EllipticEst.Q0)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    ∀ z ∈ Work.Spaces.Iz, Work.Construction.L12 (fun z θ => a z θ - b z θ) z
      = Work.Construction.L12 a z - Work.Construction.L12 b z := by
  intro z hz
  -- `z ∈ Iz = [0,∞)`, so `0 ≤ z`
  have hz0 : 0 ≤ z := hz
  -- `C^4` on `Q0` gives continuity there: this is the only input the integrability
  -- certificates need, no derivative of `a` or of `b` is used
  have hconta : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0 := ha.continuousOn
  have hcontb : ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0 := hb.continuousOn
  -- the four integrability certificates of `L12_sub_of_integrable`
  refine Work.FTS.StrongEps.EComparison.L12_sub_of_integrable (z := z) ?_ ?_ ?_ ?_
  · -- angular slice of `a`: `s > z ≥ 0` gives `s > 0`
    intro s hs
    exact Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
      hconta hma s (lt_of_le_of_lt hz0 hs)
  · intro s hs
    exact Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
      hcontb hmb s (lt_of_le_of_lt hz0 hs)
  · -- density of `a`: integrable on `(0,∞)`, hence on `(z,∞) ⊆ (0,∞)`
    exact (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
      hconta hma).mono_set (Set.Ioi_subset_Ioi hz0)
  · exact (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
      hcontb hmb).mono_set (Set.Ioi_subset_Ioi hz0)

end Work.FTS_RegExport.RXT.STC
end
-- ===== merged: Submission.Work.H2.T1Q.SupThetaIntQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

/-! ## The interior-class weight identity for the `D_θ`-slot -/



/-! ## Almost-everywhere identifications of the intervals `Iθ` and `Iz` -/

/-- `Iθ = [0,π/2]` differs from the open interval `(0,π/2)` by the null set `{0,π/2}`. -/
private theorem Iθ_ae_eq_Ioo : (Iθ : Set ℝ) =ᵐ[volume] Set.Ioo 0 (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `Iz = [0,∞)` differs from the open half-line `(0,∞)` by the null set `{0}`. -/
private theorem Iz_ae_eq_Ioi : (Iz : Set ℝ) =ᵐ[volume] Set.Ioi 0 :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm



/-! ## Integrability of the two angular slices -/

/-- On `z > 0`, `w z ≥ 1`. -/
private theorem one_le_w_of_pos_prv {z : ℝ} (hz : 0 < z) : 1 ≤ w z := by
  rw [w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith



/-! ## The two `H^k`-blocks -/



/-! ## The slicewise bound and its consequences -/

/-- The two-term majorant of the slice estimate at the fixed radius `z`. -/
private def Bfun (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (4 / Real.pi) * (∫ θ in Iθ, (DzIter 3 f z θ) ^ 2)
    + (200 / (gam α - 1))
        * ∫ θ in Iθ, (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)




/-! ## The target -/


end Work.H2.T1Q
end
end
-- ===== merged: Submission.Work.H2W.FstarDzIterFourPsiAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`4` moment of the solution in the weak class

The requested lemma is

```
```

i.e. the angular moment `F_*(D_z^4 Ψ) = ∫_θ D_z^4Ψ(z,θ)·sinθcos²θ dθ` of the four-fold
radially differentiated solution vanishes almost everywhere in `z > 0`, for every datum of the
weak hypothesis class at level `2`.

## The route

The moment chain of `H2W/momentChainAe` (`MomentAe.Fstar_DzIter_le_Psi`) gives the *pointwise*
vanishing of `F_*(D_z^j Ψ)` for `j ≤ 3` — one level short of the target.  The missing level is
obtained from the *only* other `z`-honesty the class carries, namely

`HkMem α 2 A`,   `A := z²∂_z²Ψ`,

through the radial identity `D_z^{j+2}Ψ = D_z^{j+1}Ψ + D_z^j A` (i.e.
`D_z^j A = D_z^{j+2}Ψ - D_z^{j+1}Ψ`, `MomentAe.DzIter_zsq_pzIter2_eq`).  In particular

* `j = 2`: `D_z^4Ψ = D_z^3Ψ + D_z²A` — the decomposition which reduces the target to the moment
  of `A`;
* `j = 1`: `D_zA = D_z³Ψ - D_z²Ψ`, whence `F_*(D_zA) ≡ 0` pointwise (both terms vanish by
  `Fstar_DzIter_le_Psi` at levels `3` and `2`).

Applying the *level-`2`* moment argument of `H2W/Fstar_DzIter_two_F` to the honest datum
`A ∈ ℋ²` (`SmoothOpen A` holds because `A` is `z²` times a second `z`-derivative of `Ψ`,
`MomentAe.smoothOpen_zsq`) gives `F_*(D_z²A) = 0` a.e.: the moment tower
`Cert.radIter_bmom_ae_hasDerivAt` at level `2` says that `B_1 = F_*(D_zA)` is a.e.
differentiable with derivative `B_2/r = F_*(D_z²A)/r`, and `B_1 ≡ 0` forces that derivative to
vanish.

The final assembly is the `θ`-a.e. identity `D_z^4Ψ = D_z^3Ψ + D_z²A` plus the integrability of
the two right-hand slices (`MomentAe.level_bound` for `D_z^3Ψ`, and
`Cert.GbarSin.integrableOn_DzIter_mul_sinCos2` for `D_z²A`).
-/

namespace Work.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Topology

open MeasureTheory Set Filter

end Work.H2W
end
