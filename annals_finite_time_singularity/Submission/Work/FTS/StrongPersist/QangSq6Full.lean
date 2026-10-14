import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.DzAgmonClean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.Blocks.DzV_amgm_clean` (same namespaces), so importing both was a duplicate-declaration
-- error.  The names stay available to every consumer of this module through the import
-- above.
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_cross_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeSlotOneAe.Interp

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The four functions of the cross-slot identity

`A = z²∂_z²Ψ`, `A' = z²∂_z²(D_zΨ)`, `B = ∂_θ²Ψ`, `H = ∂_θ²(D_zΨ) - ∂_θ²Ψ`. -/

/-- `A = z² ∂_z²Ψ`, the radial-second-derivative datum of the A-slot. -/
def Az (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ


/-- `B = ∂_θ²Ψ`. -/
def Bz (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pthIter 2 Ψ z θ

/-- `H = ∂_θ²(D_zΨ) - ∂_θ²Ψ`; the `B' - B` whose square is the `B`-side of the slot. -/
def Hz (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
    - Work.Spaces.pthIter 2 Ψ z θ

/-- `ρ(z) = 1 - 4/(1+z)`. -/
def rhoZ (z : ℝ) : ℝ := 1 - 4 / (1 + z)

/-- `σ(θ) = sin(2θ)^{2-γ}`, `γ = gam α`: the angular weight of the `Tk`-slot. -/
def sigA (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-! ## Facts about `ρ` and the radial weight -/



theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-! ## Facts about `σ` -/


theorem sigA_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigA α θ := by
  rw [sigA]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩) _

theorem sigA_pos {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sigA α θ := by
  rw [sigA]
  exact Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _


/-- `σ = sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}` on `Iθ`: the `γ`-weight of the `Tk`-slot is dominated
by the `η`-weight of the `ℋ^k`-norm. -/
theorem sigA_le_sEta {α : ℝ} (hα : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    sigA α θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have h0 : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le h0 with h | h
  · have h1 : 2 - Work.Spaces.gam α ≠ 0 := by
      simp only [Work.Spaces.gam]; intro hc; linarith
    have h2 : -(Work.Spaces.eta) ≠ 0 := by simp only [Work.Spaces.eta]; norm_num
    rw [sigA, ← h, Real.zero_rpow h1, Real.zero_rpow h2]
  · refine Real.rpow_le_rpow_of_exponent_ge h (Real.sin_le_one _) ?_
    simp only [Work.Spaces.eta, Work.Spaces.gam]; linarith




end Work.FTS.EllipticEst.AeSlotOneAe.Interp
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Dispatch

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `σ θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private lemma sEta_nonneg_Iθ_M {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _

/-!
# `HkMem α 0 u` in the almost-everywhere class

The level-`0` `ℋ`-membership `Work.Spaces.HkMem α 0 u` of the solution of `bslOp α u = G` in the
almost-everywhere class `AeData`.  The class gives `HkMem` of `G`, of `z²∂_zz u` and of `∂_θθ u`
but nothing directly about `u`; the missing ingredient is the *slicewise* bound
`∫_θ u(z,θ)² σ θ ≤ C ∫_θ (∂_θθ u)(z,θ)² σ θ` (`σ = sin(2θ)^{-η}`), which holds for a.e. `z`: the
two a.e. moment conditions of `AeData` kill the only angular mode (the affine one) that the second
angular derivative does not see.

That slice bound is produced by the a.e. version `H2W.Ae.aesliceU_of` of the sibling development,
fed with the *two-derivative weighted Hardy inequality* for slices whose two endpoint limits
vanish (`H2W.Ae.ZeroHardy.sliceZeroLimitHardy`, proved in `H2W/Ae/ZeroHardy/`), and the
`θ → π/2` endpoint behaviour of the slices (`H2W.Ae.AeSliceRightTendsto`).

The last step — from the a.e. *slice* bound to the honest `HkMem α 0 u` — is carried out here:
the a.e. strong measurability of the outer integrand and the slicewise boundedness of `u`
(`Endpt.sliceBdd_of_hmB`) give the two halves of `HkMem`.
-/

/-! ## The level-`0` integrand and its slice integral in the `σ`-form -/

/-- On `Iθ` the level-`0` integrand is `w(z)² · (g z θ)² · σ θ`. -/
private theorem hkIntegrand_zero_thEta_M (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, mul_pow,
    Work.FTS.EllipticEst.Honest.sq_weight_eq
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.thEta]
  ring

/-- The `θ`-integral of the level-`0` integrand, with the radial weight `w(z)²` pulled out. -/
private theorem integral_hkIntegrand_zero_M (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  exact hkIntegrand_zero_thEta_M α g hθ

/-- The `θ`-integral of the level-`0` integrand is nonnegative. -/
private theorem integral_hkIntegrand_zero_nonneg_M (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)

/-! ## From the a.e. `lintegral` slice bound to the a.e. integral slice bound -/

/-- **The a.e. slice bound in real-integral form.**  An a.e. (in `z`) `lintegral` comparison for
the slice integrands upgrades to the comparison of the honest integrals, because the right-hand
side is honest by hypothesis. -/
theorem aeReal_of_aeLintegralM {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ ENNReal.ofReal K * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
  -- the second-derivative slice integrand is honest
  have hint2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ :=
    slice_sigma_sq_of_hkMem_D hmemB hzpos
  have hnn2 : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ_M hθ))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2 hnn2] at hz
  rw [← ENNReal.ofReal_mul (le_of_lt hK)] at hz
  -- the left-hand side is finite
  have hfin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) < ⊤ :=
    lt_of_le_of_lt hz ENNReal.ofReal_lt_top
  -- hence the left integrand is integrable
  have hcontσ : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
    exact hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
  have hcontu : ContinuousOn (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsmooth hzpos 1).continuousOn
  have haesmA : MeasureTheory.AEStronglyMeasurable
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : ContinuousOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := (hcontu.pow 2).mul hcontσ
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      h1.aestronglyMeasurable measurableSet_Ioo
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2))] at h2
    rw [Work.Spaces.Iθ]
    exact h2
  -- build the `IntegrableOn` statement
  have hnnA : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ_M hθ))
  have hFinA : MeasureTheory.HasFiniteIntegral
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine lt_of_eq_of_lt ?_ hfin
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hnnA] with θ hθ
    exact Real.enorm_of_nonneg hθ
  have hintA : MeasureTheory.IntegrableOn
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    ⟨haesmA, hFinA⟩
  -- conclude by comparing `ofReal`s
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintA hnnA] at hz
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_of_lt hK)
    (MeasureTheory.integral_nonneg_of_ae hnn2))).mp hz

/-! ## The main body -/

/-- **`HkMem α 0 u` from the a.e. slice inequality.** -/
theorem hkMem_uM_of_ae_boundM (K : ℝ) (hKpos : 0 < K)
    (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :
    Work.Spaces.HkMem α 0 u := by
  -- ## the level-`0` integrand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        = fun p : ℝ × ℝ => (u p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p
      simp [Work.Spaces.HkIntegrand]
    rw [hfun]
    exact (((h.smooth 1).continuousOn).mul
      Work.FTS.EllipticEst.continuousOn_wdivsin_Q0).pow 2
  -- ## a.e. strong measurability of the angular slices
  have haesm_slice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · rw [← h0]
      refine (MeasureTheory.aestronglyMeasurable_const :
        MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
      filter_upwards with θ
      simp [Work.Spaces.HkIntegrand, Work.Spaces.w]
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
  -- ## a.e. strong measurability of the `θ`-integral
  have haesm_outer : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  -- ## the a.e. slice inequality, transported to `Iz`
  have hslice_bound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici 0)), _
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact hbound
  -- ## the a.e. bound of the outer integrand
  have hFbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ := by
    filter_upwards [hslice_bound] with z hz
    rw [integral_hkIntegrand_zero_M α u z,
      integral_hkIntegrand_zero_M α (Work.Spaces.pthIter 2 u) z]
    calc (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ (Work.Spaces.w z) ^ 2
            * (K * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
          mul_le_mul_of_nonneg_left hz (sq_nonneg _)
      _ = K * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring
  refine ⟨?_, ?_⟩
  · -- every angular slice of the integrand is integrable
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · rw [← h0]
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 u 0 θ) = fun _ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.HkIntegrand, Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · obtain ⟨Cz, hCzpos, hCz⟩ :=
        Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz0
      refine Integrable.mono'
        ((Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul
          ((Work.Spaces.w z) ^ 2 * Cz ^ 2)) (haesm_slice z hz) ?_
      have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          θ ∈ Set.Ioo 0 (Real.pi / 2) := by
        rw [Work.Spaces.Iθ]
        rw [MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
            (a := 0) (b := Real.pi / 2)).symm]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hmem] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 u z θ)]
      have hθI : θ ∈ Work.Spaces.Iθ :=
        Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsq : (u z θ) ^ 2 ≤ Cz ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hCz θ hθ).1 2
      calc Work.Spaces.HkIntegrand α 0 u z θ
          = (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
            hkIntegrand_zero_thEta_M α u hθI
        _ ≤ (Work.Spaces.w z) ^ 2 * (Cz ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right hsq
              (sEta_nonneg_Iθ_M hθI)
        _ = ((Work.Spaces.w z) ^ 2 * Cz ^ 2) * Work.FTS.EllipticEst.thEta θ := by ring
  · -- the `z`-integral of the angular slices is integrable
    refine Integrable.mono' (h.memAng2.2.const_mul K) haesm_outer ?_
    filter_upwards [hFbound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_hkIntegrand_zero_nonneg_M α u z)]
    exact hz

theorem hkMem_uM (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) : Work.Spaces.HkMem α 0 u := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.H2W.Ae.aesliceU_of
    Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
    Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy
  exact hkMem_uM_of_ae_boundM K hKpos α u G h
    (aeReal_of_aeLintegralM h.smooth h.memAng2 hKpos (hK α u G h))

end

end Work.FTS.EllipticEst.Dispatch
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.sliceZibpD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Three elementary consequences of a compactly supported tail -/





/-- The derivative of a function supported in `[δ,b]` vanishes off `[δ,b]`. -/
theorem deriv_eq_zero_off {f : ℝ → ℝ} {δ b : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ b → f z = 0) :
    ∀ z, z ∉ Set.Icc δ b → deriv f z = 0 := by
  intro z hz
  have hnb : f =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    rcases not_and_or.mp hz with h | h
    · have hzδ : z < δ := not_le.mp h
      filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hzδ)] with y hy
      refine hsupp y (fun hc => ?_)
      rw [Metric.mem_ball, Real.dist_eq] at hy
      exact absurd hc.1 (not_le.mpr (by linarith [(abs_lt.mp hy).2]))
    · have hzb : b < z := not_le.mp h
      filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hzb)] with y hy
      refine hsupp y (fun hc => ?_)
      rw [Metric.mem_ball, Real.dist_eq] at hy
      exact absurd hc.2 (not_le.mpr (by linarith [neg_lt.mp (abs_lt.mp hy).1]))
  rw [hnb.deriv_eq]
  simp


/-! ## The two radial integrations by parts, sliced in `θ` -/


end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.ReHome.TkKit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaUp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-!
# `H2W.Ae.aeSigmaUp` — the `σ`-upgrade of the level-`0` `ℋ`-mass of `u`

```
∃ C > 0, ∀ α u G, AeData α u G →
    L2Mem (∂_θu · w) → HkSq α 0 u ≤ C · L2Sq (∂_θu · w) .
```

The right-hand side is the *unweighted* angular square integral of `∂_θu` (with the radial
weight `w` inside), while the left-hand side carries the singular angular weight
`σ θ = sin(2θ)^{-η}`.  The content is the slicewise `σ`-Poincaré inequality of
`Work.FTS.EllipticEst.Honest.SigmaPoincare`: for a fibre `u(z,·)` with vanishing moment
`∫_θ u(z,θ) sinθcos²θ dθ = 0` (which `AeData` supplies for almost every `z`)

  `∫_θ u(z,θ)² σ θ ≤ C ∫_θ (∂_θu(z,θ))²`,

valid for almost every `z > 0`.  That a.e. bound is exactly `H2W.AeProof.AeSigmaUpgradeU_ae`
(in `lintegral` form), and `H2W.AeProof.AeSliceMomentU_integrable` discharges its honesty
hypothesis.

The only work left here is bookkeeping: multiply by the *nonnegative* radial weight `w(z)²`
(so that the singular weight is restored on the left and the honest integrand `(∂_θu·w)²`
appears on the right), convert the two `lintegral`s into honest integrals of the actual
`HkSq`/`L2Sq` integrands and integrate in `z`.

Two points of care: since `w z` sits *inside* the square on the right, no division by `w z`
is ever needed; and honesty of `θ ↦ HkIntegrand α 0 u z θ` is *not* assumed — the
Bochner–`lintegral` conversion is done under a case split, the non-integrable case giving the
inequality trivially, because the totalised Bochner integral is then `0` (the same dichotomy
that `H2W.HkSq_le_of_ae_slice_le` uses at the level of the whole domain).
-/




end

end Work.FTS.EllipticEst.H2W.Ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeSigma/AeHkMemU` — the honesty `HkMem α 0 u` in the a.e. class, self-contained

`Work.FTS.EllipticEst.H2W.Ae.hkMem_u` proves `HkMem α 0 u` for `AeData α u G`, but its module
imports `Honest.firstOrderHonest`, whose closure contains modules under active construction.
This module re-proves the same statement using only the `sigma`-slice bound `aesliceU` (proved),
the slice boundedness `Endpt.sliceBdd_of_hmB` (proved) and the integrability of `σ` — so that the
`aeDzNorm` development (and the lemmas delegated around it) do not depend on that closure.

The mathematical content is the same as in `hkMem_u.lean`: `AeData` gives `HkMem α 0 (∂_θθu)`,
`aesliceU` gives `∫_θ u²σ ≤ K ∫_θ (∂_θθu)²σ` for a.e. `z`, and integrating this a.e. bound
against `w²` gives the honesty of the outer level-`0` integrand; the *slicewise* integrability
of `HkIntegrand α 0 u z` is get from the boundedness of the slice
(`Endpt.sliceBdd_of_hmB`) and the integrability of `σ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.AeSigma

set_option autoImplicit false

/-! ## The level-`0` integrand in the `σ`-form -/

theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _

/-- At level `0` the `HkSq`-integrand of a slice is `w z² · g z θ² · σ θ` on `Iθ`. -/
theorem hkIntegrand_w (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.sEta]
  try rw [show θ * 2 = 2 * θ from by ring]
  ring

/-- The `θ`-integral of the level-`0` integrand, with the radial weight pulled out. -/
theorem integral_hkIntegrand_w (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => hkIntegrand_w α g hθ)

/-- The `θ`-integral of the level-`0` integrand is nonnegative. -/
theorem integral_hkIntegrand_w_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)

/-! ## From the a.e. `lintegral` slice bound to the a.e. integral slice bound -/

/-- **The a.e. slice bound in real-integral form.**  An a.e. (in `z`) `lintegral` comparison for
the slice integrands upgrades to the comparison of the honest integrals, because the right-hand
side is honest by hypothesis. -/
theorem aeRealIntegral_le_of_aeLintegral {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal K * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
  -- the second-derivative slice integrand is honest
  have hint2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hmemB hzpos
  have hnn2 : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2 hnn2] at hz
  rw [← ENNReal.ofReal_mul (le_of_lt hK)] at hz
  -- the left-hand side is finite
  have hfin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) < ⊤ :=
    lt_of_le_of_lt hz ENNReal.ofReal_lt_top
  -- hence the left integrand is integrable
  have hcontσ : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
    exact hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
  have hcontu : ContinuousOn (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsmooth hzpos 1).continuousOn
  have haesmA : MeasureTheory.AEStronglyMeasurable
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : ContinuousOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := (hcontu.pow 2).mul hcontσ
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      h1.aestronglyMeasurable measurableSet_Ioo
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2))] at h2
    rw [Work.Spaces.Iθ]
    exact h2
  have hnnA : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hFinA : MeasureTheory.HasFiniteIntegral
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine lt_of_eq_of_lt ?_ hfin
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hnnA] with θ hθ
    exact Real.enorm_of_nonneg hθ
  have hintA : MeasureTheory.IntegrableOn
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    ⟨haesmA, hFinA⟩
  -- conclude by comparing `ofReal`s
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintA hnnA] at hz
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_of_lt hK)
    (MeasureTheory.integral_nonneg_of_ae hnn2))).mp hz

/-! ## `HkMem α 0 u` -/

/-- **`HkMem α 0 u` in the a.e. class, from the a.e. slice inequality.** -/
theorem AeHkMemU_of_ae_bound (K : ℝ) (hKpos : 0 < K)
    (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :
    Work.Spaces.HkMem α 0 u := by
  -- ## the level-`0` integrand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        = fun p : ℝ × ℝ => (u p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p
      simp [Work.Spaces.HkIntegrand]
    rw [hfun]
    exact (((h.smooth 1).continuousOn).mul
      Work.FTS.EllipticEst.continuousOn_wdivsin_Q0).pow 2
  -- ## a.e. strong measurability of the angular slices
  have haesm_slice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · rw [← h0]
      refine (MeasureTheory.aestronglyMeasurable_const :
        MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
      filter_upwards with θ
      simp [Work.Spaces.HkIntegrand, Work.Spaces.w]
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
  -- ## a.e. strong measurability of the `θ`-integral
  have haesm_outer : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  -- ## the a.e. slice inequality, transported to `Iz`
  have hslice_bound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici 0)), _
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact hbound
  -- ## the a.e. bound of the outer integrand
  have hFbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ := by
    filter_upwards [hslice_bound] with z hz
    rw [integral_hkIntegrand_w α u z, integral_hkIntegrand_w α (Work.Spaces.pthIter 2 u) z]
    calc (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (Work.Spaces.w z) ^ 2
            * (K * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
          mul_le_mul_of_nonneg_left hz (sq_nonneg _)
      _ = K * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring
  refine ⟨?_, ?_⟩
  · -- every angular slice of the integrand is integrable
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · rw [← h0]
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 u 0 θ) = fun _ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.HkIntegrand, Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · obtain ⟨Cz, hCzpos, hCz⟩ :=
        Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz0
      refine Integrable.mono'
        ((Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul
          ((Work.Spaces.w z) ^ 2 * Cz ^ 2)) (haesm_slice z hz) ?_
      have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          θ ∈ Set.Ioo 0 (Real.pi / 2) := by
        rw [Work.Spaces.Iθ]
        rw [MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
            (a := 0) (b := Real.pi / 2)).symm]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hmem] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 u z θ)]
      have hθI : θ ∈ Work.Spaces.Iθ :=
        Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsq : (u z θ) ^ 2 ≤ Cz ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hCz θ hθ).1 2
      calc Work.Spaces.HkIntegrand α 0 u z θ
          = (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
            hkIntegrand_w α u hθI
        _ ≤ (Work.Spaces.w z) ^ 2 * (Cz ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right hsq
              (sEta_nonneg_Iθ hθI)
        _ = ((Work.Spaces.w z) ^ 2 * Cz ^ 2) * Work.FTS.EllipticEst.sEta θ := by ring
  · -- the `z`-integral of the angular slices is integrable
    refine Integrable.mono' (h.memAng2.2.const_mul K) haesm_outer ?_
    filter_upwards [hFbound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_hkIntegrand_w_nonneg α u z)]
    exact hz

/-- **`HkMem α 0 u` for `AeData` data** (self-contained version of `H2W.Ae.hkMem_u`). -/
theorem AeHkMemU (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) : Work.Spaces.HkMem α 0 u := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.H2W.Ae.aesliceU
  exact AeHkMemU_of_ae_bound K hKpos α u G h
    (aeRealIntegral_le_of_aeLintegral h.smooth h.memAng2 hKpos (hK α u G h))

end Work.FTS.EllipticEst.H2W.AeProof.AeSigma
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.H2W.Ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `σ θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _

/-- **Pointwise normalisation of the level-`0` integrand** (the copy of
`Honest.hkIntegrand_eq_w_sq` with the target weight `thEta` of this chapter). -/
private theorem hkIntegrand_eq_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α g z θ,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
      (Work.FTS.EllipticEst.sin_two_nonneg hθ)]
  simp only [Work.FTS.EllipticEst.thEta]
  ring

/-!
# `HkMem α 0 u` in the almost-everywhere class

The level-`0` `ℋ`-membership `Work.Spaces.HkMem α 0 u` of the solution of `bslOp α u = G` in the
almost-everywhere class `AeData`.  The class gives `HkMem` of `G`, of `z²∂_zz u` and of `∂_θθ u`
but nothing directly about `u`; the missing ingredient is the *slicewise* bound
`∫_θ u(z,θ)² σ θ ≤ C ∫_θ (∂_θθ u)(z,θ)² σ θ` (`σ = sin(2θ)^{-η}`), which holds for a.e. `z`: the
two a.e. moment conditions of `AeData` kill the only angular mode (the affine one) that the second
angular derivative does not see.

That slice bound is produced by the a.e. version `H2W.Ae.aesliceU_of` of the sibling development,
fed with the *two-derivative weighted Hardy inequality* for slices whose two endpoint limits
vanish (`H2W.Ae.ZeroHardy.sliceZeroLimitHardy`, proved in `H2W/Ae/ZeroHardy/`), and the
`θ → π/2` endpoint behaviour of the slices (`H2W.Ae.AeSliceRightTendsto`).

The last step — from the a.e. *slice* bound to the honest `HkMem α 0 u` — is carried out here:
the a.e. strong measurability of the outer integrand and the slicewise boundedness of `u`
(`Endpt.sliceBdd_of_hmB`) give the two halves of `HkMem`.
-/

/-! ## The level-`0` integrand and its slice integral in the `σ`-form -/

/-- On `Iθ` the level-`0` integrand is `w(z)² · (g z θ)² · σ θ`. -/
private theorem hkIntegrand_zero_thEta (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
  hkIntegrand_eq_w_sq α g hθ

/-- The `θ`-integral of the level-`0` integrand, with the radial weight `w(z)²` pulled out. -/
private theorem integral_hkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  exact hkIntegrand_zero_thEta α g hθ

/-- The `θ`-integral of the level-`0` integrand is nonnegative. -/
private theorem integral_hkIntegrand_zero_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)

/-! ## From the a.e. `lintegral` slice bound to the a.e. integral slice bound -/

/-- **The a.e. slice bound in real-integral form.**  An a.e. (in `z`) `lintegral` comparison for
the slice integrands upgrades to the comparison of the honest integrals, because the right-hand
side is honest by hypothesis. -/
theorem aeReal_of_aeLintegral {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ ENNReal.ofReal K * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
  -- the second-derivative slice integrand is honest
  have hint2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hmemB hzpos
  have hnn2 : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2 hnn2] at hz
  rw [← ENNReal.ofReal_mul (le_of_lt hK)] at hz
  -- the left-hand side is finite
  have hfin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) < ⊤ :=
    lt_of_le_of_lt hz ENNReal.ofReal_lt_top
  -- hence the left integrand is integrable
  have hcontσ : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
    exact hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
  have hcontu : ContinuousOn (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsmooth hzpos 1).continuousOn
  have haesmA : MeasureTheory.AEStronglyMeasurable
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : ContinuousOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := (hcontu.pow 2).mul hcontσ
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      h1.aestronglyMeasurable measurableSet_Ioo
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2))] at h2
    rw [Work.Spaces.Iθ]
    exact h2
  -- build the `IntegrableOn` statement
  have hnnA : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hFinA : MeasureTheory.HasFiniteIntegral
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine lt_of_eq_of_lt ?_ hfin
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hnnA] with θ hθ
    exact Real.enorm_of_nonneg hθ
  have hintA : MeasureTheory.IntegrableOn
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    ⟨haesmA, hFinA⟩
  -- conclude by comparing `ofReal`s
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintA hnnA] at hz
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_of_lt hK)
    (MeasureTheory.integral_nonneg_of_ae hnn2))).mp hz

/-! ## The main body -/

/-- **`HkMem α 0 u` from the a.e. slice inequality.** -/
theorem hkMem_u_of_ae_bound (K : ℝ) (hKpos : 0 < K)
    (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :
    Work.Spaces.HkMem α 0 u := by
  -- ## the level-`0` integrand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        = fun p : ℝ × ℝ => (u p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p
      simp [Work.Spaces.HkIntegrand]
    rw [hfun]
    exact (((h.smooth 1).continuousOn).mul
      Work.FTS.EllipticEst.continuousOn_wdivsin_Q0).pow 2
  -- ## a.e. strong measurability of the angular slices
  have haesm_slice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · rw [← h0]
      refine (MeasureTheory.aestronglyMeasurable_const :
        MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
      filter_upwards with θ
      simp [Work.Spaces.HkIntegrand, Work.Spaces.w]
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
  -- ## a.e. strong measurability of the `θ`-integral
  have haesm_outer : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  -- ## the a.e. slice inequality, transported to `Iz`
  have hslice_bound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici 0)), _
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact hbound
  -- ## the a.e. bound of the outer integrand
  have hFbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ := by
    filter_upwards [hslice_bound] with z hz
    rw [integral_hkIntegrand_zero α u z,
      integral_hkIntegrand_zero α (Work.Spaces.pthIter 2 u) z]
    calc (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ (Work.Spaces.w z) ^ 2
            * (K * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
          mul_le_mul_of_nonneg_left hz (sq_nonneg _)
      _ = K * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring
  refine ⟨?_, ?_⟩
  · -- every angular slice of the integrand is integrable
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · rw [← h0]
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 u 0 θ) = fun _ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.HkIntegrand, Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · obtain ⟨Cz, hCzpos, hCz⟩ :=
        Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz0
      refine Integrable.mono'
        ((Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul
          ((Work.Spaces.w z) ^ 2 * Cz ^ 2)) (haesm_slice z hz) ?_
      have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          θ ∈ Set.Ioo 0 (Real.pi / 2) := by
        rw [Work.Spaces.Iθ]
        rw [MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
            (a := 0) (b := Real.pi / 2)).symm]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hmem] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 u z θ)]
      have hθI : θ ∈ Work.Spaces.Iθ :=
        Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsq : (u z θ) ^ 2 ≤ Cz ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hCz θ hθ).1 2
      calc Work.Spaces.HkIntegrand α 0 u z θ
          = (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
            hkIntegrand_zero_thEta α u hθI
        _ ≤ (Work.Spaces.w z) ^ 2 * (Cz ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right hsq
              (sEta_nonneg_Iθ hθI)
        _ = ((Work.Spaces.w z) ^ 2 * Cz ^ 2) * Work.FTS.EllipticEst.thEta θ := by ring
  · -- the `z`-integral of the angular slices is integrable
    refine Integrable.mono' (h.memAng2.2.const_mul K) haesm_outer ?_
    filter_upwards [hFbound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_hkIntegrand_zero_nonneg α u z)]
    exact hz

theorem hkMem_u (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) : Work.Spaces.HkMem α 0 u := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.H2W.Ae.aesliceU_of
    Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
    Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy
  exact hkMem_u_of_ae_bound K hKpos α u G h
    (aeReal_of_aeLintegral h.smooth h.memAng2 hKpos (hK α u G h))

end

end Work.FTS.EllipticEst.H2W.AngBW.S3
end
-- ===== merged: Submission.Work.FTS.LocDataExt.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The interior class `RegQ` of the localised datum -/

/-- On `z > 0` the radial weight is at least `1`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith



/-! ## The deliverable: the localised datum as data for `galerkin_bound` -/


end Work.FTS.LocDataExt
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.QangSq6Full =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Null-set bookkeeping (the two ends of `Iz`, the two angular endpoints) -/

private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `w²` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The pointwise slot domination at an arbitrary order `k` -/

/-- **A single pure `D_z`-slot of the `ℋ^k`-integrand dominates the square of the iterate, on
the open quadrant.**  On `z > 0` and `0 < θ < π/2` one has `w(z) ≥ 1` and
`sin(2θ)^{-η} ≥ 1`, so the weighted slot `(D_z^j g · w/sin(2θ)^{η/2})²` of the integrand
dominates the unweighted square: `(D_z^j g)² ≤ HkIntegrand α k g` for `j ≤ k`.

This is `Work.Elliptic.sq_DzIter_le_HkIntegrand_Qd` (the case `k = 4`) with `4 ↦ k`. -/
private theorem sq_DzIter_le_HkIntegrand_k (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) {j : ℕ}
    (hj : j ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw := Work.Elliptic.one_le_w hz
  have hsinp := Work.Elliptic.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
  have hstep : (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    calc (Work.Spaces.DzIter j g z θ) ^ 2
        = (Work.Spaces.DzIter j g z θ) ^ 2 * 1 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)) hsinp ?_ (by positivity)
          positivity
  have heq : (Work.Spaces.DzIter j g z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  rw [← heq] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj)

/-! ## The weighted slot, with the full weight `w²` -/

/-- On the open quadrant, `(D_z^i g)²·w²` is dominated by the `ℋ^k`-integrand (`i ≤ k`).
Immediate from `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (which gives
`(D_z^i g)² ≤ HkIntegrand/w²`) after multiplying by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand_k (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) {i : ℕ}
    (hi : i ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g i hi hz hθ
  have hw : 0 < (Work.Spaces.w z) ^ 2 := pow_pos (Work.FTS.H2.w_pos hz) 2
  rw [le_div_iff₀ hw] at h1
  exact h1

/-! ## Cauchy–Schwarz in `θ` at an arbitrary order `k` -/

/-- **Cauchy–Schwarz in `θ` for the angular moment, at an arbitrary order `k`.**  For a datum
which is `C^∞` on the open quadrant and lies in `ℋ^k`, and for `j ≤ k` and `z > 0`,

  `(Qang g j z)² ≤ (∫_θ Kθ(θ)² dθ)·∫_θ (D_z^j g z θ)² dθ`,

with the `α`-independent constant `∫_θ Kθ²`.

This is `Work.FTS.H2.Qang_sq_leQ` / `Work.FTS.OpenPkg.QangOpen.Qang_sq_leQ_open` with the fixed
order `4` replaced by `k`: the `θ`-integrals are taken over the open interval `(0,π/2)` (the
endpoints are null), where both factors are continuous and square-integrable, and the standard
`L²`-Cauchy–Schwarz (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`) applies. -/
private theorem Qang_sq_le_k (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) {k : ℕ} (hmem : Work.Spaces.HkMem α k g)
    (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  have hIoo : (Set.Icc (0 : ℝ) (π / 2)) =ᵐ[volume] (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hQeq : Work.Elliptic.Qang g j z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.setIntegral_congr_set hIoo
  have hKeq : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  -- the `θ`-slice of `D_z^j g` at `z > 0` is continuous on `(0,π/2)`
  have hAcont : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hO.DzIter j).curry_θ hz).continuousOn
  have hKcont : Continuous (fun θ => Work.Elliptic.Ktheta θ) := by
    unfold Work.Elliptic.Ktheta
    fun_prop
  have hK2int : IntegrableOn (fun θ => Work.Elliptic.Ktheta θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hKcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- integrability of `HkIntegrand α k g z ·`, transported from `hmem` to the open interval
  have hHkint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    change Integrable (fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    simpa only [Work.Spaces.Iθ, IntegrableOn] using hmem.1 z (le_of_lt hz)
  have hAesm : AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter j g z θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using (hAcont.aestronglyMeasurable measurableSet_Ioo).norm
  have hA2int : IntegrableOn (fun θ => |Work.Spaces.DzIter j g z θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine hHkint.mono' (hAesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    exact sq_DzIter_le_HkIntegrand_k α k g hj hz hθ.1 hθ.2
  have hKesm : AEStronglyMeasurable (fun θ => |Work.Elliptic.Ktheta θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using hKcont.aestronglyMeasurable.norm
  have hKabs : IntegrableOn (fun θ => |Work.Elliptic.Ktheta θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [sq_abs] using hK2int
  have hKmem : MemLp (fun θ => |Work.Elliptic.Ktheta θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hKesm).mpr hKabs
  have hAmem : MemLp (fun θ => |Work.Spaces.DzIter j g z θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    (p := 2) (q := 2) (f := fun θ => |Work.Elliptic.Ktheta θ|)
    (g := fun θ => |Work.Spaces.DzIter j g z θ|)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun θ => abs_nonneg _)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hKmem hAmem
  have hnQ : |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
    simpa only [Real.norm_eq_abs, abs_mul] using h
  have hKIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Elliptic.Ktheta θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hAIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hK0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hA0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
    calc (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
        = |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
            Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
            * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                (Work.Spaces.DzIter j g z θ) ^ 2)) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          calc |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
              ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                  |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := hnQ
            _ ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Elliptic.Ktheta θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
                * (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
            _ = Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
                * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    (Work.Spaces.DzIter j g z θ) ^ 2) := by
                rw [hKIsq, hAIsq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      _ = (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hA0]
  rw [hQeq, hKeq, hAeq]
  exact hmain

/-! ## A.e. strong measurability of the angular moment -/

/-- `z ↦ Qang g i z` is a.e. strongly measurable on `Iz` (no integrability needed): it is the
`θ`-integral of the jointly continuous `(z,θ) ↦ Kθ(θ)·D_z^i g z θ` on the open quadrant
(`AEStronglyMeasurable.integral_prod_right'`). -/
private theorem aesm_Qang (i : ℕ) {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) :
    AEStronglyMeasurable (fun z : ℝ => Work.Elliptic.Qang g i z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h := (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
    (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hO i)).integral_prod_right'
  simpa only [Work.Elliptic.Qang] using h


/-! ## The full level-six bound (`i ≤ 6`) -/

/-- **The level-six weighted `L²`-bound for the angular moment `Qang`, at every order
`i ≤ 6`.**  For a datum which is `C^∞` on the open quadrant and lies in `ℋ⁶`,
`z ↦ (Qang g i z)² w(z)²` is integrable on `Iz` and its integral is at most
`(∫_θ Kθ²)·|g|²_{ℋ⁶}`.

This is `Work.FTS.StrongPersist.QangSq6` with the order bound `5 ↦ 6`; the proof is unchanged
because both the pointwise domination of a pure `D_z`-iterate by `HkIntegrand` and the
`θ`-Cauchy–Schwarz are already proved for an arbitrary order `k ≤ 6`. -/
theorem QangSq6Full {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ i : ℕ, i ≤ 6 →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g := by
  intro i hi
  have hi6 : i ≤ 6 := hi
  have hK0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  -- ## the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
    intro z hz
    have hCS := Qang_sq_le_k α g hO hmem i hi6 hz
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand_k α 6 g hi6 hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) :=
          mul_le_mul_of_nonneg_left hslice hK0
  -- ## the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- ## a.e. strong measurability
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ := aesm_Qang i hO
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- ## the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)

end Work.FTS.StrongPersist
end
end
