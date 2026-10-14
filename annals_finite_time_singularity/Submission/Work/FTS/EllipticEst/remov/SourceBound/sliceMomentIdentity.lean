import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HR2.HkMemU =====
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

/-- **Pointwise normalisation of the level-`0` integrand** (copy of
`Work.FTS.EllipticEst.Honest.hkIntegrand_eq_w_sq`). -/
theorem hr2_hkIntegrand_eq_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α g z θ,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- `σ θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
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
private theorem hkIntegrand_zero_thEta (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
  hr2_hkIntegrand_eq_w_sq α g hθ

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


/-! ## The main body -/



end

end Work.FTS.EllipticEst.H2W.Ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeEnergyWAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AngAWeak/aeEnergyWAux` — the auxiliary slice/integrability facts for `aeEnergyW`

This module collects the pieces of the plain-`w²` energy estimate in the almost-everywhere
class `AeData` that the assembly in `AngAWeak/aeEnergyW` consumes:

* the `θ`-slice energies `sgU`, `sgY`, `sgP`, `sgM`, `sgI` of a datum;
* the a.e. slice facts (the constrained slice gap `9∫u² ≤ ∫(∂_θu)²` and the angular self-form
  `∫(∂_θu)² ≤ ∫(Lzero u)·u + 6∫u²`), assembled from the proved `aeGapSelfForm`;
* the transfer from `HkMem α 0 f` to the plain `w²`-integrability of the slice squares
  (`integrableOn_wSq_sliceSq`), together with the a.e. strong measurability of the
  slice-integral functions (`aesm_wSq_sliceSq`);
* the pointwise `AM–GM` bounds `|∫_θ G u| ≤ (1/2)(∫_θ G²σ + ∫_θ u²)` and
  `|∫_θ (Lzero u)·u| ≤ dBnd` where `dBnd` is the explicitly integrable dominating function;
* the abstract monotone/Fatou limit lemma `integral_le_of_cutoff` used to pass from the
  truncated estimate to the global one.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The open quadrant -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Qd {z θ : ℝ} : (z, θ) ∈ Qd ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

/-- The radial weight is continuous on the open quadrant. -/
theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have h1 : Continuous fun p : ℝ × ℝ => (1 : ℝ) + p.1 := continuous_const.add continuous_fst
  have h2 : Continuous fun p : ℝ × ℝ => p.1 ^ 2 := continuous_fst.pow 2
  have hne : ∀ p ∈ Qd, p.1 ^ 2 ≠ 0 := by
    intro p hp
    have hpos : 0 < p.1 := (mem_Qd.mp hp).1
    positivity
  have hmain : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2) Qd :=
    ContinuousOn.div (h1.pow 2).continuousOn h2.continuousOn hne
  simpa [Work.Spaces.w] using hmain

/-! ## The slice energies of a datum -/

/-- `sgU u z = ∫_θ (u z θ)²`. -/
def sgU (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2

/-- `sgY u z = ∫_θ (∂_θu z θ)²`. -/
def sgY (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2

/-- `sgP u z = ∫_θ (∂_zu z θ)²`. -/
def sgP (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2

/-- `sgM u z = ∫_θ (Lzero u z θ) · u z θ`. -/
def sgM (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ

/-- `sgI G u z = ∫_θ G z θ · u z θ`. -/
def sgI (G u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, G z θ * u z θ

/-! ## The a.e. slice facts -/

/-- The a.e. left-endpoint limit, from continuity on the closed angular interval. -/
theorem ae_tendsto_left_of_continuousOn {u : ℝ → ℝ → ℝ} (hdir : ∀ z : ℝ, u z 0 = 0)
    (hcont : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  filter_upwards [hcont] with z hz
  have h1 : ContinuousWithinAt (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)) 0 :=
    hz 0 ⟨le_rfl, le_of_lt hpi⟩
  have h2 : Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2)))
      (nhds (u z 0)) := h1
  rw [hdir z] at h2
  refine h2.mono_left ?_
  rw [← nhdsWithin_Ioo_eq_nhdsGT hpi]
  exact nhdsWithin_mono 0 (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

/-- The level-`0` `HkIntegrand` collapses to the single square `g² w² σ` on `Iθ`.  (A local copy
of the lemma of the same name in `AngAWeak/aeUHkAux`, kept here so that the development does not
depend on `AngAWeak/aeTruncIdent`.) -/
theorem HkIntegrand_zero_eq_w (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-- `(∂_θu z ·)²` is integrable on the angular interval for every `z > 0`.  (A local copy of the
lemma of the same name in `AngAWeak/aeUHkAux`.) -/
theorem integrableOn_pth_sq_of_AeData (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  have hslice : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact ((h.smooth 2).comp (by fun_prop) hmap)
  have hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have h1 := h.memAng2.1 z hzI
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      h1.congr_fun (fun θ hθ => HkIntegrand_zero_eq_w α (Work.Spaces.pthIter 2 u) z hθ)
        measurableSet_Icc
    have hw' : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
    have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
    refine h3.congr (Filter.Eventually.of_forall fun θ => ?_)
    show ((Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
        = (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ
    have hpth2 : Work.Spaces.pthIter 2 u z θ
        = deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [hpth2]
    rw [show (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ * ((Work.Spaces.w z) ^ 2)⁻¹
        = (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ
          * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) from by ring,
      mul_inv_cancel₀ (pow_ne_zero 2 hw'), mul_one]
  obtain ⟨C, hC0, hC⟩ := Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hslice hint
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro hh
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hh
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne hh.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne hh.2 (fun hc => hx (Or.inr hc))⟩
    · intro hh
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at hh
      exact ⟨le_of_lt hh.1, le_of_lt hh.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  rw [MeasureTheory.IntegrableOn, hms]
  refine MeasureTheory.IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    ((measurable_deriv (fun θ' : ℝ => u z θ')).pow_const 2).aestronglyMeasurable
    (C ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hb := (hC θ hθ).2
  rw [Real.norm_of_nonneg (sq_nonneg _), show Work.Spaces.pth u z θ
    = deriv (fun θ' : ℝ => u z θ') θ from rfl, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hb 2

/-- **The two a.e. slice facts** (the constrained slice gap and the angular self-form), proved
here from the `H2W.AeProof` slice lemmas without depending on `AngAWeak/aeTruncIdent`. -/
theorem ae_gap_self {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hcont : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      9 * sgU u z ≤ sgY u z ∧ sgY u z ≤ sgM u z + 6 * sgU u z := by
  have hL := ae_tendsto_left_of_continuousOn (Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero h) hcont
  have hC := Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice h hL
  have hint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => integrableOn_pth_sq_of_AeData α u G h z hz)
  have hgap := Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices α u G h hC hint
  filter_upwards [hgap, hC, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hgapz hCz hzI
  have hz : 0 < z := hzI
  refine ⟨hgapz, ?_⟩
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth n)
  have hint2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h0 := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma
      (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 h) hz
    refine h0.congr_fun (fun θ _ => ?_) measurableSet_Icc
    have hpth2 : Work.Spaces.pthIter 2 u z θ
        = deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    show (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
    rw [hpth2]
  have heq := Work.FTS.EllipticEst.H2W.AeProof.AeSliceSelfForm u z hsm hCz
    (Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero h z)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.dirPi h z) hint2
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u z θ / Real.cos θ) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ)
        + 6 * ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2
  rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => u z θ') θ) ^ 2 from by
    simp only [Work.Spaces.pth]]
  linarith [heq, hnn]

/-! ## From `HkMem` to the plain `w²`-integrability of the slices -/

/-- **Slice form.**  For `z ∈ Iz` the plain slice square of `f` against `w` is integrable and
dominated by the level-`0` `HkIntegrand`.  The auxiliary function
`θ ↦ HkIntegrand α 0 f z θ · sin(2θ)^η` agrees with `(f z θ · w z)²` on the *open* angular
interval and is integrable because `sin(2θ)^η ≤ 1` and `HkIntegrand ≥ 0`. -/
theorem integrableOn_slice_sq_mul_w_sq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ := by
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 f z θ) Work.Spaces.Iθ := hmem.1 z hz
  have hHnn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 0 f z θ := fun θ => by
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]; positivity
  have hsin : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta) := by
    have h : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.measurable_sin.comp (measurable_const.mul measurable_id)
    exact h.pow_const Work.Spaces.eta
  have hsinn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsin_le : ∀ θ ∈ Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 := by
    intro θ hθ
    exact Real.rpow_le_one (hsinn θ hθ) (Real.sin_le_one _)
      (by rw [Work.Spaces.eta]; norm_num)
  have hsin_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * θ)) ^ Work.Spaces.eta := fun θ hθ =>
    Real.rpow_nonneg (hsinn θ hθ) _
  -- integrability of the auxiliary function
  have hgint : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 f z θ * (Real.sin (2 * θ)) ^ Work.Spaces.eta)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' h1 (h1.1.mul hsin.aestronglyMeasurable) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have hb : |Work.Spaces.HkIntegrand α 0 f z θ * (Real.sin (2 * θ)) ^ Work.Spaces.eta|
        ≤ Work.Spaces.HkIntegrand α 0 f z θ := by
      rw [abs_of_nonneg (mul_nonneg (hHnn θ) (hsin_nn θ hθ))]
      exact mul_le_of_le_one_right (hHnn θ) (hsin_le θ hθ)
    simpa only [Real.norm_eq_abs] using hb
  -- the a.e. identification
  have hcongr : (fun θ => Work.Spaces.HkIntegrand α 0 f z θ * (Real.sin (2 * θ)) ^ Work.Spaces.eta)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (f z θ * Work.Spaces.w z) ^ 2) := by
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [Work.FTS.EllipticEst.AngAWeak.HkIntegrand_zero_eq_w α f z hθI,
      Work.FTS.EllipticEst.sEta]
    have hpow : (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        = 1 := by
      rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
    calc (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ Work.Spaces.eta) := by ring
      _ = (f z θ * Work.Spaces.w z) ^ 2 := by rw [hpow]; ring
  refine ⟨hgint.congr_fun_ae hcongr, ?_⟩
  rw [← MeasureTheory.integral_congr_ae hcongr]
  exact MeasureTheory.integral_mono_ae hgint h1
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_le_of_le_one_right (hHnn θ) (hsin_le θ hθ)))

/-- **A.e. strong measurability of the slice-integral function.**  If `p ↦ f p.1 p.2 · w p.1` is
continuous on the open quadrant, then `z ↦ ∫_θ (f z θ · w z)²` is a.e. strongly measurable for
the restriction of Lebesgue measure to `Iz` (joint a.e. strong measurability of the integrand by
`aesm_of_continuousOn_Qd`, then the inner integral). -/
theorem aesm_wSq_sliceSq {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.w p.1) Qd) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2) Qd := hcont.pow 2
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ h2
  exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) haesm

/-- **`HkMem` plus a.e. strong measurability of the slice-integral gives the plain `w²`-integral
bound**: `∫_z w z² ∫_θ (f z θ)² ≤ HkSq α 0 f`. -/
theorem integrableOn_wSq_sliceSq {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 f)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2))
        ≤ Work.Spaces.HkSq α 0 f := by
  have hH : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) Work.Spaces.Iz :=
    hmem.2
  have hagree : ∀ z : ℝ,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2 := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => by ring)
  have hout : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hH haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
    have h2 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ :=
      MeasureTheory.integral_nonneg fun θ => by
        rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]; positivity
    have h3 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2 :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hb : |∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2|
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ := by
      rw [abs_of_nonneg h3]
      exact (integrableOn_slice_sq_mul_w_sq hmem hz).2
    simpa only [Real.norm_eq_abs] using hb
  refine ⟨hout.congr_fun_ae (Filter.Eventually.of_forall fun z => (hagree z).symm), ?_⟩
  have hmain : (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => hagree z)
  rw [hmain, Work.Spaces.HkSq]
  exact MeasureTheory.integral_mono_ae hout hH
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => (integrableOn_slice_sq_mul_w_sq hmem hz).2))

/-! ## The `θ`-partial of a function smooth on an open set (finite order) -/

/-- `∂_θ` lowers the order of differentiability by one: if `Function.uncurry G` is `C^{n+1}` on
the open set `U`, then `Function.uncurry (∂_θ G)` is `C^n` there.  (The `θ`-analogue of
`Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ`.) -/
theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ} (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G) U) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth G)) U := by
  have hfd : ContDiffOn ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry G)) U :=
    h.fderiv_of_isOpen hU (by simp)
  have hcomp : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (0, 1)) U :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pth_eq_fderiv
    ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))

/-! ## The `σ`-weighted slice integrability -/

/-- `σ`-weighted slice integrability, from `HkMem α 0 f`. -/
theorem integrableOn_slice_sq_mul_sEta {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 f)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (hz0 : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have h1 := hmem.1 z hz
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ =>
      Work.FTS.EllipticEst.AngAWeak.HkIntegrand_zero_eq_w α f z hθ) measurableSet_Icc
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    rw [Work.Spaces.w]
    positivity
  have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
  refine h3.congr (Filter.Eventually.of_forall fun θ => ?_)
  show ((f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      * ((Work.Spaces.w z) ^ 2)⁻¹ = (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  rw [show ((f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * ((Work.Spaces.w z) ^ 2)⁻¹
      = (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) from by ring,
    mul_inv_cancel₀ hw, mul_one]

/-- `(w z)²·∫_θ f²σ` is the slice integral of the `Hk`-integrand. -/
theorem wSq_sliceSq_sEta_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Work.FTS.EllipticEst.AngAWeak.HkIntegrand_zero_eq_w α f z hθ]
  ring

/-- **The `σ`-weighted instance of the plain-`w²` estimate**: for an honest `f`, the slice
integral `z ↦ (w z)² ∫_θ f²σ` is integrable with integral exactly `HkSq α 0 f`. -/
theorem integrableOn_wSq_sliceSq_sEta {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        = Work.Spaces.HkSq α 0 f :=
  ⟨hmem.2.congr_fun (fun z _ => (wSq_sliceSq_sEta_eq α f z).symm) measurableSet_Ici,
    by
      have h1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ici
          (fun z _ => wSq_sliceSq_sEta_eq α f z)
      rw [h1, Work.Spaces.HkSq]⟩

/-! ## Instance: `u` -/

/-- **The plain `w²`-instance of the angular mass of `u`.** -/
theorem integrableOn_wSq_sgU {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hmem : Work.Spaces.HkMem α 0 u) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sgU u z) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * sgU u z)
        ≤ Work.Spaces.HkSq α 0 u := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2 * Work.Spaces.w p.1) Qd :=
    ((h.smooth 0).continuousOn_zero).mul continuousOn_w_Qd
  have hgen := integrableOn_wSq_sliceSq hmem (aesm_wSq_sliceSq hcont)
  simpa only [sgU] using hgen

/-! ## Instance: `grad u = z ∂_zu` -/

/-- **The plain `w²z²`-instance of the radial first-order energy `∫_θ (∂_zu)²`.** -/
theorem integrableOn_wSq_zsq_sgP {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hmem : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ)) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * z ^ 2 * sgP u z) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * z ^ 2 * sgP u z)
        ≤ Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ) := by
  have hpz : ContDiffOn ℝ (0 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz u)) Qd :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 0)
      (by simpa only [Qd] using h.smooth 1)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (p.1 * Work.Spaces.pz u p.1 p.2) * Work.Spaces.w p.1) Qd :=
    (continuous_fst.continuousOn.mul hpz.continuousOn_zero).mul continuousOn_w_Qd
  have hgen := integrableOn_wSq_sliceSq hmem (aesm_wSq_sliceSq hcont)
  have heq : ∀ z : ℝ,
      (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2 * z ^ 2 * sgP u z := by
    intro z
    have h1 : (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
        = z ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun θ => by ring)
    simp only [sgP]
    rw [h1]
    ring
  refine ⟨hgen.1.congr_fun (fun z _ => heq z) measurableSet_Ici, ?_⟩
  have h2 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * z ^ 2 * sgP u z)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => (heq z).symm)
  rw [h2]
  exact hgen.2

/-! ## A.e. strong measurability of the angular energy -/

/-- The a.e. strong measurability of `z ↦ (w z)² sgY u z`, from the joint continuity of
`p ↦ ∂_θu p.1 p.2 · w p.1` on the open quadrant. -/
theorem aesm_wSq_sgY {u : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth u p.1 p.2 * Work.Spaces.w p.1) Qd) :
    MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 * sgY u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hgen := aesm_wSq_sliceSq (f := Work.Spaces.pth u) hcont
  refine hgen.congr (Filter.Eventually.of_forall fun z => ?_)
  show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      = (Work.Spaces.w z) ^ 2 * sgY u z
  simp only [sgY]
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun θ => by ring)

/-! ## The dominating function `dBnd` for the angular `Lzero`-pairing -/

/-- The `σ`-weighted `AM–GM` majorant of `|∫_θ (Lzero u)·u|`:
`dBnd z = ½(∫_θ G²σ + sgU) + (α²/2)(∫_θ (z²∂_zzu)²σ + sgU) + (α(5+α)/2)(∫_θ (z∂_zu)²σ + sgU)`. -/
def dBnd (α : ℝ) (u G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + sgU u z)
    + (α ^ 2 / 2) * ((∫ θ in Work.Spaces.Iθ,
        (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + sgU u z)
    + (α * (5 + α) / 2) * ((∫ θ in Work.Spaces.Iθ,
        (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + sgU u z)

/-- **`dBnd` is integrable against `w²`.**  Each of its three `σ`-weighted slice integrals is one
of the `ℋ⁰`-integrands of the hypotheses, and `sgU` is handled by `integrableOn_wSq_sgU`. -/
theorem integrableOn_wSq_dBnd {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hmu : Work.Spaces.HkMem α 0 u)
    (hmg : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ)) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * dBnd α u G z) Work.Spaces.Iz := by
  obtain ⟨hG1, -⟩ := integrableOn_wSq_sliceSq_sEta (α := α) (f := G) h.memG
  obtain ⟨hr1, -⟩ := integrableOn_wSq_sliceSq_sEta (α := α)
    (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) h.memRad2
  obtain ⟨hg1, -⟩ := integrableOn_wSq_sliceSq_sEta (α := α)
    (f := fun z θ => z * Work.Spaces.pz u z θ) hmg
  obtain ⟨hu1, -⟩ := integrableOn_wSq_sgU h hmu
  have hsum : (fun z => (Work.Spaces.w z) ^ 2 * dBnd α u G z)
      = fun z => ((1 / 2) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + (1 / 2) * ((Work.Spaces.w z) ^ 2 * sgU u z))
        + ((α ^ 2 / 2) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + (α ^ 2 / 2) * ((Work.Spaces.w z) ^ 2 * sgU u z))
        + ((α * (5 + α) / 2) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + (α * (5 + α) / 2) * ((Work.Spaces.w z) ^ 2 * sgU u z)) := by
    funext z
    simp only [dBnd]
    ring
  rw [hsum]
  exact (((hG1.const_mul (1 / 2)).add (hu1.const_mul (1 / 2))).add
    ((hr1.const_mul (α ^ 2 / 2)).add (hu1.const_mul (α ^ 2 / 2)))).add
      ((hg1.const_mul (α * (5 + α) / 2)).add (hu1.const_mul (α * (5 + α) / 2)))

/-! ## Measurability and continuity of the angular slices -/

/-- A function continuous on the open angular interval is a.e. strongly measurable for the
restriction of Lebesgue measure to the closed interval `Iθ`. -/
theorem aestronglyMeasurable_of_continuousOn_Ioo {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [Work.Spaces.Iθ,
    show (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)))
        = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) from
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
          (a := 0) (b := Real.pi / 2)).symm]
  exact hg.aestronglyMeasurable measurableSet_Ioo

/-- `θ ↦ tan θ` is `C^1` on the open quadrant. -/
theorem contDiffOn_tan_Qd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.tan p.2) Qd := by
  have hsin : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.sin p.2) Qd := by fun_prop
  have hcos : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.cos p.2) Qd := by fun_prop
  have hne : ∀ p ∈ Qd, Real.cos p.2 ≠ 0 := by
    intro p hp
    have h2 := (mem_Qd.mp hp).2
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h2.1, Real.pi_pos], h2.2⟩)
  have h := hsin.div hcos hne
  change ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) Qd at h
  simpa only [Real.tan_eq_sin_div_cos] using h

/-- `p ↦ tan p.2 · u p.1 p.2` is `C^1` on the open quadrant. -/
theorem contDiffOn_uncurry_tanMul {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Qd) :
    ContDiffOn ℝ 1 (Function.uncurry (fun z θ => Real.tan θ * u z θ)) Qd := by
  have hu : ContDiffOn ℝ 1 (Function.uncurry u) Qd := by
    simpa only [Qd, Nat.cast_one] using hsm 1
  exact contDiffOn_tan_Qd.mul hu

/-- `pth Iter 2 u` is jointly continuous on the open quadrant. -/
theorem continuousOn_uncurry_pthIter_two {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Qd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pthIter 2 u)) Qd := by
  have h1 : ContDiffOn ℝ (1 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth u)) Qd :=
    contDiffOn_uncurry_pth_succ isOpen_Qd (n := 1) (by simpa only [Qd] using hsm 2)
  have h2 : ContDiffOn ℝ (0 : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth u))) Qd :=
    contDiffOn_uncurry_pth_succ isOpen_Qd (n := 0) h1
  simpa [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2.continuousOn_zero

/-- `pzIter 2 u` is jointly continuous on the open quadrant. -/
theorem continuousOn_uncurry_pzIter_two {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Qd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 u)) Qd := by
  have h1 : ContDiffOn ℝ (1 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz u)) Qd :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 1)
      (by simpa only [Qd] using hsm 2)
  have h2 : ContDiffOn ℝ (0 : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz u))) Qd :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 0) h1
  simpa [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h2.continuousOn_zero

/-- `Lzero u` is jointly continuous on the open quadrant. -/
theorem continuousOn_uncurry_Lzero {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Qd) :
    ContinuousOn (Function.uncurry (Work.Elliptic.Lzero u)) Qd := by
  have hpth2 := continuousOn_uncurry_pthIter_two hsm
  have htan := contDiffOn_uncurry_tanMul hsm
  have hpth : ContDiffOn ℝ (0 : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pth (fun z θ => Real.tan θ * u z θ))) Qd :=
    contDiffOn_uncurry_pth_succ isOpen_Qd (n := 0) htan
  have hu : ContinuousOn (Function.uncurry u) Qd := (hsm 0).continuousOn_zero
  have hcongr : ∀ p ∈ Qd, Work.Elliptic.Lzero u p.1 p.2
      = -(Work.Spaces.pthIter 2 u p.1 p.2)
        + Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) p.1 p.2 - 6 * u p.1 p.2 := by
    intro p hp
    rfl
  have hcomb : ContinuousOn (fun p : ℝ × ℝ => -(Work.Spaces.pthIter 2 u p.1 p.2)
      + Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) p.1 p.2 - 6 * u p.1 p.2) Qd :=
    ((hpth2.neg).add hpth.continuousOn_zero).sub (hu.const_mul 6)
  exact hcomb.congr hcongr

/-- The `θ`-slice of `Lzero u` is continuous on the open angular interval, for `z > 0`. -/
theorem continuousOn_slice_Lzero {u : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Qd) :
    ContinuousOn (fun θ => Work.Elliptic.Lzero u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (continuousOn_uncurry_Lzero hsm).comp (continuous_const.prodMk continuous_id).continuousOn
    (fun θ hθ => mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)

/-- A.e. strong measurability of the `θ`-slice of `Lzero u`. -/
theorem aesm_slice_Lzero {u : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Qd) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Elliptic.Lzero u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  aestronglyMeasurable_of_continuousOn_Ioo (continuousOn_slice_Lzero hz hsm)

/-- **A.e. strong measurability of the `θ`-slice of the equation's source `G`.**  On the open
angular interval `G z ·` agrees with `bslOp α u z ·`, whose three summands are the slices of
`∂_z²u`, `∂_zu` (continuous on the quadrant) and of `Lzero u`. -/
theorem aesm_slice_G {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => G z θ) (MeasureTheory.volume.restrict
      Work.Spaces.Iθ) := by
  -- the `bslOp` expression is a.e. strongly measurable
  have hpz2 : ContinuousOn (fun θ => Work.Spaces.pzIter 2 u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (continuousOn_uncurry_pzIter_two h.smooth).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)
  have hpz1 : ContinuousOn (fun θ => Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hc : ContinuousOn (Function.uncurry (Work.Spaces.pz u)) Qd :=
      (Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 0)
        (by simpa only [Qd] using h.smooth 1)).continuousOn_zero
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)
  have hL := aesm_slice_Lzero hz h.smooth
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ
        - (α * (5 + α) * z) * Work.Spaces.pz u z θ + Work.Elliptic.Lzero u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((aestronglyMeasurable_of_continuousOn_Ioo hpz2).const_mul _).sub
      ((aestronglyMeasurable_of_continuousOn_Ioo hpz1).const_mul _)).add hL
  refine haesm.congr ?_
  filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
  have hb := h.eq z hz θ hθ.1 hθ.2
  rw [Work.Elliptic.bslOp] at hb
  linarith

/-! ## The `AM–GM` pointwise bounds -/

/-- Dividing out a nonzero constant factor from a square slice-integral. -/
theorem integrableOn_slice_sq_of_mul_const {g : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2 * c) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ := by
  have h2 := h.mul_const c⁻¹
  refine h2.congr (Filter.Eventually.of_forall fun θ => ?_)
  show g θ ^ 2 * c * c⁻¹ = g θ ^ 2
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]

/-- The plain `θ`-slice square of `u` is integrable, for every `z > 0`. -/
theorem integrableOn_slice_sgU {α : ℝ} {u : ℝ → ℝ → ℝ} (hmu : Work.Spaces.HkMem α 0 u)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    rw [Work.Spaces.w]
    positivity
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (u z θ) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iθ :=
    (integrableOn_slice_sq_mul_w_sq hmu (le_of_lt hz)).1.congr_fun
      (fun θ _ => by ring) measurableSet_Icc
  exact integrableOn_slice_sq_of_mul_const hw h1

/-- The elementary `AM–GM` inequality `2|X||Y| ≤ X² + Y²`. -/
theorem two_mul_abs_mul_abs_le (X Y : ℝ) : 2 * |X| * |Y| ≤ X ^ 2 + Y ^ 2 := by
  nlinarith [sq_nonneg (|X| - |Y|), sq_abs X, sq_abs Y]

/-- **The pointwise `AM–GM` bound for the source pairing**: `|G·u| ≤ ½(G²σ + u²)`. -/
theorem abs_sgI_pointwise {u G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |G z θ * u z θ|
      ≤ (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2) := by
  have hσ : 1 ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.Honest.one_le_sEta_of_mem_Ioo hθ
  have h1 := two_mul_abs_mul_abs_le (G z θ) (u z θ)
  have h2 : (G z θ) ^ 2 ≤ (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    le_mul_of_one_le_right (sq_nonneg _) hσ
  rw [abs_mul]
  linarith

/-- **The pointwise `AM–GM` bound for the `Lzero`-pairing.**  For `z > 0` and a.e. `θ`,
`|(Lzero u)·u|` is dominated by the integrand whose `θ`-integral is `dBnd`. -/
theorem abs_sgM_pointwise {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Elliptic.Lzero u z θ * u z θ|
        ≤ (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
          + (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
          + (α * (5 + α) / 2) * ((z * Work.Spaces.pz u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2) := by
  filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
  have hσ : 1 ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.Honest.one_le_sEta_of_mem_Ioo hθ
  have hL : Work.Elliptic.Lzero u z θ
      = G z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ := by
    have hb := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp] at hb
    linarith
  have b1 : 2 * |G z θ| * |u z θ| ≤ (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2 := by
    have h2 := two_mul_abs_mul_abs_le (G z θ) (u z θ)
    have h3 : (G z θ) ^ 2 ≤ (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      le_mul_of_one_le_right (sq_nonneg _) hσ
    linarith
  have b2 : 2 * |(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ| * |u z θ|
      ≤ (α ^ 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + (α ^ 2) * (u z θ) ^ 2 := by
    have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
    have hb := two_mul_abs_mul_abs_le (z ^ 2 * Work.Spaces.pzIter 2 u z θ) (u z θ)
    have hb' : 2 * (z ^ 2 * |Work.Spaces.pzIter 2 u z θ|) * |u z θ|
        ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2 := by
      have h2 : |z ^ 2 * Work.Spaces.pzIter 2 u z θ| = z ^ 2 * |Work.Spaces.pzIter 2 u z θ| := by
        rw [abs_mul, abs_of_nonneg hz2]
      rw [← h2]
      exact hb
    have h3 : (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≥ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) hσ
    have h4 : |(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ|
        = α ^ 2 * (z ^ 2 * |Work.Spaces.pzIter 2 u z θ|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hz2, abs_of_nonneg hα2]
      ring
    rw [h4]
    nlinarith [hb', h3, hα2]
  have b3 : 2 * |(α * (5 + α) * z) * Work.Spaces.pz u z θ| * |u z θ|
      ≤ (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + (α * (5 + α)) * (u z θ) ^ 2 := by
    have hα : (0 : ℝ) ≤ α * (5 + α) := by
      have hα0 : 0 < α := h.hα
      nlinarith
    have hz2 : (0 : ℝ) ≤ z := le_of_lt hz
    have hb := two_mul_abs_mul_abs_le (z * Work.Spaces.pz u z θ) (u z θ)
    have hb' : 2 * (z * |Work.Spaces.pz u z θ|) * |u z θ|
        ≤ (z * Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2 := by
      have h2 : |z * Work.Spaces.pz u z θ| = z * |Work.Spaces.pz u z θ| := by
        rw [abs_mul, abs_of_nonneg hz2]
      rw [← h2]
      exact hb
    have h3 : (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≥ (z * Work.Spaces.pz u z θ) ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) hσ
    have h4 : |(α * (5 + α) * z) * Work.Spaces.pz u z θ|
        = (α * (5 + α)) * (z * |Work.Spaces.pz u z θ|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hz2, abs_of_nonneg hα]
      ring
    rw [h4]
    nlinarith [hb', h3, hα]
  have hbsum : |G z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ|
      ≤ |G z θ| + |(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ|
        + |(α * (5 + α) * z) * Work.Spaces.pz u z θ| := by
    have h1 : |G z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ|
        ≤ |G z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ|
          + |(α * (5 + α) * z) * Work.Spaces.pz u z θ| := abs_add_le _ _
    have h2 : |G z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ|
        ≤ |G z θ| + |(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ| := abs_add_le _ _
    linarith
  have hstep : (|G z θ| + |(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ|
        + |(α * (5 + α) * z) * Work.Spaces.pz u z θ|) * |u z θ|
      ≤ (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
        + (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
        + (α * (5 + α) / 2) * ((z * Work.Spaces.pz u z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2) := by
    linarith [b1, b2, b3]
  rw [hL, abs_mul]
  linarith [mul_le_mul_of_nonneg_right hbsum (abs_nonneg (u z θ)), hstep,
    abs_mul (G z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ
      + (α * (5 + α) * z) * Work.Spaces.pz u z θ) (u z θ)]


/-! ## The integral bounds for the two pairings -/

/-- **The integral `AM–GM` bound for the `Lzero`-pairing**: `|sgM u z| ≤ dBnd α u G z`. -/
theorem abs_sgM_le {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hmu : Work.Spaces.HkMem α 0 u)
    (hmg : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    {z : ℝ} (hz : 0 < z) :
    |sgM u z| ≤ dBnd α u G z := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hIntG : MeasureTheory.IntegrableOn
      (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    integrableOn_slice_sq_mul_sEta h.memG hzI hz
  have hIntu : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_slice_sgU hmu hz
  have hIntA : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    integrableOn_slice_sq_mul_sEta h.memRad2 hzI hz
  have hIntB : MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    integrableOn_slice_sq_mul_sEta hmg hzI hz
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
      Work.Spaces.Iθ := (hIntG.add hIntu).const_mul (1 / 2)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)) Work.Spaces.Iθ :=
    (hIntA.add hIntu).const_mul (α ^ 2 / 2)
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => (α * (5 + α) / 2) * ((z * Work.Spaces.pz u z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)) Work.Spaces.Iθ :=
    (hIntB.add hIntu).const_mul (α * (5 + α) / 2)
  have hR : MeasureTheory.IntegrableOn
      (fun θ => (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
        + (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
        + (α * (5 + α) / 2) * ((z * Work.Spaces.pz u z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)) Work.Spaces.Iθ :=
    (h1.add h2).add h3
  have hpt := abs_sgM_pointwise h hz
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => |Work.Elliptic.Lzero u z θ * u z θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hu : MeasureTheory.AEStronglyMeasurable (fun θ => u z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine aestronglyMeasurable_of_continuousOn_Ioo ?_
      exact ((h.smooth 0).continuousOn_zero).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using
      ((aesm_slice_Lzero hz h.smooth).mul hu).norm
  have hintL : MeasureTheory.IntegrableOn
      (fun θ => |Work.Elliptic.Lzero u z θ * u z θ|) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hR haesm ?_
    filter_upwards [hpt] with θ hθ
    simpa only [Real.norm_eq_abs, abs_abs, Pi.add_apply] using hθ
  have e1 : (∫ θ in Work.Spaces.Iθ,
        (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
      = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + sgU u z) := by
    rw [MeasureTheory.integral_const_mul]
    have hh : (∫ θ in Work.Spaces.Iθ,
          (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 := MeasureTheory.integral_add hIntG hIntu
    rw [hh]
    simp only [sgU]
  have e2 : (∫ θ in Work.Spaces.Iθ,
        (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
      = (α ^ 2 / 2) * ((∫ θ in Work.Spaces.Iθ,
            (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + sgU u z) := by
    rw [MeasureTheory.integral_const_mul]
    have hh : (∫ θ in Work.Spaces.Iθ,
          (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
            + (u z θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 := MeasureTheory.integral_add hIntA hIntu
    rw [hh]
    simp only [sgU]
  have e3 : (∫ θ in Work.Spaces.Iθ,
        (α * (5 + α) / 2) * ((z * Work.Spaces.pz u z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
      = (α * (5 + α) / 2) * ((∫ θ in Work.Spaces.Iθ,
            (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + sgU u z) := by
    rw [MeasureTheory.integral_const_mul]
    have hh : (∫ θ in Work.Spaces.Iθ,
          (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 := MeasureTheory.integral_add hIntB hIntu
    rw [hh]
    simp only [sgU]
  have hdB : (∫ θ in Work.Spaces.Iθ,
        (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
        + (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
        + (α * (5 + α) / 2) * ((z * Work.Spaces.pz u z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
      = dBnd α u G z := by
    have eA : (∫ θ in Work.Spaces.Iθ,
          (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
          + (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
          + (α * (5 + α) / 2) * ((z * Work.Spaces.pz u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
        = (∫ θ in Work.Spaces.Iθ,
            (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
            + (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
          + (∫ θ in Work.Spaces.Iθ,
              (α * (5 + α) / 2) * ((z * Work.Spaces.pz u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)) :=
      MeasureTheory.integral_add (h1.add h2) h3
    have eB : (∫ θ in Work.Spaces.Iθ,
          (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
          + (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
        = (∫ θ in Work.Spaces.Iθ,
            (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
          + (∫ θ in Work.Spaces.Iθ,
              (α ^ 2 / 2) * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)) :=
      MeasureTheory.integral_add h1 h2
    rw [eA, eB, e1, e2, e3]
    simp only [dBnd]
  have hmain : (∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Lzero u z θ * u z θ|)
      ≤ dBnd α u G z := by
    rw [← hdB]
    exact MeasureTheory.integral_mono_ae hintL hR hpt
  calc |sgM u z| ≤ ∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Lzero u z θ * u z θ| := by
        rw [sgM]
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm
            (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
    _ ≤ dBnd α u G z := hmain

/-- **The integral `AM–GM` bound for the source pairing**:
`|sgI G u z| ≤ ½(∫_θ G²σ + sgU u z)`. -/
theorem abs_sgI_le {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hmu : Work.Spaces.HkMem α 0 u)
    {z : ℝ} (hz : 0 < z) :
    |sgI G u z| ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ,
        (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + sgU u z) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hIntG : MeasureTheory.IntegrableOn
      (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    integrableOn_slice_sq_mul_sEta h.memG hzI hz
  have hIntu : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_slice_sgU hmu hz
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |G z θ * u z θ| ≤ (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2) := by
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
    exact abs_sgI_pointwise hθ
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => |G z θ * u z θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hu : MeasureTheory.AEStronglyMeasurable (fun θ => u z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine aestronglyMeasurable_of_continuousOn_Ioo ?_
      exact ((h.smooth 0).continuousOn_zero).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using ((aesm_slice_G h hz).mul hu).norm
  have hintL : MeasureTheory.IntegrableOn (fun θ => |G z θ * u z θ|) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' ((hIntG.add hIntu).const_mul (1 / 2)) haesm ?_
    filter_upwards [hpt] with θ hθ
    simpa only [Real.norm_eq_abs, abs_abs, Pi.add_apply] using hθ
  have hmain : (∫ θ in Work.Spaces.Iθ, |G z θ * u z θ|)
      ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + sgU u z) := by
    have hR : (∫ θ in Work.Spaces.Iθ,
          (1 / 2) * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2))
        = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + sgU u z) := by
      rw [MeasureTheory.integral_const_mul]
      have hh : (∫ θ in Work.Spaces.Iθ,
            (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (u z θ) ^ 2)
          = (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 := MeasureTheory.integral_add hIntG hIntu
      rw [hh]
      simp only [sgU]
    rw [← hR]
    exact MeasureTheory.integral_mono_ae hintL ((hIntG.add hIntu).const_mul (1 / 2)) hpt
  calc |sgI G u z| ≤ ∫ θ in Work.Spaces.Iθ, |G z θ * u z θ| := by
        rw [sgI]
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm (fun θ => G z θ * u z θ)
    _ ≤ _ := hmain

/-- **The a.e. bound of the angular energy by `dBnd + 6 sgU`**, from the slice gap and the
self-form. -/
theorem ae_sgY_le {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hmu : Work.Spaces.HkMem α 0 u)
    (hmg : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hcont : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      sgY u z ≤ dBnd α u G z + 6 * sgU u z := by
  filter_upwards [ae_gap_self h hcont, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hz hzI
  have hz0 : 0 < z := hzI
  have habs := abs_sgM_le h hmu hmg hz0
  have h2 : sgM u z ≤ dBnd α u G z := (abs_le.mp habs).2
  linarith [hz.2]

/-! ## The Fatou-type limit -/



/-! ## Further a.e. strong measurabilities and the sequence limit -/

/-- A.e. strong measurability of `z ↦ (w z)² z² sgP u z`. -/
theorem aesm_wSq_zsq_sgP {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * z ^ 2 * sgP u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hpz : ContDiffOn ℝ (0 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz u)) Qd :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 0)
      (by simpa only [Qd] using h.smooth 1)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (p.1 * Work.Spaces.pz u p.1 p.2) * Work.Spaces.w p.1) Qd :=
    (continuous_fst.continuousOn.mul hpz.continuousOn_zero).mul continuousOn_w_Qd
  have hgen := aesm_wSq_sliceSq (f := fun z θ => z * Work.Spaces.pz u z θ) hcont
  refine hgen.congr (Filter.Eventually.of_forall fun z => ?_)
  show (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2)
      = (Work.Spaces.w z) ^ 2 * z ^ 2 * sgP u z
  have h1 : (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2)
      = (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => by ring)
  have h2 : (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
      = z ^ 2 * sgP u z := by
    rw [sgP, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => by ring)
  rw [h1, h2]
  ring


/-- The open quadrant is conull in `Iz × Iθ`. -/
theorem ae_mem_Qd :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p ∈ Qd := by
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] Qd :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_mem isOpen_Qd.measurableSet




/-! ## The layer masses of the cutoff sequence -/


/-- A.e. strong measurability of `z ↦ (w z)² sgM u z`. -/
theorem aesm_wSq_sgM {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 * sgM u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hL : ContinuousOn (Function.uncurry (Work.Elliptic.Lzero u)) Qd :=
    continuousOn_uncurry_Lzero h.smooth
  have hu : ContinuousOn (Function.uncurry u) Qd := (h.smooth 0).continuousOn_zero
  have hLU : ContinuousOn
      (fun p : ℝ × ℝ => Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2) Qd := hL.mul hu
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hLU
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) haesm
  have hw : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    simp only [Work.Spaces.w]
    fun_prop
  exact (hw.aestronglyMeasurable.mul h1).congr (Filter.Eventually.of_forall fun z => by
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ)
      = (Work.Spaces.w z) ^ 2 * sgM u z
    simp only [sgM])

end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular moment of `Lzero1` on a slice vanishes

Target (`sliceMomentIdentity`): for a datum of the weak hypothesis class `EllWeakPos α k F Ψ`
(`k ≥ 2`) and every `z > 0`,

`∫_{Iθ} Lzero1 (fun t => Ψ z t) θ * sinθcos²θ dθ = 0`,

i.e. the `L₀`-moment of the slice `Ψ z ·` vanishes.  Equivalently (when the integral is honest)
the two boundary values of the antiderivative
`G θ = -(deriv (fun t => Ψ z t) θ) * sinθcos²θ + Ψ z θ * (cos θ * cos (2θ))` agree.

## Strategy

* `Lzero1 (Ψ z ·) · sc = F z · · sc + α²z²·(∂_z²Ψ) z · · sc + α(5+α)z·(∂_zΨ) z · · sc` pointwise
  on the open quadrant (definitional form of `bslOp α Ψ = F`).
* If the `Lzero1`-moment at `z₀` is not honest the totalised integral is `0`
  (`MeasureTheory.integral_undef`).
* Otherwise the boundary estimate `∫ |Lzero1 u| sc < ∞ ⟹ ∫ |u| sc < ∞` (for `u` of class `C²`
  on `(0,π/2)`) gives the honesty of the slices of `Ψ`, `∂_zΨ`, `∂_z²Ψ`, and the moment chain
  `Θ(Ψ(w,·)) ≡ 0 ⟹ Θ(∂_zΨ(w,·)) ≡ 0 ⟹ Θ(∂_z²Ψ(w,·)) ≡ 0` (Fubini plus the fundamental theorem
  of calculus in `z`, the joint integrability coming from the `ℋ^k`-bounds) forces the two
  `z`-moments at `z₀` to vanish.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-! ## The moment functional -/


/-! ## The algebraic form of the equation on a slice -/




/-! ## The main theorem -/



end Work.FTS.EllipticEst.remov.SourceBound
end
end
