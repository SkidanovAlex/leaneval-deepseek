import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.H2W.Ae.aesliceU
import Submission.Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy

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

/-- **The a.e. slice bound in real-integral form.**  An a.e. (in `z`) `lintegral` comparison for
the slice integrands upgrades to the comparison of the honest integrals, because the right-hand
side is honest by hypothesis. -/
theorem hr2_aeReal_of_aeLintegral {α : ℝ} {u : ℝ → ℝ → ℝ}
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
theorem hr2_hkMem_u_of_ae_bound (K : ℝ) (hKpos : 0 < K)
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

theorem hr2_hkMem_u (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) : Work.Spaces.HkMem α 0 u := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.H2W.Ae.aesliceU_of
    Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
    Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy
  exact hr2_hkMem_u_of_ae_bound K hKpos α u G h
    (hr2_aeReal_of_aeLintegral h.smooth h.memAng2 hKpos (hK α u G h))

end

end Work.FTS.EllipticEst.H2W.Ae
