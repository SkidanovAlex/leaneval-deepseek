import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.Honest.Yc.HonSliceRightTendstoYc
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.bt_integral_weight_id

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Endpoint regularity of the slices of an `AeData` datum -/

/-- **The `θ`-derivative of a slice has a finite limit at `π/2`.** -/
theorem sliceDerivTendsto (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ∃ L : ℝ, Filter.Tendsto (fun θ => deriv (fun θ' => u z θ') θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
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
  have hsq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta
      (fun θ' : ℝ => u z θ') hint2
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq
      (fun θ' : ℝ => u z θ') hsq
  have hae : Set.Ioc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioc_ae_eq_Icc).trans (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ)
      (Set.Ioc (0 : ℝ) (Real.pi / 2)) := by
    rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set hae]
    rw [MeasureTheory.IntegrableOn] at habs
    refine habs.mono' ?_ ?_
    · exact (measurable_deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t)).aestronglyMeasurable
    · filter_upwards with θ
      exact le_of_eq (Real.norm_eq_abs _)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ => deriv (fun θ' : ℝ => u z θ') θ)
        (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 (fun θ : ℝ => u z θ) x :=
      (hsm 2).contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv (fun θ : ℝ => u z θ)) x := h2.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  exact Work.FTS.EllipticEst.Honest.exists_tendsto_nhdsWithin_Iio_of_integrableOn_deriv
    hπ2 (measurable_deriv _).aestronglyMeasurable hderiv hint

/-- **`θ ↦ u z θ / cos θ` has a finite limit at `π/2`.** -/
theorem sliceDivCosTendstoPiHalf (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ∃ c : ℝ, Filter.Tendsto (fun θ => u z θ / Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) := by
  obtain ⟨L, hL⟩ := sliceDerivTendsto α u G h hz
  refine ⟨-L, ?_⟩
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth n)
  have hzero : Filter.Tendsto (fun θ : ℝ => u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h z hz).1
  exact Work.FTS.EllipticEst.Honest.divCos_tendsto_of_tendsto_deriv hsm hzero hL

/-! ## The slicewise Hardy chain for `u / cos θ` -/

/-- The `σ`-weighted square of `u z · / cos` is integrable, for `z > 0`. -/
theorem sliceDivCosSqIntegrable (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hmu : Work.Spaces.HkMem α 0 u) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hsm2 : ContDiffOn ℝ 2 (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth 2)
  have h1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hmu hz
  have h2 : MeasureTheory.IntegrableOn
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
  exact (Work.FTS.EllipticEst.Honest.sliceBarSq2 (fun θ : ℝ => u z θ) hsm2
    (sliceDivCosTendstoPiHalf α u G h hz) h1
    (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ : ℝ => u z θ) hsm2 h1 h2).1).1

/-- **The slicewise `σ`-weighted Hardy inequality** for the fibre of an `AeData` datum. -/
theorem sliceBarLe (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hmu : Work.Spaces.HkMem α 0 u) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ 1010000 * ((∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by
  have hsm2 : ContDiffOn ℝ 2 (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth 2)
  have h1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hmu hz
  have h2 : MeasureTheory.IntegrableOn
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
  obtain ⟨h3int, h3bd⟩ := Work.FTS.EllipticEst.Honest.sliceInterp (fun θ : ℝ => u z θ) hsm2 h1 h2
  obtain ⟨-, h4bd⟩ := Work.FTS.EllipticEst.Honest.sliceBarSq2 (fun θ : ℝ => u z θ) hsm2
    (sliceDivCosTendstoPiHalf α u G h hz) h1 h3int
  have hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    fun θ hθ => Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  have hB : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  have hmain : (∫ θ in Work.Spaces.Iθ,
        (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ 100 * ((∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 10000 * ((∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ))) :=
    h4bd.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl h3bd) (by norm_num))
  linarith [hmain, hA, hB]


/-! ## The level-`0` inner integral of a `HkIntegrand` -/

/-- **The level-`0` `HkIntegrand` in `σ`-form.**  For `θ ∈ Iθ`,
`HkIntegrand α 0 g z θ = w z ^ 2 · (g z θ ^ 2 · sEta θ)`. -/
theorem barHkInt (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  rw [show Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
          Finset.sum_singleton]
        norm_num]
  rw [Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ hsin]
  simp only [Work.FTS.EllipticEst.sEta]
  ring

/-- The `θ`-inner integral of `HkIntegrand α 0 g` is `w z ^ 2` times the `σ`-weighted square
integral of the slice. -/
theorem innerEq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
    rw [barHkInt α g hθ])

/-! ## The `ℋ⁰`-membership of `u / cos θ` -/

end Work.FTS.EllipticEst.H2W.AeProof
