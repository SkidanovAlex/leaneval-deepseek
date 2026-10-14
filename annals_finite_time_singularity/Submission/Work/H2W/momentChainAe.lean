import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.GradTraceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## 1. The `σ`-weighted angular energy of the slice `θ ↦ z ∂_z u(z,θ)` -/

/-- The `σ`-weighted angular energy `sliceE u z = ∫_θ (∂_θ(z ∂_z u)(z,θ))² σ(θ) dθ` of the slice
`θ ↦ z ∂_z u(z,θ)`; `σ θ = sin(2θ)^{-η}`. -/
def sliceE (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

theorem sliceE_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sliceE u z :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)


/-- The angular weight is nonnegative on `Iθ`. -/
theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ σ θ := by
  rw [Work.FTS.EllipticEst.AngSecond.sig]
  refine Real.rpow_nonneg ?_ _
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The slice energy as an integral over the open interval (the endpoints are null). -/
theorem sliceE_eq_Ioo (u : ℝ → ℝ → ℝ) (z : ℝ) :
    sliceE u z = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
  MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm



/-! ## 2. The two a.e. honesties -/





/-! ## 3. The two slices' one-sided limits, from `sliceBoundaryLimit` -/

/-- The first half of `sliceBoundaryLimit` (the limit at `0⁺`), in `∀ f` form. -/
theorem sliceBoundaryLeftRaw : ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) →
    ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ - c) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) *
        ∫ θ' in Set.Ioo 0 θ, (deriv f θ') ^ 2 * Work.FTS.EllipticEst.thEta θ' := by
  obtain ⟨K, hKpos, hK⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  exact ⟨K, hKpos, fun f hf1 hfi => (hK f hf1 hfi).1⟩

/-- The second half of `sliceBoundaryLimit` (the limit at `(π/2)⁻`), in `∀ f` form. -/
theorem sliceBoundaryRightRaw : ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) →
    ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ - c) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          ∫ θ' in Set.Ioo θ (Real.pi / 2), (deriv f θ') ^ 2
            * Work.FTS.EllipticEst.thEta θ' := by
  obtain ⟨K, hKpos, hK⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  exact ⟨K, hKpos, fun f hf1 hfi => (hK f hf1 hfi).2⟩

/-- The `θ`-slice of `D_z u` has derivative `D_z (∂_θ u)` on the open interval. -/
theorem deriv_Dz_slice {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {s θ : ℝ} (hs : 0 < s) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.Dz u s θ') θ = Work.Spaces.Dz (Work.Spaces.pth u) s θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (s, θ) :=
    (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hs, hθ.1, hθ.2⟩))
  have h1 : deriv (fun θ' => Work.Spaces.Dz u s θ') θ
      = s * Work.Spaces.pth (Work.Spaces.pz u) s θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pth, deriv_const_mul_field]
  rw [h1]
  show s * Work.Spaces.pth (Work.Spaces.pz u) s θ
    = s * Work.Spaces.pz (Work.Spaces.pth u) s θ
  exact congrArg (fun t => s * t) (Work.Spaces.pz_pth_comm (f := u) hcd).symm

/-- **The left boundary limit of the slice `θ ↦ z ∂_z u(z,θ)`.** -/
theorem sliceBoundaryLeft {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {s K : ℝ} (hs : 0 < s) (hKnn : 0 ≤ K)
    (hraw : ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
        ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ - c) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) *
          ∫ θ' in Set.Ioo 0 θ, (deriv f θ') ^ 2 * Work.FTS.EllipticEst.thEta θ')
    (hE : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ) :
    ∃ c : ℝ, Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz u s θ - c) ^ 2
        ≤ K * θ ^ (1 + Work.Spaces.eta) * sliceE u s := by
  have hcont1 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.Dz u s θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip (fun n => (hS.Dz).forall n) hs 1
  have hsig : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' => Work.Spaces.Dz u s θ') θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hE.mono_set Set.Ioo_subset_Icc_self)
      (fun θ hθ => ?_) measurableSet_Ioo
    rw [deriv_Dz_slice hS hs hθ]
    rfl
  obtain ⟨c, hc, hb⟩ := hraw _ hcont1 hsig
  refine ⟨c, hc, fun θ hθ => ?_⟩
  have hE' : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hE.mono_set Set.Ioo_subset_Icc_self
  have hmono : (∫ t in Set.Ioo 0 θ, (Work.Spaces.Dz (Work.Spaces.pth u) s t) ^ 2
      * Work.FTS.EllipticEst.sEta t) ≤ sliceE u s := by
    rw [sliceE_eq_Ioo u s]
    exact MeasureTheory.setIntegral_mono_set hE'
      (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
      (by
        filter_upwards with t ht
        exact ⟨ht.1, lt_trans ht.2 hθ.2⟩)
  have hbθ : (Work.Spaces.Dz u s θ - c) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) *
      ∫ t in Set.Ioo 0 θ, (Work.Spaces.Dz (Work.Spaces.pth u) s t) ^ 2
        * Work.FTS.EllipticEst.sEta t := by
    have h := hb θ hθ
    rwa [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => by
        rw [deriv_Dz_slice hS hs ⟨ht.1, lt_trans ht.2 hθ.2⟩])] at h
  exact le_trans hbθ (mul_le_mul_of_nonneg_left hmono
    (mul_nonneg hKnn (Real.rpow_nonneg hθ.1.le _)))

/-- **The right boundary limit of the slice `θ ↦ z ∂_z u(z,θ)`.** -/
theorem sliceBoundaryRight {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {s K : ℝ} (hs : 0 < s) (hKnn : 0 ≤ K)
    (hraw : ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
        ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ - c) ^ 2
          ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
            ∫ θ' in Set.Ioo θ (Real.pi / 2), (deriv f θ') ^ 2
              * Work.FTS.EllipticEst.thEta θ')
    (hE : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ) :
    ∃ c : ℝ, Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz u s θ - c) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * sliceE u s := by
  have hcont1 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.Dz u s θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip (fun n => (hS.Dz).forall n) hs 1
  have hsig : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' => Work.Spaces.Dz u s θ') θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hE.mono_set Set.Ioo_subset_Icc_self)
      (fun θ hθ => ?_) measurableSet_Ioo
    rw [deriv_Dz_slice hS hs hθ]
    rfl
  obtain ⟨c, hc, hb⟩ := hraw _ hcont1 hsig
  refine ⟨c, hc, fun θ hθ => ?_⟩
  have hE' : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hE.mono_set Set.Ioo_subset_Icc_self
  have hmono : (∫ t in Set.Ioo θ (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) s t) ^ 2
      * Work.FTS.EllipticEst.sEta t) ≤ sliceE u s := by
    rw [sliceE_eq_Ioo u s]
    exact MeasureTheory.setIntegral_mono_set hE'
      (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
      (by
        filter_upwards with t ht
        exact ⟨lt_trans hθ.1 ht.1, ht.2⟩)
  have hbθ : (Work.Spaces.Dz u s θ - c) ^ 2
      ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
        ∫ t in Set.Ioo θ (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) s t) ^ 2
          * Work.FTS.EllipticEst.sEta t := by
    have h := hb θ hθ
    rwa [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => by
        rw [deriv_Dz_slice hS hs ⟨lt_trans hθ.1 ht.1, ht.2⟩])] at h
  exact le_trans hbθ (mul_le_mul_of_nonneg_left hmono
    (mul_nonneg hKnn (Real.rpow_nonneg (by linarith [hθ.2]) _)))

/-! ## 4. The pointwise domination of `|∂_z u(z,θ)|` -/

/-- **The pointwise domination.**  If the slice `θ ↦ z ∂_z u(z,θ)` has a one-sided limit `c` at an
endpoint and satisfies the quadratic boundary bound at that endpoint, then `|∂_z u(z,θ)|` is
dominated by `|∂_z u(z,1)| + M √(sliceE u z)/z` with `M = √K + √(K (π/2)^{1+η})`. -/
theorem pz_le_of_slice_bounds {u : ℝ → ℝ → ℝ} {s θ c K : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hK : 0 < K) (hΦ : 0 ≤ sliceE u s)
    (h1 : (Work.Spaces.Dz u s 1 - c) ^ 2 ≤ K * sliceE u s)
    (h2 : (Work.Spaces.Dz u s θ - c) ^ 2
      ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) :
    |Work.Spaces.pz u s θ| ≤ |Work.Spaces.pz u s 1|
      + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s) := by
  have hKΦ : 0 ≤ K * sliceE u s := mul_nonneg hK.le hΦ
  have hKΦ' : 0 ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s :=
    mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _)) hΦ
  have hc0bd : |c| ≤ |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by
    have h2abs : |Work.Spaces.Dz u s 1 - c| ≤ Real.sqrt (K * sliceE u s) :=
      abs_le_of_sq_le_sq (by rw [Real.sq_sqrt hKΦ]; exact h1) (Real.sqrt_nonneg _)
    calc |c| = |c - Work.Spaces.Dz u s 1 + Work.Spaces.Dz u s 1| := by ring_nf
      _ ≤ |c - Work.Spaces.Dz u s 1| + |Work.Spaces.Dz u s 1| := abs_add_le _ _
      _ = |Work.Spaces.Dz u s 1 - c| + |Work.Spaces.Dz u s 1| := by rw [abs_sub_comm]
      _ ≤ Real.sqrt (K * sliceE u s) + |Work.Spaces.Dz u s 1| := by linarith
      _ = |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by ring
  have h1abs : |Work.Spaces.Dz u s θ - c|
      ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) := by
    have hsq : (Work.Spaces.Dz u s θ - c) ^ 2
        ≤ (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s)) ^ 2 := by
      rw [Real.sq_sqrt hKΦ']
      exact h2
    exact abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _)
  have hM1 : Real.sqrt (K * sliceE u s) = Real.sqrt K * Real.sqrt (sliceE u s) :=
    Real.sqrt_mul hK.le _
  have hM2 : Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s)
      = Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceE u s) :=
    Real.sqrt_mul (by positivity) _
  have hDzbd : |Work.Spaces.Dz u s θ| ≤ |Work.Spaces.Dz u s 1|
      + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * Real.sqrt (sliceE u s) := by
    have h3 : |Work.Spaces.Dz u s θ| ≤ |c| + Real.sqrt
        (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) := by
      calc |Work.Spaces.Dz u s θ|
          = |Work.Spaces.Dz u s θ - c + c| := by ring_nf
        _ ≤ |Work.Spaces.Dz u s θ - c| + |c| := abs_add_le _ _
        _ ≤ _ := by linarith
    calc |Work.Spaces.Dz u s θ| ≤ |c| + Real.sqrt
          (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) := h3
      _ ≤ |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) + Real.sqrt
          (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) := by linarith
      _ = |Work.Spaces.Dz u s 1| + (Real.sqrt K
            + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s) := by rw [hM1, hM2]; ring
  have hDz : Work.Spaces.Dz u s θ = s * Work.Spaces.pz u s θ := rfl
  have hDz1 : Work.Spaces.Dz u s 1 = s * Work.Spaces.pz u s 1 := rfl
  have h4 : |Work.Spaces.Dz u s θ| / s
      ≤ (|Work.Spaces.Dz u s 1| + (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * Real.sqrt (sliceE u s)) / s := div_le_div_of_nonneg_right hDzbd hs.le
  calc |Work.Spaces.pz u s θ| = |Work.Spaces.Dz u s θ| / s := by
        rw [hDz, abs_mul, abs_of_pos hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    _ ≤ (|Work.Spaces.Dz u s 1| + (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * Real.sqrt (sliceE u s)) / s := h4
    _ = |Work.Spaces.pz u s 1| + (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) / s) := by
        rw [hDz1, abs_mul, abs_of_pos hs]; field_simp

/-! ## 5. The dominating function of the dominated-convergence step -/

/-- The dominating function `s ↦ |∂_z u(s,1)| + M √(sliceE u s)/s` of the DCT step. -/
def boundU (u : ℝ → ℝ → ℝ) (K : ℝ) (s : ℝ) : ℝ :=
  |Work.Spaces.pz u s 1|
    + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
      * (Real.sqrt (sliceE u s) / s)


end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.Honest

/-- **The right-endpoint behaviour of a `θ`-slice from the raw hypotheses.**  Only the equation
on the open quadrant, the `C^∞`-regularity there and the `HkMem α 0`-honesty of `F`,
`z²∂_zzΨ`, `∂_θθΨ` (plus `0 < α ≤ 1/4`) are used, so the result applies to `AeData`: the
slice `θ ↦ Ψ z θ` tends to `0` at `π/2` from below, with the rate `O(π/2 - θ)`. -/
theorem sliceRightTendsto_raw (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hαpos : 0 < α) (hα4 : α ≤ 1 / 4)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemF : Work.Spaces.HkMem α 0 F)
    (hmemA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (z : ℝ) (hz : 0 < z) :
    Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |Ψ z θ| ≤ K * (Real.pi / 2 - θ) := by
  -- the base point `a` of the `θ`-integration
  set a : ℝ := Real.pi / 4 with hadef
  have ha_pos : 0 < a := by rw [hadef]; linarith [Real.pi_pos]
  have ha_lt : a < Real.pi / 2 := by rw [hadef]; linarith [Real.pi_pos]
  have hz1 : 0 < z + 1 := by linarith
  -- slicewise `L²(σ)`-integrability of `∂_θθΨ` at every `s > 0` (from `memB`)
  have hth : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2
        * sEta θ) Work.Spaces.Iθ := by
    intro s hs
    have h0 := HkMemSliceSqSigma hmemB hs
    refine h0.congr_fun (fun θ _ => ?_) measurableSet_Icc
    have h1 : Work.Spaces.pthIter 2 Ψ s θ
        = deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    show (Work.Spaces.pthIter 2 Ψ s θ) ^ 2 * sEta θ
      = (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2 * sEta θ
    rw [h1]
  -- boundedness of the slices and of their `θ`-derivatives at `z` and at `z + 1`
  obtain ⟨M, hMpos, hMb⟩ :=
    SliceBddSqSigma (contDiffOn_slice Ψ hz (hsm 2)) (hth z hz)
  obtain ⟨M₁, hM₁pos, hM₁b⟩ :=
    SliceBddSqSigma (contDiffOn_slice Ψ hz1 (hsm 2)) (hth (z + 1) hz1)
  -- the `σ`-weighted square of the `z`-slice of `∂_z²Ψ` (from `memA`, divided by `z⁴`)
  have hp_int : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Work.Spaces.Iθ := by
    have h0 := HkMemSliceSqSigma hmemA hz
    have hz2 : (z ^ 2) ≠ 0 := by positivity
    have h1 := h0.const_mul ((z ^ 2) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
    field_simp
  -- the `σ`-weighted square of the `F`-slice
  have hF_int : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * sEta θ) Work.Spaces.Iθ := HkMemSliceSqSigma hmemF hz
  -- a.e. measurability of the `σ`-weighted slice norm of `∂_z²Ψ` (from the honest `z`-integral
  -- `hmemA.2`, after dividing by the measurable weight `w s²·s⁴`)
  have hγaem : AEMeasurable
      (fun s => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
      (volume.restrict Work.Spaces.Iz) := by
    have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (Work.Spaces.w s) ^ 2 * (s ^ 4)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [HkIntegrand_zero_eq_Iθ α (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) hθ]
        ring)
    have hm : AEMeasurable (fun s => (Work.Spaces.w s) ^ 2 * (s ^ 4)
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
        (volume.restrict Work.Spaces.Iz) :=
      (hmemA.2.congr_fun (fun s _ => hG s) measurableSet_Ici).aestronglyMeasurable.aemeasurable
    have hden : AEMeasurable (fun s : ℝ => (Work.Spaces.w s) ^ 2 * s ^ 4)
        (volume.restrict Work.Spaces.Iz) := by
      refine Measurable.aemeasurable ?_
      have hw : Measurable fun s : ℝ => Work.Spaces.w s := by
        show Measurable fun s : ℝ => (1 + s) ^ 2 / s ^ 2
        fun_prop
      exact (hw.pow_const 2).mul (measurable_id.pow_const 4)
    refine (hm.div hden).congr ?_
    have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (0 : ℝ)
    have h0' : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iz), s ∈ Set.Ioi (0 : ℝ) := by
      rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      filter_upwards [h0] with s hs hmem
      exact lt_of_le_of_ne hmem (Ne.symm hs)
    filter_upwards [h0'] with s hs
    have hw : (Work.Spaces.w s) ^ 2 * s ^ 4 ≠ 0 := by
      have h1 : Work.Spaces.w s ≠ 0 := by
        show (1 + s) ^ 2 / s ^ 2 ≠ 0
        have hs' : s ≠ 0 := ne_of_gt hs
        have h1' : (1 : ℝ) + s ≠ 0 := by
          have hs0 : (0 : ℝ) < s := hs
          have : (0 : ℝ) < 1 + s := by linarith
          exact ne_of_gt this
        exact div_ne_zero (pow_ne_zero 2 h1') (pow_ne_zero 2 hs')
      exact mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 4 (ne_of_gt hs))
    exact mul_div_cancel_left₀ _ hw
  -- `γ` written with the `s⁴`-weight of `memA` (the form `HkMemSliceGammaLinTop` bounds)
  have hγw : ∀ s, (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
      = (s ^ 2) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
    intro s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by ring)
  -- a.e. measurability of the *weighted* slice norm, on `Icc z (z+1)`
  have hγw_aem : AEMeasurable (fun s => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
      (volume.restrict (Set.Icc z (z + 1))) := by
    have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [HkIntegrand_zero_eq_Iθ α (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) hθ]
        ring)
    have h1 : AEMeasurable (fun s => (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) (volume.restrict Work.Spaces.Iz) :=
      (hmemA.2.congr_fun (fun s _ => hG s) measurableSet_Ici).aestronglyMeasurable.aemeasurable
    -- remove the weight `w s²` (multiply the *unweighted* norm, whose measurability is `hγaem`,
    -- by the measurable factor `(s²)²`)
    have h2 : AEMeasurable (fun s => ∫ θ in Work.Spaces.Iθ,
        ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        (volume.restrict Work.Spaces.Iz) := by
      refine (hγaem.mul ((measurable_id.pow_const 2).pow_const 2).aemeasurable).congr ?_
      refine Filter.Eventually.of_forall fun s => ?_
      show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) * (s ^ 2) ^ 2
        = ∫ θ in Work.Spaces.Iθ, (s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ
      rw [mul_comm, (hγw s).symm]
    exact (h2.ennreal_ofReal).mono_measure
      (Measure.restrict_mono (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1)) le_rfl)
  -- the weighted version is exactly `HkMemSliceGammaLinTop`
  have hγw_lin : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) < ⊤ := by
    refine lt_of_eq_of_lt ?_ (HkMemSliceGammaLinTop hmemA hz)
    exact MeasureTheory.lintegral_congr fun s => by rw [hγw s]
  -- the unweighted lintegral, via the pointwise scaling `γ s ≤ (z⁴)⁻¹ · γ_w s` on `Icc z (z+1)`
  have hgamma : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) < ⊤ := by
    have hpt : ∀ s ∈ Set.Icc z (z + 1), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        ≤ ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
      have hs4 : 0 < s ^ 4 := pow_pos hs0 4
      have hle : (s ^ 4)⁻¹ ≤ (z ^ 4)⁻¹ :=
        inv_anti₀ (pow_pos hz 4) (pow_le_pow_left₀ (le_of_lt hz) hs.1 4)
      have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
          ≤ ((z ^ 4)⁻¹) * (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
        rw [hγw s]
        have heq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            = (s ^ 4)⁻¹ * ((s ^ 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) := by
          rw [show (s ^ 2) ^ 2 = s ^ 4 from by ring, ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hs4), one_mul]
        conv_lhs => rw [heq]
        refine mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg (s ^ 2)) ?_)
        exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
      calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
          ≤ ENNReal.ofReal (((z ^ 4)⁻¹) * (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) :=
            (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
              (MeasureTheory.setIntegral_nonneg measurableSet_Icc
                (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))))).mpr h1
        _ = ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
            rw [ENNReal.ofReal_mul (by positivity)]
    calc ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        ≤ ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) :=
          MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
      _ = ENNReal.ofReal ((z ^ 4)⁻¹) * ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) :=
          MeasureTheory.lintegral_const_mul'' _ hγw_aem
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hγw_lin
  -- a.e. measurability of `ofReal γ` on `Icc z (z+1)` (transfer from `hγaem`)
  have hγaemK : AEMeasurable (fun s => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
      (volume.restrict (Set.Icc z (z + 1))) :=
    (hγaem.ennreal_ofReal).mono_measure (Measure.restrict_mono_set volume
      (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1)))
  -- the lintegral of `(1/2)(γ + π/2)` is finite (this is the constant `c` below)
  have hb_lin : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2)) < ⊤ := by
    -- it suffices to bound the *decomposed* integrand `ofReal γ + ofReal (π/2)`, since
    -- `(1/2)(γ + π/2) ≤ γ + π/2`; this avoids pulling out the constant `ofReal (1/2)`
    have hsum : ∫⁻ s in Set.Icc z (z + 1), (ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + ENNReal.ofReal (Real.pi / 2)) < ⊤ := by
      rw [MeasureTheory.lintegral_add_left' hγaemK]
      refine ENNReal.add_lt_top.mpr ⟨hgamma, ?_⟩
      rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    refine lt_of_le_of_lt ?_ hsum
    refine MeasureTheory.lintegral_mono_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s _ => ?_))
    have hγnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
    have hle : (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2) ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2 := by linarith [Real.pi_pos]
    calc ENNReal.ofReal ((1 / 2) * ((∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2))
        ≤ ENNReal.ofReal ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            + Real.pi / 2) := (ENNReal.ofReal_le_ofReal_iff (by linarith [Real.pi_pos])).mpr hle
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            + ENNReal.ofReal (Real.pi / 2) := by
          rw [ENNReal.ofReal_add hγnn (by linarith [Real.pi_pos])]
  -- the `b`-independent constant bounding `|P_b(z)|`
  set c : ℝ := ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2))) with hcdef
  have hcnonneg : 0 ≤ c := by rw [hcdef]; exact ENNReal.toReal_nonneg
  -- joint continuity of `pz Ψ` on the open quadrant (finite order: `∂_z` of a `C¹` function)
  have hpz_cont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      isOpen_Ioi.prod isOpen_Ioo
    have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderivWithin ℝ (Function.uncurry Ψ)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) p)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (hsm 1).fderivWithin (m := 0) hU.uniqueDiffOn (by norm_num)
      refine (contDiffOn_zero.mp h1).congr (fun p hp => ?_)
      show fderiv ℝ (Function.uncurry Ψ) p
        = fderivWithin ℝ (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) p
      rw [fderivWithin_of_isOpen hU hp]
    have h2 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p (1, 0))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hfd.clm_apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    refine h2.congr (fun p hp => ?_)
    show Work.Spaces.pz Ψ p.1 p.2 = fderiv ℝ (Function.uncurry Ψ) p (1, 0)
    exact Work.Spaces.pz_eq_fderiv
      (((hsm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp))
  -- **first application**: `∂_z ∫_a^b Ψ s θ dθ = ∫_a^b pz Ψ s θ dθ` for `s ∈ [z, z+1]`
  have hZderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Ψ t θ) (∫ θ in a..b, Work.Spaces.pz Ψ s θ) s := by
    intro b hb s hs
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      isOpen_Ioi.prod isOpen_Ioo
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1)
      ?_ ?_ ?_
    · exact ((hsm 0).continuousOn.mono hrect).mono hsub
    · exact (hpz_cont.mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      exact (Work.Spaces.differentiableAt_curry_left
        (((hsm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hxU))).hasDerivAt
  -- *** Stage A ***
  -- `F` is smooth on the open quadrant (it *is* `bslOp α Ψ` there), so each of its `θ`-slices
  -- is continuous on `(0, π/2)`; in particular `F z ·` is a genuine interval integral on `[a,b]`.
  have hFcont : ContinuousOn (fun θ => F z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hU : IsOpen Qd := isOpen_Qd
    have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
      Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 1) (hsm 2)
    have hpz2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Qd := by
      have h2 : ContDiffOn ℝ (2 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
        Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 2) (hsm 3)
      have h1 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 1) h2
      rw [pzIter_two_eq Ψ]
      exact h1
    have hp2 : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice (Work.Spaces.pzIter 2 Ψ) hz hpz2).continuousOn
    have hp1 : ContinuousOn (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice (Work.Spaces.pz Ψ) hz hpz1).continuousOn
    have hpsi : ContinuousOn (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice Ψ hz (hsm 0)).continuousOn
    have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (hsm 2)
    have hpth2 : ContinuousOn (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h2 : ContDiffOn ℝ 0 (deriv (fun θ' => deriv (fun θ'' => Ψ z θ'') θ'))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      rw [pthIter_two_eq Ψ z]
      exact h2.continuousOn
    have htan : ContDiffOn ℝ 2 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContDiffOn ℝ (2 : WithTop ℕ∞) (fun θ => Real.sin θ / Real.cos θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn)
          (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))
      have htanfun : Real.tan = fun θ : ℝ => Real.sin θ / Real.cos θ :=
        funext Real.tan_eq_sin_div_cos
      rw [htanfun]
      exact h
    have hpthtan : ContinuousOn (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have htw : ContDiffOn ℝ 2 (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        htan.mul hslice2
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ => Real.tan θ * Ψ z θ))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have hfun : (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          = deriv (fun θ => Real.tan θ * Ψ z θ) := rfl
      rw [hfun]
      exact h1.continuousOn
    have hcomb : ContinuousOn (fun θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        + (-Work.Spaces.pthIter 2 Ψ z θ + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
            - 6 * Ψ z θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((hp2.const_mul (-(α ^ 2 * z ^ 2))).sub (hp1.const_mul (α * (5 + α) * z))).add
        ((hpth2.neg.add hpthtan).sub (hpsi.const_mul 6))
    refine hcomb.congr (fun θ hθ => ?_)
    simpa only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
      using (heq z hz θ hθ.1 hθ.2).symm
  -- the `σ`-weighted square of the `∂_z²Ψ`-slice, for every `s > 0`
  have hps_int : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) Work.Spaces.Iθ := by
    intro s hs
    have h0 := HkMemSliceSqSigma hmemA hs
    have h2 : (s ^ 2) ≠ 0 := by positivity
    have h1 := h0.const_mul ((s ^ 2) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
    field_simp
  -- joint continuity of `pz Ψ` on the open quadrant
  have hUq : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hpz1c : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hUq (n := 1) (hsm 2)
  have hpz2c : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn hUq (hsm 2)
  -- **second application**: `∂_z ∫_a^b pz Ψ s θ dθ = ∫_a^b pzIter 2 Ψ s θ dθ`
  have hPderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Work.Spaces.pz Ψ t θ) (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
      s := by
    intro b hb s hs
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1) ?_ ?_ ?_
    · exact (hpz_cont.mono hrect).mono hsub
    · exact (hpz2c.mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      have h := hasDerivAt_slice_of_contDiffOn_open hUq hpz1c hxU
      simpa only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pzIter_succ,
        show (1 : ℕ) = 0 + 1 from rfl, Work.Spaces.pzIter_zero] using h
  -- *** Stage B ***
  -- the two `b`-independent `σ`-weighted slice norms
  set QP : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ with hQPdef
  set QF : ℝ := ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * sEta θ with hQFdef
  have hQPnn : 0 ≤ QP := by
    rw [hQPdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  have hQFnn : 0 ≤ QF := by
    rw [hQFdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  -- the third application: `Q_b` is differentiable, hence continuous
  have hpz2cd : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Qd := by
    have h1 : ContDiffOn ℝ (4 : WithTop ℕ∞) (Function.uncurry Ψ) Qd := hsm 4
    have h2 : ContDiffOn ℝ (3 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
      Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 3) h1
    have h3 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 2) h2
    rw [pzIter_two_eq Ψ]
    exact h3
  have hpz3cd : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 3 Ψ)) Qd := by
    have h4 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 1) hpz2cd
    have h5 : Work.Spaces.pzIter 3 Ψ = Work.Spaces.pz (Work.Spaces.pzIter 2 Ψ) := rfl
    rw [h5]
    exact h4
  have hQderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ t θ)
      (∫ θ in a..b, Work.Spaces.pzIter 3 Ψ s θ) s := by
    intro b hb s hs
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1) ?_ ?_ ?_
    · exact (hpz2c.mono hrect).mono hsub
    · exact ((hpz3cd.continuousOn).mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      exact hasDerivAt_slice_of_contDiffOn_open hUq (hpz2cd.of_le (by norm_num)) hxU
  -- **the bound on `P_b(z)`** — the only place where the `z`-dependence of the data is used
  have hPb : ∀ b ∈ Set.Ioo a (Real.pi / 2),
      |∫ θ in a..b, Work.Spaces.pz Ψ z θ| ≤ (Real.pi / 2) * (M + M₁) + c := by
    intro b hb
    have hZder := hZderiv b hb
    have hPder := hPderiv b hb
    have hQder := hQderiv b hb
    have hcontP : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ)
        (Set.Icc z (z + 1)) := fun s hs => (hPder s hs).continuousAt.continuousWithinAt
    have hcontQ : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
        (Set.Icc z (z + 1)) := fun s hs => (hQder s hs).continuousAt.continuousWithinAt
    have hceq : Set.uIcc z (z + 1) = Set.Icc z (z + 1) := Set.uIcc_of_le (by linarith)
    have hcontPu : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ)
        (Set.uIcc z (z + 1)) := by rw [hceq]; exact hcontP
    -- first fundamental-theorem step: `∫_z^{z+1} P_b = Z(z+1) - Z(z)`
    have h1 : (∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ t θ))
        = (∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => ∫ θ in a..b, Ψ t θ)
        (f' := fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ) ?_ hcontPu.intervalIntegrable
      intro s hs
      rw [hceq] at hs
      exact hZder s hs
    -- second step: `P_b(t) - P_b(z) = ∫_z^t Q_b`
    have h2 : ∀ t ∈ Set.Icc z (z + 1),
        (∫ θ in a..b, Work.Spaces.pz Ψ t θ) - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          = ∫ s in z..t, (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ) := by
      intro t ht
      have hle : z ≤ t := ht.1
      have hsub : Set.uIcc z t ⊆ Set.Icc z (z + 1) := by
        rw [Set.uIcc_of_le hle]
        exact Set.Icc_subset_Icc le_rfl ht.2
      have hint : IntervalIntegrable (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
          volume z t := (hcontQ.mono hsub).intervalIntegrable
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hPder s (hsub hs)) hint).symm
    -- the algebraic consequence
    have h3 : (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
        = ((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
          - ∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
              - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) := by
      have hsub2 : (∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
            - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)))
          = (∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ t θ))
            - ∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ z θ) :=
        intervalIntegral.integral_sub hcontPu.intervalIntegrable intervalIntegrable_const
      rw [hsub2, h1, intervalIntegral.integral_const]
      ring
    -- the uniform bound on the subtracted term
    have hB : ∀ t ∈ Set.Icc z (z + 1),
        |(∫ θ in a..b, Work.Spaces.pz Ψ t θ) - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)| ≤ c := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with hzt | hzt
      · rw [← hzt, sub_self, abs_zero]; exact hcnonneg
      · rw [h2 t ht]
        have hQint : IntegrableOn (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
            (Set.Icc z (z + 1)) := hcontQ.integrableOn_Icc
        have hQabs : IntegrableOn (fun s => |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|)
            (Set.Icc z (z + 1)) := by
          simpa only [Real.norm_eq_abs, MeasureTheory.IntegrableOn] using hQint.norm
        have hstep : |∫ s in z..t, (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)|
            ≤ ∫ s in Set.Icc z (z + 1), |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ| := by
          refine le_trans (intervalIntegral.abs_integral_le_integral_abs hzt.le) ?_
          rw [intervalIntegral.integral_of_le hzt.le]
          refine MeasureTheory.setIntegral_mono_set hQabs
            (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            (Filter.Eventually.of_forall (fun s hs => ?_))
          exact ⟨le_of_lt hs.1, le_trans hs.2 ht.2⟩
        refine le_trans hstep ?_
        calc (∫ s in Set.Icc z (z + 1), |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|)
              ≤ ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
                  |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|) :=
                setIntegral_le_toReal_lintegral _
                  (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            _ ≤ ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
                  ((1 / 2) * ((∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2))) := by
                refine ENNReal.toReal_mono (ne_of_lt hb_lin) (MeasureTheory.lintegral_mono_ae ?_)
                refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => ?_)
                have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
                have hQb := le_trans
                  (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
                  (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) (hps_int s hs0))
                have hnn : 0 ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2) :=
                  mul_nonneg (by norm_num) (add_nonneg
                    (MeasureTheory.setIntegral_nonneg measurableSet_Icc
                      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)))
                    (by linarith [Real.pi_pos]))
                exact (ENNReal.ofReal_le_ofReal_iff hnn).mpr hQb
            _ = c := rfl
    -- the two slice integrals at `z` and `z + 1`
    have hZc : ∀ C : ℝ, 0 ≤ C → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ z θ| ≤ C) →
        |∫ θ in a..b, Ψ z θ| ≤ C * (Real.pi / 2) := by
      intro C hC hbnd
      have hmain : |∫ θ in a..b, Ψ z θ| ≤ C * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ z θ) (a := a) (b := b) (C := C) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact hbnd θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hC)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hZc1 : ∀ C : ℝ, 0 ≤ C → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ (z + 1) θ| ≤ C) →
        |∫ θ in a..b, Ψ (z + 1) θ| ≤ C * (Real.pi / 2) := by
      intro C hC hbnd
      have hmain : |∫ θ in a..b, Ψ (z + 1) θ| ≤ C * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ (z + 1) θ) (a := a) (b := b) (C := C) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact hbnd θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hC)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hZ1 := hZc1 M₁ hM₁pos.le (fun θ hθ => (hM₁b θ hθ).2)
    have hZ0 := hZc M hMpos.le (fun θ hθ => (hMb θ hθ).2)
    calc |∫ θ in a..b, Work.Spaces.pz Ψ z θ|
        = |((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
            - ∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| := by
          conv_lhs => rw [h3]
      _ ≤ |(∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ)|
            + |∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| := by
          have := abs_sub_le ((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
            (0 : ℝ) (∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)))
          simpa using this
      _ ≤ (M₁ * (Real.pi / 2) + M * (Real.pi / 2)) + c := by
          refine add_le_add ?_ ?_
          · calc |(∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ)|
                ≤ |∫ θ in a..b, Ψ (z + 1) θ| + |∫ θ in a..b, Ψ z θ| := by
                  simpa using abs_sub_le (∫ θ in a..b, Ψ (z + 1) θ) (0 : ℝ) (∫ θ in a..b, Ψ z θ)
              _ ≤ M₁ * (Real.pi / 2) + M * (Real.pi / 2) := add_le_add hZ1 hZ0
          · have hmain : |∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| ≤ c := by
              have h := intervalIntegral.norm_integral_le_of_norm_le_const
                (f := fun t => (∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                  - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) (a := z) (b := z + 1) (C := c)
                (fun t ht => by
                  rw [Real.norm_eq_abs]
                  rw [Set.uIoc_of_le (by linarith : z ≤ z + 1)] at ht
                  exact hB t ⟨le_of_lt ht.1, ht.2⟩)
              simpa only [Real.norm_eq_abs, show (z + 1) - z = 1 from by ring, abs_one,
                mul_one] using h
            exact hmain
      _ = (Real.pi / 2) * (M + M₁) + c := by ring
  -- the per-`b` bound
  set K : ℝ := |Real.tan a * Ψ z a| + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
      + (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) + (1 / 2) * (QF + Real.pi / 2)
      + 2 * M + 6 * (M * (Real.pi / 2)) with hKdef
  have key : ∀ b ∈ Set.Ioo a (Real.pi / 2), |Real.tan b * Ψ z b| ≤ K := by
    intro b hb
    rw [hKdef]
    have hab' : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro θ hθ
      rw [Set.uIcc_of_le (le_of_lt hb.1)] at hθ
      exact ⟨lt_of_lt_of_le ha_pos hθ.1, lt_of_le_of_lt hθ.2 hb.2⟩
    have hFint : IntervalIntegrable (fun θ => F z θ) volume a b :=
      (hFcont.mono hab').intervalIntegrable
    have hcontp : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice (Work.Spaces.pzIter 2 Ψ) hz (n := 1) (hpz2cd.of_le (by norm_num))
      exact h2.continuousOn.mono hab'
    have hpI : IntervalIntegrable (fun θ => Work.Spaces.pzIter 2 Ψ z θ) volume a b :=
      hcontp.intervalIntegrable
    have hcontq : ContinuousOn (fun θ => Work.Spaces.pz Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice (Work.Spaces.pz Ψ) hz (n := 1) hpz1c
      exact h2.continuousOn.mono hab'
    have hqI : IntervalIntegrable (fun θ => Work.Spaces.pz Ψ z θ) volume a b :=
      hcontq.intervalIntegrable
    have hcontψ : ContinuousOn (fun θ => Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 0 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice Ψ hz (n := 0) (hsm 0)
      exact h2.continuousOn.mono hab'
    have hψI : IntervalIntegrable (fun θ => Ψ z θ) volume a b := hcontψ.intervalIntegrable
    have hslice1 : ContDiffOn ℝ 1 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (n := 1) (hsm 1)
    have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (n := 2) (hsm 2)
    have hcontp2 : ContinuousOn (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
        (Set.uIcc a b) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h2 : ContDiffOn ℝ 0 (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact h2.continuousOn.mono hab'
    have hp2I : IntervalIntegrable (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
        volume a b := hcontp2.intervalIntegrable
    have htansm : ContDiffOn ℝ 2 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContDiffOn ℝ (2 : WithTop ℕ∞) (fun θ => Real.sin θ / Real.cos θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn)
          (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))
      have htanfun : Real.tan = fun θ : ℝ => Real.sin θ / Real.cos θ :=
        funext Real.tan_eq_sin_div_cos
      rw [htanfun]
      exact h
    have htw : ContDiffOn ℝ 2 (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      htansm.mul hslice2
    have hconttw : ContinuousOn (deriv (fun θ => Real.tan θ * Ψ z θ)) (Set.uIcc a b) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ => Real.tan θ * Ψ z θ))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact h1.continuousOn.mono hab'
    have htwI : IntervalIntegrable (deriv (fun θ => Real.tan θ * Ψ z θ)) volume a b :=
      hconttw.intervalIntegrable
    -- the derivative facts for the three functions of `TanSliceFTC`
    have hdu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
      fun θ hθ => (hslice1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hdu1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (deriv (fun θ' => Ψ z θ')) θ := by
      intro θ hθ
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact (h1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hdtw : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (fun θ' => Real.tan θ' * Ψ z θ') θ :=
      fun θ hθ => (htw.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    -- the amplitude `A` of the `tan`-identity, and its `(a,b)`-integral
    set A : ℝ → ℝ := fun θ => α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      + α * (5 + α) * z * Work.Spaces.pz Ψ z θ + F z θ with hAdef
    have hAI : IntervalIntegrable A volume a b := by
      rw [hAdef]
      exact ((hpI.const_mul (α ^ 2 * z ^ 2)).add (hqI.const_mul (α * (5 + α) * z))).add hFint
    have hsplit : (∫ θ in a..b, A θ)
        = (α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          + (∫ θ in a..b, F z θ) := by
      rw [hAdef]
      rw [intervalIntegral.integral_add
        ((hpI.const_mul (α ^ 2 * z ^ 2)).add (hqI.const_mul (α * (5 + α) * z))) hFint]
      rw [intervalIntegral.integral_add (hpI.const_mul (α ^ 2 * z ^ 2))
        (hqI.const_mul (α * (5 + α) * z))]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    -- the `tan`-identity
    have heq : ∀ θ ∈ Set.Ioo a b, deriv (fun t => Real.tan t * Ψ z t) θ
        = A θ + deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ + 6 * Ψ z θ := by
      intro θ hθ
      have hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, ha_pos], by linarith [hθ.2, hb.2]⟩
      have hb' := heq z hz θ hθo.1 hθo.2
      rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb'
      rw [hAdef]
      simp only [pthIter_two_eq_fun Ψ, Work.Spaces.pth] at hb' ⊢
      linear_combination (norm := ring_nf) hb'
    have hid := TanSliceFTC (u := fun θ => Ψ z θ) (A := A) (a := a) (b := b) (le_of_lt hb.1)
      (fun θ hθ => (hdu θ (hab' hθ)).hasDerivAt)
      (fun θ hθ => (hdu1 θ (hab' hθ)).hasDerivAt)
      (fun θ hθ => (hdtw θ (hab' hθ)).hasDerivAt)
      hp2I htwI hAI hψI heq
    -- the individual bounds
    have htanb : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
        ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
        (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) hp_int)
    have hqbound : |∫ θ in a..b, Work.Spaces.pz Ψ z θ| ≤ (Real.pi / 2) * (M + M₁) + c :=
      hPb b hb
    have htanF : |∫ θ in a..b, F z θ| ≤ (1 / 2) * (QF + Real.pi / 2) :=
      le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
        (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) hF_int)
    have hψbd : |∫ θ in a..b, Ψ z θ| ≤ M * (Real.pi / 2) := by
      have hmain : |∫ θ in a..b, Ψ z θ| ≤ M * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ z θ) (a := a) (b := b) (C := M) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact (hMb θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩).2)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hMpos.le)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hderivbd : |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a| ≤ 2 * M := by
      have h1 : |deriv (fun θ => Ψ z θ) b| ≤ M :=
        (hMb b ⟨lt_trans ha_pos hb.1, hb.2⟩).1
      have h2 : |deriv (fun θ => Ψ z θ) a| ≤ M :=
        (hMb a ⟨ha_pos, ha_lt⟩).1
      have htri : |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          ≤ |deriv (fun θ => Ψ z θ) b| + |deriv (fun θ => Ψ z θ) a| := by
        have := abs_sub_le (deriv (fun θ => Ψ z θ) b) 0 (deriv (fun θ => Ψ z θ) a)
        simpa using this
      linarith
    -- the `tan`-identity solved for the left-hand side
    have hid' : Real.tan b * Ψ z b
        = Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
          + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
          + 6 * ∫ θ in a..b, Ψ z θ := by linarith [hid]
    -- the `(a,b)`-integral of the amplitude
    have hAbound : |∫ θ in a..b, A θ| ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
        + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
        + (1 / 2) * (QF + Real.pi / 2) := by
      rw [hsplit]
      have htri : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          + (∫ θ in a..b, F z θ)|
          ≤ |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            + |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            + |∫ θ in a..b, F z θ| := by
        have h2 := abs_add_le ((α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) (∫ θ in a..b, F z θ)
        have h1 := abs_add_le ((α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ))
          ((α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ))
        linarith
      have hbd : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            + |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            + |∫ θ in a..b, F z θ| ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
              + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
              + (1 / 2) * (QF + Real.pi / 2) := by
        have h1 : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (le_trans
            (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
            (Ioc_abs_le_half (g := fun θ => Work.Spaces.pzIter 2 Ψ z θ) ha_pos hb.2
              (le_of_lt hb.1) hp_int)) (by positivity)
        have h2 : |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            ≤ (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c) := by
          have hc2 : 0 ≤ α * (5 + α) * z :=
            mul_nonneg (mul_nonneg hαpos.le (by linarith [hαpos])) hz.le
          rw [abs_mul, abs_of_nonneg hc2]
          exact mul_le_mul_of_nonneg_left (hPb b hb) hc2
        have h3 : |∫ θ in a..b, F z θ| ≤ (1 / 2) * (QF + Real.pi / 2) :=
          le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
            (Ioc_abs_le_half (g := fun θ => F z θ) ha_pos hb.2 (le_of_lt hb.1) hF_int)
        linarith
      linarith
    rw [hid']
    have htri : |Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
        + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
        + 6 * ∫ θ in a..b, Ψ z θ|
        ≤ |Real.tan a * Ψ z a| + |∫ θ in a..b, A θ|
          + |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          + |6 * ∫ θ in a..b, Ψ z θ| := by
      have h1 := abs_add_le (Real.tan a * Ψ z a) (∫ θ in a..b, A θ)
      have h2 := abs_add_le (Real.tan a * Ψ z a + (∫ θ in a..b, A θ))
        (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
      have h3 := abs_add_le (Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
        + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a))
        (6 * ∫ θ in a..b, Ψ z θ)
      exact le_trans h3 (le_trans (add_le_add h2 le_rfl)
        (add_le_add (add_le_add h1 le_rfl) le_rfl))
    have hfin : |Real.tan a * Ψ z a| + |∫ θ in a..b, A θ|
          + |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          + |6 * ∫ θ in a..b, Ψ z θ|
        ≤ |Real.tan a * Ψ z a|
          + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
          + (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
          + (1 / 2) * (QF + Real.pi / 2) + 2 * M + 6 * (M * (Real.pi / 2)) := by
      have h6 : |6 * ∫ θ in a..b, Ψ z θ| = 6 * |∫ θ in a..b, Ψ z θ| := by
        rw [abs_mul]; norm_num
      have h6b : 6 * |∫ θ in a..b, Ψ z θ| ≤ 6 * (M * (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left hψbd (by norm_num)
      rw [h6]
      linarith [hAbound, hderivbd, h6b]
    linarith
  -- the squeeze
  have hKlim : Tendsto (fun θ => K / Real.tan θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hcos : Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := (Real.continuous_cos.continuousAt (x := Real.pi / 2)).tendsto
      have h' : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) := inf_le_left
      simpa [Real.cos_pi_div_two] using h.mono_left h'
    have hsin : Tendsto Real.sin (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
      have h := (Real.continuous_sin.continuousAt (x := Real.pi / 2)).tendsto
      have h' : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) := inf_le_left
      simpa [Real.sin_pi_div_two] using h.mono_left h'
    have h2 : Tendsto (fun θ => K * Real.cos θ / Real.sin θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h1 : Tendsto (fun θ => K * Real.cos θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using (tendsto_const_nhds.mul hcos)
      have := h1.div hsin one_ne_zero
      rw [show (0 : ℝ) / 1 = 0 from by norm_num] at this
      exact this
    refine Tendsto.congr' ?_ h2
    filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
    have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [ha_pos, hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
    have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ha_pos, hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hKnn : 0 ≤ K := by
    have hb0 : (a + Real.pi / 2) / 2 ∈ Set.Ioo a (Real.pi / 2) :=
      ⟨by linarith, by linarith⟩
    exact le_trans (abs_nonneg _) (key _ hb0)
  have hTend : Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hKlim
    filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
    have htanpos : 0 < Real.tan θ :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [ha_pos, hθ.1]) hθ.2
    rw [le_div_iff₀ htanpos]
    calc ‖Ψ z θ‖ * Real.tan θ = |Real.tan θ * Ψ z θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos htanpos, mul_comm]
      _ ≤ K := key θ hθ
  refine ⟨hTend, 2 * K, by linarith, ?_⟩
  -- the rate: `|Ψ z θ| ≤ K/tan θ` and `1/tan θ = cos θ/sin θ ≤ 2(π/2-θ)` on `(π/4, π/2)`
  filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
  have htanpos : 0 < Real.tan θ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [ha_pos, hθ.1]) hθ.2
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ha_pos, hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsinhalf : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h := Real.monotoneOn_sin (a := Real.pi / 6) (b := θ)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos, ha_pos, hθ.1], le_of_lt hθ.2⟩
      (by linarith [Real.pi_pos, ha_pos, hθ.1])
    rwa [Real.sin_pi_div_six] at h
  have hdiv : Real.cos θ / Real.sin θ ≤ 2 * (Real.pi / 2 - θ) := by
    have hcos : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
    have h1 : Real.sin (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := Real.sin_le (by linarith [hθ.2])
    have ht0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have h2 : (1 : ℝ) ≤ 2 * Real.sin θ := by linarith
    rw [div_le_iff₀ hsinpos]
    calc Real.cos θ = Real.sin (Real.pi / 2 - θ) := hcos
      _ ≤ Real.pi / 2 - θ := h1
      _ = (Real.pi / 2 - θ) * 1 := by ring
      _ ≤ (Real.pi / 2 - θ) * (2 * Real.sin θ) := mul_le_mul_of_nonneg_left h2 ht0
      _ = 2 * (Real.pi / 2 - θ) * Real.sin θ := by ring
  have htan_eq : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hu : |Ψ z θ| ≤ K / Real.tan θ := by
    rw [le_div_iff₀ htanpos]
    calc |Ψ z θ| * Real.tan θ = |Real.tan θ| * |Ψ z θ| := by
          rw [abs_of_pos htanpos, mul_comm]
      _ = |Real.tan θ * Ψ z θ| := (abs_mul _ _).symm
      _ ≤ K := key θ hθ
  calc |Ψ z θ| ≤ K / Real.tan θ := hu
    _ = K * (Real.cos θ / Real.sin θ) := by
        rw [htan_eq]
        field_simp
    _ ≤ K * (2 * (Real.pi / 2 - θ)) := mul_le_mul_of_nonneg_left hdiv hKnn
    _ = (2 * K) * (Real.pi / 2 - θ) := by ring

/-- **The right-endpoint behaviour of the `θ`-slices in the almost-everywhere class.** -/
theorem AeSliceRightTendsto : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G → ∀ z, 0 < z →
      Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro α u G h z hz
  exact (sliceRightTendsto_raw α G u h.hα h.hα4 h.eq h.smooth h.memG h.memRad2 h.memAng2
    z hz).1

end Work.FTS.EllipticEst.H2W.Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.Bridges =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bridges between the Bochner norm `HkSq` and its `∫⁻`-form

`HkSq α 0 g` is the iterated *Bochner* integral of `(g·w/σ^{1/2})²`.  Under the honesty
hypothesis `HkMem α 0 g` this is the honest value, and the identity

`ENNReal.ofReal (HkSq α 0 g) = ∫⁻_z ofReal (w z²) · (∫⁻_θ ofReal (g² σ))`

holds.  This is the form in which the `σ`-Poincaré upgrade (`AeSigmaUpgradeU_all`) and the
cut-off energy inequality are stated, so it is the bridge that lets the final arithmetic be done
in `ENNReal` and converted to the Bochner statement only at the very end.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

set_option autoImplicit false

/-- `σ θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.Spaces.Iθ] at hθ
  refine Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) ?_) _
  linarith [hθ.2, Real.pi_pos]

/-- **`HkSq α 0 g` as an `∫⁻`-integral**, for an honest `g`. -/
theorem ofReal_HkSq_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 0 g) :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 g)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have hHk : Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ := rfl
  rw [hHk]
  -- ## the outer bridge
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) :=
    Filter.Eventually.of_forall (fun z =>
      MeasureTheory.integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ))
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2 hnn]
  -- ## the inner bridge, a.e. in `z`
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  have hslice : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 g z θ) Work.Spaces.Iθ := hmem.1 z hz
  have hnnθ : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 0 g z θ) :=
    Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hslice hnnθ]
  -- the constant `ofReal (w z²)` is pulled out of the inner `∫⁻`
  rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)) _
    ENNReal.ofReal_ne_top]
  -- the two inner integrands agree a.e. on `Iθ`
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hsEta : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ hθ
  have hsq : 0 ≤ (g z θ) ^ 2 := sq_nonneg _
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq_Iθ α g hθ,
    show (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from by ring,
    ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z)), ENNReal.ofReal_mul hsq]

end Work.FTS.EllipticEst.H2W.AeProof.ae
end
end
-- ===== merged: Submission.Work.H2W.momentChainAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2W

/-- **A continuous function vanishing almost everywhere is zero.**  (The `a.e.` moment
conditions of the current `TT.EllWeakPos` are upgraded to pointwise ones with this.) -/
theorem ae_zero_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), f z = 0) :
    ∀ z, 0 < z → f z = 0 := by
  have h' : f =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] (fun _ : ℝ => 0) := by
    filter_upwards [h] with z hz
    simpa using hz
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := MeasureTheory.volume) h' isOpen_Ioi hf
    continuousOn_const
  intro z hz
  exact heq hz

end Work.H2W

namespace Work.H2W.MomentAe

open Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-- A point of `Iθ` is almost everywhere interior (the two endpoints are null). -/
theorem ae_Ioo_mem : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    rw [Set.mem_setOf_eq] at hθ
    push_neg at hθ
    obtain ⟨hmem, hnot⟩ := hθ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h0 : θ = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      by_contra hpi
      exact hnot ⟨lt_of_le_of_ne hmem.1 (Ne.symm h0), lt_of_le_of_ne hmem.2 hpi⟩
  · have hset : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton _)

/-! ## 1. Basic identities -/

/-- `F_*(D_z f)(z) = z · F_*(∂_z f)(z)`, for every function `f` and every `z`. -/
theorem Fstar_Dz_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Spaces.Dz f) z
      = z * Work.Elliptic.Fstar (Work.Spaces.pz f) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Spaces.Dz f z θ * sg θ)
      = fun θ : ℝ => z * (Work.Spaces.pz f z θ * sg θ) from by
    funext θ; simp only [Work.Spaces.Dz]; ring]
  rw [MeasureTheory.integral_const_mul]

/-- `z² ∂_z² f = D_z² f − D_z f` on the open quadrant. -/
theorem zsq_pzIter2_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.Dz f z θ :=
  Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open f hf hz hθ

/-- `D_z^j (z² ∂_z² f) = D_z^{j+2} f − D_z^{j+1} f` on the open quadrant. -/
theorem DzIter_zsq_pzIter2_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ
      = Work.Spaces.DzIter (j + 2) f z θ - Work.Spaces.DzIter (j + 1) f z θ := by
  have h1 := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open f
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n) j 0 hz hθ
  simp only [Work.Spaces.mixed_zero_right] at h1
  have h2 := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (Work.Spaces.DzIter j f)
    (hf.DzIter j) hz hθ
  rw [← h1, h2]
  rw [show Work.Spaces.DzIter 2 (Work.Spaces.DzIter j f) = Work.Spaces.DzIter (j + 2) f from
    (Work.Spaces.DzIter_add_right 2 j f).symm.trans (by rw [Nat.add_comm])]
  rw [show Work.Spaces.Dz (Work.Spaces.DzIter j f) = Work.Spaces.DzIter (j + 1) f from
    (Work.Spaces.DzIter_add_right 1 j f).symm.trans (by rw [Nat.add_comm])]

/-- `D_z³ f = D_z² f + D_z (z² ∂_z² f)` on the open quadrant. -/
theorem DzIter_three_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 3 f z θ
      = Work.Spaces.DzIter 2 f z θ
        + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ := by
  have h := DzIter_zsq_pzIter2_eq hf 1 hz hθ
  rw [show (1 + 2 : ℕ) = 3 from rfl, show (1 + 1 : ℕ) = 2 from rfl] at h
  linarith [h]

/-- `z² ∂_z² Ψ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_zsq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  rw [show Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 from rfl]
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul
    ((hΨ.pzIter 2).forall n)

/-! ## 2. Weighted angular energies and slice integrability -/

/-- `AngSq g u = ∫_θ (g u θ)² sin(2θ)^{-η}`, the `θ`-energy of the slot `g` at radius `u`. -/
def AngSq (g : ℝ → ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ θ in Iθ, (g u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

theorem AngSq_nonneg (g : ℝ → ℝ → ℝ) (u : ℝ) : 0 ≤ AngSq g u := by
  rw [AngSq]
  refine integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)

/-- The angular slice of a weighted `D_z`-slot of an `ℋ^k`-function, without the radial
weight: `θ ↦ (D_z^i g u θ)² sin(2θ)^{-η}` is integrable on `Iθ` for every `u > 0`. -/
theorem slot_slice_integrableOn {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ := by
  have hI : IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ
      * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Iθ :=
    Work.FTS.EllipticEst.integrableOn_zSummand α k hs hm i hi (Set.mem_Ici.mpr hu.le)
  have hwu : Work.Spaces.w u ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (Work.FTS.EllipticEst.one_le_w hu))
  have hWu : (Work.Spaces.w u) ^ 2 ≠ 0 := pow_ne_zero 2 hwu
  refine ((hI.mul_const ((Work.Spaces.w u) ^ 2)⁻¹).congr ?_)
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [div_eq_mul_inv]
  show (Work.Spaces.DzIter i g u θ * Wf u θ) ^ 2 / (Work.Spaces.w u) ^ 2
      = (Work.Spaces.DzIter i g u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  rw [div_eq_mul_inv, mul_pow, Wf_sq_eq (sin_two_nonneg hθ)]
  rw [show rho θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
  field_simp [hwu, hWu]

/-- The `θ`-energy of a slot is `z`-locally integrable, with the extra radial weight
`w²`: `u ↦ (∫_θ (D_z^i g u θ)² sin(2θ)^{-η}) · w(u)²` is integrable on `(a,b]`. -/
theorem slot_Iz_integrableOn {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u => AngSq (Work.Spaces.DzIter i g) u * (Work.Spaces.w u) ^ 2)
      (Set.Ioc a b) := by
  have hIz : IntegrableOn (fun u => ∫ θ in Iθ, (Work.Spaces.DzIter i g u θ
      * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz :=
    Work.FTS.EllipticEst.integrableOn_slice_Iz α k hs hm i hi
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iz := fun u hu =>
    Set.mem_Ici.mpr (le_of_lt (lt_trans ha hu.1))
  refine (hIz.mono_set hsub).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u _
  rw [AngSq, ← MeasureTheory.integral_mul_const (Work.Spaces.w u ^ 2)
    (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  show (Work.Spaces.DzIter i g u θ * Wf u θ) ^ 2
      = ((Work.Spaces.DzIter i g u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * (Work.Spaces.w u) ^ 2
  rw [mul_pow, Wf_sq_eq (sin_two_nonneg hθ)]
  rw [show rho θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
  ring

/-- The `θ`-energy `u ↦ AngSq g u` of a function `C^∞` on the open quadrant is a.e. strongly
measurable (Fubini applied to the continuous joint integrand). -/
theorem aesm_AngSq {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun u => AngSq g u) (volume.restrict (Set.Ioc a b)) := by
  have hs : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 :=
    (hs.continuousOn.pow 2).mul hw
  have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont ha).integral_prod_right'
    (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict Iθ)
  simpa only [Function.uncurry_apply_pair, AngSq] using h

/-- The Young/AM--GM bound with the angular weight, in integrated form: `|g|σ` is bounded by
the weighted `L²`-energy of `g` plus an absolute constant. -/
theorem abs_moment_le_energy {g : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict Iθ))
    (hg : IntegrableOn (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ) :
    IntegrableOn (fun θ => g θ * sg θ) Iθ ∧
      ∫ θ in Iθ, |g θ| * sg θ
        ≤ 1 + ∫ θ in Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ sg θ := fun θ hθ => by
    show 0 ≤ Real.sin θ * Real.cos θ ^ 2
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
  have hσle : ∀ θ ∈ Iθ, sg θ ≤ 1 := fun θ hθ => by
    show Real.sin θ * Real.cos θ ^ 2 ≤ 1
    have hs := Real.sin_le_one θ
    have hc : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one θ]
    have hs0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul hs hc (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hσcont : Continuous sg := by unfold Work.Elliptic.sinCos2; fun_prop
  have hσint : IntegrableOn sg Iθ := hσcont.continuousOn.integrableOn_compact isCompact_Icc
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- the `θ`-mass of `Iθ` is `π/2`
  have hvol : ∫ θ in Iθ, (1 : ℝ) = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    simp
  have hσmass : ∫ θ in Iθ, sg θ ≤ Real.pi / 2 := by
    rw [← hvol]
    exact MeasureTheory.integral_mono_ae hσint hone
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hσle θ hθ))
  -- the pointwise weighted Young bound
  have hpt : ∀ θ ∈ Iθ, |g θ| * sg θ
      ≤ (g θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (1 / 2) + sg θ * (1 / 2) := by
    intro θ hθ
    rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hs | hs
    · -- `sin(2θ) = 0`: both sides vanish
      have hσ0 : sg θ = 0 := by
        have h3 : Real.sin θ * Real.cos θ = 0 := by
          have h4 := Real.sin_two_mul θ
          rw [← hs] at h4
          linarith
        rcases mul_eq_zero.mp h3 with h | h
        · rw [Work.Elliptic.sinCos2, h]; ring
        · rw [Work.Elliptic.sinCos2, h]; ring
      have hr0 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
        rw [← hs]; exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
      rw [hσ0, hr0]
      simp
    · have hsle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hr1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        have h2 := Real.rpow_le_rpow_of_nonpos hs hsle
          (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≤ 0)
        rwa [Real.one_rpow] at h2
      have hσ0 := hσnn θ hθ
      have hσ1 := hσle θ hθ
      have h1 : 2 * (|g θ| * sg θ) ≤ g θ ^ 2 + sg θ ^ 2 := by
        nlinarith [sq_nonneg (|g θ| - sg θ), sq_abs (g θ)]
      have ha : g θ ^ 2 ≤ g θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        nlinarith [sq_nonneg (g θ), hr1]
      have hb : sg θ ^ 2 ≤ sg θ := by nlinarith
      linarith
  have hdom : IntegrableOn (fun θ =>
      (g θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (1 / 2) + sg θ * (1 / 2)) Iθ :=
    (hg.mul_const (1 / 2)).add (hσint.mul_const (1 / 2))
  have hsl : IntegrableOn (fun θ => g θ * sg θ) Iθ := by
    refine Integrable.mono' hdom (hgm.mul hσcont.aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn θ hθ)]
    exact hpt θ hθ
  refine ⟨hsl, ?_⟩
  have hsl' : Integrable (fun θ => |g θ| * sg θ) (volume.restrict Iθ) :=
    hsl.norm.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn θ hθ)]))
  have hmono : ∫ θ in Iθ, |g θ| * sg θ
      ≤ ∫ θ in Iθ, ((g θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (1 / 2)
          + sg θ * (1 / 2)) :=
    MeasureTheory.integral_mono_ae hsl' hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hσnn θ hθ))]
        exact hpt θ hθ))
  rw [MeasureTheory.integral_add (hg.mul_const (1 / 2)) (hσint.mul_const (1 / 2)),
    MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const] at hmono
  have hE0 : 0 ≤ ∫ θ in Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)))
  linarith [hmono, hσmass, hE0, Real.pi_lt_four]

/-! ## 3. Product integrability of a divided slot from a fibre bound -/

/-- If the fibres `θ ↦ f r θ` are integrable with `∫_θ |f r θ| ≤ B r` and `B` is integrable
on `(s,z]`, then `(r,θ) ↦ f r θ / r` is integrable on `(s,z] × Iθ`. -/
theorem integrable_uncurry_div_of_fibre_bound {f : ℝ → ℝ → ℝ} {B : ℝ → ℝ} {s z : ℝ}
    (hs : 0 < s) (hsz : s ≤ z)
    (hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Iθ)))
    (hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ => f r θ) Iθ)
    (hle : ∀ r ∈ Set.Ioc s z, ∫ θ in Iθ, |f r θ| ≤ B r)
    (hB : IntegrableOn B (Set.Ioc s z)) :
    Integrable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Iθ)) := by
  haveI : SFinite (volume.restrict (Set.Ioc s z)) := inferInstance
  haveI : SFinite (volume.restrict Iθ) := inferInstance
  have hbox : MeasurableSet (Set.Ioc s z ×ˢ Iθ) := measurableSet_Ioc.prod measurableSet_Icc
  have hG : Integrable (Function.uncurry (fun r θ : ℝ => |f r θ / r|))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Iθ)) := by
    refine (Work.Spaces.integrable_prod_of_iterated (μ := volume.restrict (Set.Ioc s z))
      (ν := volume.restrict Iθ) (G := fun r θ => |f r θ / r|)
      (fun a b => abs_nonneg _) ?_ ?_ ?_).1
    · exact hae.norm.congr (Filter.Eventually.of_forall fun p => by
        simp only [Function.uncurry, Real.norm_eq_abs])
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
      have hr0 : 0 < r := lt_trans hs hr.1
      exact (((hfib r hr).norm.const_mul r⁻¹).congr
        (Filter.Eventually.of_forall fun θ => by
          simp only [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hr0)]
          ring))
    · refine (hB.const_mul s⁻¹).mono' ?_ ?_
      · exact (hae.norm.integral_prod_right'
          (μ := volume.restrict (Set.Ioc s z)) (ν := volume.restrict Iθ)).congr
          (Filter.Eventually.of_forall fun r => by
            simp only [Function.uncurry, Real.norm_eq_abs])
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
        have hr0 : 0 < r := lt_trans hs hr.1
        have hBnn : 0 ≤ B r := le_trans (integral_nonneg fun θ => abs_nonneg _) (hle r hr)
        rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
        have h1 : ∫ θ in Iθ, |f r θ / r| = (∫ θ in Iθ, |f r θ|) / r := by
          rw [← MeasureTheory.integral_div]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
          rw [abs_div, abs_of_pos hr0]
        rw [h1]
        have hstep1 : (∫ θ in Iθ, |f r θ|) / r ≤ B r / r :=
          div_le_div_of_nonneg_right (hle r hr) (le_of_lt hr0)
        have hstep2 : B r / r ≤ s⁻¹ * B r := by
          rw [div_eq_mul_inv, mul_comm (B r)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hs (le_of_lt hr.1)) hBnn
        exact le_trans hstep1 hstep2
  refine (MeasureTheory.integrable_norm_iff hae).mp ?_
  exact hG.congr (Filter.Eventually.of_forall fun p => by
    simp only [Function.uncurry, Real.norm_eq_abs])

/-! ## 4. Slice control at level `i ≤ 2` -/

/-- The bound function for the slices of `D_z^i Ψ`, `i ≤ 2`: the endpoint data at `π/4` and the
weighted `L²`-energy of the second `θ`-derivative (with the constants produced by
`sliceMomentLinear`). -/
def Bnd2 (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  4 + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
    + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
    + 2 * AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u

/-- `AngSq (pthIter 2 (D_z^i Ψ)) = AngSq (D_z^i (pthIter 2 Ψ))` for `u > 0` (the two
`θ`-integrands agree off the two endpoints of `Iθ`). -/
theorem AngSq_pthIter2_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (i : ℕ)
    (u : ℝ) (hu : 0 < u) :
    AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u
      = AngSq (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ)) u := by
  rw [AngSq, AngSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
    with θ hθI _
  have hcomm := (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i)
    (show ((u, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθI⟩)
  simp only [Function.uncurry_apply_pair] at hcomm
  rw [hcomm]

/-- The angular `L²`-integrability of the second `θ`-derivative of `D_z^i Ψ`, `i ≤ 2`. -/
theorem slice_two_energy {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (i : ℕ) (hi : i ≤ 2) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ := by
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hΨ.pth).pth
  have h1 := slot_slice_integrableOn hSB hB i hi hu
  refine h1.congr ?_
  filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
    with θ hθI _
  have hcomm := (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i)
    (show ((u, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθI⟩)
  simp only [Function.uncurry_apply_pair] at hcomm
  rw [hcomm]

/-- The `θ`-slice of a `C^∞`-on-the-open-quadrant function is `C²` there. -/
theorem contDiffOn_slice_two {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {u : ℝ} (hu : 0 < u) : ContDiffOn ℝ 2 (fun θ => g u θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (hg.curry_θ hu).of_le (by simp [Work.Stability.smoothOrder])

theorem slice_two_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2) :
    ∀ u, 0 < u → IntegrableOn (fun θ => Work.Spaces.DzIter i Ψ u θ * sg θ) Iθ := fun u hu =>
  (sliceMomentLinear (g := fun θ => Work.Spaces.DzIter i Ψ u θ)
    (contDiffOn_slice_two (hΨ.DzIter i) hu) (slice_two_energy hΨ hB i hi hu)).1

theorem slice_two_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2) :
    ∀ u, 0 < u → ∫ θ in Iθ, |Work.Spaces.DzIter i Ψ u θ| * sg θ ≤ Bnd2 Ψ i u := by
  intro u hu
  have h := (sliceMomentLinear (g := fun θ => Work.Spaces.DzIter i Ψ u θ)
    (contDiffOn_slice_two (hΨ.DzIter i) hu) (slice_two_energy hΨ hB i hi hu)).2
  have hmain : ∫ θ in Iθ, |Work.Spaces.DzIter i Ψ u θ| * sg θ
      ≤ 4 + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
        + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
        + 2 * AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u := by
    simpa only [SliceEnergy, AngSq, Work.Spaces.pth, Work.Spaces.pthIter_succ,
      Work.Spaces.pthIter_zero] using h
  rw [Bnd2]
  linarith [hmain]

theorem Bnd2_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (i : ℕ) (hi : i ≤ 2) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (Bnd2 Ψ i) (Set.Ioc a b) := by
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hΨ.pth).pth
  have hpi : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcont1 : ContinuousOn (fun u => |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|) (Set.Ioi 0) :=
    ((hΨ.DzIter i).curry_z hpi).continuousOn.abs
  have hcont2 : ContinuousOn
      (fun u => |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|) (Set.Ioi 0) :=
    (((hΨ.DzIter i).pth).curry_z hpi).continuousOn.abs
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le ha hu.1
  have hint1 : IntegrableOn (fun u => |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|) (Set.Ioc a b) :=
    ((hcont1.mono hsub).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hint2 : IntegrableOn
      (fun u => |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|) (Set.Ioc a b) :=
    ((hcont2.mono hsub).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have henergy : IntegrableOn
      (fun u => AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u) (Set.Ioc a b) := by
    have hw : IntegrableOn (fun u => AngSq (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ)) u
        * (Work.Spaces.w u) ^ 2) (Set.Ioc a b) := slot_Iz_integrableOn hSB hB i hi ha
    have hcongr : IntegrableOn (fun u => AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u
        * (Work.Spaces.w u) ^ 2) (Set.Ioc a b) :=
      hw.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => by
        show AngSq (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ)) u * (Work.Spaces.w u) ^ 2
            = AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u * (Work.Spaces.w u) ^ 2
        rw [AngSq_pthIter2_comm hΨ i u (lt_trans ha hu.1)])
    have haesm : AEStronglyMeasurable
        (fun u => AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u)
        (volume.restrict (Set.Ioc a b)) :=
      (aesm_AngSq (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (hSB.DzIter i) n) (le_of_lt ha)).congr
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun u hu =>
          (AngSq_pthIter2_comm hΨ i u (lt_trans ha hu.1)).symm)
    refine hcongr.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (AngSq_nonneg _ _)]
    have h1 : 1 ≤ (Work.Spaces.w u) ^ 2 := by
      have := Work.FTS.EllipticEst.one_le_w (lt_trans ha hu.1)
      nlinarith
    nlinarith [AngSq_nonneg (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u]
  have hone : IntegrableOn (fun _ : ℝ => (4 : ℝ)) (Set.Ioc a b) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun u => (4 : ℝ) + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 2 * AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u) (Set.Ioc a b) :=
    ((hone.add (hint1.const_mul 4)).add (hint2.const_mul 4)).add (henergy.const_mul 2)
  refine hsum.congr (Filter.Eventually.of_forall fun u => ?_)
  rw [Bnd2]

/-! ## 5. Slice control at level `3` -/

/-- The bound function for the slices of `D_z³Ψ = D_z²Ψ + D_z(z²∂_z²Ψ)`. -/
def Bnd3 (Ψ : ℝ → ℝ → ℝ) (u : ℝ) : ℝ :=
  Bnd2 Ψ 2 u + (1 + AngSq (Work.Spaces.DzIter 1
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)

theorem slice_three_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) :
    ∀ u, 0 < u → IntegrableOn (fun θ => Work.Spaces.DzIter 3 Ψ u θ * sg θ) Iθ := by
  intro u hu
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) (volume.restrict Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter 1).continuousOn hu
  have hAint := (abs_moment_le_energy hm
    (slot_slice_integrableOn hSA hA 1 (by norm_num) hu)).1
  have h := (slice_two_integrableOn hΨ hB 2 le_rfl u hu).add hAint
  refine h.congr ?_
  filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
    with θ hθI _
  simp only [Pi.add_apply]
  rw [DzIter_three_eq hΨ hu hθI]
  ring

theorem slice_three_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) :
    ∀ u, 0 < u → ∫ θ in Iθ, |Work.Spaces.DzIter 3 Ψ u θ| * sg θ ≤ Bnd3 Ψ u := by
  intro u hu
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) (volume.restrict Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter 1).continuousOn hu
  have hAint := abs_moment_le_energy hm
    (slot_slice_integrableOn hSA hA 1 (by norm_num) hu)
  have h2 := slice_two_integrableOn hΨ hB 2 le_rfl u hu
  have h2b := slice_two_bound hΨ hB 2 le_rfl u hu
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ sg θ := fun θ hθ => by
    show 0 ≤ Real.sin θ * Real.cos θ ^ 2
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
  have hpt : ∀ᵐ θ ∂(volume.restrict Iθ), |Work.Spaces.DzIter 3 Ψ u θ| * sg θ
      ≤ |Work.Spaces.DzIter 2 Ψ u θ| * sg θ
        + |Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ := by
    filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
      with θ hθI hθ
    rw [DzIter_three_eq hΨ hu hθI]
    calc |Work.Spaces.DzIter 2 Ψ u θ + Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ
        ≤ (|Work.Spaces.DzIter 2 Ψ u θ|
            + |Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ|)
            * sg θ := mul_le_mul_of_nonneg_right (abs_add_le _ _) (hσnn θ hθ)
      _ = _ := by ring_nf
  have h2' : IntegrableOn (fun θ => |Work.Spaces.DzIter 2 Ψ u θ| * sg θ) Iθ :=
    h2.norm.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn θ hθ)]))
  have hA' : IntegrableOn (fun θ => |Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ) Iθ :=
    hAint.1.norm.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn θ hθ)]))
  have h := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
      (fun θ hθ => mul_nonneg (abs_nonneg _) (hσnn θ hθ)))
    (h2'.add hA') hpt
  simp only [Pi.add_apply] at h
  rw [MeasureTheory.integral_add h2' hA'] at h
  rw [Bnd3]
  simp only [AngSq]
  have hfin : (∫ θ in Iθ, |Work.Spaces.DzIter 2 Ψ u θ| * sg θ)
      + ∫ θ in Iθ, |Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ
      ≤ Bnd2 Ψ 2 u + (1 + ∫ θ in Iθ, (Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    linarith [h2b, hAint.2]
  exact le_trans h hfin

theorem Bnd3_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (Bnd3 Ψ) (Set.Ioc a b) := by
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have h1 : IntegrableOn (Bnd2 Ψ 2) (Set.Ioc a b) := Bnd2_integrableOn hΨ hB 2 le_rfl ha
  have h2 : IntegrableOn (fun u => AngSq (Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) (Set.Ioc a b) := by
    have hw := slot_Iz_integrableOn hSA hA 1 (by norm_num) (a := a) (b := b) ha
    have haesm : AEStronglyMeasurable (fun u => AngSq (Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)
        (volume.restrict (Set.Ioc a b)) :=
      aesm_AngSq (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (hSA.DzIter 1) n) (le_of_lt ha)
    refine hw.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (AngSq_nonneg _ _)]
    have h3 : 1 ≤ (Work.Spaces.w u) ^ 2 := by
      have := Work.FTS.EllipticEst.one_le_w (lt_trans ha hu.1)
      nlinarith
    nlinarith [AngSq_nonneg (Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u]
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc a b) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have h3 : IntegrableOn (fun u => Bnd2 Ψ 2 u + (1 + AngSq (Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)) (Set.Ioc a b) :=
    h1.add (hone.add h2)
  exact h3.congr (Filter.Eventually.of_forall fun u => by simp only [Bnd3])

/-! ## 6. The uniform level bound -/

/-- The bound function for the slices of `D_z^i Ψ`, `i ≤ 3`. -/
def Bnd (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  if i ≤ 2 then Bnd2 Ψ i u else Bnd3 Ψ u

theorem level_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (i : ℕ) (hi : i ≤ 3) :
    (∀ u, 0 < u → IntegrableOn (fun θ => Work.Spaces.DzIter i Ψ u θ * sg θ) Iθ) ∧
      (∀ u, 0 < u → ∫ θ in Iθ, |Work.Spaces.DzIter i Ψ u θ| * sg θ ≤ Bnd Ψ i u) ∧
      (∀ a b, 0 < a → IntegrableOn (Bnd Ψ i) (Set.Ioc a b)) := by
  by_cases h2 : i ≤ 2
  · have h := slice_two_integrableOn hΨ hB i h2
    have h' := slice_two_bound hΨ hB i h2
    have hBeq : Bnd Ψ i = Bnd2 Ψ i := by funext u; simp only [Bnd, if_pos h2]
    refine ⟨h, fun u hu => ?_, fun a b ha => ?_⟩
    · rw [hBeq]; exact h' u hu
    · rw [hBeq]; exact Bnd2_integrableOn hΨ hB i h2 ha
  · have hi3 : i = 3 := by omega
    subst hi3
    have h := slice_three_integrableOn hΨ hA hB
    have h' := slice_three_bound hΨ hA hB
    have hBeq : Bnd Ψ 3 = Bnd3 Ψ := by
      funext u; simp only [Bnd, if_neg (by omega : ¬ (3:ℕ) ≤ 2)]
    refine ⟨h, fun u hu => ?_, fun a b ha => ?_⟩
    · rw [hBeq]; exact h' u hu
    · rw [hBeq]; exact Bnd3_integrableOn hΨ hA hB ha

/-! ## 7. The chain rule and continuity for the moments -/

/-- The fundamental theorem of calculus along a radial slice, for a function `C^∞` on the open
quadrant: `f z θ - f s θ = ∫_s^z ∂_z f (r,θ) dr` for `0 < s ≤ z` and `θ ∈ (0,π/2)`. -/
theorem slice_FTC_open {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {s z θ : ℝ} (hs : 0 < s) (hsz : s ≤ z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    f z θ - f s θ = ∫ r in s..z, Work.Spaces.pz f r θ := by
  have hcont : ContinuousOn (fun r : ℝ => Work.Spaces.pz f r θ) (Set.uIcc s z) := by
    rw [Set.uIcc_of_le hsz]
    exact ((hf.pz.curry_z hθ).continuousOn).mono (fun r hr => lt_of_lt_of_le hs hr.1)
  have hderiv : ∀ r ∈ Set.uIcc s z,
      HasDerivAt (fun r : ℝ => f r θ) (Work.Spaces.pz f r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hsz] at hr
    exact hf.hasDerivAt_slice hθ (lt_of_lt_of_le hs hr.1)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable).symm

/-- **The primitive chain rule for the angular moment.**  From the two endpoint slice
integrabilities and the box integrability of `(r,θ) ↦ ∂_z f (r,θ) · sinθcos²θ`, the moment
`F_* f` is an antiderivative of `F_*(∂_z f)`:
`F_* f z − F_* f s = ∫_r in s..z F_*(∂_z f) r` for `0 < s ≤ z`. -/
theorem Fstar_sub_eq_integral {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z)
    (hsl_s : IntegrableOn (fun θ => f s θ * sg θ) Iθ)
    (hsl_z : IntegrableOn (fun θ => f z θ * sg θ) Iθ)
    (hbox : MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * sg θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Iθ))) :
    Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := by
  rcases eq_or_lt_of_le hsz with hsz0 | hszlt
  · rw [← hsz0, sub_self, intervalIntegral.integral_same]
  -- Step 1: the difference of the two moments as a single angular integral
  have h1 : Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ θ in Iθ, (f z θ - f s θ) * sg θ := by
    simp only [Work.Elliptic.Fstar]
    rw [show (fun θ : ℝ => (f z θ - f s θ) * sg θ)
        = fun θ => f z θ * sg θ - f s θ * sg θ from by funext θ; ring]
    rw [MeasureTheory.integral_sub hsl_z hsl_s]
  -- Step 2: the radial FTC on the angular slice, for a.e. angle
  have h2 : ∫ θ in Iθ, (f z θ - f s θ) * sg θ
      = ∫ θ in Iθ, (∫ r in s..z, Work.Spaces.pz f r θ) * sg θ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_Ioo_mem] with θ hθ
    rw [slice_FTC_open hf hs hsz hθ]
  -- Step 3: pull the angular weight out of the radial integral
  have h3 : ∫ θ in Iθ, (∫ r in s..z, Work.Spaces.pz f r θ) * sg θ
      = ∫ θ in Iθ, ∫ r in s..z, Work.Spaces.pz f r θ * sg θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    exact (intervalIntegral.integral_mul_const (sg θ) (fun r => Work.Spaces.pz f r θ)).symm
  -- Step 4: Fubini
  have h4 : ∫ θ in Iθ, ∫ r in s..z, Work.Spaces.pz f r θ * sg θ
      = ∫ r in s..z, ∫ θ in Iθ, Work.Spaces.pz f r θ * sg θ := by
    refine (MeasureTheory.intervalIntegral_integral_swap (a := s) (b := z)
      (μ := MeasureTheory.volume.restrict Iθ)
      (f := fun r θ => Work.Spaces.pz f r θ * sg θ) ?_).symm
    simpa only [Set.uIoc_of_le hsz] using hbox
  calc Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ θ in Iθ, (f z θ - f s θ) * sg θ := h1
    _ = ∫ θ in Iθ, (∫ r in s..z, Work.Spaces.pz f r θ) * sg θ := h2
    _ = ∫ θ in Iθ, ∫ r in s..z, Work.Spaces.pz f r θ * sg θ := h3
    _ = ∫ r in s..z, ∫ θ in Iθ, Work.Spaces.pz f r θ * sg θ := h4
    _ = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := rfl

/-- `∂_z²(D_z^j Ψ) = D_z^j(z²∂_z²Ψ)/u²` on the open quadrant. -/
theorem pz2_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) {u θ : ℝ}
    (hu : 0 < u) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u θ
      = Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ / u ^ 2 := by
  have h := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open Ψ
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ n) j 0 hu hθ
  simp only [Work.Spaces.mixed_zero_right] at h
  have hu0 : u ≠ 0 := ne_of_gt hu
  rw [show Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) u θ
      = Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u θ from rfl] at h
  rw [eq_div_iff (pow_ne_zero 2 hu0), mul_comm]
  exact h

/-- The absolute moment of `∂_z²(D_z^j Ψ)` is controlled by the weighted `L²`-slot of
`z²∂_z²Ψ`. -/
theorem abs_pz2_le_energy {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hAmem : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (j : ℕ) (hj : j ≤ 2) :
    ∀ u, 0 < u → ∫ θ in Iθ, |Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u θ| * sg θ
      ≤ (1 + AngSq (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) / u ^ 2 := by
  intro u hu
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter j
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) (volume.restrict Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter j).continuousOn hu
  have hb := abs_moment_le_energy hm (slot_slice_integrableOn hSA hAmem j hj hu)
  calc ∫ θ in Iθ, |Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u θ| * sg θ
      = ∫ θ in Iθ, (|Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ) / u ^ 2 := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
          with θ hθI _
        rw [pz2_eq hΨ j hu hθI, div_eq_mul_inv, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hu) 2))]
        ring
    _ = (∫ θ in Iθ, |Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ) / u ^ 2 :=
        MeasureTheory.integral_div (u ^ 2) _
    _ ≤ (1 + AngSq (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) / u ^ 2 :=
        div_le_div_of_nonneg_right hb.2 (by positivity)

theorem level_chain {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (j : ℕ) (hj : j ≤ 2) :
    ∀ s w, 0 < s → s ≤ w →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) w
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) s
      = ∫ r in s..w, Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r := by
  intro s w hs hsw
  have hSj : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ) := hΨ.DzIter j
  have hlevj := level_bound hΨ hA hB j (by omega)
  have hlevj1 := level_bound hΨ hA hB (j + 1) (by omega)
  have hsg : ContinuousOn (fun p : ℝ × ℝ => sg p.2) Work.FTS.EllipticEst.Q0 := by
    unfold Work.Elliptic.sinCos2; fun_prop
  refine Fstar_sub_eq_integral (hf := hSj) hs hsw
    (hlevj.1 s hs) (hlevj.1 w (lt_of_lt_of_le hs hsw)) ?_
  have hae := Work.FTS.EllipticEst.aesm_uncurry_restrict_open
    (fun p : ℝ × ℝ => Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 * sg p.2 / p.1)
    ((((hΨ.DzIter (j + 1)).continuousOn).mul hsg).div continuousOn_fst
      (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
    (a := s) (b := w) (le_of_lt hs)
  refine (integrable_uncurry_div_of_fibre_bound
    (f := fun r θ => Work.Spaces.DzIter (j + 1) Ψ r θ * sg θ) (B := Bnd Ψ (j + 1))
    hs hsw hae (fun r hr => hlevj1.1 r (lt_trans hs hr.1)) (fun r hr => ?_)
    (hlevj1.2.2 s w hs)).congr ?_
  · have heq : ∫ θ in Iθ, |Work.Spaces.DzIter (j + 1) Ψ r θ * sg θ|
        = ∫ θ in Iθ, |Work.Spaces.DzIter (j + 1) Ψ r θ| * sg θ :=
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          have hσ : 0 ≤ sg θ := mul_nonneg
            (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
          simp only [abs_mul, abs_of_nonneg hσ]))
    rw [heq]
    exact hlevj1.2.1 r (lt_trans hs hr.1)
  · rw [MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod measurableSet_Icc) (fun p hp => ?_)
    have hp1 : 0 < p.1 := lt_trans hs hp.1.1
    simp only [Function.uncurry]
    rw [show Work.Spaces.DzIter (j + 1) Ψ p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2 from rfl,
      mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt hp1)]

theorem chain_pz_level {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (j : ℕ) (hj : j ≤ 2) :
    ∀ s w, 0 < s → s ≤ w →
      Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) w
        - Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) s
      = ∫ r in s..w, Work.Elliptic.Fstar
          (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r := by
  intro s w hs hsw
  have hSj : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ) := hΨ.DzIter j
  have hlev1 := level_bound hΨ hA hB (j + 1) (by omega)
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ sg θ := fun θ hθ => by
    show 0 ≤ Real.sin θ * Real.cos θ ^ 2
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
  have hslice : ∀ u, 0 < u → IntegrableOn
      (fun θ => Work.Spaces.pz (Work.Spaces.DzIter j Ψ) u θ * sg θ) Iθ := by
    intro u hu
    refine ((hlev1.1 u hu).div_const u).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_))
    show Work.Spaces.DzIter (j + 1) Ψ u θ * sg θ / u
        = Work.Spaces.pz (Work.Spaces.DzIter j Ψ) u θ * sg θ
    rw [show Work.Spaces.DzIter (j + 1) Ψ u θ
        = u * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) u θ from rfl]
    field_simp
  refine Fstar_sub_eq_integral (hf := hSj.pz) hs hsw
    (hslice s hs) (hslice w (lt_of_lt_of_le hs hsw)) ?_
  -- box integrability of `pz (pz (DzIter j Ψ)) * sg`
  have hsg : ContinuousOn (fun p : ℝ × ℝ => sg p.2) Work.FTS.EllipticEst.Q0 := by
    unfold Work.Elliptic.sinCos2; fun_prop
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2 * sg p.2 / p.1)
      Work.FTS.EllipticEst.Q0 :=
    (((hSA.DzIter j).continuousOn).mul hsg).div continuousOn_fst (fun p hp =>
      ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hae := Work.FTS.EllipticEst.aesm_uncurry_restrict_open
    (fun p : ℝ × ℝ => Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      p.1 p.2 * sg p.2 / p.1 / p.1) (hcont.div continuousOn_fst
        (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
      (a := s) (b := w) (le_of_lt hs)
  have hint : IntegrableOn (fun r => (1 + AngSq (Work.Spaces.DzIter j
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / s) (Set.Ioc s w) := by
    have hw := slot_Iz_integrableOn hSA hA j hj (a := s) (b := w) hs
    have haesm : AEStronglyMeasurable (fun u => AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)
        (volume.restrict (Set.Ioc s w)) :=
      aesm_AngSq (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (hSA.DzIter j) n) (le_of_lt hs)
    have hE : IntegrableOn (fun u => AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) (Set.Ioc s w) := by
      refine hw.mono' haesm ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (AngSq_nonneg _ _)]
      have h1 : 1 ≤ (Work.Spaces.w u) ^ 2 := by
        have := Work.FTS.EllipticEst.one_le_w (lt_trans hs hu.1)
        nlinarith
      nlinarith [AngSq_nonneg (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u]
    have hIc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc s w) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    exact ((hE.add hIc).mul_const s⁻¹).congr
      (Filter.Eventually.of_forall fun r => by
        simp only [Pi.add_apply, div_eq_mul_inv]
        ring)
  refine (integrable_uncurry_div_of_fibre_bound
    (f := fun r θ => Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      r θ * sg θ / r) (B := fun r => (1 + AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / s)
    hs hsw hae (fun r hr => ?_) (fun r hr => ?_) hint).congr ?_
  · -- fibres
    have hr0 : 0 < r := lt_trans hs hr.1
    have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r θ) (volume.restrict Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter j).continuousOn hr0
    exact (((abs_moment_le_energy hm (slot_slice_integrableOn hSA hA j hj hr0)).1.mul_const
      r⁻¹).congr (Filter.Eventually.of_forall fun θ => by
        simp only [div_eq_mul_inv]))
  · -- fibre bound
    have hr0 : 0 < r := lt_trans hs hr.1
    have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r θ) (volume.restrict Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter j).continuousOn hr0
    have hEb := abs_moment_le_energy hm (slot_slice_integrableOn hSA hA j hj hr0)
    have h1 : ∫ θ in Iθ, |Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        r θ * sg θ / r| = (∫ θ in Iθ, |Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r θ| * sg θ) / r := by
      rw [← MeasureTheory.integral_div]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [abs_div, abs_of_pos hr0, abs_mul, abs_of_nonneg (hσnn θ hθ)]
    rw [h1]
    have hnn : 0 ≤ (1 + AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) := by
      have := AngSq_nonneg (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r
      linarith
    calc (∫ θ in Iθ, |Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          r θ| * sg θ) / r
        ≤ (1 + AngSq (Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / r :=
          div_le_div_of_nonneg_right hEb.2 (le_of_lt hr0)
      _ ≤ (1 + AngSq (Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / s :=
          div_le_div_of_nonneg_left hnn hs (le_of_lt hr.1)
  · rw [MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod measurableSet_Icc) (fun p hp => ?_)
    have hp1 : 0 < p.1 := lt_trans hs hp.1.1
    simp only [Function.uncurry]
    by_cases hzero : sg p.2 = 0
    · rw [hzero]
      ring
    · have hp2 : p.2 ∈ Set.Icc 0 (Real.pi / 2) := hp.2
      have hpθ : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
        refine ⟨lt_of_le_of_ne hp2.1 ?_, lt_of_le_of_ne hp2.2 ?_⟩
        · intro h
          exact hzero (by rw [← h]; simp [Work.Elliptic.sinCos2])
        · intro h
          exact hzero (by rw [h]; simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two])
      rw [pz2_eq hΨ j hp1 hpθ]
      ring_nf

theorem level_cont {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun u => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u)
      (Set.Ioi 0) := by
  intro z hz
  rw [Set.mem_Ioi] at hz
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have haz2 : a ≤ z + a := by linarith
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ sg θ := fun θ hθ => by
    show 0 ≤ Real.sin θ * Real.cos θ ^ 2
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
  -- integrability of `Fstar (pz (pz (DzIter j Ψ)))` on `(a, z+a]`
  have hWoc : IntegrableOn (fun r => Work.Elliptic.Fstar
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) (Set.Ioc a (z + a)) := by
    have hdom : IntegrableOn (fun r => (1 + AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / a ^ 2) (Set.Ioc a (z + a)) := by
      have hw := slot_Iz_integrableOn hSA hA j hj (a := a) (b := z + a) ha0
      have haesm : AEStronglyMeasurable (fun u => AngSq (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)
          (volume.restrict (Set.Ioc a (z + a))) :=
        aesm_AngSq (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
          (hSA.DzIter j) n) (le_of_lt ha0)
      have hE : IntegrableOn (fun u => AngSq (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) (Set.Ioc a (z + a)) := by
        refine hw.mono' haesm ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (AngSq_nonneg _ _)]
        have h1 : 1 ≤ (Work.Spaces.w u) ^ 2 := by
          have := Work.FTS.EllipticEst.one_le_w (lt_trans ha0 hu.1)
          nlinarith
        nlinarith [AngSq_nonneg (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u]
      have hIc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc a (z + a)) :=
        integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      refine ((hE.add hIc).div_const (a ^ 2)).congr ?_
      filter_upwards with x
      simp only [Pi.add_apply]
      ring
    have haesm : AEStronglyMeasurable (fun r => Work.Elliptic.Fstar
        (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r)
        (volume.restrict (Set.Ioc a (z + a))) := by
      have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz
          (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) p.1 p.2 * sg p.2)
          Work.FTS.EllipticEst.Q0 := by
        have hsg : ContinuousOn (fun p : ℝ × ℝ => sg p.2) Work.FTS.EllipticEst.Q0 := by
          unfold Work.Elliptic.sinCos2; fun_prop
        exact ((((hΨ.DzIter j).pz).pz).continuousOn).mul hsg
      have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont
        (a := a) (b := z + a) (le_of_lt ha0)).integral_prod_right'
        (μ := volume.restrict (Set.Ioc a (z + a))) (ν := volume.restrict Iθ)
      simpa only [Work.Elliptic.Fstar, Function.uncurry_apply_pair] using h
    refine hdom.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
    have hr0 : 0 < r := lt_trans ha0 hr.1
    have hbound := abs_pz2_le_energy hΨ hA j hj r hr0
    have h1 : (1 + AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / r ^ 2
        ≤ (1 + AngSq (Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / a ^ 2 := by
      refine div_le_div_of_nonneg_left ?_ (by positivity)
        (by nlinarith [mul_self_le_mul_self ha0.le hr.1.le])
      have := AngSq_nonneg (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r
      linarith
    rw [Real.norm_eq_abs]
    refine le_trans ?_ (le_trans hbound h1)
    rw [Work.Elliptic.Fstar]
    calc |∫ θ in Iθ, Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r θ * sg θ|
        ≤ ∫ θ in Iθ, |Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r θ * sg θ| := by
          simpa only [Real.norm_eq_abs] using
            (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
              (f := fun θ => Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r θ * sg θ))
      _ = ∫ θ in Iθ, |Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r θ| * sg θ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
          rw [abs_mul, abs_of_nonneg (hσnn θ hθ)]
  have hWint : IntegrableOn (fun r => Work.Elliptic.Fstar
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) (Set.uIcc a (z + a)) := by
    rw [Set.uIcc_of_le haz2]
    exact hWoc.congr_set_ae MeasureTheory.Ioc_ae_eq_Icc.symm
  have hΦ : ContinuousOn (fun x => ∫ r in a..x, Work.Elliptic.Fstar
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) (Set.uIcc a (z + a)) :=
    intervalIntegral.continuousOn_primitive_interval hWint
  have hU : Set.uIcc a (z + a) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le haz2]
    exact Icc_mem_nhds haz (by linarith)
  have hcontΦ : ContinuousWithinAt (fun x => ∫ r in a..x, Work.Elliptic.Fstar
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) (Set.Ioi 0) z :=
    (hΦ.continuousAt hU).continuousWithinAt
  have hev : (fun x => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) x)
      =ᶠ[𝓝[Set.Ioi 0] z]
      (fun x => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) a
        + ∫ r in a..x, Work.Elliptic.Fstar
            (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rcases le_total a x with h | h
    · have h2 := chain_pz_level hΨ hA hB j hj a x ha0 h
      linarith
    · have h2 := chain_pz_level hΨ hA hB j hj x a (show 0 < x from hx) h
      rw [intervalIntegral.integral_symm] at h2
      linarith
  have hz_e : Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) z
      = Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) a
        + ∫ r in a..z, Work.Elliptic.Fstar
            (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r := by
    have h2 := chain_pz_level hΨ hA hB j hj a z ha0 haz.le
    linarith
  exact (continuousWithinAt_const.add hcontΦ).congr_of_eventuallyEq hev hz_e

/-! ## 8. The induction step and the assembly -/

/-- A continuous function whose integral over every interval `[s,w] ⊆ (0,∞)` vanishes is
zero. -/
theorem eq_zero_of_interval_integral_eq_zero {V : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : ∀ s w, 0 < s → s ≤ w → ∫ r in s..w, V r = 0)
    (hcont : ContinuousOn V (Set.Ioi 0)) : V z = 0 := by
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have hsub : Set.uIcc a z ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le haz.le]
    intro x hx
    exact lt_of_lt_of_le ha0 hx.1
  have hInt : IntervalIntegrable V volume a z := (hcont.mono hsub).intervalIntegrable
  have hsm : StronglyMeasurableAtFilter V (𝓝 z) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi 0) (μ := volume) isOpen_Ioi
      (fun x hx => hcont.continuousAt (isOpen_Ioi.mem_nhds hx)) z hz
  have hderiv : HasDerivAt (fun w => ∫ r in a..w, V r) (V z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hsm
      (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hev : (fun w => ∫ r in a..w, V r) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds haz] with w hw
    exact hint a w ha0 (le_of_lt hw)
  have hderiv0 : HasDerivAt (fun w => ∫ r in a..w, V r) 0 z := by
    rw [Filter.EventuallyEq.hasDerivAt_iff hev]
    exact hasDerivAt_const z 0
  exact hderiv.unique hderiv0

/-- One step of the moment induction. -/
theorem level_step {Ψ : ℝ → ℝ → ℝ} (j : ℕ)
    (hchain : ∀ s w, 0 < s → s ≤ w →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) w
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) s
      = ∫ r in s..w, Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r)
    (hcont : ContinuousOn (fun u => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u)
      (Set.Ioi 0))
    (hprev : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0) :
    ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) z = 0 := by
  intro z hz
  have hV : Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) z = 0 := by
    refine eq_zero_of_interval_integral_eq_zero hz (fun s w hs hsw => ?_) hcont
    rw [← hchain s w hs hsw, hprev w (lt_of_lt_of_le hs hsw), hprev s hs, sub_self]
  rw [show Work.Spaces.DzIter (j + 1) Ψ = Work.Spaces.Dz (Work.Spaces.DzIter j Ψ) from rfl,
    Fstar_Dz_eq, hV, mul_zero]

/-- **The moment chain, `j ≤ 3`, for the current (`a.e.`) weak class.**  For a datum
`h : EllWeakPos α 2 F Ψ` the angular moments `F_*(D_z^j Ψ)(z) = ∫_θ D_z^j Ψ(z,θ) sinθcos²θ dθ`
vanish for every `j ≤ 3` and every `z > 0`. -/
theorem Fstar_DzIter_le_Psi (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := h.memA
  have hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  -- ## `F_*Ψ` is continuous on `(0,∞)`
  have hcont0 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) z)
      (Set.Ioi 0) := by
    intro z hz
    have hs0 : 0 < z / 2 := by linarith [Set.mem_Ioi.mp hz]
    have hchain0 := level_chain hΨ hA hB 0 (by omega)
    have hcontp := level_cont hΨ hA hB 0 (by omega)
    have hInt : IntervalIntegrable
        (fun r => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter 0 Ψ)) r)
        volume (z / 2) (2 * z) :=
      (hcontp.mono (by
        intro u hu
        rw [Set.uIcc_of_le (by linarith [Set.mem_Ioi.mp hz])] at hu
        exact lt_of_lt_of_le hs0 hu.1)).intervalIntegrable
    have hcontprim : ContinuousOn
        (fun w => ∫ r in z / 2..w,
          Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter 0 Ψ)) r)
        (Set.uIcc (z / 2) (2 * z)) :=
      intervalIntegral.continuousOn_primitive_interval' hInt (by
        rw [Set.uIcc_of_le (by linarith [Set.mem_Ioi.mp hz])]
        exact ⟨le_rfl, by linarith [Set.mem_Ioi.mp hz]⟩)
    have hmem : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith [Set.mem_Ioi.mp hz])]
      exact Icc_mem_nhds (by linarith [Set.mem_Ioi.mp hz]) (by linarith [Set.mem_Ioi.mp hz])
    have hev : (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) w) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) (z / 2)
          + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter 0 Ψ)) r) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith [Set.mem_Ioi.mp hz])] with w hw
      have h1 := hchain0 (z / 2) w hs0 hw.le
      linarith [h1]
    exact ((continuousAt_const.add (hcontprim.continuousAt hmem)).congr hev.symm).continuousWithinAt
  -- ## `F_*Ψ ≡ 0` from the moment hypothesis (in `a.e.` form) and the continuity
  -- NOTE: the two lines of `hae` are the only place where the *form* of the moment field of
  -- `TT.EllWeakPos` is used.  With the current (pointwise) definition of `EllWeakPos` the
  -- derivation below is `fun z hz => h.orthPsi z hz`; if the field is ever relaxed to
  -- `∀ᵐ z ∂(volume.restrict (Ioi 0)), Fstar Ψ z = 0`, then `hae` becomes `h.orthPsi` verbatim.
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun z hz => h.orthPsi z hz)
  have h0 : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) z = 0 := fun z hz =>
    Work.H2W.ae_zero_of_continuousOn hcont0 hae z hz
  have h1 : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 :=
    level_step 0 (level_chain hΨ hA hB 0 (by omega)) (level_cont hΨ hA hB 0 (by omega)) h0
  have h2 : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0 :=
    level_step 1 (level_chain hΨ hA hB 1 (by omega)) (level_cont hΨ hA hB 1 (by omega)) h1
  have h3 : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z = 0 :=
    level_step 2 (level_chain hΨ hA hB 2 (by omega)) (level_cont hΨ hA hB 2 (by omega)) h2
  intro j hj z hz
  interval_cases j
  · exact h0 z hz
  · exact h1 z hz
  · exact h2 z hz
  · exact h3 z hz

end Work.H2W.MomentAe
end
end
