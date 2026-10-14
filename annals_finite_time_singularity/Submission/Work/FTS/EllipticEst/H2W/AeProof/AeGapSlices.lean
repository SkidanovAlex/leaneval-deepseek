import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.AeGSlice =====
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
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Slices of the radial derivative are `sigma`-square integrable, in the a.e. class -/

theorem slice_smooth_of_smoothOpen {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  have hf : ContDiff ℝ n (fun θ : ℝ => (z, θ)) := by fun_prop
  have hcomp := ContDiffOn.comp (f := fun θ : ℝ => (z, θ)) (g := Function.uncurry u)
    (hS.forall n) hf.contDiffOn (fun θ hθ => ⟨hz, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using hcomp

/-! ## The two honesty conditions, slicewise -/

theorem memB_sigma_of {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u)) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have h2 := (hB.1 z (le_of_lt hz)).congr
    (Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq_ae α (Work.Spaces.pthIter 2 u) z)
  have h4 := h2.const_mul (1 / (Work.Spaces.w z) ^ 2)
  have h3 : (fun θ => (1 / (Work.Spaces.w z) ^ 2)
        * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 u z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)))
      = fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    funext θ
    rw [← mul_assoc, one_div,
      inv_mul_cancel₀ (pow_ne_zero 2 (Work.FTS.EllipticEst.Honest.w_ne_zero hz)), one_mul]
  rw [h3] at h4
  exact h4

theorem memA_sigma_of {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have h2 := (hA.1 z (le_of_lt hz)).congr
    (Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq_ae α
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z)
  have h4 := h2.const_mul (1 / ((Work.Spaces.w z) ^ 2 * z ^ 4))
  have h3 : (fun θ => (1 / ((Work.Spaces.w z) ^ 2 * z ^ 4))
        * ((Work.Spaces.w z) ^ 2
            * (((z ^ 2 * Work.Spaces.pzIter 2 u z θ)) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      = fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    funext θ
    have hw : Work.Spaces.w z ≠ 0 := Work.FTS.EllipticEst.Honest.w_ne_zero hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    field_simp
  rw [h3] at h4
  exact h4

/-! ## The angular slices of `u` are bounded -/

theorem psi_slice_bdd_of {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u)) {z : ℝ} (hz : 0 < z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u z θ| ≤ M := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    slice_smooth_of_smoothOpen hS hz
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := memB_sigma_of hB hz
  have hint' : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.TT.D2 (fun s => u z s) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun hint (fun θ _ => ?_) measurableSet_Icc
    rfl
  have hcont2 : ContinuousOn (fun θ => Work.FTS.EllipticEst.TT.D2 (fun s => u z s) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv (fun s => u z s)) (Set.Ioo 0 (Real.pi / 2)) :=
      (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 : ContDiffOn ℝ 0 (deriv (deriv (fun s => u z s))) (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h3 : Work.FTS.EllipticEst.TT.D2 (fun s => u z s)
        = deriv (deriv (fun s => u z s)) := rfl
    rw [h3]
    exact h2.continuousOn
  have hD2abs : MeasureTheory.IntegrableOn
      (fun θ => |Work.FTS.EllipticEst.TT.D2 (fun s => u z s) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hcont2 hint'
  have hπ4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hbound1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun s => u z s) θ - deriv (fun s => u z s) (Real.pi / 4)|
        ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 (fun s => u z s) x| :=
    fun θ hθ =>
      Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2 hsm hD2abs hθ hπ4
  set E : ℝ := ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 (fun s => u z s) x| with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => abs_nonneg _)
  set K : ℝ := |deriv (fun s => u z s) (Real.pi / 4)| + E with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact add_nonneg (abs_nonneg _) hE0
  have hKbd : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun s => u z s) ξ| ≤ K := by
    intro ξ hξ
    have h1 := hbound1 ξ hξ
    have h2 : |deriv (fun s => u z s) ξ|
        ≤ |deriv (fun s => u z s) ξ - deriv (fun s => u z s) (Real.pi / 4)|
          + |deriv (fun s => u z s) (Real.pi / 4)| := by
      have := abs_add_le (deriv (fun s => u z s) ξ - deriv (fun s => u z s) (Real.pi / 4))
        (deriv (fun s => u z s) (Real.pi / 4))
      simpa using this
    rw [hK, hE]
    linarith
  set M : ℝ := |u z (Real.pi / 4)| + K * (Real.pi / 2) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact add_nonneg (abs_nonneg _) (mul_nonneg hK0 (by positivity))
  refine ⟨M, hM0, fun θ hθ => ?_⟩
  have h2 := Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
    hsm hθ hπ4 hKbd
  have h3 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have h4 : K * |θ - Real.pi / 4| ≤ K * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left h3 hK0
  calc |u z θ| = |(u z θ - u z (Real.pi / 4)) + u z (Real.pi / 4)| := by
        rw [sub_add_cancel]
    _ ≤ |u z θ - u z (Real.pi / 4)| + |u z (Real.pi / 4)| := abs_add_le _ _
    _ ≤ K * (Real.pi / 2) + |u z (Real.pi / 4)| := by linarith
    _ = M := by rw [hM]; ring


theorem box_abs_sq_of {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have hzle : z ≤ z + 1 := by linarith
  -- ### the pointwise identity relating the `ℋ`-integrand of `z²∂_zzu` to the box integrand
  have hk_w : ∀ s : ℝ, 0 < s → ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ
        = (1 + s) ^ 4
          * ((Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro s hs θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq' hθ]
    have hws : (Work.Spaces.w s) ^ 2 = (1 + s) ^ 4 / s ^ 4 := by
      rw [Work.Spaces.w]
      field_simp
    rw [hws]
    field_simp
  -- ### continuity of the box integrand on the open quadrant and its measurability
  have hKcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2) Work.FTS.EllipticEst.Q0 :=
    ((hS.pzIter 2).continuousOn.pow 2).mul Work.FTS.EllipticEst.Honest.continuousOn_sig_Q0
  have hK_aesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2)
      ((volume.restrict (Set.Ioc z (z + 1))).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.aesm_uncurry_restrict_open _
      (by simpa [Work.FTS.EllipticEst.Q0] using hKcont) (le_of_lt hz)
  -- ### the `θ`-marginal of the box integrand is integrable in `s` (from `memA`)
  have hA2sub : MeasureTheory.IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ)
      (Set.Ioc z (z + 1)) :=
    hA.2.mono_set (fun s hs => by
      rw [Work.Spaces.Iz]; exact le_of_lt (lt_trans hz hs.1))
  have hKmarg : MeasureTheory.IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioc z (z + 1)) := by
    have hdom : MeasureTheory.IntegrableOn (fun s => ((1 + z) ^ 4)⁻¹
        * |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ|)
        (Set.Ioc z (z + 1)) :=
      (hA2sub.abs).const_mul _
    have haesm : MeasureTheory.AEStronglyMeasurable (fun s => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (volume.restrict (Set.Ioc z (z + 1))) := hK_aesm.integral_prod_right'
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with s hs
    have hs0 : 0 < s := lt_trans hz hs.1
    have hid : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ)
        = (1 + s) ^ 4 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hk_w s hs0 θ hθ)
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ)
          / (1 + s) ^ 4 := by
      rw [hid]
      field_simp
    have hX : 0 ≤ |∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ| :=
      abs_nonneg _
    have hzs : z < s := hs.1
    have hinv : ((1 + s) ^ 4)⁻¹ ≤ ((1 + z) ^ 4)⁻¹ :=
      (inv_le_inv₀ (by positivity : (0 : ℝ) < (1 + s) ^ 4)
        (by positivity : (0 : ℝ) < (1 + z) ^ 4)).mpr
        (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + z)
          (by linarith : 1 + z ≤ 1 + s) 4)
    rw [Real.norm_eq_abs, h1, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (1 + s) ^ 4)]
    calc |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ|
          / (1 + s) ^ 4
        = |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ|
          * ((1 + s) ^ 4)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ|
          * ((1 + z) ^ 4)⁻¹ := mul_le_mul_of_nonneg_left hinv hX
      _ = ((1 + z) ^ 4)⁻¹ * |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 u s θ) s θ| :=
          by ring
  -- ### Tonelli: the product integrand is integrable, hence so is the `s`-marginal in `θ`
  have hprod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.pzIter 2 u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      ((volume.restrict (Set.Ioc z (z + 1))).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.integrable_prod_iff hK_aesm]
    constructor
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with s hs
      exact memA_sigma_of hA (lt_trans hz hs.1)
    · refine hKmarg.congr (Filter.Eventually.of_forall (fun s => ?_))
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      have h0 : 0 ≤ (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
      rw [Real.norm_eq_abs]
      change (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = |(Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ|
      exact (abs_of_nonneg h0).symm
  have hth : MeasureTheory.Integrable (fun θ => ∫ s,
      ‖(Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ‖
        ∂(volume.restrict (Set.Ioc z (z + 1)))) (volume.restrict Work.Spaces.Iθ) :=
    hprod.integral_norm_prod_right
  -- ### the dominating function in `θ`
  have hdomθ : MeasureTheory.IntegrableOn (fun θ => ∫ s in z..(z + 1),
      (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine hth.congr ?_
    rw [Work.FTS.EllipticEst.Honest.restrict_Iθ_eq_Ioo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [intervalIntegral.integral_of_le hzle]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
    have h0 : 0 ≤ (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg h0
  -- ### measurability of the target
  have haesmθ : MeasureTheory.AEStronglyMeasurable (fun θ =>
      (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun θ =>
        ∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|)
        (volume.restrict Work.Spaces.Iθ) := by
      have habs : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.1 p.2|)
          Work.FTS.EllipticEst.Q0 := (hS.pzIter 2).continuousOn.abs
      have h2 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.2 p.1|)
          ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioc z (z + 1)))) := by
        refine (Work.FTS.EllipticEst.aesm_uncurry_restrict_open
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.1 p.2|) ?_ (le_of_lt hz)).prod_swap
        simpa [Work.FTS.EllipticEst.Q0] using habs
      have h3 := h2.integral_prod_right'
      simpa [intervalIntegral.integral_of_le hzle] using h3
    exact (h1.pow 2).mul Work.FTS.EllipticEst.Honest.aesm_sig_Iθ
  -- ### the pointwise Cauchy–Schwarz bound and the conclusion
  refine MeasureTheory.Integrable.mono' hdomθ haesmθ ?_
  rw [Work.FTS.EllipticEst.Honest.restrict_Iθ_eq_Ioo]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hcont2 : ContinuousOn (fun s => |Work.Spaces.pzIter 2 u s θ|) (Set.Icc z (z + 1)) := by
    refine ((hS.pzIter 2).curry_z hθ).continuousOn.abs.mono ?_
    intro s hs
    exact lt_of_lt_of_le hz hs.1
  have hcs := Work.FTS.EllipticEst.Honest.sq_integral_le_of_continuousOn hcont2
  have hsq : (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2
      ≤ ∫ s in z..(z + 1), (Work.Spaces.pzIter 2 u s θ) ^ 2 := by
    refine le_trans hcs (le_of_eq ?_)
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [sq_abs]
  have hsig0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := Work.FTS.EllipticEst.Honest.sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  calc ‖(∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2
        * Work.FTS.EllipticEst.sEta θ‖
      = (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2
        * Work.FTS.EllipticEst.sEta θ :=
        Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsig0)
    _ ≤ (∫ s in z..(z + 1), (Work.Spaces.pzIter 2 u s θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul_of_nonneg_right hsq hsig0
    _ = ∫ s in z..(z + 1),
          (Work.Spaces.pzIter 2 u s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        rw [intervalIntegral.integral_mul_const]


theorem pz_taylor_of {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pz u z θ = (u (z + 1) θ - u z θ)
      - ∫ s in z..(z + 1), (z + 1 - s) * Work.Spaces.pzIter 2 u s θ := by
  have hzle : z ≤ z + 1 := by linarith
  have hmem : ∀ s ∈ Set.uIcc z (z + 1), 0 < s := by
    intro s hs
    rw [Set.uIcc_of_le hzle] at hs
    exact lt_of_lt_of_le hz hs.1
  have hderiv_u : ∀ s ∈ Set.uIcc z (z + 1),
      HasDerivAt (fun t => Work.Spaces.pz u t θ) (Work.Spaces.pzIter 2 u s θ) s :=
    fun s hs => hS.hasDerivAt_slice_pzIter 1 hθ (hmem s hs)
  have hderiv_v : ∀ s ∈ Set.uIcc z (z + 1),
      HasDerivAt (fun t : ℝ => (z + 1) - t) (-1) s :=
    fun s _ => (hasDerivAt_id s).const_sub (z + 1)
  have hcont_u : ContinuousOn (fun s => Work.Spaces.pz u s θ) (Set.uIcc z (z + 1)) :=
    (hS.pz.curry_z hθ).continuousOn.mono (fun s hs => hmem s hs)
  have hcont_u2 : ContinuousOn (fun s => Work.Spaces.pzIter 2 u s θ) (Set.uIcc z (z + 1)) :=
    ((hS.pzIter 2).curry_z hθ).continuousOn.mono (fun s hs => hmem s hs)
  have hcont_v : ContinuousOn (fun s : ℝ => (z + 1) - s) (Set.uIcc z (z + 1)) :=
    (continuous_const.sub continuous_id).continuousOn
  have hint_u : IntervalIntegrable (fun s => Work.Spaces.pz u s θ) volume z (z + 1) :=
    hcont_u.intervalIntegrable
  have hint_u2 : IntervalIntegrable (fun s => Work.Spaces.pzIter 2 u s θ) volume z (z + 1) :=
    hcont_u2.intervalIntegrable
  have hint_v' : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume z (z + 1) :=
    continuous_const.continuousOn.intervalIntegrable
  -- the fundamental theorem for `u`
  have hFTC : (∫ s in z..(z + 1), Work.Spaces.pz u s θ) = u (z + 1) θ - u z θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hS.hasDerivAt_slice hθ (hmem s hs)) hint_u
  -- the integration by parts
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub (u := fun s => Work.Spaces.pz u s θ)
    (v := fun s : ℝ => (z + 1) - s) (u' := fun s => Work.Spaces.pzIter 2 u s θ)
    (v' := fun _ => (-1 : ℝ)) hderiv_u hderiv_v hint_u2 hint_v'
  have hsplit : (∫ s in z..(z + 1),
        (Work.Spaces.pzIter 2 u s θ * ((z + 1) - s) + Work.Spaces.pz u s θ * (-1)))
      = (∫ s in z..(z + 1), Work.Spaces.pzIter 2 u s θ * ((z + 1) - s))
        + (∫ s in z..(z + 1), Work.Spaces.pz u s θ * (-1)) :=
    intervalIntegral.integral_add (hint_u2.mul_continuousOn hcont_v)
      (hint_u.mul_continuousOn continuous_const.continuousOn)
  have hneg : (∫ s in z..(z + 1), Work.Spaces.pz u s θ * (-1))
      = -(∫ s in z..(z + 1), Work.Spaces.pz u s θ) := by
    rw [intervalIntegral.integral_mul_const]
    ring
  rw [hsplit, hneg, hFTC] at hibp
  have hcomm : (∫ s in z..(z + 1), (z + 1 - s) * Work.Spaces.pzIter 2 u s θ)
      = ∫ s in z..(z + 1), Work.Spaces.pzIter 2 u s θ * ((z + 1) - s) := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    ring
  rw [hcomm]
  linarith [hibp]


theorem gSlice_core (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    (hA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  intro z hz
  have hz1 : 0 < z + 1 := by linarith
  -- ### the level term is integrable
  obtain ⟨M1, hM1, hb1⟩ := psi_slice_bdd_of hS hB hz
  obtain ⟨M2, hM2, hb2⟩ := psi_slice_bdd_of hS hB hz1
  have hlevel : MeasureTheory.IntegrableOn
      (fun θ => (u (z + 1) θ - u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have hsig_int : MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := Work.FTS.EllipticEst.Honest.sEta_integrableOn
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (u (z + 1) θ - u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (((hS.aesm_slice_pzIter 0 hz1).sub (hS.aesm_slice_pzIter 0 hz)).pow 2).mul Work.FTS.EllipticEst.Honest.aesm_sig_Iθ
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul ((M1 + M2) ^ 2)) haesm ?_
    rw [Work.FTS.EllipticEst.Honest.restrict_Iθ_eq_Ioo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : |u (z + 1) θ - u z θ| ≤ M1 + M2 := by
      have h2 := abs_sub_le (u (z + 1) θ) (0 : ℝ) (u z θ)
      have h3 : |u (z + 1) θ| ≤ M2 := hb2 θ hθ
      have h4 : |u z θ| ≤ M1 := hb1 θ hθ
      simp only [sub_zero, zero_sub, abs_neg] at h2
      linarith
    have hsig0 : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
      Work.FTS.EllipticEst.Honest.sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h1' : (u (z + 1) θ - u z θ) ^ 2 ≤ (M1 + M2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsig0)]
    exact mul_le_mul_of_nonneg_right h1' hsig0
  -- ### the box term is integrable
  have hbox := box_abs_sq_of hS hA hz
  -- ### the pointwise domination on the open interval
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ 2 * ((u (z + 1) θ - u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
    intro θ hθ
    have hid := pz_taylor_of hS hz hθ
    have hzle : z ≤ z + 1 := by linarith
    have hcontF2 : ContinuousOn (fun s => Work.Spaces.pzIter 2 u s θ) (Set.Icc z (z + 1)) :=
      ((hS.pzIter 2).curry_z hθ).continuousOn.mono
        (fun s hs => lt_of_lt_of_le hz hs.1)
    have hcontγ : ContinuousOn (fun s : ℝ => (z + 1 - s) * Work.Spaces.pzIter 2 u s θ)
        (Set.Icc z (z + 1)) :=
      (continuous_const.sub continuous_id).continuousOn.mul hcontF2
    have hintF2 : IntervalIntegrable (fun s => Work.Spaces.pzIter 2 u s θ) volume z (z + 1) := by
      have hc : ContinuousOn (fun s => Work.Spaces.pzIter 2 u s θ) (Set.uIcc z (z + 1)) := by
        rw [Set.uIcc_of_le hzle]; exact hcontF2
      exact hc.intervalIntegrable
    have hintγ : IntervalIntegrable (fun s : ℝ => (z + 1 - s) * Work.Spaces.pzIter 2 u s θ)
        volume z (z + 1) := by
      have hc : ContinuousOn (fun s : ℝ => (z + 1 - s) * Work.Spaces.pzIter 2 u s θ)
          (Set.uIcc z (z + 1)) := by
        rw [Set.uIcc_of_le hzle]; exact hcontγ
      exact hc.intervalIntegrable
    have hbnd : |∫ s in z..(z + 1), (z + 1 - s) * Work.Spaces.pzIter 2 u s θ|
        ≤ ∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ| := by
      refine le_trans (intervalIntegral.abs_integral_le_integral_abs hzle) ?_
      refine intervalIntegral.integral_mono_on hzle hintγ.abs hintF2.abs (fun s hs => ?_)
      rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ z + 1 - s)]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [hs.1])
    have h1 : |Work.Spaces.pz u z θ| ≤ |u (z + 1) θ - u z θ|
        + ∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ| := by
      have h2 : |Work.Spaces.pz u z θ|
          ≤ |u (z + 1) θ - u z θ|
            + |∫ s in z..(z + 1), (z + 1 - s) * Work.Spaces.pzIter 2 u s θ| := by
        rw [hid, sub_eq_add_neg]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_neg]
      linarith
    have hsig0 : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
      Work.FTS.EllipticEst.Honest.sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h2 : (Work.Spaces.pz u z θ) ^ 2
        ≤ 2 * (u (z + 1) θ - u z θ) ^ 2
          + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2 := by
      have h3 : |Work.Spaces.pz u z θ| ^ 2
          ≤ (|u (z + 1) θ - u z θ|
            + (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h4 : (|u (z + 1) θ - u z θ|
            + (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|)) ^ 2
          ≤ 2 * |u (z + 1) θ - u z θ| ^ 2
            + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2 := by
        nlinarith [sq_nonneg (|u (z + 1) θ - u z θ|
          - (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|))]
      calc (Work.Spaces.pz u z θ) ^ 2 = |Work.Spaces.pz u z θ| ^ 2 := by rw [sq_abs]
        _ ≤ _ := h3
        _ ≤ 2 * |u (z + 1) θ - u z θ| ^ 2
            + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2 := h4
        _ = 2 * (u (z + 1) θ - u z θ) ^ 2
            + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2 := by
            rw [sq_abs]
    calc (Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ (2 * (u (z + 1) θ - u z θ) ^ 2
            + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2)
          * Work.FTS.EllipticEst.sEta θ :=
          mul_le_mul_of_nonneg_right h2 hsig0
      _ = 2 * ((u (z + 1) θ - u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((∫ s in z..(z + 1), |Work.Spaces.pzIter 2 u s θ|) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by ring
  -- ### assembly
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    ((hS.aesm_slice_pzIter 1 hz).pow 2).mul Work.FTS.EllipticEst.Honest.aesm_sig_Iθ
  refine MeasureTheory.Integrable.mono'
    ((hlevel.const_mul 2).add (hbox.const_mul 2)) haesm ?_
  rw [Work.FTS.EllipticEst.Honest.restrict_Iθ_eq_Ioo]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hsig0 : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.Honest.sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hpt' := hpt θ hθ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsig0)]
  exact hpt'


/-- **`AeGSlice`.**  The angular slice `θ ↦ (∂_z u z θ)² σ θ` is integrable on `Iθ` for every
`z > 0`, for every datum of the almost-everywhere class `AeData`. -/
theorem AeGSlice (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
  gSlice_core α u (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) h.memAng2 h.memRad2

end Work.FTS.EllipticEst.H2W.Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.Honest Work.FTS.EllipticEst.H2W.Ae

/-! ## Continuity on the closed interval from the one-sided limits -/

/-- **Continuity on `[0,c]` from continuity on `(0,c)` and the two one-sided endpoint limits.** -/
theorem continuousOn_Icc_of_tendsto {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hsm : ContinuousOn f (Set.Ioo 0 c))
    (hL0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f 0)))
    (hLc : Filter.Tendsto f (nhdsWithin c (Set.Iio c)) (nhds (f c))) :
    ContinuousOn f (Set.Icc 0 c) := by
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | hx0
  · rcases lt_or_eq_of_le hx.2 with hxc | hxc
    · exact (hsm.continuousAt (isOpen_Ioo.mem_nhds ⟨hx0, hxc⟩)).continuousWithinAt
    · subst hxc
      exact ((continuousWithinAt_Iio_iff_Iic).mp hLc).mono (fun y hy => hy.2)
  · subst hx0
    exact ((continuousWithinAt_Ioi_iff_Ici).mp hL0).mono (fun y hy => hy.1)

/-! ## The fibres of an `AeData` datum -/

/-- **The `θ`-fibres of an `AeData` datum are continuous on `[0, π/2]`, almost everywhere in `z`.**
The right-endpoint limit is unconditional (`AeSliceRightTendsto`); the left-endpoint limit is the
a.e. input (it is proved from the moment condition in `AeSliceLeftTendstoAe`). -/
theorem ae_continuousOn_slice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G)
    (hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)) := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hL0] with z hz hL0z
  refine continuousOn_Icc_of_tendsto (by linarith [Real.pi_pos]) ?_ ?_ ?_
  · exact (contDiffOn_slice u hz (h.smooth 1)).continuousOn
  · simpa [AeData.dirZero h z] using hL0z
  · have hR := (AeSliceRightTendsto α u G h z hz).1
    simpa [AeData.dirPi h z] using hR

/-- **The constrained slice gap for the fibres of `AeData` data, a.e. in `z`**:
`9 ∫_θ u(z,θ)² ≤ ∫_θ (∂_θu(z,θ))²`.  The hypotheses are exactly what `Gap9Open` consumes: on the
fibre, `C²`-regularity on `(0, π/2)` (from `AeData.smooth`), continuity on `[0, π/2]` (from the
endpoint limits), the Dirichlet values (fields of `AeData`), the honesty of `(∂_θu)²`, and the
solvability condition `∫_θ u(z,θ) sinθcos²θ = 0` (a.e. field of `AeData`). -/
theorem AeGapSlices (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)))
    (hint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      9 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2 := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hC, hint, AeData.momU h]
    with z hz hCz hintz hmomz
  have hcd : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice u hz (h.smooth 2)
  have hgap := Gap9Open (fun θ => u z θ) hcd hCz (AeData.dirZero h z) (AeData.dirPi h z)
    (by simpa only [Work.Spaces.pth] using hintz) (by simpa only [Work.Elliptic.Fstar] using hmomz)
  simpa only [Work.Spaces.pth] using hgap

end Work.FTS.EllipticEst.H2W.AeProof
end
end
