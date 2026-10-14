import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.TopSlotTwoFts.AHalfMain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TopSlotTwoFts

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary endpoint bookkeeping -/

/-- On `Iθ`, a nonzero `sin (2θ)` forces `θ` into the open interval. -/
theorem mem_Ioo_of_mem_Iθ_of_sin_ne {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hs : Real.sin (2 * θ) ≠ 0) : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  constructor
  · rcases eq_or_lt_of_le hθ.1 with h | h
    · exact absurd (by rw [← h]; simp) hs
    · exact h
  · rcases eq_or_lt_of_le hθ.2 with h | h
    · exfalso; apply hs
      rw [show 2 * θ = Real.pi by rw [h]; ring, Real.sin_pi]
    · exact h

/-- At `sin (2θ) = 0` the level-`0` integrand vanishes. -/
theorem hkIntegrand_zero_eq_zero {α : ℝ} (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α 0 g z θ = 0 := by
  rw [Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq, hs]
  rw [Real.zero_rpow (show Work.Spaces.eta / 2 ≠ 0 by
    rw [Work.Spaces.eta]; norm_num)]
  ring

/-! ## Dominations of the level-`0` slots -/

/-- The level-`0` slot of `∂_θ²(D_z^jΨ)` is a slot of the level-`2` integrand of `∂_θ²Ψ`. -/
theorem hk0_pthIter2_DzIter_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) {j : ℕ} (hj : j ≤ 2)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) z θ
      ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq]
    have hw : Work.Spaces.w (0 : ℝ) = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact Work.Spaces.HkIntegrand_nonneg α 2 _ 0 θ
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [hkIntegrand_zero_eq_zero _ hs]
      exact Work.Spaces.HkIntegrand_nonneg α 2 _ z θ
    · have hθ' := mem_Ioo_of_mem_Iθ_of_sin_ne hθ hs
      rw [Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq,
        Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hsm j hzpos hθ']
      exact Work.Spaces.sq_le_HkIntegrand_z α 2 (Work.Spaces.pthIter 2 Ψ) z θ j hj

/-- The level-`0` slot of `∂_θ²A` is dominated by four times the level-`2` integrand of
`∂_θ²Ψ`. -/
theorem hk0_pthIter2_Aft_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ
      ≤ 4 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq]
    have hw : Work.Spaces.w (0 : ℝ) = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 2 _ 0 θ)
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [hkIntegrand_zero_eq_zero _ hs]
      exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 2 _ z θ)
    · have hθ' := mem_Ioo_of_mem_Iθ_of_sin_ne hθ hs
      set a : ℝ := Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ with ha
      set b : ℝ := Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ with hb
      set Zu : ℝ := Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) with hZu
      have hid : Work.Spaces.pthIter 2 (Aft Ψ) z θ = a - b := by
        rw [ha, hb, pthIter2_Aft_eq hsm hzpos hθ',
          Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hsm 2 hzpos hθ',
          Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hsm 1 hzpos hθ']
      have hsq : ((a - b) * Zu) ^ 2 ≤ 2 * (a * Zu) ^ 2 + 2 * (b * Zu) ^ 2 := by
        nlinarith [sq_nonneg (a * Zu + b * Zu), sq_nonneg (a * Zu), sq_nonneg (b * Zu)]
      have h1 : (a * Zu) ^ 2 ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
        rw [ha, hZu, Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hsm 2 hzpos hθ']
        exact Work.Spaces.sq_le_HkIntegrand_z α 2 (Work.Spaces.pthIter 2 Ψ) z θ 2 (by norm_num)
      have h2 : (b * Zu) ^ 2 ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
        rw [hb, hZu, Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hsm 1 hzpos hθ']
        exact Work.Spaces.sq_le_HkIntegrand_z α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1 (by norm_num)
      rw [Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq, hid, ← hZu]
      linarith [hsq, h1, h2]

/-! ## Integrability of the level-`0` slots -/

theorem integrableOn_hk0_pthIter2_DzIter {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) {j : ℕ} (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) z θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' (h.memB.1 z (Set.mem_Ici.mpr hz.le))
    ((aesm_slice_pthIter2_DzIter hsm j hz).congr ?_) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact (hkIntegrand_zero_eq_mul α _ z θ hθ).symm
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
    exact hk0_pthIter2_DzIter_le hsm hj (Set.mem_Ici.mpr hz.le) hθ

theorem integrable_hk0_pthIter2_DzIter {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) {j : ℕ} (hj : j ≤ 2) :
    MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  refine MeasureTheory.Integrable.mono' h.memB.2 ((aesm_int_pthIter2_DzIter hsm j).congr ?_) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact (hkIntegrand_zero_eq_mul α _ z θ hθ).symm
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (h.memB.1 z hz) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact hk0_pthIter2_DzIter_le hsm hj hz hθ

theorem integrableOn_hk0_pthIter2_Aft {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0
      (Work.Spaces.pthIter 2 (Aft Ψ)) z θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' ((h.memB.1 z (Set.mem_Ici.mpr hz.le)).const_mul 4)
    ((aesm_slice_pthIter2_Aft hsm hz).congr ?_) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact (hkIntegrand_zero_eq_mul α _ z θ hθ).symm
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
    exact hk0_pthIter2_Aft_le hsm (Set.mem_Ici.mpr hz.le) hθ

theorem integrable_hk0_pthIter2_Aft {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  refine MeasureTheory.Integrable.mono' (h.memB.2.const_mul 4)
    ((aesm_int_pthIter2_Aft hsm).congr ?_) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact (hkIntegrand_zero_eq_mul α _ z θ hθ).symm
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
    have hle := MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      ((h.memB.1 z hz).const_mul 4)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
        hk0_pthIter2_Aft_le hsm hz hθ)
    rwa [MeasureTheory.integral_const_mul] at hle

end

end Work.FTS.EllipticEst.TopSlotTwoFts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoPlumb =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary facts -/

/-- `z > 0` almost everywhere on `Iz = [0,∞)`. -/
theorem ae_restrict_Iz_pos :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton 0)
  intro x hx
  simp only [Set.mem_ofPred_eq, Set.mem_Ici] at hx
  push Not at hx
  exact le_antisymm hx.2 hx.1

/-- The level-`0` integrand is the square of the weighted function. -/
theorem HkIntegrand_zero_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The level-`0` integrand against the `sEta`-weight, on `Iθ`. -/
theorem HkIntegrand_zero_eq_mul (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  rw [HkIntegrand_zero_apply, mul_pow, div_rpow_half_sq_Iθ hθ]
  ring

/-- The level-`0` integrand vanishes when `sin (2θ) = 0`. -/
theorem HkIntegrand_zero_eq_zero_of_sin_eq_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [HkIntegrand_zero_apply, h,
    Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0), div_zero,
    mul_zero, sq]
  ring

/-- The level-`0` integrand vanishes when the radial weight vanishes. -/
theorem HkIntegrand_zero_eq_zero_of_w_eq_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {z : ℝ}
    (h : Work.Spaces.w z = 0) (θ : ℝ) : Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [HkIntegrand_zero_apply, h, zero_div, mul_zero, sq]
  ring

theorem w_zero : Work.Spaces.w 0 = 0 := by
  simp [Work.Spaces.w]

theorem sin_two_zero_at_zero_aux : Real.sin (2 * (0 : ℝ)) = 0 := by
  rw [show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero]

theorem sin_two_zero_at_pi_half_aux : Real.sin (2 * (Real.pi / 2)) = 0 := by
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

/-- **Membership transfer.**  If the level-`0` integrand of `f` is pointwise dominated (on the
open quadrant) by the level-`k` integrand of an `ℋ^k`-function `g`, and `f` is smooth on the
open quadrant, then `f ∈ ℋ⁰`. -/
theorem HkMem_zero_of_pointwise {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hf : SmoothOpen f) (hg : Work.Spaces.HkMem α k g)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 0 f z θ ≤ c * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α 0 f := by
  have hpoint : ∀ z θ : ℝ, z ∈ Work.Spaces.Iz → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 f z θ ≤ c * Work.Spaces.HkIntegrand α k g z θ := by
    intro z θ hz hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0, HkIntegrand_zero_eq_zero_of_w_eq_zero α f w_zero θ]
      exact mul_nonneg hc (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
    · rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · rw [← h0, HkIntegrand_zero_eq_zero_of_sin_eq_zero α f sin_two_zero_at_zero_aux]
        exact mul_nonneg hc (Work.Spaces.HkIntegrand_nonneg α k g z 0)
      · rcases eq_or_lt_of_le hθ.2 with h1 | h1
        · rw [h1, HkIntegrand_zero_eq_zero_of_sin_eq_zero α f sin_two_zero_at_pi_half_aux]
          exact mul_nonneg hc (Work.Spaces.HkIntegrand_nonneg α k g z (Real.pi / 2))
        · exact h z θ hzpos h0 h1
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 f z θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_eq_zero_of_w_eq_zero α f (by rw [← hz0]; exact w_zero) θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono' ((hg.1 z hz).const_mul c)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (hf.continuousOn_HkIntegrand α 0) hzpos) ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => by
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 f z θ)]
        exact hpoint z θ hz hθ
  · refine (hg.2.const_mul c).mono' ?_ ?_
    · have hjoint : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        Work.Spaces.aesm_of_continuousOn_Qd _ (hf.continuousOn_HkIntegrand α 0)
      have := hjoint.integral_prod_right'
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      simpa only using this
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 0 f z θ)]
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f z θ)
        ((hg.1 z hz).const_mul c)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hpoint z θ hz hθ))

/-! ## A.e. slice inequalities imply inequalities of the integrals -/

/-- **`HkSq`-version, two dominating terms.** -/
theorem HkSq_zero_le_of_ae_slice_le_sum {α C : ℝ} (hC : 0 ≤ C) {g u v : ℝ → ℝ → ℝ}
    (huO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ) Work.Spaces.Iz)
    (hvO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 v z θ) Work.Spaces.Iz)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ))) :
    Work.Spaces.HkSq α 0 g ≤ C * (Work.Spaces.HkSq α 0 u + Work.Spaces.HkSq α 0 v) := by
  have hsplit : (∫ z in Work.Spaces.Iz,
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ)))
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ) :=
    MeasureTheory.integral_add huO hvO
  have hInt : MeasureTheory.Integrable (fun z : ℝ => C * ((∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 u z θ) + (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 v z θ))) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (huO.add hvO).const_mul C
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  by_cases hG : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
  · have hmono := MeasureTheory.integral_mono_ae hG hInt hae
    rw [MeasureTheory.integral_const_mul] at hmono
    rw [hsplit] at hmono
    linarith
  · rw [MeasureTheory.integral_undef hG]
    exact mul_nonneg hC (add_nonneg (Work.Spaces.HkSq_nonneg α 0 u)
      (Work.Spaces.HkSq_nonneg α 0 v))







/-! ## The weight identity of the top angular slot -/


/-! ## The angular weight algebra of the Agmon estimate -/







end Work.FTS.EllipticEst.Prop
end
end
