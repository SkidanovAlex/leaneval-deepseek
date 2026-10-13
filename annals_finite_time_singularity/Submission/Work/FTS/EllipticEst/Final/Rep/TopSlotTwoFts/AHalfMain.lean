/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TopSlotTwoFts/AHalfMain`: the A-slot estimate

Continuation of `TopSlotTwoFts/AHalf.lean`: the a.e.-in-`z` bookkeeping, the domination of
`HkSq α 0 (∂_θ²A)` by the two shifted slots, the pointwise-plus-slice-Poincaré reduction of
`Tk α 2 A` to `HkSq α 0 (∂_θ²A)`, and the final assembly.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Final.Rep.TopSlotTwoFts.AHalf

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
