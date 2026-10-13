import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.honSliceIntFacts
import Submission.Work.FTS.EllipticEst.Honest.honLintegralSliceBridge
import Submission.Work.FTS.EllipticEst.Honest.honYcBound
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.Honest.FOH.psiRho
import Submission.Work.FTS.EllipticEst.Honest.Step1.pthCore
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open MeasureTheory
open scoped ENNReal

/-! ## The `HkMem ↔ σ` transfer lemmas

`HkIntegrand α 0 g z θ = (g z θ · w z / sin(2θ)^{η/2})²`, and on `Iθ` the pointwise identity
`(g z θ · (w z / sin(2θ)^{η/2}))² = (w z)² · (g z θ)² · sin(2θ)^{-η}` holds
(`sq_profile_eq`).  This is the bridge between the `HkMem`/`HkSq` vocabulary and the slice
lemmas of the `Honest` chapter, which are stated with the weight `σ θ = sin(2θ)^{-η}`
(`AngSecond.sig = sEta`). -/

/-- **Pointwise normalisation of the level-`0` integrand.**  On `Iθ`,
`HkIntegrand α 0 g z θ = (w z)² · ((g z θ)² · σ θ)`. -/
theorem hkIntegrand_eq_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  rw [HkIntegrand_zero_eq α g z θ,
    sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- **From the `σ`-integrability of a slice to the integrability of its `HkIntegrand` slice.** -/
theorem integrableOn_HkIntegrand_of_sig {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (h : MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iθ := by
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2
        * ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn] at h ⊢
    exact h.const_mul ((Work.Spaces.w z) ^ 2)
  refine h2.congr_fun ?_ measurableSet_Icc
  intro θ hθ
  exact (hkIntegrand_eq_w_sq α g hθ).symm

/-- At `z = 0` the level-`0` `HkIntegrand` vanishes identically (the radial weight is `0`). -/
theorem HkIntegrand_eq_zero_left (α : ℝ) (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g 0 θ = 0 := by
  rw [HkIntegrand_zero_eq]
  have h : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
  rw [h]
  simp

/-- **Slicewise integrability transfer, handling the `z = 0` case.** -/
theorem integrableOn_HkIntegrand_of_ne_zero {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (h : z ≠ 0 → MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iθ := by
  by_cases hz0 : z = 0
  · subst hz0
    rw [show (fun θ => Work.Spaces.HkIntegrand α 0 g 0 θ) = fun _ => (0 : ℝ) from
      funext fun θ => HkIntegrand_eq_zero_left α g θ]
    exact MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  · exact integrableOn_HkIntegrand_of_sig (h hz0)

/-- The `θ`-`∫⁻` is invariant under a pointwise change of the integrand. -/
theorem lintegral_w2_congr {a b : ℝ → ℝ → ℝ} (h : ∀ z θ, a z θ = b z θ) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (a z θ)))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (b z θ)) := by
  refine MeasureTheory.lintegral_congr fun z => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [h z θ]

/-- **The `∫⁻`-functional of a profile is `ofReal (HkSq)`**, for honest data.  This is the
bridge used to turn the `∫⁻`-bounds of `honYcBound` into bounds on `HkSq`. -/
theorem lintegral_sig_eq_ofReal_HkSq {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)))
      = ENNReal.ofReal (Work.Spaces.HkSq α 0 g) := by
  obtain ⟨hInt, hval⟩ := hksq_eq_w2_sliceIntegral (α := α) hg
  -- Step 1: identify the `z`-integrand a.e. with `ofReal (∫θ HkIntegrand)`.
  have hae : (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz0 with h0 | hpos
    · subst h0
      have hw : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      have hI : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g 0 θ) = 0 := by
        simp [HkIntegrand_eq_zero_left α g]
      show ENNReal.ofReal ((Work.Spaces.w 0) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            ((g 0 θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g 0 θ)
      rw [hw, hI]
      simp
    · exact (ofReal_slice_HkIntegrand_eq α g hpos (hg.1 z hz)).symm
  rw [MeasureTheory.lintegral_congr_ae hae]
  -- Step 2: `ofReal` of the Bochner integral of the partial `θ`-integral.
  have hInt2 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) Work.Spaces.Iz := by
    rw [MeasureTheory.IntegrableOn] at hInt ⊢
    exact hInt.congr (Filter.Eventually.of_forall fun z =>
      w2_mul_slice_eq_HkIntegrand_slice α g z)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2
    (Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)]
  have hgoal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 g z θ) = Work.Spaces.HkSq α 0 g := by
    rw [← hval]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici
      (fun z _ => (w2_mul_slice_eq_HkIntegrand_slice α g z).symm)
  rw [hgoal]

/-- **The first-order honest estimate.** -/
theorem firstOrderHonest : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.Honest.Hon α F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  -- the three inputs of the estimate
  obtain ⟨CY, hCYpos, hphi⟩ := FOH.psiRhoBound
  obtain ⟨CX, hCXpos, hth⟩ := Step1.pthCore
  obtain ⟨CC, hCCpos, hYc⟩ := honYcBound
  obtain ⟨CDz, hCDzpos, hzag⟩ := HkNorm_Dz_le_open 0
  set K : ℝ := CC * (CY + CX ^ 2) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]; positivity
  refine ⟨max (Real.sqrt CY) (Real.sqrt K) + 1, by
    have h : 0 ≤ max (Real.sqrt CY) (Real.sqrt K) :=
      le_trans (Real.sqrt_nonneg CY) (le_max_left _ _)
    linarith, ?_⟩
  intro α F Ψ h
  have hα : 0 < α := h.hα
  -- ## the two Step-1 bounds and the honesty of `Ψ`
  obtain ⟨hmemΨ, hYb⟩ := hphi α F Ψ h
  obtain ⟨hmemPth, hXb⟩ := hth α F Ψ h
  -- ## conjunct 2: the honesty of `z ∂_z Ψ` (radial Agmon)
  have hα1 : α ≤ 1 := by linarith [h.hα, h.hα4]
  have hmemG : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    (hzag α Ψ h.hα hα1 h.sm hmemΨ h.memA).1
  -- ## conjuncts 3 and 5: `Ψ / cos θ` through the slicewise Hardy bound
  set Yv : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ) ^ 2)) with hYv
  set Xv : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (Work.FTS.EllipticEst.AngSecond.sig θ * (Work.Spaces.pth Ψ z θ) ^ 2)) with hXv
  set Wv : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (Work.FTS.EllipticEst.AngSecond.sig θ * (Ψ z θ / Real.cos θ) ^ 2)) with hWv
  have hWb : Wv ≤ ENNReal.ofReal CC * (Yv + Xv) := hYc α F Ψ h
  -- the two functionals are `ofReal (HkSq ·)`
  have hYeq : Yv = ENNReal.ofReal (Work.Spaces.HkSq α 0 Ψ) := by
    rw [hYv, lintegral_w2_congr (fun z θ => by rw [mul_comm])]
    exact lintegral_sig_eq_ofReal_HkSq hmemΨ
  have hXeq : Xv = ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ)) := by
    rw [hXv, lintegral_w2_congr (fun z θ => by rw [mul_comm])]
    exact lintegral_sig_eq_ofReal_HkSq hmemPth
  -- the resulting bound on `Wv`
  have hWval : Wv ≤ ENNReal.ofReal (CC * (Work.Spaces.HkSq α 0 Ψ
      + Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ))) := by
    refine le_trans hWb ?_
    rw [hYeq, hXeq,
      ← ENNReal.ofReal_add (HkSq_zero_nonneg α Ψ) (HkSq_zero_nonneg α (Work.Spaces.pth Ψ)),
      ← ENNReal.ofReal_mul hCCpos.le]
  -- the smoothness of `Ψ / cos θ` on the open quadrant
  have hsmW : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => Ψ z θ / Real.cos θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry Ψ)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.sm n
    have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (Real.cos p.2)⁻¹)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      refine ContDiffOn.inv ?_ ?_
      · fun_prop
      · intro p hp
        exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
    rw [show Function.uncurry (fun z θ => Ψ z θ / Real.cos θ)
        = Function.uncurry Ψ * (fun p : ℝ × ℝ => (Real.cos p.2)⁻¹) from
      funext fun p => by simp [Function.uncurry, div_eq_mul_inv]]
    exact h1.mul h2
  -- the per-slice integrability of the `HkIntegrand` of `Ψ / cos θ`
  have hslice := honSliceIntFacts α F Ψ h
  have hslW : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) z θ)
      Work.Spaces.Iθ := by
    intro z hzI
    refine integrableOn_HkIntegrand_of_ne_zero (fun hz0 => ?_)
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    exact (hslice z hzpos).2.2.2
  -- the `∫⁻`-bound in the factor order required by the bridge
  have hCbridge : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (((fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)))
      ≤ ENNReal.ofReal (CC * (Work.Spaces.HkSq α 0 Ψ
          + Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ))) := by
    rw [lintegral_w2_congr (a := fun z θ => (Ψ z θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (b := fun z θ => Work.FTS.EllipticEst.AngSecond.sig θ
        * (Ψ z θ / Real.cos θ) ^ 2) (fun z θ => mul_comm _ _)]
    exact hWval
  obtain ⟨hmemW, hWsq⟩ := honLintegralSliceBridge hsmW hslW hCbridge
    (by have h1 := HkSq_zero_nonneg α Ψ
        have h2 := HkSq_zero_nonneg α (Work.Spaces.pth Ψ)
        nlinarith [hCCpos])
  -- ## the final numeric bounds
  set N : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 F)
      + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) with hN
  have hN0 : 0 ≤ N := by
    rw [hN]; positivity
  have hNsq : Work.Spaces.HkSq α 0 F ≤ N ^ 2 := by
    have h1 : Real.sqrt (Work.Spaces.HkSq α 0 F) ≤ N := by
      rw [hN]
      have h2 := mul_nonneg hα.le
        (Real.sqrt_nonneg (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)))
      linarith
    nlinarith [Real.sq_sqrt (HkSq_zero_nonneg α F), h1,
      Real.sqrt_nonneg (Work.Spaces.HkSq α 0 F), hN0]
  have hXsq : Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ) ≤ (CX * N) ^ 2 := by
    have h1 : Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ)) ≤ CX * N := by
      rw [hN]; exact hXb
    have h3 : 0 ≤ CX * N := le_trans (Real.sqrt_nonneg _) h1
    nlinarith [Real.sq_sqrt (HkSq_zero_nonneg α (Work.Spaces.pth Ψ)), h1, h3,
      Real.sqrt_nonneg (Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ))]
  have hYsq : Work.Spaces.HkSq α 0 Ψ ≤ CY * N ^ 2 := by
    have h2 : CY * Work.Spaces.HkSq α 0 F ≤ CY * N ^ 2 :=
      mul_le_mul_of_nonneg_left hNsq hCYpos.le
    linarith [hYb, h2]
  have hKbound : Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ) ≤ K * N ^ 2 := by
    have hB : Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ) ≤ CX ^ 2 * N ^ 2 := by
      have h := hXsq
      nlinarith [h, sq_nonneg (CX * N)]
    rw [hKdef]
    nlinarith [hWsq, hYsq, hB, hN0, hCCpos.le, sq_nonneg N]
  refine ⟨hmemΨ, hmemG, hmemW, ?_, ?_⟩
  · -- the `√(HkSq Ψ)` bound
    have h1 : Real.sqrt (Work.Spaces.HkSq α 0 Ψ) ≤ Real.sqrt CY * N := by
      calc Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          ≤ Real.sqrt (CY * Work.Spaces.HkSq α 0 F) := Real.sqrt_le_sqrt hYb
        _ = Real.sqrt CY * Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_mul hCYpos.le _
        _ ≤ Real.sqrt CY * N := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg CY)
            rw [hN]
            have h2 := mul_nonneg hα.le
              (Real.sqrt_nonneg (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)))
            linarith
    have h3 : Real.sqrt CY ≤ max (Real.sqrt CY) (Real.sqrt K) + 1 := by
      linarith [le_max_left (Real.sqrt CY) (Real.sqrt K)]
    calc Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        ≤ Real.sqrt CY * N := h1
      _ ≤ (max (Real.sqrt CY) (Real.sqrt K) + 1) * N := by
          refine mul_le_mul h3 le_rfl hN0 ?_
          linarith [Real.sqrt_nonneg CY, Real.sqrt_nonneg K,
            le_max_left (Real.sqrt CY) (Real.sqrt K)]
      _ = (max (Real.sqrt CY) (Real.sqrt K) + 1)
            * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0
                  (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
          rw [hN]
  · -- the `√(HkSq (Ψ/cos))` bound
    have h1 : Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ Real.sqrt K * N := by
      calc Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ Real.sqrt (K * N ^ 2) := Real.sqrt_le_sqrt hKbound
        _ = Real.sqrt K * Real.sqrt (N ^ 2) := Real.sqrt_mul hKpos.le _
        _ = Real.sqrt K * N := by rw [Real.sqrt_sq hN0]
    have h3 : Real.sqrt K ≤ max (Real.sqrt CY) (Real.sqrt K) + 1 := by
      linarith [le_max_right (Real.sqrt CY) (Real.sqrt K)]
    calc Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ Real.sqrt K * N := h1
      _ ≤ (max (Real.sqrt CY) (Real.sqrt K) + 1) * N := by
          refine mul_le_mul h3 le_rfl hN0 ?_
          linarith [Real.sqrt_nonneg CY, Real.sqrt_nonneg K,
            le_max_right (Real.sqrt CY) (Real.sqrt K)]
      _ = (max (Real.sqrt CY) (Real.sqrt K) + 1)
            * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0
                  (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
          rw [hN]

end Work.FTS.EllipticEst.Honest
