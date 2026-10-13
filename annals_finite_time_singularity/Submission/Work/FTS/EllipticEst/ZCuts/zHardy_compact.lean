import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.zHardyDefs
import Submission.Work.FTS.EllipticEst.zHardyCutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.ZCuts

open scoped Real Topology Interval
open MeasureTheory Set Filter

noncomputable section

/-! ## Auxiliary facts about the weight `w` and the function `zA`

These are the ingredients of the compactly supported weighted Hardy inequality
`zHardy_compact`: smoothness of `w` and of `zA` on `(0,∞)`, and the fact that a
function vanishing on a neighbourhood of a point has vanishing derivative there. -/

/-- A function which vanishes on a neighbourhood of `x` has derivative `0` at `x`. -/
theorem zc_deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {x : ℝ}
    (h : f =ᶠ[𝓝 x] 0) : deriv f x = 0 := by
  have h' := h.deriv_eq
  simpa using h'

/-- The function `zA` is `C^∞` on `(0,∞)`. -/
theorem zc_contDiffOn_zA : ContDiffOn ℝ smoothOrder (fun z : ℝ => zA z) (Set.Ioi 0) := by
  show ContDiffOn ℝ smoothOrder (fun z : ℝ => (z - 3) / (2 * (1 + z))) (Set.Ioi 0)
  refine ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  have hz' : (0 : ℝ) < z := hz
  positivity

/-- The weight `w` is `C^∞` on `(0,∞)`. -/
theorem zc_contDiffOn_w : ContDiffOn ℝ smoothOrder (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  show ContDiffOn ℝ smoothOrder (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
  refine ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  exact pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < z from hz))

theorem zHardy_compact {h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hcd : ContDiffOn ℝ smoothOrder h (Set.Ioi 0))
    (hsupp : ∀ z, z ≤ a ∨ b ≤ z → h z = 0) :
    (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * h z ^ 2)
      ≤ 4 * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 := by
  have hab' : a ≤ b := le_of_lt hab
  have hIcc_sub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  -- ## The derivative of `h` vanishes away from `[a,b]`
  have hzero_left : ∀ z, z < a → deriv h z = 0 := by
    intro z hz
    have hlt : 0 < (a - z) / 2 := by linarith
    have hev : h =ᶠ[𝓝 z] 0 := by
      filter_upwards [Metric.ball_mem_nhds z hlt] with y hy
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have hya : y < a := by
        have := (abs_lt.mp hy).2
        linarith
      exact hsupp y (Or.inl (le_of_lt hya))
    exact zc_deriv_eq_zero_of_eventuallyEq_zero hev
  have hzero_right : ∀ z, b < z → deriv h z = 0 := by
    intro z hz
    have hlt : 0 < (z - b) / 2 := by linarith
    have hev : h =ᶠ[𝓝 z] 0 := by
      filter_upwards [Metric.ball_mem_nhds z hlt] with y hy
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have hyb : b ≤ y := by
        have := (abs_lt.mp hy).1
        linarith
      exact hsupp y (Or.inr hyb)
    exact zc_deriv_eq_zero_of_eventuallyEq_zero hev
  -- ## Both integrands vanish on `(0,∞) \ [a,b]`
  have hFsupp : ∀ z ∈ Set.Ioi 0 \ Set.Icc a b,
      (Work.Spaces.w z) ^ 2 * h z ^ 2 = 0 := by
    intro z hz
    obtain ⟨hz0, hznot⟩ := hz
    have hzab : z ≤ a ∨ b ≤ z := by
      by_contra hcon
      rw [not_or] at hcon
      exact hznot ⟨le_of_lt (not_le.mp hcon.1), le_of_lt (not_le.mp hcon.2)⟩
    simp [hsupp z hzab]
  have hGsupp : ∀ z ∈ Set.Ioi 0 \ Set.Icc a b,
      (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 = 0 := by
    intro z hz
    obtain ⟨hz0, hznot⟩ := hz
    have hzab : z < a ∨ b < z := by
      by_contra hcon
      rw [not_or] at hcon
      exact hznot ⟨not_lt.mp hcon.1, not_lt.mp hcon.2⟩
    rcases hzab with hzab | hzab
    · simp [hzero_left z hzab]
    · simp [hzero_right z hzab]
  -- ## The integrals over `(0,∞)` are the integrals over `[a,b]`
  have hIF : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * h z ^ 2)
      = ∫ z in Set.Icc a b, (Work.Spaces.w z) ^ 2 * h z ^ 2 :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioi hIcc_sub hFsupp
  have hIG : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
      = ∫ z in Set.Icc a b, (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioi hIcc_sub hGsupp
  have hIcc_int_F : (∫ z in Set.Icc a b, (Work.Spaces.w z) ^ 2 * h z ^ 2)
      = ∫ z in a..b, (Work.Spaces.w z) ^ 2 * h z ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab']
  have hIcc_int_G : (∫ z in Set.Icc a b, (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
      = ∫ z in a..b, (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab']
  -- ## The flux `Φ = zA · h² · w² · z` of the completion of squares
  set Φ : ℝ → ℝ := fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y with hΦ
  have hflux_cd : ContDiffOn ℝ smoothOrder Φ (Set.Ioi 0) := by
    rw [hΦ]
    exact ((zc_contDiffOn_zA.mul (hcd.pow 2)).mul (zc_contDiffOn_w.pow 2)).mul contDiffOn_id
  have hflux_cont : ContinuousOn Φ (Set.Icc a b) := hflux_cd.continuousOn.mono hIcc_sub
  have hflux_deriv_cont : ContinuousOn (deriv Φ) (Set.Icc a b) :=
    (hflux_cd.deriv_of_isOpen (m := smoothOrder) isOpen_Ioi (by simp [smoothOrder])).continuousOn.mono hIcc_sub
  have hflux_deriv_II : IntervalIntegrable (deriv Φ) volume a b :=
    ContinuousOn.intervalIntegrable (by simpa [Set.uIcc_of_le hab'] using hflux_deriv_cont)
  have hhasderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt Φ (deriv Φ x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha hx.1
    have hdh : HasDerivAt h (deriv h x) x :=
      (hcd.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hx0)
    have h0 := hasDerivAt_zFlux h hx0 hdh
    have h1 : HasDerivAt Φ (zFluxD h (deriv h x) x) x := by
      rw [hΦ]
      exact h0
    rw [h1.deriv]
    exact h1
  -- ## The boundary term vanishes
  have hFTC : (∫ x in a..b, deriv Φ x) = 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab' hflux_cont hhasderiv
      hflux_deriv_II
    rw [hftc, hΦ]
    have hb : h b = 0 := hsupp b (Or.inr le_rfl)
    have ha' : h a = 0 := hsupp a (Or.inl le_rfl)
    simp [hb, ha']
  -- ## The pointwise inequality of the completion of squares
  have hpt : ∀ z ∈ Set.Icc a b, 0 ≤ 4 * ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
      - (Work.Spaces.w z) ^ 2 * h z ^ 2 + 4 * deriv Φ z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hdh : HasDerivAt h (deriv h z) z :=
      (hcd.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hz0)
    have hp := zHardy_pointwise h hz0 hdh
    have hΦd : deriv Φ z = deriv (fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y) z := by
      rw [hΦ]
    linarith [hp, hΦd]
  have hnonneg : 0 ≤ ∫ x in a..b, (4 * ((Work.Spaces.w x) ^ 2 * (x * deriv h x) ^ 2)
      - (Work.Spaces.w x) ^ 2 * h x ^ 2 + 4 * deriv Φ x) :=
    intervalIntegral.integral_nonneg hab' hpt
  -- ## Interval integrability of the pieces
  have hcont_w : ContinuousOn Work.Spaces.w (Set.Icc a b) :=
    zc_contDiffOn_w.continuousOn.mono hIcc_sub
  have hcont_h : ContinuousOn h (Set.Icc a b) := hcd.continuousOn.mono hIcc_sub
  have hcont_dh : ContinuousOn (deriv h) (Set.Icc a b) :=
    (hcd.deriv_of_isOpen (m := smoothOrder) isOpen_Ioi (by simp [smoothOrder])).continuousOn.mono hIcc_sub
  have hcontG : ContinuousOn (fun x => (Work.Spaces.w x) ^ 2 * (x * deriv h x) ^ 2)
      (Set.Icc a b) := by
    fun_prop
  have hcontF : ContinuousOn (fun x => (Work.Spaces.w x) ^ 2 * h x ^ 2) (Set.Icc a b) := by
    fun_prop
  have hII_G : IntervalIntegrable (fun x => (Work.Spaces.w x) ^ 2 * (x * deriv h x) ^ 2)
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab']
    exact hcontG
  have hII_F : IntervalIntegrable (fun x => (Work.Spaces.w x) ^ 2 * h x ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab']
    exact hcontF
  have hII_4G : IntervalIntegrable (fun x => 4 * ((Work.Spaces.w x) ^ 2 * (x * deriv h x) ^ 2))
      volume a b := hII_G.const_mul 4
  have hII_4dΦ : IntervalIntegrable (fun x => 4 * deriv Φ x) volume a b :=
    hflux_deriv_II.const_mul 4
  -- ## Splitting the integral of the sum
  have hsplit : (∫ x in a..b, (4 * ((Work.Spaces.w x) ^ 2 * (x * deriv h x) ^ 2)
        - (Work.Spaces.w x) ^ 2 * h x ^ 2 + 4 * deriv Φ x))
      = 4 * (∫ x in a..b, (Work.Spaces.w x) ^ 2 * (x * deriv h x) ^ 2)
        - (∫ x in a..b, (Work.Spaces.w x) ^ 2 * h x ^ 2)
        + 4 * (∫ x in a..b, deriv Φ x) := by
    rw [intervalIntegral.integral_add (hII_4G.sub hII_F) hII_4dΦ,
      intervalIntegral.integral_sub hII_4G hII_F,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- ## The Hardy inequality on `[a,b]`
  have key : (∫ x in a..b, (Work.Spaces.w x) ^ 2 * h x ^ 2)
      ≤ 4 * ∫ x in a..b, (Work.Spaces.w x) ^ 2 * (x * deriv h x) ^ 2 := by
    have hh := hnonneg
    rw [hsplit, hFTC] at hh
    linarith
  calc (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * h z ^ 2)
      = ∫ z in Set.Icc a b, (Work.Spaces.w z) ^ 2 * h z ^ 2 := hIF
    _ = ∫ z in a..b, (Work.Spaces.w z) ^ 2 * h z ^ 2 := hIcc_int_F
    _ ≤ 4 * ∫ z in a..b, (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 := key
    _ = 4 * ∫ z in Set.Icc a b, (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 := by
          rw [← hIcc_int_G]
    _ = 4 * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 := by
          rw [hIG]

end

end Work.FTS.EllipticEst.ZCuts
