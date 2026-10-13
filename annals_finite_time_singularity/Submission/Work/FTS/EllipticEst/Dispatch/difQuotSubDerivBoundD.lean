/-
Copyright: work module for the Elgindi finite-time singularity project.

# The second-order Taylor bound for the difference quotient of the angular moment

`F_*(u)(z) = ∫_θ u(z,θ) sinθcos²θ dθ` is, for `u` smooth on the open quadrant, differentiable in
`z` with derivative `F_*(∂_zu)(z)`.  This module proves the *quantitative* form of that
statement: the difference quotient over `[z - h, z]` differs from `F_*(∂_zu)(z)` by at most the
angular integral of the second radial derivative,

`|(F_*u(z) − F_*u(z−h))/h − F_*(∂_zu)(z)| ≤ ∫_θ (∫_{z−h}^z |∂_z²u(x,θ)| dx) |sinθcos²θ|`.

This is the analytic input of the moment chain of the almost-everywhere class.  The statement and
proof follow `Submission/Work/FTS/EllipticEst/AngAWeak/difQuotSubDerivBound.lean` (which is a
`sorry`) but avoid its import of `Honest.HonDifQuotBound` (unused there, and blocking: that module
declares `Honest.contDiffOn_slice`, clashing with the declaration of the same name in
`Honest.HonSliceRightTendsto`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

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
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `sinθcos²θ` vanishes on `Iθ` only at the two endpoints. -/
private theorem sinCos2_ne_zero_iff {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≠ 0 ↔ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  constructor
  · intro h
    have hsin : Real.sin θ ≠ 0 := fun h0 => h (by rw [Work.Elliptic.sinCos2, h0, zero_mul])
    have hcos : Real.cos θ ≠ 0 := fun h0 => h (by rw [Work.Elliptic.sinCos2, h0]; ring)
    refine ⟨lt_of_le_of_ne hθ.1 (fun h0 => hsin (by rw [← h0, Real.sin_zero])),
      lt_of_le_of_ne hθ.2 ?_⟩
    intro h2
    exact hcos (by rw [h2, Real.cos_pi_div_two])
  · intro h
    rw [Work.Elliptic.sinCos2]
    refine mul_ne_zero ?_ (pow_ne_zero 2 ?_)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1])
        (by linarith [h.2, Real.pi_pos]))
    · exact ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [h.1, Real.pi_pos], by linarith [h.2, Real.pi_pos]⟩)

/-- The radial second derivative of a slice is continuous on `(0,∞)`. -/
private theorem continuousOn_pzIter_two_slice {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContinuousOn (fun y : ℝ => Work.Spaces.pzIter 2 u y θ) (Set.Ioi 0) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have h2 : ContDiffOn ℝ 2 (fun y : ℝ => u y θ) (Set.Ioi 0) :=
    contDiffOn_iff_forall_nat_le.mp (hSO.curry_z hθ) 2 le_top
  have hd1 : ContDiffOn ℝ 1 (deriv (fun y : ℝ => u y θ)) (Set.Ioi 0) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hd2 : ContDiffOn ℝ 0 (deriv (deriv (fun y : ℝ => u y θ))) (Set.Ioi 0) :=
    hd1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hid : (fun y : ℝ => Work.Spaces.pzIter 2 u y θ)
      = fun y : ℝ => deriv (deriv (fun y' : ℝ => u y' θ)) y := by
    funext y
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  rw [hid]
  exact hd2.continuousOn

theorem difQuotSubDerivBoundD {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hψ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hp1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {z hh : ℝ} (hz : 0 < z) (hh0 : 0 < hh) (hhz : hh < z / 2)
    (hbox : MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc (z - hh) z ×ˢ Work.Spaces.Iθ)) :
    |(Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
        - Work.Elliptic.Fstar (Work.Spaces.pz u) z|
      ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
  have hz' : 0 < z - hh := by linarith
  have hlt : z - hh < z := by linarith
  have hle : z - hh ≤ z := le_of_lt hlt
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  -- ## Step 1: the difference of the two moments
  have hsub : Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)
      = ∫ θ in Work.Spaces.Iθ,
          (u z θ - u (z - hh) θ) * Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar,
      ← MeasureTheory.integral_sub (hψ z hz) (hψ (z - hh) hz')]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  -- ## Step 2: the pointwise slice bound
  have hslice : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ|
        ≤ ∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ| := by
    intro θ hθ
    -- the fundamental rule of calculus along the slice
    have hderiv1 : ∀ x ∈ Set.uIcc (z - hh) z,
        HasDerivAt (fun y : ℝ => u y θ) (Work.Spaces.pz u x θ) x := by
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      exact hSO.hasDerivAt_slice hθ (lt_of_lt_of_le hz' hx.1)
    have hcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.pz u x θ)
        (Set.uIcc (z - hh) z) := by
      rw [Set.uIcc_of_le hle]
      exact ((hSO.pz).curry_z hθ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz' hx.1)
    have hFTC1 : ∫ x in (z - hh)..z, Work.Spaces.pz u x θ = u z θ - u (z - hh) θ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv1 hcont1.intervalIntegrable
    -- the mean-value bound on the derivative
    have hMVT : ∀ x ∈ Set.Icc (z - hh) z,
        |Work.Spaces.pz u x θ - Work.Spaces.pz u z θ|
          ≤ ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hz' hx.1
      have hxx : x ≤ z := hx.2
      have hderiv2 : ∀ y ∈ Set.uIcc x z,
          HasDerivAt (fun y : ℝ => Work.Spaces.pz u y θ) (Work.Spaces.pzIter 2 u y θ) y := by
        intro y hy
        rw [Set.uIcc_of_le hxx] at hy
        have hy0 : 0 < y := lt_of_lt_of_le hxpos hy.1
        have h1 := hSO.hasDerivAt_slice_pzIter 1 hθ hy0
        simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h1
      have hcont2 : ContinuousOn (fun y : ℝ => Work.Spaces.pzIter 2 u y θ) (Set.uIcc x z) := by
        rw [Set.uIcc_of_le hxx]
        exact (continuousOn_pzIter_two_slice hsm hθ).mono (fun y hy => lt_of_lt_of_le hxpos hy.1)
      have hFTC2 : ∫ y in x..z, Work.Spaces.pzIter 2 u y θ
          = Work.Spaces.pz u z θ - Work.Spaces.pz u x θ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2 hcont2.intervalIntegrable
      have hcontabs : ContinuousOn (fun y : ℝ => |Work.Spaces.pzIter 2 u y θ|)
          (Set.uIcc (z - hh) z) := by
        rw [Set.uIcc_of_le hle]
        exact (continuousOn_pzIter_two_slice hsm hθ).abs.mono
          (fun y hy => lt_of_lt_of_le hz' hy.1)
      have hle1 : ∫ y in x..z, |Work.Spaces.pzIter 2 u y θ|
          ≤ ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| :=
        intervalIntegral.integral_mono_interval hx.1 hxx le_rfl
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
            (fun y _ => abs_nonneg _))
          hcontabs.intervalIntegrable
      calc |Work.Spaces.pz u x θ - Work.Spaces.pz u z θ|
          = |∫ y in x..z, Work.Spaces.pzIter 2 u y θ| := by rw [hFTC2, abs_sub_comm]
        _ ≤ ∫ y in x..z, |Work.Spaces.pzIter 2 u y θ| :=
            intervalIntegral.abs_integral_le_integral_abs hxx
        _ ≤ ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := hle1
    -- assemble
    have hconst : ∫ x in (z - hh)..z, Work.Spaces.pz u z θ = hh * Work.Spaces.pz u z θ := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    have hInt1 : ∫ x in (z - hh)..z, (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ)
        = (u z θ - u (z - hh) θ) - hh * Work.Spaces.pz u z θ := by
      rw [intervalIntegral.integral_sub hcont1.intervalIntegrable intervalIntegrable_const,
        hFTC1, hconst]
    have hdiff : (u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ
        = (1 / hh) * ∫ x in (z - hh)..z,
            (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ) := by
      rw [hInt1]
      field_simp
    rw [hdiff, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / hh)]
    have hbnd : |∫ x in (z - hh)..z, (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ)|
        ≤ hh * ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
      calc |∫ x in (z - hh)..z, (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ)|
          ≤ ∫ x in (z - hh)..z, |Work.Spaces.pz u x θ - Work.Spaces.pz u z θ| :=
            intervalIntegral.abs_integral_le_integral_abs hle
        _ ≤ ∫ x in (z - hh)..z, ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
            refine intervalIntegral.integral_mono_on hle ?_ intervalIntegrable_const ?_
            · exact ((hcont1.sub continuousOn_const).abs).intervalIntegrable
            · intro x hx
              exact hMVT x hx
        _ = hh * ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
            rw [intervalIntegral.integral_const]
            simp only [smul_eq_mul]
            ring
    calc (1 / hh) * |∫ x in (z - hh)..z, (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ)|
        ≤ (1 / hh) * (hh * ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ|) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ = ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
          field_simp
  -- ## Step 3: integrate the pointwise bound against `|sinθcos²θ|`
  have hAsub : (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
      = ∫ θ in Work.Spaces.Iθ,
          ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ := by
    rw [hsub, ← MeasureTheory.integral_div]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  have hintA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (u z θ - u (z - hh) θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      ((hψ z hz).sub (hψ (z - hh) hz')).congr
        (Filter.Eventually.of_forall fun θ => by simp only [Pi.sub_apply]; ring)
    refine (h1.div_const hh).congr (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hcomb : (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
        - Work.Elliptic.Fstar (Work.Spaces.pz u) z
      = ∫ θ in Work.Spaces.Iθ,
          (((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
            - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ) := by
    rw [hAsub, Work.Elliptic.Fstar,
      ← MeasureTheory.integral_sub hintA (hp1 z hz)]
  -- the majorant is integrable in `θ`
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
        * |Work.Elliptic.sinCos2 θ|) Work.Spaces.Iθ := by
    have hjoint : MeasureTheory.Integrable
        (Function.uncurry (fun x θ : ℝ =>
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
        ((MeasureTheory.volume.restrict (Set.Icc (z - hh) z)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.Measure.prod_restrict]
      exact hbox
    have h1 : MeasureTheory.Integrable
        (fun θ : ℝ => ∫ x, |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|
          ∂(MeasureTheory.volume.restrict (Set.Icc (z - hh) z)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hjoint.integral_prod_right
    refine h1.congr ?_
    filter_upwards with θ
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc),
      ← MeasureTheory.integral_mul_const]
  -- the pointwise bound on the integrand
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
          - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ‖
        ≤ (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, show ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
        - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ
        = (((u z θ - u (z - hh) θ) / hh) - Work.Spaces.pz u z θ)
          * Work.Elliptic.sinCos2 θ from by ring, abs_mul]
    by_cases hs : Work.Elliptic.sinCos2 θ = 0
    · simp [hs]
    · exact mul_le_mul_of_nonneg_right
        (hslice θ ((sinCos2_ne_zero_iff hθ).mp hs)) (abs_nonneg _)
  calc |(Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
          - Work.Elliptic.Fstar (Work.Spaces.pz u) z|
      = ‖∫ θ in Work.Spaces.Iθ,
          (((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
            - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ)‖ := by
        rw [hcomb, Real.norm_eq_abs]
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          ‖((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
            - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ hmaj_int hpt
        exact Filter.Eventually.of_forall fun θ => norm_nonneg _

end Work.FTS.EllipticEst.Dispatch
