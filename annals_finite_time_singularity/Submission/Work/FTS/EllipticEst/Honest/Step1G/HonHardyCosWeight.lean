import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.SharpHardyCosWeight
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.sharpHardyCosOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.Step1G

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! # The sharp weighted Hardy inequality with a `cos²(2θ)` weight, honest hypotheses

This file proves `HonHardyCosWeight`: for `0 ≤ η < 1` there is `C > 0` such that for every
`f : ℝ → ℝ` of class `C²` on the *open* interval `(0, π/2)` whose one-sided limits at the two
endpoints vanish and whose two `η`-weighted energies `∫ f² sin(2θ)^{-η}` and
`∫ (f')² sin(2θ)^{-η}` are finite,

`∫ f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫ (f')² sin(2θ)^{-η} + C ∫ f² sin(2θ)^{-η}`.

The sharp constant `(1+η)^{-2}` is produced by the *half-interval* form of the inequality,
`Work.FTS.EllipticEst.H2W.AeWAux.leftHalfSharp`, which is the open-interval version of the
classical sharp Hardy inequality (no boundary condition at the singular endpoint is needed: the
finiteness of the `cos²`-weighted singular integral supplies the endpoint decay).  The halves
`(0, π/4)` and `(π/4, π/2)` are glued after reflecting the second one by `θ ↦ π/2 - θ` (under
which `sin(2θ)` is invariant and `cos(2θ)` changes sign, so the `cos²`-weight is preserved).

The case in which the left-hand integrand is *not* integrable needs separate treatment:
Mathlib's totalised integral assigns it the value `0`, and then the claim reduces to the
nonnegativity of the right-hand side.
-/

/-! ## Auxiliary facts about the reflection `θ ↦ π/2 - θ` and about splitting `(0, π/2)` -/

private lemma cos_two_pi_half_sub (x : ℝ) :
    Real.cos (2 * (Real.pi / 2 - x)) = -Real.cos (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.cos_pi_sub]

private lemma sin_two_pi_half_sub (x : ℝ) :
    Real.sin (2 * (Real.pi / 2 - x)) = Real.sin (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

private lemma intervalIntegrable_iff_integrableOn_Ioo {a b : ℝ} (hab : a ≤ b) {H : ℝ → ℝ} :
    IntervalIntegrable H volume a b ↔ IntegrableOn H (Set.Ioo a b) := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact ⟨fun h => h.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc,
    fun h => h.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm⟩

/-- Change of variables `θ ↦ π/2 - θ` for integrability over the right half. -/
private lemma integrableOn_Ioo_reflect_right {G : ℝ → ℝ}
    (hG : IntegrableOn G (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    IntegrableOn (fun x => G (Real.pi / 2 - x)) (Set.Ioo 0 (Real.pi / 4)) := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hii : IntervalIntegrable G volume (Real.pi / 4) (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le h4le]
    exact hG.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hii' : IntervalIntegrable (fun x => G (Real.pi / 2 - x)) volume 0 (Real.pi / 4) := by
    have h := hii.comp_sub_left (Real.pi / 2)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
      show Real.pi / 2 - Real.pi / 2 = 0 by ring] at h
    exact h.symm
  exact (intervalIntegrable_iff_integrableOn_Ioo (a := 0) (b := Real.pi / 4) h4).mp hii'

/-- Change of variables `θ ↦ π/2 - θ` for integrals over the right half. -/
private lemma integral_Ioo_reflect_right (F : ℝ → ℝ) :
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ)
      = ∫ x in Set.Ioo 0 (Real.pi / 4), F (Real.pi / 2 - x) := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le h4le, ← intervalIntegral.integral_of_le h4]
  rw [intervalIntegral.integral_comp_sub_left F (Real.pi / 2)]
  rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
    show Real.pi / 2 - 0 = Real.pi / 2 by ring]

/-- Splitting an integral over `(0, π/2)` into its two halves. -/
private lemma integral_Ioo_split {H : ℝ → ℝ}
    (h1 : IntervalIntegrable H volume 0 (Real.pi / 4))
    (h2 : IntervalIntegrable H volume (Real.pi / 4) (Real.pi / 2)) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), H θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 4), H θ)
        + ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), H θ := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h2le : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have e1 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), H θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), H θ := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo.symm,
      ← intervalIntegral.integral_of_le h2le]
  have e2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), H θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 4), H θ := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo.symm,
      ← intervalIntegral.integral_of_le h4]
  have e3 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), H θ)
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), H θ := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo.symm,
      ← intervalIntegral.integral_of_le h4le]
  rw [e1, e2, e3]
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

/-! ## The inequality on `(0, π/2)`, assuming the `cos²`-weighted integrand is integrable -/

/-- **The sharp `cos²`-weighted Hardy inequality on the open interval `(0, π/2)`, with the
`C¹`-on-the-open-interval hypothesis and assuming that the left-hand integrand is integrable.**
The two halves `(0, π/4)` and `(π/4, π/2)` are `leftHalfSharp` and its reflection. -/
private theorem cosSqHardyMain {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hC : IntegrableOn (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 2)))
    (hA : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  have hsubL : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hsubR : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  -- the left half
  have hleft := Work.FTS.EllipticEst.H2W.AeWAux.leftHalfSharp hη0 hη1 (f := f) (hf.mono hsubL)
    (hC.mono_set hsubL) (hA.mono_set hsubL) (hB.mono_set hsubL)
  -- the right half, by reflection
  have hg_cd : ContDiffOn ℝ 1 (fun x : ℝ => f (Real.pi / 2 - x)) (Set.Ioo 0 (Real.pi / 4)) := by
    have hmap : Set.MapsTo (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 4))
        (Set.Ioo 0 (Real.pi / 2)) := by
      intro x hx
      exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
    have hlin : ContDiffOn ℝ 1 (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 4)) := by
      fun_prop
    simpa only [Function.comp_def] using hf.comp hlin hmap
  have hgrC : IntegrableOn (fun x => f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * x) ^ 2
      * (Real.sin (2 * x)) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 4)) := by
    have h1 := integrableOn_Ioo_reflect_right (hC.mono_set hsubR)
    refine h1.congr_fun (fun x _ => ?_) measurableSet_Ioo
    show f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * (Real.pi / 2 - x)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-(2 + η))
      = f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
    rw [cos_two_pi_half_sub, sin_two_pi_half_sub]
    ring
  have hgrB : IntegrableOn (fun x => f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * x)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 4)) := by
    have h1 := integrableOn_Ioo_reflect_right (hB.mono_set hsubR)
    refine h1.congr_fun (fun x _ => ?_) measurableSet_Ioo
    show f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-η)
      = f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * x)) ^ (-η)
    rw [sin_two_pi_half_sub]
  have hgrA : IntegrableOn (fun x => deriv (fun x : ℝ => f (Real.pi / 2 - x)) x ^ 2
      * (Real.sin (2 * x)) ^ (-η)) (Set.Ioo 0 (Real.pi / 4)) := by
    have h1 := integrableOn_Ioo_reflect_right (hA.mono_set hsubR)
    refine h1.congr_fun (fun x _ => ?_) measurableSet_Ioo
    show deriv f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-η)
      = deriv (fun x : ℝ => f (Real.pi / 2 - x)) x ^ 2 * (Real.sin (2 * x)) ^ (-η)
    rw [deriv_comp_const_sub f (Real.pi / 2) x, sin_two_pi_half_sub]
    ring
  have hright := Work.FTS.EllipticEst.H2W.AeWAux.leftHalfSharp hη0 hη1
    (f := fun x : ℝ => f (Real.pi / 2 - x)) hg_cd hgrC hgrA hgrB
  -- rewrite the reflected integrals as integrals over the right half
  have hconvC : (∫ x in Set.Ioo 0 (Real.pi / 4), f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * x) ^ 2
        * (Real.sin (2 * x)) ^ (-(2 + η)))
      = ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
    refine Eq.trans ?_ (integral_Ioo_reflect_right
      (fun θ : ℝ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))).symm
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
    show f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
      = f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * (Real.pi / 2 - x)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-(2 + η))
    rw [cos_two_pi_half_sub, sin_two_pi_half_sub]
    ring
  have hconvB : (∫ x in Set.Ioo 0 (Real.pi / 4),
        f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * x)) ^ (-η))
      = ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
    refine Eq.trans ?_ (integral_Ioo_reflect_right
      (fun θ : ℝ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))).symm
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
    show f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * x)) ^ (-η)
      = f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-η)
    rw [sin_two_pi_half_sub]
  have hconvA : (∫ x in Set.Ioo 0 (Real.pi / 4),
        deriv (fun x : ℝ => f (Real.pi / 2 - x)) x ^ 2 * (Real.sin (2 * x)) ^ (-η))
      = ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
    refine Eq.trans ?_ (integral_Ioo_reflect_right
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))).symm
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
    show deriv (fun x : ℝ => f (Real.pi / 2 - x)) x ^ 2 * (Real.sin (2 * x)) ^ (-η)
      = deriv f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-η)
    rw [deriv_comp_const_sub f (Real.pi / 2) x, sin_two_pi_half_sub]
    ring
  rw [hconvC, hconvA, hconvB] at hright
  -- split all three integrals at `π/4`
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h1L : IntervalIntegrable (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η))) volume 0 (Real.pi / 4) :=
    (intervalIntegrable_iff_integrableOn_Ioo (by positivity : (0 : ℝ) ≤ Real.pi / 4)).mpr
      (hC.mono_set hsubL)
  have h1R : IntervalIntegrable (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η))) volume (Real.pi / 4) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo h4le).mpr (hC.mono_set hsubR)
  have h2L : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume 0 (Real.pi / 4) :=
    (intervalIntegrable_iff_integrableOn_Ioo (by positivity : (0 : ℝ) ≤ Real.pi / 4)).mpr
      (hA.mono_set hsubL)
  have h2R : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume (Real.pi / 4) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo h4le).mpr (hA.mono_set hsubR)
  have h3L : IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume 0 (Real.pi / 4) :=
    (intervalIntegrable_iff_integrableOn_Ioo (by positivity : (0 : ℝ) ≤ Real.pi / 4)).mpr
      (hB.mono_set hsubL)
  have h3R : IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume (Real.pi / 4) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo h4le).mpr (hB.mono_set hsubR)
  rw [integral_Ioo_split h1L h1R, integral_Ioo_split h2L h2R, integral_Ioo_split h3L h3R]
  refine le_of_le_of_eq (add_le_add hleft hright) ?_
  ring

/-! ## The target -/

theorem HonHardyCosWeight (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)) → Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) → Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) → MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) → MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) → (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) ≤ 1 / (1 + η) ^ 2 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) + C * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  refine ⟨2, by norm_num, fun f hf _h0 _h1 hBint hAint => ?_⟩
  by_cases hC : IntegrableOn (fun θ => (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η))) (Set.Ioo (0 : ℝ) (Real.pi / 2))
  · exact cosSqHardyMain hη0 hη1 (hf.of_le (by norm_num)) hC hAint hBint
  · -- the left-hand integrand is not integrable: Mathlib's integral is `0`
    have hzero : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) = 0 :=
      MeasureTheory.integral_undef hC
    rw [hzero]
    have hA0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _))
    have hB0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _))
    have hcoef : 0 < 1 / (1 + η) ^ 2 := by positivity
    nlinarith [hA0, hB0, hcoef]

end Work.FTS.EllipticEst.Honest.Step1G
