import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.aliasImageDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imageHeat_prod_integrable`

The joint (product) integrability of the `m`-th summand of the heat image of the aliasing
identity: for `ℓ`, `g`, `m` such that the autocorrelation kernel vanishes at the touching point
`z = ℓ • latVec m` (`hvanish`) and such that the Riesz weight `‖u − z‖⁻⁴` times the kernel is
spatially integrable (`hint`), the function

    `(t, u) ↦ t^{-3/2} · (aliasKernel g u · heatK t (z − u))`

is integrable for the product measure `(volume ↾ (0,∞)) ⊗ volume`.

**Proof.**  Write `A = aliasKernel g` and `C = 2/π^{3/2}`.  The *pointwise* identity

    `A u = (A u · C · (‖u − z‖⁴)⁻¹) · ‖u − z‖⁴ / C`

(`hvanish` is exactly what is needed at the single point `u = z`, where both sides are `0`)
shows that `A` is a.e. strongly measurable, since the right-hand side is a measurable function
times the integrable majorant of `hint`.  This gives the a.e. strong measurability of the joint
integrand.  Its *finite integral* is then computed by the iterated (Tonelli) criterion
`integrable_prod_iff'`: for each `u`,
`∫_{t>0} ‖t^{-3/2}(A u · heatK t (z−u))‖ dt = |A u| · 2/(π^{3/2}‖z−u‖⁴)`, which is precisely
`‖A u · C · (‖u − z‖⁴)⁻¹‖`, an integrable function of `u` by `hint`.  (At `u = z` the inner
`t`-integral diverges but is multiplied by `A z = 0`, so the single-point exception is harmless —
this is the role of `hvanish`.)
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem imageHeat_prod_integrable {ℓ : ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℂ} {m : Fin 3 → ℤ}
    (hvanish : Work.BoseBoxFock.aliasKernel g (ℓ • Work.BoseBoxFock.latVec m) = 0)
    (hint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseBoxFock.aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹)) :
    MeasureTheory.Integrable
      (Function.uncurry (fun (t : ℝ) (u : EuclideanSpace ℝ (Fin 3)) =>
        t ^ (-(3 / 2 : ℝ)) * (Work.BoseBoxFock.aliasKernel g u * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - u))))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod MeasureTheory.volume) := by
  set z : E3 := ℓ • latVec m with hz
  have hCne : (2 / Real.pi ^ (3 / 2 : ℝ)) ≠ 0 := by positivity
  -- (1) the pointwise identity relating the kernel to the (integrable) majorant of `hint`
  have hkey : ∀ u : E3, aliasKernel g u =
      (aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - z‖ ^ 4)⁻¹)
        * ‖u - z‖ ^ 4 / (2 / Real.pi ^ (3 / 2 : ℝ)) := by
    intro u
    by_cases h : ‖u - z‖ ^ 4 = 0
    · have huz : u = z := by
        have hn : ‖u - z‖ = 0 := (pow_eq_zero_iff (n := 4) (by norm_num)).mp h
        exact sub_eq_zero.mp (norm_eq_zero.mp hn)
      rw [huz, hvanish]
      simp
    · rw [mul_assoc, mul_assoc, inv_mul_cancel₀ h, mul_one, mul_div_assoc, div_self hCne, mul_one]
  -- (2) `aliasKernel g` is a.e. strongly measurable: it *equals* a measurable function
  have hA : AEStronglyMeasurable (fun u : E3 => aliasKernel g u) volume := by
    refine (hint.aestronglyMeasurable.mul (g := fun u : E3 =>
      ‖u - z‖ ^ 4 / (2 / Real.pi ^ (3 / 2 : ℝ))) ?_).congr ?_
    · fun_prop
    · filter_upwards with u
      simp only [Pi.mul_apply]
      rw [← mul_div_assoc]
      exact (hkey u).symm
  -- (3) a.e. strong measurability of the joint integrand
  have hF : AEStronglyMeasurable
      (Function.uncurry (fun (t : ℝ) (u : E3) =>
        t ^ (-(3 / 2 : ℝ)) * (aliasKernel g u * heatK t (z - u))))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × E3 => p.1 ^ (-(3 / 2 : ℝ)))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
      (((by fun_prop : Measurable (fun t : ℝ => t ^ (-(3 / 2 : ℝ)))).stronglyMeasurable
        ).aestronglyMeasurable).comp_fst
    have h2 : AEStronglyMeasurable (fun p : ℝ × E3 => aliasKernel g p.2)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := hA.comp_snd
    have h3 : AEStronglyMeasurable (fun p : ℝ × E3 => heatK p.1 (z - p.2))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
      unfold heatK
      fun_prop
    exact h1.mul (h2.mul h3)
  -- (4) the pointwise value of the inner `t`-integral of the absolute value
  have hpt : ∀ u : E3,
      (∫ t in Set.Ioi (0 : ℝ), ‖t ^ (-(3 / 2 : ℝ)) * (aliasKernel g u * heatK t (z - u))‖)
        = ‖aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - z‖ ^ 4)⁻¹‖ := by
    intro u
    by_cases huz : u = z
    · have hzero : (fun t : ℝ =>
          ‖t ^ (-(3 / 2 : ℝ)) * (aliasKernel g u * heatK t (z - u))‖) = fun _ => 0 := by
        funext t
        rw [huz, sub_self, hvanish]
        simp
      rw [hzero]
      simp [huz, hvanish]
    · have hzu : z - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huz)
      have hmul : ∀ t ∈ Set.Ioi (0 : ℝ),
          ‖t ^ (-(3 / 2 : ℝ)) * (aliasKernel g u * heatK t (z - u))‖
            = |aliasKernel g u| * (t ^ (-(3 / 2 : ℝ)) * heatK t (z - u)) := by
        intro t ht
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _),
          abs_of_nonneg (heatK_nonneg ht.le _)]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioi hmul, integral_const_mul]
      rw [show (-(3 / 2 : ℝ)) = -(3 : ℝ) / 2 by norm_num]
      rw [SqrtKin.heatK_rpow_integral hzu]
      have hnorm : ‖aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - z‖ ^ 4)⁻¹‖
          = |aliasKernel g u| * ((2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - z‖ ^ 4)⁻¹) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi ^ (3 / 2 : ℝ)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖u - z‖ ^ 4)⁻¹)]
        ring
      rw [hnorm, norm_sub_rev u z]
      have hpi : Real.pi ^ (3 / 2 : ℝ) ≠ 0 := by positivity
      have hn : ‖u - z‖ ^ 4 ≠ 0 := by
        have hpos : 0 < ‖u - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huz)
        positivity
      field_simp
  rw [integrable_prod_iff' hF]
  refine ⟨?_, ?_⟩
  · -- a.e. slice integrability
    filter_upwards with u
    simp only [Function.uncurry_apply_pair]
    by_cases huz : u = z
    · have hzero : (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * (aliasKernel g u * heatK t (z - u)))
          = fun _ => 0 := by
        funext t
        rw [huz, sub_self, hvanish]
        ring
      rw [hzero]
      exact integrable_zero _ _ _
    · have hzu : z - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huz)
      refine ((SqrtKin.heatK_rpow_integrableOn hzu).const_mul (aliasKernel g u)).congr ?_
      filter_upwards with t
      ring_nf
  · -- integrability of the norm of the slice integral
    refine hint.norm.congr ?_
    filter_upwards with u
    simp only [Function.uncurry_apply_pair]
    exact (hpt u).symm

end Work.BoseBoxFock
