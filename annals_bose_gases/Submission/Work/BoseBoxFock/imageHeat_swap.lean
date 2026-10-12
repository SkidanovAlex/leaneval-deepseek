import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imageHeat_prod_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imageHeat_swap`

The `t`-`u` Fubini swap of the image term of the aliasing identity, together with the
radial heat-kernel integral `∫_{t>0} t^{-3/2} heatK t z dt = 2/(π^{3/2}‖z‖⁴)`:

    ∫_{t>0} t^{-3/2} ∫_u 𝒢(u) heatK t (ℓ • latVec m − u) du
      = ∫_u 𝒢(u) (2/π^{3/2}) (‖u − ℓ • latVec m‖⁴)⁻¹ du ,

where `𝒢 = aliasKernel g = Re(autocorr g)`.

The joint integrability of the uncurried integrand on `(0,∞) × ℝ³` (which is what makes the
Fubini theorem applicable) is `imageHeat_prod_integrable`; the diagonal point
`u = ℓ • latVec m` is killed by `hvanish`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem imageHeat_swap {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ} {m : Fin 3 → ℤ} (hm : m ≠ 0) (hvanish : Work.BoseBoxFock.aliasKernel g (ℓ • Work.BoseBoxFock.latVec m) = 0) (hint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseBoxFock.aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹)) : (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.aliasKernel g u * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - u))) = ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹ := by
  have _ : (0 : ℝ) < ℓ := hℓ
  have _ : m ≠ 0 := hm
  -- The joint integrability of the uncurried integrand, from the per-`u` radial integral
  -- (`Work.BoseBoxFock.imageHeat_prod_integrable`).
  have hInt : Integrable (Function.uncurry (fun (t : ℝ) (u : E3) =>
      t ^ (-(3 / 2 : ℝ)) * (aliasKernel g u * heatK t (ℓ • latVec m - u))))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    imageHeat_prod_integrable hvanish hint
  -- The per-`u` value of the inner `t`-integral.
  have hinner : ∀ u : E3, (∫ t in Set.Ioi (0:ℝ), t ^ (-(3/2:ℝ)) * (aliasKernel g u * heatK t (ℓ • latVec m - u)))
      = aliasKernel g u * (2 / Real.pi ^ (3/2:ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by
    intro u
    rcases eq_or_ne u (ℓ • latVec m) with huz | huz
    · subst huz
      rw [hvanish]
      simp
    · have hzu : u - ℓ • latVec m ≠ 0 := sub_ne_zero.mpr huz
      have hze : ∀ t : ℝ, heatK t (ℓ • latVec m - u) = heatK t (u - ℓ • latVec m) := by
        intro t
        rw [← neg_sub u (ℓ • latVec m), heatK_even]
      have hfun : (fun t : ℝ => t ^ (-(3/2:ℝ)) * (aliasKernel g u * heatK t (ℓ • latVec m - u)))
          = fun t : ℝ => aliasKernel g u * (t ^ (-(3/2:ℝ)) * heatK t (u - ℓ • latVec m)) := by
        funext t
        rw [hze t]
        ring
      rw [hfun, integral_const_mul,
        show (∫ t in Set.Ioi (0:ℝ), t ^ (-(3/2:ℝ)) * heatK t (u - ℓ • latVec m))
          = 2 / (Real.pi ^ (3/2:ℝ) * ‖u - ℓ • latVec m‖ ^ 4) from by
          rw [show (-(3/2:ℝ)) = -(3:ℝ)/2 by norm_num]
          exact SqrtKin.heatK_rpow_integral hzu,
        div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
  calc (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u)))
      = ∫ t in Set.Ioi (0 : ℝ), ∫ u : E3, t ^ (-(3/2:ℝ)) * (aliasKernel g u * heatK t (ℓ • latVec m - u)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact (integral_const_mul (t ^ (-(3/2:ℝ)))
          (fun u : E3 => aliasKernel g u * heatK t (ℓ • latVec m - u))).symm
    _ = ∫ u : E3, ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3/2:ℝ)) * (aliasKernel g u * heatK t (ℓ • latVec m - u)) :=
        integral_integral_swap hInt
    _ = ∫ u : E3, aliasKernel g u * (2 / Real.pi ^ (3/2:ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹ :=
        integral_congr_ae (Filter.Eventually.of_forall hinner)

end Work.BoseBoxFock
