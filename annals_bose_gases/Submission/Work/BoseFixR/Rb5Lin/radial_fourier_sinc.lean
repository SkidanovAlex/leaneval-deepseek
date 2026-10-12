import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixR.Rb5Lin.SplitDefs
import Submission.Work.BoseFixR.Rb5Lin.chat_eq_cos
import Submission.Work.BoseFixR.Rb5Lin.cos_interval_sincR
import Submission.Work.BoseFixR.Rb5Lin.integrableOn_triangular_region
import Submission.Work.BoseFixR.Rb5Lin.integral_Ioi_sqrt_subst
import Submission.Work.BoseFixR.Rb5Lin.radial2D_integral
import Submission.Work.BoseFixR.Rb5Lin.radial_cos_axis
import Submission.Work.BoseFixR.Rb5Lin.triangular_swap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The radial Fourier transform is the one-dimensional `sincR` integral

For a radial function `W x = ψ ‖x‖` on `ℝ³` and any wave vector `q`,

`Ŵ(q) = 4π ∫₀^∞ r² ψ r sincR(‖q‖ r) dr`,

i.e. the three-dimensional Fourier transform of a radial integrable function is the
one-dimensional integral of `r²ψ(r)` against the spherical average `sincR(‖q‖r)` of the
plane wave `e^{-i⟪q,·⟫}`.

The proof is the coordinate computation, organised as:
`chat W q = ∫ W cos⟪q,·⟫` (`chat_eq_cos`) → rotate `q` onto the third axis
(`radial_cos_axis`) → split `ℝ³ = ℝ² × ℝ` (`SplitDefs`) → polar coordinates in the plane
(`radial2D_integral`) → substitute `r = √(u²+s²)` (`integral_Ioi_sqrt_subst`) → Fubini on the
cone `{|s| < r}` (`triangular_swap`, with integrability from `integrableOn_triangular_region`)
→ the elementary interval integral of the cosine (`cos_interval_sincR`).
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseFixR.Rb5Lin

theorem radial_fourier_sinc {W : EuclideanSpace ℝ (Fin 3) → ℝ} {ψ : ℝ → ℝ}
    (hW : MeasureTheory.Integrable W) (hψ : ∀ x, W x = ψ ‖x‖)
    (q : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat W q = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r) := by
  -- ## Step 0: the integrand `G z = ψ ‖z‖ cos (‖q‖ * z 2)` and its integrability
  have hψW : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) volume := by
    rw [show (fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖) = W from funext fun x => (hψ x).symm]
    exact hW
  have hcos_cont : Continuous fun z : EuclideanSpace ℝ (Fin 3) => Real.cos (‖q‖ * z 2) := by
    fun_prop
  have hGsm : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) => ψ ‖z‖ * Real.cos (‖q‖ * z 2)) volume := by
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) => ψ ‖z‖ * Real.cos (‖q‖ * z 2))
        = (fun z : EuclideanSpace ℝ (Fin 3) => W z * Real.cos (‖q‖ * z 2)) from
      funext fun z => by rw [hψ z]]
    exact hW.aestronglyMeasurable.mul hcos_cont.aestronglyMeasurable
  have hGint : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => ψ ‖z‖ * Real.cos (‖q‖ * z 2)) volume := by
    refine hW.norm.mono' hGsm ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← hψ z, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  -- ## Step 1: `chat W q = ∫ W cos⟪q,·⟫`, and `W x = ψ ‖x‖`
  rw [chat_eq_cos hW q]
  simp only [hψ]
  conv_lhs => rw [radial_cos_axis q]
  -- ## the region integrability input
  have hIntOn : IntegrableOn (fun r : ℝ => r ^ 2 * ψ r) (Set.Ioi (0 : ℝ)) volume := by
    have := (integrable_fun_norm_addHaar (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (f := ψ)).mp hψW
    simpa using this
  have hreg := integrableOn_triangular_region (ψ := ψ) (c := ‖q‖) hIntOn
  -- ## Step 2: the chain of identities
  trans ∫ p : EuclideanSpace ℝ (Fin 2) × ℝ, ψ ‖splitVec p‖ * Real.cos (‖q‖ * (splitVec p) 2)
  · exact integral_splitVec _ hGsm
  trans ∫ s : ℝ, ∫ y : EuclideanSpace ℝ (Fin 2),
      ψ ‖splitVec (y, s)‖ * Real.cos (‖q‖ * (splitVec (y, s)) 2)
  · exact integral_prod_symm _ (integrable_splitVec hGint)
  trans ∫ s : ℝ, ∫ y : EuclideanSpace ℝ (Fin 2),
      ψ (Real.sqrt (‖y‖ ^ 2 + s ^ 2)) * Real.cos (‖q‖ * s)
  · refine integral_congr_ae ?_
    filter_upwards with s
    refine integral_congr_ae ?_
    filter_upwards with y
    have hnorm : ‖splitVec (y, s)‖ = Real.sqrt (‖y‖ ^ 2 + s ^ 2) := by
      rw [← norm_splitVec_sq y s, Real.sqrt_sq (norm_nonneg _)]
    rw [splitVec_apply_two, hnorm]
  trans ∫ s : ℝ, (2 * Real.pi * ∫ u in Set.Ioi (0 : ℝ), u * ψ (Real.sqrt (u ^ 2 + s ^ 2)))
      * Real.cos (‖q‖ * s)
  · refine integral_congr_ae ?_
    filter_upwards with s
    rw [integral_mul_const, radial2D_integral (fun u : ℝ => ψ (Real.sqrt (u ^ 2 + s ^ 2)))]
  trans 2 * Real.pi * ∫ s : ℝ, ∫ u in Set.Ioi (0 : ℝ),
      u * ψ (Real.sqrt (u ^ 2 + s ^ 2)) * Real.cos (‖q‖ * s)
  · rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with s
    rw [integral_mul_const]
    ring
  trans 2 * Real.pi * ∫ s : ℝ, ∫ r in Set.Ioi |s|, r * ψ r * Real.cos (‖q‖ * s)
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards with s
    rw [integral_mul_const, integral_Ioi_sqrt_subst ψ s, integral_mul_const]
  trans 2 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), ∫ s in Set.Ioo (-r) r,
      r * ψ r * Real.cos (‖q‖ * s)
  · congr 1
    exact triangular_swap (F := fun s r => r * ψ r * Real.cos (‖q‖ * s)) hreg
  trans 2 * Real.pi * ∫ r in Set.Ioi (0 : ℝ),
      r * ψ r * (∫ s in Set.Ioo (-r) r, Real.cos (‖q‖ * s))
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards with r
    rw [integral_const_mul]
  trans 2 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r * ψ r * (2 * r * Work.BoseFixR.sincR (‖q‖ * r))
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr' : 0 < r := Set.mem_Ioi.mp hr
    have hIoo : (∫ s in Set.Ioo (-r) r, Real.cos (‖q‖ * s))
        = ∫ s in (-r)..r, Real.cos (‖q‖ * s) := by
      rw [intervalIntegral.integral_of_le (by linarith : -(r) ≤ r)]
      exact setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := -r) (b := r))
    rw [hIoo, cos_interval_sincR]
  · rw [show (∫ r in Set.Ioi (0 : ℝ), r * ψ r * (2 * r * Work.BoseFixR.sincR (‖q‖ * r)))
        = ∫ r in Set.Ioi (0 : ℝ), 2 * (r ^ 2 * ψ r * Work.BoseFixR.sincR (‖q‖ * r)) from by
      refine integral_congr_ae ?_
      filter_upwards with r
      ring]
    rw [integral_const_mul]
    ring

end Work.BoseFixR.Rb5Lin
