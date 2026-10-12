import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Kernel.lintegralPolarR3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0.PolarSphere

open MeasureTheory
open scoped ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Polar coordinates in `ℝ³`, Bochner form.**  For an integrable `f`, the
3-dimensional Lebesgue integral equals the iterated integral over the unit
sphere (with the surface measure `volume.toSphere`) and the radius, with the
weight `r ^ 2`. -/
theorem integral_eq_sphere_radius {f : ℝ³ → ℝ} (hf : Integrable f) :
    (∫ x, f x) = ∫ r in Set.Ioi (0 : ℝ),
      (∫ ω : Metric.sphere (0 : ℝ³) 1, f (r • (ω : ℝ³)) ∂(MeasureTheory.volume.toSphere)) * r ^ 2 := by
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure ℝ³)
  -- Remove the origin: it is a null set.
  have h1 : ∫ x, f x = ∫ x : ({0}ᶜ : Set ℝ³), f ↑x ∂(volume.comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton (0:ℝ³)).compl f, restrict_compl_singleton]
  -- Transport along the polar-coordinates homeomorphism (Mathlib's
  -- `measurePreserving_homeomorphUnitSphereProd`); the product measure carries the
  -- weight `volumeIoiPow 2` because `dim ℝ³ = 3`.
  have h2 : ∫ x : ({0}ᶜ : Set ℝ³), f ↑x ∂(volume.comap Subtype.val)
      = ∫ z : Metric.sphere (0:ℝ³) 1 × Set.Ioi (0:ℝ), f ((z.2:ℝ) • (z.1:ℝ³))
        ∂((volume : Measure ℝ³).toSphere.prod (Measure.volumeIoiPow 2)) := by
    have h2' : ∫ x : ({0}ᶜ : Set ℝ³), f ↑x ∂(volume.comap Subtype.val)
        = ∫ z : Metric.sphere (0:ℝ³) 1 × Set.Ioi (0:ℝ), f ((z.2:ℝ) • (z.1:ℝ³))
          ∂((volume : Measure ℝ³).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1))) := by
      rw [← hmp.integral_comp (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd ℝ³))
        (fun z : Metric.sphere (0:ℝ³) 1 × Set.Ioi (0:ℝ) => f ((z.2:ℝ) • (z.1:ℝ³)))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe,
        smul_inv_smul₀ (norm_ne_zero_iff.mpr x.2)]
    simpa using h2'
  -- Integrability of the transported integrand on the product space.
  have hgint : Integrable
      (fun z : Metric.sphere (0:ℝ³) 1 × Set.Ioi (0:ℝ) => f ((z.2:ℝ) • (z.1:ℝ³)))
      ((volume : Measure ℝ³).toSphere.prod (Measure.volumeIoiPow 2)) := by
    have hcomp : Integrable (fun x : ({0}ᶜ : Set ℝ³) => f ↑x)
        ((volume : Measure ℝ³).comap Subtype.val) := by
      have h : IntegrableOn f ({0}ᶜ : Set ℝ³) (volume : Measure ℝ³) := hf.integrableOn
      rw [integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0:ℝ³)).compl] at h
      exact h
    have h' : Integrable
        (fun z : Metric.sphere (0:ℝ³) 1 × Set.Ioi (0:ℝ) => f ((z.2:ℝ) • (z.1:ℝ³)))
        ((volume : Measure ℝ³).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1))) := by
      refine (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd ℝ³))
        (g := fun z : Metric.sphere (0:ℝ³) 1 × Set.Ioi (0:ℝ) => f ((z.2:ℝ) • (z.1:ℝ³)))).mp ?_
      refine hcomp.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Function.comp_apply]
      beta_reduce
      rw [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe,
        smul_inv_smul₀ (norm_ne_zero_iff.mpr x.2)]
    simpa using h'
  -- Fubini: integrate first over the sphere, then over the radius.
  have h3 : ∫ z : Metric.sphere (0:ℝ³) 1 × Set.Ioi (0:ℝ), f ((z.2:ℝ) • (z.1:ℝ³))
        ∂((volume : Measure ℝ³).toSphere.prod (Measure.volumeIoiPow 2))
      = ∫ r : Set.Ioi (0:ℝ),
          (∫ ω : Metric.sphere (0:ℝ³) 1,
            f ((r:ℝ) • (ω:ℝ³)) ∂(MeasureTheory.volume.toSphere)) ∂(Measure.volumeIoiPow 2) := by
    simpa using integral_prod_symm
      (fun z : Metric.sphere (0:ℝ³) 1 × Set.Ioi (0:ℝ) => f ((z.2:ℝ) • (z.1:ℝ³))) hgint
  rw [h1, h2, h3]
  -- Unfold the radial measure `volumeIoiPow 2` as a density `r ↦ r ^ 2`.
  simp only [Measure.volumeIoiPow]
  rw [integral_withDensity_eq_integral_toReal_smul
      (f := fun r : Set.Ioi (0:ℝ) => ENNReal.ofReal (r.1 ^ 2))
      (by fun_prop) (by filter_upwards with r; exact ENNReal.ofReal_lt_top)]
  rw [← integral_subtype_comap measurableSet_Ioi
      (fun y : ℝ => (∫ ω : Metric.sphere (0:ℝ³) 1,
        f (y • (ω:ℝ³)) ∂MeasureTheory.volume.toSphere) * y^2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp [ENNReal.toReal_ofReal (sq_nonneg (r:ℝ)), smul_eq_mul, mul_comm]

end Work.SmallBoxA0.PolarSphere
