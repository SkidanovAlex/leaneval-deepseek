import Mathlib

namespace Work.Mostow

open MeasureTheory
open scoped ENNReal

/-- Polar-coordinate formula for Lebesgue measure on `EuclideanSpace ℝ (Fin m)`, whole space:
the integral of a radial integrand `G ‖x‖` equals the surface measure of the unit sphere times
the integral over the positive ray against the radial weight `x ↦ x ^ (m - 1)`. -/
private lemma lintegral_fun_norm_volume {m : ℕ} (hm : 1 ≤ m) (G : ℝ → ENNReal)
    (hG : Measurable G) :
    ∫⁻ x, G ‖x‖ ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
      = ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere Set.univ)
        * ∫⁻ r : Set.Ioi (0 : ℝ), G r ∂(Measure.volumeIoiPow (m - 1)) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  haveI : NullSingletonClass (volume : Measure (EuclideanSpace ℝ (Fin m))) := inferInstance
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  have hcompl : MeasurableSet ({0}ᶜ : Set (EuclideanSpace ℝ (Fin m))) :=
    (measurableSet_singleton 0).compl
  -- step 1: forget the origin (a null set)
  have hA : ∫⁻ x, G ‖x‖ ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
      = ∫⁻ y : ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin m))), G ‖(y : EuclideanSpace ℝ (Fin m))‖
          ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).comap Subtype.val) := by
    rw [lintegral_subtype_comap hcompl (fun x => G ‖x‖)]
    rw [← lintegral_indicator hcompl (fun x => G ‖x‖)]
    apply lintegral_congr_ae
    filter_upwards [compl_mem_ae_iff.mpr
      (measure_singleton (0 : EuclideanSpace ℝ (Fin m)))] with x hx
    rw [Set.indicator_of_mem hx]
  rw [hA]
  -- step 2: polar coordinates
  have hmp :=
    (volume : Measure (EuclideanSpace ℝ (Fin m))).measurePreserving_homeomorphUnitSphereProd
  simp only [hfr] at hmp
  have hB := hmp.lintegral_comp_emb
    (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))))
    (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Set.Ioi (0 : ℝ) => G (p.2 : ℝ))
  simp only [homeomorphUnitSphereProd_apply_snd_coe] at hB
  rw [hB]
  -- step 3: Tonelli, the integrand does not depend on the spherical coordinate
  rw [lintegral_prod]
  · simp only
    rw [lintegral_const, mul_comm]
  · exact (hG.comp (measurable_subtype_coe.comp measurable_snd)).aemeasurable

/-- Polar-coordinate (radial) formula for Lebesgue measure on `EuclideanSpace ℝ (Fin m)`, `m ≥ 1`:
the integral of a radial integrand `G ‖w‖` over the ball of radius `ρ > 0` equals the surface
measure of the unit sphere times `∫_{0}^{ρ} x^{m-1} G x dx`.
Proof route: `Measure.measurePreserving_homeomorphUnitSphereProd` (with `E := EuclideanSpace ℝ (Fin m)`,
`μ := volume`) identifies `volume` on `{0}ᶜ` with `toSphere × volumeIoiPow (m-1)`; the ball of radius
`ρ` corresponds to the sphere times `Set.Iio ρ`, and `volumeIoiPow (m-1)` unfolds to Lebesgue measure
with density `x^(m-1)`. The same technique is carried out in `Submission/Work/Mostow/conePolarRaw.lean`. -/
theorem radialBallPolar {m : ℕ} (hm : 1 ≤ m) (ρ : ℝ) (hρ : 0 < ρ)
    (G : ℝ → ENNReal) (hG : Measurable G) :
    ∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ρ, G ‖w‖
        ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
      = ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere Set.univ)
        * ∫⁻ x in Set.Ioo (0 : ℝ) ρ, ENNReal.ofReal (x ^ (m - 1)) * G x ∂volume := by
  have hball : ∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ρ, G ‖w‖
        ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
      = ∫⁻ w, (Set.Iio ρ).indicator G ‖w‖
          ∂(volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet (fun w => G ‖w‖)]
    apply lintegral_congr
    intro w
    by_cases hw : ‖w‖ < ρ
    · have hb : w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ρ := by
        rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
      rw [Set.indicator_of_mem (s := Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ρ) (a := w) hb
            (fun w => G ‖w‖),
          Set.indicator_of_mem (s := Set.Iio ρ) (a := ‖w‖) hw G]
    · have hb : w ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ρ := by
        rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
      rw [Set.indicator_of_notMem (s := Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ρ) (a := w) hb
            (fun w => G ‖w‖),
          Set.indicator_of_notMem (s := Set.Iio ρ) (a := ‖w‖) hw G]
  have hrad : ∫⁻ r : Set.Ioi (0 : ℝ), (Set.Iio ρ).indicator G r
        ∂(Measure.volumeIoiPow (m - 1))
      = ∫⁻ x in Set.Ioo (0 : ℝ) ρ, ENNReal.ofReal (x ^ (m - 1)) * G x ∂volume := by
    have h3a : ∫⁻ r : Set.Ioi (0 : ℝ), (Set.Iio ρ).indicator G r
          ∂(Measure.volumeIoiPow (m - 1))
        = ∫⁻ x in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (x ^ (m - 1)) * (Set.Iio ρ).indicator G x ∂volume := by
      rw [Measure.volumeIoiPow]
      rw [lintegral_withDensity_eq_lintegral_mul_non_measurable]
      · simp only [Pi.mul_apply]
        exact lintegral_subtype_comap measurableSet_Ioi
          (fun x : ℝ => ENNReal.ofReal (x ^ (m - 1)) * (Set.Iio ρ).indicator G x)
      · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
      · exact Filter.Eventually.of_forall (fun r => ENNReal.ofReal_lt_top)
    have h3b : ∫⁻ x in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (x ^ (m - 1)) * (Set.Iio ρ).indicator G x ∂volume
        = ∫⁻ x in Set.Ioo (0 : ℝ) ρ, ENNReal.ofReal (x ^ (m - 1)) * G x ∂volume := by
      have hfun : (fun x => ENNReal.ofReal (x ^ (m - 1)) * (Set.Iio ρ).indicator G x)
          = Set.indicator (Set.Iio ρ) (fun x => ENNReal.ofReal (x ^ (m - 1)) * G x) := by
        funext x
        by_cases hx : x < ρ
        · simp [hx]
        · simp [hx]
      rw [hfun, setLIntegral_indicator measurableSet_Iio]
      rw [show (Set.Iio ρ ∩ Set.Ioi (0 : ℝ)) = Set.Ioo (0 : ℝ) ρ from by
        ext x; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩]
    rw [h3a, h3b]
  rw [hball, lintegral_fun_norm_volume hm (fun r => (Set.Iio ρ).indicator G r)
    (hG.indicator measurableSet_Iio), hrad]

end Work.Mostow
