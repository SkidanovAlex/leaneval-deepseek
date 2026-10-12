import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

/-- **Line-integral swap (Fubini / coarea) for `ℝ³`.**

For an integrable `g` on `ℝ³` and a fixed direction `y`, the function
`v ↦ ∫ s in (-1/2)..(1/2), g (v + s • y)` (the average of `g` over the short segment of
length `‖y‖` through `v` in direction `y`) is again integrable, and its integral is `∫ g`.

Mathematically: with the parameter measure `ν := volume.restrict (Ioc (-1/2) (1/2))` (total
mass `1`), the shear map `Φ p = p.1 + p.2 • y` from `ℝ³ × ℝ` to `ℝ³` pushes `volume.prod ν`
forward to Lebesgue measure: for a measurable `A`,
`(volume.prod ν) (Φ ⁻¹' A) = ∫⁻ s ∫⁻ v 1_A (v + s • y) = ∫⁻ s volume A = volume A`,
using translation invariance of Lebesgue measure in `v` (`lintegral_add_right_eq_self`) and
`volume (Ioc (-1/2) (1/2)) = 1`.  The claim then follows from Fubini
(`MeasurePreserving.integrable_comp`, `integrable_prod_left`, `integral_prod`,
`integral_map`). -/
theorem integral_integral_line_swap {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : MeasureTheory.Integrable g MeasureTheory.volume) (y : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
        (fun v : EuclideanSpace ℝ (Fin 3) => ∫ s in (-(1 / 2))..(1 / 2), g (v + s • y))
        MeasureTheory.volume
      ∧ ∫ v, (∫ s in (-(1 / 2))..(1 / 2), g (v + s • y)) = ∫ v, g v := by
  have hab : (-(1/2) : ℝ) ≤ 1/2 := by norm_num
  -- the parameter measure on `[-1/2, 1/2]`, of total mass `1`
  set ν : Measure ℝ := volume.restrict (Set.Ioc (-(1/2) : ℝ) (1/2)) with hνdef
  -- the shear map `(v, s) ↦ v + s • y`
  set Φ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3) :=
    (fun p => p.1 + p.2 • y) with hΦdef
  have hΦ_meas : Measurable Φ := by
    rw [hΦdef]; fun_prop
  have hν_univ : ν Set.univ = 1 := by
    rw [hνdef, Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num
  -- `Φ` pushes `volume.prod ν` forward onto Lebesgue measure
  have hmap : Measure.map Φ (volume.prod ν) = volume := by
    refine Measure.ext (fun A hA => ?_)
    rw [Measure.map_apply hΦ_meas hA]
    have hf_aem : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × ℝ =>
        A.indicator (1 : EuclideanSpace ℝ (Fin 3) → ENNReal) (Φ p)) (volume.prod ν) := by
      have hm : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × ℝ =>
          A.indicator (1 : EuclideanSpace ℝ (Fin 3) → ENNReal) (Φ p)) := by
        exact (measurable_const.indicator hA).comp hΦ_meas
      exact hm.aemeasurable
    have key : (volume.prod ν) (Φ ⁻¹' A)
        = ∫⁻ p, A.indicator (1 : EuclideanSpace ℝ (Fin 3) → ENNReal) (Φ p)
            ∂(volume.prod ν) := by
      rw [← lintegral_indicator_one (hA.preimage hΦ_meas)]
      refine lintegral_congr (fun p => ?_)
      by_cases hp : Φ p ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hp]
    rw [key, lintegral_prod_symm _ hf_aem]
    simp only [hΦdef]
    have hinner : ∀ s : ℝ,
        ∫⁻ v, A.indicator (1 : EuclideanSpace ℝ (Fin 3) → ENNReal) (v + s • y)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))) = volume A := by
      intro s
      rw [lintegral_add_right_eq_self (A.indicator (1 : EuclideanSpace ℝ (Fin 3) → ENNReal))
        (s • y), lintegral_indicator_one hA]
    rw [lintegral_congr hinner, lintegral_const, hν_univ, mul_one]
  have hmp : MeasurePreserving Φ (volume.prod ν) volume := ⟨hΦ_meas, hmap⟩
  have hF_int : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => g (Φ p))
      (volume.prod ν) :=
    (hmp.integrable_comp (g := g) hg.aestronglyMeasurable).mpr hg
  have hInt : Integrable (fun v : EuclideanSpace ℝ (Fin 3) => ∫ s, g (Φ (v, s)) ∂ν)
      volume :=
    hF_int.integral_prod_left
  have hfun : (fun v : EuclideanSpace ℝ (Fin 3) =>
        ∫ s in (-(1/2))..(1/2), g (v + s • y))
      = (fun v => ∫ s, g (Φ (v, s)) ∂ν) := by
    funext v
    rw [intervalIntegral.integral_of_le hab, hνdef]
  have hval : (∫ v, (∫ s, g (Φ (v, s)) ∂ν) ∂volume) = ∫ v, g v := by
    rw [← MeasureTheory.integral_prod
        (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => g (Φ p)) hF_int]
    rw [← MeasureTheory.integral_map (φ := Φ) (μ := volume.prod ν) hΦ_meas.aemeasurable
      (f := g) (by rw [hmap]; exact hg.aestronglyMeasurable), hmap]
  constructor
  · rw [hfun]; exact hInt
  · rw [hfun]; exact hval

end Work.BoseB1Cube
