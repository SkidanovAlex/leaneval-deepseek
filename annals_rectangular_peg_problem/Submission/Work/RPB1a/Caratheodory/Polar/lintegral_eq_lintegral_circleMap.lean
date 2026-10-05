import Mathlib

namespace Work.RPB1a.Caratheodory.Polar

open Complex Set Metric MeasureTheory
open scoped ENNReal Real Topology

/-- `circleMap c ρ θ` is the point `c` shifted by the inverse polar coordinate map applied to
`(ρ, θ)`, i.e. `c + ρ * (cos θ + sin θ * I)`. -/
private lemma circleMap_eq_add_polarCoord_symm (c : ℂ) (ρ θ : ℝ) :
    circleMap c ρ θ = c + Complex.polarCoord.symm (ρ, θ) := by
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_ofReal_mul_I]

/-- `Complex.polarCoord.symm` is measurable (in fact continuous). -/
private lemma measurable_polarCoord_symm :
    Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  have h : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
      = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * I) := by
    funext p; rw [Complex.polarCoord_symm_apply]
  rw [h]; fun_prop

/-- Polar coordinates for the plane integral, recentred at an arbitrary point `c`. -/
theorem lintegral_eq_lintegral_circleMap (c : ℂ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g z = ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ *
      ∫⁻ θ in Ioo (-π) π, g (circleMap c ρ θ) := by
  have hs : Measurable (fun p : ℝ × ℝ => c + Complex.polarCoord.symm p) :=
    measurable_const.add measurable_polarCoord_symm
  -- Translation invariance of Lebesgue measure lets us recentre the integral at `c`.
  have htrans : ∫⁻ z, g (c + z) = ∫⁻ z, g z :=
    (measurePreserving_add_left volume c).lintegral_comp hg
  rw [← htrans]
  -- Polar coordinates: the change of variables formula for `Complex.polarCoord.symm`.
  rw [← Complex.lintegral_comp_polarCoord_symm (fun z => g (c + z))]
  have key : (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • g (c + Complex.polarCoord.symm p))
      = ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ *
          ∫⁻ θ in Ioo (-π) π, g (circleMap c ρ θ) := by
    rw [show (∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • g (c + Complex.polarCoord.symm p))
        = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 * g (c + Complex.polarCoord.symm p) from ?_]
    · rw [Complex.polarCoord_target]
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod]
      · apply setLIntegral_congr_fun measurableSet_Ioi
        intro ρ hρ
        beta_reduce
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro θ hθ
        beta_reduce
        rw [circleMap_eq_add_polarCoord_symm]
      · exact (measurable_fst.ennreal_ofReal.mul (hg.comp hs)).aemeasurable
    · apply setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
      intro p hp
      beta_reduce
      rw [smul_eq_mul]
  exact key

end Work.RPB1a.Caratheodory.Polar
