import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.LocPotential
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory in
theorem slotKIntegral {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hInt : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wLoc ℓ g 0 p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    (∫ a in Submission.BoseGases.acube ℓ,
        ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 a y)
      = ∫ p in (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ),
          Submission.BoseGases.wLoc ℓ g 0 p.1 p.2 := by
  -- The anchored window `χ` is supported in `ball 0 (ℓ/2) ⊆ acube ℓ`, so the `y`-integrand
  -- `y ↦ wLoc ℓ g 0 a y` vanishes off the cube `acube ℓ`; replacing the full-space integral
  -- in the second variable by the integral over the cube is thus an identity, with no
  -- integrability input.
  have hfib : ∀ a : EuclideanSpace ℝ (Fin 3),
      (∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 a y)
        = ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wLoc ℓ g 0 a y := by
    intro a
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    have hchi : Submission.BoseGases.chiU ℓ 0 y = 0 := by
      rw [show Submission.BoseGases.chiU ℓ 0 y = Submission.BoseGases.chiScale ℓ y from by
        simp [Submission.BoseGases.chiU, Submission.BoseGases.chiScale]]
      by_contra h
      exact hy (Submission.BoseGases.mem_acube_of_norm_le (le_of_lt hℓ)
        (Submission.BoseGases.chiScale_support_le hℓ h))
    simp [Submission.BoseGases.wLoc, hchi]
  rw [show (fun a : EuclideanSpace ℝ (Fin 3) =>
        ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 a y)
      = fun a : EuclideanSpace ℝ (Fin 3) =>
        ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wLoc ℓ g 0 a y
      from funext hfib]
  -- Fubini on the product of the two cube-restricted Lebesgue measures, using the integrability
  -- of the kernel on the product cube.
  have hmeasure : (volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)
      = ((volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)).prod
        ((volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3))]
    exact (MeasureTheory.Measure.prod_restrict
      (μ := (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      (ν := (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      (Submission.BoseGases.acube ℓ) (Submission.BoseGases.acube ℓ)).symm
  have hInt' : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wLoc ℓ g 0 p.1 p.2)
      (((volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))) := by
    rw [← hmeasure]
    exact hInt
  have hF := MeasureTheory.integral_prod
    (μ := (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ))
    (ν := (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ))
    (f := fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wLoc ℓ g 0 p.1 p.2) hInt'
  rw [← hF, ← hmeasure]

end Work.BoseFixB1B
