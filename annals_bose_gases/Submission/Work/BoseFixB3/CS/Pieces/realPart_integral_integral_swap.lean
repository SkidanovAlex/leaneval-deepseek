import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

theorem realPart_integral_integral_swap {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hF : MeasureTheory.Integrable (Function.uncurry F)
      (MeasureTheory.volume.prod MeasureTheory.volume))
    (hslice : ∀ z : EuclideanSpace ℝ (Fin 3), MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F p z)) :
    (∫ p : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3), F p z).re
      = ∫ z : EuclideanSpace ℝ (Fin 3), ∫ p : EuclideanSpace ℝ (Fin 3), (F p z).re := by
  -- Fubini: swap the order of the two iterated complex integrals.
  have hswap : (∫ p : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3), F p z)
      = ∫ z : EuclideanSpace ℝ (Fin 3), ∫ p : EuclideanSpace ℝ (Fin 3), F p z :=
    MeasureTheory.integral_integral_swap hF
  rw [hswap]
  -- `Complex.re` commutes with the inner Bochner integral, slice by slice.
  have hpoint : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ p : EuclideanSpace ℝ (Fin 3), F p z).re = ∫ p : EuclideanSpace ℝ (Fin 3), (F p z).re := by
    intro z
    have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM (hslice z)
    simp only [Complex.reCLM_apply] at h
    exact h.symm
  -- The `z`-slice integrals are integrable in `z` (Fubini again), so `Complex.re` commutes
  -- with the outer integral as well.
  have hint : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => ∫ p : EuclideanSpace ℝ (Fin 3), F p z) MeasureTheory.volume :=
    MeasureTheory.Integrable.integral_prod_right hF
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hint
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)

end Work.BoseFixB3.CS.Pieces
