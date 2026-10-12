import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Commons.Analysis.Fourier

open MeasureTheory

/-- The real part of a complex-valued Schwartz map on `ℝ³ = EuclideanSpace ℝ (Fin 3)` is
measurable, bounded, and integrable. -/
theorem real_re_basic (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin 3) => (f x).re) ∧
      (∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), |(f x).re| ≤ C) ∧
      MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => (f x).re) := by
  constructor
  · -- Measurability: `z.re` and `f` are continuous, hence measurable.
    exact (Complex.continuous_re.measurable.comp f.continuous.measurable)
  constructor
  · -- Boundedness: seminorm bound on `‖f x‖`, and `|z.re| ≤ ‖z‖`.
    refine ⟨SchwartzMap.seminorm ℝ 0 0 f, ?_⟩
    intro x
    exact (Complex.abs_re_le_norm (f x)).trans (SchwartzMap.norm_le_seminorm ℝ f x)
  · -- Integrability: `re` is a continuous ℝ-linear map, Schwartz maps are integrable.
    simpa using (Complex.reCLM.integrable_comp (φ := fun x : EuclideanSpace ℝ (Fin 3) => f x)
      (f.integrable : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => f x)))

end Commons.Analysis.Fourier