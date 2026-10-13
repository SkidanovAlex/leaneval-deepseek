import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open MeasureTheory

/-- Reflection of the Lebesgue integral on an open interval: substituting `θ = b - φ`
(the reflection `φ ↦ b - φ` maps `(0, b - a)` onto `(a, b)` and preserves Lebesgue measure)
gives `∫⁻_{θ ∈ (a,b)} F θ = ∫⁻_{φ ∈ (0,b-a)} F (b - φ)`. -/
theorem lintegral_Ioo_reflect (F : ℝ → ENNReal) (a b : ℝ) :
    (∫⁻ θ in Set.Ioo a b, F θ) = ∫⁻ φ in Set.Ioo (0 : ℝ) (b - a), F (b - φ) := by
  -- The reflection `φ ↦ b - φ` is a measurable embedding (it is an isometry of `ℝ`).
  have hemb : MeasurableEmbedding (fun φ : ℝ => b - φ) :=
    (MeasurableEquiv.subLeft b).measurableEmbedding
  -- It maps `(0, b - a)` onto `(a, b)`.
  have hpre : (fun φ : ℝ => b - φ) ⁻¹' Set.Ioo a b = Set.Ioo (0 : ℝ) (b - a) := by
    ext x; simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  -- It preserves Lebesgue measure.
  have hmap : Measure.map (fun φ : ℝ => b - φ) (volume : Measure ℝ) = volume := by
    have h1 : Measure.map (fun x : ℝ => -x) (volume : Measure ℝ) = volume :=
      Measure.map_neg_eq_self (volume : Measure ℝ)
    have h2 : Measure.map (fun y : ℝ => b + y) (volume : Measure ℝ) = volume :=
      Measure.IsAddLeftInvariant.map_add_left_eq_self b
    have hg : Measurable (fun y : ℝ => b + y) := measurable_const_add b
    have hf : Measurable (fun x : ℝ => -x) := measurable_neg
    rw [show (fun φ : ℝ => b - φ) = fun x : ℝ => b + -x from by funext x; rw [sub_eq_add_neg]]
    calc Measure.map (fun x : ℝ => b + -x) (volume : Measure ℝ)
        = Measure.map ((fun y : ℝ => b + y) ∘ (fun x : ℝ => -x)) volume := rfl
      _ = Measure.map (fun y : ℝ => b + y)
            (Measure.map (fun x : ℝ => -x) (volume : Measure ℝ)) :=
            (Measure.map_map hg hf).symm
      _ = volume := by rw [h1, h2]
  -- Hence the restricted measures correspond.
  have hres : (volume : Measure ℝ).restrict (Set.Ioo a b)
      = Measure.map (fun φ : ℝ => b - φ)
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (b - a))) := by
    have h := MeasurableEmbedding.restrict_map hemb (volume : Measure ℝ) (Set.Ioo a b)
    rw [hmap, hpre] at h
    exact h
  calc (∫⁻ θ in Set.Ioo a b, F θ)
      = ∫⁻ θ, F θ ∂((volume : Measure ℝ).restrict (Set.Ioo a b)) := rfl
    _ = ∫⁻ θ, F θ ∂(Measure.map (fun φ : ℝ => b - φ)
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (b - a)))) := by rw [hres]
    _ = ∫⁻ φ, F ((fun φ : ℝ => b - φ) φ)
          ∂((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (b - a))) :=
          MeasurableEmbedding.lintegral_map hemb F
    _ = ∫⁻ φ in Set.Ioo (0 : ℝ) (b - a), F (b - φ) := rfl

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
