import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- For a nonnegative measurable function, the set integral over a disjoint union is at most the
sum of the two set integrals.  (Real-valued set integrals are `ENNReal.toReal` of the corresponding
`lintegral`s, and `toReal` is subadditive; this avoids any integrability hypothesis.) -/
private theorem setIntegral_union_le_aux {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hfm : MeasureTheory.AEStronglyMeasurable f μ)
    {A B : Set α} (hB : MeasurableSet B) (hd : Disjoint A B) :
    ∫ x in A ∪ B, f x ∂μ ≤ ∫ x in A, f x ∂μ + ∫ x in B, f x ∂μ := by
  have h1 : ∫ x in A ∪ B, f x ∂μ
      = (∫⁻ x in A ∪ B, ENNReal.ofReal (f x) ∂μ).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf) hfm.restrict
  have h2 : ∫ x in A, f x ∂μ = (∫⁻ x in A, ENNReal.ofReal (f x) ∂μ).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf) hfm.restrict
  have h3 : ∫ x in B, f x ∂μ = (∫⁻ x in B, ENNReal.ofReal (f x) ∂μ).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf) hfm.restrict
  rw [h1, h2, h3, MeasureTheory.lintegral_union hB hd]
  exact ENNReal.toReal_add_le

theorem setIntegral_split_le {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ∀ p, 0 ≤ f p) (hfm : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    {P₀ L : ℝ} (hPL : P₀ ≤ L) :
    (∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖}, f p)
      ≤ (∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖ ∧ ‖p‖ ≤ L}, f p)
        + (∫ p in {p : EuclideanSpace ℝ (Fin 3) | L < ‖p‖}, f p) := by
  have hB : MeasurableSet {p : EuclideanSpace ℝ (Fin 3) | L < ‖p‖} := by
    have h : {p : EuclideanSpace ℝ (Fin 3) | L < ‖p‖}
        = {p : EuclideanSpace ℝ (Fin 3) | (fun _ : EuclideanSpace ℝ (Fin 3) => L) p < ‖p‖} := rfl
    rw [h]
    exact measurableSet_lt measurable_const continuous_norm.measurable
  have hd : Disjoint {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖ ∧ ‖p‖ ≤ L}
      {p : EuclideanSpace ℝ (Fin 3) | L < ‖p‖} := by
    rw [Set.disjoint_left]
    rintro p ⟨-, hle⟩ hlt
    exact absurd hlt (not_lt.mpr hle)
  have hS : {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖}
      = {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖ ∧ ‖p‖ ≤ L}
        ∪ {p : EuclideanSpace ℝ (Fin 3) | L < ‖p‖} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hp
      rcases le_or_gt ‖p‖ L with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr h
    · rintro (⟨hp, _⟩ | h)
      · exact hp
      · exact lt_of_le_of_lt hPL h
  rw [hS]
  exact setIntegral_union_le_aux hf hfm hB hd

end Work.BoseBogFS
