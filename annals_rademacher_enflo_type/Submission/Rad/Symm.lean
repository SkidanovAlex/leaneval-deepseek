import Submission.Rad.Prob
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

namespace RadType
open RademacherEnfloType

lemma bernoulli_symm_half (s : Set C) (hs : MeasurableSet s) :
    ProbabilityTheory.bernoulliMeasure (⟨-1, by decide⟩ : C) (⟨1, by decide⟩ : C)
        (⟨1 / 2, by norm_num⟩ : unitInterval) s
      = ProbabilityTheory.bernoulliMeasure (⟨1, by decide⟩ : C) (⟨-1, by decide⟩ : C)
        (⟨1 / 2, by norm_num⟩ : unitInterval) s := by
  classical
  by_cases h1 : (⟨1, by decide⟩ : C) ∈ s
  · by_cases hm1 : (⟨-1, by decide⟩ : C) ∈ s
    · simp [bernoulliMeasure_def, h1, hm1]
    · norm_num [bernoulliMeasure_def, h1, hm1, unitInterval.symm]
  · by_cases hm1 : (⟨-1, by decide⟩ : C) ∈ s
    · norm_num [bernoulliMeasure_def, h1, hm1, unitInterval.symm]
    · simp [bernoulliMeasure_def, h1, hm1]

/-- The Rademacher measure is invariant under the sign flip on `{-1,1}`. -/
lemma map_neg_rademacher : (rademacherDistribution.map (fun z : C => -z)) = rademacherDistribution := by
  unfold rademacherDistribution
  rw [map_bernoulliMeasure]
  apply Measure.ext
  intro s hs
  exact bernoulli_symm_half s hs

/-- The uniform cube measure is invariant under coordinatewise sign flip. -/
lemma map_neg_cube {n : ℕ} :
    (rademacherProductDistribution (Fin n)).map (fun ε : Ω n => negΩ ε)
      = rademacherProductDistribution (Fin n) := by
  unfold rademacherProductDistribution
  rw [show (fun ε : Ω n => negΩ ε) = (fun (x : Fin n → C) (i : Fin n) => - x i) by rfl]
  rw [MeasureTheory.Measure.infinitePi_map_pi
    (μ := fun _ : Fin n => rademacherDistribution) (f := fun _ (z : C) => -z)]
  · simp [map_neg_rademacher]
  · intro i; fun_prop

/-- Coordinatewise sign flip is measurable. -/
lemma measurable_negΩ {n : ℕ} : Measurable (fun ε : Ω n => negΩ ε) := by
  fun_prop

/-- Any function on the (finite) cube into `ℝ≥0∞` is measurable. -/
lemma measurable_cube_ennreal {n : ℕ} (F : Ω n → ℝ≥0∞) : Measurable F :=
  measurable_of_countable F

/-- `lintegral` invariance under coordinatewise sign flip. -/
lemma lintegral_negΩ {n : ℕ} (F : Ω n → ℝ≥0∞) :
    (∫⁻ (ε : Ω n), F (negΩ ε) ∂rademacherProductDistribution (Fin n))
      = (∫⁻ (ε : Ω n), F ε ∂rademacherProductDistribution (Fin n)) := by
  calc
    (∫⁻ (ε : Ω n), F (negΩ ε) ∂rademacherProductDistribution (Fin n))
        = ∫⁻ (y : Ω n), F y ∂(rademacherProductDistribution (Fin n)).map
            (fun ε : Ω n => negΩ ε) := by
          rw [← lintegral_map (measurable_cube_ennreal F) measurable_negΩ]
    _ = ∫⁻ (ε : Ω n), F ε ∂rademacherProductDistribution (Fin n) := by
          rw [map_neg_cube]

/-- The uniform cube measure is preserved by sign flip. -/
lemma measurePreserving_negΩ {n : ℕ} :
    MeasurePreserving (fun ε : Ω n => negΩ ε)
      (rademacherProductDistribution (Fin n)) (rademacherProductDistribution (Fin n)) where
  measurable := measurable_negΩ
  map_eq := map_neg_cube

lemma negΩ_injective {n : ℕ} : Function.Injective (fun ε : Ω n => negΩ ε) := by
  intro a b h
  have h' := congrArg negΩ h
  simpa using h'

/-- Bochner integral invariance under sign flip. -/
lemma integral_negΩ {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (F : Ω n → X) :
    (∫ (ε : Ω n), F (negΩ ε) ∂rademacherProductDistribution (Fin n))
      = (∫ (ε : Ω n), F ε ∂rademacherProductDistribution (Fin n)) := by
  exact measurePreserving_negΩ.integral_comp (measurable_negΩ.measurableEmbedding negΩ_injective) F

end RadType
