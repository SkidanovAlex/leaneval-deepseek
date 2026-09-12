import Submission.Rad.Biased
import Submission.Rad.S1
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

noncomputable section

namespace RadType
open RademacherEnfloType

/-- The uniform point mass on the cube is `(1/2)^n`. -/
lemma uniform_real_mass {n : ℕ} (ξ : Ω n) :
    (rademacherProductDistribution (Fin n)).real ({ξ} : Set (Ω n)) = (1 / 2 : ℝ) ^ n := by
  classical
  unfold rademacherProductDistribution
  change ((Measure.infinitePi (fun _ : Fin n => rademacherDistribution)) {ξ}).toReal
      = (1 / 2 : ℝ) ^ n
  rw [Measure.infinitePi_eq_pi]
  rw [Measure.pi_singleton]
  have hcoord : ∀ z : C, (rademacherDistribution {z}).toReal = (1 / 2 : ℝ) := by
    intro z
    rw [← measureReal_def]
    rcases val_eq z with hz | hz
    · have hzC : z = cOne := by
        apply Subtype.ext
        simpa [cOne] using hz
      rw [hzC]
      unfold rademacherDistribution
      rw [bernoulliMeasure_real_apply_of_mem_of_notMem (⟨(1 : ℝ) / 2, by norm_num⟩ : unitInterval)
        (MeasurableSet.singleton cOne)
        (by change (⟨(1 : ℤ), by decide⟩ : C) = cOne; exact Subtype.ext rfl : (⟨(1 : ℤ), by decide⟩ : C) ∈ ({cOne} : Set C))
        (by intro h; have hz := congrArg (fun z : C => (z : ℤ)) h; norm_num [cOne, cNegOne] at hz : (⟨(-1 : ℤ), by decide⟩ : C) ∉ ({cOne} : Set C))]
    · have hzC : z = cNegOne := by
        apply Subtype.ext
        simpa [cNegOne] using hz
      rw [hzC]
      unfold rademacherDistribution
      rw [bernoulliMeasure_real_apply_of_notMem_of_mem (⟨(1 : ℝ) / 2, by norm_num⟩ : unitInterval)
        (MeasurableSet.singleton cNegOne)
        (by intro h; have hz := congrArg (fun z : C => (z : ℤ)) h; norm_num [cOne, cNegOne] at hz : (⟨(1 : ℤ), by decide⟩ : C) ∉ ({cNegOne} : Set C))
        (by change (⟨(-1 : ℤ), by decide⟩ : C) = cNegOne; exact Subtype.ext rfl : (⟨(-1 : ℤ), by decide⟩ : C) ∈ ({cNegOne} : Set C))]
      · norm_num
  have hprod : (∏ j : Fin n, (rademacherDistribution {ξ j}).toReal)
      = ∏ j : Fin n, (1 / 2 : ℝ) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    exact hcoord (ξ j)
  rw [ENNReal.toReal_prod]
  rw [hprod]
  simp

/-- The real (Bochner) integral over the uniform cube measure is the average over the cube. -/
lemma integral_uniform_eq {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : Ω n → E) :
    (∫ ξ : Ω n, g ξ ∂rademacherProductDistribution (Fin n))
      = ∑ ξ : Ω n, ((1 / 2 : ℝ) ^ n) • g ξ := by
  rw [integral_fintype (f := g)]
  · apply Finset.sum_congr rfl
    intro ξ hξ
    congr 1
    exact uniform_real_mass (n := n) ξ
  · exact integrable_cube g

/-- The real (Bochner) integral over the biased cube measure is the weighted sum over the cube. -/
lemma integral_biased_eq {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (θ : ℝ) (g : Ω n → E) :
    (∫ ξ : Ω n, g ξ ∂biasedMeasure (n := n) θ)
      = ∑ ξ : Ω n, (biasW θ ξ) • g ξ := by
  rw [integral_fintype (f := g)]
  · apply Finset.sum_congr rfl
    intro ξ hξ
    congr 1
    exact biased_real_mass θ ξ
  · exact integrable_biased θ g

