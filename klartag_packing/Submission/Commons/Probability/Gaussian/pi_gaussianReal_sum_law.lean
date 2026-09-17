import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

namespace Commons.Probability.Gaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The law of the sum of `n` independent standard Gaussians is the centred Gaussian of
variance `n`.  Concretely, the push-forward of the `n`-fold product of `gaussianReal 0 1`
under the summation map is `gaussianReal 0 n`. -/
theorem pi_gaussianReal_sum_law (n : ℕ) :
    (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)).map
        (fun ω : Fin n → ℝ => ∑ i, ω i)
      = ProbabilityTheory.gaussianReal 0 (n : ℝ≥0) := by
  have hX : ∀ i : Fin n,
      HasGaussianLaw (fun ω : Fin n → ℝ => ω i)
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    intro i
    have hmap : (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
        (fun ω : Fin n → ℝ => ω i) = gaussianReal 0 1 :=
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq
    exact ⟨(measurable_pi_apply i).aemeasurable, by rw [hmap]; infer_instance⟩
  have hindep : iIndepFun (fun i (ω : Fin n → ℝ) => ω i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hsum : HasGaussianLaw (fun ω : Fin n → ℝ => ∑ i, ω i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (hindep.hasGaussianLaw hX).fun_sum
  rw [HasGaussianLaw.map_eq_gaussianReal hsum]
  congr 1
  · rw [integral_finsetSum (s := Finset.univ) (f := fun i (ω : Fin n → ℝ) => ω i)
        (fun _ _ => MeasureTheory.integrable_eval (μ := fun _ : Fin n => gaussianReal 0 1)
          IsGaussian.integrable_id)]
    simp [MeasureTheory.integral_eval, integral_id_gaussianReal]
  · have hvar2 : Var[(∑ i : Fin n, fun ω : Fin n → ℝ => (id : ℝ → ℝ) (ω i));
        Measure.pi (fun _ : Fin n => gaussianReal 0 1)] = (n : ℝ) := by
      rw [variance_sum_pi (μ := fun _ : Fin n => gaussianReal 0 1)
        (X := fun _ : Fin n => (id : ℝ → ℝ)) (h := fun _ => IsGaussian.memLp_two_id)]
      simp [variance_id_gaussianReal]
    have heq : (fun ω : Fin n → ℝ => ∑ i, ω i)
        = (∑ i : Fin n, fun ω : Fin n → ℝ => (id : ℝ → ℝ) (ω i)) := by
      ext ω; simp
    rw [heq, hvar2, Real.toNNReal_natCast]

end Commons.Probability.Gaussian