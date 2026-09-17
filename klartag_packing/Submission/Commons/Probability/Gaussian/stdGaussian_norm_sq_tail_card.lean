import Mathlib
import Submission.Commons.Probability.Gaussian.stdGaussian_norm_sq_tail
import Submission.Commons.Probability.Gaussian.integral_exp_mul_sq_norm_stdGaussian

namespace Commons.Probability.Gaussian

open MeasureTheory ProbabilityTheory

/-- The linearly isometric equivalence identifying `EuclideanSpace ℝ ι` with
`EuclideanSpace ℝ (Fin (Fintype.card ι))`, induced by some bijection `ι ≃ Fin (Fintype.card ι)`. -/
private noncomputable abbrev cardEquiv (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)

/-- `cardEquiv` is an isometry. -/
private lemma cardEquiv_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖cardEquiv ι x‖ = ‖x‖ := LinearIsometryEquiv.norm_map _ _

/-- **Tail bound for the squared norm of a standard Gaussian vector, in arbitrary finite
dimension.**  For `u ≥ 0`, the standard Gaussian measure on `EuclideanSpace ℝ ι` gives the set
`{x | u ≤ ‖x‖ ^ 2}` mass at most `2 ^ card ι * exp (-(3 / 8) u)`.

The proof reduces to the case `Fin n` (the commons lemma
`Commons.Probability.Gaussian.stdGaussian_norm_sq_tail`) via the linear isometry equivalence
`EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι))`: the standard Gaussian
measure is pushed forward to the standard Gaussian measure (`stdGaussian_map`), and the set
`{x | u ≤ ‖x‖ ^ 2}` is invariant under an isometry. -/
theorem stdGaussian_norm_sq_tail_card {ι : Type*} [Fintype ι] {u : ℝ} (hu : 0 ≤ u) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).real {x | u ≤ ‖x‖ ^ 2}
      ≤ (2 : ℝ) ^ (Fintype.card ι) * Real.exp (-(3 / 8) * u) := by
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin (Fintype.card ι)) | u ≤ ‖x‖ ^ 2} :=
    measurableSet_le measurable_const (measurable_norm.pow_const 2)
  have hpre : (cardEquiv ι) ⁻¹' {x : EuclideanSpace ℝ (Fin (Fintype.card ι)) | u ≤ ‖x‖ ^ 2}
      = {x : EuclideanSpace ℝ ι | u ≤ ‖x‖ ^ 2} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, cardEquiv_norm]
  have hmap : (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map (cardEquiv ι)
      = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (Fintype.card ι))) :=
    ProbabilityTheory.stdGaussian_map (cardEquiv ι)
  have hreal : (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).real {x | u ≤ ‖x‖ ^ 2}
      = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (Fintype.card ι)))).real
          {x | u ≤ ‖x‖ ^ 2} := by
    rw [hmap.symm, map_measureReal_apply (cardEquiv ι).continuous.measurable hmeas, hpre]
  rw [hreal]
  exact stdGaussian_norm_sq_tail (n := Fintype.card ι) hu

end Commons.Probability.Gaussian
