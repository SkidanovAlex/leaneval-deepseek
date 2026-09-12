import Submission.Rad.Symm
import Submission.Commons.Analysis.Convex.rpow_midpoint_le
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Any function on the finite cube is Bochner integrable. -/
lemma integrable_cube {n : ℕ} {E : Type*} [NormedAddCommGroup E] (f : Ω n → E) :
    Integrable f (rademacherProductDistribution (Fin n)) := by
  refine Integrable.of_bound ?hf (∑ ε' : Ω n, ‖f ε'‖) ?bound
  · exact (StronglyMeasurable.of_discrete (f := f)).aestronglyMeasurable
  · apply ae_of_all
    intro ε
    exact Finset.single_le_sum (by intro a ha; exact norm_nonneg (f a)) (Finset.mem_univ ε)

/-- Convexity of `‖·‖^p` at the midpoint, `p ≥ 1`. -/
lemma norm_midpoint_smul_pow_le (a b : X) {p : ℝ} (hp : 1 ≤ p) :
    ‖(1 / 2 : ℝ) • (a - b)‖ ^ p ≤ (‖a‖ ^ p + ‖b‖ ^ p) / 2 := by
  have hp0 : 0 ≤ p := by linarith
  calc
    ‖(1 / 2 : ℝ) • (a - b)‖ ^ p ≤ ((‖a‖ + ‖b‖) / 2) ^ p := by
      apply Real.rpow_le_rpow (norm_nonneg _)
      · calc
          ‖(1 / 2 : ℝ) • (a - b)‖ = ‖(1 / 2 : ℝ)‖ * ‖a - b‖ := by rw [norm_smul]
          _ = (1 / 2 : ℝ) * ‖a - b‖ := by simp
          _ = ‖a - b‖ / 2 := by ring
          _ ≤ (‖a‖ + ‖b‖) / 2 := div_le_div_of_nonneg_right (norm_sub_le a b) (by norm_num)
      · exact hp0
    _ ≤ (‖a‖ ^ p + ‖b‖ ^ p) / 2 := by
      exact Commons.Analysis.Convex.rpow_midpoint_le (p := p) (x := ‖a‖) (y := ‖b‖)
        hp (norm_nonneg a) (norm_nonneg b)

/-- Uniform expectation of a real-valued function on the cube. -/
noncomputable def meanReal {n : ℕ} (F : Ω n → ℝ) : ℝ :=
  ∫ ε : Ω n, F ε ∂(rademacherProductDistribution (Fin n))

/-- Uniform expectation of an `X`-valued function on the cube. -/
noncomputable def meanX {n : ℕ} (f : Ω n → X) : X :=
  ∫ ε : Ω n, f ε ∂(rademacherProductDistribution (Fin n))

/--
Symmetrization step (real-valued): the expected distance from `f(ε)` to `f(-ε)` is at most
the expected distance from `f(ε)` to its mean `meanX f`.
-/
lemma symm_pow_mean_le {n : ℕ} (f : Ω n → X) {p : ℝ} (hp : 1 ≤ p) :
    meanReal (fun ε : Ω n => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p) ≤
    meanReal (fun ε : Ω n => ‖f ε - meanX f‖ ^ p) := by
  let c : X := meanX f
  let A : Ω n → ℝ := fun ε => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p
  let U : Ω n → ℝ := fun ε => ‖f ε - c‖ ^ p
  let V : Ω n → ℝ := fun ε => ‖f (negΩ ε) - c‖ ^ p
  have hpoint : ∀ ε : Ω n, A ε ≤ (U ε + V ε) / 2 := by
    intro ε
    change ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p ≤
      (‖f ε - c‖ ^ p + ‖f (negΩ ε) - c‖ ^ p) / 2
    have hsub : (1 / 2 : ℝ) • (f ε - f (negΩ ε)) = (1 / 2 : ℝ) • ((f ε - c) - (f (negΩ ε) - c)) := by
      congr 1
      abel
    rw [hsub]
    exact norm_midpoint_smul_pow_le (f ε - c) (f (negΩ ε) - c) hp
  have hA : Integrable A (rademacherProductDistribution (Fin n)) := integrable_cube A
  have hU : Integrable U (rademacherProductDistribution (Fin n)) := integrable_cube U
  have hV : Integrable V (rademacherProductDistribution (Fin n)) := integrable_cube V
  -- first inequality of integrals
  have hstep : meanReal A ≤ meanReal (fun ε => (U ε + V ε) / 2) := by
    unfold meanReal
    apply integral_mono hA
    · exact integrable_cube (fun ε : Ω n => (U ε + V ε) / 2)
    · intro ε
      exact hpoint ε
  -- ∫ (U+V)/2 = (∫U + ∫V)/2
  have hlin : meanReal (fun ε => (U ε + V ε) / 2) = (meanReal U + meanReal V) / 2 := by
    unfold meanReal
    calc
      (∫ ε : Ω n, (U ε + V ε) / 2 ∂rademacherProductDistribution (Fin n))
          = (∫ ε : Ω n, (U ε + V ε) ∂rademacherProductDistribution (Fin n)) / 2 := by
            rw [integral_div]
      _ = (∫ ε : Ω n, U ε ∂rademacherProductDistribution (Fin n) +
          ∫ ε : Ω n, V ε ∂rademacherProductDistribution (Fin n)) / 2 := by
            rw [integral_add hU hV]
      _ = (meanReal U + meanReal V) / 2 := rfl
  -- symmetry ∫V = ∫U
  have hsym : meanReal V = meanReal U := by
    unfold meanReal V U
    exact integral_negΩ (n := n) (X := ℝ) (fun ε : Ω n => ‖f ε - c‖ ^ p)
  -- assemble
  calc
    meanReal A ≤ meanReal (fun ε => (U ε + V ε) / 2) := hstep
    _ = (meanReal U + meanReal V) / 2 := hlin
    _ = (meanReal U + meanReal U) / 2 := by rw [hsym]
    _ = meanReal U := by ring
    _ = meanReal (fun ε : Ω n => ‖f ε - meanX f‖ ^ p) := rfl

end RadType
