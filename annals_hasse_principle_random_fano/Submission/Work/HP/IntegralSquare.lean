import Mathlib
import Submission.Work.HP.JcVolDefs

namespace Work.HP

open MeasureTheory

/-- The region `{u ∈ ℝ² : qbar u ≤ 1} = [-1,1]²` has measure `4`, hence the integral of its
indicator is `4`. -/
theorem IntegralSquare :
    ∫ u : EuclideanSpace ℝ (Fin 2), (if qbar u ≤ 1 then (1:ℝ) else 0) = 4 := by
  -- `qbar` is continuous, so the set `{u | qbar u ≤ 1}` is (closed, hence) measurable.
  have hcont : Continuous (fun u : EuclideanSpace ℝ (Fin 2) => qbar u) := by
    unfold qbar; fun_prop
  have hmeas : MeasurableSet {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1} :=
    IsClosed.measurableSet (isClosed_le hcont continuous_const)
  -- The integrand is the indicator of `{u | qbar u ≤ 1}`.
  have h1 : (fun u : EuclideanSpace ℝ (Fin 2) => (if qbar u ≤ 1 then (1:ℝ) else 0))
      = Set.indicator {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1} (fun _ => (1:ℝ)) := by
    funext u
    rw [Set.indicator_apply]
    by_cases h : qbar u ≤ 1 <;> simp [h]
  have h2 : ∫ u : EuclideanSpace ℝ (Fin 2), (if qbar u ≤ 1 then (1:ℝ) else 0)
      = volume.real {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1} := by
    rw [h1]
    exact MeasureTheory.integral_indicator_one hmeas
  rw [h2, measureReal_def]
  -- The set is the box `[-1,1]²`, transported from `Fin 2 → ℝ` along `toLp`.
  have key : ∀ x y : ℝ, max (x^2) (y^2) ≤ 1 ↔ (-1 ≤ x ∧ x ≤ 1) ∧ (-1 ≤ y ∧ y ≤ 1) := by
    intro x y
    rw [max_le_iff, sq_le_one_iff_abs_le_one x, sq_le_one_iff_abs_le_one y, abs_le, abs_le]
  have hpre : WithLp.toLp 2 ⁻¹' {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1}
      = Set.Icc (fun _ : Fin 2 => (-1:ℝ)) (fun _ => (1:ℝ)) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two]
    rw [show qbar (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin 2)) = max ((f 0)^2) ((f 1)^2) from by
      simp [qbar], key]
    tauto
  -- `toLp` is volume preserving, so we may compute the measure in `Fin 2 → ℝ`.
  have hmap : volume {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1}
      = volume (WithLp.toLp 2 ⁻¹' {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1}) := by
    rw [← (PiLp.volume_preserving_toLp (Fin 2)).map_eq]
    rw [Measure.map_apply (PiLp.volume_preserving_toLp (Fin 2)).measurable hmeas]
  rw [hmap, hpre, Real.volume_Icc_pi_toReal (by rw [Pi.le_def]; intro i; norm_num)]
  rw [Fin.prod_univ_two]
  norm_num

end Work.HP
