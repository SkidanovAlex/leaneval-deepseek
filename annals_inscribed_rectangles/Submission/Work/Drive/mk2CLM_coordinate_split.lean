import Mathlib
import Submission.Work.Drive.mk2CLM

namespace Work.Drive

/-- The `(u 0, u 1)`-projection and the third-coordinate functional on `ℝ³` form a coordinate
splitting: there is a vector killed by `mk2CLM` but not by `coordCLM2`, and `mk2CLM` is surjective
already on the kernel of `coordCLM2`. -/
theorem mk2CLM_coordinate_split :
    (∃ w : EuclideanSpace ℝ (Fin 3),
        Work.Drive.mk2CLM w = 0 ∧ Work.Drive.coordCLM2 w ≠ 0) ∧
      (∀ y : EuclideanSpace ℝ (Fin 2), ∃ v : EuclideanSpace ℝ (Fin 3),
        Work.Drive.coordCLM2 v = 0 ∧ Work.Drive.mk2CLM v = y) := by
  constructor
  · refine ⟨WithLp.toLp 2 (![0, 0, 1] : Fin 3 → ℝ), ?_, ?_⟩
    · ext i; fin_cases i <;> simp [mk2CLM, mk2Lin, mk2]
    · rw [coordCLM2_apply]; norm_num
  · intro y
    refine ⟨WithLp.toLp 2 (![y 0, y 1, 0] : Fin 3 → ℝ), ?_, ?_⟩
    · rw [coordCLM2_apply]; simp
    · ext i; fin_cases i <;> simp [mk2CLM, mk2Lin, mk2]

end Work.Drive
