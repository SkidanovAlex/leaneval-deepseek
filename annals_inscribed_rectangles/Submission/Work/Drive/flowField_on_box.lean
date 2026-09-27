import Mathlib
import Submission.Work.Drive.BoxParityDefs

namespace Work.Drive

open Metric

noncomputable section

/-- On the unit box, the bump `boxBump m` takes the value `1`: every point of `[0,1]^{m+1}` lies
in the closed ball of radius `√(m+1)` around the origin, which is contained in the inner ball of
the bump (of radius `√(m+1) + 1`). -/
theorem boxBump_eq_one_of_mem_unitBox {m : ℕ} {x : Amb m}
    (hx : x ∈ Submission.Drive.unitBox m) : boxBump m x = 1 := by
  -- `‖x‖ ≤ √(m+1)`, since each coordinate of `x` lies in `[0,1]`.
  have hnorm2 : ‖x‖ ^ 2 ≤ ((m : ℝ) + 1) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i : Fin (m + 1), x i ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 := (hx i).1
          have h2 := (hx i).2
          nlinarith
      _ = ((m : ℝ) + 1) := by simp
  have hnorm : ‖x‖ ≤ Real.sqrt ((m : ℝ) + 1) :=
    calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_le_sqrt hnorm2
  have hbump : (⟨Real.sqrt (m + 1) + 1, Real.sqrt (m + 1) + 2, by positivity,
      by linarith⟩ : ContDiffBump (0 : Amb m)) x = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith [Real.sqrt_nonneg ((m : ℝ) + 1)]
  simpa [boxBump] using hbump

theorem flowField_on_box {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    {x : Work.Drive.Amb m} (hx : x ∈ Submission.Drive.unitBox m) :
    Work.Drive.flowField F x =
      (Real.sqrt (1 + ‖Work.Drive.cofactorVectorF F x‖ ^ 2))⁻¹ •
        Work.Drive.cofactorVectorF F x := by
  rw [flowField, boxBump_eq_one_of_mem_unitBox hx, one_smul]

end

end Work.Drive
