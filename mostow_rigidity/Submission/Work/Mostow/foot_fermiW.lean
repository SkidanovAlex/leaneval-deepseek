import Mathlib
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.fermiW_chart

namespace Work.Mostow

/-- The normal (last `m`) chart coordinates of `fermiW 1 m v W` are exactly `W`. -/
private lemma nrmC_fermiW (m : ℕ) (v : Submission.Mostow.E 1) (W : Submission.Mostow.E m) :
    Submission.Mostow.nrmC 1 m (Submission.Mostow.fermiW 1 m v W) = W := by
  ext i
  simp [Submission.Mostow.nrmC, Submission.Mostow.fermiW]

/-- The tangential (first `1`) chart coordinates of `fermiW 1 m v W` are `√(1+‖W‖²) • v`. -/
private lemma tanC_fermiW (m : ℕ) (v : Submission.Mostow.E 1) (W : Submission.Mostow.E m) :
    Submission.Mostow.tanC 1 m (Submission.Mostow.fermiW 1 m v W)
      = Real.sqrt (1 + ‖W‖ ^ 2) • v := by
  ext i
  simp [Submission.Mostow.tanC, Submission.Mostow.fermiW]

theorem foot_fermiW (m : ℕ) (v : Submission.Mostow.E 1) (W : Submission.Mostow.E m) :
    (Submission.Mostow.fermiInv 1 m (Submission.Mostow.fermiW 1 m v W)).1 = v := by
  have hnorm : Submission.Mostow.nrmC 1 m (Submission.Mostow.fermiW 1 m v W) = W :=
    nrmC_fermiW m v W
  have htan : Submission.Mostow.tanC 1 m (Submission.Mostow.fermiW 1 m v W)
      = Real.sqrt (1 + ‖W‖ ^ 2) • v := tanC_fermiW m v W
  have hcosh : Real.cosh (Real.arsinh ‖W‖) = Real.sqrt (1 + ‖W‖ ^ 2) := Real.cosh_arsinh ‖W‖
  show ((Real.cosh (Real.arsinh ‖Submission.Mostow.nrmC 1 m
            (Submission.Mostow.fermiW 1 m v W)‖))⁻¹
          • Submission.Mostow.tanC 1 m (Submission.Mostow.fermiW 1 m v W)) = v
  rw [hnorm, hcosh, htan, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

end Work.Mostow
