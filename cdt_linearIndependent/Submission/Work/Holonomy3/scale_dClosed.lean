import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

/-- Scaling a family of power series by a (nonzero) rational scalar preserves `D`-closure: the
witnessing polynomial and matrix can be kept unchanged, since `derivative` is `ℚ`-linear and the
scaled coefficients commute with multiplication. -/
theorem scale_dClosed {m : ℕ} (q : ℕ) (hq : 0 < q) (f : Fin m → PowerSeries ℚ) (h : Submission.CDTPlan.DClosed f) : Submission.CDTPlan.DClosed (fun i => (q : ℚ)⁻¹ • f i) := by
  obtain ⟨P, hP, A, hA⟩ := h
  refine ⟨P, hP, A, fun i => ?_⟩
  rw [Derivation.map_smul]
  calc ↑P * ((q : ℚ)⁻¹ • (PowerSeries.derivative (R := ℚ)) (f i))
      = (q : ℚ)⁻¹ • (↑P * (PowerSeries.derivative (R := ℚ)) (f i)) := mul_smul_comm _ _ _
    _ = (q : ℚ)⁻¹ • ∑ j, ↑(A i j) * f j := by rw [hA i]
    _ = ∑ j, ↑(A i j) * ((q : ℚ)⁻¹ • f j) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm

end Work.Holonomy3
