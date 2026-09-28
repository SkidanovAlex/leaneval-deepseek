import Mathlib
import Submission.Work.HP.Defs

/-!
# The volume of a Euclidean ball

In `ℝ^R` (realised as `EuclideanSpace ℝ (Fin R)`) the Lebesgue measure of the closed ball of
radius `S` is `ballVol R * S ^ R`, where `ballVol R` is the volume of the unit ball.

The computation goes through Mathlib's explicit formula `EuclideanSpace.volume_closedBall`
for the volume of a ball in a Euclidean space, together with the definition of `ballVol`
as the real part of the volume of the unit ball.
-/

namespace Work.HP

theorem volume_closedBall_euclid (R : ℕ) (hR : 1 ≤ R) (S : ℝ) (hS : 0 ≤ S) :
    MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin R)) S) =
      ENNReal.ofReal (ballVol R * S ^ R) := by
  -- `Fin R` is nonempty because `1 ≤ R`; this is the instance needed by the ball formula.
  have hne : Nonempty (Fin R) := ⟨⟨0, by omega⟩⟩
  -- The closed ball of radius `S` has volume `(ofReal S)^R * ofReal g`, where
  -- `g = √π ^ R / Gamma (R / 2 + 1)`; at `S = 1` this identifies `ballVol R` with `g`.
  have h1 : MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin R)) 1)
      = ENNReal.ofReal (Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1)) := by
    rw [EuclideanSpace.volume_closedBall]
    simp
  have hvol := EuclideanSpace.volume_closedBall (Fin R) (0 : EuclideanSpace ℝ (Fin R)) S
  simp only [Fintype.card_fin] at hvol
  rw [hvol]
  unfold ballVol
  rw [h1, ENNReal.toReal_ofReal (by positivity)]
  rw [← ENNReal.ofReal_pow hS]
  rw [ENNReal.ofReal_mul
    (by positivity : (0 : ℝ) ≤ Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1))]
  rw [mul_comm]

end Work.HP
