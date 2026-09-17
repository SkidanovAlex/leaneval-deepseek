import Submission.E8CharCompute
import Submission.E8Ball
import Submission.E8Enum

/-!
# The seven ball sums of the Weyl character formula for `V`

The `decide`-checked values of the alternating sum over the certified ball of radius `4`
(`Submission/E8Ball.e8ball`) at the seven dominant weights `⪯ λ`:
`∑_{ℓ(w)≤4} ε(w)·mfun(ν + ρ - wρ) = [ν = λ]`.  These are the numerical input of
`Submission.E8WCFV.WCF_V`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Submission.E8WCFBall

open Submission.E8Ball Commons.LinearAlgebra.Matrix.Cartan
open Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo
open Submission.E8Numerics Submission.E8Support

theorem ballSum_lam : Submission.E8CharCompute.ballSum
    (fun z => mnorm (qZ (Submission.E8Enum.lam + rhoZ - z))) = 1 := by decide

theorem ballSum_e1 : Submission.E8CharCompute.ballSum
    (fun z => mnorm (qZ (Submission.E8Enum.e 1 + rhoZ - z))) = 0 := by decide

theorem ballSum_2e7 : Submission.E8CharCompute.ballSum
    (fun z => mnorm (qZ (2 • Submission.E8Enum.e 7 + rhoZ - z))) = 0 := by decide

theorem ballSum_e6 : Submission.E8CharCompute.ballSum
    (fun z => mnorm (qZ (Submission.E8Enum.e 6 + rhoZ - z))) = 0 := by decide

theorem ballSum_e0 : Submission.E8CharCompute.ballSum
    (fun z => mnorm (qZ (Submission.E8Enum.e 0 + rhoZ - z))) = 0 := by decide

theorem ballSum_e7 : Submission.E8CharCompute.ballSum
    (fun z => mnorm (qZ (Submission.E8Enum.e 7 + rhoZ - z))) = 0 := by decide

theorem ballSum_zero : Submission.E8CharCompute.ballSum
    (fun z => mnorm (qZ ((0 : Fin 8 → ℤ) + rhoZ - z))) = 0 := by decide

/-- The seven values of the ball sum, in the form needed for the Weyl character formula. -/
theorem ballSum_the7 (ν : Fin 8 → ℤ) (hν : ν ∈ Submission.E8Enum.the7) :
    Submission.E8CharCompute.ballSum (fun z => mnorm (qZ (ν + rhoZ - z)))
      = (if ν = Submission.E8Enum.lam then 1 else 0) := by
  rcases Submission.E8Enum.mem_the7_cases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ballSum_lam, if_pos rfl]
  · rw [ballSum_e1, if_neg (by decide)]
  · rw [ballSum_2e7, if_neg (by decide)]
  · rw [ballSum_e6, if_neg (by decide)]
  · rw [ballSum_e0, if_neg (by decide)]
  · rw [ballSum_e7, if_neg (by decide)]
  · rw [ballSum_zero, if_neg (by decide)]


end Submission.E8WCFBall
