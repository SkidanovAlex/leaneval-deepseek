import Submission.E8Trunc

/-!
# The Klimyk values of the forty dominant weights

`KbZ (ord40get i) = ccv i` for the forty dominant weights of `L(λ) ⊗ L(λ)`, checked by `decide` over
the certified ball of radius `4` (`Submission.E8Ball.e8ball`, 450 entries).  This is the numerical
input of the proof that all forty isotypic components occur in the tensor square
(`Submission/E8Ncard.lean`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Submission.E8Num40

open Commons.LinearAlgebra.Matrix.Cartan
open Submission.E8Extract
open Submission.E8Trunc

theorem KbZ_ccv_0 : KbZ (ord40get (0 : Fin 40)) = ccv (0 : Fin 40) := by decide

theorem KbZ_ccv_1 : KbZ (ord40get (1 : Fin 40)) = ccv (1 : Fin 40) := by decide

theorem KbZ_ccv_2 : KbZ (ord40get (2 : Fin 40)) = ccv (2 : Fin 40) := by decide

theorem KbZ_ccv_3 : KbZ (ord40get (3 : Fin 40)) = ccv (3 : Fin 40) := by decide

theorem KbZ_ccv_4 : KbZ (ord40get (4 : Fin 40)) = ccv (4 : Fin 40) := by decide

theorem KbZ_ccv_5 : KbZ (ord40get (5 : Fin 40)) = ccv (5 : Fin 40) := by decide

theorem KbZ_ccv_6 : KbZ (ord40get (6 : Fin 40)) = ccv (6 : Fin 40) := by decide

theorem KbZ_ccv_7 : KbZ (ord40get (7 : Fin 40)) = ccv (7 : Fin 40) := by decide

theorem KbZ_ccv_8 : KbZ (ord40get (8 : Fin 40)) = ccv (8 : Fin 40) := by decide

theorem KbZ_ccv_9 : KbZ (ord40get (9 : Fin 40)) = ccv (9 : Fin 40) := by decide

end Submission.E8Num40
