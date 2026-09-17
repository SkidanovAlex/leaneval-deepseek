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

theorem KbZ_ccv_20 : KbZ (ord40get (20 : Fin 40)) = ccv (20 : Fin 40) := by decide

theorem KbZ_ccv_21 : KbZ (ord40get (21 : Fin 40)) = ccv (21 : Fin 40) := by decide

theorem KbZ_ccv_22 : KbZ (ord40get (22 : Fin 40)) = ccv (22 : Fin 40) := by decide

theorem KbZ_ccv_23 : KbZ (ord40get (23 : Fin 40)) = ccv (23 : Fin 40) := by decide

theorem KbZ_ccv_24 : KbZ (ord40get (24 : Fin 40)) = ccv (24 : Fin 40) := by decide

theorem KbZ_ccv_25 : KbZ (ord40get (25 : Fin 40)) = ccv (25 : Fin 40) := by decide

theorem KbZ_ccv_26 : KbZ (ord40get (26 : Fin 40)) = ccv (26 : Fin 40) := by decide

theorem KbZ_ccv_27 : KbZ (ord40get (27 : Fin 40)) = ccv (27 : Fin 40) := by decide

theorem KbZ_ccv_28 : KbZ (ord40get (28 : Fin 40)) = ccv (28 : Fin 40) := by decide

theorem KbZ_ccv_29 : KbZ (ord40get (29 : Fin 40)) = ccv (29 : Fin 40) := by decide

end Submission.E8Num40
