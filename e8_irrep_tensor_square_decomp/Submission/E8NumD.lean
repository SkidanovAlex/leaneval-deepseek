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

theorem KbZ_ccv_30 : KbZ (ord40get (30 : Fin 40)) = ccv (30 : Fin 40) := by decide

theorem KbZ_ccv_31 : KbZ (ord40get (31 : Fin 40)) = ccv (31 : Fin 40) := by decide

theorem KbZ_ccv_32 : KbZ (ord40get (32 : Fin 40)) = ccv (32 : Fin 40) := by decide

theorem KbZ_ccv_33 : KbZ (ord40get (33 : Fin 40)) = ccv (33 : Fin 40) := by decide

theorem KbZ_ccv_34 : KbZ (ord40get (34 : Fin 40)) = ccv (34 : Fin 40) := by decide

theorem KbZ_ccv_35 : KbZ (ord40get (35 : Fin 40)) = ccv (35 : Fin 40) := by decide

theorem KbZ_ccv_36 : KbZ (ord40get (36 : Fin 40)) = ccv (36 : Fin 40) := by decide

theorem KbZ_ccv_37 : KbZ (ord40get (37 : Fin 40)) = ccv (37 : Fin 40) := by decide

theorem KbZ_ccv_38 : KbZ (ord40get (38 : Fin 40)) = ccv (38 : Fin 40) := by decide

theorem KbZ_ccv_39 : KbZ (ord40get (39 : Fin 40)) = ccv (39 : Fin 40) := by decide

end Submission.E8Num40
