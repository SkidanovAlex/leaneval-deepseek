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

theorem KbZ_ccv_10 : KbZ (ord40get (10 : Fin 40)) = ccv (10 : Fin 40) := by decide

theorem KbZ_ccv_11 : KbZ (ord40get (11 : Fin 40)) = ccv (11 : Fin 40) := by decide

theorem KbZ_ccv_12 : KbZ (ord40get (12 : Fin 40)) = ccv (12 : Fin 40) := by decide

theorem KbZ_ccv_13 : KbZ (ord40get (13 : Fin 40)) = ccv (13 : Fin 40) := by decide

theorem KbZ_ccv_14 : KbZ (ord40get (14 : Fin 40)) = ccv (14 : Fin 40) := by decide

theorem KbZ_ccv_15 : KbZ (ord40get (15 : Fin 40)) = ccv (15 : Fin 40) := by decide

theorem KbZ_ccv_16 : KbZ (ord40get (16 : Fin 40)) = ccv (16 : Fin 40) := by decide

theorem KbZ_ccv_17 : KbZ (ord40get (17 : Fin 40)) = ccv (17 : Fin 40) := by decide

theorem KbZ_ccv_18 : KbZ (ord40get (18 : Fin 40)) = ccv (18 : Fin 40) := by decide

theorem KbZ_ccv_19 : KbZ (ord40get (19 : Fin 40)) = ccv (19 : Fin 40) := by decide

end Submission.E8Num40
