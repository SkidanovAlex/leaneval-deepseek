import Submission.E8NumA
import Submission.E8NumB
import Submission.E8NumC
import Submission.E8NumD

/-!
# The Klimyk values of the forty dominant weights (combined)
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Submission.E8Num40

open Commons.LinearAlgebra.Matrix.Cartan
open Submission.E8Extract
open Submission.E8Trunc

theorem KbZ_ccv (i : Fin 40) : KbZ (ord40get i) = ccv i := by
  fin_cases i
  · exact KbZ_ccv_0
  · exact KbZ_ccv_1
  · exact KbZ_ccv_2
  · exact KbZ_ccv_3
  · exact KbZ_ccv_4
  · exact KbZ_ccv_5
  · exact KbZ_ccv_6
  · exact KbZ_ccv_7
  · exact KbZ_ccv_8
  · exact KbZ_ccv_9
  · exact KbZ_ccv_10
  · exact KbZ_ccv_11
  · exact KbZ_ccv_12
  · exact KbZ_ccv_13
  · exact KbZ_ccv_14
  · exact KbZ_ccv_15
  · exact KbZ_ccv_16
  · exact KbZ_ccv_17
  · exact KbZ_ccv_18
  · exact KbZ_ccv_19
  · exact KbZ_ccv_20
  · exact KbZ_ccv_21
  · exact KbZ_ccv_22
  · exact KbZ_ccv_23
  · exact KbZ_ccv_24
  · exact KbZ_ccv_25
  · exact KbZ_ccv_26
  · exact KbZ_ccv_27
  · exact KbZ_ccv_28
  · exact KbZ_ccv_29
  · exact KbZ_ccv_30
  · exact KbZ_ccv_31
  · exact KbZ_ccv_32
  · exact KbZ_ccv_33
  · exact KbZ_ccv_34
  · exact KbZ_ccv_35
  · exact KbZ_ccv_36
  · exact KbZ_ccv_37
  · exact KbZ_ccv_38
  · exact KbZ_ccv_39

end Submission.E8Num40
