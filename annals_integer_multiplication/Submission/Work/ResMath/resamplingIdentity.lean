import Mathlib
import Submission.Work.ResMath.defs
import Submission.Work.ResMath.resamplingDefs
import Submission.Work.ResMath.resamplingAux
import Submission.Work.ResMath.resamplingAssembly
import Submission.Work.ResMath.resamplingAssembly2
import Submission.Work.ResMath.resamplingAssembly3

namespace Work.ResMath

open HvdH

theorem resamplingIdentity (s t α : ℕ) (hs : 2 ≤ s) (hst : s < t) (hstc : Nat.Coprime s t) (hα : 2 ≤ α) :
    HvdH.resTmat s t α * HvdH.permS s t * HvdH.dftMat s =
      HvdH.permT s t * HvdH.dftMat t * HvdH.resSmat s t α := by
  have hs0 : 0 < s := by omega
  have ht0 : 0 < t := by omega
  have hα0 : 0 < α := by omega
  ext k i
  have hmul : ((HvdH.resTmat s t α * HvdH.permS s t * HvdH.dftMat s).mulVec (Pi.single i 1)) k
      = ((HvdH.permT s t * HvdH.dftMat t * HvdH.resSmat s t α).mulVec (Pi.single i 1)) k := by
    rw [resT_permS_dft_mulVec s t α hs0 ht0 hα0 (Pi.single i 1) k,
      permT_dft_resS_mulVec s t α hs0 ht0 hα0 (Pi.single i 1) k]
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hmul
  rw [Matrix.col_apply, Matrix.col_apply] at hmul
  exact hmul

end Work.ResMath
