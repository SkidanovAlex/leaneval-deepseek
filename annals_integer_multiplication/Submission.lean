import ChallengeDeps
import Submission.Helpers
import Submission.HvdH.Wiring
import Submission.Work.Compiler.compilerThm
import Submission.Work.Kernel.kernelLib
import Submission.Work.IntLib.intLib
import Submission.Work.Layout.layoutLib
import Submission.Work.Fx.fxLib
import Submission.Work.DFT.dftMath
import Submission.Work.SynFFT.synFFT
import Submission.Work.ConvR.convR
import Submission.Work.Transform.transform
import Submission.Work.ResMath.resMath1D
import Submission.Work.Resample.resample
import Submission.Work.Params.params
import Submission.Work.Main.mainStep
import Submission.Work.Recursion.recursion
import Submission.Work.Assembly.assembly

open IntegerMultiplication
open Computability Turing Real

set_option autoImplicit false

namespace Submission

theorem theorem_1_1 :
    ∃ T : TM2ComputableInTime (encodeProd encodeNat encodeNat) encodeNat (fun (x, y) ↦ x * y),
      (fun n ↦ (T.time n : ℝ)) =O[Filter.atTop] (fun n ↦ n * log n) :=
  HvdH.wired Work.Compiler.compilerThm Work.Kernel.kernelLib Work.IntLib.intLib Work.Layout.layoutLib
    Work.Fx.fxLib Work.DFT.dftMath Work.SynFFT.synFFT Work.ConvR.convR Work.Transform.transform
    Work.ResMath.resMath1D Work.Resample.resample Work.Params.params Work.Main.mainStep
    Work.Recursion.recursion Work.Assembly.assembly

end Submission
