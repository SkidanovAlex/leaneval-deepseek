import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.DFT.dftDefs
import Submission.Work.DFT.phaseLin
import Submission.Work.DFT.expId
import Submission.Work.DFT.algebra
import Submission.Work.DFT.dftNorm
import Submission.Work.DFT.dftLinear
import Submission.Work.DFT.charSumSub
import Submission.Work.DFT.charSumConv

/-!
# Norm, linearity, inversion and convolution for the multidimensional DFT (paper §2.4).

This assembles `HvdH.DFTMathProp` from

* `dftNorm` / `dftLinear` — the sup-norm bound and the linearity of `HvdH.dftMulti`;
* `charSumSub` / `charSumConv` — the character-orthogonality relations for the mixed-radix
  character `charExp`;
* `inversion` / `convolution` — the DFT inversion and convolution theorems, proved from the
  orthogonality relations by expanding the double sums and exchanging the order of summation.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-- Norm, linearity, inversion and convolution facts for the multidimensional DFT (paper 2.4). -/
theorem dftMath : HvdH.DFTMathProp := by
  intro ts hpos
  exact ⟨dftNorm ts hpos, dftLinear ts,
    inversion ts hpos (charSumSub ts hpos),
    convolution ts hpos (charSumConv ts hpos)⟩

end Work.DFT
