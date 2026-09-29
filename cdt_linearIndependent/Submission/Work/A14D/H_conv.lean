import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.H_conv_alt

open Complex Metric

namespace Work.A14D

/-- `Hfun a b c` is holomorphic on `ball 0 1` and solves `LZ = rhsZ b c` there (the
overconvergence of `H` under the absurd relation).  Immediate from `H_conv_alt`. -/
theorem H_conv (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) :
    DifferentiableOn ℂ (Hfun a b c) (ball 0 1) ∧
      ∀ z ∈ ball (0 : ℂ) 1, LZ (Hfun a b c) z = rhsZ b c z :=
  H_conv_alt a b c h

end Work.A14D
