import Mathlib
import Submission.NK.GFC.fundamentalClassElement_of_cyclotomicTower
import Submission.NK.GFC.normImage_of_auxiliary_cyclotomic

namespace NK.GFC

theorem fundamentalClassElement_unconditional : NK.GlobalCFTdeep.FundamentalClassElement :=
  fundamentalClassElement_of_cyclotomicTower NK.CFTLib.primePowerReciprocity
    normImage_of_auxiliary_cyclotomic

end NK.GFC
