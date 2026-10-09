import Mathlib
import Submission.NK.GlobalCFT.Norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Norm

theorem globalCFT_normIdeleFun_mul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (x y : NK.GlobalCFT.Idele L)
    (v : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Idele.normIdeleFun K L (x * y) v =
      NK.GlobalCFT.Idele.normIdeleFun K L x v * NK.GlobalCFT.Idele.normIdeleFun K L y v := by
  rcases v with w | q <;>
    simp [NK.GlobalCFT.Idele.normIdeleFun_ofInfinite,
      NK.GlobalCFT.Idele.normIdeleFun_ofFinite, Finset.prod_mul_distrib]

end NK.GlobalCFT.Norm
