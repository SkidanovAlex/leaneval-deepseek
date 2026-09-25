import Mathlib
import Submission.NK.GlobalCFT.Norm

namespace NK.GlobalCFT.Norm

open scoped NumberField RestrictedProduct

/-- The idèle norm `N_{L/K}` sends the identity idèle to the identity idèle: at each place of `K`
the componentwise product of local norms of `1` is a product of `1`'s. -/
theorem globalCFT_normIdeleFun_one {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (v : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Idele.normIdeleFun K L 1 v = 1 := by
  cases v with
  | inl w => simp [NK.GlobalCFT.Idele.normIdeleFun_ofInfinite]
  | inr q => simp [NK.GlobalCFT.Idele.normIdeleFun_ofFinite]

end NK.GlobalCFT.Norm
