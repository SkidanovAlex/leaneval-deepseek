import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.LinearAlgebra.FiniteDim

theorem finrank_comap_of_linearEquiv {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (e : V ≃ₗ[K] V')
    (W : Submodule K V') :
    Module.finrank K ↥(W.comap (e : V →ₗ[K] V')) = Module.finrank K ↥W := by
  exact (e.ofSubmodule' W).finrank_eq

end Commons.LinearAlgebra.FiniteDim