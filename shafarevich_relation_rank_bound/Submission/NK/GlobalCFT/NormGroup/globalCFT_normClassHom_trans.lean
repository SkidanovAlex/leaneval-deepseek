import Mathlib
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans

namespace NK.GlobalCFT.NormGroup

/-- **Transitivity of the norm on idèle class groups.**  For a tower `M / L / K` of number
fields the norm `N_{L/K} : C_L →* C_K` on idèle class groups is compatible with composition:
`N_{L/K} (N_{M/L} q) = N_{M/K} q` for all `q : C_M`.

This is the idèle class group shadow of the transitivity of the idèlic norm
`NK.GlobalCFT.Idele.normIdeleHom`: both sides are computed on the representative
`x : 𝕀 M` of `q`. -/
theorem globalCFT_normClassHom_trans {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M]
    [FiniteDimensional K M] (q : C[M]) :
    IdeleClassGroup.normClassHom K L (IdeleClassGroup.normClassHom L M q) =
      IdeleClassGroup.normClassHom K M q := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective M q
  rw [IdeleClassGroup.normClassHom_mk, IdeleClassGroup.normClassHom_mk,
    IdeleClassGroup.normClassHom_mk]
  exact congrArg (IdeleClassGroup.mk K)
    (DFunLike.congr_fun (Norm.globalCFT_normIdeleHom_trans (K := K) (L := L) (M := M)) x)

end NK.GlobalCFT.NormGroup
