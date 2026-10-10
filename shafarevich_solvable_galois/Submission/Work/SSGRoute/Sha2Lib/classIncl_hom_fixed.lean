import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.classIncl_isCanonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory Work.SSGRoute SSGRoute.PTExt

theorem classIncl_hom_fixed (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (a : classesK k K) (ha : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ a = a) :
    ∀ τ : L ≃ₐ[k] L, (classesK k L).ρ τ ((Rep.Hom.hom (classIncl k K L)) a)
      = (Rep.Hom.hom (classIncl k K L)) a := by
  intro τ
  -- `classIncl k K L` is a morphism in `Rep Coeff (L ≃ₐ[k] L)`, hence intertwines the
  -- `Gal(L/k)`-actions; on the source the action factors through `galRes k K L`.
  have h := Representation.IntertwiningMap.isIntertwining
    (Rep.res (galRes k K L) (classesK k K)).ρ (classesK k L).ρ
    (Rep.Hom.hom (classIncl k K L)) τ a
  rw [← h]
  exact congrArg _ (ha (galRes k K L τ))

end Work.SSGRoute.Sha2Lib
