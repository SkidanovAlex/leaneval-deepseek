import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

theorem galRes_autCongr_symm {k K A B : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field A] [NumberField A] [Field B] [NumberField B]
    [Algebra k K] [Algebra K A] [Algebra K B] [Algebra k A] [Algebra k B]
    [IsScalarTower k K A] [IsScalarTower k K B]
    [FiniteDimensional k A] [FiniteDimensional k B] [IsGalois k K] [IsGalois k A] [IsGalois k B]
    (e : A ≃ₐ[K] B) (σ : B ≃ₐ[k] B) :
    SSGRoute.PTExt.galRes k K A ((AlgEquiv.autCongr (e.restrictScalars k)).symm σ)
      = SSGRoute.PTExt.galRes k K B σ := by
  set e' : A ≃ₐ[k] B := e.restrictScalars k with he'
  -- `e'` is `K`-linear: it carries the copy of `K` inside `A` to the one inside `B`.
  have hAB : ∀ y : K, e' (algebraMap K A y) = algebraMap K B y := fun y => by
    rw [he', AlgEquiv.restrictScalars_apply]; exact e.commutes y
  have hBA : ∀ y : K, e'.symm (algebraMap K B y) = algebraMap K A y := fun y => by
    rw [← hAB y, AlgEquiv.symm_apply_apply]
  -- Both sides are restrictions to `K`; compare them after applying `algebraMap K A`.
  show ((AlgEquiv.autCongr e'.symm) σ).restrictNormal K = σ.restrictNormal K
  ext x
  apply (algebraMap K A).injective
  rw [AlgEquiv.restrictNormal_commutes]
  rw [← hBA (σ.restrictNormal K x)]
  rw [AlgEquiv.restrictNormal_commutes]
  rw [AlgEquiv.autCongr_apply, AlgEquiv.symm_symm, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  rw [hAB]

end Work.SSGRoute.Sha2Lib
