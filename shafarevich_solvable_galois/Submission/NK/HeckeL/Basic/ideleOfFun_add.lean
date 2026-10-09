import Mathlib
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain Filter
open NK.GlobalCFT

namespace NK.HeckeL.Basic

/-- `ideleOfFun` is additive in the exponent function: the idèle attached to `f + g` is the
product of the idèles attached to `f` and to `g`.  The two are equal as idèles because they agree
at every place: at an archimedean place both sides are `1`, and at a finite place `q` both sides
are the `q`-component `unifUnit K q ^ (f q) * unifUnit K q ^ (g q) = unifUnit K q ^ ((f + g) q)`
of the restricted product. -/
theorem ideleOfFun_add {K : Type*} [Field K] [NumberField K]
    (f g : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℤ)
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (hg : ∀ᶠ q in Filter.cofinite, g q = 0) :
    NK.GlobalCFT.IdeleClassGroup.ideleOfFun K f hf * NK.GlobalCFT.IdeleClassGroup.ideleOfFun K g hg =
      NK.GlobalCFT.IdeleClassGroup.ideleOfFun K (f + g)
        ((hf.and hg).mono fun q hq => by simp [Pi.add_apply, hq.1, hq.2]) := by
  apply NK.GlobalCFT.Idele.ext
  intro v
  cases v with
  | inl w =>
      rw [NK.GlobalCFT.Idele.mul_apply]
      show (1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) * 1 = 1
      rw [mul_one]
  | inr q =>
      rw [NK.GlobalCFT.Idele.mul_apply]
      show NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^ (f q) *
          NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^ (g q)
        = NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^ ((f + g) q)
      rw [Pi.add_apply, zpow_add]

end NK.HeckeL.Basic
