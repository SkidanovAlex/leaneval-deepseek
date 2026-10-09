import Submission.Work.SSGRoute.E1aClean.BaseChangeInstances
import Submission.Work.SSGRoute.ExtChain.e1c_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The `E1c` dictionary at the *base-changed* field data

`e1cMap` (`ExtChain/e1c_natural.lean`, field-generic in `(k, Ω, K)`) is a map

  `Ext¹_G(R, Kˣ) →+ H¹(Gal(Ω/k), Hom_ℤ(R, Ωˣ))`,  `G = Gal(K/k)`,

so instantiating it at the *base field* `↥L` for an intermediate field `L : IntermediateField k K`
— with the *same* big field `Ω` and the *same* top field `K`, re-read over `↥L` as `Kover L`
(`E1aClean/BaseChangeInstances.lean`) — gives

  `Ext¹_{Gal(K/L)}(R, Kˣ) →+ H¹(Gal(Ω/L), Hom_ℤ(R, Ωˣ))`,

i.e. the dictionary over the subgroup `Gal(K/L) ≤ Gal(K/k)` with the *absolute* group `Gal(Ω/L)`
on the cohomology side.  This is the object of the (P1) level-change naturality.

The instances of the field-generic chapter which `inferInstance` does not find are supplied:
`NumberField ↥L` (`of_module_finite` from `NumberField k` and `FiniteDimensional k K`) and
`IsAlgClosure ↥L Ω` (`isAlgClosure_Kover`); the three Galois-theoretic ones
(`FiniteDimensional ↥L (Kover L)`, `IsGalois ↥L (Kover L)`, `NumberField (Kover L)`) are
hypotheses here — for `L = K^D` they are the Galois correspondence. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- **The `E1c` dictionary over the base-changed field data `(↥L, Ω, K)`.** -/
noncomputable def e1cMap_baseChanged (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (Kover L ≃ₐ[↥L] Kover L)) [Module.Finite ℤ R.V] :
    Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK ↥L (Kover L)) 1 →+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥L] Ω) (Work.SSGRoute.homCoind ↥L Ω (Kover L) R) := by
  haveI : NumberField ↥L := NumberField.of_module_finite (K := k) (L := ↥L)
  exact Work.SSGRoute.ExtChain.e1cMap (k := ↥L) (Ω := Ω) (K := Kover L) R

/-- The same, as the additive equivalence `Ext¹ ≃+ H¹` (the dictionary proper). -/
noncomputable def e1cEquiv_baseChanged (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (Kover L ≃ₐ[↥L] Kover L)) [Module.Finite ℤ R.V] :
    Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK ↥L (Kover L)) 1 ≃+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥L] Ω) (Work.SSGRoute.homCoind ↥L Ω (Kover L) R) := by
  haveI : NumberField ↥L := NumberField.of_module_finite (K := k) (L := ↥L)
  exact Work.SSGRoute.ExtChain.e1cEquiv (k := ↥L) (Ω := Ω) (K := Kover L) R

end

end Work.SSGRoute.E1aClean
