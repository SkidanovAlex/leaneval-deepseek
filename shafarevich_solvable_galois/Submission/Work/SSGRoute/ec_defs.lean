import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.HassePrinciple.IdeleLevel
import Submission.NK.HassePrinciple.OrbitCoindSection
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the idèle class-group lifting (`exists_classLoc_lift_ptorsion`)

Thin wrappers around `NK.HassePrinciple`'s orbit-supported idèles, used to state the helper lemmas
of `Work.SSGRoute.exists_classLoc_lift_ptorsion` without dragging the `NK` namespace into the
signature.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **The idèles supported on the `Gal(L/k)`-orbit of `w₀`**, as a representation of
`Gal(L/k)`: those idèles all of whose components outside the orbit are `1`. -/
noncomputable abbrev orbitSupportedRep (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) : Rep.{0} Coeff (L ≃ₐ[k] L) :=
  NK.HassePrinciple.supportedRep k L (NK.HassePrinciple.orbitStable k L w₀)

/-- **The orbit-supported inclusion of the idèles, with a left inverse.**

`H : orbitSupportedRep k L w₀ ⟶ 𝕀_L` is the inclusion of the idèles supported on the
`Gal(L/k)`-orbit of `w₀` into all idèles; `r` is a left inverse of `H`; and the localisation of
`H` at every place `v` outside the orbit of `w₀` is the zero morphism. -/
def HasOrbitSupportedInclusion (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (w₀ : NK.GlobalCFT.Place L) : Prop :=
  ∃ H : orbitSupportedRep k L w₀ ⟶ idelesK k L,
    (∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ v) →
      Rep.resMap (decompK (k := k) v).subtype H ≫
        NK.HassePrinciple.ideleToLocalUnits k L v = 0) ∧
    ∃ r : idelesK k L ⟶ orbitSupportedRep k L w₀, H ≫ r = 𝟙 (orbitSupportedRep k L w₀)

/-- **The order of the second `Ext`-cohomology of the orbit-supported idèles** equals the order of
the decomposition group: for a **finite** place `ŵ₀` of `L`,
`|H²(Gal(L/k), orbitSupportedRep k L (Place.ofFinite ŵ₀))| = |D_{ŵ₀}|`. -/
def CardOrbitSupportedRep (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (ŵ₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) : Prop :=
  Nat.card (extH (orbitSupportedRep k L (NK.GlobalCFT.Place.ofFinite ŵ₀)) 2)
    = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite ŵ₀))

end Work.SSGRoute
