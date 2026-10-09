import Mathlib
import Submission.NK.RankTheoryDeep.TowerArc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of the cyclotomic exponent map

`NK.RankTheoryDeep.expHom Ω N : Gal(ℚ(ζ_{towerMod N})/ℚ) →* (ZMod (towerMod N))ˣ` is the
cyclotomic exponent map, sending an automorphism `σ` of the `towerMod N`-th cyclotomic level to
the exponent `a` with `σ ζ = ζ ^ a` (`expHom_spec`). Equivalently it is `IsPrimitiveRoot.autToPow`
of the chosen primitive root `towerZetaL Ω N` of order `towerMod N`.

Here we prove that it is **surjective**, i.e. that the Galois group of the cyclotomic extension
`ℚ(ζ_m)/ℚ` is (via the exponent) all of `(ℤ/m)^×`. Both sides are finite of the same cardinality —
`IsCyclotomicExtension.autEquivPow` exhibits `Gal(ℚ(ζ_m)/ℚ) ≃* (ZMod m)ˣ` because the `m`-th
cyclotomic polynomial is irreducible over `ℚ` — so it suffices that `expHom` is injective, which is
`IsPrimitiveRoot.autToPow_injective` in a cyclotomic extension.
-/

-- the same local instance priority as in `TowerArc`, so that `Algebra ℚ ↥L` for an intermediate
-- field `L` is resolved by `IntermediateField.algebra'` and the types below match `expHom`'s.
attribute [local instance 10] DivisionRing.toRatAlgebra

set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep

open Polynomial

/-- **The cyclotomic exponent map is surjective.**

For `m = towerMod N` the exponent map
`Gal(ℚ(ζ_m)/ℚ) →* (ZMod m)ˣ`, `σ ↦ a` where `σ ζ = ζ ^ a`, is onto: every unit `a` modulo `m`
occurs. -/
theorem expHom_surjective (Ω : Type*) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (N : ℕ) : Function.Surjective (NK.RankTheoryDeep.expHom Ω N) := by
  haveI : NeZero (towerMod N) := ⟨towerMod_ne_zero N⟩
  -- `expHom` is `autToPow` of the chosen primitive `towerMod N`-th root of unity
  have hζ := towerZetaL_isPrimitiveRoot Ω N
  -- the level is a cyclotomic extension, so `autToPow` is injective on it
  haveI hcyc : IsCyclotomicExtension {towerMod N} ℚ ↥(cycLevel Ω N).L :=
    (towerZeta_isPrimitiveRoot Ω N).intermediateField_adjoin_isCyclotomicExtension ℚ
  have hinj : Function.Injective (expHom Ω N) := hζ.autToPow_injective ℚ
  -- and `Gal(ℚ(ζ_m)/ℚ) ≃* (ZMod m)ˣ`, so the domain and the codomain have the same cardinality
  have hirr : Irreducible (cyclotomic (towerMod N) ℚ) :=
    cyclotomic.irreducible_rat (towerMod_pos N)
  have e : Gal(↥(cycLevel Ω N).L/ℚ) ≃ (ZMod (towerMod N))ˣ :=
    (IsCyclotomicExtension.autEquivPow (K := ℚ) ↥(cycLevel Ω N).L hirr).toEquiv
  haveI : Finite Gal(↥(cycLevel Ω N).L/ℚ) := Finite.of_equiv _ e.symm
  exact (Finite.injective_iff_surjective_of_equiv e).mp hinj

end NK.RankTheoryDeep
