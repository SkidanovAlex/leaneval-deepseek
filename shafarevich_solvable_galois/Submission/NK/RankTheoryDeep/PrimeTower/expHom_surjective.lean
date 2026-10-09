import Mathlib
import Submission.NK.RankTheoryDeep.PrimeTower.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of the cyclotomic exponent map, for an arbitrary prime `ℓ`

The ℓ = 2 analogue is `Submission/Work/RankTheoryDeep/expHom_surjective.lean`; the argument is
identical, with `towerMod N` replaced by `towerMod ℓ N`.

`expHom ℓ Ω N : Gal(ℚ(ζ_{towerMod ℓ N})/ℚ) →* (ZMod (towerMod ℓ N))ˣ` sends an automorphism `σ`
of the `N`-th cyclotomic level to the exponent `a` with `σ ζ = ζ ^ a` (`expHom_spec`). It is
surjective: the Galois group of `ℚ(ζ_m)/ℚ` is the full unit group `(ℤ/m)^×`. Both sides are finite
of the same cardinality — `IsCyclotomicExtension.autEquivPow` exhibits
`Gal(ℚ(ζ_m)/ℚ) ≃* (ZMod m)ˣ` since the `m`-th cyclotomic polynomial is irreducible over `ℚ` — so it
suffices that `expHom` is injective, which is `IsPrimitiveRoot.autToPow_injective` in a cyclotomic
extension.
-/

-- the same local instance priority as in `Defs`, so that `Algebra ℚ ↥L` for an intermediate field
-- `L` is resolved by `IntermediateField.algebra'` and the types below match `expHom`'s.
attribute [local instance 10] DivisionRing.toRatAlgebra

set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep.PrimeTower

open Polynomial

-- expHom ℓ Ω N : Gal(↥(cycLevel ℓ Ω N).L/ℚ) →* (ZMod (towerMod ℓ N))ˣ is the cyclotomic exponent map (IsPrimitiveRoot.autToPow of the chosen primitive root), defined in Submission/Work/RankTheoryDeep/PrimeTower/Defs.lean; the ℓ = 2 analogue is Submission/Work/RankTheoryDeep/expHom_surjective.lean
theorem expHom_surjective (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] (N : ℕ) :
    Function.Surjective (expHom ℓ Ω N) := by
  haveI : NeZero (towerMod ℓ N) := ⟨towerMod_ne_zero ℓ N⟩
  -- `expHom` is `autToPow` of the chosen primitive `towerMod ℓ N`-th root of unity
  have hζ := towerZetaL_isPrimitiveRoot ℓ Ω N
  -- the level is a cyclotomic extension, so `autToPow` is injective on it
  haveI hcyc : IsCyclotomicExtension {towerMod ℓ N} ℚ ↥(cycLevel ℓ Ω N).L :=
    (towerZeta_isPrimitiveRoot ℓ Ω N).intermediateField_adjoin_isCyclotomicExtension ℚ
  have hinj : Function.Injective (expHom ℓ Ω N) := hζ.autToPow_injective ℚ
  -- and `Gal(ℚ(ζ_m)/ℚ) ≃* (ZMod m)ˣ`, so the domain and the codomain have the same cardinality
  have hirr : Irreducible (cyclotomic (towerMod ℓ N) ℚ) :=
    cyclotomic.irreducible_rat (towerMod_pos ℓ N)
  have e : Gal(↥(cycLevel ℓ Ω N).L/ℚ) ≃ (ZMod (towerMod ℓ N))ˣ :=
    (IsCyclotomicExtension.autEquivPow (K := ℚ) ↥(cycLevel ℓ Ω N).L hirr).toEquiv
  haveI : Finite Gal(↥(cycLevel ℓ Ω N).L/ℚ) := Finite.of_equiv _ e.symm
  exact (Finite.injective_iff_surjective_of_equiv e).mp hinj

end NK.RankTheoryDeep.PrimeTower
