import Mathlib
import Submission.NK.ResidueFrob.Inertia
import Submission.NK.FrobeniusBridge.Descent

/-!
# The level-wise triviality condition is monotone in the level

`NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g` says that `g : Gal(K'/K)` acts trivially on
the residue field `κ(P_L) = 𝓞 L / P_L` of the finite normal level `L` at the prime `P_L` of `𝓞 L`
below the place `A` of `K'`.

This file proves that the condition is **monotone**: if it holds at a level `N` then it holds at
every sublevel `L ≤ N`.

The mathematics is the transitivity of the contraction of primes together with the compatibility of
the Galois action on rings of integers along a tower.  Concretely, for `L ≤ N` the prime `P_L` is
the contraction of `P_N` (`NK.FrobeniusBridge.primeOfLevel_under`), and the residue map
`𝓞 L → 𝓞 N / P_N` factors through `𝓞 L / P_L`, so triviality of the action on the *larger* residue
field `𝓞 N / P_N` forces triviality on the quotient `𝓞 L / P_L`.  Formally, for `x : 𝓞 L`,

* `P_L = P_N ∩ 𝓞 L`, so `g x - x ∈ P_L` iff `g x - x ∈ P_N` once mapped into `𝓞 N`;
* the elements `g x` and `g (x ↦ 𝓞 N)` agree after base change
  (`NK.Chebotarev.algebraMap_galRestrict_restrictNormalHom_le`), because the restriction of `g`
  to `L` is the restriction to `L` of the restriction of `g` to `N`
  (`NK.Chebotarev.restrictNormalHom_le_comp`).

The result is the analogue, for the triviality condition, of
`NK.FrobeniusBridge.frobAtLevel_restrict`.
-/

namespace NK.ResidueFrob

set_option linter.style.haveILetI false

/-- **Monotonicity of the level-wise triviality condition**: an element of `Gal(K'/K)` acting
trivially on the residue field of the finite normal level `N` acts trivially on the residue field of
every finite normal sublevel `L ≤ N` at the same place `A`. -/
theorem isTrivialOnResidueAtLevel_of_le {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') {L N : IntermediateField K K'}
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [FiniteDimensional K N] [Normal K N] [NumberField ↥N] (hLN : L ≤ N) (h : Gal(K'/K))
    (hh : NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N h) :
    NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L h := by
  intro x
  -- the algebra structure of the tower `K ⊆ L ⊆ N` restricted to `K'`
  letI : Algebra ↥L ↥N := (Subsemiring.inclusion hLN).toAlgebra
  haveI : IsScalarTower K ↥L ↥N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥L ↥N K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the prime of the smaller level is the contraction of the prime of the larger one
  have hunder :
      (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)).asIdeal =
        (NK.Reconstruct.primeOfLevel A.1 N
          (NK.Reconstruct.comap_level_ne_top A.2 N)).asIdeal.under
          (NumberField.RingOfIntegers ↥L) := by
    rw [NK.FrobeniusBridge.primeOfLevel_under hLN A]
    rfl
  -- the action on `𝓞 L` is the action on `𝓞 N` after base change
  have key : (algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥N))
        ((galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
          ((AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥N) ↥L)
            (AlgEquiv.restrictNormalHom N h))) x)
      = (galRestrict (NumberField.RingOfIntegers K) K ↥N (NumberField.RingOfIntegers ↥N)
          (AlgEquiv.restrictNormalHom N h))
        ((algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥N)) x) :=
    NK.Chebotarev.algebraMap_galRestrict_restrictNormalHom_le L N hLN
      (AlgEquiv.restrictNormalHom N h) x
  -- restriction to `L` is restriction to `N` followed by restriction to `L`
  have hcomp := NK.Chebotarev.restrictNormalHom_le_comp L N hLN h
  rw [hunder, Ideal.mem_under]
  rw [map_sub]
  rw [hcomp]
  rw [key]
  exact hh ((algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥N)) x)

end NK.ResidueFrob
