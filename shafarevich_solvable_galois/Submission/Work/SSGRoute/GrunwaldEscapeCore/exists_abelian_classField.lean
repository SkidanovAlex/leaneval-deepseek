import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.TopologySetup
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
import Submission.Work.SSGRoute.CFTSide.exists_intermediateField_normClassSubgroup_eq_of_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.GrunwaldEscapeCore

set_option linter.style.haveILetI false

open NK.GlobalCFT

/-- **Global class field theory existence, in the abelian extension form used by the Čebotarev
input**: every open subgroup `V` of finite index of the idèle class group `C_K` of a number field
`K` is the norm class subgroup `N_{L/K} C_L` of a *finite abelian* extension `L / K`.

The route is the one already carried out in `Submission/Work/SSGRoute/CycLevel/levelData_of_localGroup.lean`:

* `Work.SSGRoute.CFTSide.classField_exists_of_index` produces `L / K` Galois with
  `N_{L/K}C_L = V` (the Galois group is *not* recorded as commutative there);
* `Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le` (with
  `NK.CFTLib.fundamentalClassElement`) produces the maximal abelian subextension `A ≤ L` with
  `N_{A/K}C_A ≤ V` and `IsMulCommutative Gal(A/K)`;
* `NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index` (with
  `NK.CFTLib.artinReciprocityIdeal_proved` and `NK.CFTLib.fundamentalClassElement`) applied to the
  abelian extension `A / K` produces `E ≤ A` with `IsGalois K E` and `N_{E/K}C_E = V`.

The commutativity of `Gal(E/K)` follows because `E ≤ A` and `Gal(A/K)` is commutative
(`AlgEquiv.restrictNormalHom_surjective`); the instance transport is exactly as in
`levelData_of_localGroup`. -/
theorem exists_abelian_classField {K : Type} [Field K] [NumberField K]
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)) (hfin : V.FiniteIndex)
    (hopen : IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K))) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      IsGalois K L ∧ IsMulCommutative (L ≃ₐ[K] L) ∧
        NK.GlobalCFT.Idele.normClassSubgroup K L = V := by
  -- the index of `V` is positive, so the existence theorem applies to it
  have hVne : V.index ≠ 0 := Subgroup.finiteIndex_iff.mp hfin
  -- ## Step 1: a finite Galois extension `L / K` with `N_{L/K}C_L = V`
  obtain ⟨L, hFL, hNL, hAL, hfdL, _hGalL, hNormL, _hdegL⟩ :=
    Work.SSGRoute.CFTSide.classField_exists_of_index (K := K) V.index
      (Nat.pos_of_ne_zero hVne) V hfin hopen rfl
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra K L := hAL
  letI : FiniteDimensional K L := hfdL
  -- ## Step 2: the maximal abelian subextension `A ≤ L`
  obtain ⟨A, hAgal, hAcomm, hAle⟩ :=
    Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
      NK.CFTLib.fundamentalClassElement (K := K) (L := L) V (le_of_eq hNormL)
  haveI : IsGalois K ↥A := hAgal
  haveI : IsMulCommutative (↥A ≃ₐ[K] ↥A) := hAcomm
  -- ## Step 3: the norm-group correspondence for the abelian extension `A / K`
  obtain ⟨E, hEgal, hEnorm, _hEdeg⟩ :=
    NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index
      NK.CFTLib.artinReciprocityIdeal_proved NK.CFTLib.fundamentalClassElement
      (K := K) (L := ↥A) V hAle
  haveI : IsGalois K ↥E := hEgal
  -- ## `Gal(E/K)` is commutative, being a quotient of the commutative `Gal(A/K)`
  have hcommE : ∀ a b : ↥E ≃ₐ[K] ↥E, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) (E := ↥A) a
    obtain ⟨y, rfl⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) (E := ↥A) b
    rw [← map_mul, ← map_mul, mul_comm' x y]
  exact ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance, hEgal,
    IsMulCommutative.of_comm hcommE, hEnorm⟩

end Work.SSGRoute.GrunwaldEscapeCore
