/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.NormIndex.Defs
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage
import Submission.NK.GlobalCFTdeep.NormIndex.constrainedE_inf_TIdeles_index
import Submission.NK.GlobalCFTdeep.NormIndex.exists_good_S
import Submission.NK.GlobalCFTdeep.SecondInequality.secondInequality_of_isCyclic_prime_kummerCase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm index is finite for a finite **Galois** extension

The elementary proof that `[C_K : N_{L/K} C_L]` is finite for a finite Galois extension `L / K`
of number fields, with no class field theory:

* choose a finite set `S` of places of `K` containing the archimedean places, the places below all
  ramified primes of `L`, and a set of places whose idèles generate the class group
  (`exists_good_S`);
* choose a place `g v` of `L` above each place `v` of `K` (`exists_place_liesOver`);
* the local norm data `Φ v` (`exists_normAt_data`) gives, at each `v`, a homomorphism
  `L_{g v}ˣ →* K_vˣ` of finite index image which computes the idèlic norm and which is onto on
  units outside `S`;
* the subgroup `A v := (Φ v).range` therefore defines a subgroup `E = constrainedE S A ≤ N 𝕀_L`;
* the restricted-product computation `[𝕀_{K,S} : E ∩ 𝕀_{K,S}] = ∏_{v ∈ S} [K_vˣ : A v]` shows that
  `E ∩ 𝕀_{K,S}` has finite index in `𝕀_{K,S}`;
* since `⊤ = Kˣ · 𝕀_{K,S}`, the abstract group-theoretic step
  `finiteIndex_sup_of_sup_eq_top` gives that `Kˣ · E` has finite index in `𝕀_K`, hence so does
  `Kˣ · N_{L/K} 𝕀_L = N_{L/K} C_L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.NormIndex

open NK.GlobalCFT

/-- **The norm index is finite for a finite Galois extension.** -/
theorem index_ne_zero_of_isGalois {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (Idele.normClassSubgroup K L).index ≠ 0 := by
  obtain ⟨S, hSinf, hunr, htop⟩ := exists_good_S (K := K) (L := L)
  choose g hg using fun v => exists_place_liesOver (K := K) (L := L) v
  have hdata := exists_normAt_data (K := K) (L := L) S g hg hSinf hunr
  let Φ : (v : Place K) → (Place.localField L (g v))ˣ →* (Place.localField K v)ˣ :=
    fun v => Classical.choose (hdata v)
  have hbridge : ∀ (v : Place K) (u : (Place.localField L (g v))ˣ),
      Idele.normIdeleFun K L (SecondInequality.KummerCase.singleIdele (g v) u) v = Φ v u :=
    fun v u => (Classical.choose_spec (hdata v)).1 u
  have hfin : ∀ v : Place K, (Φ v).range.FiniteIndex :=
    fun v => (Classical.choose_spec (hdata v)).2.1
  have hunit : ∀ (v : Place K), v ∉ S → ∀ a ∈ Place.localUnits K v,
      ∃ u ∈ Place.localUnits L (g v), Φ v u = a :=
    fun v => (Classical.choose_spec (hdata v)).2.2
  let A : (v : S) → Subgroup ((Place.localField K v)ˣ) := fun v => (Φ v).range
  have hA_le : constrainedE S A ≤ Idele.normImage K L :=
    constrainedE_le_normImage S A g hg Φ hbridge (fun v => le_refl _) hunit
  have hidx : ((constrainedE S A ⊓ TIdeles (L := K) (S : Set (Place K))).subgroupOf
      (TIdeles (L := K) (S : Set (Place K)))).index = ∏ v : S, (A v).index :=
    constrainedE_inf_TIdeles_index S A
  have hBfin : ((TIdeles (L := K) (S : Set (Place K)) ⊓ constrainedE S A).subgroupOf
      (TIdeles (L := K) (S : Set (Place K)))).FiniteIndex := by
    rw [inf_comm, Subgroup.finiteIndex_iff, hidx]
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => Subgroup.finiteIndex_iff.mp (hfin v))
  have hsup : (Idele.principalSubgroup K ⊔ constrainedE S A).FiniteIndex :=
    finiteIndex_sup_of_sup_eq_top htop.symm hBfin
  haveI : (Idele.principalSubgroup K ⊔ constrainedE S A).FiniteIndex := hsup
  have hsup' : (Idele.principalSubgroup K ⊔ Idele.normImage K L).FiniteIndex :=
    Subgroup.finiteIndex_of_le (sup_le_sup_left hA_le _)
  rw [SecondInequality.index_normClassSubgroup_eq_index_sup_normImage]
  exact Subgroup.finiteIndex_iff.mp hsup'

end NK.GlobalCFTdeep.NormIndex
