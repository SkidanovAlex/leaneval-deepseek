import Mathlib
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.finiteIndex_localUnits_ellPow
import Submission.Work.SSGRoute.finiteIndex_integralIdeles_powTIdeles
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finite index of `U = im(Kˣ · E)` in the idèle class group

This module proves `Work.SSGRoute.finiteIndex_gesU`: the subgroup

  `U = im(P · E) ≤ C_K`,  `P = Kˣ` (principal idèles),  `E = powTIdeles K p T`,

is of finite index in `C_K`.  Together with `Work.SSGRoute.isOpen_gesU` this is the pair
`U.FiniteIndex ∧ IsOpen U` consumed by `CFTSide.classField_exists_of_index` in the
escape-form Grünwald route (see `NOTE_ges_zmod_escape_route.md`, §3ter/§3quater/§3quinquies).

## The argument

Let `𝕀 = 𝕀_K`, `J = integralIdeles K` (local units at all finite places), `P = Kˣ` and `E` as
above.  Two finite-index inputs and one lattice computation suffice.

* **`J` up to `P` has finite index in `𝕀`.**  The ideal class map `𝕀 → Cl(K)` is surjective with
  kernel `P ⊔ J` (`ker_idealClassMap`), and `Cl(K)` is finite, so `(P ⊔ J).FiniteIndex`
  (`finiteIndex_principal_sup_integralIdeles`).

* **`E ⊓ J` has finite index in `J`.**  For an idèle which is a local unit at every finite place
  the only thing that `E` additionally imposes is that the components at the primes of `T` are
  `p`-th powers.  Hence `J/(J ⊓ E) ≅ ∏_{𝔭 ∈ T} O_𝔭ˣ ⧸ (O_𝔭ˣ)ᵖ`, a finite product of finite
  groups (each local factor is finite by `finiteIndex_localUnits_ellPow`); this is the delegated
  lemma `finiteIndex_integralIdeles_powTIdeles`, whose statement takes the local finiteness as an
  explicit hypothesis.

* **Lattice computation.**  Put `U = P ⊔ E` and `A = U ⊔ J`.  Since `P ⊔ J ≤ A` we get
  `A.FiniteIndex` (`Subgroup.finiteIndex_of_le`).  Since `E ⊓ J ≤ U ⊓ J` and `U ⊓ J` has finite
  index in `J` (a quotient of `J/(J ⊓ E)`), we get `U.relIndex J ≠ 0`.  Noether's second
  isomorphism theorem in the form `Subgroup.relIndex_sup_right` (`U.relIndex (J ⊔ U) = U.relIndex J`,
  valid because `𝕀` is abelian) then gives `U.relIndex A ≠ 0`, and `Subgroup.relIndex_ne_zero_trans`
  combines the two relative indices into `U.FiniteIndex`.

* Finally `U` contains `ker (mk K) = P`, so `Subgroup.index_map_eq` transports the finite index
  along the quotient map `𝕀 → C_K`.

-/

open scoped NumberField RestrictedProduct

set_option linter.style.haveILetI false

namespace Work.SSGRoute

variable {K : Type*} [Field K] [NumberField K]

/-- **The idèles which are local units at every finite place, together with the principal idèles,
generate a finite-index subgroup of `𝕀_K`.**

The ideal class map `𝕀_K → Cl(K)` has kernel `integralIdeles K ⊔ principalSubgroup K` and its
target `Cl(K)` is finite. -/
theorem finiteIndex_principal_sup_integralIdeles (K : Type*) [Field K] [NumberField K] :
    (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFT.Idele.integralIdeles K).FiniteIndex := by
  rw [sup_comm, ← NK.GlobalCFT.IdeleClassGroup.ker_idealClassMap K]
  exact Subgroup.finiteIndex_ker _

/-- A subgroup `U` has finite index in `G` as soon as it has finite index in some `A ≤ G` of
finite index in `G` (multiplicativity of the index, `Subgroup.relIndex_mul_index`). -/
theorem finiteIndex_of_relIndex_ne_zero {G : Type*} [Group G] {U A : Subgroup G}
    (hUA : U.relIndex A ≠ 0) (hA : A.FiniteIndex) : U.FiniteIndex := by
  have hA' : A.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.finiteIndex_iff.mp hA
  have h := Subgroup.relIndex_ne_zero_trans hUA hA'
  rw [Subgroup.relIndex_top_right] at h
  exact Subgroup.finiteIndex_iff.mpr h

theorem finiteIndex_gesU (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    ((NK.GlobalCFT.Idele.principalSubgroup K ⊔ Work.SSGRoute.powTIdeles K p T).map
      (NK.GlobalCFT.IdeleClassGroup.mk K)).FiniteIndex := by
  set P : Subgroup (NK.GlobalCFT.Idele K) := NK.GlobalCFT.Idele.principalSubgroup K with hP
  set J : Subgroup (NK.GlobalCFT.Idele K) := NK.GlobalCFT.Idele.integralIdeles K with hJ
  set E : Subgroup (NK.GlobalCFT.Idele K) := Work.SSGRoute.powTIdeles K p T with hE
  set U : Subgroup (NK.GlobalCFT.Idele K) := P ⊔ E with hUdef
  -- `P ⊔ J` has finite index in `𝕀_K` (kernel of the ideal class map)
  have hPJ : (P ⊔ J).FiniteIndex := by
    rw [hP, hJ]
    exact finiteIndex_principal_sup_integralIdeles K
  -- `E ⊓ J` has finite index in `J` (the local `p`-th power conditions)
  have hEJ : (E ⊓ J).relIndex J ≠ 0 := by
    rw [hE, hJ]
    exact finiteIndex_integralIdeles_powTIdeles K p T
      (fun 𝔭 => finiteIndex_localUnits_ellPow K 𝔭.1 p)
  -- hence `E ⊓ J ≤ U ⊓ J` also has finite index in `J`
  have hUJ : U.relIndex J ≠ 0 := by
    have hle : (E ⊓ J).subgroupOf J ≤ U.subgroupOf J :=
      Subgroup.subgroupOf_mono J (le_trans inf_le_left (by rw [hUdef]; exact le_sup_right))
    haveI : ((E ⊓ J).subgroupOf J).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by simpa only [Subgroup.relIndex] using hEJ)
    exact Subgroup.finiteIndex_iff.mp (Subgroup.finiteIndex_of_le hle)
  -- Noether's second isomorphism theorem: `U` has finite index in `U ⊔ J`
  have hUA : U.relIndex (U ⊔ J) ≠ 0 := by
    rw [sup_comm, Subgroup.relIndex_sup_right]
    exact hUJ
  -- `U ⊔ J` contains `P ⊔ J`, so it has finite index in `𝕀_K` as well
  have hA : (U ⊔ J).FiniteIndex := by
    haveI := hPJ
    refine Subgroup.finiteIndex_of_le (H := P ⊔ J) ?_
    rw [hUdef]
    exact sup_le_sup le_sup_left le_rfl
  have hU : U.FiniteIndex := finiteIndex_of_relIndex_ne_zero hUA hA
  -- the principal idèles lie in the kernel of `𝕀_K → C_K`, so `U` maps onto its image
  have hker : (NK.GlobalCFT.IdeleClassGroup.mk K).ker ≤ U := by
    rw [hUdef, ker_mk_eq_principal, ← hP]
    exact le_sup_left
  refine Subgroup.finiteIndex_iff.mpr ?_
  rw [Subgroup.index_map_eq U (NK.GlobalCFT.IdeleClassGroup.mk_surjective K) hker]
  exact Subgroup.finiteIndex_iff.mp hU

end Work.SSGRoute
