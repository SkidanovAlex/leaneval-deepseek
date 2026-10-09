/-
# Ray-class Čebotarev (existence form)

`Work.SSGRoute.rayClass_chebotarev_v2`: for an open finite-index subgroup `V` of the idèle class
group `C_K` of a number field `K`, every class of `C_K ⧸ V` is the class of a prime ideal `𝔮`
outside any prescribed finite set.  Equivalently (class field theory): the image of a class field
`M` of `V` under the idèlic Artin map is surjective on the primes.

The proof is the standard one:

* `classField_exists_of_index` produces an abstract finite Galois extension `L/K` with
  `N_{L/K} C_L = V`; passing to the abelian subextension
  (`exists_abelian_subextension_normClassSubgroup_le`) and then to the intermediate field with
  exactly the norm subgroup `V` (`exists_intermediateField_normClassSubgroup_eq_of_index`) gives an
  *abelian* `M/K` with `N_{M/K} C_M = V`;
* the idèlic Artin map of `M/K` with its Frobenius normalisation is supplied by
  `NK.CFTLib.Existence.exists_ideleArtinMap_of_arl` (from the proved ideal-theoretic reciprocity
  law), and `exists_artinIso_of_ideleArtin` turns it into an isomorphism
  `C_K ⧸ N_{M/K}C_M ≃* Gal(M/K)` whose *values* on idèles are the Artin map;
* Čebotarev's density theorem (`Work.SSGRoute.chebotarev_density_general`, proved from the Hecke
  input and the proved reciprocity law) gives a prime outside any finite bad set at which the
  prescribed element is a Frobenius element; avoiding the primes dividing `(m)` makes the Artin map
  at that prime the Frobenius, and the two descriptions of the prescribed element are equal.
-/
import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.CFTLib.Existence.artinMapOfARL
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
import Submission.Work.SSGRoute.CFTSide.exists_intermediateField_normClassSubgroup_eq_of_index
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.finiteIndex_gesU
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open NumberField IsDedekindDomain
open NK.GlobalCFT (Idele IdeleClassGroup)

open scoped Pointwise

/-! ## Čebotarev in existence form, abstractly -/

/-- **Čebotarev, existence form, for an abstract finite Galois extension of number fields.**  For
every finite set `Bad` of primes of `k` and every `g : Gal(N/k)` there is a prime of `k` outside
`Bad` at which `g` is a Frobenius element. -/
theorem exists_isFrobAtPrime_notMem_abstract {k N : Type} [Field k] [NumberField k] [Field N]
    [NumberField N] [Algebra k N] [FiniteDimensional k N] [IsGalois k N]
    (Bad : Set (NK.Chebotarev.PrimeIdeal k)) (hBad : Bad.Finite) (g : Gal(N/k)) :
    ∃ p : NK.Chebotarev.PrimeIdeal k, p ∉ Bad ∧ NK.Chebotarev.IsFrobAtPrime p g := by
  classical
  have hdens : NumberField.Set.HasDirichletDensity
      (NK.ChebotarevGeneral.frobSet (K := k) (N := N) g)
      (NK.ChebotarevGeneral.frobDensity (K := k) (N := N) g) :=
    chebotarev_density_general k N g
  haveI : Nonempty ↥(Subgroup.centralizer ({g} : Set (Gal(N/k)))) := ⟨1, Subgroup.one_mem _⟩
  have hpos : 0 < NK.ChebotarevGeneral.frobDensity (K := k) (N := N) g := by
    rw [NK.ChebotarevGeneral.frobDensity]
    exact one_div_pos.mpr (by exact_mod_cast Nat.card_pos)
  by_contra hcon
  push_neg at hcon
  have hsub : NK.ChebotarevGeneral.frobSet (K := k) (N := N) g ⊆ Bad := by
    intro p hp
    by_contra hpBad
    exact hcon p hpBad hp
  have hzn : NumberField.Set.HasDirichletDensity
      (NK.ChebotarevGeneral.frobSet (K := k) (N := N) g) 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hBad) hsub
  rw [NumberField.Set.HasDirichletDensity] at hdens hzn
  exact absurd (tendsto_nhds_unique hdens hzn) hpos.ne'

/-! ## Ray-class Čebotarev, given a class field -/

/-- **Ray-class Čebotarev, conditional form.**  Let `M/K` be a finite *abelian* Galois extension of
number fields with norm class subgroup `N_{M/K} C_M = V`.  Then every class of `C_K ⧸ V` is the
class of a prime ideal outside any prescribed finite set of primes.

Nothing is assumed about ramification: the primes where the idèlic Artin map is not the Frobenius
map are the divisors of a single integer `m`, and Čebotarev is applied outside them. -/
theorem chebotarev_of_classField {K : Type} [Field K] [NumberField K]
    (M : Type) [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (hcomm : ∀ a b : Gal(M/K), a * b = b * a)
    (V : Subgroup (IdeleClassGroup K)) (hV : Idele.normClassSubgroup K M = V)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) (c : IdeleClassGroup K ⧸ V) :
    ∃ 𝔮 : NK.Chebotarev.PrimeIdeal K, 𝔮 ∉ T ∧
      QuotientGroup.mk' V (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮)) = c := by
  classical
  subst V
  haveI hMc : IsMulCommutative Gal(M/K) := IsMulCommutative.of_comm hcomm
  -- the idèlic Artin map with Frobenius normalisation
  obtain ⟨m, hm, art, hram, hprinc, hnorm, hfrob, hsurj⟩ :=
    NK.CFTLib.Existence.exists_ideleArtinMap_of_arl
      NK.CFTLib.artinReciprocityIdeal_proved (K := K) (L := M)
  have hker : Idele.principalSubgroup K ≤ art.ker := by
    rintro x ⟨a, rfl⟩
    exact MonoidHom.mem_ker.mpr (hprinc a)
  obtain ⟨e, he⟩ := NK.CFTLib.Existence.exists_artinIso_of_ideleArtin
    NK.CFTLib.fundamentalClassElement art hker hnorm hsurj
  -- the bad set: the primes dividing `(m)` and `T`
  have hm0 : (m : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast hm.ne'
  have hspan0 : Ideal.span {(m : NumberField.RingOfIntegers K)} ≠ 0 := by
    rw [Ne]
    intro h
    exact hm0 (Ideal.span_singleton_eq_bot.mp h)
  have hfin1 : ({𝔭 : NK.Chebotarev.PrimeIdeal K |
      (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal} : Set _).Finite := by
    refine (Ideal.finite_factors (R := NumberField.RingOfIntegers K) (I :=
      Ideal.span {(m : NumberField.RingOfIntegers K)}) hspan0).subset ?_
    intro 𝔭 h𝔭
    show 𝔭.asIdeal ∣ Ideal.span {(m : NumberField.RingOfIntegers K)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h𝔭
  have hBadfin : ({𝔭 : NK.Chebotarev.PrimeIdeal K |
      (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal} ∪ (T : Set _)).Finite :=
    hfin1.union T.finite_toSet
  obtain ⟨𝔮, h𝔮Bad, h𝔮Frob⟩ :=
    exists_isFrobAtPrime_notMem_abstract
      ({𝔭 : NK.Chebotarev.PrimeIdeal K |
        (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal} ∪ (T : Set _)) hBadfin (e c)
  have h𝔮T : 𝔮 ∉ T := fun h => h𝔮Bad (Or.inr h)
  have h𝔮m : (m : NumberField.RingOfIntegers K) ∉ 𝔮.asIdeal := fun h => h𝔮Bad (Or.inl h)
  refine ⟨𝔮, h𝔮T, ?_⟩
  refine e.injective ?_
  rw [he (NK.HeckeL.ideleOfPrime K 𝔮), hfrob 𝔮 h𝔮m]
  exact (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔮 (hram 𝔮 h𝔮m) (e c)).mp h𝔮Frob

/-! ## Ray-class Čebotarev, unconditionally -/

/-- **Ray-class Čebotarev.**  For an open finite-index subgroup `V` of the idèle class group `C_K`
of a number field `K`, every class of `C_K ⧸ V` is the class of a prime ideal `𝔮` outside any
prescribed finite set of primes. -/
theorem rayClass_chebotarev_v2 {K : Type} [Field K] [NumberField K]
    (V : Subgroup (IdeleClassGroup K)) (hVfin : V.FiniteIndex)
    (hVopen : IsOpen (V : Set (IdeleClassGroup K)))
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) (c : IdeleClassGroup K ⧸ V) :
    ∃ 𝔮 : NK.Chebotarev.PrimeIdeal K, 𝔮 ∉ T ∧
      QuotientGroup.mk' V (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮)) = c := by
  classical
  have hidxpos : 0 < V.index := Nat.pos_of_ne_zero (Subgroup.finiteIndex_iff.mp hVfin)
  obtain ⟨L, hFL, hNL, hAL, hfdL, hGalL, hNormL, _⟩ :=
    Work.SSGRoute.CFTSide.classField_exists_of_index (K := K) V.index hidxpos V hVfin hVopen rfl
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra K L := hAL
  letI : FiniteDimensional K L := hfdL
  haveI : IsGalois K L := hGalL
  obtain ⟨A, hAgal, hAcomm, hAle⟩ :=
    Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
      NK.CFTLib.fundamentalClassElement (K := K) (L := L) V (le_of_eq hNormL)
  haveI : IsGalois K ↥A := hAgal
  haveI : IsMulCommutative (↥A ≃ₐ[K] ↥A) := hAcomm
  haveI : NumberField ↥A := NumberField.of_module_finite K ↥A
  obtain ⟨E, hEgal, hEnorm, _⟩ :=
    NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index
      NK.CFTLib.artinReciprocityIdeal_proved NK.CFTLib.fundamentalClassElement
      (K := K) (L := ↥A) V hAle
  haveI : IsGalois K ↥E := hEgal
  haveI : NumberField ↥E := NumberField.of_module_finite K ↥E
  have hcommE : ∀ a b : ↥E ≃ₐ[K] ↥E, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) (E := ↥A) a
    obtain ⟨y, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) (E := ↥A) b
    rw [← map_mul, ← map_mul, mul_comm' x y]
  exact chebotarev_of_classField (K := K) ↥E hcommE V hEnorm T c

end Work.SSGRoute
