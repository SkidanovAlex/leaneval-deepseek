import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.NKRayClassImports
import Submission.Work.SSGRoute.GrunwaldEscapeCore.isOpen_congSubgroup
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_abelian_classField
import Submission.NK.CFTLib.Existence.artinMapOfARL
import Submission.NK.CFTLib.Existence.artinKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Čebotarev for the ray class group of a modulus: every ray class contains a prime

`Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass`: for every modulus `𝔪` of a number
field `K` and every class `c` of the ray class group `𝕀 K ⧸ (Kˣ · U(𝔪))` there is a prime ideal `𝔮`
with `𝔪.exps 𝔮 = 0` (i.e. `𝔮 ∤ 𝔪`) whose ray class is `c`.

This is Čebotarev's density theorem applied to the ray class field of the modulus, in existence
form.  The route of the proof is:

1. `U = U(𝔪)` is open in `𝕀 K`
   (`Work.SSGRoute.GrunwaldEscapeCore.isOpen_congSubgroup`) and `V = U·Kˣ/Kˣ ≤ C_K` is therefore
   open; `V` has finite index because the ray class group `𝕀 K ⧸ (Kˣ · U(𝔪))` is finite
   (`NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup`) and the canonical map
   `C_K ⧸ V →* 𝕀 K ⧸ (Kˣ · U)` is bijective;
2. `Work.SSGRoute.GrunwaldEscapeCore.exists_abelian_classField` gives a *finite abelian* extension
   `L / K` with `N_{L/K}C_L = V`;
3. the idèlic Artin map `art : 𝕀 K →* Gal(L/K)` of `L / K`
   (`NK.CFTLib.Existence.exists_ideleArtinMap_of_arl`, from the ideal-theoretic reciprocity law
   `NK.CFTLib.artinReciprocityIdeal_proved`) kills `Kˣ`, is surjective and sends the idèle of a
   prime `𝔭` outside a finite set `S` to `frobAtPrime 𝔭`;
4. Artin reciprocity (`NK.CFTLib.Existence.exists_artinIso_of_ideleArtin`, using the fundamental
   class `NK.CFTLib.fundamentalClassElement`) identifies `C_K ⧸ N_{L/K}C_L = C_K ⧸ V` with
   `Gal(L/K)`; composing with the canonical isomorphism `𝕀 K ⧸ (Kˣ · U) ≃* C_K ⧸ V` gives an
   isomorphism `Φ : 𝕀 K ⧸ (Kˣ · U) ≃* Gal(L/K)` which sends the ray class of an ideal `I` to
   `art (ideleOfIdeal K I)`;
5. Čebotarev (`NK.NUV2.abelianLFunctions_of_freeInputs` and
   `NK.Chebotarev.infinite_setOf_isFrobAtPrime_of_abelianLFunctions`) supplies, for the prescribed
   element `Φ c`, a prime `𝔮` outside `S ∪ support 𝔪` with `frobAtPrime 𝔮 = Φ c`; then
   `Φ (classOfIdeal K U 𝔮.asIdeal) = art (ideleOfPrime K 𝔮) = frobAtPrime 𝔮 = Φ c`, and the
   injectivity of `Φ` gives `classOfIdeal K U 𝔮.asIdeal = c`.
-/

set_option maxHeartbeats 1600000

open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative

namespace Work.SSGRoute.GrunwaldEscapeCore

open NK.GlobalCFT (Idele IdeleClassGroup)

/-- **Čebotarev with a finite set of primes avoided**, for an abelian extension `L / K` of number
fields: every element of `Gal(L/K)` is an arithmetic Frobenius element at a prime outside any
prescribed finite set of primes.

This is the analytic input `NK.NUV2.abelianLFunctions_of_freeInputs` (the Hecke `L`-series input
`NK.NUV2.heckeInput_proved` together with the reciprocity data
`NK.NUV2.artinFrobeniusInputFree_of_artinReciprocityIdeal`), turned into the qualitative statement
that the set of primes with a prescribed Frobenius element is infinite. -/
private theorem exists_isFrobAtPrime_notMem_finset {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (Bad : Finset (NK.Chebotarev.PrimeIdeal K)) (σ : Gal(L/K)) :
    ∃ 𝔭 ∉ Bad, NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ := by
  have hLF : NK.Chebotarev.AbelianLFunctions K L :=
    NK.NUV2.abelianLFunctions_of_freeInputs NK.NUV2.heckeInput_proved
      (NK.NUV2.artinFrobeniusInputFree_of_artinReciprocityIdeal
        NK.CFTLib.artinReciprocityIdeal_proved) K L hcomm
  obtain ⟨𝔭, hfrob, h𝔭⟩ :=
    (NK.Chebotarev.infinite_setOf_isFrobAtPrime_of_abelianLFunctions hcomm hLF σ)
      |>.exists_notMem_finset Bad
  exact ⟨𝔭, h𝔭, hfrob⟩

theorem exists_prime_mem_rayClass {K : Type} [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K)
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :
    ∃ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps 𝔮 = 0 ∧
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) 𝔮.asIdeal = c := by
  classical
  -- ## 1. The congruence subgroup, its image in `C_K`, and the canonical identification
  have hUopen : IsOpen (NK.NUV2.RouteB.CongSubgroup K 𝔪 : Set (Idele K)) :=
    isOpen_congSubgroup 𝔪
  set V : Subgroup (IdeleClassGroup K) :=
    (NK.NUV2.RouteB.CongSubgroup K 𝔪).map (IdeleClassGroup.mk K) with hV
  haveI hGfin : Finite (IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :=
    NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup K 𝔪
  have hker : (IdeleClassGroup.rayClassGroupMk K (NK.NUV2.RouteB.CongSubgroup K 𝔪)).ker = V := by
    rw [hV, IdeleClassGroup.ker_rayClassGroupMk]
  have hVle : V ≤ (IdeleClassGroup.rayClassGroupMk K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)).ker := le_of_eq hker.symm
  let Ψ : IdeleClassGroup K ⧸ V →*
      IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪) :=
    QuotientGroup.lift V (IdeleClassGroup.rayClassGroupMk K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) hVle
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨x, hx⟩ := IdeleClassGroup.rayClassGroupMk_surjective
      (NK.NUV2.RouteB.CongSubgroup K 𝔪) y
    exact ⟨QuotientGroup.mk x, by
      show QuotientGroup.lift V (IdeleClassGroup.rayClassGroupMk K
        (NK.NUV2.RouteB.CongSubgroup K 𝔪)) hVle (QuotientGroup.mk x) = y
      rw [QuotientGroup.lift_mk]; exact hx⟩
  have hΨker : Ψ.ker = ⊥ := by
    show (QuotientGroup.lift V (IdeleClassGroup.rayClassGroupMk K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) hVle).ker = ⊥
    rw [QuotientGroup.ker_lift, hker]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hΨinj : Function.Injective Ψ := (MonoidHom.ker_eq_bot_iff Ψ).mp hΨker
  haveI : Finite (IdeleClassGroup K ⧸ V) := Finite.of_injective Ψ hΨinj
  have hVfin : V.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  have hVopen : IsOpen (V : Set (IdeleClassGroup K)) := by
    refine Subgroup.isOpen_of_mem_nhds V (g := 1) ?_
    have h : ((QuotientGroup.mk ''
        ((NK.NUV2.RouteB.CongSubgroup K 𝔪 : Subgroup (Idele K)) : Set (Idele K))) :
        Set (Idele K ⧸ Idele.principalSubgroup K)) ∈
        nhds (1 : Idele K ⧸ Idele.principalSubgroup K) :=
      (QuotientGroup.isOpenMap_coe (N := Idele.principalSubgroup K) (G := Idele K)).image_mem_nhds
        (hUopen.mem_nhds (Subgroup.one_mem _))
    rw [hV, Subgroup.coe_map]
    exact h
  -- ## 2. The abelian class field `L` of `V`
  obtain ⟨L, hFL, hNL, hAL, hFDL, hGalL, hCommL, hNormL⟩ :=
    exists_abelian_classField (K := K) V hVfin hVopen
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra K L := hAL
  letI : FiniteDimensional K L := hFDL
  haveI : IsGalois K L := hGalL
  haveI : IsMulCommutative (L ≃ₐ[K] L) := hCommL
  have hcommL : ∀ a b : Gal(L/K), a * b = b * a := fun a b => mul_comm' a b
  -- ## 3. The idèlic Artin map of `L / K`
  obtain ⟨m, hm, art, hram, hprinc, hnorm, hfrob, hsurj⟩ :=
    NK.CFTLib.Existence.exists_ideleArtinMap_of_arl NK.CFTLib.artinReciprocityIdeal_proved
      (K := K) (L := L)
  have hAprinc : Idele.principalSubgroup K ≤ art.ker := by
    intro z hz
    obtain ⟨a, rfl⟩ := Idele.mem_principalSubgroup.mp hz
    exact MonoidHom.mem_ker.mpr (hprinc a)
  obtain ⟨e, he⟩ := NK.CFTLib.Existence.exists_artinIso_of_ideleArtin
    NK.CFTLib.fundamentalClassElement art hAprinc hnorm hsurj
  -- ## 4. The canonical isomorphism `𝕀 K ⧸ (Kˣ · U) ≃* C_K ⧸ N_{L/K}C_L`
  have hNle : Idele.normClassSubgroup K L ≤ (IdeleClassGroup.rayClassGroupMk K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)).ker := by
    rw [hker, ← hNormL]
  let Ψb : (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) →*
      IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪) :=
    QuotientGroup.lift (Idele.normClassSubgroup K L) (IdeleClassGroup.rayClassGroupMk K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) hNle
  have hΨbsurj : Function.Surjective Ψb := by
    intro y
    obtain ⟨x, hx⟩ := IdeleClassGroup.rayClassGroupMk_surjective
      (NK.NUV2.RouteB.CongSubgroup K 𝔪) y
    exact ⟨QuotientGroup.mk x, by
      show QuotientGroup.lift (Idele.normClassSubgroup K L) (IdeleClassGroup.rayClassGroupMk K
        (NK.NUV2.RouteB.CongSubgroup K 𝔪)) hNle (QuotientGroup.mk x) = y
      rw [QuotientGroup.lift_mk]; exact hx⟩
  have hΨbker : Ψb.ker = ⊥ := by
    show (QuotientGroup.lift (Idele.normClassSubgroup K L) (IdeleClassGroup.rayClassGroupMk K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) hNle).ker = ⊥
    rw [QuotientGroup.ker_lift, hker, ← hNormL]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hΨbinj : Function.Injective Ψb := (MonoidHom.ker_eq_bot_iff Ψb).mp hΨbker
  let Ψe : (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) ≃*
      IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪) :=
    MulEquiv.ofBijective Ψb ⟨hΨbinj, hΨbsurj⟩
  let Φ : IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪) ≃* Gal(L/K) :=
    Ψe.symm.trans e
  have hΦ_apply : ∀ g, Φ g = e (Ψe.symm g) := fun g => MulEquiv.trans_apply _ _ g
  -- the value of `Φ` on the ray class of an ideal
  have hΦclass : ∀ I : Ideal (𝓞 K),
      Φ (NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I) =
        art (NK.HeckeL.ideleOfIdeal K I) := by
    intro I
    have h1 : NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I =
        Ψb (QuotientGroup.mk (IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I))) := by
      show IdeleClassGroup.rayClassGroupMk K (NK.NUV2.RouteB.CongSubgroup K 𝔪)
          (IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I)) =
        Ψb (QuotientGroup.mk (IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I)))
      rw [show Ψb (QuotientGroup.mk (IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I))) =
          IdeleClassGroup.rayClassGroupMk K (NK.NUV2.RouteB.CongSubgroup K 𝔪)
            (IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I))
          from QuotientGroup.lift_mk _ _ _]
    rw [h1, hΦ_apply]
    have h2 : Ψe (QuotientGroup.mk (IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I))) =
        Ψb (QuotientGroup.mk (IdeleClassGroup.mk K (NK.HeckeL.ideleOfIdeal K I))) :=
      MulEquiv.ofBijective_apply Ψb ⟨hΨbinj, hΨbsurj⟩ _
    rw [← h2, MulEquiv.symm_apply_apply]
    exact he (NK.HeckeL.ideleOfIdeal K I)
  -- ## 5. Čebotarev: a prime with the prescribed Frobenius, outside `S ∪ support 𝔪`
  have hfinm : {𝔭 : NK.Chebotarev.PrimeIdeal K | (m : 𝓞 K) ∈ 𝔭.asIdeal}.Finite :=
    NK.CFTLib.ArtinReciprocityIdeal.finite_setOf_mem_span (K := K) m hm
  set Bad : Finset (NK.Chebotarev.PrimeIdeal K) := 𝔪.supportFinset ∪ hfinm.toFinset with hBaddef
  obtain ⟨𝔭, h𝔭bad, h𝔭frob⟩ := exists_isFrobAtPrime_notMem_finset hcommL Bad (Φ c)
  have h𝔭supp : 𝔭 ∉ 𝔪.supportFinset := fun h => h𝔭bad (Finset.mem_union_left _ h)
  have h𝔭m : (m : 𝓞 K) ∉ 𝔭.asIdeal := fun h =>
    h𝔭bad (Finset.mem_union_right _ (hfinm.mem_toFinset.mpr h))
  refine ⟨𝔭, NK.NUV2.RouteB.Modulus.exps_eq_zero_of_not_mem 𝔪 h𝔭supp, ?_⟩
  have hfrob𝔭 : NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 = Φ c :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommL 𝔭 (hram 𝔭 h𝔭m) (Φ c)).mp h𝔭frob
  have hfinal : Φ (NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) 𝔭.asIdeal) =
      Φ c := by
    rw [hΦclass 𝔭.asIdeal,
      NK.GlobalCFTdeep.SecondInequality.ideleOfIdeal_prime_eq_ideleOfPrime, hfrob 𝔭 h𝔭m,
      hfrob𝔭]
  exact Φ.injective hfinal

end Work.SSGRoute.GrunwaldEscapeCore
