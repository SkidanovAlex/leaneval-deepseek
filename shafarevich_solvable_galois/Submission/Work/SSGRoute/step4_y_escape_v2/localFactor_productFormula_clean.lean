import Mathlib
import Submission.Work.SSGRoute.step4_y_escape_v2.ChebotarevSplit
import Submission.Work.SSGRoute.step4_y_escape_v2.RayClass
import Submission.Work.SSGRoute.ZDataMup.LTRecFamCrux.ideleArtin_ideleOfPrime_of_unramified
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Artin factors of an abelian extension, with the product formula

For a finite **abelian** extension `F / K` of number fields we construct the family of local Artin
maps `θ_v : K_vˣ →* Gal(F/K)` and verify the three properties the Step-4 escape consumes:

* `ker θ_v = N_v` (Milne, *CFT*, V.5.3(a): local faithfulness at one place);
* `θ_Q (unif_Q) = Frob_Q` at **every** unramified prime `Q` (the conductor drop, i.e. Milne
  VII.8.1(a) in the sharp form: the reciprocity law may be taken with a modulus supported on the
  ramified primes);
* the product formula: `∏_{v ∈ s} θ_v(x_v) = 1` for `x ∈ Kˣ` and any finite set `s` off which the
  local factors of `x` are trivial.

## The construction

The family is `θ_v := Φ ∘ onePlace_v`, where `onePlace_v` embeds `K_vˣ` as the one-place idèles and
`Φ : 𝕀_K →* Gal(F/K)` is the idèlic Artin map of the ideal-theoretic reciprocity law
(`NK.CFTLib.artinReciprocityIdeal_proved`): `Φ x := artinSym (idealOf (x · b_x))` for the
congruence adjustment `b_x` of a modulus `m` of the law
(`Work.SSGRoute.ZDataMup.exists_ideleArtinMap_with_kernel`, which also identifies
`ker Φ = N_{F/K} 𝕀_F ⊔ Kˣ` through `NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup`).

* The **kernel clause** is the one-place dictionary
  `NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff` together with the abelian local faithfulness
  `Work.SSGRoute.ZDataMup.localFaithful_abelian` (a one-place idèle in `N 𝕀_F · Kˣ` is already a
  norm idèle).
* The **Frobenius clause** is the conductor drop at every unramified prime,
  `Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified`, transported through
  `NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime` (a congruence adjustment of the prime idèle at an
  unramified `Q` has trivial Artin symbol, so the Artin symbol of `Q` is `Frob_Q`).
* The **product formula** is `Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one`: `Φ` kills the
  principal idèles, and `∏_{v ∈ T} onePlace_v(x_v) = principalIdele K x` for any finite `T`
  containing the support of the principal idèle, so the product of the local factors is `Φ` of that
  idèle once the factors outside `s` are trivial.
-/

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

namespace Work.SSGRoute.step4_y_escape_v2

theorem localFactor_productFormula_clean {K : Type} [Field K] [NumberField K]
    {F : Type} [Field F] [NumberField F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    (hcomm : ∀ a b : Gal(F/K), a * b = b * a) :
    ∃ θ : (v : NK.GlobalCFT.Place K) → (NK.GlobalCFT.Place.localField K v)ˣ →* Gal(F/K),
      (∀ v, MonoidHom.ker (θ v) =
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := F) v) ∧
      (∀ Q : NK.Chebotarev.PrimeIdeal K, NK.HeckeL.IsUnramifiedIn (K := K) (L := F) Q →
        θ (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)
          = NK.Chebotarev.frobAtPrime (K := K) (L := F) Q) ∧
      (∀ (x : Kˣ) (s : Finset (NK.GlobalCFT.Place K)),
        (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt v x) = 1) →
        NK.CFTLib.IdeleHasse.cprod hcomm s
          (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) := by
  classical
  -- the ideal-theoretic reciprocity law at a modulus `m`, and a congruence subgroup of modulus `m`
  obtain ⟨m, hm, hram, hprinc⟩ := NK.CFTLib.artinReciprocityIdeal_proved K F hcomm
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  -- the idèlic Artin map at the modulus `m`, with its kernel `N_{F/K} 𝕀_F ⊔ Kˣ`
  obtain ⟨Φ, hagree, hker, _hprincipal, _hgood, _hsurj⟩ :=
    Work.SSGRoute.ZDataMup.exists_ideleArtinMap_with_kernel (K := K) (L := F) hcomm m hm hram
      hprinc U hU hadj
  -- Frobenius normalisation at *every* unramified prime (the conductor drop)
  have hfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := F) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := F) Q := by
    intro Q hunr
    rw [hagree]
    exact Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified (K := K) (L := F) hcomm m
      hm hram hprinc U hU hadj hunr
  -- `Φ` kills the idèlic norms and the principal idèles (it is the Artin map of the class field)
  have hnorm : ∀ y : NK.GlobalCFT.Idele F, Φ (NK.GlobalCFT.Idele.normIdeleHom K F y) = 1 := by
    intro y
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_left
      (NK.GlobalCFT.Idele.mem_normImage.mpr ⟨y, fun v => by
        rw [NK.GlobalCFT.Idele.normIdeleHom_apply]⟩)
  have hprin : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1 := by
    intro a
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_right (NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩)
  -- one-place faithfulness: the kernel of `Φ ∘ onePlace_v` is the local norm subgroup
  have hloc : ∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := F) v := by
    intro v a
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨fun h => (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := F) v a).mp
        (Work.SSGRoute.ZDataMup.localFaithful_abelian (K := K) (L := F) hcomm h),
      fun h => Subgroup.mem_sup_left
        ((NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := F) v a).mpr h)⟩
  refine ⟨fun v => Φ.comp (NK.CFTLib.IdeleHasse.onePlaceHom v), ?_, ?_, ?_⟩
  · -- the local norm subgroup is the kernel of the local factor
    intro v
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, NK.CFTLib.IdeleHasse.onePlaceHom_apply]
    exact hloc v a
  · -- Frobenius normalisation at every unramified prime
    intro Q hunr
    rw [MonoidHom.comp_apply, NK.CFTLib.IdeleHasse.onePlaceHom_apply,
      NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime]
    exact hfrob Q hunr
  · -- the product formula on the principal idèles
    intro x s hs
    have h1 : NK.CFTLib.IdeleHasse.cprod hcomm s
        (fun v => (Φ.comp (NK.CFTLib.IdeleHasse.onePlaceHom v))
          (NK.CFTLib.IdeleHasse.localImageAt v x)) =
        NK.CFTLib.IdeleHasse.cprod hcomm s
          (fun v => Φ (NK.HassePrinciple.onePlace v
            (NK.CFTLib.IdeleHasse.localImageAt v x))) :=
      NK.CFTLib.IdeleHasse.cprod_congr hcomm (fun v => by
        rw [MonoidHom.comp_apply, NK.CFTLib.IdeleHasse.onePlaceHom_apply])
    rw [h1]
    exact Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one (K := K) (L := F) hcomm Φ hprin hnorm
      x s (fun v hv => by
        have h := hs v hv
        rwa [MonoidHom.comp_apply, NK.CFTLib.IdeleHasse.onePlaceHom_apply] at h)

end Work.SSGRoute.step4_y_escape_v2
