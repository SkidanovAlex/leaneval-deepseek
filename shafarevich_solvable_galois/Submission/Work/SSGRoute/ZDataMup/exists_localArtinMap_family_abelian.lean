import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.Work.SSGRoute.NKExistenceImport
import Submission.Work.SSGRoute.ZDataMup.onePlace_mem_normImage_of_mem_sup_abelian
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The family of local Artin maps of an abelian extension, from the global Artin map

`Work.SSGRoute.ZDataMup.exists_localArtinMap_family_abelian` asks for a family
`θ v : (K_v)ˣ →* Gal(L/K)` of *local Artin maps* of an **abelian** extension `L/K` of number
fields, with

* `ker (θ v) = localNormSubgroup K L v` (the family is faithful, one place at a time),
* `θ (ofFinite Q) (unifUnit K Q) = frobAtPrime Q` for every prime `Q` unramified in `L/K`
  (the Frobenius normalisation),
* the *product formula*: `∏_v θ v (localImageAt v x) = 1` for every `x ∈ Kˣ` (Milne, *CFT*,
  VII.8.1(a): the product of the local Artin maps kills the principal idèles).

This file reduces the existence statement to the **global** Artin map: given a homomorphism
`Φ : 𝕀_K →* Gal(L/K)` which kills the principal idèles and the idèlic norms, is one-place
faithful and Frobenius-normalised, the family `θ v := Φ ∘ onePlace_v` has the three properties.

* Faithfulness is the one-place clause of `Φ` combined with the dictionary
  `onePlace v a ∈ N_{L/K}𝕀_L ↔ a ∈ localNormSubgroup K L v`
  (`NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff`).
* The Frobenius normalisation is the corresponding clause of `Φ`, together with the fact that the
  one-place idèle at `unifUnit Q` *is* the prime idèle `ideleOfPrime K Q`
  (`onePlace_ofFinite_unifUnit_eq_ideleOfPrime` below).
* The product formula is `Φ (principalIdele K x) = 1` rewritten through the decomposition of an
  idèle into its one-place pieces (`idele_eq_prod_onePlace`) and the fact that
  `(principalIdele K x) v = localImageAt v x`.

So the whole arithmetic content is concentrated in the existence of the global `Φ` (Artin
reciprocity in idèlic form); the passage from `Φ` to the local family is elementary.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT

/-! ## A `cprod` helper -/

/-- `cprod` (the product in the commutative monoid structure determined by `hcomm`) behaves as
expected under adjoining a single index. -/
private theorem cprod_insert_of_onePlace {G : Type} [Group G] {ι : Type*} [DecidableEq ι]
    (hcomm : ∀ x y : G, x * y = y * x)
    {s : Finset ι} {f : ι → G} {a : ι} (ha : a ∉ s) :
    NK.CFTLib.IdeleHasse.cprod hcomm (insert a s) f = f a * NK.CFTLib.IdeleHasse.cprod hcomm s f := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold NK.CFTLib.IdeleHasse.cprod
  rw [Finset.prod_insert ha]

/-! ## Two elementary lemmas about idèles -/

/-- **The product of a family of idèles, evaluated at a place, is the product of the values.**
`Idele K` is a restricted product, so multiplication is componentwise
(`NK.GlobalCFT.Idele.mul_apply`); this lemma records the consequence for finite products (there is
no `Finset.prod_apply` for a restricted product). -/
theorem idele_prod_apply {K : Type} [Field K] [NumberField K] (s : Finset (Place K))
    (f : Place K → Idele K) (w : Place K) :
    (∏ v ∈ s, f v) w = ∏ v ∈ s, (f v) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Idele.mul_apply, ih]

/-- **An idèle is the product of its one-place pieces**, over any finite set of places containing
its support. -/
theorem idele_eq_prod_onePlace {K : Type} [Field K] [NumberField K] (y : Idele K)
    (s : Finset (Place K)) (h : ∀ v : Place K, v ∉ s → y v = 1) :
    y = ∏ v ∈ s, NK.CFTLib.IdeleHasse.onePlaceHom v (y v) := by
  classical
  refine Idele.ext fun w => ?_
  rw [idele_prod_apply]
  by_cases hw : w ∈ s
  · rw [Finset.prod_eq_single w]
    · rw [NK.CFTLib.IdeleHasse.onePlaceHom_apply, NK.HassePrinciple.onePlace_apply_self]
    · intro b _ hb
      rw [NK.CFTLib.IdeleHasse.onePlaceHom_apply,
        NK.HassePrinciple.onePlace_apply_ne (Ne.symm hb)]
    · intro hws
      exact absurd hw hws
  · rw [Finset.prod_eq_one]
    · exact h w hw
    · intro b hb
      rw [NK.CFTLib.IdeleHasse.onePlaceHom_apply,
        NK.HassePrinciple.onePlace_apply_ne (fun hbw => hw (by rw [hbw]; exact hb))]

/-- **The one-place idèle at the unit idèle of a prime is the prime idèle.** -/
theorem onePlace_ofFinite_unifUnit_eq_ideleOfPrime {K : Type} [Field K] [NumberField K]
    (Q : HeightOneSpectrum (𝓞 K)) :
    NK.HassePrinciple.onePlace (Place.ofFinite Q) (IdeleClassGroup.unifUnit K Q) =
      NK.HeckeL.ideleOfPrime K Q := by
  refine Idele.ext fun v => ?_
  rcases v with w | q
  · rw [NK.HassePrinciple.onePlace_apply_ne (by simp [Place.ofInfinite, Place.ofFinite]),
      NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofInfinite]
  · by_cases h : q = Q
    · subst h
      rw [NK.HassePrinciple.onePlace_apply_self,
        NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_self]
    · rw [NK.HassePrinciple.onePlace_apply_ne (by simpa using h),
        NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_ne_exists h]

/-! ## From the global Artin map to the family of local maps -/

open NK.CFTLib.IdeleHasse

variable {K : Type} [Field K] [NumberField K]
variable {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A monoid homomorphism out of `𝕀 K` evaluated on a product of one-place idèles is the product
of the evaluations, in the explicitly commutative monoid structure on the target. -/
theorem cprod_map_onePlace {G : Type} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    (Φ : Idele K →* G) (c : ∀ v : Place K, (Place.localField K v)ˣ) (s : Finset (Place K)) :
    Φ (∏ v ∈ s, onePlaceHom v (c v)) =
      cprod hcomm s (fun v => Φ (onePlaceHom v (c v))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [NK.CFTLib.IdeleHasse.cprod]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, map_mul, ih, cprod_insert_of_onePlace hcomm ha]

/-- **The family `θ v = Φ ∘ onePlace v` of local maps attached to a global Artin map.** -/
theorem exists_localArtinMap_family_of_globalArtinMap
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hΦ : ∃ Φ : Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ (v : Place K) (a : (Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ Idele.normImage K L) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 K)), NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)) :
    ∃ θ : (v : Place K) → (Place.localField K v)ˣ →* (L ≃ₐ[K] L),
      (∀ v, MonoidHom.ker (θ v) = localNormSubgroup (K := K) (L := L) v) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 K)), NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        θ (Place.ofFinite Q) (IdeleClassGroup.unifUnit K Q) =
          NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ∧
      (∀ (x : Kˣ) (s : Finset (Place K)),
        (∀ v, v ∉ s → localImageAt v x = 1) →
        cprod hcomm s (fun v => θ v (localImageAt v x)) = 1) := by
  obtain ⟨Φ, hprin, hnorm, hsurj, hone, hfrob⟩ := hΦ
  refine ⟨fun v => Φ.comp (onePlaceHom v), ?_, ?_, ?_⟩
  · intro v
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, onePlaceHom_apply, hone v a]
    exact onePlace_mem_normImage_iff (K := K) (L := L) v a
  · intro Q hunr
    show Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q) (IdeleClassGroup.unifUnit K Q)) =
      NK.Chebotarev.frobAtPrime (K := K) (L := L) Q
    rw [onePlace_ofFinite_unifUnit_eq_ideleOfPrime Q]
    exact hfrob Q hunr
  · intro x s hs
    have hy : ∀ v : Place K, v ∉ s → (Idele.principalIdele K x) v = 1 := by
      intro v hv
      have h := hs v hv
      simpa [NK.CFTLib.IdeleHasse.localImageAt, Idele.principalIdele_apply] using h
    have hΦ : Φ (Idele.principalIdele K x) =
        cprod hcomm s
          (fun v => Φ (NK.HassePrinciple.onePlace v ((Idele.principalIdele K x) v))) := by
      conv_lhs => rw [idele_eq_prod_onePlace (Idele.principalIdele K x) s hy]
      rw [cprod_map_onePlace hcomm Φ (fun v => (Idele.principalIdele K x) v) s]
      simp only [NK.CFTLib.IdeleHasse.onePlaceHom_apply]
    have hcongr : cprod hcomm s
          (fun v => (Φ.comp (onePlaceHom v)) (localImageAt v x)) =
        cprod hcomm s
          (fun v => Φ (NK.HassePrinciple.onePlace v ((Idele.principalIdele K x) v))) := by
      refine cprod_congr hcomm fun v => ?_
      rw [MonoidHom.comp_apply, onePlaceHom_apply]
      rfl
    rw [hcongr, ← hΦ, hprin x]

/-! ## The global Artin map of an abelian extension, from the two arithmetic inputs -/

/-- **The global Artin map of an abelian extension, from the ideal-theoretic reciprocity law and
the two remaining arithmetic inputs.**

* `hone` is the *one-place faithfulness* of the Artin map (Milne, *CFT*, V.5.3(a)): a one-place
  idèle which is a norm modulo the principal idèles is a norm.
* `hfrob` is the *Frobenius normalisation at the unramified primes dividing the conductor*: for
  every congruence datum `(m, U)` satisfying the reciprocity law, the idèlic Artin map `ideleArtin`
  sends the prime idèle `ideleOfPrime K Q` to `frobAtPrime Q` at every unramified prime `Q` (in
  particular at the primes dividing the modulus, where the normalisation does *not* follow from
  the definition).

The construction is the standard one: the reciprocity law gives a modulus `m` and a congruence
subgroup `U`; the map `art := ideleArtin` is a monoid homomorphism (this is
`NK.CFTLib.Arl.exists_monoidHom_ideleArtin`) which kills the principal idèles and the idèlic norms
and is surjective; by the existence theorem (`ker_artinMapCK_eq_normClassSubgroup`) its kernel is
exactly `N_{L/K}𝕀_L · Kˣ`, which turns `hone` into one-place faithfulness. -/
theorem global_artinMap_abelian_of_onePlace_faithful_of_frobAtPrime
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hone : ∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
      NK.HassePrinciple.onePlace v a ∈
        NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K →
      NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L)
    (hfrob : ∀ (m : ℕ) (hm : 0 < m)
      (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
      (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
      (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
      (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
        x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
      (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L) ∧
      (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  open NK.GlobalCFT in
  obtain ⟨m, hm, hramIn, hprincIn⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  obtain ⟨art, hagree, hprincipal, hgood, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hramIn hprincIn
      U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hramIn
      hprincIn U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm z
    exact ⟨d, hUeq ▸ hd⟩
  have hPle : Idele.principalSubgroup K ≤ art.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hprincipal a)
  have hker : art.ker = Idele.normImage K L ⊔ Idele.principalSubgroup K := by
    have hFC := NK.CFTLib.fundamentalClassElement
    have h1 := NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup (K := K) (L := L)
      hFC art hPle hnorm hsurj
    refine le_antisymm ?_ ?_
    · intro x hx
      have hmk : IdeleClassGroup.mk K x ∈ (NK.CFTLib.Existence.artinMapCK art hPle).ker := by
        rw [MonoidHom.mem_ker, NK.CFTLib.Existence.artinMapCK_mk]
        exact MonoidHom.mem_ker.mp hx
      rw [h1] at hmk
      obtain ⟨n, hn, hmn⟩ := Subgroup.mem_map.mp hmk
      have h2 : n⁻¹ * x ∈ Idele.principalSubgroup K :=
        (IdeleClassGroup.mk_eq_mk_iff).mp hmn
      have h3 : n * (n⁻¹ * x) ∈ Idele.normImage K L ⊔ Idele.principalSubgroup K :=
        Subgroup.mul_mem_sup hn h2
      rwa [mul_inv_cancel_left] at h3
    · refine sup_le ?_ hPle
      intro x hx
      obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hx
      rw [MonoidHom.mem_ker,
        show x = Idele.normIdeleHom K L y from
          Idele.ext (fun v => by rw [Idele.normIdeleHom_apply]; exact hy v)]
      exact hnorm y
  refine ⟨art, hprincipal, hnorm, hsurj, ?_, ?_⟩
  · intro v a
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨hone v a, fun h => Subgroup.mem_sup_left h⟩
  · intro Q hunr
    rw [hagree]
    exact hfrob m hm hramIn hprincIn U hU hadj Q hunr

/-! ## The global Artin map of an abelian extension -/

/-- **The global Artin map of an abelian extension of number fields, with the five clauses.**

There is a homomorphism `Φ : 𝕀_K →* Gal(L/K)` which kills the principal idèles, kills the idèlic
norms, is surjective, is *one-place faithful*
(`Φ (onePlace v a) = 1 ↔ onePlace v a ∈ N_{L/K}𝕀_L`, Milne, *CFT*, V.5.3(a)) and is
Frobenius-normalised at every unramified prime (Milne, *CFT*, VII.8.1 with the Frobenius
normalisation of the Artin symbol). -/
theorem global_artinMap_abelian {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L) ∧
      (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  refine global_artinMap_abelian_of_onePlace_faithful_of_frobAtPrime (K := K) (L := L) hcomm ?_ ?_
  · intro v a h
    exact onePlace_mem_normImage_of_mem_sup_abelian (K := K) (L := L) hcomm h
  · intro m hm hram hprinc U hU hadj Q hunr
    exact ideleArtin_ideleOfPrime_of_unramified (K := K) (L := L) hcomm m hm hram
      hprinc U hU hadj hunr

/-- **The family of local Artin maps of an abelian extension of number fields.**

For an abelian extension `L/K` of number fields there is a family `θ v : (K_v)ˣ →* Gal(L/K)` of
local Artin maps with kernel the local norm subgroup, Frobenius-normalised at the unramified
primes, and satisfying the product formula `∏_v θ v (localImageAt v x) = 1` for every `x ∈ Kˣ`
(Milne, *CFT*, VII.8.1(a)). -/
theorem exists_localArtinMap_family_abelian {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) :
    ∃ θ : (v : NK.GlobalCFT.Place K) →
        (NK.GlobalCFT.Place.localField K v)ˣ →* (L ≃ₐ[K] L),
      (∀ v, MonoidHom.ker (θ v) = NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) ∧
      (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        θ (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)
          = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ∧
      (∀ (x : Kˣ) (s : Finset (NK.GlobalCFT.Place K)),
        (∀ v, v ∉ s → NK.CFTLib.IdeleHasse.localImageAt v x = 1) →
        NK.CFTLib.IdeleHasse.cprod hcomm s
          (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) :=
  exists_localArtinMap_family_of_globalArtinMap (K := K) (L := L) hcomm
    (global_artinMap_abelian (K := K) (L := L) hcomm)

end Work.SSGRoute.ZDataMup
