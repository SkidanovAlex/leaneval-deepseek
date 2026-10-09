import Mathlib
import Submission.Work.SSGRoute.ZDataMup.MupCruxImports
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.exists_localGlobalArtinMap_kills_principal_cyclic
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.exists_artinMap_ker_eq_normImage_sup_principal
import Submission.Work.SSGRoute.ZDataMup.localFactor_productFormula_abelian
import Submission.Work.SSGRoute.ZDataMup.artinSym_eq_one_of_isAdmissible_cyclic
import Submission.NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Artin factors of a cyclic extension: kernels, Frobenius normalisation, product formula

`Work.SSGRoute.ZDataMup.mup_localArtin_productFormula`: for a cyclic extension `L/K` of number
fields with `K` totally imaginary, there is a family `θ_Q : (Q.adicCompletion K)ˣ →* Gal(L/K)` of
finite-place local maps with

1. `ker (θ_Q) = localNormSubgroup (K := K) (L := L) (ofFinite Q)` (local faithfulness, Milne
   *CFT* V.5.3(a)),
2. `θ_Q (unifUnit K Q) = frobAtPrime Q` at every unramified `Q`, and
3. the product formula `∏_Q θ_Q (x_Q) = 1` for every `x ∈ K^×` (Milne *CFT* VII.8.1(a)).

## The reduction (the whole content of this file)

The family is `θ_Q := Φ ∘ onePlace_Q` for a single global map `Φ : 𝕀 K →* Gal(L/K)` which kills the
principal idèles, kills the idèlic norms, is Frobenius-normalised at *every* unramified prime and is
faithful at every one-place idèle.  Such a `Φ` is exactly "the local–global Artin map kills `K^×`",
i.e. the **product form of Hilbert reciprocity** (Milne *CFT* VII.8.1(a)).  It is produced here by
`Work.SSGRoute.ZDataMup.ArtinReciprocity.exists_localGlobalArtinMap_kills_principal_cyclic`, whose
route is the ideal-modulus port of Lang's conductor theorem, and given `Φ`:

* clause 1 is `Φ (onePlace_Q a) = 1 ↔ onePlace_Q a ∈ N_{L/K}𝕀_L` (one-place faithfulness, from
  `ker Φ = N_{L/K}𝕀_L ⊔ K^×` and `NK.CFTLib.IdeleHasse.localFaithful_onePlace`) together with the
  one-place dictionary `onePlace_mem_normImage_iff`;
* clause 2 is `onePlace_unifUnit_eq_ideleOfPrime` plus the Frobenius normalisation of `Φ` (this is
  the conductor drop at the primes dividing the modulus, Neukirch *ANT* V.6.1 / Lang *ANT* X §4);
* clause 3 is `cprod_localFactor_eq_one` (the product formula), together with the fact that `x_Q` is
  a local norm — hence `θ_Q (x_Q) = 1` — at all but finitely many `Q`, and that at a **complex**
  infinite place the local factor is trivial (Milne V.5.3: at a complex place `L_w = K_w = ℂ` and
  the norm is onto, so `localNormSubgroup = ⊤`); the hypothesis `hcomplex` is used exactly here.

## The kernel of `Φ`

The existence theorem of the `ArtinReciprocity` lane only supplies, besides the Frobenius
normalisation, the *surjectivity* of `Φ` and the triviality of `Φ` on the principal idèles and on
the idèlic norms.  The class-formation index computation
(`ker_artinMapCK_eq_normClassSubgroup`, from the global fundamental class
`NK.CFTLib.fundamentalClassElement`) upgrades these to the exact kernel
`ker Φ = N_{L/K}𝕀_L ⊔ K^×`; that is the auxiliary lemma
`ker_eq_normImage_sup_principalSubgroup` below, and it is the only extra input clause 1 needs.
-/

namespace Work.SSGRoute.ZDataMup

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

/-- **The kernel of an idèlic Artin map.**  Let `L/K` be a finite Galois extension of number fields
with commutative Galois group and let `Φ : 𝕀 K →* Gal(L/K)` be surjective, trivial on the principal
idèles `Kˣ` and on the idèlic norms `N_{L/K}𝕀_L`.  Then `ker Φ = N_{L/K}𝕀_L ⊔ Kˣ`.

The inclusion `⊇` is the two trivialities.  For `⊆`, `Φ` kills `Kˣ`, so it descends to a
homomorphism `artinMapCK Φ : C_K →* Gal(L/K)`; the class field theory index computation
`NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup` (from the global fundamental class)
identifies its kernel with the norm class subgroup `N_{L/K} C_L`, whose preimage in `𝕀 K` is
exactly `N_{L/K}𝕀_L ⊔ Kˣ`. -/
lemma ker_eq_normImage_sup_principalSubgroup {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    {Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L)}
    (hprin : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hnorm : ∀ y : NK.GlobalCFT.Idele L,
      Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hsurj : Function.Surjective Φ) :
    Φ.ker = NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K := by
  classical
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  have hPle : NK.GlobalCFT.Idele.principalSubgroup K ≤ Φ.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hprin a)
  have hFC := NK.CFTLib.fundamentalClassElement
  have h1 := NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup (K := K) (L := L)
    hFC Φ hPle hnorm hsurj
  refine le_antisymm ?_ ?_
  · intro x hx
    have hmk : NK.GlobalCFT.IdeleClassGroup.mk K x ∈
        (NK.CFTLib.Existence.artinMapCK Φ hPle).ker := by
      rw [MonoidHom.mem_ker, NK.CFTLib.Existence.artinMapCK_mk]
      exact MonoidHom.mem_ker.mp hx
    rw [h1] at hmk
    obtain ⟨n, hn, hmn⟩ := Subgroup.mem_map.mp hmk
    have h2 : n⁻¹ * x ∈ NK.GlobalCFT.Idele.principalSubgroup K :=
      (NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff).mp hmn
    have h3 : n * (n⁻¹ * x) ∈
        NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K :=
      Subgroup.mul_mem_sup hn h2
    rwa [mul_inv_cancel_left] at h3
  · refine sup_le ?_ hPle
    intro x hx
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hx
    rw [MonoidHom.mem_ker,
      show x = NK.GlobalCFT.Idele.normIdeleHom K L y from
        NK.GlobalCFT.Idele.ext (fun v => by
          rw [NK.GlobalCFT.Idele.normIdeleHom_apply]; exact hy v)]
    exact hnorm y

theorem mup_localArtin_productFormula {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcyc : IsCyclic (L ≃ₐ[K] L))
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hcomplex : ∀ w : NumberField.InfinitePlace K, NumberField.InfinitePlace.IsComplex w) :
    ∃ θ : (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        (Q.adicCompletion K)ˣ →* (L ≃ₐ[K] L),
      (∀ Q, MonoidHom.ker (θ Q) = NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q)) ∧
      (∀ Q, NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        θ Q (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q) =
          NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ∧
      (∀ x : Kˣ, ∃ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (∀ Q, Q ∉ s → θ Q (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom x) = 1) ∧
        NK.CFTLib.IdeleHasse.cprod hcomm s
          (fun Q => θ Q (Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom x)) = 1) := by
  classical
  haveI hTC : NumberField.IsTotallyComplex K := ⟨hcomplex⟩
  haveI hcycI : IsCyclic (L ≃ₐ[K] L) := hcyc
  obtain ⟨Φ, hprin, hnorm, hsurj, hfrob⟩ :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.exists_localGlobalArtinMap_kills_principal_cyclic
      (K := K) (L := L)
  -- the kernel of the global map, and its one-place faithfulness
  have hker := ker_eq_normImage_sup_principalSubgroup (K := K) (L := L) hcomm hprin hnorm hsurj
  have hloc : ∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L := by
    intro v a
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨fun h => NK.CFTLib.IdeleHasse.localFaithful_onePlace (K := K) (L := L) hcyc h,
      fun h => Subgroup.mem_sup_left h⟩
  refine ⟨fun Q => Φ.comp (NK.CFTLib.IdeleHasse.onePlaceHom (NK.GlobalCFT.Place.ofFinite Q)),
    ?_, ?_, ?_⟩
  · -- the kernel of the local factor is the local norm subgroup
    intro Q
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, NK.CFTLib.IdeleHasse.onePlaceHom_apply,
      hloc (NK.GlobalCFT.Place.ofFinite Q) a]
    exact NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite Q) a
  · -- Frobenius normalisation at an unramified prime
    intro Q hunr
    show Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)) = _
    rw [NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime]
    exact hfrob Q hunr
  · -- the product formula
    intro x
    have hNu : ({v : NK.GlobalCFT.Place K | (NK.GlobalCFT.Idele.principalIdele K x) v ∉
        NK.GlobalCFT.Place.localUnits K v}).Finite :=
      Filter.eventually_cofinite.mp (NK.GlobalCFT.Idele.principalIdele K x).2
    have hX : ({Q : HeightOneSpectrum (𝓞 K) | (NK.GlobalCFT.Idele.principalIdele K x)
        (NK.GlobalCFT.Place.ofFinite Q) ∉ NK.GlobalCFT.Place.localUnits K
          (NK.GlobalCFT.Place.ofFinite Q)}).Finite := by
      refine hNu.preimage ?_
      intro a _ b _ hab
      exact NK.GlobalCFT.Place.ofFinite_inj.mp hab
    have hY : ({Q : HeightOneSpectrum (𝓞 K) |
        ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q}).Finite := by
      have hL := Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
        (K := K) (L := L)
      refine (hL.image (fun q : HeightOneSpectrum (𝓞 L) =>
        IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) q)).subset ?_
      rintro Q hQ
      have hex : ∃ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal ∧
          q.asIdeal.ramificationIdx (𝓞 K) ≠ 1 := by
        by_contra h
        refine hQ fun q hq => ?_
        by_contra hne
        exact h ⟨q, hq, hne⟩
      obtain ⟨q, hq, hqe⟩ := hex
      exact ⟨q, hqe, IsDedekindDomain.HeightOneSpectrum.ext (by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, hq.over])⟩
    refine ⟨(hX.union hY).toFinset, ?_, ?_⟩
    · -- away from the finite set the local factor is trivial
      intro Q hQ
      have hunit : (NK.GlobalCFT.Idele.principalIdele K x) (NK.GlobalCFT.Place.ofFinite Q) ∈
          NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) := by
        by_contra h
        exact hQ ((Set.Finite.mem_toFinset (hX.union hY)).mpr (Or.inl h))
      have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
        by_contra h
        exact hQ ((Set.Finite.mem_toFinset (hX.union hY)).mpr (Or.inr h))
      refine (hloc (NK.GlobalCFT.Place.ofFinite Q) _).mpr ?_
      refine (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q) _).mpr ?_
      show (NK.GlobalCFT.Idele.principalIdele K x) (NK.GlobalCFT.Place.ofFinite Q) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
          (NK.GlobalCFT.Place.ofFinite Q)
      exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
        (K := K) (L := L) Q hunr hunit
    · -- the product over the finite set is trivial
      have hinj : Set.InjOn (NK.GlobalCFT.Place.ofFinite)
          (↑((hX.union hY).toFinset) : Set (HeightOneSpectrum (𝓞 K))) :=
        fun a _ b _ hab => NK.GlobalCFT.Place.ofFinite_inj.mp hab
      have hunr : ∀ v : NK.GlobalCFT.Place K,
          v ∉ ((hX.union hY).toFinset).image (NK.GlobalCFT.Place.ofFinite) →
          Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1 := by
        intro v hv
        rcases v with w | Q
        · refine (hloc (NK.GlobalCFT.Place.ofInfinite w) _).mpr ?_
          refine (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L)
            (NK.GlobalCFT.Place.ofInfinite w) _).mpr ?_
          rw [NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top_of_isTotallyComplex
            (M := K) (E := L) hTC w]
          exact Subgroup.mem_top _
        · have hunit : (NK.GlobalCFT.Idele.principalIdele K x) (NK.GlobalCFT.Place.ofFinite Q) ∈
              NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) := by
            by_contra h
            exact hv (Finset.mem_image.mpr
              ⟨Q, (Set.Finite.mem_toFinset (hX.union hY)).mpr (Or.inl h), rfl⟩)
          have hunri : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
            by_contra h
            exact hv (Finset.mem_image.mpr
              ⟨Q, (Set.Finite.mem_toFinset (hX.union hY)).mpr (Or.inr h), rfl⟩)
          refine (hloc (NK.GlobalCFT.Place.ofFinite Q) _).mpr ?_
          refine (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L)
            (NK.GlobalCFT.Place.ofFinite Q) _).mpr ?_
          show (NK.GlobalCFT.Idele.principalIdele K x) (NK.GlobalCFT.Place.ofFinite Q) ∈
            NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
              (NK.GlobalCFT.Place.ofFinite Q)
          exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
            (K := K) (L := L) Q hunri hunit
      have hmain := Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one (K := K) (L := L) hcomm Φ
        hprin hnorm x (((hX.union hY).toFinset).image (NK.GlobalCFT.Place.ofFinite)) hunr
      rw [← hmain, Work.SSGRoute.ZDataMup.cprod_image hcomm hinj
        (fun v => Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)))]
      exact NK.CFTLib.IdeleHasse.cprod_congr hcomm (fun Q => by
        rw [MonoidHom.comp_apply, NK.CFTLib.IdeleHasse.onePlaceHom_apply]
        rfl)


end

end Work.SSGRoute.ZDataMup
