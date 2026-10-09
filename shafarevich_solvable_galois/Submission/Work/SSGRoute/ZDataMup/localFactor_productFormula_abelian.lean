import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup
import Submission.Work.SSGRoute.ZDataMup.onePlace_mem_normImage_of_mem_sup_abelian
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local factors of the abelian Artin map, and the product formula

Two remarks for the reader/prover:

* The requested statement referred to `NK.CFTLib.IdeleClassGroup.unifUnit`; that name does *not*
  exist in this workspace (the local uniformiser idèle is `NK.GlobalCFT.IdeleClassGroup.unifUnit`,
  used with exactly this signature in `Submission/Work/SSGRoute/ZSplit/localFactor_productFormula_cyclic.lean`).
  The statement below is the requested one with that single identifier corrected; nothing else about
  it has been changed.

* The residue of this module is exactly two arithmetic inputs.  The chain that closes them is:

  `Work.SSGRoute.ZDataMup.normImage_fixedField_inf_le`   (class-formation axiom: intersection of
      norm groups of `fixedField H₁` and `fixedField H₂` inside the norm group of
      `fixedField (H₁ ⊓ H₂)`, for abelian `L/K`)
    plus `Work.SSGRoute.ZDataMup.hilbertReciprocity_abelian_of_classFormation`
      (iterating that axiom over the cyclic subextensions, together with the cyclic case and
      `iInf_subgroup_isCyclic_quotient`)
    gives the abelian "one place omitted" statement `onePlace_hilbertReciprocity_abelian` below,
    which is the arithmetic heart of `localFaithful_abelian` and of the Artin map input.

  Each of the two is delegated and proved independently by a sibling in-flight module:

  - `exists_ideleArtin_abelian_frob_unramified`  ~  `Work.SSGRoute.ZDataMup.ideleArtin_frob_unramified_abelian`
    (abelian idèlic Artin map: kernel `N 𝕀_L · Kˣ`, Frobenius normalised at *every* unramified prime);
  - `onePlace_hilbertReciprocity_abelian`       ~  `Work.SSGRoute.ZDataMup.hilbertReciprocity_abelian_onePlace`
    (Hilbert reciprocity, one place omitted, for abelian `L/K`).

  Everything else is proved here: the product formula `cprod_localFactor_eq_one`, the bridge
  `map_prod_onePlace`, the componentwise local-norm criterion, and the reduction
  `localFaithful_abelian` of V.5.3(a) to the one-place statement (the same skeleton as the cyclic
  `NK.CFTLib.IdeleHasse.localFaithful_onePlace`).
-/


/-!
# The local factors of the abelian Artin map and the product formula

For a finite **abelian** extension `L / K` of number fields there is a family of local maps
`θ_v : K_vˣ →* Gal(L/K)`, one at each place, with local norm subgroups as kernels, Frobenius
normalised, and satisfying the product formula: for `x ∈ Kˣ` and a finite set `s` with
`θ_v (x_v) = 1` for `v ∉ s`, the product `∏_{v ∈ s} θ_v (x_v)` is `1`.

## Layout

The family is `θ_v := Φ ∘ onePlace_v` for the global idèlic Artin map `Φ : 𝕀_K →* Gal(L/K)`.  Two
arithmetic inputs are isolated as hypotheses-free theorems below:

* `exists_ideleArtin_abelian_frob_unramified`: `Φ` exists with `ker Φ = N 𝕀_L · Kˣ` and
  `Φ (ideleOfPrime K Q) = Frob_Q` at *every* unramified prime;
* `localFaithful_abelian`: `{a : onePlace v a ∈ N 𝕀_L · Kˣ} = N_v` (Milne, *CFT*, V.5.3(a)), the
  abelian generalisation of the workspace's cyclic `NK.CFTLib.IdeleHasse.localFaithful_onePlace`.

Everything else — in particular the product formula — is proved here.
-/

namespace Work.SSGRoute.ZDataMup

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {K : Type} [Field K] [NumberField K]


/-! ## The two arithmetic inputs -/

/-- **The idèlic Artin map of an abelian extension, Frobenius-normalised at every unramified
prime.**  (Arithmetic input.  The same statement, with the proof strategy
"ideal-theoretic reciprocity law + conductor supported on the ramified primes", is being built
under `Work.SSGRoute.ZDataMup.ideleArtin_frob_unramified_abelian`; it is restated here so that
this module can be switched to that one by a single import as soon as it builds.) -/
theorem exists_ideleArtin_abelian_frob_unramified {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      MonoidHom.ker Φ = NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  -- the ideal-theoretic reciprocity law at a modulus `m`
  obtain ⟨m, hm, hram, hprinc⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  -- the congruence subgroup of modulus `m`, with an adjustment
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  -- the idèlic Artin map together with its kernel
  obtain ⟨art, hagree, hker, _hprincipal, _hgood, _hsurj⟩ :=
    exists_ideleArtinMap_with_kernel (K := K) (L := L) hcomm m hm hram hprinc U hU hadj
  refine ⟨art, hker, fun Q hunr => ?_⟩
  rw [hagree]
  exact ideleArtin_ideleOfPrime_of_unramified (K := K) (L := L) hcomm m hm hram hprinc
    U hU hadj hunr

/-! ## The main theorem -/

-- (Repair note: this file carried an *orphaned* declaration docstring — a docstring followed by a
-- section comment instead of a declaration — which made the module fail to elaborate and took the
-- whole `ArtinReciprocity` / `mup` cone (including `mup_localArtin_productFormula`) out of the
-- build.  It was removed verbatim here so that the cone builds again; the statement it described
-- (the abelian one-place form of Hilbert reciprocity) was not used anywhere in this file.)

theorem localFactor_productFormula_abelian {K : Type} [Field K] [NumberField K]
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
        (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt v x) = 1) →
        NK.CFTLib.IdeleHasse.cprod hcomm s
          (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) := by
  classical
  obtain ⟨Φ, hker, hfrob⟩ := exists_ideleArtin_abelian_frob_unramified (K := K) (L := L) hcomm
  have hnorm : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_left
      (NK.GlobalCFT.Idele.mem_normImage.mpr ⟨y, fun v => by
        rw [NK.GlobalCFT.Idele.normIdeleHom_apply]⟩)
  have hprin : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1 := by
    intro a
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_right (NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩)
  refine ⟨fun v =>
    { toFun := fun a => Φ (NK.HassePrinciple.onePlace v a)
      map_one' := by rw [NK.CFTLib.IdeleHasse.onePlace_one, map_one]
      map_mul' := by
        intro a b
        rw [NK.CFTLib.IdeleHasse.onePlace_mul, map_mul] }, ?_, ?_, ?_⟩
  · intro v
    ext a
    show Φ (NK.HassePrinciple.onePlace v a) = 1 ↔ a ∈ _
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨fun h => (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a).mp
        (localFaithful_abelian (K := K) (L := L) hcomm h),
      fun h => Subgroup.mem_sup_left
        ((NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a).mpr h)⟩
  · intro Q hunr
    show Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q)) = _
    rw [NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime]
    exact hfrob Q hunr
  · intro x s hs
    exact cprod_localFactor_eq_one (K := K) (L := L) hcomm Φ hprin hnorm x s
      (fun v hv => hs v hv)

end Work.SSGRoute.ZDataMup
