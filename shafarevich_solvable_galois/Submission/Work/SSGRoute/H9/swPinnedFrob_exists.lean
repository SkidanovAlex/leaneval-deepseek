import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swChainConjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A Frobenius element pinned at a level of `↥K`

The §4(b) chain of Schmidt--Wingberg needs its Frobenius elements *pinned*: the local
pairing--value dictionary `Work.SSGRoute.H9.swPairingValueFrob` is a statement about the value of a
Kummer cochain at the element whose image in the Kummer level is the canonical Frobenius
`NK.Chebotarev.frobAtPrime`.

This module produces such an element at an arbitrary finite level `Λ` of `↥K` which is Galois over
`↥K` (the levels of the assembly are the composita of the Kummer levels `hLevel w`, `w ∈ W`, of the
recursion's elements; see `Submission/Work/SSGRoute/H9/NOTE_pinning_and_promotion_session7.md` §2):

    `∃ ψ ∈ decomp k A ⊓ K.fixingSubgroup,  IsFrobAtPrime (K := ↥K) (L := Λ) 𝔮 (res_Λ ψ)`

with `𝔮 = oddPrime (K := K) A hA`.  **No unramifiedness of `Λ` at `A` is used** (and none holds in
the application); the construction is

* the prime `P` of `𝓞 Λ` above `𝔮` and below `A` (`NK.Reconstruct.primeOfLevel` +
  `NK.Reconstruct.primeOfLevel_spec`, `NK.ResidueFrob.primeOfLevel_liesOver`),
* an arithmetic Frobenius `σ` at `P` (`NK.Chebotarev.exists_isFrobAt`, no unramifiedness needed),
* its lift `g ∈ decomp ↥K A` (`Work.SSGRoute.ZDataMup.exists_mem_decomp_res_eq_of_isFrobAt` at the
  base field `↥K`),

and the passage back to `G_k` is `Work.SSGRoute.toGkHom` (`Gal(Ω/↥K) ≃* K.fixingSubgroup ≤ G_k`).
The template is the proof of `Work.SSGRoute.ZDataMup.exists_isFrobAtPrime_split` (the same
construction at the base `k`).
-/

open _root_.SSGRoute

namespace Work.SSGRoute.H9

/-- **A pinned Frobenius at a level of `↥K`.** -/
theorem swPinnedFrob_exists (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    (Λ : IntermediateField ↥K Ω) [FiniteDimensional ↥K Λ] [IsGalois ↥K Λ] [NumberField ↥Λ]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥Λ)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
        (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) Λ
          ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩)) := by
  classical
  haveI hACK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- `A` is a finite place for the base field `↥K` as well
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA
  -- the prime of `𝓞 Λ` below `A`
  have hne : A.comap (algebraMap ↥Λ Ω) ≠ ⊤ :=
    NK.Reconstruct.comap_level_ne_top (K₁ := ↥K) hAK Λ
  set P : NK.Chebotarev.PrimeIdeal ↥Λ := NK.Reconstruct.primeOfLevel A Λ hne with hPdef
  have hPspec : A.comap (algebraMap ↥Λ Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ P :=
    NK.Reconstruct.primeOfLevel_spec A Λ hne
  -- `P` lies over the prime of `↥K` below `A`
  have hlies : P.asIdeal.LiesOver
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).asIdeal := by
    have h := NK.ResidueFrob.primeOfLevel_liesOver (K := ↥K) (K' := Ω) ⟨A, hAK⟩ Λ
    rwa [show Submission.NeukirchUchida.primeOf A hAK =
        Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA from rfl] at h
  -- a Frobenius element at `P`
  obtain ⟨σ, hσ⟩ := NK.Chebotarev.exists_isFrobAt (K := ↥K) (L := ↥Λ)
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) P hlies
  -- lift it into the decomposition group of `A` over `↥K`
  obtain ⟨g, hgD, hgres⟩ :=
    Work.SSGRoute.ZDataMup.exists_mem_decomp_res_eq_of_isFrobAt (k := ↥K) (Ω := Ω) Λ A hAK P
      hPspec σ hσ
  -- pass back to `G_k`
  have hψK : Work.SSGRoute.toGkHom K g ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [Work.SSGRoute.toGkHom_apply]
    simpa using g.commutes ⟨x, hx⟩
  have hψD : Work.SSGRoute.toGkHom K g ∈ SSGRoute.decomp k A :=
    (Work.SSGRoute.toGkHom_mem_decomp K A g).mpr hgD
  refine ⟨Work.SSGRoute.toGkHom K g, Subgroup.mem_inf.mpr ⟨hψD, hψK⟩, ?_⟩
  have hfix : (IntermediateField.fixingSubgroupEquiv K)
      ⟨Work.SSGRoute.toGkHom K g, hψK⟩ = g := by
    apply Work.SSGRoute.toGkHom_injective K
    rw [Work.SSGRoute.toGkHom_fixingSubgroupEquiv]
  rw [hfix]
  refine ⟨P, hlies, ?_⟩
  show NK.Chebotarev.IsFrobAt P (SSGRoute.res ↥K Λ g)
  rw [hgres]
  exact hσ

end Work.SSGRoute.H9
