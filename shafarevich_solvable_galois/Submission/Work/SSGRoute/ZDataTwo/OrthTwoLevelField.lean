import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.N2v2.orthogonality_hsplit_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The full-clause Artin map of a level field, at `p = 2`

This is the first assembled piece of
`Work.SSGRoute.ZDataTwo.orthogonality_L2K_trichotomy_two`: given the level field `F ≤ N'`
(with its norm class subgroup `U' ⊔ W`, produced by `N2v2.levelField`) this packages

* the idèlic Artin map `Φ` of `F/↥K` in the full-clause form of `N2v2.exists_artinMap_fullClauses`
  — kernel `N 𝕀_F ⊔ ↥Kˣ`, the local-factor kernel clause `Φ (onePlace v u) = 1 ↔ u ∈ N_v`, the
  Frobenius normalisation, the product formula, the decomposition lift `hlift` and the inertia lift
  `hunith` — together with
* `hexpE : ∀ σ : Gal(F/↥K), σ ^ 2 = 1` (from `galExp_of_pPowSubgroup_le`, using `C² ⊆ N_{F/↥K}`).

The instances of `F` are *variables* of the statement (not existential binders), so that the
typeclass search in the statement stays cheap.
-/

namespace Work.SSGRoute.ZDataTwo

set_option maxHeartbeats 1600000

open _root_.SSGRoute
open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

/-- **The Artin map of a level field `F/↥K` with all the clauses the orthogonality consumes**, plus
the exponent-`2` clause. -/
theorem artinMap_fullClauses_of_levelField
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F]
    [NumberField ↥F] [IsMulCommutative (↥F ≃ₐ[↥K] ↥F)]
    (hp2 : Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup ↥K) ≤
      Idele.normClassSubgroup ↥K ↥F) :
    ∃ Φ : Idele ↥K →* (↥F ≃ₐ[↥K] ↥F),
      Φ.ker = Idele.normImage ↥K ↥F ⊔ Idele.principalSubgroup ↥K ∧
      (∀ (v : Place ↥K) (u : (Place.localField ↥K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v u) = 1 ↔
          u ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F) v) ∧
      (∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
        NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) Q →
        Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥F) Q) ∧
      (∀ (x : (↥K)ˣ) (s : Finset (Place ↥K)),
        (∀ v, v ∉ s →
          Φ (NK.HassePrinciple.onePlace v
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v x)) = 1) →
        NK.CFTLib.IdeleHasse.cprod (fun a b => mul_comm' a b) s
          (fun v => Φ (NK.HassePrinciple.onePlace v
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v x))) = 1) ∧
      (∀ σ : ↥F ≃ₐ[↥K] ↥F, σ ^ 2 = 1) ∧
      (∀ (A : ValuationSubring Ω) (_hA : SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ x : (↥K)ˣ,
        ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) F σ =
            Φ (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) x))) ∧
      (∀ (A : ValuationSubring Ω) (_hA : SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ u : (Place.localField ↥K (Place.ofFinite 𝔭))ˣ,
          u ∈ Place.localUnits ↥K (Place.ofFinite 𝔭) →
        ∃ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) F σ =
            Φ (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭) u)) := by
  classical
  obtain ⟨Φ, hker, hloc, hfrob, hprod, hlift, hunith⟩ :=
    Work.SSGRoute.N2v2.exists_artinMap_fullClauses (K := K) F
  refine ⟨Φ, hker, hloc, hfrob, hprod, ?_, hlift, hunith⟩
  exact Work.SSGRoute.N2v2.galExp_of_pPowSubgroup_le (p := 2) (K := K) (E := F) hp2 Φ hker hfrob

end Work.SSGRoute.ZDataTwo
