import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZDataMup.localGlobalArtinMap_exists_comm
import Submission.Work.SSGRoute.ZDataMup.AbelianOnePlaceAux4
import Submission.Work.SSGRoute.step4_y_escape_v2.localFactor_productFormula_clean
import Submission.Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
import Submission.Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn
import Submission.Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

open scoped Pointwise
open NumberField IsDedekindDomain

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
## The decomposition clause of an idèlic Artin map

For a finite abelian extension `E/↥K` of number fields, an idèlic Artin map `Φ` of `E/↥K` is
determined by two clauses: its kernel `N_{E/↥K}𝕀_E ⊔ ↥Kˣ` and its Frobenius normalisation
`Φ (ideleOfPrime Q) = Frob_Q` at every unramified prime `Q` (Artin uniqueness, via Čebotarev
generation).  `decompLift_of_artinMap` below records that such a map automatically satisfies the
*decomposition clause*: the one-place idèle at a finite prime `𝔭` of a global unit `x` is sent into
the decomposition group of every place `A` of an algebraic closure `Ω` above `𝔭`, i.e. its image has
a lift `σ ∈ decomp (k := ↥K) A`.

The argument goes through the **decomposition field** `F = E^{D_A}` of `A`, where

  `D_A := (SSGRoute.decomp (k := ↥K) A).map (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E)`

is the image of the decomposition group of `A` in the commutative group `Gal(E/↥K)`, so that
`F = IntermediateField.fixedField H` in the code.

* Because `Gal(E/↥K)` is commutative, `D_A` is normal, so `F/↥K` is Galois, and `𝔭` splits
  completely in `F/↥K` (`hsplit`): the decomposition group of `A` fixes `F` pointwise.
  Equivalently `A.comap (algebraMap ↥F Ω)` has ramification index and inertia degree `1`, so by
  `Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn` the local norm subgroup of `F/↥K`
  at `𝔭` is everything (`htop`).
* The Artin map `Ψ` of `F/↥K` (`Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors`, whose
  one-place faithfulness clause is available) therefore kills every one-place idèle at `𝔭` (`hΨz`).
* The compatibility of the local factors in the tower `↥K ⊆ F ≤ E`
  (`Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq`, an instance of Artin uniqueness
  plus Čebotarev generation) identifies the local factor of `Φ` at `𝔭` with that of `Ψ`, so `Φ`
  kills the decomposition field (`hcompat`, `hmemF`).
* As `F` has fixing subgroup `D_A` (`IntermediateField.fixingSubgroup_fixedField`), the local factor
  lies in `D_A`, and reading that membership in the image of `SSGRoute.decomp (k := ↥K) A` produces
  the required lift `σ`.

No hypothesis on the ramification of `𝔭` in `E/↥K` is used: the decomposition field `F/↥K` is
unramified *and* residue-degree one at `𝔭` regardless, and the local unit part of the local factor
dies there.
-/

/-- **The decomposition clause of an idèlic Artin map with the reciprocity kernel.**  Let `Φ` be an
idèlic Artin map of the finite abelian extension `E/↥K` (kernel `N_{E/↥K}𝕀_E ⊔ ↥Kˣ` and Frobenius
normalised at every unramified prime), let `A` be a finite place of `Ω` over `k` whose restriction to
`↥K` is the place of the prime `𝔭`, and let `x ∈ (↥K)ˣ`.  Then the local factor
`Φ (onePlace 𝔭 (localImageAt 𝔭 x))` has a lift `σ ∈ Ω ≃ₐ[↥K] Ω` lying in the decomposition group
`SSGRoute.decomp (k := ↥K) A` of `A`. -/
theorem decompLift_of_artinMap {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E))
    (hΦker : Φ.ker =
      NK.GlobalCFT.Idele.normImage ↥K ↥E ⊔ NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hΦfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K, NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
      Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (x : (↥K)ˣ) :
    ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A ∧
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
        Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x)) := by
  classical
  -- ## arithmetic instances for the base and the top field
  haveI hNumK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hNumE : NumberField ↥E :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥K) (K' := Ω) E
  haveI hAlgClK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepK : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- commutativity of `Gal(E/↥K)`
  have hcommE : ∀ a b : ↥E ≃ₐ[↥K] ↥E, a * b = b * a := fun a b => mul_comm' a b
  -- ## the decomposition field `F = E^{D_A}` of `A` inside `E`
  let H : Subgroup (↥E ≃ₐ[↥K] ↥E) :=
    (SSGRoute.decomp (k := ↥K) A).map (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E)
  let F : IntermediateField ↥K ↥E := IntermediateField.fixedField H
  haveI hHnorm : Subgroup.Normal H := Subgroup.normal_of_isMulCommutative H
  have hFfix : F.fixingSubgroup = H := IntermediateField.fixingSubgroup_fixedField H
  haveI hFfd : FiniteDimensional ↥K ↥F := inferInstance
  haveI hFgal : IsGalois ↥K ↥F := inferInstance
  haveI hFnum : NumberField ↥F :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥K) (K' := ↥E) F
  -- the same level, viewed inside `Ω`
  let F' : IntermediateField ↥K Ω := F.map (IsScalarTower.toAlgHom ↥K ↥E Ω)
  have hF'E : F' ≤ E := by
    intro z hz
    obtain ⟨w, _hw, rfl⟩ :=
      (IntermediateField.mem_map (S := F) (f := IsScalarTower.toAlgHom ↥K ↥E Ω)).mp hz
    exact w.2
  haveI hF'fd : FiniteDimensional ↥K ↥F' :=
    Module.Finite.equiv (IntermediateField.equivMap F (IsScalarTower.toAlgHom ↥K ↥E Ω)).toLinearEquiv
  haveI hF'gal : IsGalois ↥K ↥F' :=
    IsGalois.of_algEquiv (IntermediateField.equivMap F (IsScalarTower.toAlgHom ↥K ↥E Ω))
  haveI hF'num : NumberField ↥F' :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥K) (K' := Ω) F'
  -- `A` is a finite place of `↥K`
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    rw [h𝔭]; exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔭
  -- ## `𝔭` splits completely in `F/↥K`
  have hsplit : SSGRoute.IsSplitIn ↥K F' A := by
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨z, hz, rfl⟩ :=
      (IntermediateField.mem_map (S := F) (f := IsScalarTower.toAlgHom ↥K ↥E Ω)).mp hy
    have h1 : σ ((algebraMap ↥E Ω) z) = (algebraMap ↥E Ω) z := by
      have hzmem : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E) σ ∈ H :=
        Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
      rw [← hFfix] at hzmem
      have h2 : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E) σ z = z :=
        (IntermediateField.mem_fixingSubgroup_iff F _).mp hzmem z hz
      have h3 := AlgEquiv.restrictNormalHom_apply (F := ↥K) E σ z
      rw [h2] at h3
      exact h3.symm
    exact h1
  -- ## the local norm subgroup at `𝔭` is everything
  have htop : NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F')
      (NK.GlobalCFT.Place.ofFinite 𝔭) = ⊤ :=
    Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn (K := K) (E := F')
      A hAK 𝔭 h𝔭 hsplit
  -- ## the abelian Artin map of `F'/↥K`
  have hcommF : ∀ a b : ↥F ≃ₐ[↥K] ↥F, a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥F) (E := ↥E) a
    obtain ⟨b', rfl⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥F) (E := ↥E) b
    rw [← map_mul, ← map_mul, hcommE a' b']
  have hcommF' : ∀ a b : ↥F' ≃ₐ[↥K] ↥F', a * b = b * a := by
    intro a b
    let e : ↥F ≃ₐ[↥K] ↥F' := IntermediateField.equivMap F (IsScalarTower.toAlgHom ↥K ↥E Ω)
    let ee := e.autCongr
    obtain ⟨a', rfl⟩ := ee.surjective a
    obtain ⟨b', rfl⟩ := ee.surjective b
    rw [← map_mul, ← map_mul, hcommF a' b']
  obtain ⟨Ψ, hΨker, _hΨnorm, _hΨprin, hΨloc, hΨfrob, _hΨprod⟩ :=
    Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K) (L := ↥F') hcommF'
  -- ## the prime of `↥K` below `A` is `𝔭`
  have hpb : Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA = 𝔭 := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥K) (K := ↥K) ?_
    rw [← Submission.NeukirchUchida.primeOf_spec A
      (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA), h𝔭]
  -- ## the local factor of `x` at `𝔭` is killed by the Artin map of `F'`
  have hΨz : Ψ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x)) = 1 :=
    (hΨloc (NK.GlobalCFT.Place.ofFinite 𝔭) _).mpr (by rw [htop]; exact Subgroup.mem_top _)
  -- ## compatibility of the local factors of `Φ` and `Ψ`
  have hcompat : ∀ y' : ↥F', Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x))
        ⟨(y' : Ω), hF'E y'.2⟩ = ⟨(y' : Ω), hF'E y'.2⟩ := by
    intro y'
    have h1 := Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq (p := 2) k Ω K A hA
      F' E hF'E hcommE Φ hΦker hΦfrob Ψ hΨker hΨfrob x y'
    rw [show Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA E Φ x =
        Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite
            (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA))
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite
            (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA)) x)) from rfl,
      show Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA F' Ψ x =
        Ψ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite
            (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA))
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite
            (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA)) x)) from rfl] at h1
    rw [hpb] at h1
    have h2 : ((Ψ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x))) y'
        : Ω) = (y' : Ω) := by
      rw [hΨz]; rfl
    exact Subtype.ext (h1.trans h2)
  -- ## hence `Φ` kills the decomposition field, and `Gal(E/F) = D_A` produces the lift
  have hmemH : Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x)) ∈ H := by
    have hmemF : Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x))
        ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hy' : (y : Ω) ∈ F' :=
        (IntermediateField.mem_map (S := F) (f := IsScalarTower.toAlgHom ↥K ↥E Ω)).mpr ⟨y, hy, rfl⟩
      have hcoe : (⟨(y : Ω), hF'E hy'⟩ : ↥E) = y := Subtype.ext rfl
      rw [← hcoe]
      exact hcompat ⟨(y : Ω), hy'⟩
    rwa [hFfix] at hmemF
  obtain ⟨σ, hσ, hσres⟩ := Subgroup.mem_map.mp hmemH
  exact ⟨σ, hσ, hσres⟩

/-- **An idèlic Artin map of a finite abelian `E/↥K` whose local factors lie in the decomposition
groups of the places of `Ω` (input (S1) of the escape orthogonality).**

`Work.SSGRoute.ZDataMup.exists_localMap_ofFinite_of_abelian` builds the local Artin map at a finite
place `Q` of `↥K` as `(decompositionSubgroup q).subtype ∘ iso ∘ (local Artin map)`: its *values lie
in the decomposition subgroup* of a prime `q` of `E` above `Q`.  The proof of
`Work.SSGRoute.ZDataMup.localGlobalArtinMap_exists_comm` glues these local maps into one `Φ` with
`Φ ∘ onePlace_v` equal to the local map at `v`, hence value in the decomposition subgroup; the
correspondence between primes `q` of `E` above `𝔭` and places `A` of `Ω` above `𝔭` (via
`A.comap (algebraMap ↥K Ω) = valuationSubringAtPrime ↥K 𝔭`) then converts "stabilises `q`" into
"`σ ∈ decomp (k := ↥K) A`" for a lift `σ ∈ Ω ≃ₐ[↥K] Ω` of the local factor.  The reviewers noted
that clause (a) (the kernel) is *not* delivered by `localGlobalArtinMap_exists_comm` and should be
combined with `ZConstruction.exists_abelianArtin_localFactors` (or any Artin map of the reciprocity
lane) via Artin uniqueness. -/
theorem exists_artinMap_with_decompLift {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)] :
    ∃ Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E),
      Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥E ⊔ NK.GlobalCFT.Idele.principalSubgroup ↥K ∧
      (∀ Q : NK.Chebotarev.PrimeIdeal ↥K, NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
        Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q) ∧
      (∀ (A : ValuationSubring Ω) (_hA : SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ x : (↥K)ˣ,
        ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x))) := by
  -- the idèlic Artin map of the reciprocity lane, with its kernel and its Frobenius normalisation
  have hcommE : ∀ a b : ↥E ≃ₐ[↥K] ↥E, a * b = b * a := fun a b => mul_comm' a b
  obtain ⟨Φ, hΦker, _hΦnorm, _hΦprin, _hΦloc, hΦfrob, _hΦprod⟩ :=
    Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K) (L := ↥E) hcommE
  exact ⟨Φ, hΦker, hΦfrob, fun A hA 𝔭 h𝔭 x =>
    decompLift_of_artinMap (K := K) (E := E) Φ hΦker hΦfrob A hA 𝔭 h𝔭 x⟩

end Work.SSGRoute.N2v2
