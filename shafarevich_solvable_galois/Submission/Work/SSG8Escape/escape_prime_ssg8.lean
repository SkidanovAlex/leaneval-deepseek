import Mathlib
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.EscapeCoreLib.placeFrobenius_of_compat
import Submission.Work.SSGRoute.EscapeCoreLib.memGesUOfIsFrobAtPrime
import Submission.Work.SSGRoute.EscapeCoreLib.escapePrimeFrobAtPrime
import Submission.Work.SSGRoute.EscapeCoreLib.card_residue_eq_of_isFrobAt_one
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT
open Work.SSGRoute

namespace Work.SSG8Escape

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The escape place, with the prescribed Frobenius at the `↥K`-level, the complete splitting
in `Λ`, the avoidance of the classes of `T`, and unramifiedness in `↥M/↥K`.**

Given a finite Galois extension `K/k` of number fields inside `Ω`, a finite Galois extension
`M/↥K`, a finite Galois extension `Λ/k` with `K ≤ Λ`, a finite Galois level `L/k` containing `K`,
`M` and `Λ`, and an element `τ ∈ G_k` acting on `M` by `α` and fixing `Λ`, there are a prime `p`
of `k`, a `↥K`-prime `𝔮` and a finite place `Q` of `Ω` above `p` such that

* `Q` is a finite place of `k`, completely split in `Λ`, not conjugate to any element of `T`, and
  `Q` lies over `𝔮`;
* `𝔮` is unramified in `M/↥K` and `α` is a Frobenius element at `𝔮` in `M/↥K`.

This is `EscapeCoreLib.escapePrimeFrobAtPrime` with the additional conclusion of unramifiedness
(the bad set of the Čebotarev step contains the traces on `k` of the primes of `↥K` ramified in
`M/↥K`). -/
theorem escapePlace_ssg8
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) (hML : ∀ x : Ω, x ∈ M → x ∈ L) (hΛL : Λ ≤ L) (hKΛ : K ≤ Λ)
    (τ : Ω ≃ₐ[k] Ω) (α : ↥M ≃ₐ[↥K] ↥M)
    (hτM : ∀ x : ↥M, τ (x : Ω) = ((α x : ↥M) : Ω))
    (hτΛ : τ ∈ Λ.fixingSubgroup)
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (T : Finset (ValuationSubring Ω)) :
    ∃ (Q : ValuationSubring Ω) (p : NK.Chebotarev.PrimeIdeal k) (𝔮 : NK.Chebotarev.PrimeIdeal ↥K),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k Λ Q ∧
      (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A Q) ∧
      Q.comap (algebraMap k Ω) = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p ∧
      (∀ A ∈ T, A.comap (algebraMap k Ω) ≠
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p) ∧
      Q.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 ∧
      NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M) 𝔮 α := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  haveI hnumL : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI hnumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hnumΛ : NumberField ↥Λ := NumberField.of_module_finite k ↥Λ
  -- ### algebra structures for the towers
  letI : Algebra ↥K ↥L := (Subsemiring.inclusion hKL).toAlgebra
  haveI htowKLk : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowKLΩ : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowZKL : IsScalarTower ℤ ↥K ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hfdKL : FiniteDimensional ↥K ↥L := Module.Finite.of_restrictScalars_finite k ↥K ↥L
  letI : Algebra ↥M ↥L := (Subsemiring.inclusion hML).toAlgebra
  haveI htowMLΩ : IsScalarTower ↥M ↥L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowZML : IsScalarTower ℤ ↥M ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowKML : IsScalarTower ↥K ↥M ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowZMK : IsScalarTower ℤ ↥K ↥M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra ↥Λ ↥L := (Subsemiring.inclusion hΛL).toAlgebra
  haveI htowΛLk : IsScalarTower k ↥Λ ↥L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htowΛLΩ : IsScalarTower ↥Λ ↥L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hfdΛL : FiniteDimensional ↥Λ ↥L := Module.Finite.of_restrictScalars_finite k ↥Λ ↥L
  -- ### the bad set of primes of `k`
  set Bad₁ : Set (NK.Chebotarev.PrimeIdeal k) :=
    {p | ∃ A ∈ T, A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p} with hBad₁def
  set Bad₂ : Set (NK.Chebotarev.PrimeIdeal k) :=
    {p | ∃ P : NK.Chebotarev.PrimeIdeal ↥Λ,
        P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} with hBad₂def
  set Bad₃ : Set (NK.Chebotarev.PrimeIdeal k) :=
    {p | ∃ 𝔪 : NK.Chebotarev.PrimeIdeal ↥M,
        𝔪.asIdeal.LiesOver p.asIdeal ∧
        𝔪.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) ≠ 1} with hBad₃def
  set Bad : Set (NK.Chebotarev.PrimeIdeal k) := ((Bad₁ ∪ Bad₂) ∪ Bad₃) with hBaddef
  have hBad₁fin : Bad₁.Finite := by
    rw [hBad₁def]
    exact Work.SSGRoute.finite_setOf_primeUnder (k := k) (Ω := Ω) T
  have hBad₂fin : Bad₂.Finite := by
    rw [hBad₂def]
    exact Work.SSGRoute.finite_setOf_primeUnder_ramified (k := k) (Ω := Ω) Λ
  have hBad₃fin : Bad₃.Finite := by
    rw [hBad₃def]
    have hS : {𝔪 : NK.Chebotarev.PrimeIdeal ↥M |
        𝔪.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) ≠ 1}.Finite :=
      Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := ↥K) (L := ↥M)
    refine Set.Finite.of_finite_image (f := fun p : NK.Chebotarev.PrimeIdeal k => p.asIdeal) ?_ ?_
    · refine (hS.image (fun 𝔪 => 𝔪.asIdeal.under (NumberField.RingOfIntegers k))).subset ?_
      rintro β ⟨p, ⟨𝔪, hlies, hram⟩, rfl⟩
      exact ⟨𝔪, hram, hlies.over.symm⟩
    · intro p _ q _ hpq
      exact IsDedekindDomain.HeightOneSpectrum.ext hpq
  have hBad : Bad.Finite := by
    rw [hBaddef]
    exact (hBad₁fin.union hBad₂fin).union hBad₃fin
  -- ### Čebotarev with the prescribed Frobenius at the level `L`
  obtain ⟨p, hpBad, hFrob⟩ :=
    Work.SSGRoute.exists_isFrobAtPrime_notMem_finite hc Bad hBad L (SSGRoute.res k L τ)
  obtain ⟨P, hPlies, hPfrob⟩ := hFrob
  -- the components of `p ∉ Bad`
  have hpBad₁ : p ∉ Bad₁ := fun h => hpBad (by rw [hBaddef]; exact Or.inl (Or.inl h))
  have hpBad₂ : ∀ PΛ : NK.Chebotarev.PrimeIdeal ↥Λ, PΛ.asIdeal.LiesOver p.asIdeal →
      PΛ.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro PΛ hPΛ
    by_contra hne
    exact hpBad (by rw [hBaddef]; exact Or.inl (Or.inr ⟨PΛ, hPΛ, hne⟩))
  have hpBad₃ : ∀ 𝔪 : NK.Chebotarev.PrimeIdeal ↥M, 𝔪.asIdeal.LiesOver p.asIdeal →
      𝔪.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) = 1 := by
    intro 𝔪 h𝔪
    by_contra hne
    exact hpBad (by rw [hBaddef]; exact Or.inr ⟨𝔪, h𝔪, hne⟩)
  -- ### the place `Q` over `P`
  obtain ⟨Q, hQcomapL⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := ↥L) (K' := Ω) P
  have hQp : Q.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p := by
    have h1 : Q.comap (algebraMap k Ω) =
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P).comap
          (algebraMap k ↥L) := by
      rw [← hQcomapL]
      exact (ValuationSubring.comap_comap Q (algebraMap ↥L Ω) (algebraMap k ↥L)).symm
    rw [h1]
    exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime p P hPlies
  have hQne : Q.comap (algebraMap k Ω) ≠ ⊤ := by
    rw [hQp]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := k) p
  have hQfin : SSGRoute.IsFinPlace k Q := hQne
  have hpT : ∀ A ∈ T, A.comap (algebraMap k Ω) ≠
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p := by
    intro A hA h
    exact hpBad₁ ⟨A, hA, h⟩
  -- ### the `↥K`-prime `𝔮` below `Q`
  set 𝔮 : NK.Chebotarev.PrimeIdeal ↥K := P.under (NumberField.RingOfIntegers ↥K) with h𝔮def
  have h𝔮 : 𝔮.asIdeal = P.asIdeal.under (NumberField.RingOfIntegers ↥K) := by
    rw [h𝔮def, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  have hliesK : P.asIdeal.LiesOver 𝔮.asIdeal := by
    rw [h𝔮]
    exact ⟨rfl⟩
  have hQ𝔮 : Q.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 := by
    have h1 : Q.comap (algebraMap ↥K Ω) =
        (Q.comap (algebraMap ↥L Ω)).comap (algebraMap ↥K ↥L) :=
      (ValuationSubring.comap_comap Q (algebraMap ↥L Ω) (algebraMap ↥K ↥L)).symm
    rw [h1, hQcomapL, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime 𝔮 P hliesK]
  -- ### the avoidance clause
  have havoid : ∀ C ∈ T, ¬ SSGRoute.IsConjPlace k C Q := by
    intro C hC hconj
    refine not_isConjPlace_of_notMem_primeUnder (k := k) (Ω := Ω) T Q p hQp ?_ C hC hconj
    intro hmem
    exact hpBad₁ hmem
  -- ### complete splitting in `Λ`
  have hresΛ : SSGRoute.res k Λ τ = 1 := by
    rw [show SSGRoute.res k Λ τ = AlgEquiv.restrictNormalHom Λ τ from rfl,
      ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff Λ τ).mp hτΛ x hx
  have hsplit : SSGRoute.IsSplitIn k Λ Q := by
    have hQΛ : Q.comap (algebraMap ↥Λ Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ
          (P.under (NumberField.RingOfIntegers ↥Λ)) := by
      have hliesΛ : P.asIdeal.LiesOver (P.under (NumberField.RingOfIntegers ↥Λ)).asIdeal := by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
        exact ⟨rfl⟩
      have h1 : Q.comap (algebraMap ↥Λ Ω) =
          (Q.comap (algebraMap ↥L Ω)).comap (algebraMap ↥Λ ↥L) :=
        (ValuationSubring.comap_comap Q (algebraMap ↥L Ω) (algebraMap ↥Λ ↥L)).symm
      rw [h1, hQcomapL, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
        (P.under (NumberField.RingOfIntegers ↥Λ)) P hliesΛ]
    have hliesΛ' : (P.under (NumberField.RingOfIntegers ↥Λ)).asIdeal.LiesOver p.asIdeal := by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      refine ⟨?_⟩
      rw [Ideal.under_under]
      exact hPlies.over
    have heΛ : (P.under (NumberField.RingOfIntegers ↥Λ)).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers k) = 1 := hpBad₂ _ hliesΛ'
    have hfrobΛ : NK.Chebotarev.IsFrobAt (K := k) (L := ↥Λ)
        (P.under (NumberField.RingOfIntegers ↥Λ)) (SSGRoute.res k Λ τ) := by
      have h := NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := k) (E := ↥Λ) (M := ↥L)
        P (SSGRoute.res k L τ) hPfrob
      have hcompat := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply ↥Λ ↥L (F := k) (K₃ := Ω) τ
      have hres : AlgEquiv.restrictNormalHom ↥Λ (SSGRoute.res k L τ) =
          AlgEquiv.restrictNormalHom ↥Λ τ := by
        rw [show SSGRoute.res k L τ = AlgEquiv.restrictNormalHom ↥L τ from rfl, hcompat]
      rw [show SSGRoute.res k Λ τ = AlgEquiv.restrictNormalHom ↥Λ τ from rfl, ← hres]
      exact h
    have hdec : Submission.NeukirchUchida.Local.decompositionSubgroup (K := k)
        (P.under (NumberField.RingOfIntegers ↥Λ)) = ⊥ := by
      rw [NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt (K := k) (N := ↥Λ)
        (P.under (NumberField.RingOfIntegers ↥Λ)) (SSGRoute.res k Λ τ) heΛ hfrobΛ, hresΛ]
      exact Subgroup.zpowers_one_eq_bot
    have hbridgeΛ := Work.SSGRoute.map_res_decomp_eq_stabilizer_valuationRing (k := k) (Ω := Ω)
      Λ Q hQne (P.under (NumberField.RingOfIntegers ↥Λ)) hQΛ
    have hstab : MulAction.stabilizer (↥Λ ≃ₐ[k] ↥Λ)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ
          (P.under (NumberField.RingOfIntegers ↥Λ))) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      rw [Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup,
        hdec] at hx
      exact hx
    rw [SSGRoute.IsSplitIn]
    intro δ hδ
    rw [← IntermediateField.restrictNormalHom_ker Λ, MonoidHom.mem_ker]
    have hmem : SSGRoute.res k Λ δ ∈ (SSGRoute.decomp k Q).map (SSGRoute.res k Λ) :=
      Subgroup.mem_map_of_mem _ hδ
    rw [hbridgeΛ, hstab] at hmem
    simpa using hmem
  -- ### unramifiedness of `𝔮` in `M/↥K`
  have hQ𝔮lies : 𝔮.asIdeal.LiesOver p.asIdeal := by
    rw [h𝔮]
    exact ⟨hPlies.over⟩
  have hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 := by
    intro 𝔪 h𝔪
    haveI : 𝔪.asIdeal.LiesOver p.asIdeal :=
      ⟨by rw [hQ𝔮lies.over, h𝔪.over, Ideal.under_under 𝔪.asIdeal]⟩
    exact hpBad₃ 𝔪 inferInstance
  -- ### the Frobenius clause
  have hfrob : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M) 𝔮 α := by
    refine ⟨P.under (NumberField.RingOfIntegers ↥M), ?_, ?_⟩
    · have hPM : (P.under (NumberField.RingOfIntegers ↥M)).asIdeal
          = P.asIdeal.under (NumberField.RingOfIntegers ↥M) := by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      have hunder : (P.under (NumberField.RingOfIntegers ↥M)).asIdeal.under
            (NumberField.RingOfIntegers ↥K) = 𝔮.asIdeal := by
        rw [hPM, Ideal.under_under, h𝔮]
      refine ⟨?_⟩
      rw [hunder]
    · rw [NK.Chebotarev.isFrobAt_def]
      intro x
      have hPM : (P.under (NumberField.RingOfIntegers ↥M)).asIdeal
          = P.asIdeal.under (NumberField.RingOfIntegers ↥M) := by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      have hunder : (P.under (NumberField.RingOfIntegers ↥M)).asIdeal.under
            (NumberField.RingOfIntegers ↥K) = 𝔮.asIdeal := by
        rw [hPM, Ideal.under_under, h𝔮]
      rw [hunder, hPM]
      -- the Frobenius of `𝔮` in `K/k` is trivial
      have hfrobK : NK.Chebotarev.IsFrobAt (K := k) (L := ↥K) 𝔮 (1 : ↥K ≃ₐ[k] ↥K) := by
        haveI : Normal k ↥K := inferInstance
        have h := NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := k) (E := ↥K) (M := ↥L) P
          (SSGRoute.res k L τ) hPfrob
        have hres : AlgEquiv.restrictNormalHom ↥K (SSGRoute.res k L τ) = 1 := by
          have hcompat := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply ↥K ↥L (F := k)
            (K₃ := Ω) τ
          rw [show SSGRoute.res k L τ = AlgEquiv.restrictNormalHom ↥L τ from rfl, ← hcompat]
          have hτK : SSGRoute.res k K τ = 1 := by
            rw [show SSGRoute.res k K τ = AlgEquiv.restrictNormalHom K τ from rfl,
              ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
              IntermediateField.mem_fixingSubgroup_iff]
            intro z hz
            exact (IntermediateField.mem_fixingSubgroup_iff Λ τ).mp hτΛ z (hKΛ hz)
          rw [hτK]
        rw [hres] at h
        exact h
      have hcard := EscapeCoreLib.inertiaDeg_eq_one_of_isFrobAt_one (k := k) (K := ↥K) 𝔮 hfrobK
      have hcardPow := Ideal.cardQuot_pow_inertiaDeg (𝔮.asIdeal.under (NumberField.RingOfIntegers k))
        𝔮.asIdeal
      rw [hcard, pow_one] at hcardPow
      have hexp : Nat.card (NumberField.RingOfIntegers ↥K ⧸ 𝔮.asIdeal) =
          Nat.card (NumberField.RingOfIntegers k ⧸ p.asIdeal) := by
        have h1 : 𝔮.asIdeal.under (NumberField.RingOfIntegers k) = p.asIdeal := by
          rw [h𝔮, Ideal.under_under]
          exact hPlies.over.symm
        rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← h1, ← hcardPow]
      -- the comparison of the two `galRestrict` values (in `Ω`)
      have h1 : (((algebraMap (NumberField.RingOfIntegers ↥L) ↥L
            (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers ↥L)
              (galRestrict (NumberField.RingOfIntegers ↥K) ↥K ↥M (NumberField.RingOfIntegers ↥M)
                α x))) : ↥L) : Ω)
          = τ ((algebraMap (NumberField.RingOfIntegers ↥M) ↥M x) : Ω) := by
        rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M)
              (NumberField.RingOfIntegers ↥L) ↥L,
          IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M ↥L,
          algebraMap_galRestrict_apply]
        exact (hτM _).symm
      have h2 : (((algebraMap (NumberField.RingOfIntegers ↥L) ↥L
            (galRestrict (NumberField.RingOfIntegers k) k ↥L (NumberField.RingOfIntegers ↥L)
              (SSGRoute.res k L τ)
              (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers ↥L) x))) : ↥L) : Ω)
          = τ ((algebraMap (NumberField.RingOfIntegers ↥M) ↥M x) : Ω) := by
        rw [algebraMap_galRestrict_apply,
          show (((SSGRoute.res k L τ) (algebraMap (NumberField.RingOfIntegers ↥L) ↥L
                (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers ↥L) x)) : ↥L) : Ω)
              = τ (((algebraMap (NumberField.RingOfIntegers ↥L) ↥L
                (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers ↥L) x)) : ↥L) : Ω)
              from AlgEquiv.restrictNormal_commutes τ ↥L _,
          ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M)
            (NumberField.RingOfIntegers ↥L) ↥L,
          IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M ↥L]
        rfl
      have hkey : algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers ↥L)
          (galRestrict (NumberField.RingOfIntegers ↥K) ↥K ↥M (NumberField.RingOfIntegers ↥M) α x)
          = galRestrict (NumberField.RingOfIntegers k) k ↥L (NumberField.RingOfIntegers ↥L)
              (SSGRoute.res k L τ)
              (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers ↥L) x) := by
        apply NumberField.RingOfIntegers.ext
        exact Subtype.ext (h1.trans h2.symm)
      rw [Ideal.mem_under (NumberField.RingOfIntegers ↥M) P.asIdeal, map_sub, map_pow, hkey]
      have h := hPfrob.mk_apply hPlies
        (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers ↥L) x)
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [map_sub, map_pow, hexp, h, sub_self]
  exact ⟨Q, p, 𝔮, hQfin, hsplit, havoid, hQp, hpT, hQ𝔮, hunr, hfrob⟩

theorem escape_prime_ssg8 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'below : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, (∃ τ ∈ K.fixingSubgroup, τ • A = B) → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (hc : NK.Reconstruct.ChebotarevDensityInput k Ω)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (hM : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M = Work.SSGRoute.SSG8Escape.gesUPow ↥K p T')
    (hcomm : ∀ a b : (↥M ≃ₐ[↥K] ↥M), a * b = b * a)
    (art : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hker : art.ker = NK.GlobalCFT.Idele.normImage ↥K ↥M ⊔ NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hα : art (NK.NUV2.RouteB.RayModulus.fracIdele
      (Work.SSGRoute.tFreePart (K := ↥K) T' a)) = α)
    (hαfix : ∀ x : ↥M, ((x : Ω) ∈ (L₁ ⊔ L₂)) → α x = x) :
    ∃ (Q : ValuationSubring Ω) (𝔮 : NK.Chebotarev.PrimeIdeal ↥K),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (L₁ ⊔ L₂) Q ∧ 𝔮 ∉ T' ∧
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 ∧
      Q.comap (algebraMap ↥K Ω) = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ Q) ∧
      NK.GlobalCFT.IdeleClassGroup.mk ↥K (NK.HeckeL.ideleOfPrime ↥K 𝔮) *
        NK.GlobalCFT.IdeleClassGroup.mk ↥K
          (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)) ∈
        Work.SSGRoute.SSG8Escape.gesUPow ↥K p T' := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  -- `α⁻¹` also fixes `M ⊓ (L₁ ⊔ L₂)` pointwise
  have hα'inv : ∀ x : ↥M, ((x : Ω) ∈ (L₁ ⊔ L₂)) → α⁻¹ x = x := by
    intro x hx
    have h := hαfix x hx
    have h2 : α⁻¹ x = α⁻¹ (α x) := (congrArg (fun y => α⁻¹ y) h).symm
    rw [h2]
    exact α.symm_apply_apply x
  have hKΛ : K ≤ L₁ ⊔ L₂ := le_trans hKL₁ le_sup_left
  haveI hfdΛ : FiniteDimensional k ↥(L₁ ⊔ L₂) := IntermediateField.finiteDimensional_sup L₁ L₂
  haveI hgalΛ : IsGalois k ↥(L₁ ⊔ L₂) := inferInstance
  -- ### Step 1: a finite Galois extension of `k` containing `K`, `M` and `L₁ ⊔ L₂`
  let Mk : IntermediateField k Ω := M.restrictScalars k
  have hMk : (Mk : Set Ω) = (M : Set Ω) := IntermediateField.coe_restrictScalars k (E := M)
  haveI hfdMk : FiniteDimensional k Mk := by
    haveI : FiniteDimensional k ↥M := FiniteDimensional.trans k ↥K ↥M
    exact ‹FiniteDimensional k ↥M›
  obtain ⟨L, hLd, hLg, hKL, hMLk, hΛL⟩ :=
    EscapeCoreLib.exists_finiteDimensional_galois_superset K Mk (L₁ ⊔ L₂)
  haveI : FiniteDimensional k L := hLd
  haveI : IsGalois k L := hLg
  have hMLset : ∀ x : Ω, x ∈ M → x ∈ L := fun x hx => hMLk (by
    show x ∈ (Mk : Set Ω); rw [hMk]; exact hx)
  -- ### Step 2: transport `M` and `L₁ ⊔ L₂` into the `↥K`-extension `LK`
  let LK : IntermediateField ↥K Ω := EscapeCoreLib.baseChange K L hKL
  haveI htow_k_LK_Ω : IsScalarTower k ↥LK Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI htow_k_K_LK : IsScalarTower k ↥K ↥LK := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois k ↥LK := IsGalois.of_algEquiv (EscapeCoreLib.baseChangeAlgEquiv K L hKL)
  haveI : IsGalois ↥K LK := EscapeCoreLib.isGalois_baseChange K L hKL
  haveI : FiniteDimensional k ↥LK := EscapeCoreLib.finiteDimensional_baseChange K L hKL
  haveI : FiniteDimensional ↥K ↥LK := Module.Finite.of_restrictScalars_finite k ↥K ↥LK
  let NKf : IntermediateField ↥K Ω := EscapeCoreLib.baseChange K (L₁ ⊔ L₂) hKΛ
  haveI : IsGalois ↥K NKf := EscapeCoreLib.isGalois_baseChange K (L₁ ⊔ L₂) hKΛ
  haveI : FiniteDimensional k ↥NKf := EscapeCoreLib.finiteDimensional_baseChange K (L₁ ⊔ L₂) hKΛ
  haveI : FiniteDimensional ↥K ↥NKf := Module.Finite.of_restrictScalars_finite k ↥K ↥NKf
  have hMLK : M ≤ LK := fun x hx => (EscapeCoreLib.mem_baseChange K L hKL).mpr (hMLk (by
    show x ∈ (Mk : Set Ω); rw [hMk]; exact hx))
  have hNKLK : NKf ≤ LK := fun x hx =>
    (EscapeCoreLib.mem_baseChange K L hKL).mpr (hΛL ((EscapeCoreLib.mem_baseChange K (L₁ ⊔ L₂) hKΛ).mp hx))
  let ML : IntermediateField ↥K ↥LK := M.comap (IsScalarTower.toAlgHom ↥K ↥LK Ω)
  let NLc : IntermediateField ↥K ↥LK := NKf.comap (IsScalarTower.toAlgHom ↥K ↥LK Ω)
  haveI : IsGalois ↥K ML := EscapeCoreLib.isGalois_comap_of_le_over K LK M hMLK
  haveI : IsGalois ↥K NLc := EscapeCoreLib.isGalois_comap_of_le_over K LK NKf hNKLK
  haveI : FiniteDimensional ↥K ↥ML :=
    FiniteDimensional.of_injective (EscapeCoreLib.comapAlgEquiv K LK M hMLK).symm.toLinearEquiv.toLinearMap
      (EscapeCoreLib.comapAlgEquiv K LK M hMLK).symm.injective
  haveI : FiniteDimensional ↥K ↥NLc :=
    FiniteDimensional.of_injective (EscapeCoreLib.comapAlgEquiv K LK NKf hNKLK).symm.toLinearEquiv.toLinearMap
      (EscapeCoreLib.comapAlgEquiv K LK NKf hNKLK).symm.injective
  -- ### Step 3: extend `α⁻¹` to a `↥K`-automorphism of `LK` fixing `NLc`
  let e := EscapeCoreLib.comapAlgEquiv K LK M hMLK
  let α' : ↥ML ≃ₐ[↥K] ↥ML := e.symm.trans ((α⁻¹).trans e)
  have hα'fix : ∀ x : ↥ML, ((x : ↥LK) ∈ NLc) → (((α' x : ↥ML) : ↥LK)) = (x : ↥LK) := by
    intro x hx
    refine Subtype.ext ?_
    have hxN : ((x : ↥LK) : Ω) ∈ NKf := hx
    exact EscapeCoreLib.comapAlgEquiv_transport K LK M NKf hMLK (α⁻¹)
      (fun y hy => congrArg (fun z : ↥M => (z : Ω))
        (hα'inv y ((EscapeCoreLib.mem_baseChange K (L₁ ⊔ L₂) hKΛ).mp hy))) x hxN
  obtain ⟨g, hgML, hgNL⟩ :=
    EscapeCoreLib.exists_algEquiv_restrict_eq_of_fixing (K := ↥K) (L := ↥LK) ML NLc α' hα'fix
  -- ### Step 4: lift the `↥K`-automorphism of `LK` to a `k`-automorphism `τ` of `Ω`
  let gk : ↥LK ≃ₐ[k] ↥LK := g.restrictScalars k
  have hgk_apply : ∀ y : ↥LK, gk y = g y := fun y => rfl
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥LK) (E := Ω) gk
  -- ### Step 5: `τ` acts as `α⁻¹` on `M` and fixes `L₁ ⊔ L₂`
  have hτN : SSGRoute.res k (L₁ ⊔ L₂) τ = 1 := by
    rw [show SSGRoute.res k (L₁ ⊔ L₂) τ = AlgEquiv.restrictNormalHom ↥(L₁ ⊔ L₂) τ from rfl,
      ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxL : x ∈ L := hΛL hx
    have hxLK : x ∈ LK := (EscapeCoreLib.mem_baseChange K L hKL).mpr hxL
    have hxNK : x ∈ NKf := (EscapeCoreLib.mem_baseChange K (L₁ ⊔ L₂) hKΛ).mpr hx
    have hxNL : (⟨x, hxLK⟩ : ↥LK) ∈ NLc := hxNK
    have hτx : τ x = (((gk ⟨x, hxLK⟩ : ↥LK)) : Ω) := by
      have h1 : ((((AlgEquiv.restrictNormalHom ↥LK τ)) ⟨x, hxLK⟩ : ↥LK) : Ω) = τ x :=
        AlgEquiv.restrictNormal_commutes τ ↥LK ⟨x, hxLK⟩
      have hy : (AlgEquiv.restrictNormalHom ↥LK τ) ⟨x, hxLK⟩ = gk ⟨x, hxLK⟩ :=
        congrArg (fun f => f ⟨x, hxLK⟩) hτ
      rw [← h1, hy]
    have hgx : (((g ⟨x, hxLK⟩ : ↥LK)) : Ω) = x := by
      have h := congrArg (fun (z : ↥LK) => (z : Ω)) (hgNL _ hxNL)
      simpa using h
    rw [hτx, hgk_apply, hgx]
  have hτM : ∀ x : ↥M, τ (x : Ω) = (((α⁻¹) x : ↥M) : Ω) := by
    intro x
    have hxL : (x : Ω) ∈ L := hMLset x x.2
    have hxLK : (x : Ω) ∈ LK := (EscapeCoreLib.mem_baseChange K L hKL).mpr hxL
    have hτx : τ (x : Ω) = (((gk ⟨(x : Ω), hxLK⟩ : ↥LK)) : Ω) := by
      have h1 : ((((AlgEquiv.restrictNormalHom ↥LK τ)) ⟨(x : Ω), hxLK⟩ : ↥LK) : Ω) = τ (x : Ω) :=
        AlgEquiv.restrictNormal_commutes τ ↥LK ⟨(x : Ω), hxLK⟩
      have hy : (AlgEquiv.restrictNormalHom ↥LK τ) ⟨(x : Ω), hxLK⟩ = gk ⟨(x : Ω), hxLK⟩ :=
        congrArg (fun f => f ⟨(x : Ω), hxLK⟩) hτ
      rw [← h1, hy]
    rw [hτx, hgk_apply]
    have hzx : (((e x : ↥ML)) : ↥LK) = ⟨(x : Ω), hxLK⟩ := by
      refine Subtype.ext ?_
      rw [EscapeCoreLib.comapAlgEquiv_coe]
    have hgval : (((g ⟨(x : Ω), hxLK⟩ : ↥LK)) : Ω) = ((((α' (e x) : ↥ML)) : ↥LK) : Ω) := by
      have h1 : g ⟨(x : Ω), hxLK⟩ = ((α' (e x) : ↥ML) : ↥LK) := by
        rw [← hzx]
        exact hgML (e x)
      exact congrArg (fun (z : ↥LK) => (z : Ω)) h1
    rw [hgval]
    have hα'x : α' (e x) = e ((α⁻¹) x) := by
      simp only [α', AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rw [hα'x]
    exact EscapeCoreLib.comapAlgEquiv_coe K LK M hMLK ((α⁻¹) x)
  have hτΛ : τ ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 : τ.restrictNormal ↥(L₁ ⊔ L₂) = 1 := by
      rw [show SSGRoute.res k (L₁ ⊔ L₂) τ = τ.restrictNormal ↥(L₁ ⊔ L₂) from rfl] at hτN
      exact hτN
    exact (AlgEquiv.restrictNormal_eq_one_iff (L₁ ⊔ L₂) τ).mp h1 x hx
  -- ### Step 6: the escape place
  obtain ⟨Q, pp, 𝔮, hQfin, hsplit, havoid, hQp, hpT, hQ𝔮, hunr, hF⟩ :=
    escapePlace_ssg8 k Ω K M (L₁ ⊔ L₂) L hKL hMLset hΛL hKΛ τ α⁻¹ hτM hτΛ hc T
  refine ⟨Q, 𝔮, hQfin, hsplit, ?_, hunr, hQ𝔮, ?_, ?_⟩
  · -- `𝔮 ∉ T'`
    intro h𝔮T'
    obtain ⟨A, hA, hA𝔮⟩ := hT'below 𝔮 h𝔮T'
    have h1 : A.comap (algebraMap k Ω) =
        (A.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) :=
      (ValuationSubring.comap_comap A (algebraMap ↥K Ω) (algebraMap k ↥K)).symm
    have h2 : Q.comap (algebraMap k Ω) =
        (Q.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) :=
      (ValuationSubring.comap_comap Q (algebraMap ↥K Ω) (algebraMap k ↥K)).symm
    have hcomap : A.comap (algebraMap k Ω) = Q.comap (algebraMap k Ω) := by
      rw [h1, h2, hA𝔮, hQ𝔮]
    exact hpT A hA (by rw [hcomap, hQp])
  · -- the `K`-conjugacy clause
    intro A hA τ' hτ' hτ'A
    exact havoid A hA ⟨τ', hτ'A⟩
  · -- the class membership
    exact EscapeCoreLib.memGesUOfIsFrobAtPrime (↥M) hcomm
      (Work.SSGRoute.SSG8Escape.gesUPow ↥K p T') hM art hker hfrob
      (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      α hα 𝔮 hunr hF

end Work.SSG8Escape
