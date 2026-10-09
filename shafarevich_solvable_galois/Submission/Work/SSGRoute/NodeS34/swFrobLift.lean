import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq
import Submission.NK.Chebotarev.IsFrobAtStabilizes
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.Work.SSGRoute.ZDataTwo.finPairEqZeroOfKillsInertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS34

/-!
# The pinned Frobenius lift at a place of `Ω` over an unramified prime of `K`

Given a finite Galois level `K/k` inside `Ω` and a finite abelian level `M/K` inside `Ω`, a finite
place `A` of `Ω` over an unramified prime `𝔮` of `K`, there is an element `ψ ∈ Gal(Ω/K) ∩ D_A`
whose image in `Gal(M/K)` is the Frobenius at `𝔮`.

The construction is: let `P` be the prime of `𝓞 M` below the place `A`; since `M/K` is abelian and
`𝔮` is unramified, the Frobenius `frobAtPrime 𝔮` is a Frobenius at *every* prime of `M` above `𝔮`,
in particular at `P`, hence stabilises `P`, i.e. lies in the stabiliser of the valuation ring
`A ∩ M`.  The restriction map on stabilisers of valuation subrings,
`Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq`, then lifts it to an element
of `Gal(Ω/K)` stabilising `A` itself.
-/

theorem swFrobLift {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (hcomm : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔮 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮)
    (hunr : ∀ P : NK.Chebotarev.PrimeIdeal ↥M, P.asIdeal.LiesOver 𝔮.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) = 1) :
    ∃ (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ K.fixingSubgroup),
      ψ ∈ SSGRoute.decomp k A ∧
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥M
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, hψ⟩) =
        NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮 := by
  -- `Ω` is an algebraic (separable) closure of `↥K` as well.
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepK : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- The trace of `A` on `↥K` is a proper place.
  have hCK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    rw [h𝔮]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔮
  -- The prime `P` of `𝓞 M` below the place `A`.
  let P : NK.Chebotarev.PrimeIdeal ↥M := Work.SSGRoute.levelPrime ↥K Ω A hCK M
  have hPspec : A.comap (algebraMap ↥M Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P :=
    NK.Reconstruct.primeOfLevel_spec A M (NK.Reconstruct.comap_level_ne_top hCK M)
  have hPlies : P.asIdeal.LiesOver 𝔮.asIdeal :=
    Work.SSGRoute.ZDataTwo.levelPrime_liesOver_of_comap_eq ↥K Ω A hCK 𝔮 h𝔮 M
  -- The Frobenius `frobAtPrime 𝔮` is a Frobenius at the prime `P`.
  obtain ⟨σ₀, hσ₀⟩ := NK.Chebotarev.exists_isFrobAt (K := ↥K) (L := ↥M) 𝔮 P hPlies
  have hfrob : NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮 = σ₀ :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔮 hunr σ₀).mp ⟨P, hPlies, hσ₀⟩
  have hFrobP : NK.Chebotarev.IsFrobAt P
      (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮) := by
    rw [hfrob]
    exact hσ₀
  -- A Frobenius at `P` stabilises `P`, hence the valuation ring `A ∩ M`.
  have hstabP : NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮 ∈
      Submission.NeukirchUchida.Local.decompositionSubgroup (K := ↥K) P := by
    rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup,
      IsDedekindDomain.HeightOneSpectrum.ext_iff,
      Submission.NeukirchUchida.Local.placeSmul_asIdeal]
    exact NK.Chebotarev.IsFrobAtStabilizes hFrobP
  have hτ : NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮 ∈
      MulAction.stabilizer (↥M ≃ₐ[↥K] ↥M) (A.comap (algebraMap ↥M Ω)) := by
    rw [hPspec]
    exact (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
      (K := ↥K) P _).mpr hstabP
  -- Lift it through the restriction map on the stabilisers of valuation subrings.
  obtain ⟨σ, hσA, hσres⟩ :=
    Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq
      (F := ↥K) (K' := Ω) A hCK M (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮) hτ
  have hσA' : σ • A = A := MulAction.mem_stabilizer_iff.mp hσA
  -- Descend along `k → ↥K`.
  have hfix : σ.restrictScalars k ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : σ (algebraMap ↥K Ω (⟨x, hx⟩ : ↥K)) = algebraMap ↥K Ω (⟨x, hx⟩ : ↥K) :=
      σ.commutes (⟨x, hx⟩ : ↥K)
    rw [AlgEquiv.restrictScalars_apply]
    simpa using hx'
  refine ⟨σ.restrictScalars k, hfix, ?_, ?_⟩
  · rw [SSGRoute.decomp]
    refine MulAction.mem_stabilizer_iff.mpr ?_
    rw [show σ.restrictScalars k • A = σ • A from rfl, hσA']
  · have hσeq : (IntermediateField.fixingSubgroupEquiv K)
        ⟨σ.restrictScalars k, hfix⟩ = σ := by
      apply AlgEquiv.ext
      intro x
      rfl
    rw [hσeq]
    exact hσres

end Work.SSGRoute.NodeS34
