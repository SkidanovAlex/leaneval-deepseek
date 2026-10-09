import Mathlib
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup

open scoped Pointwise

/-- **The prime–place bridge, in the direction needed to *produce* a Frobenius lift.**

Let `L|k` be a finite Galois level of the separable closure `Ω` of the number field `k` and let `A`
be a finite place of `Ω` whose trace on `L` is the valuation ring of the prime `P` of `𝓞 L`.  If
`σ ∈ Gal(L|k)` is an arithmetic Frobenius at `P`, then `σ` is the restriction of some
`g ∈ decomp k A`:

  `res k L g = σ`  with  `g • A = A`.

This is the surjectivity half of `Work.SSGRoute.map_res_decomp_eq_stabilizer_valuationRing`
(`res k L` maps `decomp k A` *onto* the stabiliser of `P`) applied to the fact that a Frobenius
element fixes its own prime (`NK.Chebotarev.IsFrobAtStabilizes`). -/
theorem exists_mem_decomp_res_eq_of_isFrobAt
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hP : A.comap (algebraMap ↥L Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P)
    (σ : ↥L ≃ₐ[k] ↥L) (hσ : NK.Chebotarev.IsFrobAt P σ) :
    ∃ g : Ω ≃ₐ[k] Ω, g ∈ SSGRoute.decomp k A ∧ SSGRoute.res k L g = σ := by
  classical
  have hnumL : NumberField ↥L := inferInstance
  -- the Frobenius stabilises the valuation ring of `P`
  have hstab : σ ∈ MulAction.stabilizer Gal(↥L/k)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P) := by
    rw [Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup]
    rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup]
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [Submission.NeukirchUchida.Local.placeSmul_asIdeal]
    exact NK.Chebotarev.IsFrobAtStabilizes hσ
  -- the prime–place bridge: `res k L (decomp k A) = stabiliser of the valuation ring of P`
  have hbridge := Work.SSGRoute.map_res_decomp_eq_stabilizer_valuationRing
    (k := k) (Ω := Ω) L A hA P hP
  have hmem : σ ∈ (SSGRoute.decomp k A).map (SSGRoute.res k L) := by
    rw [hbridge]; exact hstab
  obtain ⟨g, hgD, hgres⟩ := Subgroup.mem_map.mp hmem
  exact ⟨g, hgD, hgres⟩

/-- **A split place realises the Frobenius of any finite Galois level.**

`k` a number field, `Ω` an algebraic closure, `K`, `L` finite Galois levels of `Ω|k`, `A` a finite
place of `Ω` lying over the prime `𝔭` of `k` which is completely split in `K|k`
(`IsSplitIn k K A`, i.e. `decomp k A ≤ K.fixingSubgroup`) and unramified in `L|k`
(`hunrL`; in fact this hypothesis is not needed for the construction below).

Then some `g ∈ decomp k A ⊓ K.fixingSubgroup` restricts to a Frobenius element of `L|k` at `𝔭`:

  `IsFrobAtPrime 𝔭 (res k L g)`.

The content is the prime–place bridge: `res k L` maps the decomposition group of `A` *onto* the
stabiliser of the prime `P` of `𝓞 L` below `A`, and a Frobenius at `P` exists
(`NK.Chebotarev.exists_isFrobAt`) and lies in that stabiliser
(`NK.Chebotarev.IsFrobAtStabilizes`).  Unramifiedness is *not* used: uniqueness of the Frobenius at
`P` only holds when `P` is unramified over `𝔭`, but producing a lift of one Frobenius at `P` needs
nothing beyond the surjectivity of the restriction map on decomposition groups. -/
theorem exists_isFrobAtPrime_split {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hAsplit : SSGRoute.IsSplitIn k K A)
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭) :
    ∃ g : Ω ≃ₐ[k] Ω, g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup ∧
      NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (SSGRoute.res k L g) := by
  classical
  haveI : IsSepClosure k Ω := inferInstance
  haveI hnumL : NumberField ↥L := inferInstance
  haveI hnormL : Normal k ↥L := inferInstance
  -- the prime of `𝓞 L` below the place `A`
  set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) :=
    Work.SSGRoute.levelPrime k Ω A hA L with hPdef
  have hPspec : A.comap (algebraMap ↥L Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P :=
    NK.Reconstruct.primeOfLevel_spec A L (NK.Reconstruct.comap_level_ne_top hA L)
  -- the prime of `𝓞 k` below `A` really is `𝔭`, so `P` lies over `𝔭`
  have hprimeOf_eq : Submission.NeukirchUchida.primeOf A hA = 𝔭 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := k) (by
      rw [← Submission.NeukirchUchida.primeOf_spec A hA, h𝔭])
  have hliesP : P.asIdeal.LiesOver 𝔭.asIdeal := by
    have h := NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω)
      (⟨A, hA⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω) L
    rw [hprimeOf_eq] at h
    exact h
  -- a Frobenius at the prime `P` of `𝓞 L`
  obtain ⟨σ, hσfrob⟩ := NK.Chebotarev.exists_isFrobAt (K := k) (L := ↥L) 𝔭 P hliesP
  -- lift it to `decomp k A`
  obtain ⟨g, hgD, hgres⟩ :=
    exists_mem_decomp_res_eq_of_isFrobAt L A hA P hPspec σ hσfrob
  have hsplit : SSGRoute.decomp k A ≤ K.fixingSubgroup := hAsplit
  refine ⟨g, Subgroup.mem_inf.mpr ⟨hgD, hsplit hgD⟩, ?_⟩
  rw [NK.Chebotarev.isFrobAtPrime_iff]
  exact ⟨P, hliesP, by rwa [hgres]⟩

end Work.SSGRoute.ZDataMup
