import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.vf_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **`finQW` does not depend on the proof that the place is finite.**  The chosen prime of `𝓞 L`
below a place `A` of `Ω` is a function of `A` and `L` only; the finiteness proof is a propositional
argument of `finQW` and may therefore be replaced by any other one. -/
theorem finQW_proof_irrel {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (h1 h2 : SSGRoute.IsFinPlace k A) :
    finQW L A h1 = finQW L A h2 :=
  congrArg (finQW L A) (Subsingleton.elim h1 h2)

/-- **`finQW` is invariant under an equality of the underlying places.** -/
theorem finQW_congr {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    {A B : ValuationSubring Ω} (h : A = B) (hA : SSGRoute.IsFinPlace k A)
    (hB : SSGRoute.IsFinPlace k B) :
    finQW L A hA = finQW L B hB := by
  obtain rfl : B = A := h.symm
  exact finQW_proof_irrel L _ hA hB

theorem exists_smul_ofFinite_finQW_eq {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L]
    [IsGalois k L] [NumberField L]
    (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v)
    (hRcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      ∃ v ∈ R, SSGRoute.IsConjPlace k v B)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L)) :
    ∃ (v : ValuationSubring Ω) (hv : v ∈ R) (σ : ↥L ≃ₐ[k] ↥L),
      σ • NK.GlobalCFT.Place.ofFinite q =
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L v (hRfin v hv)) := by
  classical
  -- A finite place `A` of `Ω` above `q`.
  obtain ⟨A, hAcomap, hAfin⟩ :=
    Work.SSGRoute.exists_isFinPlace_comap_eq (k := k) (Ω := Ω) L q
  -- The prime of `𝓞 L` below `A` is `q` (injectivity of `valuationSubringAtPrime`).
  have hfinA : finQW L A hAfin = q := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥L) (K := ↥L) ?_
    rw [← finQW_comap L A hAfin, hAcomap]
  -- Covering: some `v ∈ R` is conjugate to `A` over `k`.
  obtain ⟨v, hv, hconj⟩ := hRcov A hAfin
  obtain ⟨τ, hτv⟩ := hconj
  have hA' : SSGRoute.IsFinPlace k (τ • v) := hτv ▸ hAfin
  -- Transport `finQW` along `τ`: `finQW L (τ • v) = q`.
  have h4 := ofFinite_finQW_smul L v (hRfin v hv) τ hA'
  have h5 : finQW L (τ • v) hA' = q := by
    rw [finQW_congr L hτv hA' hAfin]
    exact hfinA
  rw [h5] at h4
  -- `h4 : ofFinite q = (τ.restrictNormal L) • ofFinite (finQW L v)`; invert the action.
  refine ⟨v, hv, (τ.restrictNormal ↥L)⁻¹, ?_⟩
  rw [h4, inv_smul_smul]

end Work.SSGRoute.PT
