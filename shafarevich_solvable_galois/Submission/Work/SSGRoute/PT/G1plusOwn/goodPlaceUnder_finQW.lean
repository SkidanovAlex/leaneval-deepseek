import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.glue_fin_decomp_ex
import Submission.Work.SSGRoute.PT.vf_aux
import Submission.Work.SSGRoute.PT.exists_smul_ofFinite_finQW_eq
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

/-- **A place of `Ω` above a prescribed finite place of `L` avoiding the classes of `S'`.**

`q'` is a finite place of the level `L ⊆ Ω` which is not conjugate (by `Gal(L/k)`) to any of the
places `ofFinite (finQW L A hA)`, `A ∈ S'`.  Then `q'` has a place `B` of `Ω` above it
(`finQW L B hB = q'`) which is a finite place of `Ω` over `k` and whose `Gal(Ω/k)`-class meets none
of the classes of `S'`.

This is the place-theoretic bookkeeping step of clause (7) of `G1⁺` at the finite places: the
vanishing of the local components off the classes of `S'` (the hypothesis `hT` of
`Work.SSGRoute.PT.G1plusOwn.sum_iota_eq_zero_of_extToClasses_zero`) is proved at the `Ω`-places,
from the arithmetic hypothesis `hgood`, and this result converts an arbitrary finite place of `L`
into such an `Ω`-place.

Proof.  `Work.SSGRoute.exists_isFinPlace_comap_eq L q'` extends `q'` to a place `B` of `Ω` with
`B.comap (algebraMap ↥L Ω) = 𝓞_{L,q'}` and `IsFinPlace k B`; then `finQW L B hB = q'` by
injectivity of `valuationSubringAtPrime` applied to `finQW_comap` (both sides have the same
`valuationSubringAtPrime`, namely `B.comap`), as in
`Submission/Work/SSGRoute/PT/exists_smul_ofFinite_finQW_eq.lean`.  For the avoidance clause: if
`IsConjPlace k A B` with `τ • A = B`, then `ofFinite q' = ofFinite (finQW L B hB) =
ofFinite (finQW L (τ • A)) = (τ.restrictNormal L) • ofFinite (finQW L A hA)` by
`Work.SSGRoute.PT.ofFinite_finQW_smul` and `Work.SSGRoute.PT.finQW_congr`, contradicting the
hypothesis on `q'`.

Ingredients available sorry-free: `Work.SSGRoute.exists_isFinPlace_comap_eq`
(`Submission/Work/SSGRoute/glue_fin_decomp_ex.lean`), `Work.SSGRoute.PT.finQW_comap`,
`Work.SSGRoute.PT.ofFinite_finQW_smul`, `Work.SSGRoute.PT.finQW_congr`,
`Work.SSGRoute.PT.finQW_proof_irrel` (`Submission/Work/SSGRoute/PT/vf_aux.lean`,
`Submission/Work/SSGRoute/PT/exists_smul_ofFinite_finQW_eq.lean`), and
`Commons.RingTheory.Valuation.valuationSubringAtPrime_injective`. -/
theorem goodPlaceUnder_finQW {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField ↥L]
    (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hnot : ∀ (A : ValuationSubring Ω) (hA : A ∈ S'), ∀ σ : ↥L ≃ₐ[k] ↥L,
      σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A (hS'fin A hA)) ≠
        NK.GlobalCFT.Place.ofFinite q') :
    ∃ (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B),
      Work.SSGRoute.PT.finQW L B hB = q' ∧
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) := by
  classical
  -- Extend the prescribed finite place `q'` of `L` to a finite place `B` of `Ω`.
  obtain ⟨B, hBcomap, hBfin⟩ :=
    Work.SSGRoute.exists_isFinPlace_comap_eq (k := k) (Ω := Ω) L q'
  -- `finQW L B hBfin = q'` by injectivity of `valuationSubringAtPrime`.
  have hfinB : Work.SSGRoute.PT.finQW L B hBfin = q' := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥L) (K := ↥L) ?_
    rw [← finQW_comap L B hBfin, hBcomap]
  refine ⟨B, hBfin, hfinB, ?_⟩
  -- Avoidance clause: no `A ∈ S'` is conjugate to `B` over `k`.
  intro A hA hconj
  obtain ⟨τ, hτ⟩ := hconj
  have hA' : SSGRoute.IsFinPlace k (τ • A) := hτ.symm ▸ hBfin
  -- `finQW` transports along the conjugacy `τ • A = B`.
  have h1 : Work.SSGRoute.PT.finQW L (τ • A) hA' = Work.SSGRoute.PT.finQW L B hBfin :=
    finQW_congr L hτ hA' hBfin
  -- The Galois action on `finQW`.
  have h4 := ofFinite_finQW_smul L A (hS'fin A hA) τ hA'
  have hq : NK.GlobalCFT.Place.ofFinite q' =
      NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L B hBfin) := by rw [hfinB]
  have h1' : NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L B hBfin) =
      NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L (τ • A) hA') := by rw [h1]
  -- Hence `ofFinite q' = (τ.restrictNormal L) • ofFinite (finQW L A)`, contradicting `hnot`.
  exact (hnot A hA (τ.restrictNormal ↥L)) (hq.trans (h1'.trans h4)).symm

end Work.SSGRoute.PT.G1plusOwn
