import Submission.Work.DSG4b.Defs

/-!
# DSG4b — reductions for gonflement

The frozen statement `DSMap.area_G4b_gonflement` asks for a flat `ψ : A →+* A'` with `A'` a
complete regular local ring, algebraically closed residue field, and `maximalIdeal A'` lying over
`m ⊂ A` (a maximal ideal, `A` regular Noetherian).

Here we record the two reductions that make the problem local and complete:

* `isGonflement_of_localization` — a gonflement of `Localization.AtPrime m` at its maximal ideal is
  a gonflement of `A` at `m` (localisation is flat, and the maximal ideal of the localisation lies
  over `m`).
* `isGonflement_of_completion` — a gonflement of the `m`-adic completion of a regular local ring
  `R` is a gonflement of `R` (adic completion is flat for Noetherian rings, and is a local map).

Consequently the frozen statement follows from

`Work.DSG4b.gonflement_regular_local` (see `Submission/Work/DSG4b/HardCore*.lean`), the case where
`A` is itself local: the residue-field-enlargement theorem of
EGA 0_III 10.3.1 / Česnavičius, *Purity for the Brauer group*, Lemma 5.1.
-/

namespace Work.DSG4b

open IsLocalRing

universe u

section Localization

variable {A : Type u} [CommRing A] {m : Ideal A}

/-- A gonflement of the localisation of `A` at a maximal ideal `m` (at the maximal ideal of the
localisation) is a gonflement of `A` at `m`. -/
theorem isGonflement_of_localization (hm : m.IsMaximal) {A' : Type u} [CommRing A']
    [IsLocalRing A'] (ψ : Localization.AtPrime m →+* A')
    (h : IsGonflement (maximalIdeal (Localization.AtPrime m)) A' ψ) :
    IsGonflement m A' (ψ.comp (algebraMap A (Localization.AtPrime m))) := by
  haveI : m.IsPrime := hm.isPrime
  have hloc : RingHom.Flat (algebraMap A (Localization.AtPrime m)) := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat (Localization.AtPrime m) m.primeCompl
  refine ⟨h.isRegularLocal, h.isAdicComplete, h.isAlgClosed, RingHom.Flat.comp hloc h.flat, ?_⟩
  rw [← Ideal.comap_comap, h.comap_maximalIdeal]
  exact Localization.AtPrime.under_maximalIdeal

end Localization

section Completion

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A gonflement of the `m`-adic completion of a regular local ring `R` is a gonflement of `R`. -/
theorem isGonflement_of_completion {A' : Type u} [CommRing A'] [IsLocalRing A']
    (ψ : AdicCompletion (maximalIdeal R) R →+* A')
    (h : IsGonflement (maximalIdeal (AdicCompletion (maximalIdeal R) R)) A' ψ) :
    IsGonflement (maximalIdeal R) A'
      (ψ.comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  haveI : IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) := inferInstance
  have hloc : RingHom.Flat (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    rw [RingHom.flat_algebraMap_iff]
    exact AdicCompletion.flat_of_isNoetherian (maximalIdeal R)
  refine ⟨h.isRegularLocal, h.isAdicComplete, h.isAlgClosed,
    RingHom.Flat.comp hloc h.flat, ?_⟩
  rw [← Ideal.comap_comap, h.comap_maximalIdeal, IsLocalRing.maximalIdeal_comap]

end Completion

end Work.DSG4b
