import Mathlib.RepresentationTheory.Coinduced
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.GlobalCFTdeep.Audit.index_normClassSubgroup_self
import Submission.NK.GlobalCFTdeep.Corollaries.HasseInput
import Submission.NK.GlobalCFTdeep.Herbrand.Assembly
import Submission.NK.GlobalCFTdeep.Herbrand.FiberAll
import Submission.NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective
import Submission.NK.GlobalCFTdeep.Herbrand.fiberUnitsRep_iso_coind
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_iff_of_finite_quotient
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_ind_iff
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitSubRep_ofFinite
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tIdeles_mul_eq_unitIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_supportedIdelesRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_unitIdelesOutsideRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `ℋ⁰` and `ℋ¹` of the unit part of a fibre, from Shapiro's lemma

For a finite Galois extension `L / K` of number fields with cyclic Galois group, a finite place
`v` of `K`, a finite place `q` of `L` above it, and assuming that the local units at `q` have
trivial `ℋ⁰` and `ℋ¹` (`hZero (localUnitSubRep q) = 1`, `hOne (localUnitSubRep q) = 1`), the unit
part of the fibre of `v` has trivial `ℋ⁰` and `ℋ¹` as well:

  `|ℋ⁰(G, ∏_{w' | v} 𝒪_{w'}ˣ)| = 1` and `|ℋ¹(G, ∏_{w' | v} 𝒪_{w'}ˣ)| = 1`.

The proof is Shapiro's lemma
(`NK.GlobalCFTdeep.fiberUnitsRep_iso_coind` identifies `∏_{w' | v} 𝒪_{w'}ˣ` with
`Coind_{D_q}^G 𝒪_qˣ`) together with `hZero_coind` / `hOne_coind`, the Shapiro isomorphisms
`ℋ⁰(G, Coind_H^G M) ≅ ℋ⁰(H, M)` and `ℋ¹(G, Coind_H^G M) ≅ ℋ¹(H, M)`. -/

namespace NK.GlobalCFTdeep.Herbrand

open CategoryTheory

theorem natCard_tateCohomology_fiberUnitsRep_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (v : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    (hw : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v)
    (h0 : NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) = 1)
    (h1 : NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) = 1) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 0) = 1 ∧
      Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 1) = 1 := by
  classical
  obtain ⟨e⟩ := NK.GlobalCFTdeep.fiberUnitsRep_iso_coind (K := K) (L := L) v q hw
  refine ⟨?_, ?_⟩
  · calc Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 0)
        = Nat.card (tateCohomology (Rep.coind
              (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
                (NK.GlobalCFT.Place.ofFinite q)).subtype
              (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
                (NK.GlobalCFT.Place.ofFinite q))) 0) :=
          Nat.card_congr
            ((tateCohomologyFunctor (R := ℤ) (G := L ≃ₐ[K] L) 0).mapIso e).toLinearEquiv.toEquiv
      _ = NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
            (NK.GlobalCFT.Place.ofFinite q)) := by
          rw [← hZero_def]
          exact hZero_coind _ _
      _ = 1 := h0
  · calc Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 1)
        = Nat.card (tateCohomology (Rep.coind
              (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
                (NK.GlobalCFT.Place.ofFinite q)).subtype
              (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
                (NK.GlobalCFT.Place.ofFinite q))) 1) :=
          Nat.card_congr
            ((tateCohomologyFunctor (R := ℤ) (G := L ≃ₐ[K] L) 1).mapIso e).toLinearEquiv.toEquiv
      _ = NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
            (NK.GlobalCFT.Place.ofFinite q)) := by
          rw [← hOne_def]
          exact hOne_coind _ _
      _ = 1 := h1

end NK.GlobalCFTdeep.Herbrand
