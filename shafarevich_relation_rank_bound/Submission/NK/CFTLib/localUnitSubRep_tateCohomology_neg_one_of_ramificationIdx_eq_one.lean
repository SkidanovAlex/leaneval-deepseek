import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsDefs
import Submission.NK.GlobalCFTdeep.Herbrand.LocalUnits
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsLocal
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_mul_eq_of_shortExact_noFin
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_trivial
import Submission.NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic
import Submission.NK.LocalReciprocity.index_normGroup_eq_finrank

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory

namespace NK.CFTLib

/-!
# `Ĥ⁻¹(D_q, 𝒪_qˣ) = 0` for an unramified place

For a finite Galois extension `L / K` of number fields, a finite place `q` of `L` lying over the
finite place `Q` of `K`, with `q` unramified over `K` (`e(q|Q) = 1`) and cyclic decomposition
group `D_q`, the local units `𝒪_qˣ` of the completion `L_q` have vanishing Tate cohomology in
degree `-1`:

  `Ĥ⁻¹(D_q, 𝒪_qˣ) = 0`.

The proof is the standard one.

* **Herbrand input.**  Since `D_q` is cyclic, Herbrand's lemma gives
  `|Ĥ⁰(D_q, 𝒪_qˣ)| = |Ĥ¹(D_q, 𝒪_qˣ)|` (`herbrandEq_localUnitSubRep_of_isCyclic` below).
  This is `NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitSubRep_ofFinite` with the hypothesis
  `IsCyclic (L ≃ₐ[K] L)` weakened to `IsCyclic D_q` (which is exactly what the unramified case
  supplies: `D_q` is the Galois group of the residue field extension).
* **`Ĥ⁰`.**  For unramified `q` the norm on the local units is surjective, so
  `Ĥ⁰(D_q, 𝒪_qˣ) = 0` (the existing
  `NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one`).
  Herbrand then gives `Ĥ¹(D_q, 𝒪_qˣ) = 0`.
* **Periodicity.**  In degree one the Tate cohomology agrees with ordinary group cohomology,
  and for a finite cyclic group `Ĥ⁻¹` is isomorphic to `H¹`; so `H¹ = 0` gives `Ĥ⁻¹ = 0`
  (`NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic`).
-/

/-- **Herbrand's theorem for the local units `𝒪_qˣ`, with cyclicity assumed on the decomposition
group.**  For a finite Galois extension `L / K` of number fields and a finite place `q` of `L`
above `Q` whose decomposition group `D_q` is cyclic, the local units `𝒪_qˣ` have Herbrand
quotient `1` for the action of `D_q`:

  `HerbrandEq (localUnitSubRep (Place.ofFinite q)) 1`,  i.e.  `|Ĥ⁰(D_q,𝒪_qˣ)| = |Ĥ¹(D_q,𝒪_qˣ)|`.

This is `NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitSubRep_ofFinite` with the hypothesis
`IsCyclic (L ≃ₐ[K] L)` weakened to `IsCyclic D_q`. -/
theorem herbrandEq_localUnitSubRep_of_isCyclic_decompSubgroup {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    [IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))] :
    NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1 := by
  classical
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  -- a cyclic group is commutative, and `D_q` is commutative
  letI hcg : CommGroup (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) := IsCyclic.commGroup
  have hcomm : ∀ a b : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q), a * b = b * a := fun a b => mul_comm a b
  -- the middle term: `HerbrandEq (L_qˣ) |D_q|`
  have hmid : NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
      (Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q))) :=
    NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_ofFinite (K := K) (L := L) Q q hcomm
  -- Hilbert 90: `|Ĥ¹(L_qˣ)| = 1`, hence `|Ĥ⁰(L_qˣ)| = |D_q|`
  have h1mid : NK.GlobalCFTdeep.hOne
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q)) = 1 :=
    NK.GlobalCFTdeep.Herbrand.hOne_localUnitsRep_eq_one (K := K) (L := L) Q q
  have h0mid : NK.GlobalCFTdeep.hZero
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
      = Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) := by
    rw [NK.GlobalCFTdeep.HerbrandEq] at hmid
    rw [hmid, h1mid, mul_one]
  -- the trivial module `ℤ`
  have h0triv : NK.GlobalCFTdeep.hZero
      (Rep.trivial ℤ (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) ℤ)
      = Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) := NK.GlobalCFTdeep.Herbrand.hZero_trivial _
  have h1triv : NK.GlobalCFTdeep.hOne
      (Rep.trivial ℤ (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) ℤ) = 1 := NK.GlobalCFTdeep.Herbrand.hOne_trivial _
  -- the six-term exact hexagon attached to `0 ⟶ 𝒪_qˣ ⟶ L_qˣ ⟶ ℤ ⟶ 0`
  have hhex := NK.GlobalCFTdeep.Herbrand.tateCohomology_mul_eq_of_shortExact_noFin
    (NK.GlobalCFTdeep.sesLocalUnits (K := K) (L := L) Q q hq)
    (NK.GlobalCFTdeep.sesLocalUnits_shortExact (K := K) (L := L) Q q hq)
  have hhex' : NK.GlobalCFTdeep.hZero
          (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
        * NK.GlobalCFTdeep.hOne
          (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
        * NK.GlobalCFTdeep.hOne
          (Rep.trivial ℤ (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
            (NK.GlobalCFT.Place.ofFinite q)) ℤ)
      = NK.GlobalCFTdeep.hZero
          (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
        * NK.GlobalCFTdeep.hZero
          (Rep.trivial ℤ (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
            (NK.GlobalCFT.Place.ofFinite q)) ℤ)
        * NK.GlobalCFTdeep.hOne
          (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L)
            (NK.GlobalCFT.Place.ofFinite q)) := hhex
  rw [h0mid, h1mid, h0triv, h1triv] at hhex'
  -- cancel the non-zero factor `|D_q|` and conclude
  rw [NK.GlobalCFTdeep.HerbrandEq, one_mul]
  have hpos : 0 < Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) :=
    Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  have hkey : NK.GlobalCFTdeep.hOne
        (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
      = NK.GlobalCFTdeep.hZero
        (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
          (NK.GlobalCFT.Place.ofFinite q)) := by
    simp only [mul_one] at hhex'
    rw [Nat.mul_comm (Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)))
      (NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)))] at hhex'
    exact Nat.mul_right_cancel hpos hhex'
  exact hkey.symm

/-- **`Ĥ⁻¹(D_q, 𝒪_qˣ) = 0` for an unramified place.**  For a finite Galois extension `L / K` of
number fields and a finite place `q` of `L` lying over `Q` with `e(q|Q) = 1` and cyclic
decomposition group `D_q`, the Tate cohomology of the local units `𝒪_qˣ` in degree `-1` vanishes.

(`q.asIdeal.ramificationIdx (𝓞 K) = 1` is the unramified hypothesis.) -/
theorem localUnitSubRep_tateCohomology_neg_one_of_ramificationIdx_eq_one {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    [IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) (-1)) := by
  classical
  set M : Rep ℤ (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) :=
    NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q) with hM
  -- Herbrand's theorem for `𝒪_qˣ` over the cyclic decomposition group
  have hherb : NK.GlobalCFTdeep.HerbrandEq M 1 := by
    rw [hM]
    exact herbrandEq_localUnitSubRep_of_isCyclic_decompSubgroup (K := K) (L := L) Q q hq
  -- `Ĥ⁰(D_q, 𝒪_qˣ) = 0` in the unramified case
  have h0 : NK.GlobalCFTdeep.hZero M = 1 := by
    rw [hM]
    exact NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one
      (K := K) (L := L) Q q hq hunr
  -- Herbrand's lemma gives `Ĥ¹(D_q, 𝒪_qˣ) = 0`
  have hOne_eq : NK.GlobalCFTdeep.hOne M = 1 := by
    rw [NK.GlobalCFTdeep.HerbrandEq] at hherb
    rw [h0, one_mul] at hherb
    exact hherb.symm
  have hsub_tate : Subsingleton (tateCohomology M 1) := by
    have hcard : Nat.card (tateCohomology M 1) = 1 := by
      rw [← NK.GlobalCFTdeep.hOne_def]
      exact hOne_eq
    exact (Nat.card_eq_one_iff_unique.mp hcard).1
  -- in degree one, Tate cohomology is ordinary group cohomology
  have hsub_grp : Subsingleton (groupCohomology M 1) := by
    haveI : Subsingleton (tateCohomology M 1) := hsub_tate
    have e := ((TateCohomology.isoGroupCohomology (R := ℤ)
      (G := NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1).app M).toLinearEquiv.toEquiv
    exact ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩
  -- Tate periodicity in degree `-1` for a cyclic group
  exact NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic
    M hsub_grp

end NK.CFTLib
