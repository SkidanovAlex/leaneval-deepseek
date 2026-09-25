import Mathlib
import Submission.Work.CFTLib.NKHerbrand

/-!
# `Ĥ⁻¹(D_q, 𝒪_qˣ) = 0` for an unramified finite place `q`

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` and `q` a
finite place of `L` above `Q` with **ramification index one**, so that the local extension
`L_q / K_Q` is unramified.  Then the decomposition group `D_q` acts on the units `𝒪_qˣ` of the ring
of integers of `L_q` and

  `Ĥ⁻¹(D_q, 𝒪_qˣ) = 0`.

## Proof

For `e(q|Q) = 1` the local Galois group `Gal(L_q/K_Q)` is cyclic
(`isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one`), hence so is `D_q`
(`decompositionSubgroupIsoLocalGalois`).  For a finite cyclic group `G`, Tate cohomology in degree
`-1` is `H¹` (`subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic`), so
it suffices to prove `H¹(D_q, 𝒪_qˣ) = 0`.  By cyclic periodicity `H¹ ≅ Ĥ¹`, and `|Ĥ¹| = 1` follows
from Herbrand's theorem for the local units,

  `|Ĥ⁰(D_q, 𝒪_qˣ)| = |Ĥ¹(D_q, 𝒪_qˣ)|`

(the six-term exact hexagon of `0 → 𝒪_qˣ → L_qˣ → ℤ → 0`), together with the unconditional
unramified computation `|Ĥ⁰(D_q, 𝒪_qˣ)| = 1` of
`hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one`.

The only point in the existing proof of Herbrand's theorem for `𝒪_qˣ`
(`herbrandEq_localUnitSubRep_ofFinite`) that uses the hypothesis `IsCyclic (L ≃ₐ[K] L)` — rather
than cyclicity of `D_q` itself — is the local Herbrand computation for `L_qˣ`; we therefore
re-prove it here with cyclicity of the decomposition group as the hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace Work.CFTLib

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Cyclicity of the decomposition group of an unramified place -/

/-- The decomposition group of a place with ramification index one is cyclic: it is isomorphic to
the Galois group of the unramified local extension `L_q / K_Q`, which is cyclic. -/
theorem isCyclic_decompositionSubgroup_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) := by
  haveI : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
      Q q hq hunr
  exact (NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois Q q hq).isCyclic.mpr ‹_›

/-! ## Herbrand's theorem for `𝒪_qˣ`, for a cyclic decomposition group -/

/-- **Herbrand's theorem for the local units `𝒪_qˣ`.**  If the decomposition group `D_q` is cyclic,
then the local units `𝒪_qˣ` of the completion `L_q` have Herbrand quotient `1`:

  `|Ĥ⁰(D_q, 𝒪_qˣ)| = |Ĥ¹(D_q, 𝒪_qˣ)|`.

This is `NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitSubRep_ofFinite` with the hypothesis
`IsCyclic (L ≃ₐ[K] L)` weakened to `IsCyclic D_q`, which is what the proof actually uses. -/
theorem herbrandEq_localUnitSubRep_of_isCyclic_decompositionSubgroup
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    [IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))] :
    NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1 := by
  classical
  have hq : q.asIdeal.LiesOver Q.asIdeal := inferInstance
  -- the decomposition group is cyclic, hence abelian
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
        (NK.GlobalCFT.Place.ofFinite q)) :=
    NK.GlobalCFTdeep.Herbrand.hZero_trivial _
  have h1triv : NK.GlobalCFTdeep.hOne
      (Rep.trivial ℤ (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) ℤ) = 1 :=
    NK.GlobalCFTdeep.Herbrand.hOne_trivial _
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

/-! ## `H¹(D_q, 𝒪_qˣ) = 0` and the main theorem -/

/-- **`|Ĥ¹(D_q, 𝒪_qˣ)| = 1`** for an unramified finite place: Herbrand's theorem above computes
`|Ĥ¹| = |Ĥ⁰|`, and `|Ĥ⁰| = 1` unconditionally for `e(q|Q) = 1`. -/
theorem hOne_localUnitSubRep_eq_one_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) = 1 := by
  have hq : q.asIdeal.LiesOver Q.asIdeal := inferInstance
  haveI : IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) :=
    isCyclic_decompositionSubgroup_of_ramificationIdx_eq_one Q q hq hunr
  have herb : NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1 :=
    herbrandEq_localUnitSubRep_of_isCyclic_decompositionSubgroup (K := K) (L := L) Q q
  have hzero : NK.GlobalCFTdeep.hZero
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) = 1 :=
    NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one Q q hq hunr
  rw [NK.GlobalCFTdeep.HerbrandEq] at herb
  rw [hzero, one_mul] at herb
  exact herb.symm

/-- **`Ĥ⁻¹(D_q, 𝒪_qˣ) = 0` for an unramified finite place.**  The decomposition group `D_q` of a
place `q` with `e(q|Q) = 1` is cyclic, so that `Ĥ⁻¹(D_q, ·) ≅ H¹(D_q, ·)`; the latter vanishes
because `H¹ ≅ Ĥ¹` (in positive degrees Tate cohomology is ordinary cohomology) and `Ĥ¹` is trivial
by the previous lemma. -/
theorem subsingleton_tateCohomology_neg_one_localUnitSubRep_of_ramificationIdx_eq_one
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Subsingleton (tateCohomology (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) (-1)) := by
  classical
  have hq : q.asIdeal.LiesOver Q.asIdeal := inferInstance
  haveI hcyc : IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) :=
    isCyclic_decompositionSubgroup_of_ramificationIdx_eq_one Q q hq hunr
  -- `|Ĥ¹(D_q, 𝒪_qˣ)| = 1`, hence `Ĥ¹` and then `H¹` are trivial
  have hOne : NK.GlobalCFTdeep.hOne
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) = 1 :=
    hOne_localUnitSubRep_eq_one_of_ramificationIdx_eq_one Q q hunr
  have hcard : Nat.card (tateCohomology (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) 1) = 1 := by
    rw [← NK.GlobalCFTdeep.hOne_def]
    exact hOne
  have hsubG : Subsingleton (groupCohomology (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) 1) := by
    have hsub1 : Subsingleton (tateCohomology (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1) := (Nat.card_eq_one_iff_unique.mp hcard).1
    have e := ((TateCohomology.isoGroupCohomology (R := ℤ)
      (G := NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1).app
        (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
          (NK.GlobalCFT.Place.ofFinite q))).toLinearEquiv
    exact ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩
  exact NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic
    _ hsubG

end Work.CFTLib
