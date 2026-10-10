import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.CoindHerbrand
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsLocal
import Submission.NK.GlobalCFTdeep.Herbrand.FiniteIndex
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_mul_eq_of_shortExact_noFin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Herbrand's theorem for the local units `𝒪_qˣ`

For a finite Galois extension `L / K` of number fields with **cyclic** Galois group, a finite place
`q` of `L` above the finite place `Q` of `K`, the local units `𝒪_qˣ` of the completion `L_q`, viewed
as a `ℤ[D_q]`-module for the decomposition group `D_q`, have Herbrand quotient `1`:

  `HerbrandEq (localUnitSubRep (Place.ofFinite q)) 1`,

i.e. `|Ĥ⁰(D_q, 𝒪_qˣ)| = |Ĥ¹(D_q, 𝒪_qˣ)|`.

## Proof

The valuation logarithm exhibits a short exact sequence of `ℤ[D_q]`-modules

  `0 ⟶ 𝒪_qˣ ⟶ L_qˣ ⟶ ℤ ⟶ 0`

(`NK.GlobalCFTdeep.sesLocalUnits`, `..._shortExact`), with `D_q` cyclic (a subgroup of the cyclic
group `L ≃ₐ[K] L`).  The six-term exact hexagon of Tate cohomology
(`NK.GlobalCFTdeep.Herbrand.tateCohomology_mul_eq_of_shortExact_noFin`) then reads

  `|Ĥ⁰(L_qˣ)| · |Ĥ¹(𝒪_qˣ)| · |Ĥ¹(ℤ)| = |Ĥ⁰(𝒪_qˣ)| · |Ĥ⁰(ℤ)| · |Ĥ¹(L_qˣ)|`.

The three remaining inputs are

* `|Ĥ⁰(ℤ)| = |D_q|` and `|Ĥ¹(ℤ)| = 1` (`hZero_trivial`, `hOne_trivial`);
* `|Ĥ¹(L_qˣ)| = 1` (Hilbert 90, `natCard_tateCohomology_one_of_fintype`, transported along the
  identification of `D_q` with the local Galois group);
* `|Ĥ⁰(L_qˣ)| = |D_q|` (the local norm index theorem
  `NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_ofFinite`, together with the previous
  point).

Substituting, the hexagon becomes `|D_q| · |Ĥ¹(𝒪_qˣ)| = |Ĥ⁰(𝒪_qˣ)| · |D_q|`, and cancelling the
non-zero factor `|D_q| = Nat.card D_q` gives `|Ĥ¹(𝒪_qˣ)| = |Ĥ⁰(𝒪_qˣ)|`, which is
`HerbrandEq (localUnitSubRep (Place.ofFinite q)) 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-- **Hilbert 90 for the local units at a finite place.**  The first Tate cohomology of the
representation of the decomposition group `D_q` on `L_qˣ` is trivial,
`|Ĥ¹(D_q, L_qˣ)| = 1`.

This is Hilbert 90 for the local Galois extension `L_q / K_Q`
(`natCard_tateCohomology_one_of_fintype`), transported to `D_q` along the isomorphism
`D_q ≃* Gal(L_q/K_Q)` of `NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois`. -/
theorem hOne_localUnitsRep_eq_one {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))] :
    NK.GlobalCFTdeep.hOne
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q)) = 1 := by
  classical
  have hq : q.asIdeal.LiesOver Q.asIdeal := inferInstance
  -- the local field is finite and Galois over the base local field
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  haveI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := Fintype.ofFinite _
  let e := NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois Q q hq
  -- the representation of `D_q` is the restriction of the local one along `e`
  have h1 : NK.GlobalCFTdeep.hOne
        (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
      = NK.GlobalCFTdeep.hOne (Rep.ofMulDistribMulAction
          (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ) := by
    rw [NK.GlobalCFTdeep.localUnitsRep_eq_res (K := K) (L := L) Q q hq,
      NK.GlobalCFTdeep.hOne_def, NK.GlobalCFTdeep.hOne_def]
    exact NK.GlobalCFTdeep.natCard_tateCohomology_one_of_mulEquiv_res e _
  rw [h1, NK.GlobalCFTdeep.hOne_def]
  exact NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_one_of_fintype _

/-- **Herbrand's theorem for the local units `𝒪_qˣ`.**  For a finite Galois extension `L / K` of
number fields with cyclic Galois group and a finite place `q` of `L` above the finite place `Q` of
`K`, the local units `𝒪_qˣ` — the kernel of the valuation at `q` on `L_qˣ` — have Herbrand quotient
`1` for the action of the decomposition group `D_q`. -/
theorem herbrandEq_localUnitSubRep_ofFinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))] :
    NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) 1 := by
  classical
  have hq : q.asIdeal.LiesOver Q.asIdeal := inferInstance
  -- the decomposition group is cyclic (a subgroup of the cyclic group `L ≃ₐ[K] L`), hence abelian
  haveI hcyc : IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) := inferInstance
  letI hcg : CommGroup (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) := IsCyclic.commGroup
  have hcomm : ∀ a b : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q), a * b = b * a := fun a b => mul_comm a b
  -- the middle term: `HerbrandEq (L_qˣ) |D_q|`
  have hmid : NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
      (Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q))) :=
    herbrandEq_localUnitsRep_ofFinite (K := K) (L := L) Q q hcomm
  -- Hilbert 90: `|Ĥ¹(L_qˣ)| = 1`, hence `|Ĥ⁰(L_qˣ)| = |D_q|`
  have h1mid : NK.GlobalCFTdeep.hOne
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q)) = 1 :=
    hOne_localUnitsRep_eq_one (K := K) (L := L) Q q
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
        (NK.GlobalCFT.Place.ofFinite q)) := hZero_trivial _
  have h1triv : NK.GlobalCFTdeep.hOne
      (Rep.trivial ℤ (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) ℤ) = 1 := hOne_trivial _
  -- the six-term exact hexagon attached to `0 ⟶ 𝒪_qˣ ⟶ L_qˣ ⟶ ℤ ⟶ 0`
  have hhex := tateCohomology_mul_eq_of_shortExact_noFin
    (sesLocalUnits (K := K) (L := L) Q q hq)
    (sesLocalUnits_shortExact (K := K) (L := L) Q q hq)
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

end NK.GlobalCFTdeep.Herbrand
