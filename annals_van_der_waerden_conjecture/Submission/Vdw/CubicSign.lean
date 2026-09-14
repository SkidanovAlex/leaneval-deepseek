import Mathlib
import Submission.Vdw.GaloisTower
import Submission.Vdw.PerFieldFibreAll
import Submission.Commons.NumberTheory.NumberField.discr_eq_of_algEquiv
import Submission.Commons.NumberTheory.NumberField.splittingField_numberField

open Polynomial Filter Asymptotics
open scoped BigOperators NumberField Classical
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The sign of the discriminant in degree three

For an irreducible cubic `p` over `ℚ` whose Galois group has order `< 6`
(equivalently `= 3`, the `Bad` condition of the van der Waerden problem for
`n = 3`), the field `K_p = ℚ[X]/p` is Galois over `ℚ` of degree `3`, hence
totally real, hence has *positive* discriminant.

This is the missing input of the `n = 3` field count: the Dedekind index
relation `disc (minpoly ℤ θ) = discr K · m²` then has the *definite* sign,
so the surviving relation is a *definite* binary quadratic form equation.

The proof of total reality uses
`NumberField.InfinitePlace.even_finrank_of_not_isUnramified`: a ramified
infinite place forces the degree to be even; a cubic Galois extension has odd
degree, so every infinite place is unramified, i.e. real (the base field `ℚ`
is totally real).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## 1. The Galois group of a cubic with `Bad` has order three -/

/-- An irreducible cubic over `ℚ` whose Galois group has order `< 6` has
Galois group of order exactly `3` (the action on the three roots is transitive,
so `3` divides the order). -/
theorem gal_card_eq_three_of_lt_six (p : ℚ[X]) (hp : Irreducible p) (hnd : p.natDegree = 3)
    (hcard : Nat.card p.Gal < 6) : Nat.card p.Gal = 3 := by
  classical
  have hsep : p.Separable := separable_of_irreducible_rat hp
  have hpre : MulAction.IsPretransitive (galFinHom p hsep).range (Fin p.natDegree) :=
    galFinHom_pretransitive p hp hsep
  haveI hfinG : Fintype (galFinHom p hsep).range := inferInstance
  have h3pos : 0 < p.natDegree := by rw [hnd]; norm_num
  set x : Fin p.natDegree := ⟨0, h3pos⟩ with hx
  have horbit : MulAction.orbit (galFinHom p hsep).range x = Set.univ :=
    MulAction.orbit_eq_univ _ x
  have hcorbit : Fintype.card (MulAction.orbit (galFinHom p hsep).range x) = 3 := by
    rw [horbit]
    simp [Fintype.card_fin, hnd]
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := (galFinHom p hsep).range) x
  have hcardrange : Fintype.card (galFinHom p hsep).range = Nat.card p.Gal := by
    rw [gal_card_eq_card_range p hsep, Nat.card_eq_fintype_card]
  rw [hcorbit, hcardrange] at hOS
  -- `3 * s = |Gal|` with `1 ≤ s` and `3 * s ≤ 5`
  have hspos : 1 ≤ Fintype.card (MulAction.stabilizer (galFinHom p hsep).range x) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hle : 3 * Fintype.card (MulAction.stabilizer (galFinHom p hsep).range x) ≤ 5 := by
    rw [hOS]; omega
  have hs1 : Fintype.card (MulAction.stabilizer (galFinHom p hsep).range x) = 1 := by omega
  rw [hs1, mul_one] at hOS
  exact hOS.symm

/-! ## 2. Total reality of the splitting field -/

/-- The degree of the splitting field of an irreducible cubic with Galois
group of order `< 6` is `3` (it equals the order of the Galois group). -/
theorem finrank_splittingField (p : ℚ[X]) (hp : Irreducible p) (hnd : p.natDegree = 3)
    (hcard : Nat.card p.Gal < 6) : Module.finrank ℚ p.SplittingField = 3 := by
  classical
  haveI : Fact (Irreducible p) := ⟨hp⟩
  haveI : IsGalois ℚ p.SplittingField := spl_galois p
  have hcard3 : Nat.card p.Gal = 3 := gal_card_eq_three_of_lt_six p hp hnd hcard
  rw [← IsGalois.card_aut_eq_finrank (F := ℚ) (E := p.SplittingField)]
  exact hcard3

/-- **The splitting field of an irreducible cubic with Galois group of order
`< 6` is totally real.**  Its degree over `ℚ` equals `|Gal| = 3`, and a
ramified infinite place would force that degree to be even. -/
theorem isTotallyReal_splittingField (p : ℚ[X]) (hp : Irreducible p) (hnd : p.natDegree = 3)
    (hcard : Nat.card p.Gal < 6) :
    NumberField.IsTotallyReal p.SplittingField := by
  classical
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI hNF : NumberField p.SplittingField :=
    Commons.NumberTheory.NumberField.splittingField_numberField hp0
  haveI hGal : IsGalois ℚ p.SplittingField := spl_galois p
  have hcard3 : Nat.card p.Gal = 3 := gal_card_eq_three_of_lt_six p hp hnd hcard
  have hfr : Module.finrank ℚ p.SplittingField = 3 :=
    finrank_splittingField p hp hnd hcard
  rw [← NumberField.nrComplexPlaces_eq_zero_iff]
  by_contra hne
  have hpos : 0 < NumberField.InfinitePlace.nrComplexPlaces p.SplittingField :=
    Nat.pos_of_ne_zero hne
  obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace p.SplittingField,
      NumberField.InfinitePlace.IsComplex w := by
    by_contra hcon
    push_neg at hcon
    have hemp : IsEmpty {w : NumberField.InfinitePlace p.SplittingField //
        NumberField.InfinitePlace.IsComplex w} := ⟨fun w => hcon w.1 w.2⟩
    have h0 : NumberField.InfinitePlace.nrComplexPlaces p.SplittingField = 0 :=
      Fintype.card_eq_zero_iff.mpr hemp
    rw [h0] at hpos
    exact absurd hpos (by norm_num)
  have hram : ¬ NumberField.InfinitePlace.IsUnramified ℚ w := by
    rw [NumberField.InfinitePlace.not_isUnramified_iff]
    refine ⟨hw, ?_⟩
    exact (show NumberField.IsTotallyReal ℚ from inferInstance).isReal _
  have hev : Even (Module.finrank ℚ p.SplittingField) :=
    NumberField.InfinitePlace.even_finrank_of_not_isUnramified (k := ℚ)
      (K := p.SplittingField) hram
  rw [hfr] at hev
  exact absurd hev (by norm_num)

/-- The splitting field's discriminant is positive. -/
theorem discr_splittingField_pos (p : ℚ[X]) (hp : Irreducible p) (hnd : p.natDegree = 3)
    (hcard : Nat.card p.Gal < 6) : 0 < NumberField.discr p.SplittingField := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI hNF : NumberField p.SplittingField :=
    Commons.NumberTheory.NumberField.splittingField_numberField hp0
  have htot := isTotallyReal_splittingField p hp hnd hcard
  have hz : NumberField.InfinitePlace.nrComplexPlaces p.SplittingField = 0 :=
    NumberField.nrComplexPlaces_eq_zero_iff.mpr htot
  have hsign := NumberField.sign_discr p.SplittingField
  rw [hz, pow_zero] at hsign
  exact Int.sign_eq_one_iff_pos.mp hsign

/-! ## 4. The discriminant of the field of a cubic with `Bad` is positive -/

/-- **The field of an irreducible cubic with `Bad` has positive discriminant.**
The splitting field is totally real of degree `3` over `ℚ`; the root field
`K_f = AdjoinRoot (f.map φℚ)` is a `ℚ`-subalgebra of it of the same dimension,
hence equal to it (the algebra map is bijective because the relative dimension
is `1`). -/
theorem discr_Kpoly_pos (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] (hm : f.Monic)
    (hdeg : f.natDegree = 3) (hcard : Nat.card (f.map φℚ).Gal < 6) :
    0 < NumberField.discr (Kpoly f) := by
  classical
  have hp : Irreducible (f.map φℚ) := Fact.out
  have hp0 : f.map φℚ ≠ 0 := hp.ne_zero
  have hnd : (f.map φℚ).natDegree = 3 := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero φℚ (by rw [hm.leadingCoeff]; simp),
      hdeg]
  haveI hNF : NumberField ((f.map φℚ).SplittingField) :=
    Commons.NumberTheory.NumberField.splittingField_numberField hp0
  haveI hGal : IsGalois ℚ ((f.map φℚ).SplittingField) := spl_galois (f.map φℚ)
  have hdiscL : 0 < NumberField.discr ((f.map φℚ).SplittingField) :=
    discr_splittingField_pos (f.map φℚ) hp hnd hcard
  letI : Algebra (Kpoly f) ((f.map φℚ).SplittingField) := kpolyAlgebra (f.map φℚ)
  haveI hST : IsScalarTower ℚ (Kpoly f) ((f.map φℚ).SplittingField) := kpoly_tower (f.map φℚ)
  have hfrL : Module.finrank ℚ ((f.map φℚ).SplittingField) = 3 :=
    finrank_splittingField (f.map φℚ) hp hnd hcard
  have hfrK : Module.finrank ℚ (Kpoly f) = 3 := finrank_Kpoly hm hdeg
  have hfrOne : Module.finrank (Kpoly f) ((f.map φℚ).SplittingField) = 1 := by
    have h := Module.finrank_mul_finrank (F := ℚ) (K := Kpoly f)
      (A := (f.map φℚ).SplittingField)
    rw [hfrL, hfrK] at h
    have h3 : (3 : ℕ) * Module.finrank (Kpoly f) ((f.map φℚ).SplittingField) = 3 * 1 := by
      rw [mul_one]
      exact h
    exact Nat.mul_left_cancel (by norm_num) h3
  have hbij : Function.Bijective
      (algebraMap (Kpoly f) ((f.map φℚ).SplittingField)) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := Kpoly f)
      (E := (f.map φℚ).SplittingField)).mp hfrOne
  let e : Kpoly f ≃+* ((f.map φℚ).SplittingField) :=
    RingEquiv.ofBijective _ hbij
  have hd := NumberField.discr_eq_discr_of_ringEquiv (K := Kpoly f) e
  rw [hd]
  exact hdiscL

end

end Submission.Vdw
