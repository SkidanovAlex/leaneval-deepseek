import Mathlib
import Submission.Work.ShafarevichKoch.WingbergDefs
import Submission.Work.ShafarevichKoch.KcRank
import Submission.Work.ClassFieldTower.two_pow_classGroupTwoRank
import Submission.Work.ClassFieldTower.card_quotient_sq_eq_card_twoTorsion
import Submission.Work.ShafarevichKoch.card_twoTorsion_twoPrimaryPart

/-!
# `Work.ShafarevichKoch.KcArithmetic` -- the arithmetic of the two outer terms

The two outer terms of the relation count
`#H²(G_∅,ℤ/2) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #(H³(G_∅,ℤ)[2])`
(`Work.ShafarevichKoch.natCard_H2_zmodTwo_eq`) are, under Wingberg's duality
(`Work.ShafarevichKoch.WingbergDuality`), the `2`-primary part of the class group of `Kc` and the
universal-norm quotient of the units `(𝓞 Kc)ˣ = {±1}`.  This module collects the arithmetic of
those two groups:

* `Work.ShafarevichKoch.card_twoTorsion_classGroup_Kc` : `#Cl(Kc)[2] = 32 = 2^5`;
* `Work.ShafarevichKoch.card_RingUnit_Kc_le_two` : `#(𝓞 Kc)ˣ ≤ 2`;
* the general bookkeeping lemmas about `2`-torsion, additive isomorphisms and quotients.

## Main declarations

* `Work.ShafarevichKoch.card_twoTorsion_classGroup_Kc`,
  `Work.ShafarevichKoch.card_RingUnit_Kc_le_two`, `Work.ShafarevichKoch.finite_RingUnit_Kc`;
* `Work.ShafarevichKoch.card_twoTorsion_addEquiv`,
  `Work.ShafarevichKoch.card_twoTorsion_additive`,
  `Work.ShafarevichKoch.card_twoTorsion_additive_le`,
  `Work.ShafarevichKoch.card_quotient_le_of_subgroup`,
  `Work.ShafarevichKoch.finite_of_finite_ker_and_range`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower
open Work.ConCohomology

/-! ## The arithmetic of the two outer terms -/

/-- The `2`-torsion of a finite abelian group commutes with additive isomorphisms. -/
theorem card_twoTorsion_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    Nat.card {x : A // (2 : ℕ) • x = 0} = Nat.card {y : B // (2 : ℕ) • y = 0} := by
  have hmap : ∀ x : A, e ((2 : ℕ) • x) = (2 : ℕ) • e x := by
    intro x
    rw [two_nsmul, two_nsmul, map_add]
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => ?_))
  constructor
  · intro h
    change (2 : ℕ) • e x = 0
    rw [← hmap, h, map_zero]
  · intro h
    change (2 : ℕ) • e x = 0 at h
    exact e.injective (by rw [hmap, h, map_zero])

/-- The `2`-torsion of `Additive A` is the `2`-torsion of `A`. -/
theorem card_twoTorsion_additive (A : Type*) [CommGroup A] :
    Nat.card {x : Additive A // (2 : ℕ) • x = 0} = Nat.card {x : A // x ^ 2 = 1} := by
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := Additive.toMul, invFun := Additive.ofMul, left_inv := fun x => rfl,
      right_inv := fun x => rfl } (fun x => ?_))
  constructor
  · intro h
    have := congrArg Additive.toMul h
    simpa [two_nsmul, pow_two] using this
  · intro h
    apply Additive.toMul.injective
    simpa [two_nsmul, pow_two] using h

/-- **`Cl(Kc)[2]` has 32 elements**: the `2`-torsion of the class group has the cardinality of
`Cl(Kc)/Cl(Kc)²`, which is `2 ^ classGroupTwoRank Kc = 2^5`
(`Work.ShafarevichKoch.classGroupTwoRank_Kc`). -/
theorem card_twoTorsion_classGroup_Kc :
    Nat.card {x : ClassGroup (NumberField.RingOfIntegers Kc) // x ^ 2 = 1} = 32 := by
  haveI : Fintype (ClassGroup (NumberField.RingOfIntegers Kc)) := Fintype.ofFinite _
  have h := Work.ClassFieldTower.card_quotient_sq_eq_card_twoTorsion
    (ClassGroup (NumberField.RingOfIntegers Kc))
  have h2 := Work.ClassFieldTower.two_pow_classGroupTwoRank Kc
  rw [classGroupTwoRank_Kc] at h2
  rw [← h, ← h2]
  norm_num

/-- **`(𝓞 Kc)ˣ = {±1}` is finite**: every unit of the ring of integers of `Kc` is `±1`
(`Work.ShafarevichKoch.unitEmbed_Kc_eq_one_or_eq_neg_one`). -/
theorem finite_RingUnit_Kc : Finite (RingUnit Kc) := by
  refine Finite.of_injective
    (fun u : RingUnit Kc => if unitEmbed Kc u = 1 then (0 : Fin 2) else 1) ?_
  intro a b hab
  have hinj : Function.Injective (unitEmbed Kc) := fun x y h => by
    apply Units.ext
    have h' : ((x : 𝓞 Kc) : Kc) = ((y : 𝓞 Kc) : Kc) := by
      simpa [unitEmbed_coe] using congrArg (fun z : Kcˣ => (z : Kc)) h
    exact Subtype.ext h'
  have ha := unitEmbed_Kc_eq_one_or_eq_neg_one a
  have hb := unitEmbed_Kc_eq_one_or_eq_neg_one b
  by_cases h1 : unitEmbed Kc a = 1
  · have h2 : unitEmbed Kc b = 1 := by
      by_contra h2
      have hne : (if unitEmbed Kc a = 1 then (0 : Fin 2) else 1) ≠
          (if unitEmbed Kc b = 1 then (0 : Fin 2) else 1) := by
        rw [if_pos h1, if_neg h2]
        decide
      exact hne hab
    exact hinj (by rw [h1, h2])
  · have ha' : unitEmbed Kc a = -1 := ha.resolve_left h1
    have h2 : unitEmbed Kc b ≠ 1 := by
      intro h2
      have hne : ¬ ((if unitEmbed Kc a = 1 then (0 : Fin 2) else 1) =
          (if unitEmbed Kc b = 1 then (0 : Fin 2) else 1)) := by
        rw [if_neg h1, if_pos h2]
        decide
      exact hne hab
    have hb' : unitEmbed Kc b = -1 := hb.resolve_left h2
    exact hinj (by rw [ha', hb'])

/-- **`(𝓞 Kc)ˣ = {±1}`**: the ring of integers of `Kc` has at most two units. -/
theorem card_RingUnit_Kc_le_two : Nat.card (RingUnit Kc) ≤ 2 := by
  haveI := finite_RingUnit_Kc
  have hinj : Function.Injective
      (fun u : RingUnit Kc => if unitEmbed Kc u = 1 then (0 : Fin 2) else 1) := by
    intro a b hab
    have hinj' : Function.Injective (unitEmbed Kc) := fun x y h => by
      apply Units.ext
      have h' : ((x : 𝓞 Kc) : Kc) = ((y : 𝓞 Kc) : Kc) := by
        simpa [unitEmbed_coe] using congrArg (fun z : Kcˣ => (z : Kc)) h
      exact Subtype.ext h'
    have ha := unitEmbed_Kc_eq_one_or_eq_neg_one a
    have hb := unitEmbed_Kc_eq_one_or_eq_neg_one b
    by_cases h1 : unitEmbed Kc a = 1
    · have h2 : unitEmbed Kc b = 1 := by
        by_contra h2
        have hne : (if unitEmbed Kc a = 1 then (0 : Fin 2) else 1) ≠
            (if unitEmbed Kc b = 1 then (0 : Fin 2) else 1) := by
          rw [if_pos h1, if_neg h2]
          decide
        exact hne hab
      exact hinj' (by rw [h1, h2])
    · have ha' : unitEmbed Kc a = -1 := ha.resolve_left h1
      have h2 : unitEmbed Kc b ≠ 1 := by
        intro h2
        have hne : ¬ ((if unitEmbed Kc a = 1 then (0 : Fin 2) else 1) =
            (if unitEmbed Kc b = 1 then (0 : Fin 2) else 1)) := by
          rw [if_neg h1, if_pos h2]
          decide
        exact hne hab
      have hb' : unitEmbed Kc b = -1 := hb.resolve_left h2
      exact hinj' (by rw [ha', hb'])
  calc Nat.card (RingUnit Kc) ≤ Nat.card (Fin 2) :=
        Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

end Work.ShafarevichKoch
