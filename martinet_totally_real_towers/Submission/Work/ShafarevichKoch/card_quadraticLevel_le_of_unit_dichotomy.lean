import Mathlib
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.nonempty_embedding_quadraticLevel_twoTorsion
import Submission.Work.ShafarevichKoch.hunits_of_unit_dichotomy

/-!
# `Work.ShafarevichKoch.card_quadraticLevel_le_of_unit_dichotomy`

**The Kummer two-descent with the unit dichotomy as a hypothesis.**

Let `F` be a number field and `M` the maximal unramified pro-`2` extension of `F`.  Assume

* every unit of `𝓞 F` is, inside `Fˣ`, either a square or the negative of a square (`hunit`), and
* `-1` is not a square in `M.K` (`hneg`).

Then the number of unramified quadratic levels of `F_∅/F` is at most `2 ^ rank₂ Cl(F) - 1`.

The proof is the Kummer two-descent:

1. `Work.ShafarevichKoch.hunits_of_unit_dichotomy` collapses the unit dichotomy along `M.K`:
   a unit of `𝓞 F` acquiring a square root in `M.K` is already a square in `F`;
2. `Work.ShafarevichKoch.nonempty_embedding_quadraticLevel_twoTorsion` then embeds the
   quadratic levels into the *non-trivial* `2`-torsion classes of `Cl(F)`
   (`L ↦ vClass F a`, `a` a Kummer generator of `L`);
3. the non-trivial `2`-torsion classes are the `2`-torsion classes minus the identity, so there
   are `2 ^ rank₂ Cl(F) - 1` of them
   (`Work.ClassFieldTower.card_quotient_squareSubgroup_eq_card_twoTorsion` together with
   `Work.ClassFieldTower.two_pow_classGroupTwoRank`).

This is the sharpened form of
`Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le_classGroupTwoRank` in which the unit
factor `#(𝓞 Fˣ/(𝓞 Fˣ)²)` has been removed: the `2 ^ unitTwoRank F` factor survives only in the
*unsharp* count `Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **The `2`-torsion of a finite type, minus the identity, has one element less.**

This is the cardinality input of the sharpened Kummer two-descent: the levels inject into the
`2`-torsion classes which are not the identity, and dropping the identity class from a finite type
decreases the cardinality by exactly one. -/
theorem natCard_twoTorsion_subtype_ne_one (F : Type*) [Field F] [NumberField F] :
    Nat.card {c : ClassGroup (𝓞 F) // c ^ 2 = 1 ∧ c ≠ 1}
      = Nat.card {c : ClassGroup (𝓞 F) // c ^ 2 = 1} - 1 := by
  classical
  -- rewrite the conjunction subtype as a subtype of the `2`-torsion, cut out by `≠ 1`
  have hswap : Nat.card {c : ClassGroup (𝓞 F) // c ^ 2 = 1 ∧ c ≠ 1}
      = Nat.card {x : {c : ClassGroup (𝓞 F) // c ^ 2 = 1} // (x : ClassGroup (𝓞 F)) ≠ 1} :=
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun c : ClassGroup (𝓞 F) => c ^ 2 = 1) (fun c => c ≠ 1)).symm
  rw [hswap]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  -- the identity is the unique `2`-torsion class equal to `1`
  have hone : Fintype.card {x : {c : ClassGroup (𝓞 F) // c ^ 2 = 1} //
      (x : ClassGroup (𝓞 F)) = 1} = 1 := by
    let a : {c : ClassGroup (𝓞 F) // c ^ 2 = 1} := ⟨1, by simp⟩
    have hiff : ∀ x : {c : ClassGroup (𝓞 F) // c ^ 2 = 1},
        ((x : ClassGroup (𝓞 F)) = 1) ↔ (x = a) := by
      intro x
      constructor
      · intro hx; exact Subtype.ext hx
      · intro hx; rw [hx]
    have h1 : Fintype.card {x : {c : ClassGroup (𝓞 F) // c ^ 2 = 1} //
        (x : ClassGroup (𝓞 F)) = 1}
        = Fintype.card {x : {c : ClassGroup (𝓞 F) // c ^ 2 = 1} // x = a} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hiff)
    rw [h1, Fintype.card_subtype_eq a]
  -- complement in a finite type
  rw [Fintype.card_subtype_compl (fun x : {c : ClassGroup (𝓞 F) // c ^ 2 = 1} =>
    (x : ClassGroup (𝓞 F)) = 1)]
  rw [hone]

theorem card_quadraticLevel_le_of_unit_dichotomy (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (hunit : ∀ u : Work.ShafarevichKoch.RingUnit F, ∃ y : Fˣ,
      Work.ShafarevichKoch.unitEmbed F u = y ^ 2 ∨
        Work.ShafarevichKoch.unitEmbed F u = -y ^ 2)
    (hneg : ∀ z : M.K, z * z = -1 → False) :
    Nat.card (Work.ShafarevichKoch.QuadraticLevel F M) ≤
      2 ^ Work.ClassFieldTower.classGroupTwoRank F - 1 := by
  classical
  -- the unit dichotomy collapses along the unramified extension
  have hunits := hunits_of_unit_dichotomy F M hunit hneg
  -- the Kummer two-descent, landing in the non-trivial `2`-torsion
  obtain ⟨e⟩ := nonempty_embedding_quadraticLevel_twoTorsion F M hunits
  have hle : Nat.card (QuadraticLevel F M)
      ≤ Nat.card {c : ClassGroup (𝓞 F) // c ^ 2 = 1 ∧ c ≠ 1} :=
    Nat.card_le_card_of_injective e e.injective
  -- the non-trivial `2`-torsion has `2 ^ rank₂ Cl(F) - 1` elements
  have hT : Nat.card {c : ClassGroup (𝓞 F) // c ^ 2 = 1}
      = 2 ^ Work.ClassFieldTower.classGroupTwoRank F :=
    (Work.ClassFieldTower.card_quotient_squareSubgroup_eq_card_twoTorsion
      (ClassGroup (𝓞 F))).symm.trans
        (Work.ClassFieldTower.two_pow_classGroupTwoRank F).symm
  have hcard : Nat.card {c : ClassGroup (𝓞 F) // c ^ 2 = 1 ∧ c ≠ 1}
      = 2 ^ Work.ClassFieldTower.classGroupTwoRank F - 1 := by
    rw [natCard_twoTorsion_subtype_ne_one F, ← hT]
  omega

end Work.ShafarevichKoch
