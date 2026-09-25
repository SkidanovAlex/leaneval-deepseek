import Mathlib
import Submission.Work.ClassFieldTower.two_pow_classGroupTwoRank
import Submission.Work.ClassFieldTower.card_quotient_squareSubgroup_eq_card_twoTorsion

/-!
# `Work.ShafarevichKoch.twoTorsion_card_sub_one`

The cardinality of the **nontrivial** `2`-torsion of the class group,

```
#{c ∈ Cl(F) : c² = 1, c ≠ 1} = 2 ^ rank₂ Cl(F) - 1,
```

the target of the sharpened Kummer embedding
`Work.ShafarevichKoch.nonempty_embedding_quadraticLevel_twoTorsion`.  The `2`-torsion of the
class group is finite and contains the identity, and the "forget the identity" bijection
`Cl(F)[2] ≃ Option {c : c² = 1, c ≠ 1}` reduces the statement to
`2 ^ rank₂ Cl(F) = #Cl(F)[2]` (the workspace lemmas `two_pow_classGroupTwoRank` and
`card_quotient_squareSubgroup_eq_card_twoTorsion`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The number of nontrivial classes of order `2` is `2 ^ rank₂ Cl(F) - 1`.** -/
theorem card_twoTorsion_ne_one (F : Type*) [Field F] [NumberField F] :
    Nat.card {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1 ∧ c ≠ 1}
      = 2 ^ classGroupTwoRank F - 1 := by
  classical
  haveI : Finite (ClassGroup (NumberField.RingOfIntegers F)) := inferInstance
  haveI : Fintype {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1} := Fintype.ofFinite _
  haveI : Fintype {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1 ∧ c ≠ 1} :=
    Fintype.ofFinite _
  -- the "delete the identity" bijection
  have hequiv : Nat.card {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1}
      = Nat.card (Option {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1 ∧ c ≠ 1}) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => if h : (x : ClassGroup (NumberField.RingOfIntegers F)) = 1 then none
          else some ⟨x.1, x.2, h⟩
        invFun := fun o => o.elim ⟨1, by simp⟩ (fun y => ⟨y.1, y.2.1⟩)
        left_inv := ?_
        right_inv := ?_ }
    · rintro ⟨c, hc⟩
      by_cases h : c = 1
      · subst h
        simp
      · simp [h]
    · rintro (_ | ⟨c, hc, hne⟩)
      · simp
      · simp [hne]
  -- `2 ^ rank₂ Cl(F) = #Cl(F)[2]`
  have hrank : Nat.card {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1}
      = 2 ^ classGroupTwoRank F :=
    (card_quotient_squareSubgroup_eq_card_twoTorsion (ClassGroup (NumberField.RingOfIntegers F))).symm.trans
      (two_pow_classGroupTwoRank F).symm
  have hsplit : Nat.card {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1 ∧ c ≠ 1} + 1
      = Nat.card {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1} := by
    rw [hequiv, Nat.card_eq_fintype_card (α := Option _), Fintype.card_option,
      Nat.card_eq_fintype_card (α := {c : ClassGroup (NumberField.RingOfIntegers F) // c ^ 2 = 1 ∧ c ≠ 1})]
  rw [hrank] at hsplit
  omega

end Work.ShafarevichKoch
