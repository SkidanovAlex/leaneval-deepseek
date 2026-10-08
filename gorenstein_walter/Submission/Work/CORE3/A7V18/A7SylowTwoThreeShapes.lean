import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.DSTR.layerShape
import Submission.Work.A7.Defs

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE3.A7V18

/-!
# `CORE3` / `A7V18` / `A7SylowTwoThreeShapes`

Every group `Q` that is one of the three "shapes" occurring in the `A₇` branch of the
Gorenstein–Walter argument — a 2-group, an extension of a self-centralizing normal Klein
four-group, or `A₇` itself — and that *contains* a quasisimple `E` with `E/Z(E) ≅ A₇`, has
`2`-part of its order equal to `8`.

The two "small" shapes are impossible: a 2-group is nilpotent, hence solvable, and a group with a
normal self-centralizing four-subgroup is solvable (`Work.DSTR.isSolvable_of_normal_fourGroup_selfCentralizing`);
in both cases `E ≤ Q` is then solvable, so the quotient `E/Z(E)` is solvable, contradicting
`Work.DSTR.not_isSolvable_quotient_center` (for quasisimple `E`, `E/Z(E)` is simple non-abelian).
So only the shape `Q ≅ A₇` remains, where `|Q| = |A₇| = 7!/2 = 2520 = 2³ · 315` and the
`2`-adic valuation is `3`.
-/

theorem A7SylowTwoThreeShapes {Q : Type} [Group Q] [Finite Q] (h : IsPGroup 2 Q ∨ (∃ V : Subgroup Q, V.Normal ∧ Work.GW2.IsFourGroup V ∧ Subgroup.centralizer (V : Set Q) = V) ∨ Nonempty (Q ≃* alternatingGroup (Fin 7))) (E : Subgroup Q) (hEq : Work.GW2.IsQuasisimple E) (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7))) : 2 ^ (Nat.card Q).factorization 2 = 8 := by
  -- For quasisimple `E`, the quotient `E ⧸ Z(E)` is simple non-abelian, hence not solvable.
  have hnsolv : ¬ Group.IsSolvable (↥E ⧸ Subgroup.center ↥E) :=
    Work.DSTR.not_isSolvable_quotient_center hEq
  rcases h with hpg | ⟨V, hVn, hV4, hVc⟩ | he7
  · -- `Q` is a 2-group: nilpotent, hence solvable, so every subgroup is solvable.
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent Q := hpg.isNilpotent
    haveI : Group.IsSolvable Q := inferInstance
    haveI : Group.IsSolvable ↥E := inferInstance
    haveI : Group.IsSolvable (↥E ⧸ Subgroup.center ↥E) := inferInstance
    exact (hnsolv inferInstance).elim
  · -- `Q` has a normal self-centralizing four-subgroup: then `Q` is solvable.
    haveI : Group.IsSolvable Q :=
      Work.DSTR.isSolvable_of_normal_fourGroup_selfCentralizing V hVn hV4 hVc
    haveI : Group.IsSolvable ↥E := inferInstance
    haveI : Group.IsSolvable (↥E ⧸ Subgroup.center ↥E) := inferInstance
    exact (hnsolv inferInstance).elim
  · -- `Q ≅ A₇`: the order is `7! / 2 = 2520 = 2³ · 315`, whose `2`-adic valuation is `3`.
    obtain ⟨e7⟩ := he7
    have hcardQ : Nat.card Q = 2520 := by
      rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    rw [hcardQ,
      show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
      Nat.factorization_mul (by norm_num : (2 : ℕ) ^ 3 ≠ 0) (by norm_num : (315 : ℕ) ≠ 0),
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬(2 : ℕ) ∣ 315)]
    norm_num

end Work.CORE3.A7V18
