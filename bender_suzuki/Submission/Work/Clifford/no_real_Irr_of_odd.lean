import Mathlib
import Submission.Work.Clifford.Classes
import Submission.Work.Clifford.card_realIrr_eq_card_realClasses
import Submission.Work.Clifford.card_realClasses_eq_one_of_odd
import Submission.Work.Clifford.realIrr_eq_principal_of_card_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.no_real_Irr_of_odd` — Feit–Thompson 3.13 (Burnside)

A finite group of odd order has no non-principal real valued irreducible character: every
real valued `χ ∈ Irr G` is the principal character.

## The argument

* The real valued irreducible characters of a finite group and its real conjugacy classes are
  equinumerous (`Work.Clifford.card_realIrr_eq_card_realClasses`).  This is Brauer's
  permutation lemma applied to the character table `M χ C = χ (rep C)`: complex conjugation
  `χ ↦ χ̄` permutes the rows (the conjugate of an irreducible character is irreducible: it is
  the Galois twist of `χ` by the automorphism `starRingEnd ℂ` of `ℂ`), inversion `C ↦ C⁻¹`
  permutes the columns, and the two permutations are intertwined by the table because
  `χ (g⁻¹) = star (χ g)`; the fixed points are the real characters
  (`Work.Clifford.IsRealChar`) and the real classes (`Work.Clifford.IsRealClass`).
* In a group of odd order there is exactly one real conjugacy class, the class of the
  identity (`Work.Clifford.card_realClasses_eq_one_of_odd`): an element conjugate to its
  inverse in a group of odd order is trivial.
* Hence there is exactly one real irreducible character; since the principal character is
  real, it is the only one (`Work.Clifford.realIrr_eq_principal_of_card_one`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

/-- **Feit–Thompson 3.13 (Burnside).** In a group of odd order the only real valued
irreducible character is the principal character. -/
theorem no_real_Irr_of_odd {G : Type*} [Group G] [Fintype G] (hG : Odd (Nat.card G))
    {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) (hreal : Work.Clifford.IsRealChar χ) :
    χ = Work.Clifford.principalChar G := by
  -- `#`(real irreducible characters)` = #`(real classes)` = 1`, so there is exactly one
  have hcard : Nat.card {ψ : G → ℂ // ψ ∈ Work.Clifford.Irr G ∧
      Work.Clifford.IsRealChar ψ} = 1 := by
    rw [Work.Clifford.card_realIrr_eq_card_realClasses,
      Work.Clifford.card_realClasses_eq_one_of_odd hG]
  exact Work.Clifford.realIrr_eq_principal_of_card_one hcard hχ hreal

end Work.Clifford
