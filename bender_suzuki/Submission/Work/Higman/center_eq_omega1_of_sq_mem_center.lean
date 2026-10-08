import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.center_eq_omega1
import Submission.Work.Higman.commutator_sq_eq_one_of_sq_mem_center
import Submission.Work.Higman.inv_sq_mul_sq_eq_commutator_inv
import Submission.Work.Higman.card_eq_one_of_sq_descends

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

open scoped commutatorElement

/-- In a Suzuki 2-group `P` with `|P| = |Z(P)|²` in which every square is central,
`Z(P) = Ω₁(P)`.

Suppose `Z(P) ≠ Ω₁(P)`.  Then `Ω₁(P) ≤ Z(P)²` (Higman), and since every commutator is an
involution (all squares are central), `P' ≤ Ω₁(P) ≤ Z(P)²`.  Hence the squaring map
`P → Z(P)/Z(P)²`, `x ↦ x²` descends to a homomorphism `P/Z(P) → Z(P)/Z(P)²`, which is
injective because an element whose square is a square of a central element is central
(Higman's Lemma 2).  So `|P/Z(P)| ≤ |Z(P)/Z(P)²|`.  But `|P/Z(P)| = |P|/|Z(P)| = |Z(P)|`
and `|Z(P)| = |Z(P)²| · |Z(P)/Z(P)²|`, forcing `Z(P)² = 1`, i.e. `Z(P) ≤ Ω₁(P)`, a
contradiction. -/
theorem center_eq_omega1_of_sq_mem_center {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2)
    (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P) :
    Subgroup.center P = Work.Higman.omega1 P := by
  refine le_antisymm ?_ h.omega1_le_center
  by_cases hcase : Subgroup.center P = Work.Higman.omega1 P
  · rw [hcase]
  · have hnotle : ¬ Subgroup.center P ≤ Work.Higman.omega1 P :=
      fun hle => hcase (le_antisymm hle h.omega1_le_center)
    obtain ⟨z, hz, hzO⟩ : ∃ z : P, z ∈ Subgroup.center P ∧ z ∉ Work.Higman.omega1 P := by
      by_contra hc
      exact hnotle (fun x hx => by
        by_contra hxO
        exact hc ⟨x, hx, hxO⟩)
    have hz2 : z ^ 2 ≠ 1 := fun h2 => hzO (h.mem_omega1.mpr h2)
    have hOm : Work.Higman.omega1 P ≤ Work.Higman.centerSq P :=
      omega1_le_centerSq h ⟨z, hz, hz2⟩
    have hbot : Work.Higman.centerSq P = ⊥ :=
      card_eq_one_of_sq_descends (Work.Higman.centerSq P) centerSq_le_center hb
        (fun z hz => by simpa [pow_two] using sq_mem_centerSq hz)
        (fun x y => by
          rw [inv_sq_mul_sq_eq_commutator_inv hb x y]
          exact hOm (Subgroup.inv_mem (Work.Higman.omega1 P)
            (h.mem_omega1.mpr (commutator_sq_eq_one_of_sq_mem_center hb x y))))
        (fun x hx => mem_center_of_sq_mem_centerSq h hx)
        hcard
    intro w hw
    have hw2 : w * w ∈ Work.Higman.centerSq P := sq_mem_centerSq hw
    rw [hbot] at hw2
    rw [Subgroup.mem_bot] at hw2
    exact h.mem_omega1.mpr (by rwa [pow_two])

end Work.Higman
