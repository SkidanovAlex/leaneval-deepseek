/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 9 (existence form): assembly of the final step

The target `Work.Higman.maximal_abelian_invariant_ge_phi` produces a maximal `ξ`-invariant
abelian normal subgroup `A` of a Suzuki 2-group `P` together with

* `Ω₁(P) ≤ A`, `[P,P] ≤ A`, `∀ x : P, x ^ 2 ∈ A` (i.e. `Φ(P) ≤ A`);
* `A ^ (4) = ⊥`, i.e. `exp A ≤ 4`.

Maximality (`exists_maximal_isXiAbelNormal`) and `Ω₁(P) ≤ A` (`omega1_le_of_maximal`) are already
proved here, as is `Z(P) ≤ A` (`center_le_of_maximal`).  This file records that *everything else*
follows from the two structural facts

* `[P,P] ≤ Z(P)` and `x ^ 2 ∈ Z(P)` for every `x` (`Work.Higman.suzuki_class_two_squares`), and
* `Z(P) = Ω₁(P)` (`Work.Higman.center_eq_omega1`),

which are proved elsewhere in the workspace.  Concretely: `A ⊇ Z(P)` and `Z(P) = Ω₁(P)` has
exponent `2`, while `A ^ 2 ⊆ Z(P)` because every square is central; hence `A ^ 4 = 1`.

The two `theorem`s below take those structural facts as explicit hypotheses, so that this module
is sorry-free; plugging in the finished statements gives the target theorem verbatim.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- The commutator subgroup of a Suzuki 2-group is contained in `A`. -/
theorem commutator_le_of_maximal (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P) : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A :=
  hcomm.trans (center_le_of_maximal h hA hmax)

/-- Every square of a Suzuki 2-group lies in `A`. -/
theorem sq_mem_of_maximal (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P) : ∀ x : P, x ^ 2 ∈ A :=
  fun x => center_le_of_maximal h hA hmax (hsq x)

/-- If the centre of a Suzuki 2-group is its `Ω₁` and every square is central, then a maximal
`ξ`-invariant abelian normal subgroup has exponent dividing `4`. -/
theorem powSub_four_bot_of_maximal (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P) (hZ : Subgroup.center P = omega1 P) :
    powSub A 4 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨x, _hxA, rfl⟩ := (mem_powSub_iff (hA.abelian)).mp hy
  have hxZ : x ^ 2 ∈ Subgroup.center P := hsq x
  have hxO : x ^ 2 ∈ omega1 P := hZ ▸ hxZ
  have h2 : (x ^ 2) ^ 2 = 1 := h.mem_omega1.mp hxO
  have h3 : (x ^ 2) ^ 2 = x ^ 4 := by rw [← pow_mul]
  show x ^ 4 ∈ (⊥ : Subgroup P)
  rw [Subgroup.mem_bot, ← h3]
  exact h2

/-- **Higman 1963, Lemma 9 (existence form).**  Assembly from the structural facts. -/
theorem maximal_abelian_of_ingredients (h : IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P)
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P) (hZ : Subgroup.center P = omega1 P) :
    ∃ A : Subgroup P, A.Normal ∧ A.map (h.xi : MulAut P).toMonoidHom = A ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      (∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A) ∧
      omega1 P ≤ A ∧ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A ∧ (∀ x : P, x ^ 2 ∈ A) ∧
      powSub A 4 = ⊥ := by
  obtain ⟨A, hA, hmax⟩ := exists_maximal_isXiAbelNormal h
  have hmax' : ∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A :=
    fun B hn hi hab hAB => hmax B ⟨hn, hi, hab⟩ hAB
  exact ⟨A, hA.normal, hA.map_eq, hA.abelian, hmax', omega1_le_of_maximal h hA hmax,
    commutator_le_of_maximal h hA hmax hcomm, sq_mem_of_maximal h hA hmax hsq,
    powSub_four_bot_of_maximal h hA hmax hsq hZ⟩

end Work.Higman
