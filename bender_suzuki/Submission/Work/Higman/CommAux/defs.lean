/-
Copyright (c) 2024. All rights reserved.

# Auxiliary definitions for Higman's Lemma 3

Higman, *Suzuki 2-groups* (1963), pp. 83--84: if `A` is a normal abelian `X`-subgroup of a
Suzuki 2-group and `C` a normal `X`-subgroup covering `A` with `Φ(C) = Φ(A) = A²`, then `A` has
exponent at most `4`.  This file collects the notions shared by the pieces of that proof:

* `xiSub` -- the restriction of the automorphism `ξ` to a `ξ`-invariant subgroup `A`;
* `l3_omega1_le_of_ne_bot` -- a non-trivial `ξ`-invariant abelian normal subgroup contains `Ω₁(P)`;
* the two "dichotomy" consequences of Higman's Lemma 1 that turn the vanishing of a fourth power
  (resp. of a square) in `A` into membership of `A` in `A ^ (2)`, given the exponent data
  `2 ^ e` of `A`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- The restriction to `↥A` of an automorphism of `P` preserving `A`. -/
def xiSub (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (a : ↥A) : ↥A :=
  ⟨h.xi (a : P), by
    have hmem : h.xi (a : P) ∈ A.map (h.xi : MulAut P).toMonoidHom :=
      Subgroup.mem_map_of_mem _ a.2
    rwa [hAinv] at hmem⟩

@[simp] theorem xiSub_coe (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (a : ↥A) :
    ((xiSub h hAinv a : ↥A) : P) = h.xi (a : P) := rfl

theorem xiSub_mul (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (a b : ↥A) :
    xiSub h hAinv (a * b) = xiSub h hAinv a * xiSub h hAinv b := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, xiSub_coe, map_mul]

/-! ## A non-trivial `ξ`-invariant abelian normal subgroup contains `Ω₁(P)` -/

/-- A non-trivial `ξ`-invariant subgroup of `Ω₁(P)` is all of `Ω₁(P)` (the `ξ`-orbit of a
non-identity involution is everything). -/
theorem l3_eq_omega1_of_ne_bot_of_map_eq (h : IsSuzuki2Grp P) {S : Subgroup P}
    (hS : S ≤ omega1 P) (hSinv : S.map (h.xi : MulAut P).toMonoidHom = S) (hne : S ≠ ⊥) :
    S = omega1 P := by
  rcases invariant_subgroup_inf_omega1 h (⊤ : Subgroup P) (by simpa using hS)
    (by simpa using hSinv) with h1 | h1
  · exact absurd h1 hne
  · simpa using h1

/-- A non-trivial finite `2`-subgroup contains an involution. -/
theorem l3_exists_involution_of_ne_bot (h : IsSuzuki2Grp P) {A : Subgroup P} (hne : A ≠ ⊥) :
    ∃ x ∈ A, x ≠ 1 ∧ x ^ 2 = 1 := by
  have hdvd : 2 ∣ Nat.card ↥A := by
    rcases (h.isPGroup.to_subgroup A).card_eq_or_dvd with h1 | h2
    · exfalso
      have hsub : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp h1).1
      refine hne (le_bot_iff.mp (fun x hx => ?_))
      have hx1 : (⟨x, hx⟩ : ↥A) = 1 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val hx1
    · exact h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz2 : (z : ↥A) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hz]
  refine ⟨(z : P), z.2, ?_, ?_⟩
  · intro hc
    have h1 : (z : ↥A) = 1 := Subtype.ext (by simpa using hc)
    rw [h1] at hz
    exact absurd hz (by norm_num)
  · simpa [Subgroup.coe_pow] using congrArg (fun t : ↥A => (t : P)) hz2

/-- A non-trivial `ξ`-invariant abelian normal subgroup contains `Ω₁(P)`. -/
theorem l3_omega1_le_of_ne_bot (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hne : A ≠ ⊥) : omega1 P ≤ A := by
  have hTinv : (A ⊓ omega1 P).map (h.xi : MulAut P).toMonoidHom = A ⊓ omega1 P := by
    rw [Subgroup.map_inf A (omega1 P) (h.xi : MulAut P).toMonoidHom
      (h.xi : MulAut P).injective, hA.map_eq, map_xi_omega1 h]
  have hTne : A ⊓ omega1 P ≠ ⊥ := by
    obtain ⟨x, hxA, hx1, hx2⟩ := l3_exists_involution_of_ne_bot h hne
    intro hbot
    have hmem : x ∈ (A ⊓ omega1 P : Subgroup P) :=
      Subgroup.mem_inf.mpr ⟨hxA, Subgroup.subset_closure (mem_sqOne.mpr hx2)⟩
    rw [hbot] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)
  have hEq : A ⊓ omega1 P = omega1 P :=
    l3_eq_omega1_of_ne_bot_of_map_eq h inf_le_right hTinv hTne
  rw [← hEq]
  exact inf_le_left

/-! ## Consequences of the exponent data of `A` -/

/-- Higman's dichotomy for the sub-quotient `A / A²`: if `2 ^ e` is the exponent of `A` and
`e ≥ 2`, an element of `A` of order dividing `2` lies in `A ^ (2)`. -/
theorem l3_mem_powSub_two_of_sq_one {A : Subgroup P}
    {e : ℕ} (hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) (he : 2 ≤ e)
    {x : P} (hx : x ∈ A) (hx2 : x * x = 1) : x ∈ powSub A 2 := by
  rw [hkey x hx]
  have hx2' : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have hsplit : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := by
    rw [show e - 1 = e - 2 + 1 from by omega, pow_succ']
  rw [hsplit, pow_mul, hx2']
  simp

/-- Higman's dichotomy for the sub-quotient `A / A²`: if `2 ^ e` is the exponent of `A` and
`e ≥ 3`, an element of `A` whose fourth power is trivial lies in `A ^ (2)`. -/
theorem l3_mem_powSub_two_of_four_one {A : Subgroup P}
    {e : ℕ} (hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) (he : 3 ≤ e)
    {x : P} (hx : x ∈ A) (hx4 : x ^ 4 = 1) : x ∈ powSub A 2 := by
  rw [hkey x hx]
  have hsplit : 2 ^ (e - 1) = 4 * 2 ^ (e - 3) := by
    rw [show e - 1 = 2 + (e - 3) from by omega, pow_add,
      show (2 : ℕ) ^ 2 = 4 from by norm_num]
  rw [hsplit, pow_mul, hx4]
  simp

end Work.Higman
