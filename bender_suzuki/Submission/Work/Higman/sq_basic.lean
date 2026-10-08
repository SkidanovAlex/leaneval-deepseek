/-
Copyright (c) 2024. All rights reserved.

# Auxiliary structure facts for Suzuki 2-groups (own copy)

This module collects the elementary facts about `Ω₁(P)` and about `ξ`-invariant abelian normal
subgroups of a Suzuki 2-group that the proof of
`Work.Higman.sq_mem_center_of_suzuki` needs, stated for the *non-maximal* setting (a
`ξ`-invariant abelian normal subgroup `A ≠ ⊥` already contains `Ω₁(P)`).

The proofs are the standard ones (Higman 1963, §2--§3); they are reproduced here so that the
final module `Submission.Work.Higman.sq_mem_center_of_suzuki` rests only on modules that are
free of `sorry`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P]

/-! ## Restricting an automorphism to an invariant subgroup -/

/-- The automorphism of a `φ`-invariant subgroup induced by `φ`. -/
def sq_mulAutSubtype (S : Subgroup P) (φ : MulAut P) (hS : S.map φ.toMonoidHom = S) :
    MulAut ↥S where
  toFun s := ⟨φ s, by
    have hmem : φ (s : P) ∈ S.map φ.toMonoidHom := Subgroup.mem_map.mpr ⟨(s : P), s.2, rfl⟩
    rwa [hS] at hmem⟩
  invFun s := ⟨φ.symm (s : P), by
    have hmem : (s : P) ∈ S.map φ.toMonoidHom := by rw [hS]; exact s.2
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
    have hys : φ.symm (s : P) = y := by
      rw [← hyeq]
      simp
    rw [hys]; exact hy⟩
  left_inv s := Subtype.ext (by show φ.symm (φ (s : P)) = (s : P); simp)
  right_inv s := Subtype.ext (by show φ (φ.symm (s : P)) = (s : P); simp)
  map_mul' s t := Subtype.ext (by show φ ((s : P) * (t : P)) = φ (s : P) * φ (t : P); simp)

@[simp] theorem sq_mulAutSubtype_apply (S : Subgroup P) (φ : MulAut P)
    (hS : S.map φ.toMonoidHom = S) (s : ↥S) :
    ((sq_mulAutSubtype S φ hS s : ↥S) : P) = φ s := rfl

theorem sq_mulAutSubtype_pow_apply (S : Subgroup P) (φ : MulAut P)
    (hS : S.map φ.toMonoidHom = S) : ∀ (k : ℕ) (s : ↥S),
    (((sq_mulAutSubtype S φ hS) ^ k) s : P) = (φ ^ k) s := by
  intro k
  induction k with
  | zero => intro s; simp
  | succ k ih =>
      intro s
      rw [pow_succ, MulAut.mul_apply, ih, sq_mulAutSubtype_apply, pow_succ, MulAut.mul_apply]

end Work.Higman

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- Conjugating an element of a normal subgroup: `g⁻¹ * z * g ∈ A`. -/
theorem sq_conj_mem {G : Type*} [Group G] {A : Subgroup G} (hAn : A.Normal) {z g : G}
    (hz : z ∈ A) : g⁻¹ * z * g ∈ A := by
  have h := hAn.conj_mem z hz g⁻¹
  simpa [mul_assoc] using h

/-- A non-trivial `ξ`-invariant subgroup of `Ω₁(P)` is all of `Ω₁(P)`: `ξ` acts transitively on
the involutions, so the `ξ`-orbit of a non-identity element is everything. -/
theorem sq_eq_omega1_of_ne_bot_of_map_eq (h : IsSuzuki2Grp P) {S : Subgroup P}
    (hS : S ≤ omega1 P) (hSinv : S.map (h.xi : MulAut P).toMonoidHom = S) (hne : S ≠ ⊥) :
    S = omega1 P := by
  rcases invariant_subgroup_inf_omega1 h (⊤ : Subgroup P) (by simpa using hS)
    (by simpa using hSinv) with h1 | h1
  · exact absurd h1 hne
  · simpa using h1

/-- A non-trivial finite `2`-subgroup contains an involution. -/
theorem sq_exists_involution_of_ne_bot (h : IsSuzuki2Grp P) {A : Subgroup P} (hne : A ≠ ⊥) :
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

/-- A non-trivial `ξ`-invariant abelian normal subgroup of a Suzuki 2-group contains `Ω₁(P)`. -/
theorem sq_omega1_le_of_isXiAbelNormal_ne_bot (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hne : A ≠ ⊥) : omega1 P ≤ A := by
  have hTinv : (A ⊓ omega1 P).map (h.xi : MulAut P).toMonoidHom = A ⊓ omega1 P := by
    rw [Subgroup.map_inf A (omega1 P) (h.xi : MulAut P).toMonoidHom
      (h.xi : MulAut P).injective, hA.map_eq, map_xi_omega1 h]
  have hTne : A ⊓ omega1 P ≠ ⊥ := by
    obtain ⟨x, hxA, hx1, hx2⟩ := sq_exists_involution_of_ne_bot h hne
    intro hbot
    have hmem : x ∈ (A ⊓ omega1 P : Subgroup P) :=
      Subgroup.mem_inf.mpr ⟨hxA, Subgroup.subset_closure (mem_sqOne.mpr hx2)⟩
    rw [hbot] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)
  have hEq : A ⊓ omega1 P = omega1 P :=
    sq_eq_omega1_of_ne_bot_of_map_eq h inf_le_right hTinv hTne
  rw [← hEq]
  exact inf_le_left

/-- A non-identity element of `Ω₁(P)` has order two. -/
theorem sq_orderOf_eq_two_of_mem_omega1 (h : IsSuzuki2Grp P) {x : P} (hx : x ∈ omega1 P)
    (hx1 : x ≠ 1) : orderOf x = 2 := by
  have hd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ((h.mem_omega1).mp hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h2

/-- The `ξ`-action on `Ω₁(P)`: `ξ` restricts to an automorphism of `Ω₁(P)`. -/
def sq_xiOmega1 (h : IsSuzuki2Grp P) : MulAut ↥(omega1 P) :=
  sq_mulAutSubtype (omega1 P) h.xi (map_xi_omega1 h)

theorem sq_xiOmega1_pow_apply (h : IsSuzuki2Grp P) : ∀ (k : ℕ) (a : ↥(omega1 P)),
    (((sq_xiOmega1 h) ^ k) a : P) = (h.xi ^ k) a :=
  sq_mulAutSubtype_pow_apply (omega1 P) h.xi (map_xi_omega1 h)

/-- `ξ` acts transitively on the non-identity elements of `Ω₁(P)`. -/
theorem sq_trans_omega1 (h : IsSuzuki2Grp P) :
    ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, ((sq_xiOmega1 h) ^ k) a = b := by
  intro a b ha hb
  have ha' : (a : P) ≠ 1 := fun hc => ha (Subtype.ext hc)
  have hb' : (b : P) ≠ 1 := fun hc => hb (Subtype.ext hc)
  obtain ⟨k, hk⟩ := h.trans (a : P) (b : P)
    (sq_orderOf_eq_two_of_mem_omega1 h a.2 ha') (sq_orderOf_eq_two_of_mem_omega1 h b.2 hb')
  exact ⟨k, Subtype.ext (by rw [sq_xiOmega1_pow_apply, hk])⟩

end Work.Higman
