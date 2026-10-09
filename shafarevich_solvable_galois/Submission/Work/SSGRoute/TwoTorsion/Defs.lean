import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm set of an involution

Let `Ω` be a field and `c : Ω ≃+* Ω` a ring automorphism of order two (`c * c = 1`).  The *norm set*
`normSet c = {x * c x | x ≠ 0}` is the image of the norm map of the quadratic extension
`Ω / Ω^c`.  This file collects the elementary algebraic facts about it that are used to prove that
`-1` is not a norm; that non-representability makes `Ω^c` formally real (it carries an ordering), the
Artin–Schreier input which shows that an involutive automorphism of `ℚ̄` cannot fix a non-trivial
root of unity.

Everything here is stated for an abstract field `Ω` with an involutive ring automorphism, so that
the results apply to `G_ℚ = (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)` through
`AlgEquiv.toRingEquiv`.
-/

namespace Work.SSGRoute
namespace TwoTorsion

variable {Ω : Type*} [Field Ω]

/-- The norm set of a ring automorphism `c : Ω ≃+* Ω`: the elements `x * c x` with `x ≠ 0`. -/
def normSet (c : Ω ≃+* Ω) : Set Ω := {y | ∃ x : Ω, x ≠ 0 ∧ y = x * c x}

@[simp] lemma mem_normSet {c : Ω ≃+* Ω} {y : Ω} :
    y ∈ normSet c ↔ ∃ x : Ω, x ≠ 0 ∧ y = x * c x := Iff.rfl

/-- The second iterate of an involution is the identity. -/
lemma apply_apply {c : Ω ≃+* Ω} (hc : c * c = 1) (x : Ω) : c (c x) = x := by
  have h := congrArg (fun f : Ω ≃+* Ω => f x) hc
  simpa using h

/-- Norms are fixed by `c`. -/
lemma normSet.fixed {c : Ω ≃+* Ω} (hc : c * c = 1) {y : Ω} (hy : y ∈ normSet c) : c y = y := by
  obtain ⟨x, -, rfl⟩ := hy
  rw [map_mul, apply_apply hc x]
  ring

lemma one_mem_normSet (c : Ω ≃+* Ω) : (1 : Ω) ∈ normSet c :=
  ⟨1, one_ne_zero, by simp⟩

lemma zero_notMem_normSet {c : Ω ≃+* Ω} : (0 : Ω) ∉ normSet c := by
  rintro ⟨x, hx, h⟩
  have h' : x * c x = 0 := h.symm
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact hx h0
  · exact hx (c.injective (by simpa using h0))

/-- The norm set is closed under multiplication. -/
lemma normSet.mul_mem {c : Ω ≃+* Ω} {y y' : Ω}
    (hy : y ∈ normSet c) (hy' : y' ∈ normSet c) : y * y' ∈ normSet c := by
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨x', hx', rfl⟩ := hy'
  refine ⟨x * x', mul_ne_zero hx hx', ?_⟩
  rw [map_mul]
  ring

/-- Every norm is the square of a *fixed* element (`Ω` algebraically closed). -/
lemma exists_fixed_sq_of_mem_normSet [IsAlgClosed Ω] {c : Ω ≃+* Ω} (hc : c * c = 1)
    {y : Ω} (hy : y ∈ normSet c) : ∃ m : Ω, c m = m ∧ m ≠ 0 ∧ y = m ^ 2 := by
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self x
  have hs0 : s ≠ 0 := by rintro rfl; exact hx (by simpa using hs)
  refine ⟨s * c s, ?_, mul_ne_zero hs0 (c.map_ne_zero_iff.mpr hs0), ?_⟩
  · rw [map_mul, apply_apply hc s]
    ring
  · have h1 : s * s = x := hs.symm
    have h2 : c s * c s = c x := by rw [← map_mul, h1]
    rw [show (s * c s) ^ 2 = (s * s) * (c s * c s) by rw [pow_two]; ring]
    rw [h1, ← h2]

/-- Every non-zero fixed element is either a norm or the negative of a norm (`Ω` algebraically
closed). -/
lemma mem_or_neg_mem_normSet [IsAlgClosed Ω] {c : Ω ≃+* Ω}
    {a : Ω} (ha : c a = a) (ha0 : a ≠ 0) : a ∈ normSet c ∨ -a ∈ normSet c := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self a
  have hs0 : s ≠ 0 := by rintro rfl; exact ha0 (by simpa using hs)
  have hsq : (s * c s) ^ 2 = a ^ 2 := by
    have h1 : s * s = a := hs.symm
    have h2 : c s * c s = a := by rw [← map_mul, h1, ha]
    rw [show (s * c s) ^ 2 = (s * s) * (c s * c s) by rw [pow_two]; ring]
    rw [h1, h2, pow_two]
  have hprod : (s * c s - a) * (s * c s + a) = 0 := by
    have h3 : (s * c s - a) * (s * c s + a) = (s * c s) ^ 2 - a ^ 2 := by ring
    rw [h3, hsq, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · left
    exact ⟨s, hs0, (sub_eq_zero.mp h).symm⟩
  · right
    refine ⟨s, hs0, ?_⟩
    have h' : s * c s = -a := add_eq_zero_iff_eq_neg.mp h
    exact h'.symm

end TwoTorsion
end Work.SSGRoute
