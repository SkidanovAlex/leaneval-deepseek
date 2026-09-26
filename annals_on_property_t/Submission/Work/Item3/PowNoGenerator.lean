import Submission.Work.Nielsen
import Mathlib.Tactic

open FreeGroup
set_option autoImplicit false

/-!
# No square in a free group is a generator

A standard generator of `F_n` has no square root: for every `x : Fₙ` and every
coordinate `u`, `x * x` is neither `a_u` nor `a_u⁻¹`.

The proof is the exponent-sum character: the homomorphism
`χ : F_n → Multiplicative ℤ` with `χ a_u = ofAdd 1`, `χ a_j = 1` (`j ≠ u`)
sends `x * x` to `χ x * χ x` (whose additive value is `2 · χ x`, even) while
`a_u^{±1}` has additive value `±1` (odd).

This rules out the degenerate half-length-1 balanced configuration `A = B`
(a balanced element would then be the square of a generator, hence not part of
a basis — the free-group form of "a basis element is not a proper power", in
the only case the balanced-side energy argument needs).

All lemmas kernel-checked.
-/

namespace Submission.Nielsen

/-- The exponent-sum character isolating a coordinate: `a_u ↦ ofAdd 1`,
`a_j ↦ 1` (`j ≠ u`), with values in `Multiplicative ℤ`. -/
noncomputable def coordChar (n : ℕ) (u : Fin n) :
    FreeGroup (Fin n) →* Multiplicative ℤ :=
  FreeGroup.lift (fun j : Fin n => if j = u then Multiplicative.ofAdd (1 : ℤ) else 1)

lemma coordChar_of (n : ℕ) (u j : Fin n) : coordChar n u (FreeGroup.of j) =
    if j = u then Multiplicative.ofAdd (1 : ℤ) else 1 :=
  FreeGroup.lift_apply_of

lemma coordChar_self (n : ℕ) (u : Fin n) :
    coordChar n u (FreeGroup.of u) = Multiplicative.ofAdd (1 : ℤ) := by
  rw [coordChar_of, if_pos rfl]

lemma coordChar_other (n : ℕ) {u j : Fin n} (h : j ≠ u) :
    coordChar n u (FreeGroup.of j) = 1 := by
  rw [coordChar_of, if_neg h]

/-- The additive value of `χ (a_u⁻¹)` is `-1`. -/
lemma coordChar_toAdd_inv_self (n : ℕ) (u : Fin n) :
    (coordChar n u ((FreeGroup.of u)⁻¹)).toAdd = -1 := by
  rw [(coordChar n u).map_inv, coordChar_self]
  simp

/-- The additive value of `χ (x * x)` is twice the additive value of `χ x`. -/
lemma coordChar_toAdd_mul_self (n : ℕ) (u : Fin n) (x : FreeGroup (Fin n)) :
    (coordChar n u (x * x)).toAdd = 2 * (coordChar n u x).toAdd := by
  rw [(coordChar n u).map_mul, toAdd_mul]
  ring

/-- **No square of an element of `F_n` is a standard generator (or its
inverse).** -/
theorem sq_ne_of {n : ℕ} (x : FreeGroup (Fin n)) (u : Fin n) :
    x * x ≠ FreeGroup.of u ∧ x * x ≠ (FreeGroup.of u)⁻¹ := by
  constructor
  · intro h
    have h1 := congrArg (coordChar n u) h
    rw [coordChar_self] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    rw [coordChar_toAdd_mul_self] at h2
    simp at h2
    omega
  · intro h
    have h1 := congrArg (coordChar n u) h
    have h2 := congrArg Multiplicative.toAdd h1
    rw [coordChar_toAdd_mul_self, coordChar_toAdd_inv_self] at h2
    omega

/-- Equivalent form: there is no element whose square is `±a_u`. -/
theorem not_exists_sq_eq_generator {n : ℕ} (u : Fin n) :
    ¬ ∃ x : FreeGroup (Fin n), x * x = FreeGroup.of u ∨ x * x = (FreeGroup.of u)⁻¹ := by
  rintro ⟨x, h | h⟩
  · exact (sq_ne_of x u).1 h
  · exact (sq_ne_of x u).2 h

end Submission.Nielsen
