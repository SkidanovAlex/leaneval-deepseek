import Submission.Prelude
import Mathlib.Tactic.Group

open UnitConjecture

set_option autoImplicit false

noncomputable section

namespace Submission

-- ============================================================
-- Basic consequences of the relators (in P)
-- ============================================================

lemma a2_b_a2 : a ^ 2 * b * a ^ 2 = b := by
  calc
    a ^ 2 * b * a ^ 2 = b * (b⁻¹ * a ^ 2 * b * a ^ 2) := by group
    _ = b * 1 := by rw [rel1]
    _ = b := by simp

lemma b2_a_b2 : b ^ 2 * a * b ^ 2 = a := by
  calc
    b ^ 2 * a * b ^ 2 = a * (a⁻¹ * b ^ 2 * a * b ^ 2) := by group
    _ = a * 1 := by rw [rel2]
    _ = a := by simp

lemma a2_mul_b : a ^ 2 * b = b * (a ^ 2)⁻¹ := by
  have h := a2_b_a2
  calc
    a ^ 2 * b = (a ^ 2 * b * a ^ 2) * (a ^ 2)⁻¹ := by group
    _ = b * (a ^ 2)⁻¹ := by rw [h]

lemma b_mul_a2 : b * a ^ 2 = (a ^ 2)⁻¹ * b := by
  have h := a2_b_a2
  calc
    b * a ^ 2 = (a ^ 2)⁻¹ * (a ^ 2 * b * a ^ 2) := by group
    _ = (a ^ 2)⁻¹ * b := by rw [h]

lemma b2_mul_a : b ^ 2 * a = a * (b ^ 2)⁻¹ := by
  have h := b2_a_b2
  calc
    b ^ 2 * a = (b ^ 2 * a * b ^ 2) * (b ^ 2)⁻¹ := by group
    _ = a * (b ^ 2)⁻¹ := by rw [h]

lemma a_mul_b2 : a * b ^ 2 = (b ^ 2)⁻¹ * a := by
  have h := b2_a_b2
  calc
    a * b ^ 2 = (b ^ 2)⁻¹ * (b ^ 2 * a * b ^ 2) := by group
    _ = (b ^ 2)⁻¹ * a := by rw [h]

-- x = a^2, y = b^2 pushes
lemma x_mul_b : x * b = b * x⁻¹ := by
  simpa [x_eq_a2] using a2_mul_b

lemma b_mul_x : b * x = x⁻¹ * b := by
  simpa [x_eq_a2] using b_mul_a2

lemma y_mul_a : y * a = a * y⁻¹ := by
  simpa [y_eq_b2] using b2_mul_a

lemma a_mul_y : a * y = y⁻¹ * a := by
  simpa [y_eq_b2] using a_mul_b2

-- x and y commute
lemma xy_comm : x * y = y * x := by
  calc
    x * y = x * (b * b) := by rw [y_eq_b2, pow_two]
    _ = (x * b) * b := by group
    _ = (b * x⁻¹) * b := by rw [x_mul_b]
    _ = b * (x⁻¹ * b) := by group
    _ = b * (b * x) := by rw [b_mul_x]
    _ = (b * b) * x := by group
    _ = y * x := by simpa [y_eq_b2, pow_two]

-- ============================================================
-- z = (ab)^2 ; conjugation properties of z
-- ============================================================

lemma z_exp : z = a * b * a * b := by
  rw [z_eq_ab2]
  rw [pow_two]
  group

lemma a2_mul_b_word : a * a * b = b * a⁻¹ * a⁻¹ := by
  have h := a2_mul_b
  calc
    a * a * b = a ^ 2 * b := by rw [pow_two]
    _ = b * (a ^ 2)⁻¹ := h
    _ = b * a⁻¹ * a⁻¹ := by group

/-- a⁻¹ z a z = 1 -/
lemma conj_az : a⁻¹ * z * a * z = 1 := by
  calc
    a⁻¹ * z * a * z = b * a * b * (a * a * b) * a * b := by
      rw [z_exp]
      group
    _ = b * a * b * (b * a⁻¹ * a⁻¹) * a * b := by
      rw [a2_mul_b_word]
    _ = b * a * b * b * a⁻¹ * b := by
      group
    _ = b * (a * (b * b)) * a⁻¹ * b := by
      group
    _ = b * (a * b ^ 2) * a⁻¹ * b := by
      rw [← pow_two]
    _ = b * ((b ^ 2)⁻¹ * a) * a⁻¹ * b := by
      rw [a_mul_b2]
    _ = 1 := by
      rw [show (b ^ 2)⁻¹ = b⁻¹ * b⁻¹ by group]
      group

-- ============================================================
-- z = (ab)^2 ; conjugation properties of z
-- ============================================================

/-- a⁻¹ z a = z⁻¹ -/
lemma az_inv : a⁻¹ * z * a = z⁻¹ := by
  calc
    a⁻¹ * z * a = (a⁻¹ * z * a * z) * z⁻¹ := by group
    _ = 1 * z⁻¹ := by rw [conj_az]
    _ = z⁻¹ := by simp

/-- z a = a z⁻¹ -/
lemma z_mul_a : z * a = a * z⁻¹ := by
  calc
    z * a = a * (a⁻¹ * z * a) := by group
    _ = a * z⁻¹ := by rw [az_inv]

/-- a z = z⁻¹ a -/
lemma a_mul_z : a * z = z⁻¹ * a := by
  have h : z * a * z = a := by
    calc
      z * a * z = a * (a⁻¹ * z * a * z) := by group
      _ = a * 1 := by rw [conj_az]
      _ = a := by simp
  calc
    a * z = z⁻¹ * (z * a * z) := by group
    _ = z⁻¹ * a := by rw [h]

/-- z = b⁻¹ z⁻¹ b -/
lemma z_eq_bz : z = b⁻¹ * z⁻¹ * b := by
  calc
    z = (a * b)⁻¹ * z * (a * b) := by
      rw [z_eq_ab2, pow_two]
      group
    _ = b⁻¹ * (a⁻¹ * z * a) * b := by group
    _ = b⁻¹ * z⁻¹ * b := by rw [az_inv]

/-- b z = z⁻¹ b -/
lemma b_mul_z : b * z = z⁻¹ * b := by
  have h : b * z * b⁻¹ = z⁻¹ := by
    calc
      b * z * b⁻¹ = (b * (b⁻¹ * z⁻¹ * b)) * b⁻¹ := by
        conv_lhs => rw [z_eq_bz]
      _ = z⁻¹ := by group
  calc
    b * z = (b * z * b⁻¹) * b := by group
    _ = z⁻¹ * b := by rw [h]

/-- b⁻¹ z b = z⁻¹ -/
lemma bz_inv : b⁻¹ * z * b = z⁻¹ := by
  calc
    b⁻¹ * z * b = (b⁻¹ * z⁻¹ * b)⁻¹ := by group
    _ = z⁻¹ := by rw [← z_eq_bz]

/-- z b = b z⁻¹ -/
lemma z_mul_b : z * b = b * z⁻¹ := by
  calc
    z * b = b * (b⁻¹ * z * b) := by group
    _ = b * z⁻¹ := by rw [bz_inv]

/-- x commutes with z -/
lemma xz_comm : x * z = z * x := by
  have h : a ^ 2 * z = z * a ^ 2 := by
    calc
      a ^ 2 * z = a * (a * z) := by rw [pow_two]; group
      _ = a * (z⁻¹ * a) := by rw [a_mul_z]
      _ = (a * z⁻¹) * a := by group
      _ = (z * a) * a := by rw [z_mul_a]
      _ = z * a ^ 2 := by rw [pow_two]; group
  simpa [x_eq_a2] using h

/-- y commutes with z -/
lemma yz_comm : y * z = z * y := by
  have h : b ^ 2 * z = z * b ^ 2 := by
    calc
      b ^ 2 * z = b * (b * z) := by rw [pow_two]; group
      _ = b * (z⁻¹ * b) := by rw [b_mul_z]
      _ = (b * z⁻¹) * b := by group
      _ = (z * b) * b := by rw [z_mul_b]
      _ = z * b ^ 2 := by rw [pow_two]; group
  simpa [y_eq_b2] using h

end Submission
