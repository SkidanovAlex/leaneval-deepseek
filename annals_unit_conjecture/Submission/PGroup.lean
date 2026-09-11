import Submission.GroupIdentities
import Mathlib.Tactic.FinCases

open UnitConjecture

set_option autoImplicit false

noncomputable section

namespace Submission

open scoped Classical

/-- Exponent triples for the normal form. -/
abbrev E := ℤ × ℤ × ℤ

/-- Normal-form monomial map. -/
def w (m : E) : P := x ^ m.1 * y ^ m.2.1 * z ^ m.2.2

lemma xz_pow_comm (t u : ℤ) : z ^ t * x ^ u = x ^ u * z ^ t := by
  exact (Commute.zpow_zpow (show Commute x z from xz_comm) u t).eq.symm
lemma yz_pow_comm (t u : ℤ) : z ^ t * y ^ u = y ^ u * z ^ t := by
  exact (Commute.zpow_zpow (show Commute y z from yz_comm) u t).eq.symm
lemma xy_pow_comm (t u : ℤ) : x ^ t * y ^ u = y ^ u * x ^ t := by
  exact (Commute.zpow_zpow (show Commute x y from xy_comm) t u).eq

lemma w_zero : w 0 = 1 := by
  simp [w]

lemma w_hom (m m' : E) : w (m + m') = w m * w m' := by
  rcases m with ⟨a, b, c⟩; rcases m' with ⟨a', b', c'⟩
  simp [w]
  symm
  calc
    (x ^ a * y ^ b * z ^ c) * (x ^ a' * y ^ b' * z ^ c')
        = x ^ a * y ^ b * (z ^ c * x ^ a') * (y ^ b' * z ^ c') := by group
    _ = x ^ a * y ^ b * (x ^ a' * z ^ c) * (y ^ b' * z ^ c') := by
      rw [xz_pow_comm c a']
    _ = x ^ a * (y ^ b * x ^ a') * z ^ c * (y ^ b' * z ^ c') := by group
    _ = x ^ a * (x ^ a' * y ^ b) * z ^ c * (y ^ b' * z ^ c') := by
      rw [xy_pow_comm a' b]
    _ = (x ^ a * x ^ a') * y ^ b * z ^ c * (y ^ b' * z ^ c') := by group
    _ = x ^ (a + a') * y ^ b * (z ^ c * y ^ b') * z ^ c' := by
      rw [← zpow_add]
      group
    _ = x ^ (a + a') * y ^ b * (y ^ b' * z ^ c) * z ^ c' := by
      rw [yz_pow_comm c b']
    _ = x ^ (a + a') * (y ^ b * y ^ b') * (z ^ c * z ^ c') := by group
    _ = x ^ (a + a') * y ^ (b + b') * z ^ (c + c') := by
      rw [← zpow_add]
      group

lemma w_neg (m : E) : w (-m) = (w m)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  calc
    w (-m) * w m = w (-m + m) := by rw [w_hom]
    _ = w 0 := by
      congr
      ext <;> simp
    _ = 1 := w_zero


-- ============================================================
-- zpow-push lemmas: conjugator times a power of a generator
-- ============================================================

/-- If c conjugates g to g^s then c pushes past g^t. -/
lemma conj_push {c g : P} (s : ℤ) (h : MulAut.conj c g = g ^ s) (t : ℤ) :
    c * g ^ t = g ^ (s * t) * c := by
  let φ : P →* P := MulAut.conj c
  have hφ : φ g = g ^ s := h
  have hp : c * g ^ t * c⁻¹ = g ^ (s * t) := by
    calc
      c * g ^ t * c⁻¹ = φ (g ^ t) := by simp [φ, MulAut.conj_apply]
      _ = φ g ^ t := by rw [map_zpow]
      _ = (g ^ s) ^ t := by rw [hφ]
      _ = g ^ (s * t) := by rw [zpow_mul]
  calc
    c * g ^ t = (c * g ^ t * c⁻¹) * c := by group
    _ = g ^ (s * t) * c := by rw [hp]

lemma a_pow_x (t : ℤ) : a * x ^ t = x ^ t * a := by
  have h : a * x = x * a := by
    rw [x_eq_a2]
    group
  exact (Commute.zpow_right (show Commute a x from h) t).eq

lemma a_pow_y (t : ℤ) : a * y ^ t = y ^ (-t) * a := by
  simpa [zpow_neg] using
    (conj_push (c := a) (g := y) (-1) (by
      rw [MulAut.conj_apply]
      rw [a_mul_y]
      group
    ) t)

lemma a_pow_z (t : ℤ) : a * z ^ t = z ^ (-t) * a := by
  simpa [zpow_neg] using
    (conj_push (c := a) (g := z) (-1) (by
      rw [MulAut.conj_apply]
      rw [a_mul_z]
      group
    ) t)

lemma b_pow_y (t : ℤ) : b * y ^ t = y ^ t * b := by
  have h : b * y = y * b := by
    rw [y_eq_b2]
    group
  exact (Commute.zpow_right (show Commute b y from h) t).eq

lemma b_pow_x (t : ℤ) : b * x ^ t = x ^ (-t) * b := by
  simpa [zpow_neg] using
    (conj_push (c := b) (g := x) (-1) (by
      rw [MulAut.conj_apply]
      rw [b_mul_x]
      group
    ) t)

lemma b_pow_z (t : ℤ) : b * z ^ t = z ^ (-t) * b := by
  simpa [zpow_neg] using
    (conj_push (c := b) (g := z) (-1) (by
      rw [MulAut.conj_apply]
      rw [b_mul_z]
      group
    ) t)

lemma ab_pow_x (t : ℤ) : (a * b) * x ^ t = x ^ (-t) * (a * b) := by
  simpa [zpow_neg] using
    (conj_push (c := a * b) (g := x) (-1) (by
      rw [MulAut.conj_apply]
      have hx : a * x⁻¹ = x⁻¹ * a := by simpa using a_pow_x (-1)
      calc
        (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
        _ = a * (x⁻¹ * b * b⁻¹) * a⁻¹ := by rw [b_mul_x]
        _ = a * x⁻¹ * a⁻¹ := by group
        _ = x⁻¹ * a * a⁻¹ := by rw [hx]
        _ = x⁻¹ := by group
    ) t)

lemma ab_pow_y (t : ℤ) : (a * b) * y ^ t = y ^ (-t) * (a * b) := by
  simpa [zpow_neg] using
    (conj_push (c := a * b) (g := y) (-1) (by
      rw [MulAut.conj_apply]
      have hy : b * y = y * b := by simpa using (b_pow_y 1)
      calc
        (a * b) * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
        _ = a * (y * b * b⁻¹) * a⁻¹ := by rw [hy]
        _ = a * y * a⁻¹ := by group
        _ = y⁻¹ := by
          rw [a_mul_y]
          group
    ) t)

lemma ab_pow_z (t : ℤ) : (a * b) * z ^ t = z ^ t * (a * b) := by
  have h : (a * b) * z = z * (a * b) := by
    rw [z_eq_ab2, pow_two]
    group
  exact (Commute.zpow_right (show Commute (a * b) z from h) t).eq

-- ============================================================
-- The quotient group Q = (Z/2)^2, the section sigma, action and cocycle
-- ============================================================

/-- The Klein four quotient group. -/
abbrev Q := ZMod 2 × ZMod 2

/-- The identity element of Q. -/
def q0 : Q := (0, 0)

/-- The class of a. -/
def qA : Q := (1, 0)

/-- The class of b. -/
def qB : Q := (0, 1)

/-- The class of ab. -/
def qAB : Q := (1, 1)

/-- Section sigma: a set-theoretic section Q -> P. -/
def sig (q : Q) : P :=
  if q = qA then a else if q = qB then b else if q = qAB then a * b else 1

lemma sig_qA : sig qA = a := by simp [sig, qA, qB, qAB]
lemma sig_qB : sig qB = b := by simp [sig, qA, qB, qAB]
lemma sig_qAB : sig qAB = a * b := by simp [sig, qA, qB, qAB]
lemma sig_q0 : sig q0 = 1 := by simp [sig, qA, qB, qAB, q0]

/-- The action of Q on the exponents (conjugation action). -/
def act (q : Q) (m : E) : E :=
  if q.1 = 1 then (if q.2 = 1 then (-m.1, -m.2.1, m.2.2) else (m.1, -m.2.1, -m.2.2))
  else (if q.2 = 1 then (-m.1, m.2.1, -m.2.2) else m)

/-- The cocycle f (values in exponent triples). -/
def f (q q' : Q) : E :=
  if q = qA then (if q' = qA then (1, 0, 0) else if q' = qAB then (1, 0, 0) else (0, 0, 0))
  else if q = qB then
    (if q' = qA then (-1, 1, -1) else if q' = qB then (0, 1, 0)
      else if q' = qAB then (-1, 0, -1) else (0, 0, 0))
  else if q = qAB then
    (if q' = qA then (0, -1, 1) else if q' = qB then (0, -1, 0)
      else if q' = qAB then (0, 0, 1) else (0, 0, 0))
  else (0, 0, 0)

/-- Every element of Q is one of the four classes. -/
lemma Q_cases (q : Q) : q = q0 ∨ q = qA ∨ q = qB ∨ q = qAB := by
  rcases q with ⟨u, v⟩
  fin_cases u <;> fin_cases v <;> decide

lemma act_qA (m : E) : act qA m = (m.1, -m.2.1, -m.2.2) := by
  rcases m with ⟨i, j, k⟩
  simp [act, qA]
lemma act_qB (m : E) : act qB m = (-m.1, m.2.1, -m.2.2) := by
  rcases m with ⟨i, j, k⟩
  simp [act, qB]
lemma act_qAB (m : E) : act qAB m = (-m.1, -m.2.1, m.2.2) := by
  rcases m with ⟨i, j, k⟩
  simp [act, qAB]
lemma act_q0 (m : E) : act q0 m = m := by
  rcases m with ⟨i, j, k⟩
  simp [act, q0]

/-- The action is linear in the exponent. -/
lemma act_add (q : Q) (m n : E) : act q (m + n) = act q m + act q n := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  <;> rcases m with ⟨i,j,k⟩ <;> rcases n with ⟨i',j',k'⟩
  <;> ext <;> simp [act, q0, qA, qB, qAB] <;> ring

/-- The action is an involution. -/
lemma act_act (q : Q) (m : E) : act q (act q m) = m := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  <;> rcases m with ⟨i,j,k⟩
  <;> ext <;> simp [act, q0, qA, qB, qAB]

/-- The action of q then q' equals action of q+q'. -/
lemma act_add_q (q q' : Q) (m : E) : act q (act q' m) = act (q + q') m := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  <;> rcases (Q_cases q') with rfl | rfl | rfl | rfl
  <;> rcases m with ⟨i,j,k⟩
  <;> ext <;> simp [act, q0, qA, qB, qAB]

lemma w_push_a (m : E) : a * w m = w (act qA m) * a := by
  rcases m with ⟨i, j, k⟩
  simp [w, act, qA]
  calc
    a * (x ^ i * y ^ j * z ^ k) = (a * x ^ i) * y ^ j * z ^ k := by group
    _ = (x ^ i * a) * y ^ j * z ^ k := by rw [a_pow_x i]
    _ = x ^ i * (a * y ^ j) * z ^ k := by group
    _ = x ^ i * (y ^ (-j) * a) * z ^ k := by rw [a_pow_y j]
    _ = x ^ i * y ^ (-j) * (a * z ^ k) := by group
    _ = x ^ i * y ^ (-j) * (z ^ (-k) * a) := by rw [a_pow_z k]
    _ = x ^ i * (y ^ j)⁻¹ * (z ^ k)⁻¹ * a := by
      rw [zpow_neg]
      group

-- pushes for b and ab
lemma w_push_b (m : E) : b * w m = w (act qB m) * b := by
  rcases m with ⟨i, j, k⟩
  simp [w, act, qB]
  calc
    b * (x ^ i * y ^ j * z ^ k) = (b * x ^ i) * y ^ j * z ^ k := by group
    _ = (x ^ (-i) * b) * y ^ j * z ^ k := by rw [b_pow_x i]
    _ = x ^ (-i) * (b * y ^ j) * z ^ k := by group
    _ = x ^ (-i) * (y ^ j * b) * z ^ k := by rw [b_pow_y j]
    _ = x ^ (-i) * y ^ j * (b * z ^ k) := by group
    _ = x ^ (-i) * y ^ j * (z ^ (-k) * b) := by rw [b_pow_z k]
    _ = (x ^ i)⁻¹ * y ^ j * (z ^ k)⁻¹ * b := by
      rw [zpow_neg]
      group

lemma w_push_ab (m : E) : (a * b) * w m = w (act qAB m) * (a * b) := by
  rcases m with ⟨i, j, k⟩
  simp [w, act, qAB]
  calc
    (a * b) * (x ^ i * y ^ j * z ^ k) = ((a * b) * x ^ i) * y ^ j * z ^ k := by group
    _ = (x ^ (-i) * (a * b)) * y ^ j * z ^ k := by rw [ab_pow_x i]
    _ = x ^ (-i) * ((a * b) * y ^ j) * z ^ k := by group
    _ = x ^ (-i) * (y ^ (-j) * (a * b)) * z ^ k := by rw [ab_pow_y j]
    _ = x ^ (-i) * y ^ (-j) * ((a * b) * z ^ k) := by group
    _ = x ^ (-i) * y ^ (-j) * (z ^ k * (a * b)) := by rw [ab_pow_z k]
    _ = (x ^ i)⁻¹ * (y ^ j)⁻¹ * z ^ k * (a * b) := by
      rw [zpow_neg]
      group

lemma sig_push (q : Q) (m : E) : sig q * w m = w (act q m) * sig q := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  · rw [sig_q0, act_q0]
    simp
  · rw [sig_qA, act_qA]
    exact w_push_a m
  · rw [sig_qB, act_qB]
    exact w_push_b m
  · rw [sig_qAB, act_qAB]
    exact w_push_ab m

lemma commute_inv_left {a b : P} (h : a * b = b * a) : a⁻¹ * b = b * a⁻¹ := by
  simpa using (Commute.zpow_left (show Commute a b from h) (-1)).eq
lemma commute_inv_right {a b : P} (h : a * b = b * a) : a * b⁻¹ = b⁻¹ * a := by
  simpa using (Commute.zpow_right (show Commute a b from h) (-1)).eq
lemma commute_inv_inv {a b : P} (h : a * b = b * a) : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
  have hc : Commute a b := h
  simpa using (Commute.zpow_zpow hc (-1) (-1)).eq

lemma b_mul_a_aux : b * a = (a ^ 2)⁻¹ * b * a⁻¹ := by
  have h : a ^ 2 * b * a = b * a⁻¹ := by
    calc
      a ^ 2 * b * a = (a ^ 2 * b * a ^ 2) * a⁻¹ := by group
      _ = b * a⁻¹ := by rw [a2_b_a2]
  calc
    b * a = (a ^ 2)⁻¹ * (a ^ 2 * b * a) := by group
    _ = (a ^ 2)⁻¹ * (b * a⁻¹) := by rw [h]
    _ = (a ^ 2)⁻¹ * b * a⁻¹ := by group

lemma y_mul_b_inv : y * b⁻¹ = b := by
  rw [y_eq_b2, pow_two]
  group

lemma hz_ab : z⁻¹ * (a * b) = b⁻¹ * a⁻¹ := by
  rw [z_eq_ab2]
  rw [pow_two]
  group

lemma sp_ba : b * a = x⁻¹ * y * z⁻¹ * (a * b) := by
  rw [b_mul_a_aux]
  calc
    (a ^ 2)⁻¹ * b * a⁻¹ = x⁻¹ * (b * a⁻¹) := by
      rw [x_eq_a2]
      group
    _ = x⁻¹ * (y * b⁻¹ * a⁻¹) := by
      conv_lhs => rw [← y_mul_b_inv]
    _ = x⁻¹ * y * (b⁻¹ * a⁻¹) := by group
    _ = x⁻¹ * y * (z⁻¹ * (a * b)) := by rw [← hz_ab]
    _ = x⁻¹ * y * z⁻¹ * (a * b) := by group

lemma sp_abb : (a * b) * b = y⁻¹ * a := by
  calc
    (a * b) * b = a * (b * b) := by group
    _ = a * y := by rw [← pow_two, ← y_eq_b2]
    _ = y⁻¹ * a := a_mul_y

-- push a past x⁻¹, y, z⁻¹ inside monomials
lemma a_mul_x_inv : a * x⁻¹ = x⁻¹ * a := by
  have h : a * x = x * a := by rw [x_eq_a2]; group
  exact commute_inv_right h
lemma a_mul_y_inv : a * y⁻¹ = y * a := by
  have h : a * y * a⁻¹ = y⁻¹ := by rw [a_mul_y]; group
  calc a * y⁻¹ = (a * y * a⁻¹)⁻¹ * a := by group
    _ = (y⁻¹)⁻¹ * a := by rw [h]
    _ = y * a := by simp
lemma a_mul_z_inv : a * z⁻¹ = z * a := by
  have h : a * z * a⁻¹ = z⁻¹ := by rw [a_mul_z]; group
  calc a * z⁻¹ = (a * z * a⁻¹)⁻¹ * a := by group
    _ = (z⁻¹)⁻¹ * a := by rw [h]
    _ = z * a := by simp

lemma sp_aba : (a * b) * a = y⁻¹ * z * b := by
  calc
    (a * b) * a = a * (b * a) := by group
    _ = a * (x⁻¹ * y * z⁻¹ * (a * b)) := by rw [sp_ba]
    _ = (a * x⁻¹) * y * z⁻¹ * (a * b) := by group
    _ = (x⁻¹ * a) * y * z⁻¹ * (a * b) := by rw [a_mul_x_inv]
    _ = x⁻¹ * (a * y) * z⁻¹ * (a * b) := by group
    _ = x⁻¹ * (y⁻¹ * a) * z⁻¹ * (a * b) := by rw [a_mul_y]
    _ = x⁻¹ * y⁻¹ * (a * z⁻¹) * (a * b) := by group
    _ = x⁻¹ * y⁻¹ * (z * a) * (a * b) := by rw [a_mul_z_inv]
    _ = x⁻¹ * y⁻¹ * z * (a * a) * b := by group
    _ = x⁻¹ * y⁻¹ * z * x * b := by rw [← pow_two, ← x_eq_a2]
    _ = y⁻¹ * z * b := by
      -- x⁻¹ * (y⁻¹ * z) * x = y⁻¹ * z
      have hx : x⁻¹ * (y⁻¹ * z) * x = y⁻¹ * z := by
        calc
          x⁻¹ * (y⁻¹ * z) * x = (x⁻¹ * y⁻¹) * (z * x) := by group
          _ = (y⁻¹ * x⁻¹) * (x * z) := by
            rw [commute_inv_inv xy_comm]
            rw [← xz_comm]
          _ = y⁻¹ * z := by group
      calc
        x⁻¹ * y⁻¹ * z * x * b = (x⁻¹ * (y⁻¹ * z) * x) * b := by group
        _ = (y⁻¹ * z) * b := by rw [hx]


lemma sp_bab : b * (a * b) = x⁻¹ * z⁻¹ * a := by
  calc
    b * (a * b) = (b * a) * b := by group
    _ = (x⁻¹ * y * z⁻¹ * (a * b)) * b := by rw [sp_ba]
    _ = x⁻¹ * y * z⁻¹ * ((a * b) * b) := by group
    _ = x⁻¹ * y * z⁻¹ * (y⁻¹ * a) := by rw [sp_abb]
    _ = x⁻¹ * (y * z⁻¹) * (y⁻¹ * a) := by group
    _ = x⁻¹ * (z⁻¹ * y) * (y⁻¹ * a) := by rw [commute_inv_right yz_comm]
    _ = x⁻¹ * z⁻¹ * a := by group
@[simp] lemma add_q0_q0 : q0 + q0 = q0 := by decide
@[simp] lemma add_q0_qA : q0 + qA = qA := by decide
@[simp] lemma add_q0_qB : q0 + qB = qB := by decide
@[simp] lemma add_q0_qAB : q0 + qAB = qAB := by decide
@[simp] lemma add_qA_q0 : qA + q0 = qA := by decide
@[simp] lemma add_qA_qA : qA + qA = q0 := by decide
@[simp] lemma add_qA_qB : qA + qB = qAB := by decide
@[simp] lemma add_qA_qAB : qA + qAB = qB := by decide
@[simp] lemma add_qB_q0 : qB + q0 = qB := by decide
@[simp] lemma add_qB_qA : qB + qA = qAB := by decide
@[simp] lemma add_qB_qB : qB + qB = q0 := by decide
@[simp] lemma add_qB_qAB : qB + qAB = qA := by decide
@[simp] lemma add_qAB_q0 : qAB + q0 = qAB := by decide
@[simp] lemma add_qAB_qA : qAB + qA = qB := by decide
@[simp] lemma add_qAB_qB : qAB + qB = qA := by decide
@[simp] lemma add_qAB_qAB : qAB + qAB = q0 := by decide

@[simp] lemma f_q0_q0 : f q0 q0 = (0,0,0) := by decide
@[simp] lemma f_q0_qA : f q0 qA = (0,0,0) := by decide
@[simp] lemma f_q0_qB : f q0 qB = (0,0,0) := by decide
@[simp] lemma f_q0_qAB : f q0 qAB = (0,0,0) := by decide
@[simp] lemma f_qA_q0 : f qA q0 = (0,0,0) := by decide
@[simp] lemma f_qA_qA : f qA qA = (1,0,0) := by decide
@[simp] lemma f_qA_qB : f qA qB = (0,0,0) := by decide
@[simp] lemma f_qA_qAB : f qA qAB = (1,0,0) := by decide
@[simp] lemma f_qB_q0 : f qB q0 = (0,0,0) := by decide
@[simp] lemma f_qB_qA : f qB qA = (-1,1,-1) := by decide
@[simp] lemma f_qB_qB : f qB qB = (0,1,0) := by decide
@[simp] lemma f_qB_qAB : f qB qAB = (-1,0,-1) := by decide
@[simp] lemma f_qAB_q0 : f qAB q0 = (0,0,0) := by decide
@[simp] lemma f_qAB_qA : f qAB qA = (0,-1,1) := by decide
@[simp] lemma f_qAB_qB : f qAB qB = (0,-1,0) := by decide
@[simp] lemma f_qAB_qAB : f qAB qAB = (0,0,1) := by decide

lemma aa : a * a = x := by
  exact (pow_two a).symm.trans x_eq_a2.symm
lemma bb : b * b = y := by
  exact (pow_two b).symm.trans y_eq_b2.symm
lemma abab : (a * b) * (a * b) = z := by
  exact (pow_two (a * b)).symm.trans z_eq_ab2.symm

lemma sig_prod_AA : a * a = w (f qA qA) * sig (qA + qA) := by
  simp [w, aa, sig_q0]
lemma sig_prod_AB : a * b = w (f qA qB) * sig (qA + qB) := by
  simp [w, sig_qAB]
lemma sig_prod_AAB : a * (a * b) = w (f qA qAB) * sig (qA + qAB) := by
  rw [← mul_assoc, aa]
  simp [w, sig_qB]
lemma sig_prod_BB : b * b = w (f qB qB) * sig (qB + qB) := by
  simp [w, bb, sig_q0]
lemma sig_prod_BA : b * a = w (f qB qA) * sig (qB + qA) := by
  rw [sp_ba]
  simp [w, sig_qAB]
lemma sig_prod_BAB : b * (a * b) = w (f qB qAB) * sig (qB + qAB) := by
  rw [sp_bab]
  simp [w, sig_qA]
lemma sig_prod_ABA : (a * b) * a = w (f qAB qA) * sig (qAB + qA) := by
  rw [sp_aba]
  simp [w, sig_qB]
lemma sig_prod_ABB : (a * b) * b = w (f qAB qB) * sig (qAB + qB) := by
  rw [sp_abb]
  simp [w, sig_qA]
lemma sig_prod_ABAB : (a * b) * (a * b) = w (f qAB qAB) * sig (qAB + qAB) := by
  simp [w, abab, sig_q0]

lemma sig_mul (q q' : Q) : sig q * sig q' = w (f q q') * sig (q + q') := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  · rcases (Q_cases q') with rfl | rfl | rfl | rfl <;> simp [w, sig_q0]
  · rcases (Q_cases q') with rfl | rfl | rfl | rfl
    · simp [w, sig_q0]
    · rw [sig_qA]; exact sig_prod_AA
    · rw [sig_qA, sig_qB]; exact sig_prod_AB
    · rw [sig_qA]; exact sig_prod_AAB
  · rcases (Q_cases q') with rfl | rfl | rfl | rfl
    · simp [w, sig_q0]
    · rw [sig_qB]; exact sig_prod_BA
    · rw [sig_qB]; exact sig_prod_BB
    · rw [sig_qB]; exact sig_prod_BAB
  · rcases (Q_cases q') with rfl | rfl | rfl | rfl
    · simp [w, sig_q0]
    · rw [sig_qAB]; exact sig_prod_ABA
    · rw [sig_qAB]; exact sig_prod_ABB
    · rw [sig_qAB]; exact sig_prod_ABAB


lemma prod_formula (m : E) (q : Q) (m' : E) (q' : Q) :
    (w m * sig q) * (w m' * sig q') = w (m + act q m' + f q q') * sig (q + q') := by
  calc
    (w m * sig q) * (w m' * sig q') = w m * (sig q * w m') * sig q' := by group
    _ = w m * (w (act q m') * sig q) * sig q' := by rw [sig_push q m']
    _ = (w m * w (act q m')) * (sig q * sig q') := by group
    _ = w (m + act q m') * (sig q * sig q') := by rw [← w_hom]
    _ = w (m + act q m') * (w (f q q') * sig (q + q')) := by rw [sig_mul]
    _ = (w (m + act q m') * w (f q q')) * sig (q + q') := by group
    _ = w (m + act q m' + f q q') * sig (q + q') := by rw [← w_hom]

end Submission
