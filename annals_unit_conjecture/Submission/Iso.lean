import Submission.Model

open UnitConjecture

set_option autoImplicit false

noncomputable section

namespace Submission

open scoped Classical
open UnitConjecture

-- ============================================================
-- The isomorphism P ≃ HW
-- ============================================================

/-- generator map into HW -/
def phi_fun : generators → HW
  | generators.a => HW.A
  | generators.b => HW.B

lemma rel1_lift : FreeGroup.lift phi_fun (UnitConjecture.b⁻¹ * UnitConjecture.a ^ 2 *
    UnitConjecture.b * UnitConjecture.a ^ 2) = 1 := by
  simp [UnitConjecture.a, UnitConjecture.b, phi_fun, FreeGroup.lift_apply_of,
    map_mul, map_inv, map_pow]
  decide

lemma rel2_lift : FreeGroup.lift phi_fun (UnitConjecture.a⁻¹ * UnitConjecture.b ^ 2 *
    UnitConjecture.a * UnitConjecture.b ^ 2) = 1 := by
  simp [UnitConjecture.a, UnitConjecture.b, phi_fun, FreeGroup.lift_apply_of,
    map_mul, map_inv, map_pow]
  decide

lemma rels_in_ker : ∀ r ∈ relations, FreeGroup.lift phi_fun r = 1 := by
  intro r hr
  simp [relations] at hr
  rcases hr with rfl | rfl
  · simpa using rel1_lift
  · simpa using rel2_lift

/-- canonical hom P -> HW -/
def phi : P →* HW := PresentedGroup.toGroup rels_in_ker

lemma phi_a : phi (UnitConjecture.a : P) = HW.A := by
  change (PresentedGroup.toGroup rels_in_ker) (PresentedGroup.of generators.a) = HW.A
  rw [PresentedGroup.toGroup.of]
  rfl

lemma phi_b : phi (UnitConjecture.b : P) = HW.B := by
  change (PresentedGroup.toGroup rels_in_ker) (PresentedGroup.of generators.b) = HW.B
  rw [PresentedGroup.toGroup.of]
  rfl

/-- inverse of a translation element -/
lemma inv_trans (e : E) : ({e := e, q := q0} : HW)⁻¹ = {e := -e, q := q0} := by
  rw [HW.inv_def]
  change ({ e := act q0 (-(e + f q0 q0)), q := q0 } : HW) = { e := -e, q := q0 }
  have hf : f q0 q0 = (0, 0, 0) := by decide
  rw [hf]
  rw [act_q0]
  ext <;> simp

/-- translation powers in HW -/
lemma Tx_zpow (n : ℤ) : HW.Tx ^ n = { e := (n, 0, 0), q := q0 } := by
  by_cases hn : 0 ≤ n
  · rcases (Int.eq_ofNat_of_zero_le hn) with ⟨m, rfl⟩
    rw [zpow_natCast]
    simp [HW.Tx, HW.pow_q0]
  · have hn' : n < 0 := Int.lt_of_not_ge hn
    rcases (Int.eq_negSucc_of_lt_zero hn') with ⟨m, rfl⟩
    rw [zpow_negSucc]
    rw [show HW.Tx ^ (m + 1) = ({e := ((m : ℤ) + 1, 0, 0), q := q0} : HW) by
      simp [HW.Tx, HW.pow_q0]]
    rw [inv_trans]
    ext <;> simp <;> omega

lemma Ty_zpow (n : ℤ) : HW.Ty ^ n = { e := (0, n, 0), q := q0 } := by
  by_cases hn : 0 ≤ n
  · rcases (Int.eq_ofNat_of_zero_le hn) with ⟨m, rfl⟩
    rw [zpow_natCast]
    simp [HW.Ty, HW.pow_q0]
  · have hn' : n < 0 := Int.lt_of_not_ge hn
    rcases (Int.eq_negSucc_of_lt_zero hn') with ⟨m, rfl⟩
    rw [zpow_negSucc]
    rw [show HW.Ty ^ (m + 1) = ({e := (0, (m : ℤ) + 1, 0), q := q0} : HW) by
      simp [HW.Ty, HW.pow_q0]]
    rw [inv_trans]
    ext <;> simp <;> omega

lemma Tz_zpow (n : ℤ) : HW.Tz ^ n = { e := (0, 0, n), q := q0 } := by
  by_cases hn : 0 ≤ n
  · rcases (Int.eq_ofNat_of_zero_le hn) with ⟨m, rfl⟩
    rw [zpow_natCast]
    simp [HW.Tz, HW.pow_q0]
  · have hn' : n < 0 := Int.lt_of_not_ge hn
    rcases (Int.eq_negSucc_of_lt_zero hn') with ⟨m, rfl⟩
    rw [zpow_negSucc]
    rw [show HW.Tz ^ (m + 1) = ({e := (0, 0, (m : ℤ) + 1), q := q0} : HW) by
      simp [HW.Tz, HW.pow_q0]]
    rw [inv_trans]
    ext <;> simp <;> omega

/-- phi applied to x, y, z -/
lemma phi_x : phi x = HW.Tx := by
  rw [x_eq_a2]
  rw [map_pow]
  rw [phi_a]
  exact HW.A_sq

lemma phi_y : phi y = HW.Ty := by
  rw [y_eq_b2]
  rw [map_pow]
  rw [phi_b]
  exact HW.B_sq

lemma phi_z : phi z = HW.Tz := by
  rw [z_eq_ab2]
  rw [map_pow]
  rw [map_mul]
  rw [phi_a, phi_b]
  exact HW.AB_sq

/-- phi maps monomials to translations -/
lemma phi_w (e : E) : phi (w e) = { e := e, q := q0 } := by
  rcases e with ⟨i, j, k⟩
  change phi (x ^ i * y ^ j * z ^ k) = { e := (i, j, k), q := q0 }
  calc
    phi (x ^ i * y ^ j * z ^ k) = phi (x ^ i * y ^ j) * phi (z ^ k) := by
      rw [map_mul]
    _ = (phi (x ^ i) * phi (y ^ j)) * phi (z ^ k) := by
      rw [map_mul]
    _ = (HW.Tx ^ i * HW.Ty ^ j) * HW.Tz ^ k := by
      rw [map_zpow, map_zpow, map_zpow]
      rw [phi_x, phi_y, phi_z]
    _ = { e := (i, j, k), q := q0 } := by
      rw [Tx_zpow, Ty_zpow, Tz_zpow]
      rw [HW.mul_q0, HW.mul_q0]
      congr 1
      ext <;> simp

/-- products of translations -/
lemma q0_mul_q (e : E) (q : Q) :
    ({e := e, q := q0} : HW) * ({e := (0, 0, 0), q := q} : HW) = ({e := e, q := q} : HW) := by
  rw [HW.mul_def]
  change ({ e := e + act q0 (0,0,0) + f q0 q, q := q0 + q } : HW) = ({ e := e, q := q } : HW)
  rw [HW.act_zero, HW.f_zero_left q, HW.q_add_zero]
  rcases e with ⟨i, j, k⟩
  ext <;> simp

/-- phi maps the section elements -/
lemma phi_sig (q : Q) : phi (sig q) = { e := (0, 0, 0), q := q } := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  · rw [sig_q0]
    change (PresentedGroup.toGroup rels_in_ker) 1 = (1 : HW)
    simp
  · rw [sig_qA]
    change (PresentedGroup.toGroup rels_in_ker) (PresentedGroup.of generators.a) = { e := (0, 0, 0), q := qA }
    rw [PresentedGroup.toGroup.of]
    rfl
  · rw [sig_qB]
    change (PresentedGroup.toGroup rels_in_ker) (PresentedGroup.of generators.b) = { e := (0, 0, 0), q := qB }
    rw [PresentedGroup.toGroup.of]
    rfl
  · rw [sig_qAB]
    rw [map_mul]
    rw [phi_a, phi_b]
    decide

/-- candidate inverse map HW -> P -/
def psi_fun (g : HW) : P := w g.e * sig g.q

lemma psi_mul (g h : HW) : psi_fun (g * h) = psi_fun g * psi_fun h := by
  rw [HW.mul_def]
  change w (g.e + act g.q h.e + f g.q h.q) * sig (g.q + h.q)
      = (w g.e * sig g.q) * (w h.e * sig h.q)
  exact (prod_formula g.e g.q h.e h.q).symm

/-- psi is a monoid hom -/
def psi : HW →* P where
  toFun := psi_fun
  map_one' := by
    change w (0 : E) * sig q0 = 1
    rw [w_zero, sig_q0]
    simp
  map_mul' := psi_mul

lemma psi_A : psi HW.A = a := by
  change w (0 : E) * sig qA = (a : P)
  rw [w_zero, sig_qA]
  simp

lemma psi_B : psi HW.B = b := by
  change w (0 : E) * sig qB = (b : P)
  rw [w_zero, sig_qB]
  simp

/-- psi after phi is the identity on P -/
lemma psi_phi_id : psi.comp phi = MonoidHom.id P := by
  apply PresentedGroup.ext
  intro g
  cases g with
  | a =>
      change psi (phi (UnitConjecture.a : P)) = (UnitConjecture.a : P)
      rw [phi_a]
      simp [psi_A]
  | b =>
      change psi (phi (UnitConjecture.b : P)) = (UnitConjecture.b : P)
      rw [phi_b]
      simp [psi_B]

/-- phi after psi is the identity on HW -/
lemma phi_psi_id : phi.comp psi = MonoidHom.id HW := by
  apply MonoidHom.ext
  intro g
  rcases g with ⟨e, q⟩
  change phi (psi { e := e, q := q }) = { e := e, q := q }
  change phi (w e * sig q) = { e := e, q := q }
  rw [map_mul]
  rw [phi_w]
  rw [phi_sig]
  exact q0_mul_q e q

def iso : P ≃* HW :=
  MonoidHom.toMulEquiv phi psi psi_phi_id phi_psi_id

end Submission
