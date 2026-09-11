import Submission.RingMain

open UnitConjecture

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

namespace Submission

open scoped Classical
open MonoidAlgebra
open Finset

/-!
# Component expansions of the transported element

Fill in the proofs below.  All definitions (Phi, m, Qp, Qq, Qr, Qs) are in
`Submission.Ring` / `Submission.RingMain`.  Reference facts available there:
- `Phi_coe_x : Phi ((x : P) : RR) = single (m 1 0 0 q0) 1`
- `Phi_coe_y`, `Phi_coe_z_inv`, `Phi_coe_a`, `Phi_coe_b` (analogous)
- `iso_x`, `iso_y`, `iso_z_inv`, `iso_a`, `iso_b`
- `Phi_mono (e : E) (q : Q) : Phi (single (w e * sig q) 1) = single {e := e, q := q} 1`
- `q0_mul_q`, and ring machinery `prod_sum_single`, `sum_single_map_eq_sum_single`,
  `sum_mul_single_right`, `sum_sum_union`, `coeff_sum_single`, ...
- `x_eq_a2 : x = a ^ 2`, `y_eq_b2`, `z_eq_ab2` (in Prelude/GroupIdentities)

`simp`, `rw [map_add, map_mul]` on the ring hom `Phi` (it is an `AlgEquiv`);
`simp` with the `Phi_coe_*` lemmas; the coefficient-level tools let you verify
equalities of sums of `single`s with `native_decide`.

You may add helper lemmas freely but do not change the statements.
-/

-- ============================================================
-- helper machinery for the transport lemmas
-- ============================================================

/-- Phi on a monomial (coefficient 1). -/
private lemma comp_Phi_single (g : P) :
    Phi (single g (1 : ZMod 2)) = single (iso g) (1 : ZMod 2) := by
  rw [Phi, MonoidAlgebra.domCongr_single]

/-- iso z = m 0 0 1 q0 -/
private lemma comp_iso_z_pos : iso (z : P) = m 0 0 1 q0 := by
  calc
    iso (z : P) = iso ((z⁻¹ : P)⁻¹) := by rw [inv_inv]
    _ = (iso (z⁻¹ : P))⁻¹ := by rw [map_inv]
    _ = m 0 0 1 q0 := by
      rw [iso_z_inv]
      decide

/-- iso of the monomials appearing in q, r, s -/
private lemma comp_iso_x_inv_y_inv : iso (x⁻¹ * y⁻¹) = m (-1) (-1) 0 q0 := by
  rw [map_mul, map_inv, iso_x, map_inv, iso_y]
  decide

private lemma comp_iso_y_inv_z : iso (y⁻¹ * z) = m 0 (-1) 1 q0 := by
  rw [map_mul, map_inv, iso_y, comp_iso_z_pos]
  decide

private lemma comp_iso_x_mul_y_mul_z : iso (x * y * z) = m 1 1 1 q0 := by
  rw [map_mul, map_mul, iso_x, iso_y, comp_iso_z_pos]
  decide

private lemma comp_iso_x_z_inv : iso (x * z⁻¹) = m 1 0 (-1) q0 := by
  rw [map_mul, iso_x, iso_z_inv]
  decide

private lemma comp_iso_x_inv_z_inv : iso (x⁻¹ * z⁻¹) = m (-1) 0 (-1) q0 := by
  rw [map_mul, map_inv, iso_x, iso_z_inv]
  decide

private lemma comp_iso_y_z_inv : iso (y * z⁻¹) = m 0 1 (-1) q0 := by
  rw [map_mul, iso_y, iso_z_inv]
  decide

private lemma comp_iso_y_inv_z_inv : iso (y⁻¹ * z⁻¹) = m 0 (-1) (-1) q0 := by
  rw [map_mul, map_inv, iso_y, iso_z_inv]
  decide

/-- q expanded as four monomials -/
private lemma comp_q_chain : (q : RR)
    = single (x⁻¹ * y⁻¹) (1 : ZMod 2) + single (x : P) (1 : ZMod 2)
      + single (y⁻¹ * z) (1 : ZMod 2) + single (z : P) (1 : ZMod 2) := by
  rw [q]
  rw [show ((x⁻¹ : P) : RR) = single (x⁻¹ : P) (1 : ZMod 2) by rfl]
  rw [show ((y⁻¹ : P) : RR) = single (y⁻¹ : P) (1 : ZMod 2) by rfl]
  rw [show ((x : P) : RR) = single (x : P) (1 : ZMod 2) by rfl]
  rw [show ((z : P) : RR) = single (z : P) (1 : ZMod 2) by rfl]
  simp only [single_mul_single]
  simp only [one_mul]

/-- r expanded as four monomials -/
private lemma comp_r_chain : (r : RR)
    = (1 : RR) + single (x : P) (1 : ZMod 2)
      + single (y⁻¹ * z) (1 : ZMod 2) + single (x * y * z) (1 : ZMod 2) := by
  rw [r]
  rw [show (1 : RR) = single (1 : P) (1 : ZMod 2) by rw [MonoidAlgebra.one_def]]
  rw [show ((x : P) : RR) = single (x : P) (1 : ZMod 2) by rfl]
  rw [show ((y⁻¹ : P) : RR) = single (y⁻¹ : P) (1 : ZMod 2) by rfl]
  rw [show ((z : P) : RR) = single (z : P) (1 : ZMod 2) by rfl]
  rw [show ((y : P) : RR) = single (y : P) (1 : ZMod 2) by rfl]
  simp only [single_mul_single]
  simp only [one_mul]

/-- s expanded as five monomials -/
private lemma comp_s_chain : (s : RR)
    = (1 : RR)
      + (single (x * z⁻¹) (1 : ZMod 2))
      + (single (x⁻¹ * z⁻¹) (1 : ZMod 2))
      + (single (y * z⁻¹) (1 : ZMod 2))
      + (single (y⁻¹ * z⁻¹) (1 : ZMod 2)) := by
  rw [s]
  rw [show (1 : RR) = single (1 : P) (1 : ZMod 2) by rw [MonoidAlgebra.one_def]]
  rw [show ((x : P) : RR) = single (x : P) (1 : ZMod 2) by rfl]
  rw [show ((x⁻¹ : P) : RR) = single (x⁻¹ : P) (1 : ZMod 2) by rfl]
  rw [show ((y : P) : RR) = single (y : P) (1 : ZMod 2) by rfl]
  rw [show ((y⁻¹ : P) : RR) = single (y⁻¹ : P) (1 : ZMod 2) by rfl]
  rw [show ((z⁻¹ : P) : RR) = single (z⁻¹ : P) (1 : ZMod 2) by rfl]
  rw [add_mul, add_mul, add_mul]
  simp only [single_mul_single]
  simp only [one_mul]
  simp only [add_assoc]

/-- the monomial factors of the transported product -/
private abbrev comp_MA : Finset HW := ({m 0 0 0 q0, m 1 0 0 q0})
private abbrev comp_MB : Finset HW := ({m 0 0 0 q0, m 0 1 0 q0})
private abbrev comp_MC : Finset HW := ({m 0 0 0 q0, m 0 0 (-1) q0})

private lemma comp_binom_A : (1 : MonoidAlgebra (ZMod 2) HW) + single (m 1 0 0 q0) (1 : ZMod 2)
    = ∑ q ∈ comp_MA, single q (1 : ZMod 2) := by
  rw [MonoidAlgebra.one_def]
  rw [show (1 : HW) = m 0 0 0 q0 by decide]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
  · decide

private lemma comp_binom_B : (1 : MonoidAlgebra (ZMod 2) HW) + single (m 0 1 0 q0) (1 : ZMod 2)
    = ∑ q ∈ comp_MB, single q (1 : ZMod 2) := by
  rw [MonoidAlgebra.one_def]
  rw [show (1 : HW) = m 0 0 0 q0 by decide]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
  · decide

private lemma comp_binom_C : (1 : MonoidAlgebra (ZMod 2) HW) + single (m 0 0 (-1) q0) (1 : ZMod 2)
    = ∑ q ∈ comp_MC, single q (1 : ZMod 2) := by
  rw [MonoidAlgebra.one_def]
  rw [show (1 : HW) = m 0 0 0 q0 by decide]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
  · decide

/-- each triple product of the factors lands in Qp -/
private lemma comp_pprod_cover :
    ∀ p ∈ (comp_MA.product comp_MB).product comp_MC, (p.1.1 * p.1.2) * p.2 ∈ Qp := by
  intro p hp
  rcases p with ⟨⟨a, b⟩, c⟩
  simp at hp
  rcases hp with ⟨⟨ha, hb⟩, hc⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> decide

/-- each element of Qp has a unique preimage among the triples -/
private lemma comp_pprod_uniq :
    ∀ q ∈ Qp, (∑ p ∈ (comp_MA.product comp_MB).product comp_MC,
      if (p.1.1 * p.1.2) * p.2 = q then (1 : ZMod 2) else 0) = 1 := by
  intro q hq
  simp [Qp] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

-- ============================================================
-- the component expansions
-- ============================================================

/-- transport of q -/
lemma Phi_q_eq : Phi (q : RR) = ∑ q0e ∈ Qq, single q0e (1 : ZMod 2) := by
  rw [comp_q_chain]
  rw [map_add, map_add, map_add]
  rw [comp_Phi_single, comp_Phi_single, comp_Phi_single, comp_Phi_single]
  rw [comp_iso_x_inv_y_inv, iso_x, comp_iso_y_inv_z, comp_iso_z_pos]
  rw [Qq]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        ac_rfl
      · decide
    · decide
  · decide

/-- transport of r -/
lemma Phi_r_eq : Phi (r : RR) = ∑ q0e ∈ Qr, single q0e (1 : ZMod 2) := by
  rw [comp_r_chain]
  rw [map_add, map_add, map_add]
  rw [map_one]
  rw [MonoidAlgebra.one_def]
  rw [comp_Phi_single, comp_Phi_single, comp_Phi_single]
  rw [show (1 : HW) = m 0 0 0 q0 by decide]
  rw [iso_x, comp_iso_y_inv_z, comp_iso_x_mul_y_mul_z]
  rw [Qr]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        ac_rfl
      · decide
    · decide
  · decide

/-- transport of s -/
lemma Phi_s_eq : Phi (s : RR) = ∑ q0e ∈ Qs, single q0e (1 : ZMod 2) := by
  rw [comp_s_chain]
  rw [map_add, map_add, map_add, map_add]
  rw [map_one]
  rw [MonoidAlgebra.one_def]
  rw [comp_Phi_single, comp_Phi_single, comp_Phi_single, comp_Phi_single]
  rw [show (1 : HW) = m 0 0 0 q0 by decide]
  rw [comp_iso_x_z_inv, comp_iso_x_inv_z_inv, comp_iso_y_z_inv, comp_iso_y_inv_z_inv]
  rw [Qs]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_singleton]
          ac_rfl
        · decide
      · decide
    · decide
  · decide

/-- product of the three translated factors (1+X)(1+Y)(1+Z⁻¹) expands to Qp -/
lemma pprod_RG :
    ((1 : MonoidAlgebra (ZMod 2) HW) + single (m 1 0 0 q0) (1 : ZMod 2))
      * ((1 : MonoidAlgebra (ZMod 2) HW) + single (m 0 1 0 q0) (1 : ZMod 2))
      * ((1 : MonoidAlgebra (ZMod 2) HW) + single (m 0 0 (-1) q0) (1 : ZMod 2))
    = ∑ q ∈ Qp, single q (1 : ZMod 2) := by
  rw [comp_binom_A, comp_binom_B, comp_binom_C]
  rw [prod_sum_single]
  rw [prod_sum_map_single]
  exact sum_single_map_eq_sum_single ((comp_MA.product comp_MB).product comp_MC)
    (fun q : (HW × HW) × HW => (q.1.1 * q.1.2) * q.2) Qp comp_pprod_cover comp_pprod_uniq

/-- transport of p -/
lemma Phi_p_eq : Phi (p : RR) = ∑ q ∈ Qp, single q (1 : ZMod 2) := by
  rw [p]
  rw [map_mul, map_mul]
  rw [map_add, map_add, map_add]
  rw [map_one]
  rw [Phi_coe_x, Phi_coe_y, Phi_coe_z_inv]
  exact pprod_RG

end Submission
