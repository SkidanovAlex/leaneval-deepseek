import Submission.Components
import Submission.RingProd
import Submission.Computation

open UnitConjecture

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

namespace Submission

open scoped Classical
open MonoidAlgebra
open Finset

/-- The transported element u equals the 21 monomial sum. -/
lemma Phi_u_eq_U0 : Phi (u : RR) = U0 := by
  rw [u]
  simp only [map_add]
  rw [map_mul, map_mul, map_mul]
  rw [map_mul]
  simp [Phi_single_coe, iso_a_m, iso_b_m]
  rw [Phi_p_eq, Phi_q_eq, Phi_r_eq, Phi_s_eq]
  rw [show HW.mul (m 0 0 0 qA) (m 0 0 0 qB) = m 0 0 0 qAB by decide]
  rw [qA_prod, rB_prod, sAB_prod]
  rfl


/-- u is a unit in the group ring -/
lemma u_unit : IsUnit (u : RR) := by
  let w : RR := Phi.symm V0
  have hPhiw : Phi w = V0 := by
    exact AlgEquiv.apply_symm_apply Phi V0
  have h1 : (u : RR) * w = 1 := by
    apply (Phi).injective
    rw [map_mul, hPhiw]
    rw [Phi_u_eq_U0]
    rw [U0_mul_V0]
    rw [map_one]
    rw [MonoidAlgebra.one_def]
    rw [show m 0 0 0 q0 = (1 : HW) by decide]
  have h2 : w * (u : RR) = 1 := by
    apply (Phi).injective
    rw [map_mul, hPhiw]
    rw [Phi_u_eq_U0]
    rw [V0_mul_U0]
    rw [map_one]
    rw [MonoidAlgebra.one_def]
    rw [show m 0 0 0 q0 = (1 : HW) by decide]
  let un : (RR)ˣ := { val := (u : RR), inv := w, val_inv := h1, inv_val := h2 }
  exact ⟨un, rfl⟩

/-- u is not a group element -/
lemma u_not_group : ¬ ∃ g : P, u = (g : RR) := by
  intro ⟨g, hg⟩
  have hc := congrArg Phi hg
  rw [Phi_u_eq_U0] at hc
  rw [show Phi ((g : RR)) = single (iso g) (1 : ZMod 2) by
    change Phi (single g (1 : ZMod 2)) = single (iso g) (1 : ZMod 2)
    exact Phi_single_coe g] at hc
  exact U0_not_single ⟨iso g, hc⟩

/-- P is torsion-free -/
lemma P_torsion_free : ∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1 := by
  intro g n hn hgn
  apply iso.injective
  by_contra hg1
  have hpow : (iso g) ^ n ≠ 1 := HW.torsion_free (iso g) hg1 n hn
  have h1 : iso g ^ n = 1 := by
    rw [← map_pow]
    rw [hgn]
    simp
  exact hpow h1

/-- the combined statement -/
theorem theorem_A_combined :
    (∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1) ∧ IsUnit u ∧ ¬ ∃ g : P, u = g := by
  constructor
  · intro g n hn hgn
    exact P_torsion_free g n hn hgn
  constructor
  · exact u_unit
  · exact u_not_group

end Submission
