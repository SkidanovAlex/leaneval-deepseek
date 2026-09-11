import Submission.RingCombine
import Submission.RingBlocksV
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.NoncommRing

open UnitConjecture

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Submission

open scoped Classical
open MonoidAlgebra
open Finset

lemma char2_add_self (x : RG) : x + x = 0 := by
  rw [MonoidAlgebra.ext_iff]
  apply Finsupp.ext
  intro m
  have hc : (x.coeff m) + (x.coeff m) = 0 := CharTwo.add_self_eq_zero (x.coeff m)
  simpa [Finsupp.add_apply] using hc

lemma indicator_sd (R S : Finset HW) (m : HW) :
    (if m ∈ R then (1 : ZMod 2) else 0) + (if m ∈ S then (1 : ZMod 2) else 0)
      = (if m ∈ (R \ S) ∪ (S \ R) then (1 : ZMod 2) else 0) := by
  by_cases hmR : m ∈ R
  · by_cases hmS : m ∈ S
    · simp [hmR, hmS]; decide
    · simp [hmR, hmS]
  · by_cases hmS : m ∈ S
    · simp [hmR, hmS]
    · simp [hmR, hmS]

lemma pair_sum_sd (R S : Finset HW) :
    (∑ r ∈ R, single r (1 : ZMod 2)) + (∑ s ∈ S, single s (1 : ZMod 2))
      = ∑ m ∈ (R \ S) ∪ (S \ R), single m (1 : ZMod 2) := by
  rw [MonoidAlgebra.ext_iff]
  apply Finsupp.ext
  intro m
  simp [Finsupp.add_apply, Finsupp.single_apply]
  rw [indicator_sd R S m]
  simp [Finset.mem_union, Finset.mem_sdiff]

lemma coeff_sum_singles (R : Finset HW) (m : HW) :
    (∑ r ∈ R, single r (1 : ZMod 2)).coeff m = (if m ∈ R then (1 : ZMod 2) else 0) := by
  rw [coeff_sum_single]
  rw [Finset.sum_ite_eq' (s := R) (a := m) (b := fun _ => (1 : ZMod 2))]

/-- cancellation in the qA coset -/
lemma coset_A : (((∑ r ∈ r_q0_qA, single r (1 : ZMod 2)) + (∑ r ∈ r_qA_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qAB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qB, single r (1 : ZMod 2)) = 0 := by
  have h1 : ((∑ r ∈ r_q0_qA, single r (1 : ZMod 2))) = ((∑ r ∈ r_qA_q0, single r (1 : ZMod 2))) := by
    rw [r_q0_qA, r_qA_q0]
  have h2 : ((∑ r ∈ r_qB_qAB, single r (1 : ZMod 2))) = ((∑ r ∈ r_qAB_qB, single r (1 : ZMod 2))) := by
    rw [r_qB_qAB, r_qAB_qB]
  rw [h1, h2, add_assoc]
  rw [char2_add_self, char2_add_self]
  simp

/-- cancellation in the qB coset -/
lemma coset_B : (((∑ r ∈ r_q0_qB, single r (1 : ZMod 2)) + (∑ r ∈ r_qB_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qA_qAB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qA, single r (1 : ZMod 2)) = 0 := by
  have h1 : ((∑ r ∈ r_q0_qB, single r (1 : ZMod 2))) = ((∑ r ∈ r_qB_q0, single r (1 : ZMod 2))) := by
    rw [r_q0_qB, r_qB_q0]
  have h2 : ((∑ r ∈ r_qA_qAB, single r (1 : ZMod 2))) = ((∑ r ∈ r_qAB_qA, single r (1 : ZMod 2))) := by
    rw [r_qA_qAB, r_qAB_qA]
  rw [h1, h2, add_assoc]
  rw [char2_add_self, char2_add_self]
  simp

/-- cancellation in the qAB coset -/
lemma coset_AB : (((∑ r ∈ r_q0_qAB, single r (1 : ZMod 2)) + (∑ r ∈ r_qAB_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qA_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qA, single r (1 : ZMod 2)) = 0 := by
  have hsd : ((r_q0_qAB \ r_qAB_q0) ∪ (r_qAB_q0 \ r_q0_qAB)) = ((r_qA_qB \ r_qB_qA) ∪ (r_qB_qA \ r_qA_qB)) := by decide
  rw [add_assoc]
  rw [show (∑ r ∈ r_q0_qAB, single r (1 : ZMod 2)) + (∑ r ∈ r_qAB_q0, single r (1 : ZMod 2)) = ∑ m ∈ ((r_q0_qAB \ r_qAB_q0) ∪ (r_qAB_q0 \ r_q0_qAB)), single m (1 : ZMod 2) by
    exact pair_sum_sd r_q0_qAB r_qAB_q0]
  rw [show (∑ r ∈ r_qA_qB, single r (1 : ZMod 2)) + (∑ r ∈ r_qB_qA, single r (1 : ZMod 2)) = ∑ m ∈ ((r_qA_qB \ r_qB_qA) ∪ (r_qB_qA \ r_qA_qB)), single m (1 : ZMod 2) by
    exact pair_sum_sd r_qA_qB r_qB_qA]
  rw [hsd]
  rw [char2_add_self]

/-- the diagonal (q0 coset) four blocks sum to the identity monomial -/
lemma coset_q0 : (((∑ r ∈ r_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2)) = single (m 0 0 0 q0) (1 : ZMod 2) := by
  rw [show (((∑ r ∈ r_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2)) = ((∑ r ∈ r_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2))) + ((∑ r ∈ r_qA_qA, single r (1 : ZMod 2)) + (∑ r ∈ r_qB_qB, single r (1 : ZMod 2))) by abel]
  let A1 := ((r_q0_q0 \ r_qAB_qAB) ∪ (r_qAB_qAB \ r_q0_q0))
  let A2 := ((r_qA_qA \ r_qB_qB) ∪ (r_qB_qB \ r_qA_qA))
  have hd1 : (∑ r ∈ r_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2)) = ∑ m ∈ A1, single m (1 : ZMod 2) := by
    exact pair_sum_sd r_q0_q0 r_qAB_qAB
  have hd2 : (∑ r ∈ r_qA_qA, single r (1 : ZMod 2)) + (∑ r ∈ r_qB_qB, single r (1 : ZMod 2)) = ∑ m ∈ A2, single m (1 : ZMod 2) := by
    exact pair_sum_sd r_qA_qA r_qB_qB
  rw [hd1, hd2]
  have hset : A1 = A2 ∪ ({m 0 0 0 q0} : Finset HW) := by
    dsimp [A1, A2]; decide
  have hmem : m 0 0 0 q0 ∉ A2 := by
    dsimp [A2]; decide
  rw [hset]
  have hdisj : Disjoint A2 ({m 0 0 0 q0} : Finset HW) := by
    rw [Finset.disjoint_left]
    intro x hx hx1
    have hxeq : x = m 0 0 0 q0 := by simpa using hx1
    subst x
    exact hmem hx
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_singleton]
  rw [add_assoc]
  rw [add_comm (single (m 0 0 0 q0) (1 : ZMod 2))]
  rw [← add_assoc]
  rw [char2_add_self]
  simp

/-- coset blocks sum to the identity -/
lemma coset_total : ((((((∑ r ∈ r_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2))) + ((((∑ r ∈ r_q0_qA, single r (1 : ZMod 2)) + (∑ r ∈ r_qA_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qAB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qB, single r (1 : ZMod 2)))) + ((((∑ r ∈ r_q0_qB, single r (1 : ZMod 2)) + (∑ r ∈ r_qB_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qA_qAB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qA, single r (1 : ZMod 2)))) + ((((∑ r ∈ r_q0_qAB, single r (1 : ZMod 2)) + (∑ r ∈ r_qAB_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qA_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qA, single r (1 : ZMod 2))) = single (m 0 0 0 q0) (1 : ZMod 2) := by
  rw [coset_q0, coset_A, coset_B, coset_AB]
  simp

/-- U0 * V0 = 1 (forward product) -/
lemma U0_mul_V0 : U0 * V0 = single (m 0 0 0 q0) (1 : ZMod 2) := by
  have hprod : U0 * V0 = ((((((((∑ s ∈ Qp, single s (1 : ZMod 2))) * ((∑ t ∈ sVq0, single t (1 : ZMod 2)))) + (((∑ s ∈ Qp, single s (1 : ZMod 2))) * ((∑ t ∈ sVqA, single t (1 : ZMod 2))))) + (((∑ s ∈ Qp, single s (1 : ZMod 2))) * ((∑ t ∈ sVqB, single t (1 : ZMod 2))))) + (((∑ s ∈ Qp, single s (1 : ZMod 2))) * ((∑ t ∈ sVqAB, single t (1 : ZMod 2)))) + (((((∑ s ∈ PqA, single s (1 : ZMod 2))) * ((∑ t ∈ sVq0, single t (1 : ZMod 2)))) + (((∑ s ∈ PqA, single s (1 : ZMod 2))) * ((∑ t ∈ sVqA, single t (1 : ZMod 2))))) + (((∑ s ∈ PqA, single s (1 : ZMod 2))) * ((∑ t ∈ sVqB, single t (1 : ZMod 2))))) + (((∑ s ∈ PqA, single s (1 : ZMod 2))) * ((∑ t ∈ sVqAB, single t (1 : ZMod 2))))) + (((((∑ s ∈ PrB, single s (1 : ZMod 2))) * ((∑ t ∈ sVq0, single t (1 : ZMod 2)))) + (((∑ s ∈ PrB, single s (1 : ZMod 2))) * ((∑ t ∈ sVqA, single t (1 : ZMod 2))))) + (((∑ s ∈ PrB, single s (1 : ZMod 2))) * ((∑ t ∈ sVqB, single t (1 : ZMod 2))))) + (((∑ s ∈ PrB, single s (1 : ZMod 2))) * ((∑ t ∈ sVqAB, single t (1 : ZMod 2))))) + (((((∑ s ∈ PsAB, single s (1 : ZMod 2))) * ((∑ t ∈ sVq0, single t (1 : ZMod 2)))) + (((∑ s ∈ PsAB, single s (1 : ZMod 2))) * ((∑ t ∈ sVqA, single t (1 : ZMod 2))))) + (((∑ s ∈ PsAB, single s (1 : ZMod 2))) * ((∑ t ∈ sVqB, single t (1 : ZMod 2))))) + (((∑ s ∈ PsAB, single s (1 : ZMod 2))) * ((∑ t ∈ sVqAB, single t (1 : ZMod 2))))) := by
    rw [U0, V0]
    noncomm_ring
  rw [hprod]
  rw [B_q0_q0, B_q0_qA, B_q0_qB, B_q0_qAB]
  rw [B_qA_q0, B_qA_qA, B_qA_qB, B_qA_qAB]
  rw [B_qB_q0, B_qB_qA, B_qB_qB, B_qB_qAB]
  rw [B_qAB_q0, B_qAB_qA, B_qAB_qB, B_qAB_qAB]
  rw [show ((((((∑ r ∈ r_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_q0_qA, single r (1 : ZMod 2))) + (∑ r ∈ r_q0_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_q0_qAB, single r (1 : ZMod 2)) + (((∑ r ∈ r_qA_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ r_qA_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qA_qAB, single r (1 : ZMod 2))) + (((∑ r ∈ r_qB_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qB_qA, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qAB, single r (1 : ZMod 2))) + (((∑ r ∈ r_qAB_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qAB_qA, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2))) = ((((((∑ r ∈ r_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ r_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2))) + ((((∑ r ∈ r_q0_qA, single r (1 : ZMod 2)) + (∑ r ∈ r_qA_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qAB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qB, single r (1 : ZMod 2)))) + ((((∑ r ∈ r_q0_qB, single r (1 : ZMod 2)) + (∑ r ∈ r_qB_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qA_qAB, single r (1 : ZMod 2))) + (∑ r ∈ r_qAB_qA, single r (1 : ZMod 2)))) + ((((∑ r ∈ r_q0_qAB, single r (1 : ZMod 2)) + (∑ r ∈ r_qAB_q0, single r (1 : ZMod 2))) + (∑ r ∈ r_qA_qB, single r (1 : ZMod 2))) + (∑ r ∈ r_qB_qA, single r (1 : ZMod 2))) by abel]
  rw [coset_total]
/-- cancellation in the qA coset -/
lemma vcoset_A : (((∑ r ∈ vr_q0_qA, single r (1 : ZMod 2)) + (∑ r ∈ vr_qA_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qAB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qB, single r (1 : ZMod 2)) = 0 := by
  have h1 : ((∑ r ∈ vr_q0_qA, single r (1 : ZMod 2))) = ((∑ r ∈ vr_qA_q0, single r (1 : ZMod 2))) := by
    rw [vr_q0_qA, vr_qA_q0]
  have h2 : ((∑ r ∈ vr_qB_qAB, single r (1 : ZMod 2))) = ((∑ r ∈ vr_qAB_qB, single r (1 : ZMod 2))) := by
    rw [vr_qB_qAB, vr_qAB_qB]
  rw [h1, h2, add_assoc]
  rw [char2_add_self, char2_add_self]
  simp

/-- cancellation in the qB coset -/
lemma vcoset_B : (((∑ r ∈ vr_q0_qB, single r (1 : ZMod 2)) + (∑ r ∈ vr_qB_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qA_qAB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qA, single r (1 : ZMod 2)) = 0 := by
  have h1 : ((∑ r ∈ vr_q0_qB, single r (1 : ZMod 2))) = ((∑ r ∈ vr_qB_q0, single r (1 : ZMod 2))) := by
    rw [vr_q0_qB, vr_qB_q0]
  have h2 : ((∑ r ∈ vr_qA_qAB, single r (1 : ZMod 2))) = ((∑ r ∈ vr_qAB_qA, single r (1 : ZMod 2))) := by
    rw [vr_qA_qAB, vr_qAB_qA]
  rw [h1, h2, add_assoc]
  rw [char2_add_self, char2_add_self]
  simp

/-- cancellation in the qAB coset -/
lemma vcoset_AB : (((∑ r ∈ vr_q0_qAB, single r (1 : ZMod 2)) + (∑ r ∈ vr_qAB_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qA_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qA, single r (1 : ZMod 2)) = 0 := by
  have hsd : ((vr_q0_qAB \ vr_qAB_q0) ∪ (vr_qAB_q0 \ vr_q0_qAB)) = ((vr_qA_qB \ vr_qB_qA) ∪ (vr_qB_qA \ vr_qA_qB)) := by decide
  rw [add_assoc]
  rw [show (∑ r ∈ vr_q0_qAB, single r (1 : ZMod 2)) + (∑ r ∈ vr_qAB_q0, single r (1 : ZMod 2)) = ∑ m ∈ ((vr_q0_qAB \ vr_qAB_q0) ∪ (vr_qAB_q0 \ vr_q0_qAB)), single m (1 : ZMod 2) by
    exact pair_sum_sd vr_q0_qAB vr_qAB_q0]
  rw [show (∑ r ∈ vr_qA_qB, single r (1 : ZMod 2)) + (∑ r ∈ vr_qB_qA, single r (1 : ZMod 2)) = ∑ m ∈ ((vr_qA_qB \ vr_qB_qA) ∪ (vr_qB_qA \ vr_qA_qB)), single m (1 : ZMod 2) by
    exact pair_sum_sd vr_qA_qB vr_qB_qA]
  rw [hsd]
  rw [char2_add_self]

/-- the diagonal (q0 coset) four blocks sum to the identity monomial -/
lemma vcoset_q0 : (((∑ r ∈ vr_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qAB, single r (1 : ZMod 2)) = single (m 0 0 0 q0) (1 : ZMod 2) := by
  rw [show (((∑ r ∈ vr_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qAB, single r (1 : ZMod 2)) = ((∑ r ∈ vr_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qAB_qAB, single r (1 : ZMod 2))) + ((∑ r ∈ vr_qA_qA, single r (1 : ZMod 2)) + (∑ r ∈ vr_qB_qB, single r (1 : ZMod 2))) by abel]
  let A1 := ((vr_q0_q0 \ vr_qAB_qAB) ∪ (vr_qAB_qAB \ vr_q0_q0))
  let A2 := ((vr_qA_qA \ vr_qB_qB) ∪ (vr_qB_qB \ vr_qA_qA))
  have hd1 : (∑ r ∈ vr_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qAB_qAB, single r (1 : ZMod 2)) = ∑ m ∈ A1, single m (1 : ZMod 2) := by
    exact pair_sum_sd vr_q0_q0 vr_qAB_qAB
  have hd2 : (∑ r ∈ vr_qA_qA, single r (1 : ZMod 2)) + (∑ r ∈ vr_qB_qB, single r (1 : ZMod 2)) = ∑ m ∈ A2, single m (1 : ZMod 2) := by
    exact pair_sum_sd vr_qA_qA vr_qB_qB
  rw [hd1, hd2]
  have hset : A1 = A2 ∪ ({m 0 0 0 q0} : Finset HW) := by
    dsimp [A1, A2]; decide
  have hmem : m 0 0 0 q0 ∉ A2 := by
    dsimp [A2]; decide
  rw [hset]
  have hdisj : Disjoint A2 ({m 0 0 0 q0} : Finset HW) := by
    rw [Finset.disjoint_left]
    intro x hx hx1
    have hxeq : x = m 0 0 0 q0 := by simpa using hx1
    subst x
    exact hmem hx
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_singleton]
  rw [add_assoc]
  rw [add_comm (single (m 0 0 0 q0) (1 : ZMod 2))]
  rw [← add_assoc]
  rw [char2_add_self]
  simp



/-- mirror coset blocks sum to the identity -/
lemma vcoset_total : ((((((∑ r ∈ vr_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qAB, single r (1 : ZMod 2))) + ((((∑ r ∈ vr_q0_qA, single r (1 : ZMod 2)) + (∑ r ∈ vr_qA_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qAB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qB, single r (1 : ZMod 2)))) + ((((∑ r ∈ vr_q0_qB, single r (1 : ZMod 2)) + (∑ r ∈ vr_qB_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qA_qAB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qA, single r (1 : ZMod 2)))) + ((((∑ r ∈ vr_q0_qAB, single r (1 : ZMod 2)) + (∑ r ∈ vr_qAB_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qA_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qA, single r (1 : ZMod 2))) = single (m 0 0 0 q0) (1 : ZMod 2) := by
  rw [vcoset_q0, vcoset_A, vcoset_B, vcoset_AB]
  simp

/-- V0 * U0 = 1 (reverse product) -/
lemma V0_mul_U0 : V0 * U0 = single (m 0 0 0 q0) (1 : ZMod 2) := by
  have hprod : V0 * U0 = (((((((((∑ a ∈ sVq0, single a (1 : ZMod 2))) * ((∑ b ∈ Qp, single b (1 : ZMod 2)))) + (((∑ a ∈ sVq0, single a (1 : ZMod 2))) * ((∑ b ∈ PqA, single b (1 : ZMod 2))))) + (((∑ a ∈ sVq0, single a (1 : ZMod 2))) * ((∑ b ∈ PrB, single b (1 : ZMod 2))))) + (((∑ a ∈ sVq0, single a (1 : ZMod 2))) * ((∑ b ∈ PsAB, single b (1 : ZMod 2))))) + ((((((∑ a ∈ sVqA, single a (1 : ZMod 2))) * ((∑ b ∈ Qp, single b (1 : ZMod 2)))) + (((∑ a ∈ sVqA, single a (1 : ZMod 2))) * ((∑ b ∈ PqA, single b (1 : ZMod 2))))) + (((∑ a ∈ sVqA, single a (1 : ZMod 2))) * ((∑ b ∈ PrB, single b (1 : ZMod 2))))) + (((∑ a ∈ sVqA, single a (1 : ZMod 2))) * ((∑ b ∈ PsAB, single b (1 : ZMod 2)))))) + ((((((∑ a ∈ sVqB, single a (1 : ZMod 2))) * ((∑ b ∈ Qp, single b (1 : ZMod 2)))) + (((∑ a ∈ sVqB, single a (1 : ZMod 2))) * ((∑ b ∈ PqA, single b (1 : ZMod 2))))) + (((∑ a ∈ sVqB, single a (1 : ZMod 2))) * ((∑ b ∈ PrB, single b (1 : ZMod 2))))) + (((∑ a ∈ sVqB, single a (1 : ZMod 2))) * ((∑ b ∈ PsAB, single b (1 : ZMod 2)))))) + ((((((∑ a ∈ sVqAB, single a (1 : ZMod 2))) * ((∑ b ∈ Qp, single b (1 : ZMod 2)))) + (((∑ a ∈ sVqAB, single a (1 : ZMod 2))) * ((∑ b ∈ PqA, single b (1 : ZMod 2))))) + (((∑ a ∈ sVqAB, single a (1 : ZMod 2))) * ((∑ b ∈ PrB, single b (1 : ZMod 2))))) + (((∑ a ∈ sVqAB, single a (1 : ZMod 2))) * ((∑ b ∈ PsAB, single b (1 : ZMod 2)))))) := by
    rw [V0, U0]
    noncomm_ring
  rw [hprod]
  rw [VB_q0_q0, VB_q0_qA, VB_q0_qB, VB_q0_qAB]
  rw [VB_qA_q0, VB_qA_qA, VB_qA_qB, VB_qA_qAB]
  rw [VB_qB_q0, VB_qB_qA, VB_qB_qB, VB_qB_qAB]
  rw [VB_qAB_q0, VB_qAB_qA, VB_qAB_qB, VB_qAB_qAB]
  rw [show (((((((∑ r ∈ vr_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_q0_qA, single r (1 : ZMod 2))) + (∑ r ∈ vr_q0_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_q0_qAB, single r (1 : ZMod 2))) + ((((∑ r ∈ vr_qA_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ vr_qA_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qA_qAB, single r (1 : ZMod 2)))) + ((((∑ r ∈ vr_qB_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qB_qA, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qAB, single r (1 : ZMod 2)))) + ((((∑ r ∈ vr_qAB_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qAB_qA, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qAB, single r (1 : ZMod 2)))) = ((((((∑ r ∈ vr_q0_q0, single r (1 : ZMod 2)) + (∑ r ∈ vr_qA_qA, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qAB, single r (1 : ZMod 2))) + ((((∑ r ∈ vr_q0_qA, single r (1 : ZMod 2)) + (∑ r ∈ vr_qA_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qAB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qB, single r (1 : ZMod 2)))) + ((((∑ r ∈ vr_q0_qB, single r (1 : ZMod 2)) + (∑ r ∈ vr_qB_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qA_qAB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qAB_qA, single r (1 : ZMod 2)))) + ((((∑ r ∈ vr_q0_qAB, single r (1 : ZMod 2)) + (∑ r ∈ vr_qAB_q0, single r (1 : ZMod 2))) + (∑ r ∈ vr_qA_qB, single r (1 : ZMod 2))) + (∑ r ∈ vr_qB_qA, single r (1 : ZMod 2))) by abel]
  rw [vcoset_total]

end Submission
