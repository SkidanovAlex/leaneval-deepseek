import Submission.RingMain

open UnitConjecture

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace Submission

open scoped Classical
open MonoidAlgebra
open Finset

/-- mirror (v·u) block sets: sVpart × Upart, product order t * s -/
def vr_q0_q0 : Finset HW := {(m (-1) (-1) (-1) q0), (m (-1) (-1) (1) q0), (m (-1) (1) (-1) q0), (m (-1) (1) (1) q0), (m (1) (-1) (-1) q0), (m (1) (-1) (1) q0), (m (1) (1) (-1) q0), (m (1) (1) (1) q0)}

def vr_q0_qA : Finset HW := {(m (-2) (-2) (0) qA), (m (-2) (-2) (1) qA), (m (-2) (-1) (0) qA), (m (-2) (-1) (1) qA), (m (-1) (-2) (0) qA), (m (-1) (-2) (2) qA), (m (-1) (-1) (0) qA), (m (-1) (-1) (1) qA), (m (-1) (0) (1) qA), (m (-1) (0) (2) qA), (m (0) (-2) (1) qA), (m (0) (-2) (2) qA), (m (0) (-1) (0) qA), (m (0) (-1) (1) qA), (m (0) (0) (0) qA), (m (0) (0) (2) qA), (m (1) (-1) (0) qA), (m (1) (-1) (1) qA), (m (1) (0) (0) qA), (m (1) (0) (1) qA)}

def vr_q0_qB : Finset HW := {(m (-1) (-2) (1) qB), (m (-1) (-2) (2) qB), (m (-1) (-1) (0) qB), (m (-1) (-1) (2) qB), (m (-1) (0) (0) qB), (m (-1) (0) (1) qB), (m (0) (-2) (1) qB), (m (0) (-2) (2) qB), (m (0) (-1) (1) qB), (m (0) (-1) (2) qB), (m (0) (0) (1) qB), (m (0) (0) (2) qB), (m (0) (1) (1) qB), (m (0) (1) (2) qB), (m (1) (-1) (0) qB), (m (1) (-1) (1) qB), (m (1) (0) (0) qB), (m (1) (0) (2) qB), (m (1) (1) (1) qB), (m (1) (1) (2) qB)}

def vr_q0_qAB : Finset HW := {(m (-2) (-1) (-1) qAB), (m (-2) (-1) (0) qAB), (m (-2) (0) (-1) qAB), (m (-2) (0) (0) qAB), (m (-1) (-2) (-1) qAB), (m (-1) (-2) (0) qAB), (m (-1) (-1) (0) qAB), (m (-1) (-1) (1) qAB), (m (-1) (0) (0) qAB), (m (-1) (0) (1) qAB), (m (-1) (1) (-1) qAB), (m (-1) (1) (0) qAB), (m (0) (-2) (-1) qAB), (m (0) (-2) (0) qAB), (m (0) (-1) (0) qAB), (m (0) (-1) (1) qAB), (m (0) (0) (0) qAB), (m (0) (0) (1) qAB), (m (0) (1) (-1) qAB), (m (0) (1) (0) qAB), (m (1) (-1) (-1) qAB), (m (1) (-1) (0) qAB), (m (1) (0) (-1) qAB), (m (1) (0) (0) qAB)}

def vr_qA_q0 : Finset HW := {(m (-2) (-2) (0) qA), (m (-2) (-2) (1) qA), (m (-2) (-1) (0) qA), (m (-2) (-1) (1) qA), (m (-1) (-2) (0) qA), (m (-1) (-2) (2) qA), (m (-1) (-1) (0) qA), (m (-1) (-1) (1) qA), (m (-1) (0) (1) qA), (m (-1) (0) (2) qA), (m (0) (-2) (1) qA), (m (0) (-2) (2) qA), (m (0) (-1) (0) qA), (m (0) (-1) (1) qA), (m (0) (0) (0) qA), (m (0) (0) (2) qA), (m (1) (-1) (0) qA), (m (1) (-1) (1) qA), (m (1) (0) (0) qA), (m (1) (0) (1) qA)}

def vr_qA_qA : Finset HW := {(m (-2) (0) (0) q0), (m (-1) (-1) (-1) q0), (m (-1) (0) (-1) q0), (m (-1) (0) (1) q0), (m (-1) (1) (1) q0), (m (1) (-1) (1) q0), (m (1) (0) (-1) q0), (m (1) (0) (1) q0), (m (1) (1) (-1) q0), (m (2) (0) (0) q0)}

def vr_qA_qB : Finset HW := {(m (-2) (-1) (0) qAB), (m (-2) (0) (-1) qAB), (m (-1) (-2) (-1) qAB), (m (-1) (-1) (0) qAB), (m (-1) (-1) (1) qAB), (m (-1) (0) (0) qAB), (m (-1) (0) (1) qAB), (m (-1) (1) (0) qAB), (m (0) (-2) (0) qAB), (m (0) (-1) (0) qAB), (m (0) (-1) (1) qAB), (m (0) (0) (0) qAB), (m (0) (0) (1) qAB), (m (0) (1) (-1) qAB), (m (1) (-1) (-1) qAB), (m (1) (0) (0) qAB)}

def vr_qA_qAB : Finset HW := {(m (-2) (-1) (1) qB), (m (-1) (-2) (1) qB), (m (-1) (-1) (0) qB), (m (-1) (-1) (2) qB), (m (-1) (0) (1) qB), (m (-1) (0) (2) qB), (m (0) (-2) (2) qB), (m (0) (-1) (2) qB), (m (0) (0) (2) qB), (m (0) (1) (2) qB), (m (1) (-1) (1) qB), (m (1) (-1) (2) qB), (m (1) (0) (0) qB), (m (1) (0) (2) qB), (m (1) (1) (1) qB), (m (2) (0) (1) qB)}

def vr_qB_q0 : Finset HW := {(m (-1) (-2) (1) qB), (m (-1) (-2) (2) qB), (m (-1) (-1) (0) qB), (m (-1) (-1) (2) qB), (m (-1) (0) (0) qB), (m (-1) (0) (1) qB), (m (0) (-2) (1) qB), (m (0) (-2) (2) qB), (m (0) (-1) (1) qB), (m (0) (-1) (2) qB), (m (0) (0) (1) qB), (m (0) (0) (2) qB), (m (0) (1) (1) qB), (m (0) (1) (2) qB), (m (1) (-1) (0) qB), (m (1) (-1) (1) qB), (m (1) (0) (0) qB), (m (1) (0) (2) qB), (m (1) (1) (1) qB), (m (1) (1) (2) qB)}

def vr_qB_qA : Finset HW := {(m (-2) (-1) (0) qAB), (m (-2) (0) (-1) qAB), (m (-1) (-2) (-1) qAB), (m (-1) (-1) (-2) qAB), (m (-1) (-1) (-1) qAB), (m (-1) (0) (-2) qAB), (m (-1) (0) (-1) qAB), (m (-1) (1) (0) qAB), (m (0) (-2) (0) qAB), (m (0) (-1) (-2) qAB), (m (0) (-1) (-1) qAB), (m (0) (0) (-2) qAB), (m (0) (0) (-1) qAB), (m (0) (1) (-1) qAB), (m (1) (-1) (-1) qAB), (m (1) (0) (0) qAB)}

def vr_qB_qB : Finset HW := {(m (-1) (-1) (1) q0), (m (-1) (1) (-1) q0), (m (0) (-2) (0) q0), (m (0) (-1) (-1) q0), (m (0) (-1) (1) q0), (m (0) (1) (-1) q0), (m (0) (1) (1) q0), (m (0) (2) (0) q0), (m (1) (-1) (-1) q0), (m (1) (1) (1) q0)}

def vr_qB_qAB : Finset HW := {(m (-2) (-2) (1) qA), (m (-2) (-1) (0) qA), (m (-1) (-3) (1) qA), (m (-1) (-1) (-1) qA), (m (-1) (-1) (0) qA), (m (-1) (-1) (1) qA), (m (-1) (0) (0) qA), (m (-1) (0) (1) qA), (m (0) (-2) (0) qA), (m (0) (-2) (1) qA), (m (0) (-1) (-1) qA), (m (0) (-1) (0) qA), (m (0) (-1) (1) qA), (m (0) (1) (1) qA), (m (1) (-1) (0) qA), (m (1) (0) (1) qA)}

def vr_qAB_q0 : Finset HW := {(m (-2) (-1) (-1) qAB), (m (-2) (-1) (0) qAB), (m (-2) (0) (-1) qAB), (m (-2) (0) (0) qAB), (m (-1) (-2) (-1) qAB), (m (-1) (-2) (0) qAB), (m (-1) (-1) (-2) qAB), (m (-1) (-1) (-1) qAB), (m (-1) (0) (-2) qAB), (m (-1) (0) (-1) qAB), (m (-1) (1) (-1) qAB), (m (-1) (1) (0) qAB), (m (0) (-2) (-1) qAB), (m (0) (-2) (0) qAB), (m (0) (-1) (-2) qAB), (m (0) (-1) (-1) qAB), (m (0) (0) (-2) qAB), (m (0) (0) (-1) qAB), (m (0) (1) (-1) qAB), (m (0) (1) (0) qAB), (m (1) (-1) (-1) qAB), (m (1) (-1) (0) qAB), (m (1) (0) (-1) qAB), (m (1) (0) (0) qAB)}

def vr_qAB_qA : Finset HW := {(m (-2) (-1) (1) qB), (m (-1) (-2) (1) qB), (m (-1) (-1) (0) qB), (m (-1) (-1) (2) qB), (m (-1) (0) (1) qB), (m (-1) (0) (2) qB), (m (0) (-2) (2) qB), (m (0) (-1) (2) qB), (m (0) (0) (2) qB), (m (0) (1) (2) qB), (m (1) (-1) (1) qB), (m (1) (-1) (2) qB), (m (1) (0) (0) qB), (m (1) (0) (2) qB), (m (1) (1) (1) qB), (m (2) (0) (1) qB)}

def vr_qAB_qB : Finset HW := {(m (-2) (-2) (1) qA), (m (-2) (-1) (0) qA), (m (-1) (-3) (1) qA), (m (-1) (-1) (-1) qA), (m (-1) (-1) (0) qA), (m (-1) (-1) (1) qA), (m (-1) (0) (0) qA), (m (-1) (0) (1) qA), (m (0) (-2) (0) qA), (m (0) (-2) (1) qA), (m (0) (-1) (-1) qA), (m (0) (-1) (0) qA), (m (0) (-1) (1) qA), (m (0) (1) (1) qA), (m (1) (-1) (0) qA), (m (1) (0) (1) qA)}

def vr_qAB_qAB : Finset HW := {(m (-2) (0) (0) q0), (m (-1) (0) (-1) q0), (m (-1) (0) (1) q0), (m (0) (-2) (0) q0), (m (0) (-1) (-1) q0), (m (0) (-1) (1) q0), (m (0) (0) (0) q0), (m (0) (1) (-1) q0), (m (0) (1) (1) q0), (m (0) (2) (0) q0), (m (1) (0) (-1) q0), (m (1) (0) (1) q0), (m (2) (0) (0) q0)}

lemma VB_q0_q0 :
    (∑ a ∈ sVq0, single a (1 : ZMod 2)) * (∑ b ∈ Qp, single b (1 : ZMod 2))
      = ∑ r ∈ vr_q0_q0, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVq0 Qp (fun a b => a * b) (vr_q0_q0)
    (by decide) (by decide)

lemma VB_q0_qA :
    (∑ a ∈ sVq0, single a (1 : ZMod 2)) * (∑ b ∈ PqA, single b (1 : ZMod 2))
      = ∑ r ∈ vr_q0_qA, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVq0 PqA (fun a b => a * b) (vr_q0_qA)
    (by decide) (by decide)

lemma VB_q0_qB :
    (∑ a ∈ sVq0, single a (1 : ZMod 2)) * (∑ b ∈ PrB, single b (1 : ZMod 2))
      = ∑ r ∈ vr_q0_qB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVq0 PrB (fun a b => a * b) (vr_q0_qB)
    (by decide) (by decide)

lemma VB_q0_qAB :
    (∑ a ∈ sVq0, single a (1 : ZMod 2)) * (∑ b ∈ PsAB, single b (1 : ZMod 2))
      = ∑ r ∈ vr_q0_qAB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVq0 PsAB (fun a b => a * b) (vr_q0_qAB)
    (by decide) (by decide)

lemma VB_qA_q0 :
    (∑ a ∈ sVqA, single a (1 : ZMod 2)) * (∑ b ∈ Qp, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qA_q0, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqA Qp (fun a b => a * b) (vr_qA_q0)
    (by decide) (by decide)

lemma VB_qA_qA :
    (∑ a ∈ sVqA, single a (1 : ZMod 2)) * (∑ b ∈ PqA, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qA_qA, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqA PqA (fun a b => a * b) (vr_qA_qA)
    (by decide) (by decide)

lemma VB_qA_qB :
    (∑ a ∈ sVqA, single a (1 : ZMod 2)) * (∑ b ∈ PrB, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qA_qB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqA PrB (fun a b => a * b) (vr_qA_qB)
    (by decide) (by decide)

lemma VB_qA_qAB :
    (∑ a ∈ sVqA, single a (1 : ZMod 2)) * (∑ b ∈ PsAB, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qA_qAB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqA PsAB (fun a b => a * b) (vr_qA_qAB)
    (by decide) (by decide)

lemma VB_qB_q0 :
    (∑ a ∈ sVqB, single a (1 : ZMod 2)) * (∑ b ∈ Qp, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qB_q0, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqB Qp (fun a b => a * b) (vr_qB_q0)
    (by decide) (by decide)

lemma VB_qB_qA :
    (∑ a ∈ sVqB, single a (1 : ZMod 2)) * (∑ b ∈ PqA, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qB_qA, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqB PqA (fun a b => a * b) (vr_qB_qA)
    (by decide) (by decide)

lemma VB_qB_qB :
    (∑ a ∈ sVqB, single a (1 : ZMod 2)) * (∑ b ∈ PrB, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qB_qB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqB PrB (fun a b => a * b) (vr_qB_qB)
    (by decide) (by decide)

lemma VB_qB_qAB :
    (∑ a ∈ sVqB, single a (1 : ZMod 2)) * (∑ b ∈ PsAB, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qB_qAB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqB PsAB (fun a b => a * b) (vr_qB_qAB)
    (by decide) (by decide)

lemma VB_qAB_q0 :
    (∑ a ∈ sVqAB, single a (1 : ZMod 2)) * (∑ b ∈ Qp, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qAB_q0, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqAB Qp (fun a b => a * b) (vr_qAB_q0)
    (by decide) (by decide)

lemma VB_qAB_qA :
    (∑ a ∈ sVqAB, single a (1 : ZMod 2)) * (∑ b ∈ PqA, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qAB_qA, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqAB PqA (fun a b => a * b) (vr_qAB_qA)
    (by decide) (by decide)

lemma VB_qAB_qB :
    (∑ a ∈ sVqAB, single a (1 : ZMod 2)) * (∑ b ∈ PrB, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qAB_qB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqAB PrB (fun a b => a * b) (vr_qAB_qB)
    (by decide) (by decide)

lemma VB_qAB_qAB :
    (∑ a ∈ sVqAB, single a (1 : ZMod 2)) * (∑ b ∈ PsAB, single b (1 : ZMod 2))
      = ∑ r ∈ vr_qAB_qAB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op sVqAB PsAB (fun a b => a * b) (vr_qAB_qAB)
    (by decide) (by decide)

end Submission
